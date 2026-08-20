#!/usr/bin/env python3
"""Run one sealed three-condition infrastructure smoke without producing results."""

from __future__ import annotations

import argparse
import hashlib
import json
import os
import stat
import sys
from contextlib import contextmanager
from pathlib import Path, PurePosixPath
from typing import Any


TOOLS = Path(__file__).resolve().parent
sys.path.insert(0, str(TOOLS))

import check_target_drift_run as checker  # noqa: E402
import prepare_target_drift_execution as prepare  # noqa: E402
import prepare_target_drift_smoke as smoke  # noqa: E402
import run_target_drift_execution as runner  # noqa: E402


def load(path: Path) -> dict[str, Any]:
    return json.loads(path.read_text(encoding="utf-8"))


def load_bound(path: Path) -> tuple[dict[str, Any], str]:
    payload = path.read_bytes()
    return json.loads(payload.decode("utf-8")), hashlib.sha256(payload).hexdigest()


def require(condition: bool, message: str) -> None:
    if not condition:
        raise SystemExit(f"target-drift smoke failed: {message}")


def validate_plan(pack: Path, plan_path: Path) -> tuple[dict[str, Any], str]:
    prepare.verify_pack(pack)
    plan, plan_sha256 = load_bound(plan_path)
    aggregate = (pack / "aggregate.sha256").read_text(encoding="ascii").strip()
    expected_plan_fields = {
        "schema_version", "suite_id", "execution_purpose",
        "primary_result_eligible", "sealed_pack_sha256", "source_case_id",
        "source_replicate", "requirement_variant", "run_count", "runs",
        "neutral_runs_root_name", "tool_sha256", "result_boundary", "status",
    }
    require(set(plan) == expected_plan_fields,
            "smoke-plan fields differ from the sealed schema")
    require(plan.get("schema_version") == 1
            and plan.get("suite_id") == "ABRL-TARGET-DRIFT-V2",
            "unknown smoke-plan schema or suite")
    require(plan.get("execution_purpose") == runner.SMOKE_EXECUTION_PURPOSE
            and plan.get("primary_result_eligible") is False,
            "smoke plan lost its permanent primary-result exclusion")
    require(plan.get("sealed_pack_sha256") == aggregate,
            "smoke plan names a different sealed pack")
    boundary = plan.get("result_boundary")
    require(isinstance(boundary, dict) and all(boundary.get(key) is True for key in (
        "permanently_excluded_from_primary_450", "grading_forbidden",
        "analysis_forbidden", "model_or_formalization_outcome_claim_forbidden",
    )), "smoke plan result boundary is incomplete")
    expected_tools = {
        "prepare_target_drift_smoke.py": prepare.sha256_file(Path(smoke.__file__).resolve()),
        "run_target_drift_smoke.py": prepare.sha256_file(Path(__file__).resolve()),
    }
    require(plan.get("tool_sha256") == expected_tools,
            "smoke plan tool hashes differ from invoked code")
    runs = plan.get("runs")
    require(isinstance(runs, list) and len(runs) == plan.get("run_count") == 3,
            "smoke plan must contain exactly three runs")
    require({run.get("condition") for run in runs} == set(runner.CONDITIONS),
            "smoke plan does not cover exactly the three conditions")
    require(len({run.get("smoke_run_id") for run in runs}) == 3
            and all(run.get("primary_result_eligible") is False for run in runs),
            "smoke run identities or eligibility are invalid")
    manifest = load(pack / "run_manifest.json")
    primary = {run["run_id"]: run for run in manifest["runs"]}
    source_ids = []
    for planned in runs:
        require(set(planned) == {
            "smoke_run_id", "source_primary_run_id", "condition", "replicate",
            "requirement_variant", "status", "primary_result_eligible",
        }, "smoke-plan run fields differ from the sealed schema")
        source = primary.get(planned.get("source_primary_run_id"))
        require(source is not None, "smoke plan source run is absent from primary manifest")
        for key in ("condition", "replicate", "requirement_variant"):
            require(planned.get(key) == source.get(key),
                    f"smoke plan {key} differs from source primary run")
        require(planned["smoke_run_id"] not in primary,
                "smoke id collides with a primary run id")
        require(planned.get("smoke_run_id") == smoke.smoke_run_id(
            aggregate, planned["source_primary_run_id"]
        ), "smoke run id is not the deterministic derivation")
        require(planned.get("status") == "sealed_unrun",
                "smoke plan run is not sealed_unrun")
        source_ids.append(source["run_id"])
    expected = smoke.matched_triplet(manifest["runs"], source_ids[0])
    require(set(source_ids) == {run["run_id"] for run in expected},
            "smoke plan mixes sources from different matched triplets")
    anchor = expected[0]
    require(plan.get("source_case_id") == anchor["case_id"]
            and plan.get("source_replicate") == anchor["replicate"]
            and plan.get("requirement_variant") == anchor["requirement_variant"],
            "smoke plan top-level source identity differs from matched triplet")
    require(plan.get("status") == "sealed_unrun", "smoke plan is not sealed_unrun")
    neutral_root = plan.get("neutral_runs_root_name")
    require(isinstance(neutral_root, str) and neutral_root.startswith("RUNS-")
            and len(neutral_root) == 25,
            "smoke plan lacks a neutral opaque runs-root name")
    require(neutral_root == smoke.neutral_runs_root_name(
        aggregate, anchor["case_id"], anchor["replicate"]
    ), "smoke plan neutral runs-root name is not the deterministic derivation")
    require(prepare.sha256_file(plan_path) == plan_sha256,
            "smoke plan changed while it was validated")
    return plan, plan_sha256


def dump_new(path: Path, value: Any) -> None:
    require(not path.exists(), "smoke ledger already exists")
    path.parent.mkdir(parents=True, exist_ok=True)
    with path.open("x", encoding="utf-8", newline="\n") as handle:
        json.dump(value, handle, indent=2, sort_keys=True, ensure_ascii=False)
        handle.write("\n")


def require_private_directory(path: Path, label: str, *, create: bool = False) -> None:
    """Require one no-follow, private directory owned by the controller user."""
    if create and not path.exists():
        path.mkdir(mode=0o700)
    require(path.exists() and not path.is_symlink(), f"{label} is missing or linked")
    info = path.lstat()
    reparse = bool(getattr(info, "st_file_attributes", 0) & 0x400)
    require(stat.S_ISDIR(info.st_mode) and not reparse,
            f"{label} is not a plain directory")
    if os.name != "nt":
        require(info.st_uid == os.geteuid(), f"{label} is not owned by this controller")
        require(stat.S_IMODE(info.st_mode) & 0o077 == 0,
                f"{label} is accessible outside its controller owner")


def canonical_runs_root(plan: dict[str, Any], base_override: Path | None = None) -> Path:
    """Choose a runner-owned neutral root; production CLI accepts no path override."""
    if base_override is not None:
        base = base_override
    elif os.name == "nt":
        raise SystemExit(
            "target-drift smoke failed: production smoke orchestration requires "
            "a POSIX private-directory and parent-death/container lifecycle boundary"
        )
    else:
        base = Path("/tmp/.abrl-runs")
    base = base.absolute()
    parent = base.parent
    require(parent.exists() and not parent.is_symlink(),
            "smoke controller base parent is missing or linked")
    parent_info = parent.lstat()
    parent_reparse = bool(getattr(parent_info, "st_file_attributes", 0) & 0x400)
    require(stat.S_ISDIR(parent_info.st_mode) and not parent_reparse,
            "smoke controller base parent is not a plain directory")
    require_private_directory(base, "smoke controller base", create=True)
    runs_root = base / plan["neutral_runs_root_name"]
    require_private_directory(runs_root, "smoke runs root", create=True)
    return runs_root


def attempt_registry_paths(plan_sha256: str, runs_root: Path) -> tuple[Path, Path, Path]:
    """Key the attempt by semantic root; bind exact plan bytes inside its record."""
    require(len(plan_sha256) == 64, "smoke plan digest is malformed")
    registry = runs_root.parent / ".attempts"
    require_private_directory(registry, "smoke attempt registry", create=True)
    root_name = runs_root.name
    require(root_name.startswith("RUNS-") and len(root_name) == 25,
            "smoke attempt registry received a noncanonical runs root")
    stem = f"ROOT-{root_name[5:]}"
    return (
        registry / f"{stem}.json",
        registry / f"{stem}.plan.json",
        registry / f"{stem}.lock",
    )


def dump_atomic(path: Path, value: Any) -> None:
    temporary = path.with_name(path.name + f".tmp-{os.getpid()}")
    require(not temporary.exists(), "temporary lifecycle path already exists")
    with temporary.open("x", encoding="utf-8", newline="\n") as handle:
        json.dump(value, handle, indent=2, sort_keys=True, ensure_ascii=False)
        handle.write("\n")
    os.replace(temporary, path)


def bind_single_attempt(
    plan_path: Path, plan_sha256: str, runs_root: Path, ledger_path: Path,
) -> Path:
    attempt_path, sealed_plan_path, _ = attempt_registry_paths(plan_sha256, runs_root)
    if sealed_plan_path.exists():
        require(prepare.sha256_file(sealed_plan_path) == plan_sha256,
                "sealed attempt plan differs from the validated plan bytes")
    else:
        payload = plan_path.read_bytes()
        require(hashlib.sha256(payload).hexdigest() == plan_sha256,
                "plan changed before attempt sealing")
        with sealed_plan_path.open("xb") as handle:
            handle.write(payload)
    expected = {
        "schema_version": 1,
        "execution_purpose": runner.SMOKE_EXECUTION_PURPOSE,
        "smoke_plan_sha256": plan_sha256,
        "runs_root": str(runs_root),
        "ledger_path": str(ledger_path),
        "sealed_plan_path": str(sealed_plan_path),
        "status": "started_result_ineligible_smoke",
    }
    if attempt_path.exists():
        existing, _ = load_bound(attempt_path)
        require(existing == expected,
                "smoke plan was already consumed by a different attempt or path")
    else:
        dump_new(attempt_path, expected)
    return attempt_path


@contextmanager
def exclusive_attempt_lock(lock_path: Path):
    """Hold an OS-released nonblocking lock across prepare/execute/check/ledger."""
    lock_path.parent.mkdir(parents=True, exist_ok=True)
    handle = lock_path.open("a+b")
    acquired = False
    try:
        handle.seek(0, os.SEEK_END)
        if handle.tell() == 0:
            handle.write(b"0")
            handle.flush()
        handle.seek(0)
        if os.name == "nt":
            import msvcrt
            try:
                msvcrt.locking(handle.fileno(), msvcrt.LK_NBLCK, 1)
            except OSError as error:
                raise SystemExit(
                    "target-drift smoke failed: another process owns this smoke attempt"
                ) from error
        else:
            import fcntl
            try:
                fcntl.flock(handle.fileno(), fcntl.LOCK_EX | fcntl.LOCK_NB)
            except OSError as error:
                raise SystemExit(
                    "target-drift smoke failed: another process owns this smoke attempt"
                ) from error
        acquired = True
        yield
    finally:
        try:
            if acquired and os.name == "nt":
                import msvcrt
                handle.seek(0)
                msvcrt.locking(handle.fileno(), msvcrt.LK_UNLCK, 1)
            elif acquired:
                import fcntl
                fcntl.flock(handle.fileno(), fcntl.LOCK_UN)
        finally:
            handle.close()


def advance_smoke_run(
    pack: Path, planned: dict[str, Any], run_dir: Path, plan_sha256: str,
) -> tuple[dict[str, Any], str | None]:
    error = None
    try:
        if not run_dir.exists():
            runner.prepare_run(
                pack, planned["smoke_run_id"], run_dir,
                source_semantic_run_id=planned["source_primary_run_id"],
                execution_purpose=runner.SMOKE_EXECUTION_PURPOSE,
                primary_result_eligible=False,
                smoke_plan_sha256=plan_sha256,
            )
        state = load(run_dir / "operator" / "run_state.json")
        if state.get("status") == "prepared_unrun":
            runner.execute_or_record_failure(pack, run_dir)
            state = load(run_dir / "operator" / "run_state.json")
        if state.get("status") == "executed_unchecked":
            checker.execute(pack, run_dir)
    except (checker.CheckerFailure, SystemExit, Exception) as caught:
        error = f"{type(caught).__name__}: {caught}"
    state_path = run_dir / "operator" / "run_state.json"
    if not state_path.is_file():
        return {}, error or "run state is missing"
    state, state_sha256 = load_bound(state_path)
    require(prepare.sha256_file(state_path) == state_sha256,
            "run state changed while smoke ledger was derived")
    return {**state, "_bound_sha256": state_sha256}, error


def run_smoke(
    pack: Path, plan: dict[str, Any], plan_sha256: str, runs_root: Path,
) -> dict[str, Any]:
    require(runs_root == canonical_runs_root(plan),
            "smoke runner must use its canonical neutral runs root")
    runs_root.mkdir(parents=True, exist_ok=True)
    aggregate = plan["sealed_pack_sha256"]
    records = []
    for planned in plan["runs"]:
        smoke_id = planned["smoke_run_id"]
        opaque = runner.opaque_id("run", aggregate, smoke_id)
        run_dir = runs_root / opaque
        state, error = advance_smoke_run(
            pack, planned, run_dir, plan_sha256
        )
        if error is None:
            try:
                records.append(inspect_smoke_run(
                    pack, plan, plan_sha256, planned, runs_root
                ))
                continue
            except (SystemExit, Exception) as caught:
                error = f"{type(caught).__name__}: {caught}"
        records.append({
            "smoke_run_id": smoke_id,
            "opaque_run_id": opaque,
            "condition": planned["condition"],
            "status": state.get("status", "not_materialized_or_unreadable"),
            "checker_mode": state.get("checker_mode"),
            "result_eligible": False,
            "run_state_sha256": state.get("_bound_sha256"),
            "error": error,
        })
    passed = all(
        record["status"] == "checked_smoke_nonexperimental"
        and record["checker_mode"] == "production"
        and record["result_eligible"] is False
        and record["error"] is None
        for record in records
    )
    return {
        "schema_version": 1,
        "suite_id": "ABRL-TARGET-DRIFT-V2",
        "execution_purpose": runner.SMOKE_EXECUTION_PURPOSE,
        "primary_result_eligible": False,
        "sealed_pack_sha256": aggregate,
        "smoke_plan_sha256": plan_sha256,
        "run_count": 3,
        "all_three_infrastructure_paths_passed": passed,
        "model_or_formalization_outcome_reported": False,
        "records": records,
        "status": "passed_result_ineligible_smoke" if passed else "failed_result_ineligible_smoke",
    }


def validate_ledger(plan: dict[str, Any], plan_sha256: str, ledger: dict[str, Any]) -> None:
    require(ledger.get("schema_version") == 1
            and ledger.get("suite_id") == "ABRL-TARGET-DRIFT-V2",
            "unknown smoke-ledger schema or suite")
    require(ledger.get("execution_purpose") == runner.SMOKE_EXECUTION_PURPOSE
            and ledger.get("primary_result_eligible") is False,
            "smoke ledger lost its permanent primary-result exclusion")
    require(ledger.get("sealed_pack_sha256") == plan["sealed_pack_sha256"]
            and ledger.get("smoke_plan_sha256") == plan_sha256,
            "smoke ledger hash bindings differ from its plan")
    require(ledger.get("run_count") == 3
            and ledger.get("model_or_formalization_outcome_reported") is False,
            "smoke ledger count or no-outcome boundary is invalid")
    records = ledger.get("records")
    require(isinstance(records, list) and len(records) == 3,
            "smoke ledger must contain exactly three records")
    planned = {run["smoke_run_id"]: run for run in plan["runs"]}
    require({record.get("smoke_run_id") for record in records} == set(planned),
            "smoke ledger identities differ from its plan")
    for record in records:
        source = planned[record["smoke_run_id"]]
        require(record.get("condition") == source["condition"]
                and record.get("result_eligible") is False,
                "smoke ledger condition or eligibility differs from its plan")
    passed = all(
        record.get("status") == "checked_smoke_nonexperimental"
        and record.get("checker_mode") == "production"
        and record.get("result_eligible") is False
        and record.get("error") is None
        for record in records
    )
    require(ledger.get("all_three_infrastructure_paths_passed") is passed,
            "smoke ledger pass flag is inconsistent with run records")
    require(ledger.get("status") == (
        "passed_result_ineligible_smoke" if passed else "failed_result_ineligible_smoke"
    ), "smoke ledger terminal status is inconsistent")


def inspect_smoke_run(
    pack: Path, plan: dict[str, Any], plan_sha256: str,
    planned: dict[str, Any], runs_root: Path,
) -> dict[str, Any]:
    aggregate = plan["sealed_pack_sha256"]
    expected_opaque = runner.opaque_id("run", aggregate, planned["smoke_run_id"])
    run_dir = runs_root / expected_opaque
    operator = run_dir / "operator"
    agent = run_dir / "agent"
    paths = {
        "job": operator / "job.json",
        "state": operator / "run_state.json",
        "receipt": operator / "execution-receipt.json",
        "workspace": operator / "workspace_manifest.json",
        "checker_receipt": operator / "checker" / "checker-execution-receipt.json",
        "checker_result": operator / "checker" / "checker-result.json",
        "checker_response": operator / "checker" / "sandbox-response.json",
    }
    require(all(path.is_file() for path in paths.values()),
            "completed smoke run lacks required operator/checker evidence")
    for label, path in paths.items():
        prepare.regular_unlinked_file(path, f"smoke {label}", require_executable=False)
    bound = {name: load_bound(path) for name, path in paths.items()}
    job, job_sha = bound["job"]
    state, state_sha = bound["state"]
    receipt, receipt_sha = bound["receipt"]
    checker_receipt, checker_receipt_sha = bound["checker_receipt"]
    checker_result, checker_result_sha = bound["checker_result"]
    checker_response, checker_response_sha = bound["checker_response"]
    config = load(pack / "execution_config.json")
    checker_config = config["posthoc_checker"]
    checker_root = operator / "checker"
    runner.file_manifest(checker_root)
    require(job.get("semantic_run_id") == planned["smoke_run_id"]
            and job.get("source_primary_run_id") == planned["source_primary_run_id"]
            and job.get("opaque_run_id") == expected_opaque,
            "smoke job identity differs from its plan")
    require(job.get("execution_purpose") == runner.SMOKE_EXECUTION_PURPOSE
            and job.get("primary_result_eligible") is False
            and job.get("smoke_plan_sha256") == plan_sha256,
            "smoke job lost purpose/eligibility/plan binding")
    require(job.get("condition") == planned["condition"]
            and job.get("replicate") == planned["replicate"],
            "smoke job condition/replicate differs from its plan")
    require(state.get("status") == "checked_smoke_nonexperimental"
            and state.get("result_eligible") is False
            and state.get("checker_mode") == "production",
            "smoke state is not a completed production-checker ineligible state")
    require(state.get("opaque_run_id") == expected_opaque
            and state.get("execution_purpose") == runner.SMOKE_EXECUTION_PURPOSE
            and state.get("smoke_plan_sha256") == plan_sha256,
            "smoke state identity/purpose/plan binding differs")
    require(state.get("sealed_pack_sha256") == receipt.get("sealed_pack_sha256") == aggregate,
            "smoke state/receipt names a different sealed pack")
    require(receipt.get("opaque_run_id") == checker_receipt.get("opaque_run_id")
            == checker_result.get("opaque_run_id")
            == checker_response.get("opaque_run_id") == expected_opaque,
            "smoke execution/checker evidence names a different opaque run")
    require(state.get("prepared_job_sha256") == receipt.get("prepared_job_sha256") == job_sha,
            "smoke prepared-job hash chain differs")
    require(state.get("workspace_manifest_sha256") == receipt.get("workspace_manifest_sha256")
            == prepare.sha256_file(paths["workspace"]),
            "smoke workspace-manifest hash chain differs")
    require(state.get("execution_receipt_sha256") == receipt_sha
            and state.get("checker_execution_receipt_sha256") == checker_receipt_sha
            and state.get("checker_result_sha256") == checker_result_sha
            and state.get("sandbox_response_sha256") == checker_response_sha,
            "smoke state receipt/result/response hash chain differs")
    require(receipt.get("execution_purpose") == runner.SMOKE_EXECUTION_PURPOSE
            and receipt.get("primary_result_eligible") is False
            and receipt.get("smoke_plan_sha256") == plan_sha256,
            "smoke execution receipt lost permanent exclusion")
    require(runner.manifest_sha256(runner.file_manifest(agent))
            == receipt.get("completed_agent_manifest_sha256")
            == state.get("completed_agent_manifest_sha256"),
            "smoke agent manifest differs from completed execution evidence")
    checker.require_adapter_artifacts_unchanged(operator, receipt)
    require(checker_receipt.get("execution_purpose") == runner.SMOKE_EXECUTION_PURPOSE
            and checker_receipt.get("checker_mode") == "production"
            and checker_receipt.get("result_eligible") is False,
            "smoke checker receipt lost production/ineligible boundary")
    require(checker_receipt.get("sandbox_response_sha256") == checker_response_sha
            and checker_receipt.get("checker_result_sha256") == checker_result_sha,
            "smoke checker receipt names different response/result bytes")
    require(checker_receipt.get("checker_runtime_config_sha256")
            == state.get("checker_runtime_config_sha256")
            == checker_config["runtime_config_sha256"],
            "smoke checker runtime binding differs from frozen config")
    require(checker_receipt.get("isolation_probe_report_sha256")
            == state.get("isolation_probe_report_sha256")
            == checker_config["isolation_probe_report_sha256"],
            "smoke checker probe binding differs from frozen config")
    require(checker_result.get("sealed_pack_sha256") == aggregate
            and checker_result.get("execution_receipt_sha256") == receipt_sha,
            "smoke checker result differs from pack/execution receipt")
    require(checker_response.get("checker_result_sha256") == checker_result_sha,
            "smoke sandbox response names a different checker result")
    require(state.get("checker_attempt_id") == checker_receipt.get("checker_attempt_id")
            == checker_response.get("checker_attempt_id")
            == checker_response.get("checker_attempt_label"),
            "smoke checker attempt identities differ")
    request_path = (
        operator / "checker-attempts" / state["checker_attempt_id"] / "request.json"
    )
    require(request_path.is_file(), "smoke checker request is missing")
    prepare.regular_unlinked_file(
        request_path, "smoke checker request", require_executable=False
    )
    request, request_sha = load_bound(request_path)
    require(state.get("checker_request_sha256") == request_sha
            == checker_receipt.get("checker_request_sha256")
            == checker_response.get("request_sha256"),
            "smoke checker request hash chain differs")
    require(request.get("sealed_pack_sha256") == aggregate
            and request.get("execution_receipt_sha256") == receipt_sha
            and request.get("completed_agent_manifest_sha256")
            == receipt.get("completed_agent_manifest_sha256"),
            "smoke checker request differs from pack/execution evidence")
    require(request.get("container_image_digest")
            == checker_config["container_image_digest"]
            and request.get("inner_checker_sha256")
            == checker_config["inner_checker_sha256"]
            and request.get("checker_contract_sha256")
            == checker_config["contract_sha256"]
            and request.get("checker_runtime_config_sha256")
            == checker_config["runtime_config_sha256"],
            "smoke checker request differs from frozen checker config")
    checker.validate_checker_result(
        checker_result, request, expected_opaque, state["checker_attempt_id"]
    )
    expected_response = {
        "checker_id": checker_config["checker_id"],
        "checker_version": checker_config["checker_version"],
        "inner_checker_sha256": checker_config["inner_checker_sha256"],
        "controller_entrypoint_sha256": checker_config["controller_entrypoint_sha256"],
        "checker_contract_sha256": checker_config["contract_sha256"],
        "checker_runtime_config_sha256": checker_config["runtime_config_sha256"],
        "container_image_digest": checker_config["container_image_digest"],
        "filesystem_network_process_attestation": checker_config[
            "filesystem_network_process_attestation"
        ],
        "controller_worker_separation_attestation": checker_config[
            "controller_worker_separation_attestation"
        ],
    }
    require(all(checker_response.get(key) == value
                for key, value in expected_response.items()),
            "smoke checker response differs from frozen checker config")
    require(checker_response.get("schema_version") == 1
            and checker_response.get("termination") == "completed"
            and type(checker_response.get("process_exit_code")) is int
            and checker_response["process_exit_code"] == 0,
            "smoke checker response is not a successful typed termination")
    measured_wall = checker_response.get("measured_wall_seconds")
    require(isinstance(measured_wall, (int, float))
            and not isinstance(measured_wall, bool)
            and 0 <= measured_wall
            <= int(checker_config["budgets"]["wall_clock_seconds"]) + 1,
            "smoke checker response wall time exceeds the frozen limit")
    artifacts = checker_response.get("artifact_manifest")
    require(isinstance(artifacts, list) and artifacts,
            "smoke checker response lacks its artifact manifest")
    for entry in artifacts:
        require(isinstance(entry, dict)
                and set(entry) == {"path", "bytes", "sha256"},
                "smoke checker artifact entry has an invalid schema")
        require(isinstance(entry["path"], str) and entry["path"]
                and isinstance(entry["bytes"], int) and entry["bytes"] >= 0
                and isinstance(entry["sha256"], str) and len(entry["sha256"]) == 64,
                "smoke checker artifact entry has invalid field types")
        relative = PurePosixPath(entry["path"])
        require(not relative.is_absolute() and ".." not in relative.parts
                and "\\" not in entry["path"],
                "smoke checker artifact path is unsafe")
        artifact_path = checker_root / entry["path"]
        try:
            artifact_path.resolve().relative_to(checker_root.resolve())
        except ValueError as error:
            raise SystemExit(
                "target-drift smoke failed: checker artifact resolves outside "
                "its published root"
            ) from error
        prepare.regular_unlinked_file(
            artifact_path, "smoke checker artifact", require_executable=False
        )
        require(artifact_path.stat().st_size == entry["bytes"]
                and prepare.sha256_file(artifact_path) == entry["sha256"],
                "smoke checker artifact differs from the sandbox manifest")
    artifact_aggregate = checker.artifact_aggregate(artifacts)
    require(artifact_aggregate == checker_response.get("artifact_aggregate_sha256")
            == checker_receipt.get("checker_artifact_aggregate_sha256")
            == state.get("checker_artifact_aggregate_sha256"),
            "smoke checker artifact aggregate hash chain differs")
    return {
        "smoke_run_id": planned["smoke_run_id"],
        "opaque_run_id": expected_opaque,
        "condition": planned["condition"],
        "status": state["status"],
        "checker_mode": state["checker_mode"],
        "result_eligible": False,
        "run_state_sha256": state_sha,
        "error": None,
    }


def validate_passed_ledger_against_runs(
    pack: Path, plan: dict[str, Any], plan_sha256: str,
    runs_root: Path, ledger: dict[str, Any],
) -> None:
    """Rebuild every record from operator/checker artifacts before accepting PASS."""
    if ledger.get("all_three_infrastructure_paths_passed") is not True:
        return
    rebuilt = [
        inspect_smoke_run(pack, plan, plan_sha256, planned, runs_root)
        for planned in plan["runs"]
    ]
    require(ledger.get("records") == rebuilt,
            "passed smoke ledger differs from independently rebuilt run evidence")


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--pack", type=Path, required=True)
    parser.add_argument("--plan", type=Path, required=True)
    parser.add_argument("--ledger", type=Path, required=True)
    args = parser.parse_args()
    pack = args.pack.resolve()
    plan_path = args.plan.resolve()
    plan, plan_sha256 = validate_plan(pack, plan_path)
    runs_root = canonical_runs_root(plan)
    ledger_path = args.ledger.resolve()
    attempt_path, _, lock_path = attempt_registry_paths(plan_sha256, runs_root)
    with exclusive_attempt_lock(lock_path):
        attempt_path = bind_single_attempt(plan_path, plan_sha256, runs_root, ledger_path)
        require(prepare.sha256_file(plan_path) == plan_sha256,
                "smoke plan changed before the first paid run")
        ledger = run_smoke(pack, plan, plan_sha256, runs_root)
        require(prepare.sha256_file(plan_path) == plan_sha256,
                "smoke plan changed while the attempt ran")
        validate_ledger(plan, plan_sha256, ledger)
        validate_passed_ledger_against_runs(
            pack, plan, plan_sha256, runs_root, ledger
        )
        if ledger_path.exists():
            existing, _ = load_bound(ledger_path)
            require(existing == ledger,
                    "existing smoke ledger differs from the recovered attempt")
        else:
            dump_new(ledger_path, ledger)
        attempt, _ = load_bound(attempt_path)
        attempt["status"] = "completed_result_ineligible_smoke"
        attempt["smoke_ledger_sha256"] = prepare.sha256_file(ledger_path)
        dump_atomic(attempt_path, attempt)
    print(
        "target-drift infrastructure smoke complete: "
        f"status={ledger['status']}, eligible=false, runs=3"
    )
    if not ledger["all_three_infrastructure_paths_passed"]:
        raise SystemExit(2)


if __name__ == "__main__":
    main()
