#!/usr/bin/env python3
"""Host controller for the isolated target-drift checker sandbox.

This process never elaborates model-authored Lean.  It verifies the sealed
pack/run chain, constructs a sanitized checker request and pristine base
snapshot, invokes one frozen sandbox command without a shell, validates the
returned artifact bundle, and only then publishes the checker result.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import os
import shutil
import signal
import stat
import subprocess
import sys
import tempfile
import threading
import time
from pathlib import Path
from typing import Any


TOOLS = Path(__file__).resolve().parent
sys.path.insert(0, str(TOOLS))

import check_target_drift_inner as inner  # noqa: E402
import prepare_target_drift_execution as prepare  # noqa: E402
import run_target_drift_execution as runner  # noqa: E402


class CheckerFailure(RuntimeError):
    pass


def require(condition: bool, message: str) -> None:
    if not condition:
        raise CheckerFailure(message)


def load(path: Path) -> dict[str, Any]:
    return json.loads(path.read_text(encoding="utf-8"))


def regular_file_bytes(path: Path, maximum_bytes: int, label: str) -> bytes:
    require(path.exists() and not path.is_symlink(), f"{label} is missing or linked")
    info = path.lstat()
    reparse = bool(getattr(info, "st_file_attributes", 0) & 0x400)
    require(stat.S_ISREG(info.st_mode) and not reparse and info.st_nlink == 1,
            f"{label} must be one unlinked regular file")
    require(0 < info.st_size <= maximum_bytes, f"{label} exceeds its byte bound")
    with path.open("rb") as stream:
        payload = stream.read(maximum_bytes + 1)
    require(len(payload) == info.st_size and len(payload) <= maximum_bytes,
            f"{label} changed or exceeded its byte bound while reading")
    return payload


def load_bounded_regular_json(path: Path, maximum_bytes: int, label: str) -> dict[str, Any]:
    payload = regular_file_bytes(path, maximum_bytes, label)
    value = json.loads(payload.decode("utf-8"))
    require(isinstance(value, dict), f"{label} must contain one JSON object")
    return value


def regular_file_sha256(path: Path, maximum_bytes: int, label: str) -> str:
    return hashlib.sha256(regular_file_bytes(path, maximum_bytes, label)).hexdigest()


def dump(path: Path, value: Any) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(
        json.dumps(value, indent=2, sort_keys=True, ensure_ascii=False) + "\n",
        encoding="utf-8",
    )


def dump_atomic(path: Path, value: Any) -> None:
    temporary = path.with_name(path.name + ".tmp")
    dump(temporary, value)
    os.replace(temporary, path)


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def canonical_bytes(value: Any) -> bytes:
    return json.dumps(
        value, sort_keys=True, separators=(",", ":"), ensure_ascii=False
    ).encode("utf-8")


def terminate_tree(process: subprocess.Popen[str]) -> None:
    if os.name == "nt":
        subprocess.run(
            ["taskkill", "/PID", str(process.pid), "/T", "/F"],
            stdout=subprocess.DEVNULL,
            stderr=subprocess.DEVNULL,
            check=False,
        )
    else:
        try:
            os.killpg(process.pid, signal.SIGKILL)
        except ProcessLookupError:
            pass


def render_command(template: list[str], replacements: dict[str, str]) -> list[str]:
    command = []
    for token in template:
        rendered = token
        for placeholder, value in replacements.items():
            rendered = rendered.replace(placeholder, value)
        require("{{" not in rendered and "}}" not in rendered,
                f"unresolved checker-sandbox placeholder in argv token: {rendered}")
        command.append(rendered)
    return command


def run_capped_process(
    command: list[str], cwd: Path, timeout: int, maximum_output_bytes: int,
) -> dict[str, Any]:
    started = time.monotonic()
    kwargs: dict[str, Any] = {}
    if os.name != "nt":
        kwargs["start_new_session"] = True
    process = subprocess.Popen(
        command,
        cwd=cwd,
        stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT,
        **kwargs,
    )
    require(process.stdout is not None, "failed to capture checker process output")
    captured = bytearray()
    output_overflow = threading.Event()

    def drain() -> None:
        while True:
            chunk = process.stdout.read(65536)
            if not chunk:
                return
            remaining = maximum_output_bytes - len(captured)
            if remaining > 0:
                captured.extend(chunk[:remaining])
            if len(chunk) > remaining:
                output_overflow.set()
                return

    reader = threading.Thread(target=drain, name="checker-stdout-drain", daemon=True)
    reader.start()
    timed_out = False
    try:
        while process.poll() is None:
            elapsed = time.monotonic() - started
            if output_overflow.is_set() or elapsed > timeout:
                timed_out = elapsed > timeout
                terminate_tree(process)
                break
            time.sleep(0.02)
        try:
            process.wait(timeout=5)
        except subprocess.TimeoutExpired:
            terminate_tree(process)
            process.wait(timeout=5)
    except BaseException:
        if process.poll() is None:
            terminate_tree(process)
            try:
                process.wait(timeout=5)
            except subprocess.TimeoutExpired:
                pass
        raise
    finally:
        reader.join(timeout=5)
        try:
            process.stdout.close()
        except OSError:
            pass
    return {
        "command": command,
        "exit_code": process.returncode,
        "timed_out": timed_out,
        "output_limit_exceeded": output_overflow.is_set(),
        "wall_seconds": round(time.monotonic() - started, 6),
        "output": captured.decode("utf-8", errors="replace"),
    }


def valid_cidfile(path: Path) -> str:
    require(path.is_file() and not path.is_symlink(), "checker cidfile is missing or linked")
    info = path.lstat()
    reparse = bool(getattr(info, "st_file_attributes", 0) & 0x400)
    require(stat.S_ISREG(info.st_mode) and not reparse and info.st_nlink == 1
            and info.st_size <= 256,
            "checker cidfile is not one small regular file")
    lines = path.read_text(encoding="ascii").splitlines()
    require(len(lines) == 1 and lines[0]
            and all(character.isalnum() or character in "_.-" for character in lines[0]),
            "checker cidfile contains an unsafe container identifier")
    return lines[0]


def run_sandbox(
    command: list[str], cleanup_command: list[str], inspect_command: list[str],
    cleanup_by_label_command: list[str], inspect_by_label_command: list[str],
    cwd: Path, timeout: int, maximum_output_bytes: int, cidfile: Path,
    inspect_absent_exit_code: int,
) -> dict[str, Any]:
    require(not cidfile.exists(), "checker cidfile must not pre-exist")
    lifecycle_limit = min(maximum_output_bytes, 262144)
    lifecycle_timeout = min(30, max(5, timeout))
    lifecycle_errors: list[str] = []
    process: dict[str, Any] | None = None
    launch_error: BaseException | None = None

    def lifecycle_command(argv: list[str], label: str) -> dict[str, Any]:
        try:
            return run_capped_process(argv, cwd, lifecycle_timeout, lifecycle_limit)
        except (OSError, subprocess.SubprocessError) as error:
            lifecycle_errors.append(f"checker {label} could not run: {type(error).__name__}: {error}")
            return {
                "command": argv, "exit_code": -1, "timed_out": False,
                "output_limit_exceeded": False, "wall_seconds": 0.0, "output": "",
            }

    lifecycle: dict[str, Any] = {}

    def bounded_diagnostic(record: dict[str, Any] | None, label: str) -> str:
        if record is None:
            return f"{label}: no process record"
        output = str(record.get("output", ""))
        # The process reader has already enforced the configured byte cap.  Keep
        # the exception itself small as well so that an always-uploaded attempt
        # log remains useful without becoming another unbounded artifact.
        if len(output) > 2048:
            output = output[-2048:]
        return (
            f"{label}: exit={record.get('exit_code')}, "
            f"timed_out={record.get('timed_out')}, "
            f"output_limit_exceeded={record.get('output_limit_exceeded')}, "
            f"output={output!r}"
        )

    def close_route(name: str, inspect_argv: list[str], cleanup_argv: list[str]) -> None:
        before = lifecycle_command(inspect_argv, f"{name} pre-cleanup inspect")
        present = before["exit_code"] == 0
        absent = before["exit_code"] == inspect_absent_exit_code
        if before["timed_out"] or before["output_limit_exceeded"] or not (present or absent):
            lifecycle_errors.append(f"checker {name} pre-cleanup state is unknown")
        cleanup: dict[str, Any] | None = None
        if present or not absent:
            cleanup = lifecycle_command(cleanup_argv, f"{name} cleanup")
            if cleanup["exit_code"] != 0 or cleanup["timed_out"] \
                    or cleanup["output_limit_exceeded"]:
                lifecycle_errors.append(f"checker {name} cleanup did not complete")
        after = lifecycle_command(inspect_argv, f"{name} post-cleanup inspect")
        if after["exit_code"] != inspect_absent_exit_code \
                or after["timed_out"] or after["output_limit_exceeded"]:
            lifecycle_errors.append(f"checker {name} absence could not be proved")
        lifecycle[name] = {"inspect_before": before, "cleanup": cleanup, "inspect_after": after}

    try:
        process = run_capped_process(command, cwd, timeout, maximum_output_bytes)
    except BaseException as error:
        launch_error = error
    finally:
        cidfile_valid = True
        try:
            valid_cidfile(cidfile)
        except CheckerFailure as error:
            cidfile_valid = False
            lifecycle_errors.append(str(error))
        close_route("cid", inspect_command, cleanup_command)
        close_route("label", inspect_by_label_command, cleanup_by_label_command)

    if launch_error is not None:
        lifecycle_errors.append(
            f"checker launch/monitor failed: {type(launch_error).__name__}: {launch_error}"
        )
    if lifecycle_errors:
        diagnostics = [bounded_diagnostic(process, "launch")]
        for route, records in lifecycle.items():
            diagnostics.append(bounded_diagnostic(
                records.get("inspect_before"), f"{route} inspect-before"
            ))
            diagnostics.append(bounded_diagnostic(
                records.get("cleanup"), f"{route} cleanup"
            ))
            diagnostics.append(bounded_diagnostic(
                records.get("inspect_after"), f"{route} inspect-after"
            ))
        raise CheckerFailure(
            "; ".join(lifecycle_errors) + "\n" + "\n".join(diagnostics)
        )
    require(process is not None, "checker sandbox process record is missing")
    return {
        **process,
        "cidfile_container_id": valid_cidfile(cidfile) if cidfile_valid else None,
        "lifecycle": lifecycle,
        "lifecycle_verified_absent": True,
    }


def require_adapter_artifacts_unchanged(operator: Path, receipt: dict[str, Any]) -> None:
    adapter = operator / "adapter"
    for name, expected in receipt["adapter_artifact_sha256"].items():
        path = adapter / name
        require(path.is_file(), f"agent adapter artifact missing: {name}")
        require(sha256(path) == expected, f"agent adapter artifact changed: {name}")


def validate_workflow_artifacts(output_dir: Path, job: dict[str, Any]) -> None:
    payload = load(output_dir / "workflow-compliance.json")
    require(payload.get("schema_version") == 1,
            "workflow-compliance schema_version must be 1")
    require(payload.get("opaque_run_id") == job["opaque_run_id"],
            "workflow-compliance run id mismatch")
    contract = job["result_contract"]
    require(payload.get("workflow_id") == contract["workflow_id"],
            "workflow-compliance id differs from the frozen workflow")
    evidence = payload.get("evidence_files")
    require(isinstance(evidence, list), "workflow-compliance evidence_files must be a list")
    require(all(isinstance(item, dict) and set(item) == {"path", "sha256"}
                for item in evidence), "invalid workflow-compliance evidence entry")
    require([item["path"] for item in evidence] == contract["workflow_evidence_files"],
            "workflow-compliance paths differ from the frozen contract")
    for item in evidence:
        path = output_dir / item["path"]
        require(path.is_file(), f"workflow artifact is missing: {item['path']}")
        require(sha256(path) == item["sha256"],
                f"workflow artifact hash mismatch: {item['path']}")


def self_verify(pack: Path, config: dict[str, Any]) -> None:
    expected = {
        Path(__file__).resolve(): config["posthoc_checker"]["driver_sha256"],
        Path(inner.__file__).resolve(): config["posthoc_checker"]["inner_checker_sha256"],
        Path(prepare.__file__).resolve(): config["sealed_agent_view"]["materializer_sha256"],
        Path(runner.__file__).resolve(): config["sealed_agent_view"]["run_preparer_sha256"],
    }
    for current, digest in expected.items():
        sealed = pack / "execution_code" / current.name
        require(sealed.is_file(), f"sealed execution code is missing: {current.name}")
        require(sha256(current) == digest,
                f"invoked execution code differs from frozen hash: {current.name}")
        require(sha256(sealed) == digest,
                f"sealed execution code differs from frozen hash: {current.name}")


def checker_attempt_id(
    aggregate: str, opaque_run_id: str, execution_receipt_sha256: str,
    driver_sha256: str, inner_sha256: str, runtime_config_sha256: str,
    attempt_number: int,
) -> str:
    payload = "\0".join((
        aggregate, opaque_run_id, execution_receipt_sha256,
        driver_sha256, inner_sha256, runtime_config_sha256, str(attempt_number),
    )).encode("utf-8")
    return f"CHK-{hashlib.sha256(payload).hexdigest()[:24]}-{attempt_number:02d}"


def regular_artifact_manifest(root: Path, maximum_bytes: int) -> list[dict[str, Any]]:
    require(root.is_dir(), "checker sandbox output directory is missing")
    entries = []
    total = 0
    for path in sorted(root.rglob("*")):
        relative = path.relative_to(root).as_posix()
        info = path.lstat()
        reparse = bool(getattr(info, "st_file_attributes", 0) & 0x400)
        require(not stat.S_ISLNK(info.st_mode) and not reparse,
                f"checker sandbox output contains a link/reparse point: {relative}")
        require(path.is_dir() or stat.S_ISREG(info.st_mode),
                f"checker sandbox output contains a special file: {relative}")
        if path.is_dir():
            continue
        require(info.st_nlink == 1,
                f"checker sandbox output contains a multiply linked file: {relative}")
        total += info.st_size
        require(total <= maximum_bytes, "checker sandbox output exceeds frozen byte budget")
        entries.append({"path": relative, "bytes": info.st_size, "sha256": sha256(path)})
    require(entries, "checker sandbox returned no artifacts")
    return entries


def artifact_aggregate(entries: list[dict[str, Any]]) -> str:
    digest = hashlib.sha256()
    for entry in entries:
        payload = canonical_bytes(entry)
        digest.update(len(payload).to_bytes(8, "big"))
        digest.update(payload)
    return digest.hexdigest()


def copy_artifacts(source: Path, destination: Path, manifest: list[dict[str, Any]]) -> None:
    destination.mkdir()
    for entry in manifest:
        target = destination / entry["path"]
        target.parent.mkdir(parents=True, exist_ok=True)
        shutil.copyfile(source / entry["path"], target)
        require(sha256(target) == entry["sha256"],
                f"checker artifact changed while publishing: {entry['path']}")


def typed_worker_record(record: Any, label: str) -> dict[str, Any]:
    require(isinstance(record, dict)
            and set(record) == {"command", "exit_code", "timed_out", "wall_seconds"},
            f"{label} worker record has the wrong schema")
    require(isinstance(record["command"], list) and record["command"]
            and all(isinstance(item, str) and item for item in record["command"]),
            f"{label} worker command is malformed")
    require(type(record["exit_code"]) is int and type(record["timed_out"]) is bool
            and isinstance(record["wall_seconds"], (int, float))
            and not isinstance(record["wall_seconds"], bool)
            and record["wall_seconds"] >= 0,
            f"{label} worker outcome types are malformed")
    return record


def successful_worker(record: Any) -> bool:
    return (
        isinstance(record, dict)
        and isinstance(record.get("exit_code"), int)
        and not isinstance(record.get("exit_code"), bool)
        and record["exit_code"] == 0
        and record.get("timed_out") is False
    )


def validate_checker_result(
    result: dict[str, Any], request: dict[str, Any], opaque_run_id: str,
    attempt_id: str,
) -> None:
    expected_fields = {
        "schema_version", "opaque_run_id", "checker_attempt_id", "checker_pass",
        "changed_files", "deleted_files", "forbidden_lean_hits",
        "replay_forbidden_lean_hits", "replay_changed_files", "replay_deleted_files",
        "patch_check", "patch_apply", "replayed_content_matches_completed_workspace",
        "post_worker_content_unchanged", "public_declarations_absent_from_frozen_base",
        "cache_prelude", "neutral_build", "neutral_canary", "public_declarations",
        "axiom_dependencies", "unexpected_axioms", "artifact_replay_success",
        "workflow_compliance_pass", "execution_usage", "sealed_pack_sha256",
        "execution_receipt_sha256", "completed_agent_manifest_sha256",
        "agent_claimed_status", "claim_consistent_with_checker", "inner_checker_sha256",
        "checker_contract_sha256", "container_image_digest",
        "checker_runtime_config_sha256",
    }
    require(set(result) == expected_fields, "checker-result schema fields differ from contract")
    require(result["schema_version"] == 1, "checker-result schema_version must be 1")
    require(result["opaque_run_id"] == opaque_run_id
            and result["checker_attempt_id"] == attempt_id,
            "checker result identity mismatch")
    bool_fields = (
        "checker_pass", "replayed_content_matches_completed_workspace",
        "post_worker_content_unchanged", "public_declarations_absent_from_frozen_base",
        "artifact_replay_success", "workflow_compliance_pass",
        "claim_consistent_with_checker",
    )
    require(all(type(result[field]) is bool for field in bool_fields),
            "checker-result pass/invariant fields must be literal booleans")
    list_fields = (
        "changed_files", "deleted_files", "replay_changed_files", "replay_deleted_files",
        "forbidden_lean_hits", "replay_forbidden_lean_hits", "public_declarations",
        "axiom_dependencies", "unexpected_axioms",
    )
    require(all(isinstance(result[field], list) for field in list_fields),
            "checker-result list field has the wrong type")
    require(result["changed_files"] == result["replay_changed_files"]
            and result["deleted_files"] == result["replay_deleted_files"]
            and result["forbidden_lean_hits"] == result["replay_forbidden_lean_hits"],
            "checker-result replay ledgers disagree")
    declarations = request["public_declarations"]
    patch_check = typed_worker_record(result["patch_check"], "patch check")
    require(len(patch_check["command"]) == 4
            and patch_check["command"][:3] == ["git", "apply", "--check"],
            "patch-check command differs from the sealed replay route")
    patch_check_success = successful_worker(patch_check)
    require((result["patch_apply"] is None) is (not patch_check_success),
            "patch apply presence disagrees with patch-check success")
    patch_apply_success = False
    if result["patch_apply"] is not None:
        patch_apply = typed_worker_record(result["patch_apply"], "patch apply")
        require(len(patch_apply["command"]) == 3
                and patch_apply["command"][:2] == ["git", "apply"],
                "patch-apply command differs from the sealed replay route")
        patch_apply_success = successful_worker(patch_apply)
    require(not result["replayed_content_matches_completed_workspace"]
            or (patch_check_success and patch_apply_success),
            "replayed-content success lacks successful patch check/application")
    build = typed_worker_record(result["neutral_build"], "neutral build")
    expected_build = [*request["worker_command_prefix"], "lake", "build"]
    require(build["command"] == expected_build,
            "neutral build command differs from the frozen worker route")
    require((result["neutral_canary"] is not None) is bool(declarations),
            "declaration canary presence must match public declarations")
    canary_success = not declarations
    if declarations:
        canary = typed_worker_record(result["neutral_canary"], "neutral canary")
        expected_prefix = [*request["worker_command_prefix"], "lake", "env", "lean"]
        require(canary["command"][:len(expected_prefix)] == expected_prefix
                and len(canary["command"]) == len(expected_prefix) + 1
                and canary["command"][-1].endswith("NeutralDeclarationCanary.lean"),
                "neutral canary command differs from the frozen worker route")
        canary_success = successful_worker(canary)
    require((result["cache_prelude"] is not None)
            is bool(request["cache_prelude_argv"]),
            "cache-prelude record presence differs from the request")
    if result["cache_prelude"] is not None:
        cache = typed_worker_record(result["cache_prelude"], "cache prelude")
        require(cache["command"] == request["cache_prelude_argv"],
                "cache-prelude command differs from the request")
    require(all(isinstance(item, str) for item in result["axiom_dependencies"])
            and all(isinstance(item, str) for item in result["unexpected_axioms"]),
            "checker axiom ledgers must contain strings")
    require(result["axiom_dependencies"] == sorted(set(result["axiom_dependencies"]))
            and result["unexpected_axioms"] == sorted(set(result["unexpected_axioms"])),
            "checker axiom ledgers must be sorted and unique")
    expected_unexpected = sorted(
        set(result["axiom_dependencies"]) - set(request["allowed_axioms"])
    )
    require(result["unexpected_axioms"] == expected_unexpected,
            "unexpected-axiom ledger is inconsistent")
    require(bool(declarations) or not result["axiom_dependencies"],
            "axiom dependencies require a declaration canary")
    derived_replay = (
        result["replayed_content_matches_completed_workspace"]
        and successful_worker(build)
        and canary_success
        and result["post_worker_content_unchanged"]
        and not result["forbidden_lean_hits"]
        and not result["deleted_files"]
        and not result["unexpected_axioms"]
    )
    require(result["artifact_replay_success"] is derived_replay,
            "checker artifact-replay invariant is inconsistent")
    derived_pass = derived_replay and result["public_declarations_absent_from_frozen_base"]
    require(result["checker_pass"] is derived_pass,
            "checker pass is inconsistent with replay/base-absence evidence")
    require(result["workflow_compliance_pass"] is True,
            "checker result lost the frozen workflow-compliance gate")
    expected_claim = request["final_status"] != "compiled" or derived_pass
    require(result["claim_consistent_with_checker"] is expected_claim,
            "checker claim-consistency invariant is inconsistent")
    bindings = {
        "sealed_pack_sha256": request["sealed_pack_sha256"],
        "execution_receipt_sha256": request["execution_receipt_sha256"],
        "completed_agent_manifest_sha256": request["completed_agent_manifest_sha256"],
        "agent_claimed_status": request["final_status"],
        "public_declarations": request["public_declarations"],
        "inner_checker_sha256": request["inner_checker_sha256"],
        "checker_contract_sha256": request["checker_contract_sha256"],
        "container_image_digest": request["container_image_digest"],
        "checker_runtime_config_sha256": request["checker_runtime_config_sha256"],
    }
    for key, value in bindings.items():
        require(result[key] == value, f"checker-result binding mismatch: {key}")


def record_terminal_failure(
    state_path: Path, state: dict[str, Any], attempt_dir: Path,
    attempt_id: str, reason: str,
) -> None:
    receipt = {
        "schema_version": 1,
        "checker_attempt_id": attempt_id,
        "opaque_run_id": state["opaque_run_id"],
        "status": "checker_terminal_failure",
        "reason": reason,
    }
    dump(attempt_dir / "terminal-failure.json", receipt)
    state.update({
        "status": "checker_terminal_failure",
        "result_eligible": False,
        "last_checker_attempt_id": attempt_id,
        "checker_terminal_failure_sha256": sha256(attempt_dir / "terminal-failure.json"),
    })
    dump_atomic(state_path, state)


def checked_state_for(
    job: dict[str, Any], checker_mode: str,
    provider_runtime_kind: str, adapter_termination: str,
) -> tuple[str, bool]:
    """Classify a successful checker run without promoting smoke data to results."""
    purpose = job.get("execution_purpose")
    declared_eligible = job.get("primary_result_eligible")
    require(purpose in runner.EXECUTION_PURPOSES, "unknown job execution purpose")
    require(isinstance(declared_eligible, bool),
            "job primary-result eligibility must be literal boolean")
    if checker_mode != "production":
        require(purpose == runner.PRIMARY_EXECUTION_PURPOSE,
                "excluded fixture is reserved for primary plumbing checks")
        return "checked_fixture_nonexperimental", False
    require(provider_runtime_kind == "codex_cli",
            "production-checked evidence requires a real codex_cli provider runtime")
    require(adapter_termination == "completed",
            "production-checked evidence requires completed provider termination")
    if purpose == runner.SMOKE_EXECUTION_PURPOSE:
        require(declared_eligible is False,
                "smoke job cannot declare primary-result eligibility")
        return "checked_smoke_nonexperimental", False
    require(declared_eligible is True,
            "primary job must declare primary-result eligibility")
    return "checked", True


def preflight(pack: Path, run_dir: Path) -> dict[str, Any]:
    prepare.verify_pack(pack)
    config = load(pack / "execution_config.json")
    require(config["execution_status"] == "frozen_ready", "checker requires frozen pack")
    self_verify(pack, config)
    operator = run_dir / "operator"
    agent = run_dir / "agent"
    workspace = agent / "workspace"
    output_dir = agent / "output"
    require(workspace.is_dir() and output_dir.is_dir(), "completed agent view is missing")
    job_path = operator / "job.json"
    state_path = operator / "run_state.json"
    receipt_path = operator / "execution-receipt.json"
    job = load(job_path)
    state = load(state_path)
    receipt = load(receipt_path)
    require(state["status"] == "executed_unchecked",
            "run is not available for neutral checking")
    aggregate = (pack / "aggregate.sha256").read_text(encoding="ascii").strip()
    require(state["sealed_pack_sha256"] == receipt["sealed_pack_sha256"] == aggregate,
            "run artifacts name different sealed packs")
    require(job["opaque_run_id"] == state["opaque_run_id"] == receipt["opaque_run_id"],
            "opaque run identifiers differ")
    require(job.get("execution_purpose") == state.get("execution_purpose")
            == receipt.get("execution_purpose"),
            "execution-purpose bindings differ")
    require(job.get("primary_result_eligible")
            is state.get("primary_result_eligible")
            is receipt.get("primary_result_eligible"),
            "primary-result eligibility bindings differ")
    require(job.get("smoke_plan_sha256") == state.get("smoke_plan_sha256")
            == receipt.get("smoke_plan_sha256"),
            "smoke-plan bindings differ")
    require(state["execution_receipt_sha256"] == sha256(receipt_path),
            "execution receipt hash mismatch")
    require(state["prepared_job_sha256"] == receipt["prepared_job_sha256"] == sha256(job_path),
            "prepared job hash mismatch")
    workspace_manifest_path = operator / "workspace_manifest.json"
    require(state["workspace_manifest_sha256"] == receipt["workspace_manifest_sha256"]
            == sha256(workspace_manifest_path), "workspace manifest hash mismatch")
    require_adapter_artifacts_unchanged(operator, receipt)
    require(runner.manifest_sha256(runner.file_manifest(agent))
            == state["completed_agent_manifest_sha256"]
            == receipt["completed_agent_manifest_sha256"],
            "agent view changed after execution")
    require(receipt["protected_input_hashes"]["prompt.md"] == sha256(agent / "prompt.md")
            == job["prompt_sha256"], "prompt changed after execution")
    require(receipt["protected_input_hashes"]["source/source.pdf"]
            == sha256(agent / "source" / "source.pdf") == job["source_sha256"],
            "source packet changed after execution")
    for name in job["result_contract"]["required_files"]:
        require((output_dir / name).is_file(), f"required agent output is missing: {name}")
    result = load(output_dir / "result.json")
    require(result.get("schema_version") == 1, "result schema_version must be 1")
    require(result.get("opaque_run_id") == job["opaque_run_id"], "result run id mismatch")
    require(result.get("final_status") in {
        "compiled", "partial", "source_amended", "source_rejected",
        "library_blocked", "mathematically_blocked", "counterexample",
        "budget_exhausted", "infrastructure_failure",
    }, "unknown agent final status")
    adapter_response = load(operator / "adapter" / "response.json")
    if config["posthoc_checker"]["mode"] == "production":
        require(config["execution_adapter"]["provider_runtime"]["kind"] == "codex_cli",
                "production checker requires a real codex_cli provider runtime")
        invocations = adapter_response.get("model_invocations")
        require(isinstance(invocations, list) and bool(invocations)
                and all(invocation.get("transport") == "codex_cli"
                        and invocation.get("usage_observed") is True
                        for invocation in invocations),
                "production checker requires a real codex_cli invocation with observed usage")
    require(adapter_response.get("termination") == "completed",
            "neutral checking requires a completed provider run")
    termination_status = {
        "budget_exhausted": "budget_exhausted",
        "infrastructure_failure": "infrastructure_failure",
    }
    if adapter_response["termination"] in termination_status:
        require(result["final_status"] == termination_status[adapter_response["termination"]],
                "agent final status conflicts with adapter termination")
    else:
        require(result["final_status"] not in {"budget_exhausted", "infrastructure_failure"},
                "agent final status conflicts with completed adapter response")
    require("public_declarations" in result,
            "result contract requires public_declarations even when empty")
    declarations = result["public_declarations"]
    require(isinstance(declarations, list) and all(isinstance(item, str) for item in declarations),
            "public_declarations must be a string list")
    require(all(inner.DECLARATION_NAME.fullmatch(item) for item in declarations),
            "public_declarations contains an unsafe Lean identifier")
    require(len(declarations) == len(set(declarations)), "duplicate public declaration")
    require(result["final_status"] != "compiled" or bool(declarations),
            "compiled result requires at least one public declaration")
    require(isinstance(result.get("primary_grader_rationale"), str)
            and bool(result["primary_grader_rationale"].strip()),
            "result requires a nonempty primary_grader_rationale")
    require("source_amendment" not in result,
            "source amendment text must live only in source-amendment.md")
    amendment = output_dir / "source-amendment.md"
    require((result["final_status"] == "source_amended") == amendment.is_file(),
            "source_amended status and source-amendment.md presence disagree")
    if amendment.is_file():
        require(bool(amendment.read_text(encoding="utf-8").strip()),
                "source-amendment.md must be nonempty")
    validate_workflow_artifacts(output_dir, job)
    return {
        "config": config,
        "operator": operator,
        "agent": agent,
        "workspace": workspace,
        "output_dir": output_dir,
        "job": job,
        "state": state,
        "state_path": state_path,
        "receipt": receipt,
        "receipt_path": receipt_path,
        "adapter_response": adapter_response,
        "result": result,
        "declarations": declarations,
        "aggregate": aggregate,
    }


def begin_checker_attempt(pack: Path, run_dir: Path) -> dict[str, Any]:
    """Create the sole fail-closed checker attempt before full preflight."""
    operator = run_dir / "operator"
    state_path = operator / "run_state.json"
    job_path = operator / "job.json"
    config = load(pack / "execution_config.json")
    state = load(state_path)
    job = load(job_path)
    require(isinstance(config, dict) and isinstance(state, dict) and isinstance(job, dict),
            "checker attempt metadata must be JSON objects")
    require(state.get("status") == "executed_unchecked",
            "checker retry is forbidden after a terminal checker state")
    checker = config["posthoc_checker"]
    aggregate = (pack / "aggregate.sha256").read_text(encoding="ascii").strip()
    attempts_root = operator / "checker-attempts"
    attempts_root.mkdir(exist_ok=True)
    require(not any(path.is_dir() for path in attempts_root.iterdir()),
            "the frozen checker retry limit is zero")
    attempt_number = 1
    attempt_id = checker_attempt_id(
        aggregate, job["opaque_run_id"], state["execution_receipt_sha256"], checker["driver_sha256"],
        checker["inner_checker_sha256"], checker["runtime_config_sha256"], attempt_number,
    )
    attempt_dir = attempts_root / attempt_id
    require(not attempt_dir.exists(), "checker attempt directory already exists")
    attempt_dir.mkdir()
    return {
        "config": config, "checker": checker, "operator": operator,
        "state": state, "state_path": state_path, "job": job,
        "aggregate": aggregate, "attempt_id": attempt_id, "attempt_dir": attempt_dir,
    }


def execute(pack: Path, run_dir: Path) -> bool:
    attempt = begin_checker_attempt(pack, run_dir)
    attempt_id = attempt["attempt_id"]
    attempt_dir = attempt["attempt_dir"]

    try:
        context = preflight(pack, run_dir)
        config = context["config"]
        checker = config["posthoc_checker"]
        operator = context["operator"]
        require(context["aggregate"] == attempt["aggregate"]
                and context["job"]["opaque_run_id"] == attempt["job"]["opaque_run_id"]
                and context["state"]["execution_receipt_sha256"]
                == attempt["state"]["execution_receipt_sha256"],
                "checker preflight identity changed after attempt creation")
        baseline_payload = load(operator / "workspace_manifest.json")
        baseline_manifest = baseline_payload["files"]
        expected_manifest = runner.file_manifest(context["workspace"])
        policy = load(pack / "resource_policy.json")
        with tempfile.TemporaryDirectory(prefix="abrl-checker-base-") as temporary:
            base_snapshot = Path(temporary) / "base"
            paths = runner.selected_paths(
                config["workspace_base_commit"], policy, context["job"]["condition"]
            )
            runner.extract_git_archive(config["workspace_base_commit"], paths, base_snapshot)
            require(runner.file_manifest(base_snapshot) == baseline_manifest,
                    "fresh base snapshot differs from the prepared workspace manifest")

            patch_path = context["output_dir"] / "lean-diff.patch"
            request = {
                "schema_version": 1,
                "suite_id": config["suite_id"],
                "opaque_run_id": context["job"]["opaque_run_id"],
                "checker_attempt_id": attempt_id,
                "checker_attempt_label": attempt_id,
                "sealed_pack_sha256": context["aggregate"],
                "execution_receipt_sha256": context["state"]["execution_receipt_sha256"],
                "completed_agent_manifest_sha256": context["receipt"][
                    "completed_agent_manifest_sha256"
                ],
                "baseline_manifest": baseline_manifest,
                "baseline_manifest_sha256": runner.manifest_sha256(baseline_manifest),
                "expected_completed_workspace_manifest": expected_manifest,
                "expected_completed_workspace_manifest_sha256": runner.manifest_sha256(
                    expected_manifest
                ),
                "patch_sha256": sha256(patch_path),
                "result_sha256": sha256(context["output_dir"] / "result.json"),
                "public_declarations": context["declarations"],
                "final_status": context["result"]["final_status"],
                "allowed_axioms": sorted(inner.ALLOWED_AXIOMS),
                "checker_id": checker["checker_id"],
                "checker_version": checker["checker_version"],
                "inner_checker_sha256": checker["inner_checker_sha256"],
                "controller_entrypoint_sha256": checker[
                    "controller_entrypoint_sha256"
                ],
                "checker_contract_sha256": checker["contract_sha256"],
                "checker_runtime_config_sha256": checker["runtime_config_sha256"],
                "container_image_digest": checker["container_image_digest"],
                "filesystem_network_process_attestation": checker[
                    "filesystem_network_process_attestation"
                ],
                "controller_worker_separation_attestation": checker[
                    "controller_worker_separation_attestation"
                ],
                "checker_cache_manifest_sha256": checker.get(
                    "checker_cache_manifest_sha256", "excluded-fixture-no-image-cache"
                ),
                "resource_limits": checker["budgets"],
                "worker_command_prefix": checker["worker_command_prefix"],
                "cache_prelude_argv": checker["cache_prelude_argv"],
                "sandbox_mode": checker["mode"],
                "workflow_compliance_pass": True,
                "execution_usage": context["receipt"]["usage"],
            }
            checker_contract = load(pack / "checker_sandbox_contract.json")
            forbidden_request_fields = set(
                checker_contract["request_schema"]["forbidden_semantic_fields"]
            )
            required_request_fields = set(checker_contract["request_schema"]["required"])
            require(set(request) == required_request_fields,
                    "sanitized checker request fields differ from the frozen contract")
            require(not (forbidden_request_fields & set(request)),
                    "sanitized checker request contains forbidden semantic fields")
            request_path = attempt_dir / "request.json"
            response_root = attempt_dir / "sandbox-response-output"
            response_root.mkdir()
            response_path = response_root / "response.json"
            output_path = attempt_dir / "sandbox-output"
            cidfile = attempt_dir / "container.cid"
            dump(request_path, request)
            output_path.mkdir()
            protected_file_limit = max(
                int(checker["budgets"]["maximum_output_bytes"]),
                int(checker["budgets"]["maximum_response_bytes"]),
            )
            request_sha256_before = regular_file_sha256(
                request_path, protected_file_limit, "checker request before sandbox"
            )
            base_manifest_before = runner.file_manifest(base_snapshot)
            patch_sha256_before = regular_file_sha256(
                patch_path, protected_file_limit, "submitted patch before sandbox"
            )
            result_sha256_before = regular_file_sha256(
                context["output_dir"] / "result.json", protected_file_limit,
                "agent result before sandbox",
            )
            replacements = {
                "{{CHECKER_REQUEST_PATH}}": str(request_path.resolve()),
                "{{BASE_SNAPSHOT_PATH}}": str(base_snapshot.resolve()),
                "{{PATCH_PATH}}": str(patch_path.resolve()),
                "{{CHECKER_OUTPUT_DIR}}": str(output_path.resolve()),
                "{{CHECKER_RESPONSE_PATH}}": str(response_path.resolve()),
                "{{CIDFILE}}": str(cidfile.resolve()),
                "{{CHECKER_ATTEMPT_LABEL}}": attempt_id,
                "{{CHECKER_IMAGE_DIGEST}}": checker["container_image_digest"],
            }
            command = render_command(checker["sandbox_command_argv"], replacements)
            cleanup = render_command(checker["sandbox_cleanup_argv"], replacements)
            inspect = render_command(checker["sandbox_inspect_argv"], replacements)
            cleanup_by_label = render_command(
                checker["sandbox_cleanup_by_label_argv"], replacements
            )
            inspect_by_label = render_command(
                checker["sandbox_inspect_by_label_argv"], replacements
            )
            process = run_sandbox(
                command, cleanup, inspect, cleanup_by_label, inspect_by_label, attempt_dir,
                int(checker["budgets"]["wall_clock_seconds"]),
                int(checker["budgets"]["maximum_output_bytes"]), cidfile,
                int(checker["inspect_absent_exit_code"]),
            )
            (attempt_dir / "process.log").write_text(process["output"], encoding="utf-8")
            for route, records in process["lifecycle"].items():
                for phase, record in records.items():
                    if record is not None:
                        (attempt_dir / f"lifecycle-{route}-{phase}.log").write_text(
                            record["output"], encoding="utf-8"
                        )
            require(not process["timed_out"], "checker sandbox timed out")
            require(not process["output_limit_exceeded"],
                    "checker sandbox stdout exceeded the frozen byte budget")
            require(process["exit_code"] == 0, "checker sandbox process failed")
            require(process["lifecycle_verified_absent"] is True,
                    "checker sandbox lifecycle was not proven closed")
            inner.require_plain_tree(base_snapshot, "host base snapshot after sandbox")
            require(regular_file_sha256(
                request_path, protected_file_limit, "checker request after sandbox"
            ) == request_sha256_before,
                    "checker request changed while sandbox ran")
            require(runner.file_manifest(base_snapshot) == base_manifest_before,
                    "checker base snapshot changed while sandbox ran")
            require(regular_file_sha256(
                patch_path, protected_file_limit, "submitted patch after sandbox"
            ) == patch_sha256_before,
                    "submitted patch changed while checker sandbox ran")
            require(regular_file_sha256(
                context["output_dir"] / "result.json", protected_file_limit,
                "agent result after sandbox",
            ) == result_sha256_before,
                    "agent result changed while checker sandbox ran")
            response = load_bounded_regular_json(
                response_path, int(checker["budgets"]["maximum_response_bytes"]),
                "checker sandbox response",
            )
            expected_response = {
                "opaque_run_id": context["job"]["opaque_run_id"],
                "checker_attempt_id": attempt_id,
                "checker_attempt_label": attempt_id,
                "request_sha256": request_sha256_before,
                "checker_id": checker["checker_id"],
                "checker_version": checker["checker_version"],
                "inner_checker_sha256": checker["inner_checker_sha256"],
                "controller_entrypoint_sha256": checker[
                    "controller_entrypoint_sha256"
                ],
                "checker_contract_sha256": checker["contract_sha256"],
                "checker_runtime_config_sha256": checker["runtime_config_sha256"],
                "container_image_digest": checker["container_image_digest"],
                "filesystem_network_process_attestation": checker[
                    "filesystem_network_process_attestation"
                ],
                "controller_worker_separation_attestation": checker[
                    "controller_worker_separation_attestation"
                ],
            }
            response_fields = {
                "schema_version", *expected_response.keys(), "termination",
                "checker_result_sha256", "artifact_manifest",
                "artifact_aggregate_sha256", "process_exit_code",
                "measured_wall_seconds",
            }
            require(set(response) == response_fields,
                    "checker sandbox response schema fields differ from contract")
            require(response.get("schema_version") == 1,
                    "checker sandbox response schema_version must be 1")
            for key, value in expected_response.items():
                require(response.get(key) == value,
                        f"checker sandbox response differs from frozen {key}")
            require(response.get("termination") == "completed",
                    "checker sandbox did not terminate as completed")
            require(type(response.get("process_exit_code")) is int
                    and response["process_exit_code"] == 0,
                    "checker sandbox response records a failed inner process")
            measured_wall = response.get("measured_wall_seconds")
            require(isinstance(measured_wall, (int, float))
                    and not isinstance(measured_wall, bool)
                    and 0 <= measured_wall
                    <= int(checker["budgets"]["wall_clock_seconds"]) + 1,
                    "checker sandbox response wall time exceeds the frozen limit")
            artifacts = regular_artifact_manifest(
                output_path, int(checker["budgets"]["maximum_output_bytes"])
            )
            require(response.get("artifact_manifest") == artifacts,
                    "checker sandbox artifact manifest mismatch")
            aggregate = artifact_aggregate(artifacts)
            require(response.get("artifact_aggregate_sha256") == aggregate,
                    "checker sandbox artifact aggregate mismatch")
            result_path = output_path / "checker-result.json"
            require(result_path.is_file(), "checker-result.json is missing")
            require(response.get("checker_result_sha256") == sha256(result_path),
                    "checker-result hash differs from sandbox response")
            checker_result = load(result_path)
            validate_checker_result(
                checker_result, request, context["job"]["opaque_run_id"], attempt_id
            )
            require(runner.manifest_sha256(runner.file_manifest(context["agent"]))
                    == context["receipt"]["completed_agent_manifest_sha256"],
                    "agent view changed while checker sandbox ran")
            require(patch_sha256_before == request["patch_sha256"],
                    "submitted patch changed while checker sandbox ran")
            require(result_sha256_before == request["result_sha256"],
                    "agent result changed while checker sandbox ran")

            published = operator / "checker"
            require(not published.exists(), "published checker directory already exists")
            temporary_publish = operator / f"checker.tmp-{attempt_id}"
            require(not temporary_publish.exists(), "temporary checker publish path exists")
            copy_artifacts(output_path, temporary_publish, artifacts)
            shutil.copyfile(response_path, temporary_publish / "sandbox-response.json")
            checked_status, result_eligible = checked_state_for(
                context["job"], checker["mode"],
                config["execution_adapter"]["provider_runtime"]["kind"],
                context["adapter_response"]["termination"],
            )
            checker_receipt = {
                "schema_version": 1,
                "opaque_run_id": context["job"]["opaque_run_id"],
                "checker_attempt_id": attempt_id,
                "checker_request_sha256": request_sha256_before,
                "sandbox_response_sha256": sha256(response_path),
                "checker_result_sha256": sha256(result_path),
                "checker_artifact_aggregate_sha256": aggregate,
                "checker_runtime_config_sha256": checker["runtime_config_sha256"],
                "isolation_probe_report_sha256": checker[
                    "isolation_probe_report_sha256"
                ],
                "checker_mode": checker["mode"],
                "execution_purpose": context["job"]["execution_purpose"],
                "result_eligible": result_eligible,
                "process": {key: value for key, value in process.items() if key != "output"},
            }
            dump(temporary_publish / "checker-execution-receipt.json", checker_receipt)
            os.replace(temporary_publish, published)
            published_response = published / "sandbox-response.json"
            published_result = published / "checker-result.json"
            published_receipt = published / "checker-execution-receipt.json"
            context["state"].update({
                "status": checked_status,
                "result_eligible": result_eligible,
                "checker_mode": checker["mode"],
                "checker_runtime_config_sha256": checker["runtime_config_sha256"],
                "isolation_probe_report_sha256": checker[
                    "isolation_probe_report_sha256"
                ],
                "checker_attempt_id": attempt_id,
                "checker_request_sha256": request_sha256_before,
                "sandbox_response_sha256": sha256(published_response),
                "checker_result_sha256": sha256(published_result),
                "checker_execution_receipt_sha256": sha256(published_receipt),
                "checker_artifact_aggregate_sha256": aggregate,
            })
            dump_atomic(context["state_path"], context["state"])
            print(
                f"isolated neutral checker {'PASS' if checker_result['checker_pass'] else 'FAIL'} "
                f"for {context['job']['opaque_run_id']}: attempt={attempt_id}"
            )
            return checker_result["checker_pass"] is True
    except (SystemExit, Exception) as error:
        reason = str(error)
        record_terminal_failure(
            attempt["state_path"], attempt["state"], attempt_dir, attempt_id, reason
        )
        raise CheckerFailure(reason) from error


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--pack", type=Path, required=True)
    parser.add_argument("--run-dir", type=Path, required=True)
    args = parser.parse_args()
    try:
        passed = execute(args.pack.resolve(), args.run_dir.resolve())
    except CheckerFailure as error:
        raise SystemExit(f"target-drift checker controller failed: {error}") from error
    raise SystemExit(0 if passed else 1)


if __name__ == "__main__":
    main()
