#!/usr/bin/env python3
"""Build the frozen 450-run completion ledger and enforce the no-imputation gate."""

from __future__ import annotations

import argparse
import hashlib
import json
import os
import stat
import sys
from collections import Counter
from pathlib import Path, PurePosixPath
from typing import Any


TOOLS = Path(__file__).resolve().parent
sys.path.insert(0, str(TOOLS))

import prepare_target_drift_execution as prepare  # noqa: E402
import run_target_drift_execution as runner  # noqa: E402
import check_target_drift_run as checker  # noqa: E402


ELIGIBLE_STATUS = "checked"
REQUIRED_CHECKED_STATE_HASH_FIELDS = (
    "prepared_job_sha256",
    "workspace_manifest_sha256",
    "execution_receipt_sha256",
    "checker_request_sha256",
    "checker_result_sha256",
    "checker_execution_receipt_sha256",
    "sandbox_response_sha256",
)
KNOWN_STATES = {
    "prepared_unrun",
    "terminal_operator_failure",
    "executed_unchecked",
    "checker_terminal_failure",
    "checked_fixture_nonexperimental",
    ELIGIBLE_STATUS,
}
LEDGER_STATES = KNOWN_STATES | {"not_materialized", "integrity_failure"}
POLICY_ID = "complete_450_no_replacement_no_imputation_v1"


def load(path: Path) -> dict[str, Any]:
    return json.loads(path.read_text(encoding="utf-8"))


def dump_new(path: Path, value: Any) -> None:
    require(not path.exists(), f"refusing to overwrite {path}")
    path.parent.mkdir(parents=True, exist_ok=True)
    with path.open("x", encoding="utf-8", newline="\n") as handle:
        json.dump(value, handle, indent=2, sort_keys=True, ensure_ascii=False)
        handle.write("\n")


def local_sha256_file(path: Path) -> str:
    """Hash verifier dependencies without trusting an imported verifier helper."""
    return hashlib.sha256(path.read_bytes()).hexdigest()


def require(condition: bool, message: str) -> None:
    if not condition:
        raise SystemExit(f"target-drift completion ledger failed: {message}")


def regular_json(path: Path, label: str) -> dict[str, Any]:
    try:
        info = path.lstat()
    except OSError as error:
        raise SystemExit(f"target-drift completion ledger failed: missing {label}: {error}") from error
    require(stat.S_ISREG(info.st_mode) and not path.is_symlink(), f"{label} is not a plain file")
    require(info.st_nlink == 1, f"{label} is hard-linked")
    attributes = getattr(info, "st_file_attributes", 0)
    reparse = getattr(stat, "FILE_ATTRIBUTE_REPARSE_POINT", 0x400)
    require(not (attributes & reparse), f"{label} is a reparse point")
    value = load(path)
    require(isinstance(value, dict), f"{label} must be a JSON object")
    return value


def policy_from_pack(pack: Path, config: dict[str, Any]) -> tuple[dict[str, Any], str]:
    policy_path = pack / "missing-run-policy.json"
    policy = regular_json(policy_path, "sealed missing-run policy")
    policy_sha256 = prepare.sha256_file(policy_path)
    configured = config["missing_run_policy"]
    retry_id = config["retry_policy"]["missing_run_policy"]
    require(policy.get("schema_version") == 1, "missing-run policy schema_version must be 1")
    require(policy.get("suite_id") == config["suite_id"], "missing-run policy suite mismatch")
    require(policy.get("policy_id") == configured.get("policy_id") == retry_id == POLICY_ID,
            "missing-run policy ID mismatch")
    require(policy_sha256 == configured.get("policy_sha256"),
            "sealed missing-run policy hash mismatch")
    require(policy.get("planned_run_count") == 450, "missing-run policy must cover 450 runs")
    require(policy.get("replacement_runs") == "forbidden", "replacement runs must be forbidden")
    require(policy.get("outcome_imputation") == "forbidden", "outcome imputation must be forbidden")
    require(policy.get("continuation_after_individual_failure")
            == "continue_remaining_preregistered_runs",
            "individual failures must not stop the remaining preregistered schedule")
    require(policy.get("schedule_order") == "sealed_presentation_order",
            "missing-run policy schedule order differs")
    require(policy.get("automatic_retry_after_terminal_state") == "forbidden",
            "missing-run policy terminal retry semantics differ")
    require(policy.get("result_eligible_state") == {
        "status": "checked", "result_eligible": True, "checker_mode": "production",
    }, "missing-run policy result-eligible state differs")
    require(policy.get("primary_analysis_gate")
            == "exactly_450_result_eligible_graded_records_and_zero_missing_runs",
            "unsupported primary analysis gate")
    require(policy.get("incomplete_run_action")
            == "write_hash_bound_completion_ledger_and_refuse_grading_and_inferential_analysis",
            "missing-run policy incomplete-run action differs")
    require(policy.get("incomplete_analysis_output")
            == "missingness_counts_only_no_effect_estimate_interval_pvalue_or_success_claim",
            "missing-run policy incomplete-analysis output differs")
    require(policy.get("missingness_dimensions") == [
        "state_status", "missing_reason", "condition", "requirement_variant",
    ], "missing-run policy missingness dimensions differ")
    require(set(policy.get("terminal_state_categories", {})) == LEDGER_STATES,
            "missing-run policy terminal-state categories differ")
    return policy, policy_sha256


def self_verify(pack: Path, config: dict[str, Any]) -> None:
    expected = config["missing_run_policy"]["completion_ledger_builder_sha256"]
    current = Path(__file__).resolve()
    sealed = pack / "execution_code" / current.name
    require(local_sha256_file(current) == expected,
            "invoked completion-ledger builder differs from frozen hash")
    require(local_sha256_file(sealed) == expected,
            "sealed completion-ledger builder differs from frozen hash")


def evidence_hashes(operator: Path, state: dict[str, Any]) -> dict[str, str]:
    status = state["status"]
    if status == ELIGIBLE_STATUS:
        for field in REQUIRED_CHECKED_STATE_HASH_FIELDS:
            expected = state.get(field)
            require(
                isinstance(expected, str)
                and len(expected) == 64
                and all(character in "0123456789abcdef" for character in expected),
                f"checked run state lacks a lowercase SHA-256 binding for {field}",
            )
    candidates: list[tuple[str, Path, str | None]] = [
        ("run_state", operator / "run_state.json", None),
        ("job", operator / "job.json", state.get("prepared_job_sha256")),
    ]
    if status == ELIGIBLE_STATUS:
        checker_attempt_id = state.get("checker_attempt_id")
        require(isinstance(checker_attempt_id, str) and checker_attempt_id,
                "checked run state lacks a checker attempt ID")
        candidates.extend([
            ("workspace_manifest", operator / "workspace_manifest.json",
             state.get("workspace_manifest_sha256")),
            ("checker_request",
             operator / "checker-attempts" / checker_attempt_id / "request.json",
             state.get("checker_request_sha256")),
        ])
    if status == "terminal_operator_failure":
        candidates.append((
            "operator_failure_receipt",
            operator / "operator-failure-receipt.json",
            state.get("operator_failure_receipt_sha256"),
        ))
    if status in {"executed_unchecked", "checker_terminal_failure", "checked_fixture_nonexperimental", "checked"}:
        candidates.append((
            "execution_receipt",
            operator / "execution-receipt.json",
            state.get("execution_receipt_sha256"),
        ))
    if status == "checker_terminal_failure":
        attempt = state.get("last_checker_attempt_id")
        require(isinstance(attempt, str) and attempt, "checker failure lacks an attempt ID")
        candidates.append((
            "checker_terminal_failure",
            operator / "checker-attempts" / attempt / "terminal-failure.json",
            state.get("checker_terminal_failure_sha256"),
        ))
    if status in {"checked_fixture_nonexperimental", "checked"}:
        candidates.extend([
            ("checker_result", operator / "checker" / "checker-result.json",
             state.get("checker_result_sha256")),
            ("checker_execution_receipt", operator / "checker" / "checker-execution-receipt.json",
             state.get("checker_execution_receipt_sha256")),
            ("sandbox_response", operator / "checker" / "sandbox-response.json",
             state.get("sandbox_response_sha256")),
        ])
    hashes: dict[str, str] = {}
    for name, path, expected in candidates:
        regular_json(path, name.replace("_", " "))
        actual = prepare.sha256_file(path)
        if expected is not None:
            require(actual == expected, f"{name} hash differs from run state")
        hashes[name] = actual
    return hashes


def _sha256_value(value: Any, label: str) -> str:
    require(
        isinstance(value, str)
        and len(value) == 64
        and all(character in "0123456789abcdef" for character in value),
        f"{label} is not a lowercase SHA-256 digest",
    )
    return value


def _manifest_entries(value: Any, label: str) -> list[dict[str, Any]]:
    require(isinstance(value, list), f"{label} must be a list")
    paths: list[str] = []
    for entry in value:
        require(
            isinstance(entry, dict)
            and set(entry) == {"path", "bytes", "sha256"}
            and isinstance(entry["path"], str)
            and entry["path"]
            and type(entry["bytes"]) is int
            and entry["bytes"] >= 0,
            f"{label} contains a malformed entry",
        )
        path = PurePosixPath(entry["path"])
        require(
            not path.is_absolute()
            and ".." not in path.parts
            and path.as_posix() == entry["path"],
            f"{label} contains an unsafe path",
        )
        _sha256_value(entry["sha256"], f"{label} entry hash")
        paths.append(entry["path"])
    require(paths == sorted(paths) and len(paths) == len(set(paths)),
            f"{label} paths must be sorted and unique")
    return value


def validate_checked_run_evidence(
    pack: Path, run_dir: Path, planned: dict[str, Any], aggregate: str,
    config: dict[str, Any],
) -> dict[str, Any]:
    """Re-derive the complete evidence chain for one result-eligible checked run.

    This function deliberately lives in the ledger module so both ledger creation
    and final grading use the same fail-closed semantic validation without a
    grading/checker import cycle.
    """
    operator = run_dir / "operator"
    agent = run_dir / "agent"
    workspace = agent / "workspace"
    output = agent / "output"
    job_path = operator / "job.json"
    state_path = operator / "run_state.json"
    workspace_manifest_path = operator / "workspace_manifest.json"
    receipt_path = operator / "execution-receipt.json"
    adapter = operator / "adapter"
    adapter_request_path = adapter / "request.json"
    adapter_response_path = adapter / "response.json"
    adapter_trace_path = adapter / "trace.jsonl"

    job = regular_json(job_path, "prepared job")
    state = regular_json(state_path, "run state")
    workspace_manifest = regular_json(
        workspace_manifest_path, "prepared workspace manifest"
    )
    receipt = regular_json(receipt_path, "execution receipt")
    adapter_request = regular_json(adapter_request_path, "adapter request")
    adapter_response = regular_json(adapter_response_path, "adapter response")

    semantic_id = planned["run_id"]
    opaque_id = runner.opaque_id("run", aggregate, semantic_id)
    require(job.get("schema_version") == 1 and job.get("suite_id") == config["suite_id"],
            "prepared job schema or suite differs")
    require(set(job) == {
        "schema_version", "suite_id", "opaque_run_id", "semantic_run_id",
        "source_primary_run_id", "execution_purpose", "primary_result_eligible",
        "smoke_plan_sha256", "condition", "replicate", "agent_mount",
        "prompt_path", "prompt_sha256", "source_sha256", "workspace_base_commit",
        "model", "pricing", "budgets", "retry_policy", "adapter_contract_sha256",
        "provider_runtime", "required_adapter_attestations", "result_contract", "status",
    }, "prepared job schema fields differ")
    require(job.get("semantic_run_id") == semantic_id,
            "prepared job names a different semantic run")
    require(job.get("source_primary_run_id") == semantic_id
            and job.get("status") == "prepared_unrun",
            "primary job source/status provenance differs")
    require(job.get("opaque_run_id") == state.get("opaque_run_id")
            == receipt.get("opaque_run_id") == opaque_id,
            "checked run opaque identity chain differs")
    require(job.get("condition") == planned["condition"]
            and job.get("replicate") == planned["replicate"],
            "prepared job differs from the sealed condition/replicate")
    require(job.get("execution_purpose") == state.get("execution_purpose")
            == receipt.get("execution_purpose") == runner.PRIMARY_EXECUTION_PURPOSE,
            "checked run is not a primary execution")
    require(job.get("primary_result_eligible") is True
            and state.get("primary_result_eligible") is True
            and receipt.get("primary_result_eligible") is True,
            "checked run is not primary-result-eligible")
    require(job.get("smoke_plan_sha256") is None
            and state.get("smoke_plan_sha256") is None
            and receipt.get("smoke_plan_sha256") is None,
            "checked primary run unexpectedly carries smoke provenance")
    require(state.get("status") == ELIGIBLE_STATUS
            and state.get("result_eligible") is True
            and state.get("checker_mode") == "production",
            "checked state is not production-result-eligible")
    require(state.get("sealed_pack_sha256") == receipt.get("sealed_pack_sha256")
            == aggregate, "checked run names a different sealed pack")

    adapter_config = config["execution_adapter"]
    checker_config = config["posthoc_checker"]
    require(adapter_config["provider_runtime"].get("kind") == "codex_cli",
            "checked run is not bound to the codex_cli provider")
    require(checker_config.get("mode") == "production",
            "checked run is not bound to the production checker")
    for current, expected in (
        (
            Path(prepare.__file__).resolve(),
            config["sealed_agent_view"]["materializer_sha256"],
        ),
        (
            Path(runner.__file__).resolve(),
            config["sealed_agent_view"]["run_preparer_sha256"],
        ),
        (Path(checker.__file__).resolve(), checker_config["driver_sha256"]),
        (Path(checker.inner.__file__).resolve(), checker_config["inner_checker_sha256"]),
    ):
        sealed = pack / "execution_code" / current.name
        require(current.is_file() and not current.is_symlink()
                and local_sha256_file(current) == expected,
                f"invoked evidence dependency differs from frozen hash: {current.name}")
        require(sealed.is_file() and not sealed.is_symlink()
                and local_sha256_file(sealed) == expected,
                f"sealed evidence dependency differs from frozen hash: {current.name}")
    require(job.get("workspace_base_commit") == config["workspace_base_commit"],
            "prepared job base commit differs from frozen config")
    require(job.get("agent_mount") == str(agent.resolve())
            and job.get("prompt_path") == str((agent / "prompt.md").resolve()),
            "prepared job agent/prompt paths differ from this run")
    for key, expected in (
        ("model", config["model"]),
        ("pricing", config["pricing"]),
        ("budgets", config["budgets_per_run"]),
        ("retry_policy", config["retry_policy"]),
        ("provider_runtime", adapter_config["provider_runtime"]),
    ):
        require(job.get(key) == expected, f"prepared job {key} differs from frozen config")
    require(job.get("adapter_contract_sha256") == adapter_config["contract_sha256"],
            "prepared job adapter contract differs from frozen config")
    require(job.get("required_adapter_attestations") == [
        "fresh model context and process",
        "only agent_mount plus pinned read-only toolchain/dependency cache visible",
        "general network disabled inside evaluated tools",
        "token/tool/build/time/cost budgets enforced",
        "complete request/response/tool/process accounting retained under operator output",
    ], "prepared job adapter attestations differ from the runner contract")
    require(job.get("result_contract") == {
        "agent_output_directory": str(output.resolve()),
        "required_files": [
            "result.json", "lean-diff.patch", "build.log", "explanation.md",
            "workflow-compliance.json",
        ],
        "optional_files": ["source-amendment.md"],
        "workflow_id": planned["condition"],
        "workflow_evidence_files": runner.WORKFLOW_EVIDENCE[planned["condition"]],
        "result_required_fields": [
            "schema_version", "opaque_run_id", "final_status",
            "public_declarations", "primary_grader_rationale",
        ],
        "blind_grading_text_rule": runner.BLIND_GRADING_TEXT_RULE,
    }, "prepared job result contract differs from the runner contract")

    adapter_contract_path = pack / "adapter_contract.json"
    adapter_contract = regular_json(adapter_contract_path, "sealed adapter contract")
    require(prepare.sha256_file(adapter_contract_path) == adapter_config["contract_sha256"],
            "sealed adapter contract hash differs from frozen config")
    checker_contract_path = pack / "checker_sandbox_contract.json"
    checker_contract = regular_json(checker_contract_path, "sealed checker contract")
    require(prepare.sha256_file(checker_contract_path) == checker_config["contract_sha256"],
            "sealed checker contract hash differs from frozen config")

    require(set(workspace_manifest) == {
        "schema_version", "opaque_run_id", "workspace_base_commit",
        "condition_view", "selected_repository_paths", "files",
    }, "prepared workspace manifest schema differs")
    require(workspace_manifest["schema_version"] == 1
            and workspace_manifest["opaque_run_id"] == opaque_id
            and workspace_manifest["workspace_base_commit"] == config["workspace_base_commit"]
            and workspace_manifest["condition_view"] == planned["condition"],
            "prepared workspace manifest identity differs")
    baseline_manifest = _manifest_entries(
        workspace_manifest["files"], "prepared workspace manifest files"
    )
    require(state.get("prepared_job_sha256") == receipt.get("prepared_job_sha256")
            == prepare.sha256_file(job_path), "prepared job hash chain differs")
    require(state.get("workspace_manifest_sha256")
            == receipt.get("workspace_manifest_sha256")
            == prepare.sha256_file(workspace_manifest_path),
            "workspace manifest hash chain differs")

    require(receipt.get("schema_version") == 1
            and receipt.get("status") == "executed_unchecked",
            "execution receipt schema or status differs")
    require(set(receipt) == {
        "schema_version", "opaque_run_id", "execution_purpose",
        "primary_result_eligible", "smoke_plan_sha256", "sealed_pack_sha256",
        "prepared_agent_manifest_sha256", "prepared_job_sha256",
        "workspace_manifest_sha256", "completed_agent_manifest_sha256",
        "completed_agent_manifest", "protected_input_hashes",
        "adapter_artifact_sha256", "adapter_process_exit_code",
        "adapter_process_wall_seconds", "usage", "termination", "status",
    }, "execution receipt schema fields differ")
    require(receipt.get("termination") == adapter_response.get("termination") == "completed",
            "checked run lacks completed provider termination")
    require(type(receipt.get("adapter_process_exit_code")) is int
            and receipt["adapter_process_exit_code"] == 0,
            "checked run adapter process did not exit successfully")
    require(isinstance(receipt.get("adapter_process_wall_seconds"), (int, float))
            and not isinstance(receipt["adapter_process_wall_seconds"], bool)
            and 0 <= receipt["adapter_process_wall_seconds"]
            <= float(job["budgets"]["wall_clock_seconds"]) + 1,
            "checked run adapter wall time is invalid")

    require(agent.is_dir() and workspace.is_dir() and output.is_dir(),
            "completed agent view is incomplete")
    current_agent_manifest = runner.file_manifest(agent)
    current_agent_manifest_sha256 = runner.manifest_sha256(current_agent_manifest)
    require(receipt.get("completed_agent_manifest") == current_agent_manifest
            and receipt.get("completed_agent_manifest_sha256")
            == state.get("completed_agent_manifest_sha256")
            == current_agent_manifest_sha256,
            "completed agent manifest is absent, stale, or disconnected")
    require(receipt.get("prepared_agent_manifest_sha256")
            == state.get("prepared_agent_manifest_sha256"),
            "prepared agent manifest hash chain differs")
    _sha256_value(
        receipt.get("prepared_agent_manifest_sha256"),
        "prepared agent manifest receipt binding",
    )
    require(receipt.get("protected_input_hashes") == {
        "prompt.md": prepare.sha256_file(agent / "prompt.md"),
        "source/source.pdf": prepare.sha256_file(agent / "source" / "source.pdf"),
    }, "execution receipt protected-input hashes differ")
    require(job.get("prompt_sha256") == receipt["protected_input_hashes"]["prompt.md"]
            and job.get("source_sha256")
            == receipt["protected_input_hashes"]["source/source.pdf"],
            "prepared job prompt/source hashes differ from completed inputs")

    required_outputs = job.get("result_contract", {}).get("required_files")
    require(isinstance(required_outputs, list) and required_outputs
            and all(isinstance(name, str) and (output / name).is_file()
                    for name in required_outputs),
            "checked run omits required agent output")
    result_path = output / "result.json"
    result = regular_json(result_path, "agent result")
    require(set(result) == set(job["result_contract"]["result_required_fields"]),
            "agent result schema differs from prepared contract")
    require(result.get("schema_version") == 1
            and result.get("opaque_run_id") == opaque_id,
            "agent result identity differs")
    require(result.get("final_status") in {
        "compiled", "partial", "source_amended", "source_rejected",
        "library_blocked", "mathematically_blocked", "counterexample",
        "budget_exhausted", "infrastructure_failure",
    }, "agent result has an unknown final status")
    declarations = result.get("public_declarations")
    require(isinstance(declarations, list)
            and len(declarations) == len(set(declarations))
            and all(isinstance(name, str) and checker.inner.DECLARATION_NAME.fullmatch(name)
                    for name in declarations),
            "agent result has malformed public declarations")
    require(result["final_status"] != "compiled" or bool(declarations),
            "compiled agent result has no public declaration")
    require(isinstance(result.get("primary_grader_rationale"), str)
            and bool(result["primary_grader_rationale"].strip()),
            "agent result lacks a primary-grader rationale")
    checker.validate_workflow_artifacts(output, job)

    require(adapter_request == runner.adapter_request(job, agent),
            "adapter request differs from the prepared job/agent view")
    expected_adapter_response_fields = set(
        adapter_contract["response_schema"]["required"]
    ) | {"schema_version"}
    require(set(adapter_response) == expected_adapter_response_fields
            and adapter_response.get("schema_version") == 1,
            "adapter response schema differs from sealed contract")
    expected_adapter_response = {
        "opaque_run_id": opaque_id,
        "adapter_id": adapter_config["adapter_id"],
        "adapter_version": adapter_config["adapter_version"],
        "model_id": config["model"]["model_id"],
        "immutable_model_version": config["model"]["immutable_version"],
        "replicate": planned["replicate"],
        "container_or_sandbox_image_digest": adapter_config[
            "container_or_sandbox_image_digest"
        ],
        "budget_enforcement_attestation": adapter_config[
            "budget_enforcement_attestation"
        ],
        "filesystem_network_process_attestation": adapter_config[
            "filesystem_network_process_attestation"
        ],
    }
    for key, expected in expected_adapter_response.items():
        require(adapter_response.get(key) == expected,
                f"adapter response differs from frozen {key}")
    invocations = adapter_response.get("model_invocations")
    require(isinstance(invocations, list) and bool(invocations),
            "checked run lacks a provider invocation")
    require(all(
        invocation.get("transport") == "codex_cli"
        and invocation.get("observable_id_kind") == "codex_thread"
        and isinstance(invocation.get("observable_id"), str)
        and bool(invocation["observable_id"])
        and invocation.get("process_exit_code") == 0
        and invocation.get("usage_observed") is True
        for invocation in invocations
    ), "checked run lacks a successful observable codex_cli completion")
    trace = runner.parse_trace(adapter_trace_path)
    usage = runner.validate_usage(adapter_response, trace, job)
    require(receipt.get("usage") == {
        **usage,
        "orchestrator_wall_seconds": receipt["adapter_process_wall_seconds"],
    }, "execution receipt usage differs from the re-derived adapter trace")
    adapter_manifest = runner.file_manifest(adapter)
    actual_adapter_hashes = {
        entry["path"]: entry["sha256"] for entry in adapter_manifest
    }
    require(receipt.get("adapter_artifact_sha256") == actual_adapter_hashes,
            "execution receipt does not bind the exact adapter artifact set")
    require(state.get("execution_receipt_sha256") == prepare.sha256_file(receipt_path),
            "execution receipt hash differs from checked state")

    attempt_id = state.get("checker_attempt_id")
    require(isinstance(attempt_id, str) and attempt_id,
            "checked state lacks a checker attempt ID")
    expected_attempt_id = checker.checker_attempt_id(
        aggregate, opaque_id, state["execution_receipt_sha256"],
        checker_config["driver_sha256"], checker_config["inner_checker_sha256"],
        checker_config["runtime_config_sha256"], 1,
    )
    require(attempt_id == expected_attempt_id,
            "checker attempt ID differs from the frozen single-attempt derivation")
    attempts_root = operator / "checker-attempts"
    require(attempts_root.is_dir() and not attempts_root.is_symlink()
            and [path.name for path in attempts_root.iterdir()] == [attempt_id]
            and (attempts_root / attempt_id).is_dir()
            and not (attempts_root / attempt_id).is_symlink(),
            "checked run does not have exactly one deterministic checker attempt")
    checker_request_path = operator / "checker-attempts" / attempt_id / "request.json"
    checker_request = regular_json(checker_request_path, "checker request")
    request_fields = set(checker_contract["request_schema"]["required"])
    require(set(checker_request) == request_fields,
            "checker request schema differs from sealed contract")
    require(not (set(checker_contract["request_schema"]["forbidden_semantic_fields"])
                 & set(checker_request)),
            "checker request exposes forbidden semantic fields")
    completed_workspace_manifest = runner.file_manifest(workspace)
    expected_request = {
        "schema_version": 1,
        "suite_id": config["suite_id"],
        "opaque_run_id": opaque_id,
        "checker_attempt_id": attempt_id,
        "checker_attempt_label": attempt_id,
        "sealed_pack_sha256": aggregate,
        "execution_receipt_sha256": state["execution_receipt_sha256"],
        "completed_agent_manifest_sha256": current_agent_manifest_sha256,
        "baseline_manifest": baseline_manifest,
        "baseline_manifest_sha256": runner.manifest_sha256(baseline_manifest),
        "expected_completed_workspace_manifest": completed_workspace_manifest,
        "expected_completed_workspace_manifest_sha256": runner.manifest_sha256(
            completed_workspace_manifest
        ),
        "patch_sha256": prepare.sha256_file(output / "lean-diff.patch"),
        "result_sha256": prepare.sha256_file(result_path),
        "public_declarations": declarations,
        "final_status": result["final_status"],
        "allowed_axioms": sorted(checker.inner.ALLOWED_AXIOMS),
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
        "checker_cache_manifest_sha256": checker_config[
            "checker_cache_manifest_sha256"
        ],
        "resource_limits": checker_config["budgets"],
        "worker_command_prefix": checker_config["worker_command_prefix"],
        "cache_prelude_argv": checker_config["cache_prelude_argv"],
        "sandbox_mode": "production",
        "workflow_compliance_pass": True,
        "execution_usage": receipt["usage"],
    }
    require(checker_request == expected_request,
            "checker request is not the frozen semantic request for this run")

    checker_dir = operator / "checker"
    checker_result_path = checker_dir / "checker-result.json"
    checker_receipt_path = checker_dir / "checker-execution-receipt.json"
    checker_response_path = checker_dir / "sandbox-response.json"
    checker_result = regular_json(checker_result_path, "checker result")
    checker_receipt = regular_json(checker_receipt_path, "checker execution receipt")
    checker_response = regular_json(checker_response_path, "checker sandbox response")
    checker.validate_checker_result(checker_result, checker_request, opaque_id, attempt_id)
    require(checker_result.get("execution_usage") == receipt["usage"],
            "checker result usage differs from execution receipt")

    runtime_sha256 = prepare.checker_runtime_config_sha256(config)
    require(checker_config["runtime_config_sha256"] == runtime_sha256,
            "checker runtime digest differs from the frozen config")
    probe_path = pack / "checker_isolation_probe.json"
    probe = regular_json(probe_path, "sealed checker isolation probe")
    probe_artifacts = prepare.probe_artifact_bytes(
        pack / "checker_isolation_probe_artifacts"
    )
    require(prepare.probe_artifact_manifest(probe_artifacts)
            == probe.get("artifact_manifest"),
            "checker isolation-probe artifact bytes differ from its manifest")
    required_probes = {
        "network_denied", "host_sentinel_protected", "operator_ground_truth_absent",
        "checker_outputs_not_worker_writable",
        "patched_source_and_controller_input_read_only",
        "mounted_inputs_and_cidfile_protected", "background_process_reaped",
    }
    require(probe.get("schema_version") == 1
            and probe.get("suite_id") == config["suite_id"]
            and probe.get("status") == "passed"
            and probe.get("checker_id") == checker_config["checker_id"]
            and probe.get("checker_version") == checker_config["checker_version"]
            and probe.get("container_image_digest")
            == checker_config["container_image_digest"]
            and probe.get("controller_entrypoint_sha256")
            == checker_config["controller_entrypoint_sha256"]
            and probe.get("checker_runtime_config_sha256") == runtime_sha256
            and probe.get("runtime_command_template_sha256")
            == prepare.sha256_bytes(prepare.canonical_json_bytes(
                checker_config["sandbox_command_argv"]
            ))
            and probe.get("probe_runner_sha256")
            == checker_config["isolation_probe_runner_sha256"]
            and set(probe.get("probes", {})) == required_probes
            and all(probe["probes"][name] is True for name in required_probes),
            "checker isolation probe is absent, failed, or runtime-disconnected")
    probe_nonce = probe.get("probe_nonce")
    require(isinstance(probe_nonce, str) and len(probe_nonce) == 48
            and all(character in "0123456789abcdef" for character in probe_nonce)
            and probe.get("checker_attempt_label") == f"ABRL-PROBE-{probe_nonce}",
            "checker isolation probe nonce/attempt provenance differs")
    require("host-observations.json" in probe_artifacts,
            "checker isolation probe lacks host observations")
    try:
        host_observations = json.loads(
            probe_artifacts["host-observations.json"].decode("utf-8")
        )
    except (UnicodeDecodeError, json.JSONDecodeError) as error:
        raise SystemExit(
            "target-drift completion ledger failed: malformed probe host observations"
        ) from error
    require(isinstance(host_observations, dict)
            and host_observations.get("probe_nonce") == probe_nonce
            and host_observations.get("checker_attempt_label")
            == probe["checker_attempt_label"]
            and host_observations.get("checker_runtime_config_sha256") == runtime_sha256
            and host_observations.get("container_image_digest")
            == checker_config["container_image_digest"]
            and host_observations.get("derived_probes") == probe["probes"],
            "checker isolation host observations differ from the passed report")
    require(checker_config["isolation_probe_report_sha256"]
            == prepare.sha256_file(probe_path),
            "checker isolation-probe report hash differs from frozen config")

    response_fields = set(checker_contract["response_schema"]["required"]) | {
        "schema_version"
    }
    require(set(checker_response) == response_fields
            and checker_response.get("schema_version") == 1,
            "checker sandbox response schema differs from sealed contract")
    expected_response = {
        "opaque_run_id": opaque_id,
        "checker_attempt_id": attempt_id,
        "checker_attempt_label": attempt_id,
        "request_sha256": prepare.sha256_file(checker_request_path),
        "checker_id": checker_config["checker_id"],
        "checker_version": checker_config["checker_version"],
        "inner_checker_sha256": checker_config["inner_checker_sha256"],
        "controller_entrypoint_sha256": checker_config["controller_entrypoint_sha256"],
        "checker_contract_sha256": checker_config["contract_sha256"],
        "checker_runtime_config_sha256": runtime_sha256,
        "container_image_digest": checker_config["container_image_digest"],
        "filesystem_network_process_attestation": checker_config[
            "filesystem_network_process_attestation"
        ],
        "controller_worker_separation_attestation": checker_config[
            "controller_worker_separation_attestation"
        ],
    }
    for key, expected in expected_response.items():
        require(checker_response.get(key) == expected,
                f"checker sandbox response differs from frozen {key}")
    require(checker_response.get("termination") == "completed"
            and checker_response.get("process_exit_code") == 0,
            "checker sandbox response is not a completed success")
    measured_wall = checker_response.get("measured_wall_seconds")
    require(isinstance(measured_wall, (int, float))
            and not isinstance(measured_wall, bool)
            and 0 <= measured_wall
            <= float(checker_config["budgets"]["wall_clock_seconds"]) + 1,
            "checker sandbox response wall time is invalid")
    artifact_manifest = _manifest_entries(
        checker_response.get("artifact_manifest"), "checker artifact manifest"
    )
    actual_checker_manifest = runner.file_manifest(checker_dir)
    published_artifacts = [
        entry for entry in actual_checker_manifest
        if entry["path"] not in {
            "sandbox-response.json", "checker-execution-receipt.json"
        }
    ]
    require(artifact_manifest == published_artifacts,
            "checker artifact manifest differs from the exact published artifacts")
    checker_artifact_aggregate = checker.artifact_aggregate(artifact_manifest)
    require(checker_response.get("artifact_aggregate_sha256")
            == checker_artifact_aggregate,
            "checker artifact aggregate is not re-derived from published bytes")
    require(checker_response.get("checker_result_sha256")
            == prepare.sha256_file(checker_result_path),
            "checker sandbox response does not bind checker-result bytes")

    require(set(checker_receipt) == {
        "schema_version", "opaque_run_id", "checker_attempt_id",
        "checker_request_sha256", "sandbox_response_sha256",
        "checker_result_sha256", "checker_artifact_aggregate_sha256",
        "checker_runtime_config_sha256", "isolation_probe_report_sha256",
        "checker_mode", "execution_purpose", "result_eligible", "process",
    }, "checker execution receipt schema differs")
    process = checker_receipt.get("process")
    require(isinstance(process, dict)
            and process.get("exit_code") == 0
            and process.get("timed_out") is False
            and process.get("output_limit_exceeded") is False
            and process.get("lifecycle_verified_absent") is True,
            "checker execution receipt lacks a successful closed lifecycle")
    require(checker_receipt.get("schema_version") == 1
            and checker_receipt.get("opaque_run_id") == opaque_id
            and checker_receipt.get("checker_attempt_id") == attempt_id
            and checker_receipt.get("checker_mode") == "production"
            and checker_receipt.get("execution_purpose")
            == runner.PRIMARY_EXECUTION_PURPOSE
            and checker_receipt.get("result_eligible") is True,
            "checker execution receipt is not production-result-eligible")
    require(checker_receipt.get("checker_request_sha256")
            == state.get("checker_request_sha256")
            == checker_response["request_sha256"]
            == prepare.sha256_file(checker_request_path),
            "checker request hash chain differs")
    require(checker_receipt.get("checker_result_sha256")
            == state.get("checker_result_sha256")
            == checker_response["checker_result_sha256"]
            == prepare.sha256_file(checker_result_path),
            "checker result hash chain differs")
    require(checker_receipt.get("checker_artifact_aggregate_sha256")
            == state.get("checker_artifact_aggregate_sha256")
            == checker_response["artifact_aggregate_sha256"]
            == checker_artifact_aggregate,
            "checker artifact aggregate chain differs")
    require(checker_receipt.get("sandbox_response_sha256")
            == state.get("sandbox_response_sha256")
            == prepare.sha256_file(checker_response_path),
            "checker sandbox-response hash chain differs")
    require(state.get("checker_execution_receipt_sha256")
            == prepare.sha256_file(checker_receipt_path),
            "checker execution-receipt hash differs from checked state")
    require(checker_receipt.get("checker_runtime_config_sha256")
            == state.get("checker_runtime_config_sha256")
            == checker_result.get("checker_runtime_config_sha256")
            == runtime_sha256,
            "checker runtime hash chain differs")
    require(checker_receipt.get("isolation_probe_report_sha256")
            == state.get("isolation_probe_report_sha256")
            == checker_config["isolation_probe_report_sha256"],
            "checker isolation-probe hash chain differs")

    hashes = evidence_hashes(operator, state)
    return {
        "job": job,
        "state": state,
        "workspace_manifest": workspace_manifest,
        "execution_receipt": receipt,
        "adapter_response": adapter_response,
        "agent_result": result,
        "checker_request": checker_request,
        "checker_result": checker_result,
        "checker_execution_receipt": checker_receipt,
        "checker_sandbox_response": checker_response,
        "evidence_sha256": hashes,
    }


def missing_reason(status: str) -> str | None:
    return {
        "prepared_unrun": "adapter_not_completed",
        "terminal_operator_failure": "operator_or_adapter_terminal_failure",
        "executed_unchecked": "checker_not_completed",
        "checker_terminal_failure": "checker_terminal_failure",
        "checked_fixture_nonexperimental": "fixture_nonexperimental",
        "checked": None,
    }[status]


def inspect_run(
    run_dir: Path, planned: dict[str, Any], aggregate: str,
    config: dict[str, Any], pack: Path,
) -> dict[str, Any]:
    operator = run_dir / "operator"
    job = regular_json(operator / "job.json", "prepared job")
    state = regular_json(operator / "run_state.json", "run state")
    semantic_id = planned["run_id"]
    opaque_id = runner.opaque_id("run", aggregate, semantic_id)
    require(job.get("semantic_run_id") == semantic_id, "run directory names a different semantic run")
    require(job.get("opaque_run_id") == state.get("opaque_run_id") == opaque_id,
            "run opaque identifier mismatch")
    require(state.get("sealed_pack_sha256") == aggregate, "run state names a different sealed pack")
    require(state.get("schema_version") == 1, "run state schema_version must be 1")
    status = state.get("status")
    require(status in KNOWN_STATES, f"unknown run state {status!r}")
    eligible = (
        status == ELIGIBLE_STATUS
        and state.get("result_eligible") is True
        and state.get("checker_mode") == "production"
    )
    if status == ELIGIBLE_STATUS:
        require(eligible, "checked run is not literal production-result-eligible")
        hashes = validate_checked_run_evidence(
            pack, run_dir, planned, aggregate, config
        )["evidence_sha256"]
    else:
        hashes = evidence_hashes(operator, state)
    if status == "checked_fixture_nonexperimental":
        require(state.get("result_eligible") is False,
                "fixture run must be explicitly result-ineligible")
    return {
        "semantic_run_id": semantic_id,
        "opaque_run_id": opaque_id,
        "case_id": planned["case_id"],
        "condition": planned["condition"],
        "replicate": planned["replicate"],
        "requirement_variant": planned["requirement_variant"],
        "presentation_order": planned["presentation_order"],
        "state_status": status,
        "result_eligible": eligible,
        "missing_reason": None if eligible else missing_reason(status),
        "evidence_sha256": hashes,
    }


def summary(records: list[dict[str, Any]]) -> dict[str, Any]:
    missing = [record for record in records if not record["result_eligible"]]
    return {
        "result_eligible_count": len(records) - len(missing),
        "missing_count": len(missing),
        "state_status_counts": dict(sorted(Counter(
            record["state_status"] for record in records
        ).items())),
        "missing_reason_counts": dict(sorted(Counter(
            record["missing_reason"] for record in missing
        ).items())),
        "missing_by_condition": dict(sorted(Counter(
            record["condition"] for record in missing
        ).items())),
        "missing_by_requirement_variant": dict(sorted(Counter(
            record["requirement_variant"] for record in missing
        ).items())),
    }


def build_ledger(pack: Path, runs_root: Path) -> dict[str, Any]:
    config = load(pack / "execution_config.json")
    policy, policy_sha256 = policy_from_pack(pack, config)
    aggregate = (pack / "aggregate.sha256").read_text(encoding="ascii").strip()
    manifest = load(pack / "run_manifest.json")
    planned_runs = manifest["runs"]
    require(len(planned_runs) == policy["planned_run_count"] == 450,
            "sealed run universe must contain exactly 450 runs")
    planned_by_id = {run["run_id"]: run for run in planned_runs}
    require(len(planned_by_id) == 450, "sealed semantic run IDs must be unique")

    expected_by_opaque = {
        runner.opaque_id("run", aggregate, semantic_id): semantic_id
        for semantic_id in planned_by_id
    }
    discovered: dict[str, Path] = {}
    if runs_root.exists():
        require(runs_root.is_dir() and not runs_root.is_symlink(), "runs root is not a plain directory")
        for run_dir in sorted(runs_root.iterdir(), key=lambda path: path.name):
            require(run_dir.is_dir() and not run_dir.is_symlink(),
                    f"runs root contains a non-directory entry: {run_dir.name}")
            semantic_id = expected_by_opaque.get(run_dir.name)
            require(semantic_id in planned_by_id,
                    f"unknown or nondeterministically named run directory: {run_dir.name}")
            require(semantic_id not in discovered, f"duplicate run directory for {semantic_id}")
            discovered[semantic_id] = run_dir

    records = []
    for planned in sorted(planned_runs, key=lambda run: run["presentation_order"]):
        semantic_id = planned["run_id"]
        if semantic_id in discovered:
            try:
                records.append(inspect_run(
                    discovered[semantic_id], planned, aggregate, config, pack
                ))
            except (SystemExit, Exception) as error:
                records.append({
                    "semantic_run_id": semantic_id,
                    "opaque_run_id": runner.opaque_id("run", aggregate, semantic_id),
                    "case_id": planned["case_id"],
                    "condition": planned["condition"],
                    "replicate": planned["replicate"],
                    "requirement_variant": planned["requirement_variant"],
                    "presentation_order": planned["presentation_order"],
                    "state_status": "integrity_failure",
                    "result_eligible": False,
                    "missing_reason": "run_evidence_unreadable_or_invalid",
                    "evidence_sha256": {},
                    "integrity_error": f"{type(error).__name__}: {error}",
                })
        else:
            records.append({
                "semantic_run_id": semantic_id,
                "opaque_run_id": runner.opaque_id("run", aggregate, semantic_id),
                "case_id": planned["case_id"],
                "condition": planned["condition"],
                "replicate": planned["replicate"],
                "requirement_variant": planned["requirement_variant"],
                "presentation_order": planned["presentation_order"],
                "state_status": "not_materialized",
                "result_eligible": False,
                "missing_reason": "run_not_materialized",
                "evidence_sha256": {},
            })
    counts = summary(records)
    complete = counts["result_eligible_count"] == 450 and counts["missing_count"] == 0
    return {
        "schema_version": 1,
        "suite_id": config["suite_id"],
        "sealed_pack_sha256": aggregate,
        "missing_run_policy_id": policy["policy_id"],
        "missing_run_policy_sha256": policy_sha256,
        "planned_run_count": 450,
        "completion_status": (
            "complete_result_eligible_for_blind_grading"
            if complete else "incomplete_primary_analysis_forbidden"
        ),
        "primary_analysis_permitted": complete,
        "replacement_runs_permitted": False,
        "outcome_imputation_permitted": False,
        "summary": counts,
        "records": records,
    }


def validate_ledger(pack: Path, ledger: dict[str, Any], require_complete: bool) -> dict[str, Any]:
    config = load(pack / "execution_config.json")
    policy, policy_sha256 = policy_from_pack(pack, config)
    aggregate = (pack / "aggregate.sha256").read_text(encoding="ascii").strip()
    manifest = load(pack / "run_manifest.json")
    require(ledger.get("schema_version") == 1, "completion ledger schema_version must be 1")
    require(ledger.get("suite_id") == config["suite_id"], "completion ledger suite mismatch")
    require(ledger.get("sealed_pack_sha256") == aggregate, "completion ledger pack mismatch")
    require(ledger.get("missing_run_policy_id") == policy["policy_id"],
            "completion ledger policy ID mismatch")
    require(ledger.get("missing_run_policy_sha256") == policy_sha256,
            "completion ledger policy hash mismatch")
    require(ledger.get("planned_run_count") == len(manifest["runs"]) == 450,
            "completion ledger planned count mismatch")
    records = ledger.get("records")
    require(isinstance(records, list) and len(records) == 450,
            "completion ledger must contain 450 records")
    expected = {
        run["run_id"]: (
            run["case_id"], run["condition"], run["replicate"],
            run["requirement_variant"], run["presentation_order"],
            runner.opaque_id("run", aggregate, run["run_id"]),
        )
        for run in manifest["runs"]
    }
    observed: dict[str, tuple[Any, ...]] = {}
    for record in records:
        semantic_id = record.get("semantic_run_id")
        require(semantic_id in expected and semantic_id not in observed,
                "completion ledger has an unknown or duplicate semantic run")
        require(record.get("state_status") in LEDGER_STATES,
                "completion ledger has an unknown state")
        require(isinstance(record.get("result_eligible"), bool),
                "completion ledger eligibility must be boolean")
        status = record.get("state_status")
        expected_reason = {
            "not_materialized": "run_not_materialized",
            "integrity_failure": "run_evidence_unreadable_or_invalid",
        }.get(status, missing_reason(status) if status in KNOWN_STATES else None)
        require(record.get("result_eligible") == (status == "checked"),
                "completion ledger eligibility/state invariant failed")
        require(record.get("missing_reason") == expected_reason,
                "completion ledger missing reason differs from state")
        observed[semantic_id] = (
            record.get("case_id"), record.get("condition"), record.get("replicate"),
            record.get("requirement_variant"), record.get("presentation_order"),
            record.get("opaque_run_id"),
        )
    require(observed == expected, "completion ledger run metadata differs from sealed manifest")
    counts = summary(records)
    require(ledger.get("summary") == counts, "completion ledger summary does not match records")
    complete = counts["result_eligible_count"] == 450 and counts["missing_count"] == 0
    require(ledger.get("primary_analysis_permitted") is complete,
            "completion ledger analysis gate differs from run records")
    require(ledger.get("replacement_runs_permitted") is False
            and ledger.get("outcome_imputation_permitted") is False,
            "completion ledger weakened the no-replacement/no-imputation policy")
    require(ledger.get("completion_status") == (
        "complete_result_eligible_for_blind_grading"
        if complete else "incomplete_primary_analysis_forbidden"
    ), "completion ledger status differs from records")
    if require_complete:
        require(complete, "450/450 production-result-eligible runs are required")
    return counts


def validate_ledger_against_runs(
    pack: Path, runs_root: Path, ledger: dict[str, Any], require_complete: bool,
) -> dict[str, Any]:
    """Rebuild the operator ledger from run artifacts before trusting its states."""
    counts = validate_ledger(pack, ledger, require_complete=require_complete)
    rebuilt = build_ledger(pack, runs_root)
    for key, value in rebuilt.items():
        require(ledger.get(key) == value,
                f"completion ledger {key} differs from current run evidence")
    return counts


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--pack", type=Path, required=True)
    parser.add_argument("--runs-root", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    pack = args.pack.resolve()
    prepare.verify_pack(pack)
    config = load(pack / "execution_config.json")
    require(config["execution_status"] == "frozen_ready",
            "completion ledger requires a frozen_ready pack")
    self_verify(pack, config)
    ledger = build_ledger(pack, args.runs_root.resolve())
    validate_ledger_against_runs(
        pack, args.runs_root.resolve(), ledger, require_complete=False,
    )
    dump_new(args.output.resolve(), ledger)
    missing = ledger["summary"]["missing_count"]
    print(
        f"target-drift completion ledger: eligible={450 - missing}/450, "
        f"missing={missing}, status={ledger['completion_status']}"
    )
    if missing:
        raise SystemExit(2)


if __name__ == "__main__":
    main()
