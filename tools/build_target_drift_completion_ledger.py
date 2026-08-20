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
from pathlib import Path
from typing import Any


TOOLS = Path(__file__).resolve().parent
sys.path.insert(0, str(TOOLS))

import prepare_target_drift_execution as prepare  # noqa: E402
import run_target_drift_execution as runner  # noqa: E402


ELIGIBLE_STATUS = "checked"
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
    require(prepare.sha256_file(current) == expected,
            "invoked completion-ledger builder differs from frozen hash")
    require(prepare.sha256_file(sealed) == expected,
            "sealed completion-ledger builder differs from frozen hash")


def evidence_hashes(operator: Path, state: dict[str, Any]) -> dict[str, str]:
    status = state["status"]
    candidates: list[tuple[str, Path, str | None]] = [
        ("run_state", operator / "run_state.json", None),
        ("job", operator / "job.json", state.get("prepared_job_sha256")),
    ]
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
    hashes = evidence_hashes(operator, state)
    eligible = (
        status == ELIGIBLE_STATUS
        and state.get("result_eligible") is True
        and state.get("checker_mode") == "production"
    )
    if status == ELIGIBLE_STATUS:
        require(eligible, "checked run is not literal production-result-eligible")
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
                records.append(inspect_run(discovered[semantic_id], planned, aggregate))
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
