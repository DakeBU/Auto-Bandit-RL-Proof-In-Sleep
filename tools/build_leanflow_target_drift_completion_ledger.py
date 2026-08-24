#!/usr/bin/env python3
"""Materialize only a result-free LeanFlow completion-ledger template."""

from __future__ import annotations

import argparse
import hashlib
import json
from collections import Counter
from pathlib import Path
from typing import Any


ROOT = Path(__file__).resolve().parents[1]
V2 = ROOT / "evaluation" / "target-drift-v2"
SCHEDULE = V2 / "leanflow-external-schedule.json"
CONTRACT = V2 / "leanflow-external-completion-ledger-contract.json"
FORBIDDEN_OUTPUT_NAMES = {
    "external-comparator-results.json",
    "leanflow-external-completion-ledger.json",
}


def require(condition: bool, message: str) -> None:
    if not condition:
        raise SystemExit(f"LeanFlow completion ledger failed: {message}")


def load_object(path: Path) -> dict[str, Any]:
    value = json.loads(path.read_text(encoding="utf-8"))
    require(isinstance(value, dict), f"{path} must contain one JSON object")
    return value


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def build_result_free_ledger(
    schedule: dict[str, Any],
    contract: dict[str, Any],
    schedule_sha256: str,
) -> dict[str, Any]:
    require(schedule.get("status") == "sealed_unrun_result_free_provider_disabled",
            "schedule is not the provider-disabled result-free schedule")
    require(schedule.get("outcomes_observed") is False,
            "schedule says outcomes were observed")
    require(schedule.get("provider_execution_enabled") is False,
            "schedule enables provider execution")
    require(contract.get("status") == "schema_frozen_results_absent",
            "completion-ledger contract is not result-free")
    require(contract.get("schedule_sha256") == schedule_sha256,
            "completion-ledger contract names different schedule bytes")
    runs = schedule.get("runs")
    require(isinstance(runs, list)
            and len(runs) == contract.get("planned_run_count") == 30,
            "completion-ledger universe must contain exactly 30 IDs")

    records = [{
        "semantic_run_id": run["run_id"],
        "case_id": run["case_id"],
        "source_id": run["source_id"],
        "stratum": run["stratum"],
        "condition": run["condition"],
        "replicate_index": run["replicate_index"],
        "requirement_variant": run["requirement_variant"],
        "presentation_order": run["presentation_order"],
        "state_status": "not_materialized",
        "result_eligible": False,
        "missing_reason": "external_run_not_executed",
        "evidence_sha256": {},
    } for run in runs]
    missing_by_variant = dict(sorted(Counter(
        record["requirement_variant"] for record in records
    ).items()))
    missing_by_condition = dict(sorted(Counter(
        record["condition"] for record in records
    ).items()))
    missing_by_stratum = dict(sorted(Counter(
        record["stratum"] for record in records
    ).items()))
    missing_by_paper_cluster = dict(sorted(Counter(
        record["source_id"] for record in records
        if record["stratum"] == "paper_derived"
    ).items()))
    missing_by_textbook_target = dict(sorted(Counter(
        record["case_id"] for record in records
        if record["stratum"] == "textbook_control"
    ).items()))

    return {
        "schema_version": 1,
        "suite_id": schedule["suite_id"],
        "comparator_id": schedule["comparator_id"],
        "policy_id": contract["policy_id"],
        "status": "result_free_template_external_runs_not_executed",
        "outcomes_observed": False,
        "provider_execution_enabled": False,
        "schedule_sha256": schedule_sha256,
        "planned_run_count": 30,
        "result_eligible_count": 0,
        "missing_count": 30,
        "complete_analysis_gate_passed": False,
        "effect_estimates_permitted": False,
        "records": records,
        "missingness_summary": {
            "state_status_counts": {"not_materialized": 30},
            "missing_reason_counts": {"external_run_not_executed": 30},
            "missing_by_condition": missing_by_condition,
            "missing_by_requirement_variant": missing_by_variant,
            "missing_by_stratum": missing_by_stratum,
            "missing_by_paper_cluster": missing_by_paper_cluster,
            "missing_by_textbook_target": missing_by_textbook_target,
        },
        "nonclaim": (
            "This template records only the preregistered ID universe. It contains "
            "no LeanFlow execution, formalization, checker, grader, or model outcome."
        ),
    }


def validate_result_free_ledger(
    ledger: dict[str, Any], schedule: dict[str, Any], contract: dict[str, Any]
) -> None:
    expected = build_result_free_ledger(schedule, contract, contract["schedule_sha256"])
    require(ledger == expected, "ledger differs from the exact result-free template")
    require(all(record["state_status"] == "not_materialized"
                and record["result_eligible"] is False
                and not record["evidence_sha256"]
                for record in ledger["records"]),
            "result-free ledger contains execution evidence or an eligible record")


def canonical_bytes(value: Any) -> bytes:
    return (json.dumps(
        value, indent=2, sort_keys=True, ensure_ascii=False
    ) + "\n").encode("utf-8")


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--schedule", type=Path, default=SCHEDULE)
    parser.add_argument("--contract", type=Path, default=CONTRACT)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    schedule_path = args.schedule.resolve()
    contract_path = args.contract.resolve()
    output_path = args.output.resolve()
    require(output_path.name not in FORBIDDEN_OUTPUT_NAMES,
            "this result-free builder may not create a production ledger or results file")
    require(not output_path.exists(), f"refusing to overwrite {output_path}")
    schedule = load_object(schedule_path)
    contract = load_object(contract_path)
    ledger = build_result_free_ledger(schedule, contract, sha256(schedule_path))
    validate_result_free_ledger(ledger, schedule, contract)
    output_path.parent.mkdir(parents=True, exist_ok=True)
    with output_path.open("xb") as handle:
        handle.write(canonical_bytes(ledger))
    print(
        "wrote result-free 30-ID completion-ledger template; "
        "0 eligible, 30 not materialized, no outcomes"
    )


if __name__ == "__main__":
    main()
