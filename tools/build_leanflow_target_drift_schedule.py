#!/usr/bin/env python3
"""Build the deterministic, result-free 30-ID LeanFlow calibration schedule."""

from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
from typing import Any


ROOT = Path(__file__).resolve().parents[1]
V1 = ROOT / "evaluation" / "target-drift-v1"
V2 = ROOT / "evaluation" / "target-drift-v2"
PLAN = V2 / "external-comparator-plan.json"
CHALLENGES = V1 / "challenges.json"
PAIRED_REQUIREMENTS = V2 / "paired-requirements.json"
CONDITION = "leanflow_external"
REPLICATE_INDEX = 0


def require(condition: bool, message: str) -> None:
    if not condition:
        raise SystemExit(f"LeanFlow schedule build failed: {message}")


def load_object(path: Path) -> dict[str, Any]:
    value = json.loads(path.read_text(encoding="utf-8"))
    require(isinstance(value, dict), f"{path} must contain one JSON object")
    return value


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def requirement_variant(case_index: int, replicate_index: int) -> str:
    """Match target-drift-v2's frozen case/replicate parity rule exactly."""

    return (
        "injected_drift"
        if (case_index + replicate_index) % 2 == 0
        else "source_faithful"
    )


def semantic_run_id(case_id: str) -> str:
    return f"{case_id}--{CONDITION}--replicate-{REPLICATE_INDEX}"


def build_schedule(
    plan_path: Path = PLAN,
    challenges_path: Path = CHALLENGES,
    paired_requirements_path: Path = PAIRED_REQUIREMENTS,
) -> dict[str, Any]:
    plan = load_object(plan_path)
    challenges_payload = load_object(challenges_path)
    paired_payload = load_object(paired_requirements_path)
    design = plan.get("design", {})

    require(plan.get("suite_id") == "ABRL-TARGET-DRIFT-V2", "suite ID differs")
    require(plan.get("status") == "planned_unrun_result_free", "plan is not result-free")
    require(design.get("external_condition_id") == CONDITION, "condition differs")
    require(design.get("selected_replicate_index") == REPLICATE_INDEX,
            "selected replicate index differs")
    require(design.get("planned_external_run_count") == 30,
            "plan does not require exactly 30 runs")

    cases = challenges_payload.get("cases")
    paired_cases = paired_payload.get("cases")
    require(isinstance(cases, list) and len(cases) == 30,
            "challenge manifest must contain exactly 30 cases")
    require(isinstance(paired_cases, list) and len(paired_cases) == 30,
            "paired requirements must contain exactly 30 cases")
    paired_ids = [entry.get("case_id") for entry in paired_cases]
    case_ids = [case.get("id") for case in cases]
    require(paired_ids == case_ids,
            "paired-requirement order must exactly match the frozen challenge order")
    require(len(set(case_ids)) == 30 and all(isinstance(item, str) and item for item in case_ids),
            "challenge case IDs must be 30 unique nonempty strings")

    runs: list[dict[str, Any]] = []
    for case_index, case in enumerate(cases):
        case_id = case["id"]
        runs.append({
            "presentation_order": case_index,
            "run_id": semantic_run_id(case_id),
            "case_id": case_id,
            "source_id": case["source_id"],
            "stratum": case["stratum"],
            "condition": CONDITION,
            "replicate_index": REPLICATE_INDEX,
            "requirement_variant": requirement_variant(case_index, REPLICATE_INDEX),
            "status": "sealed_unrun",
        })

    require(sum(run["requirement_variant"] == "source_faithful" for run in runs) == 15,
            "schedule must contain 15 source-faithful runs")
    require(sum(run["requirement_variant"] == "injected_drift" for run in runs) == 15,
            "schedule must contain 15 injected-drift runs")
    require(sum(run["stratum"] == "paper_derived" for run in runs) == 18,
            "schedule must contain 18 paper-derived cases")
    require(sum(run["stratum"] == "textbook_control" for run in runs) == 12,
            "schedule must contain 12 textbook controls")

    return {
        "schema_version": 1,
        "suite_id": "ABRL-TARGET-DRIFT-V2",
        "comparator_id": CONDITION,
        "status": "sealed_unrun_result_free_provider_disabled",
        "outcomes_observed": False,
        "provider_execution_enabled": False,
        "external_comparator_plan_path": (
            "evaluation/target-drift-v2/external-comparator-plan.json"
        ),
        "external_comparator_plan_sha256": sha256(plan_path),
        "challenge_manifest_path": "evaluation/target-drift-v1/challenges.json",
        "challenge_manifest_sha256": sha256(challenges_path),
        "paired_requirements_path": "evaluation/target-drift-v2/paired-requirements.json",
        "paired_requirements_sha256": sha256(paired_requirements_path),
        "schedule_rule": (
            "frozen challenge-manifest order; external condition leanflow_external; "
            "replicate index 0; target-drift-v2 case-index plus replicate-index parity"
        ),
        "planned_run_count": 30,
        "hidden_variant_balance": {
            "source_faithful": 15,
            "injected_drift": 15,
        },
        "stratum_balance": {
            "paper_derived": 18,
            "textbook_control": 12,
        },
        "visibility": (
            "sealed operator schedule; requirement_variant is hidden from evaluated "
            "systems and graders"
        ),
        "runs": runs,
    }


def canonical_bytes(value: Any) -> bytes:
    return (json.dumps(
        value, indent=2, sort_keys=True, ensure_ascii=False
    ) + "\n").encode("utf-8")


def write_new(path: Path, value: Any) -> None:
    require(not path.exists(), f"refusing to overwrite {path}")
    path.parent.mkdir(parents=True, exist_ok=True)
    with path.open("xb") as handle:
        handle.write(canonical_bytes(value))


def main() -> None:
    parser = argparse.ArgumentParser()
    choice = parser.add_mutually_exclusive_group(required=True)
    choice.add_argument("--output", type=Path)
    choice.add_argument("--check", type=Path)
    args = parser.parse_args()
    expected = canonical_bytes(build_schedule())
    if args.output:
        write_new(args.output.resolve(), json.loads(expected))
        print(f"wrote deterministic 30-ID result-free schedule to {args.output}")
        return
    actual = args.check.resolve().read_bytes()
    require(actual == expected, f"{args.check} differs from deterministic schedule")
    print("LeanFlow external schedule valid: 30 sealed-unrun IDs, provider disabled")


if __name__ == "__main__":
    main()
