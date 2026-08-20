#!/usr/bin/env python3
"""Seal one matched three-condition infrastructure smoke plan.

The plan is operator-only.  Its three outputs are permanently excluded from the
450-run primary result set even when the production checker succeeds.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import sys
from pathlib import Path
from typing import Any


TOOLS = Path(__file__).resolve().parent
sys.path.insert(0, str(TOOLS))

import prepare_target_drift_execution as prepare  # noqa: E402
import run_target_drift_execution as runner  # noqa: E402


CONDITIONS = set(runner.CONDITIONS)


def load(path: Path) -> dict[str, Any]:
    return json.loads(path.read_text(encoding="utf-8"))


def require(condition: bool, message: str) -> None:
    if not condition:
        raise SystemExit(f"target-drift smoke preparation failed: {message}")


def dump_new(path: Path, value: Any) -> None:
    require(not path.exists(), "smoke plan already exists")
    path.parent.mkdir(parents=True, exist_ok=True)
    with path.open("x", encoding="utf-8", newline="\n") as handle:
        json.dump(value, handle, indent=2, sort_keys=True, ensure_ascii=False)
        handle.write("\n")


def matched_triplet(runs: list[dict[str, Any]], selected_run_id: str) -> list[dict[str, Any]]:
    selected = [run for run in runs if run.get("run_id") == selected_run_id]
    require(len(selected) == 1, "selected primary run id is missing or duplicated")
    anchor = selected[0]
    match_keys = ("case_id", "replicate", "requirement_variant", "proposed_requirement")
    triplet = [
        run for run in runs
        if all(run.get(key) == anchor.get(key) for key in match_keys)
    ]
    require(len(triplet) == 3, "selected run does not have exactly one matched triplet")
    require({run.get("condition") for run in triplet} == CONDITIONS,
            "matched triplet does not cover the three frozen conditions")
    require(all(run.get("status") == "sealed_unrun" for run in triplet),
            "smoke source triplet must remain sealed_unrun")
    return sorted(triplet, key=lambda run: runner.CONDITIONS.index(run["condition"]))


def smoke_run_id(aggregate: str, source_primary_run_id: str) -> str:
    digest = hashlib.sha256(
        (aggregate + "\0real-infrastructure-smoke\0" + source_primary_run_id).encode("utf-8")
    ).hexdigest()[:24]
    return f"SMOKE-{digest}"


def neutral_runs_root_name(aggregate: str, case_id: str, replicate: int) -> str:
    return "RUNS-" + hashlib.sha256(
        (aggregate + "\0neutral-auxiliary-run-root\0" + case_id
         + "\0" + str(replicate)).encode("utf-8")
    ).hexdigest()[:20]


def build_plan(
    aggregate: str,
    run_manifest: dict[str, Any],
    selected_run_id: str,
    materializer_sha256: str,
    smoke_runner_sha256: str,
) -> dict[str, Any]:
    require(run_manifest.get("suite_id") == "ABRL-TARGET-DRIFT-V2",
            "smoke requires the v2 run manifest")
    require(isinstance(aggregate, str) and len(aggregate) == 64,
            "sealed pack aggregate is not a SHA-256 digest")
    triplet = matched_triplet(run_manifest["runs"], selected_run_id)
    primary_ids = {run["run_id"] for run in run_manifest["runs"]}
    plan_runs = []
    for source in triplet:
        smoke_id = smoke_run_id(aggregate, source["run_id"])
        require(smoke_id not in primary_ids, "derived smoke id collides with primary manifest")
        plan_runs.append({
            "smoke_run_id": smoke_id,
            "source_primary_run_id": source["run_id"],
            "condition": source["condition"],
            "replicate": source["replicate"],
            "requirement_variant": source["requirement_variant"],
            "status": "sealed_unrun",
            "primary_result_eligible": False,
        })
    require(len({run["smoke_run_id"] for run in plan_runs}) == 3,
            "derived smoke ids are not unique")
    return {
        "schema_version": 1,
        "suite_id": "ABRL-TARGET-DRIFT-V2",
        "execution_purpose": runner.SMOKE_EXECUTION_PURPOSE,
        "primary_result_eligible": False,
        "sealed_pack_sha256": aggregate,
        "source_case_id": triplet[0]["case_id"],
        "source_replicate": triplet[0]["replicate"],
        "requirement_variant": triplet[0]["requirement_variant"],
        "run_count": 3,
        "runs": plan_runs,
        "neutral_runs_root_name": neutral_runs_root_name(
            aggregate, triplet[0]["case_id"], triplet[0]["replicate"]
        ),
        "tool_sha256": {
            "prepare_target_drift_smoke.py": materializer_sha256,
            "run_target_drift_smoke.py": smoke_runner_sha256,
        },
        "result_boundary": {
            "permanently_excluded_from_primary_450": True,
            "grading_forbidden": True,
            "analysis_forbidden": True,
            "model_or_formalization_outcome_claim_forbidden": True,
        },
        "status": "sealed_unrun",
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--pack", type=Path, required=True)
    parser.add_argument("--run-id", required=True,
                        help="one primary run id; its matched three-condition block is selected")
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    pack = args.pack.resolve()
    prepare.verify_pack(pack)
    config = load(pack / "execution_config.json")
    require(config.get("execution_status") == "frozen_ready",
            "smoke plan requires a frozen_ready pack")
    aggregate = (pack / "aggregate.sha256").read_text(encoding="ascii").strip()
    smoke_runner = TOOLS / "run_target_drift_smoke.py"
    require(smoke_runner.is_file(), "smoke runner is missing")
    plan = build_plan(
        aggregate,
        load(pack / "run_manifest.json"),
        args.run_id,
        prepare.sha256_file(Path(__file__).resolve()),
        prepare.sha256_file(smoke_runner),
    )
    dump_new(args.output.resolve(), plan)
    print(
        "sealed result-ineligible target-drift infrastructure smoke: "
        f"case={plan['source_case_id']}, replicate={plan['source_replicate']}, runs=3"
    )


if __name__ == "__main__":
    main()
