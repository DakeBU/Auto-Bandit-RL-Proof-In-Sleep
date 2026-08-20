#!/usr/bin/env python3
"""Execute the sealed target-drift schedule once per run and continue after failures."""

from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path
from typing import Any


TOOLS = Path(__file__).resolve().parent
sys.path.insert(0, str(TOOLS))

import build_target_drift_completion_ledger as completion  # noqa: E402
import check_target_drift_run as checker  # noqa: E402
import prepare_target_drift_execution as prepare  # noqa: E402
import run_target_drift_execution as runner  # noqa: E402


TERMINAL_STATES = {
    "terminal_operator_failure",
    "checker_terminal_failure",
    "checked_fixture_nonexperimental",
    "checked",
}


def load(path: Path) -> dict[str, Any]:
    return json.loads(path.read_text(encoding="utf-8"))


def require(condition: bool, message: str) -> None:
    if not condition:
        raise SystemExit(f"target-drift schedule failed: {message}")


def self_verify(pack: Path, config: dict[str, Any]) -> None:
    expected = config["missing_run_policy"]["schedule_runner_sha256"]
    current = Path(__file__).resolve()
    sealed = pack / "execution_code" / current.name
    require(prepare.sha256_file(current) == expected,
            "invoked schedule runner differs from frozen hash")
    require(prepare.sha256_file(sealed) == expected,
            "sealed schedule runner differs from frozen hash")


def advance_run(pack: Path, runs_root: Path, planned: dict[str, Any]) -> dict[str, Any]:
    aggregate = (pack / "aggregate.sha256").read_text(encoding="ascii").strip()
    semantic_id = planned["run_id"]
    opaque_id = runner.opaque_id("run", aggregate, semantic_id)
    run_dir = runs_root / opaque_id
    if not run_dir.exists():
        runner.prepare_run(pack, semantic_id, run_dir)
    state_path = run_dir / "operator" / "run_state.json"
    state = load(state_path)
    require(state.get("opaque_run_id") == opaque_id, "run directory opaque ID mismatch")
    status_before = state.get("status")
    error = None
    if status_before == "prepared_unrun":
        try:
            runner.execute_or_record_failure(pack, run_dir)
        except (SystemExit, Exception) as caught:
            error = f"{type(caught).__name__}: {caught}"
    state = load(state_path)
    if state.get("status") == "executed_unchecked":
        try:
            checker.execute(pack, run_dir)
        except (checker.CheckerFailure, SystemExit, Exception) as caught:
            error = f"{type(caught).__name__}: {caught}"
    state = load(state_path)
    status_after = state.get("status")
    require(status_after in completion.KNOWN_STATES,
            f"run ended in an unknown state {status_after!r}")
    return {
        "semantic_run_id": semantic_id,
        "opaque_run_id": opaque_id,
        "status_before": status_before,
        "status_after": status_after,
        "terminal": status_after in TERMINAL_STATES,
        "error": error,
    }


def run_schedule(pack: Path, runs_root: Path) -> list[dict[str, Any]]:
    manifest = load(pack / "run_manifest.json")
    planned = sorted(manifest["runs"], key=lambda run: run["presentation_order"])
    require(len(planned) == 450, "schedule requires exactly 450 sealed runs")
    runs_root.mkdir(parents=True, exist_ok=True)
    events = []
    for index, run in enumerate(planned, 1):
        try:
            event = advance_run(pack, runs_root, run)
        except (SystemExit, Exception) as caught:
            aggregate = (pack / "aggregate.sha256").read_text(encoding="ascii").strip()
            semantic_id = run["run_id"]
            event = {
                "semantic_run_id": semantic_id,
                "opaque_run_id": runner.opaque_id("run", aggregate, semantic_id),
                "status_before": "not_materialized_or_unreadable",
                "status_after": "not_materialized_or_unreadable",
                "terminal": False,
                "error": f"{type(caught).__name__}: {caught}",
            }
        events.append(event)
        print(
            f"target-drift schedule {index}/450: {event['opaque_run_id']} "
            f"{event['status_before']} -> {event['status_after']}"
        )
    return events


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--pack", type=Path, required=True)
    parser.add_argument("--runs-root", type=Path, required=True)
    parser.add_argument("--completion-ledger", type=Path, required=True)
    args = parser.parse_args()
    pack = args.pack.resolve()
    prepare.verify_pack(pack)
    config = load(pack / "execution_config.json")
    require(config["execution_status"] == "frozen_ready",
            "schedule requires a frozen_ready pack")
    self_verify(pack, config)
    completion.self_verify(pack, config)
    completion.policy_from_pack(pack, config)
    events = run_schedule(pack, args.runs_root.resolve())
    ledger = completion.build_ledger(pack, args.runs_root.resolve())
    ledger["schedule_summary"] = {
        "attempted_in_sealed_presentation_order": True,
        "schedule_event_count": len(events),
        "terminal_event_count": sum(event["terminal"] for event in events),
        "events_with_operator_error": sum(event["error"] is not None for event in events),
    }
    completion.validate_ledger_against_runs(
        pack, args.runs_root.resolve(), ledger, require_complete=False,
    )
    completion.dump_new(args.completion_ledger.resolve(), ledger)
    missing = ledger["summary"]["missing_count"]
    print(f"target-drift schedule complete: eligible={450 - missing}/450, missing={missing}")
    if missing:
        raise SystemExit(2)


if __name__ == "__main__":
    main()
