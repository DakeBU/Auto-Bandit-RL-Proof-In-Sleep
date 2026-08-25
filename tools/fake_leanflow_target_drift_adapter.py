#!/usr/bin/env python3
"""Provider-disabled LeanFlow adapter fixture for local plumbing tests only.

This module intentionally has no network or subprocess capability.  It accepts
only the exact excluded-fixture request schema and emits no formalization result.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import stat
from pathlib import Path
from typing import Any


ADAPTER_ID = "leanflow-excluded-fixture"
ADAPTER_VERSION = "1"
MODE = "excluded-fixture-smoke"


def require(condition: bool, message: str) -> None:
    if not condition:
        raise SystemExit(f"LeanFlow excluded-fixture adapter failed: {message}")


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def load_regular_object(path: Path, label: str) -> dict[str, Any]:
    info = path.lstat()
    require(stat.S_ISREG(info.st_mode) and not path.is_symlink(),
            f"{label} is not a plain regular file")
    require(info.st_nlink == 1, f"{label} is hard-linked")
    value = json.loads(path.read_text(encoding="utf-8"))
    require(isinstance(value, dict), f"{label} must contain one JSON object")
    return value


def validate_contract(contract: dict[str, Any]) -> None:
    require(contract.get("schema_version") == 1, "contract schema_version must be 1")
    require(contract.get("suite_id") == "ABRL-TARGET-DRIFT-V2", "suite differs")
    require(contract.get("comparator_id") == "leanflow_external", "comparator differs")
    require(contract.get("status") == "provider_disabled_result_free_fixture_only",
            "contract does not keep the provider disabled")
    capability = contract.get("execution_capability", {})
    require(capability == {
        "allowed_mode": MODE,
        "credential_access_allowed": False,
        "leanflow_repository_execution_allowed": False,
        "model_invocations_allowed": 0,
        "network_allowed": False,
        "provider_mode": "disabled",
        "real_adapter_available": False,
        "subprocess_allowed": False,
    }, "execution capability is not the exact excluded-fixture boundary")


def validate_request(
    request: dict[str, Any], contract: dict[str, Any], contract_sha256: str,
    schedule: dict[str, Any], schedule_sha256: str,
) -> None:
    validate_contract(contract)
    request_contract = contract["request_schema"]
    required = set(request_contract["required_fields"])
    allowed = set(request_contract["allowed_fields"])
    require(set(request) == allowed and required <= set(request),
            "request fields differ from the exact allowlist")
    require(request.get("schema_version") == 1, "request schema_version must be 1")
    require(request.get("suite_id") == contract["suite_id"], "request suite differs")
    require(request.get("comparator_id") == contract["comparator_id"],
            "request comparator differs")
    require(request.get("condition") == contract["comparator_id"],
            "request condition differs")
    require(request.get("adapter_mode") == MODE, "only excluded-fixture-smoke is allowed")
    require(request.get("execution_purpose") == "external_result_ineligible_fixture_smoke",
            "execution purpose is not the excluded fixture")
    require(request.get("result_eligible") is False,
            "fixture request may never be result-eligible")
    require(request.get("provider_mode") == "disabled", "provider must be disabled")
    require(request.get("network_allowed") is False, "network must be disabled")
    require(request.get("credential_access_allowed") is False,
            "credential access must be disabled")
    require(request.get("model_invocations_allowed") == 0,
            "model invocation budget must be zero")
    require(request.get("leanflow_repository_execution_allowed") is False,
            "LeanFlow repository execution must be disabled")
    require(request.get("replicate_index") == 0, "replicate index must be zero")
    require(request.get("requirement_variant") in {"source_faithful", "injected_drift"},
            "requirement variant is not part of the frozen two-variant design")
    case_id = request.get("case_id")
    require(isinstance(case_id, str) and case_id,
            "case_id must be a nonempty string")
    require(request.get("semantic_run_id")
            == f"{case_id}--leanflow_external--replicate-0",
            "semantic run ID is not deterministic")
    for field in ("opaque_run_id", "schedule_sha256"):
        value = request.get(field)
        require(isinstance(value, str) and len(value) == 64
                and all(character in "0123456789abcdef" for character in value),
                f"{field} must be a lowercase SHA-256 value")
    require(request.get("schedule_sha256") == contract["schedule_sha256"],
            "request names different schedule bytes")
    require(schedule_sha256 == contract["schedule_sha256"],
            "loaded schedule bytes differ from the contract binding")
    require(request.get("adapter_contract_sha256") == contract_sha256,
            "request names different adapter-contract bytes")
    require(schedule.get("comparator_id") == contract["comparator_id"],
            "schedule comparator differs")
    require(schedule.get("provider_execution_enabled") is False
            and schedule.get("outcomes_observed") is False,
            "schedule is not the sealed-unrun provider-disabled schedule")
    runs = schedule.get("runs")
    require(isinstance(runs, list), "schedule runs must be a list")
    matches = [
        run for run in runs
        if isinstance(run, dict)
        and run.get("run_id") == request["semantic_run_id"]
    ]
    require(len(matches) == 1, "request is not a unique scheduled run")
    scheduled = matches[0]
    for field in ("case_id", "condition", "replicate_index", "requirement_variant"):
        require(request.get(field) == scheduled.get(field),
                f"request {field} differs from the sealed schedule")
    require(scheduled.get("status") == "sealed_unrun",
            "scheduled run is not sealed_unrun")
    expected_opaque = hashlib.sha256((
        f"leanflow-excluded-fixture:{schedule_sha256}:"
        f"{request['semantic_run_id']}"
    ).encode("utf-8")).hexdigest()
    require(request.get("opaque_run_id") == expected_opaque,
            "opaque run ID differs from the schedule-bound derivation")


def build_fixture_response(
    request: dict[str, Any], contract: dict[str, Any],
    request_sha256: str, contract_sha256: str,
    schedule: dict[str, Any], schedule_sha256: str,
) -> tuple[dict[str, Any], list[dict[str, Any]]]:
    validate_request(
        request, contract, contract_sha256, schedule, schedule_sha256
    )
    zero_usage = {
        "input_tokens": 0,
        "output_tokens": 0,
        "reasoning_output_tokens": 0,
        "tool_calls": 0,
        "build_attempts": 0,
        "wall_seconds": 0,
        "cost_usd": 0,
    }
    response = {
        "schema_version": 1,
        "suite_id": request["suite_id"],
        "comparator_id": request["comparator_id"],
        "adapter_id": ADAPTER_ID,
        "adapter_version": ADAPTER_VERSION,
        "adapter_mode": MODE,
        "semantic_run_id": request["semantic_run_id"],
        "opaque_run_id": request["opaque_run_id"],
        "execution_purpose": request["execution_purpose"],
        "status": "excluded_fixture_completed",
        "termination": "fixture_only_no_provider",
        "result_eligible": False,
        "provider_mode": "disabled",
        "provider_called": False,
        "network_used": False,
        "credentials_read": False,
        "leanflow_repository_executed": False,
        "model_invocations": 0,
        "formalization_outcome_reported": False,
        "request_sha256": request_sha256,
        "adapter_contract_sha256": contract_sha256,
        "usage": zero_usage,
    }
    trace = [
        {"sequence": 0, "kind": "excluded_fixture_started"},
        {"sequence": 1, "kind": "provider_disabled_request_validated"},
        {
            "sequence": 2,
            "kind": "excluded_fixture_summary",
            "result_eligible": False,
            "provider_called": False,
            "model_invocations": 0,
            "formalization_outcome_reported": False,
        },
    ]
    return response, trace


def write_new_json(path: Path, value: Any) -> None:
    require(not path.exists(), f"refusing to overwrite {path}")
    path.parent.mkdir(parents=True, exist_ok=True)
    with path.open("x", encoding="utf-8", newline="\n") as handle:
        json.dump(value, handle, indent=2, sort_keys=True, ensure_ascii=False)
        handle.write("\n")


def write_new_jsonl(path: Path, events: list[dict[str, Any]]) -> None:
    require(not path.exists(), f"refusing to overwrite {path}")
    path.parent.mkdir(parents=True, exist_ok=True)
    with path.open("x", encoding="utf-8", newline="\n") as handle:
        for event in events:
            handle.write(json.dumps(event, sort_keys=True, ensure_ascii=False) + "\n")


def preflight_output_paths(
    response_path: Path, trace_path: Path, forbidden_names: set[str]
) -> None:
    require(response_path != trace_path, "response and trace paths must differ")
    require(response_path.name not in forbidden_names
            and trace_path.name not in forbidden_names,
            "fixture adapter may not create a comparator results or production-ledger file")
    require(not response_path.exists(), f"refusing to overwrite {response_path}")
    require(not trace_path.exists(), f"refusing to overwrite {trace_path}")


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--mode", required=True, choices=[MODE])
    parser.add_argument("--contract", type=Path, required=True)
    parser.add_argument("--schedule", type=Path, required=True)
    parser.add_argument("--request", type=Path, required=True)
    parser.add_argument("--response", type=Path, required=True)
    parser.add_argument("--trace", type=Path, required=True)
    args = parser.parse_args()
    contract_path = args.contract.resolve()
    schedule_path = args.schedule.resolve()
    request_path = args.request.resolve()
    response_path = args.response.resolve()
    trace_path = args.trace.resolve()
    contract = load_regular_object(contract_path, "adapter contract")
    schedule = load_regular_object(schedule_path, "sealed schedule")
    request = load_regular_object(request_path, "fixture request")
    forbidden_names = set(contract["forbidden_output_basenames"])
    preflight_output_paths(response_path, trace_path, forbidden_names)
    response, trace = build_fixture_response(
        request, contract, sha256(request_path), sha256(contract_path),
        schedule, sha256(schedule_path),
    )
    write_new_json(response_path, response)
    write_new_jsonl(trace_path, trace)
    print(
        "LeanFlow excluded fixture completed: provider disabled, 0 model calls, "
        "no formalization outcome, result-ineligible"
    )


if __name__ == "__main__":
    main()
