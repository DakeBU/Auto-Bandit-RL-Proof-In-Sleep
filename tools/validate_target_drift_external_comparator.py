#!/usr/bin/env python3
"""Validate the separate, result-free LeanFlow calibration plan."""

from __future__ import annotations

import hashlib
import json
import re
import ast
import sys
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
V2 = ROOT / "evaluation" / "target-drift-v2"
PLAN = V2 / "external-comparator-plan.json"
SEAL = V2 / "external-comparator-plan.seal.json"
PRIMARY = V2 / "protocol.json"
RESULTS = V2 / "external-comparator-results.json"
ADAPTER_CONTRACT = V2 / "leanflow-adapter-contract.json"
SCHEDULE = V2 / "leanflow-external-schedule.json"
FIXTURE_REQUEST = V2 / "leanflow-excluded-fixture-request.json"
LEDGER_CONTRACT = V2 / "leanflow-external-completion-ledger-contract.json"
PLUMBING_SEAL = V2 / "leanflow-external-plumbing.seal.json"
COMPLETION_LEDGER = V2 / "leanflow-external-completion-ledger.json"
FAKE_ADAPTER = ROOT / "tools" / "fake_leanflow_target_drift_adapter.py"
SCHEDULE_BUILDER = ROOT / "tools" / "build_leanflow_target_drift_schedule.py"
LEDGER_BUILDER = ROOT / "tools" / "build_leanflow_target_drift_completion_ledger.py"

sys.path.insert(0, str(ROOT / "tools"))

import build_leanflow_target_drift_completion_ledger as ledger_builder  # noqa: E402
import build_leanflow_target_drift_schedule as schedule_builder  # noqa: E402
import fake_leanflow_target_drift_adapter as fake_adapter  # noqa: E402


def require(condition: bool, message: str) -> None:
    if not condition:
        raise SystemExit(f"external-comparator validation failed: {message}")


def load(path: Path) -> dict:
    value = json.loads(path.read_text(encoding="utf-8"))
    require(isinstance(value, dict), f"{path.name} must contain one JSON object")
    return value


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def validate_provider_disabled_plumbing(plan: dict) -> None:
    contract = load(ADAPTER_CONTRACT)
    schedule = load(SCHEDULE)
    fixture_request = load(FIXTURE_REQUEST)
    ledger_contract = load(LEDGER_CONTRACT)
    plumbing_seal = load(PLUMBING_SEAL)

    require(not RESULTS.exists(), "external comparator results are forbidden before execution")
    require(not COMPLETION_LEDGER.exists(),
            "production external completion ledger is forbidden before execution")

    expected_schedule = schedule_builder.build_schedule(
        PLAN,
        ROOT / "evaluation" / "target-drift-v1" / "challenges.json",
        V2 / "paired-requirements.json",
    )
    require(schedule == expected_schedule,
            "tracked external schedule is not the deterministic frozen 30-ID schedule")
    runs = schedule["runs"]
    require(len(runs) == 30
            and len({run["run_id"] for run in runs}) == 30
            and all(run["condition"] == "leanflow_external"
                    and run["replicate_index"] == 0
                    and run["status"] == "sealed_unrun"
                    for run in runs),
            "external schedule IDs, condition, replicate, or status differ")
    require(sum(run["requirement_variant"] == "source_faithful" for run in runs) == 15
            and sum(run["requirement_variant"] == "injected_drift" for run in runs) == 15,
            "external schedule is not balanced 15/15")
    primary_conditions = set(load(PRIMARY)["conditions"])
    require(all(run["condition"] not in primary_conditions for run in runs),
            "external semantic IDs overlap a primary condition")

    fake_adapter.validate_contract(contract)
    require(contract["external_comparator_plan_sha256"] == sha256(PLAN)
            and contract["schedule_sha256"] == sha256(SCHEDULE)
            and contract["fixture_entrypoint_sha256"] == sha256(FAKE_ADAPTER),
            "adapter contract hash bindings differ")
    forbidden_import_roots = {
        "anthropic", "httpx", "openai", "requests", "socket", "subprocess", "urllib",
    }
    tree = ast.parse(FAKE_ADAPTER.read_text(encoding="utf-8"), filename=str(FAKE_ADAPTER))
    imported_roots: set[str] = set()
    for node in ast.walk(tree):
        if isinstance(node, ast.Import):
            imported_roots.update(alias.name.split(".", 1)[0] for alias in node.names)
        elif isinstance(node, ast.ImportFrom) and node.module:
            imported_roots.add(node.module.split(".", 1)[0])
    require(not (imported_roots & forbidden_import_roots),
            "excluded fixture imports a provider, network, or subprocess module")

    first = runs[0]
    expected_opaque = hashlib.sha256((
        f"leanflow-excluded-fixture:{sha256(SCHEDULE)}:{first['run_id']}"
    ).encode("utf-8")).hexdigest()
    expected_request = {
        "schema_version": 1,
        "suite_id": "ABRL-TARGET-DRIFT-V2",
        "comparator_id": "leanflow_external",
        "adapter_mode": "excluded-fixture-smoke",
        "execution_purpose": "external_result_ineligible_fixture_smoke",
        "semantic_run_id": first["run_id"],
        "opaque_run_id": expected_opaque,
        "case_id": first["case_id"],
        "condition": first["condition"],
        "replicate_index": first["replicate_index"],
        "requirement_variant": first["requirement_variant"],
        "result_eligible": False,
        "provider_mode": "disabled",
        "network_allowed": False,
        "credential_access_allowed": False,
        "model_invocations_allowed": 0,
        "leanflow_repository_execution_allowed": False,
        "schedule_sha256": sha256(SCHEDULE),
        "adapter_contract_sha256": sha256(ADAPTER_CONTRACT),
    }
    require(fixture_request == expected_request,
            "excluded-fixture request is not the deterministic first scheduled ID")
    fake_adapter.validate_request(
        fixture_request, contract, sha256(ADAPTER_CONTRACT),
        schedule, sha256(SCHEDULE)
    )
    response, trace = fake_adapter.build_fixture_response(
        fixture_request, contract, sha256(FIXTURE_REQUEST), sha256(ADAPTER_CONTRACT),
        schedule, sha256(SCHEDULE)
    )
    require(response["status"] == "excluded_fixture_completed"
            and response["result_eligible"] is False
            and response["provider_called"] is False
            and response["credentials_read"] is False
            and response["network_used"] is False
            and response["leanflow_repository_executed"] is False
            and response["model_invocations"] == 0
            and response["formalization_outcome_reported"] is False
            and all(value == 0 for value in response["usage"].values()),
            "excluded fixture response crosses the result-free provider boundary")
    require([event["kind"] for event in trace]
            == contract["trace_schema"]["event_kinds_in_order"],
            "excluded fixture trace grammar differs")

    require(ledger_contract["schema_version"] == 1
            and ledger_contract["suite_id"] == "ABRL-TARGET-DRIFT-V2"
            and ledger_contract["comparator_id"] == "leanflow_external"
            and ledger_contract["status"] == "schema_frozen_results_absent"
            and ledger_contract["planned_run_count"] == 30
            and ledger_contract["schedule_sha256"] == sha256(SCHEDULE)
            and ledger_contract["builder_sha256"] == sha256(LEDGER_BUILDER)
            and ledger_contract["replacement_runs"] == "forbidden"
            and ledger_contract["outcome_imputation"] == "forbidden"
            and ledger_contract["tracked_completion_ledger_must_be_absent"] is True
            and ledger_contract["results_must_be_absent"] is True,
            "external completion-ledger contract differs")
    ledger = ledger_builder.build_result_free_ledger(
        schedule, ledger_contract, sha256(SCHEDULE)
    )
    ledger_builder.validate_result_free_ledger(ledger, schedule, ledger_contract)
    require(len(ledger["records"]) == 30
            and ledger["result_eligible_count"] == 0
            and ledger["missing_count"] == 30
            and ledger["outcomes_observed"] is False
            and ledger["complete_analysis_gate_passed"] is False
            and ledger["effect_estimates_permitted"] is False,
            "result-free completion-ledger structure admits an outcome or analysis")

    require(plumbing_seal == {
        "schema_version": 1,
        "suite_id": "ABRL-TARGET-DRIFT-V2",
        "comparator_id": "leanflow_external",
        "sealed_on": "2026-08-25",
        "amended_pre_execution_on": "2026-08-26",
        "integrity_resealed_on": "2026-08-27",
        "provider_calls_observed_before_integrity_reseal": False,
        "formalization_outcomes_observed_before_integrity_reseal": False,
        "status": "sealed_result_free_provider_disabled_fixture_plumbing",
        "external_comparator_plan_path": (
            "evaluation/target-drift-v2/external-comparator-plan.json"
        ),
        "external_comparator_plan_sha256": sha256(PLAN),
        "adapter_contract_path": (
            "evaluation/target-drift-v2/leanflow-adapter-contract.json"
        ),
        "adapter_contract_sha256": sha256(ADAPTER_CONTRACT),
        "schedule_path": "evaluation/target-drift-v2/leanflow-external-schedule.json",
        "schedule_sha256": sha256(SCHEDULE),
        "fixture_request_path": (
            "evaluation/target-drift-v2/leanflow-excluded-fixture-request.json"
        ),
        "fixture_request_sha256": sha256(FIXTURE_REQUEST),
        "completion_ledger_contract_path": (
            "evaluation/target-drift-v2/leanflow-external-completion-ledger-contract.json"
        ),
        "completion_ledger_contract_sha256": sha256(LEDGER_CONTRACT),
        "fixture_entrypoint_path": "tools/fake_leanflow_target_drift_adapter.py",
        "fixture_entrypoint_sha256": sha256(FAKE_ADAPTER),
        "schedule_builder_path": "tools/build_leanflow_target_drift_schedule.py",
        "schedule_builder_sha256": sha256(SCHEDULE_BUILDER),
        "completion_ledger_builder_path": (
            "tools/build_leanflow_target_drift_completion_ledger.py"
        ),
        "completion_ledger_builder_sha256": sha256(LEDGER_BUILDER),
        "provider_calls_observed_at_seal": False,
        "formalization_outcomes_observed_at_seal": False,
        "results_path": "evaluation/target-drift-v2/external-comparator-results.json",
        "completion_ledger_path": (
            "evaluation/target-drift-v2/leanflow-external-completion-ledger.json"
        ),
        "results_and_completion_ledger_must_be_absent": True,
    }, "LeanFlow plumbing seal differs from the provider-disabled artifacts")


def main() -> None:
    plan = load(PLAN)
    seal = load(SEAL)
    primary = load(PRIMARY)
    require(plan["schema_version"] == 1
            and plan["suite_id"] == primary["suite_id"]
            == "ABRL-TARGET-DRIFT-V2", "suite identity differs")
    require(plan["frozen_on"] == "2026-08-24"
            and plan["amended_pre_execution_on"] == "2026-08-26"
            and plan["integrity_resealed_on"] == "2026-08-27"
            and plan["primary_outcomes_observed_before_integrity_reseal"] is False
            and plan["comparator_outcomes_observed_before_integrity_reseal"] is False
            and plan["status"] == "planned_unrun_result_free"
            and plan["purpose"]
            == "external_system_calibration_not_primary_causal_condition",
            "plan status or purpose is not the frozen result-free calibration")
    require(plan["primary_protocol"]
            == "evaluation/target-drift-v2/protocol.json"
            and plan["primary_protocol_sha256"] == sha256(PRIMARY)
            and plan["primary_outcomes_observed_at_freeze"] is False
            and plan["comparator_outcomes_observed_at_freeze"] is False,
            "plan does not preserve the versioned pre-execution protocol boundary")
    require(seal == {
        "schema_version": 1,
        "suite_id": "ABRL-TARGET-DRIFT-V2",
        "sealed_on": "2026-08-24",
        "amended_pre_execution_on": "2026-08-26",
        "integrity_resealed_on": "2026-08-27",
        "primary_outcomes_observed_before_integrity_reseal": False,
        "comparator_outcomes_observed_before_integrity_reseal": False,
        "status": "frozen_result_free_external_comparator_plan",
        "plan_path": "evaluation/target-drift-v2/external-comparator-plan.json",
        "plan_sha256": sha256(PLAN),
        "primary_protocol_path": "evaluation/target-drift-v2/protocol.json",
        "primary_protocol_sha256": sha256(PRIMARY),
        "primary_outcomes_observed_at_seal": False,
        "comparator_outcomes_observed_at_seal": False,
    }, "external comparator seal differs from the frozen plan or primary bytes")
    require(primary["frozen_on"] == "2026-08-18"
            and primary["planned_run_count"] == 450,
            "primary protocol identity changed")
    require(not RESULTS.exists(), "external comparator results are forbidden before execution")

    system = plan["system"]
    for field, pattern in (
        ("repository_commit", r"[0-9a-f]{40}"),
        ("paper_pdf_sha256_observed_2026_08_24", r"[0-9a-f]{64}"),
        ("repository_commit_time_utc", r"\d{4}-\d{2}-\d{2}T\d{2}:\d{2}:\d{2}Z"),
        ("repository_ref_observed_on", r"\d{4}-\d{2}-\d{2}"),
    ):
        require(re.fullmatch(pattern, system[field]) is not None,
                f"system {field} is malformed")
    require(system["name"] == "LeanFlow"
            and system["paper_url"] == "https://arxiv.org/abs/2607.20503"
            and system["repository_url"] == "https://github.com/epfl-lara/LeanFlow"
            and system["repository_commit"]
            == "72a58a5ffe3d26710e8e0a5d0f4e9bcaab3fed4d"
            and system["repository_commit_time_utc"] == "2026-08-11T02:39:36Z"
            and system["repository_ref_observed_on"] == plan["frozen_on"]
            and system["license"] == "Apache-2.0",
            "LeanFlow source identity or license is not pinned")

    design = plan["design"]
    balance = design["hidden_variant_balance"]
    require(design["planned_external_run_count"] == 30
            and design["primary_study_run_count_unchanged"] == 450
            and design["selected_replicate_index"] == 0
            and balance == {
                "source_faithful": 15,
                "injected_drift": 15,
                "assignment": "the primary suite parity rule evaluated at replicate index zero",
            }, "external schedule or hidden-variant balance changed")
    require(design["external_condition_id"] not in primary["conditions"]
            and len(design["prespecified_contrasts"]) == 2
            and all("replicate index zero" in item
                    for item in design["prespecified_contrasts"]),
            "external run IDs or contrasts are not fixed and disjoint")
    forbidden = ("no p-value", "winner/rank", "superiority", "equivalence",
                 "noninferiority", "selective headline")
    boundary = design["analysis_boundary"].lower()
    require(all(marker in boundary for marker in forbidden),
            "analysis boundary leaves post-hoc inferential freedom")
    require("30/30" in design["missing_run_policy"]
            and "no replacement" in design["missing_run_policy"].lower()
            and "no outcome imputation" in design["missing_run_policy"].lower(),
            "external missing-run gate is incomplete")
    require(len(design["required_fairness_bindings"]) >= 13,
            "external fairness bindings are incomplete")
    fairness = " ".join(design["required_fairness_bindings"]).lower()
    require("system-general workflow assets" in fairness
            and "case-specific and cross-system assets are forbidden" in fairness
            and "rather than claimed equal" in fairness,
            "system-specific workflow assets are not bounded or disclosed")
    require("system-level descriptive contrast" in " ".join(
                design["prespecified_contrasts"]).lower()
            and "not mechanism-level resource-equated comparisons" in boundary,
            "external contrasts overclaim resource-equated mechanisms")
    require(len(plan["execution_gate"]) >= 5 and len(plan["nonclaims"]) >= 5,
            "execution gates or nonclaims are incomplete")
    validate_provider_disabled_plumbing(plan)
    print(
        "external comparator plan valid and unrun: LeanFlow commit "
        f"{system['repository_commit'][:12]}, 30 cases at replicate index 0, "
        "15 faithful + 15 drifted, two descriptive contrasts, primary 450 unchanged, "
        "provider-disabled excluded fixture valid, result and completion ledger absent, "
        f"plan_sha256={sha256(PLAN)}, seal_sha256={sha256(SEAL)}, "
        f"schedule_sha256={sha256(SCHEDULE)}"
    )


if __name__ == "__main__":
    main()
