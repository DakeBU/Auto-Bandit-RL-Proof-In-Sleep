#!/usr/bin/env python3
"""Validate the separate, result-free LeanFlow calibration plan."""

from __future__ import annotations

import hashlib
import json
import re
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
V2 = ROOT / "evaluation" / "target-drift-v2"
PLAN = V2 / "external-comparator-plan.json"
SEAL = V2 / "external-comparator-plan.seal.json"
PRIMARY = V2 / "protocol.json"
RESULTS = V2 / "external-comparator-results.json"


def require(condition: bool, message: str) -> None:
    if not condition:
        raise SystemExit(f"external-comparator validation failed: {message}")


def load(path: Path) -> dict:
    value = json.loads(path.read_text(encoding="utf-8"))
    require(isinstance(value, dict), f"{path.name} must contain one JSON object")
    return value


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main() -> None:
    plan = load(PLAN)
    seal = load(SEAL)
    primary = load(PRIMARY)
    require(plan["schema_version"] == 1
            and plan["suite_id"] == primary["suite_id"]
            == "ABRL-TARGET-DRIFT-V2", "suite identity differs")
    require(plan["frozen_on"] == "2026-08-24"
            and plan["status"] == "planned_unrun_result_free"
            and plan["purpose"]
            == "external_system_calibration_not_primary_causal_condition",
            "plan status or purpose is not the frozen result-free calibration")
    require(plan["primary_protocol"]
            == "evaluation/target-drift-v2/protocol.json"
            and plan["primary_protocol_sha256"] == sha256(PRIMARY)
            and plan["primary_outcomes_observed_at_freeze"] is False
            and plan["comparator_outcomes_observed_at_freeze"] is False,
            "plan does not preserve the original primary-protocol boundary")
    require(seal == {
        "schema_version": 1,
        "suite_id": "ABRL-TARGET-DRIFT-V2",
        "sealed_on": "2026-08-24",
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
    print(
        "external comparator plan valid and unrun: LeanFlow commit "
        f"{system['repository_commit'][:12]}, 30 cases at replicate index 0, "
        "15 faithful + 15 drifted, two descriptive contrasts, primary 450 unchanged, "
        f"plan_sha256={sha256(PLAN)}, seal_sha256={sha256(SEAL)}"
    )


if __name__ == "__main__":
    main()
