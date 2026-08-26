#!/usr/bin/env python3
"""Validate the balanced, still-unrun ABRL target-drift v2 protocol."""

from __future__ import annotations

import json
import subprocess
import sys
from pathlib import Path
from typing import Any


ROOT = Path(__file__).resolve().parents[1]
V1 = ROOT / "evaluation" / "target-drift-v1"
V2 = ROOT / "evaluation" / "target-drift-v2"
sys.path.insert(0, str(ROOT / "tools"))

import prepare_target_drift_execution as prepare  # noqa: E402
import audit_target_drift_wording as wording  # noqa: E402


WORDING_RECORD_SCHEMA_VERSION = 1
WORDING_AUDIT_SCHEMA_VERSION = 1
WORDING_SUITE_ID = "ABRL-TARGET-DRIFT-V2"
WORDING_RECORD_COMMAND = (
    "python tools/audit_target_drift_wording.py "
    "--bank evaluation/target-drift-v2/paired-requirements.json"
)
WORDING_RECORD_KEYS = frozenset({
    "schema_version", "suite_id", "status", "result_eligible", "command",
    "input", "script", "audit",
})
WORDING_BINDING_KEYS = frozenset({"path", "sha256"})
WORDING_AUDIT_KEYS = frozenset({
    "schema_version",
    "suite_id",
    "paired_case_count",
    "rendered_requirement_count",
    "identical_template",
    "legacy_style_marker_hits",
    "deterministic_leave_one_pair_out_bernoulli_nb_accuracy",
    "interpretation",
})


def load(path: Path) -> dict:
    return json.loads(path.read_text(encoding="utf-8"))


def require(condition: bool, message: str) -> None:
    if not condition:
        raise SystemExit(f"target-drift v2 validation failed: {message}")


def require_exact_keys(value: Any, expected: frozenset[str], label: str) -> None:
    require(isinstance(value, dict), f"{label} must be an object")
    actual = set(value)
    missing = expected - actual
    extra = actual - expected
    require(
        not missing and not extra,
        f"{label} keys differ; missing={sorted(map(str, missing))}, "
        f"extra={sorted(map(str, extra))}",
    )


def validate_wording_negative_control_record(
    record: dict[str, Any],
    wording_result: dict[str, Any],
    *,
    protocol_suite_id: str,
    paired_path: Path,
    wording_script: Path,
) -> None:
    """Validate the checked-in result-ineligible wording record fail-closed."""
    require_exact_keys(record, WORDING_RECORD_KEYS, "wording negative-control record")
    require_exact_keys(record["input"], WORDING_BINDING_KEYS, "wording record input")
    require_exact_keys(record["script"], WORDING_BINDING_KEYS, "wording record script")
    require_exact_keys(record["audit"], WORDING_AUDIT_KEYS, "wording record audit")
    require_exact_keys(wording_result, WORDING_AUDIT_KEYS, "recomputed wording audit")

    require(
        type(record["schema_version"]) is int
        and record["schema_version"] == WORDING_RECORD_SCHEMA_VERSION,
        f"wording record schema_version must be {WORDING_RECORD_SCHEMA_VERSION}",
    )
    require(
        type(record["audit"]["schema_version"]) is int
        and record["audit"]["schema_version"] == WORDING_AUDIT_SCHEMA_VERSION,
        f"wording record audit schema_version must be {WORDING_AUDIT_SCHEMA_VERSION}",
    )
    require(
        type(wording_result["schema_version"]) is int
        and wording_result["schema_version"] == WORDING_AUDIT_SCHEMA_VERSION,
        f"recomputed wording audit schema_version must be {WORDING_AUDIT_SCHEMA_VERSION}",
    )
    require(
        protocol_suite_id == WORDING_SUITE_ID
        and record["suite_id"] == WORDING_SUITE_ID
        and record["audit"]["suite_id"] == WORDING_SUITE_ID
        and wording_result["suite_id"] == WORDING_SUITE_ID,
        "wording negative-control suite identifier differs",
    )
    require(
        record["status"] == "deterministic_result_free_negative_control"
        and record["result_eligible"] is False,
        "wording negative-control record has the wrong authority or status",
    )
    require(
        type(record["command"]) is str
        and record["command"] == WORDING_RECORD_COMMAND,
        "wording negative-control command differs from the frozen command",
    )
    require(
        record["input"]["path"]
        == "evaluation/target-drift-v2/paired-requirements.json"
        and record["input"]["sha256"] == prepare.sha256_file(paired_path),
        "wording negative-control input binding is stale",
    )
    require(
        record["script"]["path"] == "tools/audit_target_drift_wording.py"
        and record["script"]["sha256"] == prepare.sha256_file(wording_script),
        "wording negative-control script binding is stale",
    )
    require(
        record["audit"] == wording_result,
        "wording negative-control result does not reproduce",
    )


def main() -> None:
    protocol = load(V2 / "protocol.json")
    config = load(V2 / "execution-template.json")
    challenges = load(V1 / "challenges.json")["cases"]
    sources = load(V2 / "source-files.template.json")
    rubric = load(V2 / "grading-rubric.json")
    policy = load(V2 / "resource-policy.json")
    missing_policy = load(V2 / "missing-run-policy.json")
    paired = load(V2 / "paired-requirements.json")
    wording_record = load(V2 / "wording-negative-control-record.json")

    require(protocol["suite_id"] == config["suite_id"] == rubric["suite_id"]
            == policy["suite_id"] == missing_policy["suite_id"]
            == sources["suite_id"] == "ABRL-TARGET-DRIFT-V2",
            "suite identifiers differ")
    require(prepare.resolve_repo_path(config["protocol"]) == V2 / "protocol.json",
            "execution config must pin the v2 protocol path")
    require(
        protocol["execution_status"]
        == "balanced_variants_amended_pre_execution_execution_not_started",
        "v2 protocol must record the result-free pre-execution amendment",
    )
    require(
        protocol.get("pre_execution_amendment_on") == "2026-08-26"
        and protocol.get("pre_execution_amendment_path")
        == "evaluation/source-contract-audit-v1/amendment.json"
        and protocol.get("outcomes_observed_before_amendment") is False
        and (ROOT / protocol["pre_execution_amendment_path"]).is_file(),
        "v2 pre-execution amendment binding is missing or overstates outcomes",
    )
    require(
        protocol.get("grading_blinding_integrity_patch_on") == "2026-08-27"
        and protocol.get("outcomes_observed_before_grading_blinding_patch") is False,
        "v2 grading-blinding integrity patch is missing or overstates outcomes",
    )
    require(
        protocol.get("primary_analysis_integrity_patch_on") == "2026-08-27"
        and protocol.get("outcomes_observed_before_primary_analysis_patch") is False,
        "v2 primary-analysis integrity patch is missing or overstates outcomes",
    )
    require(
        protocol.get("primary_interval_method_id")
        == config["analysis"].get("primary_interval_method_id")
        == "fixed_30_target_variant_preserving_paired_invocation_bootstrap_v1",
        "v2 primary interval method differs across protocol and execution template",
    )
    require(
        protocol.get("primary_success_rule")
        == config["analysis"].get("primary_success_rule"),
        "v2 primary success rule differs across protocol and execution template",
    )
    require(
        protocol.get("textbook_derived_control_count") == 10
        and protocol.get("internal_evidence_policy_control_count") == 2,
        "v2 control-stratum 10/2 origin split differs",
    )
    require(config["execution_status"] == "template_unfrozen",
            "v2 execution template must remain unfrozen")
    require(len(challenges) == protocol["base_challenge_count"] == 30,
            "v2 must reuse exactly thirty frozen v1 cases")
    require(protocol["planned_run_count"] == 450, "planned run count must be 450")
    require(missing_policy["policy_id"] == config["retry_policy"]["missing_run_policy"]
            == config["missing_run_policy"]["policy_id"]
            == "complete_450_no_replacement_no_imputation_v1",
            "missing-run policy ID differs across protocol inputs")
    require(missing_policy["planned_run_count"] == 450
            and missing_policy["replacement_runs"] == "forbidden"
            and missing_policy["outcome_imputation"] == "forbidden",
            "missing-run policy weakens the exact 450-run gate")
    variants = [
        prepare.requirement_variant(case_index, replicate_index)
        for case_index in range(30)
        for replicate_index in range(5)
    ]
    require(variants.count("source_faithful") == 75, "expected 75 faithful pairs")
    require(variants.count("injected_drift") == 75, "expected 75 drifted pairs")
    require(rubric["no_results"] is True, "rubric must remain result-free")
    require(not (V2 / "results.json").exists(), "results.json forbidden before execution")
    prepare.validate_paired_requirements(config, challenges)
    wording_result = wording.audit(paired)
    require(wording_result["legacy_style_marker_hits"] == 0,
            "paired wording contains a deterministic legacy style marker")
    require(
        wording_result["deterministic_leave_one_pair_out_bernoulli_nb_accuracy"] <= 2 / 3,
        "deterministic text-only diagnostic exceeds the frozen two-thirds gate",
    )
    wording_script = ROOT / "tools" / "audit_target_drift_wording.py"
    validate_wording_negative_control_record(
        wording_record,
        wording_result,
        protocol_suite_id=protocol["suite_id"],
        paired_path=V2 / "paired-requirements.json",
        wording_script=wording_script,
    )

    base = protocol["workspace_base_commit"]
    require(base == config["workspace_base_commit"] == policy["workspace_base_commit"],
            "workspace base commits differ")
    subprocess.run(["git", "cat-file", "-e", f"{base}^{{commit}}"], cwd=ROOT, check=True)
    tree = subprocess.check_output(
        ["git", "ls-tree", "-r", "--name-only", base], cwd=ROOT, text=True
    ).splitlines()
    require(not any(path.startswith("evaluation/") for path in tree),
            "pre-audit workspace base unexpectedly contains evaluation artifacts")
    require(not any("DelayedFeedback" in path for path in tree),
            "pre-audit workspace base unexpectedly contains case-specific delayed audit files")

    require(len(sources["sources"]) == 4, "expected four source files")
    challenge_hashes = {case["source_id"]: case["source_sha256"] for case in challenges}
    require(all(challenge_hashes[source["source_id"]] == source["sha256"]
                for source in sources["sources"]),
            "v2 source hashes differ from the frozen challenge bank")
    prepare.check_template(V2 / "execution-template.json")
    print(
        "target-drift v2 valid and unrun: 30 bases, 75 faithful + 75 drifted "
        "target-replicate pairs, 450 planned runs, pre-audit workspace base verified"
        f", wording NB={wording_result['deterministic_leave_one_pair_out_bernoulli_nb_accuracy']:.3f}"
    )


if __name__ == "__main__":
    main()
