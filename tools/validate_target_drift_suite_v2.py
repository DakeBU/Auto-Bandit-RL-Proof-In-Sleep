#!/usr/bin/env python3
"""Validate the balanced, still-unrun ABRL target-drift v2 protocol."""

from __future__ import annotations

import json
import subprocess
import sys
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
V1 = ROOT / "evaluation" / "target-drift-v1"
V2 = ROOT / "evaluation" / "target-drift-v2"
sys.path.insert(0, str(ROOT / "tools"))

import prepare_target_drift_execution as prepare  # noqa: E402
import audit_target_drift_wording as wording  # noqa: E402


def load(path: Path) -> dict:
    return json.loads(path.read_text(encoding="utf-8"))


def require(condition: bool, message: str) -> None:
    if not condition:
        raise SystemExit(f"target-drift v2 validation failed: {message}")


def main() -> None:
    protocol = load(V2 / "protocol.json")
    config = load(V2 / "execution-template.json")
    challenges = load(V1 / "challenges.json")["cases"]
    sources = load(V2 / "source-files.template.json")
    rubric = load(V2 / "grading-rubric.json")
    policy = load(V2 / "resource-policy.json")
    missing_policy = load(V2 / "missing-run-policy.json")
    paired = load(V2 / "paired-requirements.json")

    require(protocol["suite_id"] == config["suite_id"] == rubric["suite_id"]
            == policy["suite_id"] == missing_policy["suite_id"]
            == sources["suite_id"] == "ABRL-TARGET-DRIFT-V2",
            "suite identifiers differ")
    require(prepare.resolve_repo_path(config["protocol"]) == V2 / "protocol.json",
            "execution config must pin the v2 protocol path")
    require(protocol["execution_status"] == "balanced_variants_designed_execution_not_started",
            "v2 protocol must remain unrun")
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
