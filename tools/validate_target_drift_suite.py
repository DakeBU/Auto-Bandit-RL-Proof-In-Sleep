#!/usr/bin/env python3
"""Validate the frozen, result-free ABRL target-drift challenge bank."""

from __future__ import annotations

import json
import subprocess
import sys
from collections import Counter
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
SUITE = ROOT / "evaluation" / "target-drift-v1"
PAPER_SOURCES = {
    "PPR-SCHLISSELBERG-LANCEWICKI-AUER-MANSOUR-2025-DELAYED-BOBW",
    "PPR-ZENG-HONORIO-2025-SUCCINCT-LOWER-BOUNDS",
    "PPR-BAUDRY-JOHNSON-VARY-PIKEBURKE-REBESCHINI-2025-SGB",
}
PAPER_HASHES = {
    "PPR-SCHLISSELBERG-LANCEWICKI-AUER-MANSOUR-2025-DELAYED-BOBW": "525240c98b67616b4918bf5bffb799577f298786fc46538aff91153380ae0f9e",
    "PPR-ZENG-HONORIO-2025-SUCCINCT-LOWER-BOUNDS": "98e2511709b155e9e032b305c6fb1eb933237508f3ea4db76dbd229b6c5160b8",
    "PPR-BAUDRY-JOHNSON-VARY-PIKEBURKE-REBESCHINI-2025-SGB": "a3aff97fe2179c47fff61cc51453b84a082332e2a205f7fa2268cc68cba73b3d",
}
TEXTBOOK_HASH = "b71acb03034d73ca0ea148c9c6a91c34a88dd8c7ab8471af38035b34399bad9f"
DRIFT_CLASSES = {
    "objective",
    "random_index_information",
    "quantifier_scope",
    "conclusion_mode",
    "policy_semantics",
    "evidence_authority",
}
FORBIDDEN_RESULT_KEYS = {"result", "score", "outcome", "effect_size", "winner"}
REQUIRED_CASE_KEYS = {
    "id",
    "stratum",
    "source_id",
    "source_sha256",
    "source_locator",
    "drift_class",
    "faithful_contract",
    "injected_drift",
    "expected_affected_fields",
    "status",
}


def load(name: str) -> dict:
    return json.loads((SUITE / name).read_text(encoding="utf-8"))


def require(condition: bool, message: str) -> None:
    if not condition:
        raise SystemExit(f"target-drift validation failed: {message}")


def main() -> None:
    protocol = load("protocol.json")
    manifest = load("challenges.json")
    cases = manifest["cases"]

    require(
        protocol["execution_status"]
        == "challenge_bank_amended_pre_execution_execution_not_started",
        "execution status must record the result-free pre-execution amendment",
    )
    require(
        protocol.get("pre_execution_amendment_on") == "2026-08-26"
        and protocol.get("pre_execution_amendment_path")
        == "evaluation/source-contract-audit-v1/amendment.json"
        and protocol.get("outcomes_observed_before_amendment") is False
        and (ROOT / protocol["pre_execution_amendment_path"]).is_file(),
        "pre-execution amendment binding is missing or overstates outcomes",
    )
    require(len(cases) == protocol["challenge_count"] == 30, "expected 30 challenges")
    require(len(set(protocol["conditions"])) == 3, "expected three unique conditions")
    require(protocol["paired_seeds_per_condition"] == 5, "expected five paired seeds")
    require(protocol["planned_run_count"] == len(cases) * len(protocol["conditions"]) * protocol["paired_seeds_per_condition"], "planned run arithmetic is inconsistent")

    ids = [case["id"] for case in cases]
    require(len(ids) == len(set(ids)), "challenge ids must be unique")
    for case in cases:
        require(REQUIRED_CASE_KEYS <= case.keys(), f"{case.get('id', '<missing id>')} is missing required fields")
        require(case["status"] == "authored_unrun", f"{case['id']} must remain authored_unrun")
        require(case["drift_class"] in DRIFT_CLASSES, f"{case['id']} has an unknown drift class")
        require(bool(case["expected_affected_fields"]), f"{case['id']} has no adjudication fields")
        require(not (FORBIDDEN_RESULT_KEYS & case.keys()), f"{case['id']} contains result-shaped fields")

    by_stratum = Counter(case["stratum"] for case in cases)
    require(by_stratum == {"paper_derived": 18, "textbook_control": 12}, "stratum allocation must be 18/12")
    require(
        protocol.get("textbook_derived_control_count") == 10
        and protocol.get("internal_evidence_policy_control_count") == 2,
        "the historical textbook-control stratum must disclose its 10/2 origin split",
    )
    paper_cases = [case for case in cases if case["stratum"] == "paper_derived"]
    by_paper = Counter(case["source_id"] for case in paper_cases)
    require(set(by_paper) == PAPER_SOURCES, "paper-derived source set differs from the frozen portfolio")
    require(all(count == 6 for count in by_paper.values()), "each paper must contribute six probes")
    require(
        all(case["source_sha256"] == PAPER_HASHES[case["source_id"]] for case in paper_cases),
        "every paper probe must carry its exact frozen SHA-256",
    )

    textbook_cases = [case for case in cases if case["stratum"] == "textbook_control"]
    by_drift = Counter(case["drift_class"] for case in textbook_cases)
    require(set(by_drift) == DRIFT_CLASSES, "textbook controls must cover all six drift classes")
    require(all(count == 2 for count in by_drift.values()), "each textbook drift class must have two controls")
    require(
        all(case["source_sha256"] == TEXTBOOK_HASH for case in textbook_cases),
        "every textbook control must carry the exact frozen online-edition SHA-256",
    )

    execution_template = load("execution-template.json")
    require(execution_template["execution_status"] == "template_unfrozen",
            "execution template must remain explicitly unfrozen")
    require(bool(execution_template["unresolved_fields"]),
            "execution template must enumerate unresolved choices")
    rubric = load("grading-rubric.json")
    require(rubric["no_results"] is True, "grading rubric must remain result-free")
    require(not (SUITE / "results.json").exists(),
            "results.json is forbidden before the execution freeze and actual runs")
    subprocess.run(
        [sys.executable, str(ROOT / "tools" / "prepare_target_drift_execution.py"),
         "--check-template"],
        cwd=ROOT,
        check=True,
    )

    print("target-drift suite valid: 30 authored/unrun cases, pre-execution source amendment bound, 450 planned runs")


if __name__ == "__main__":
    main()
