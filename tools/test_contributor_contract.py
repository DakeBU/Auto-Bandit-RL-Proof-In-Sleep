from __future__ import annotations

import json
import tempfile
import unittest
from pathlib import Path

from tools import check_contributor_contract as contract


def base_contract() -> dict:
    return {
        "schema_version": "2.0",
        "id": "TEST-CONTRACT",
        "route": "internal",
        "frontier_cell": "n/a",
        "source_facing": False,
        "source": {
            "kind": "internal-design",
            "title": "test",
            "version": "test",
            "anchor": "test",
            "url": ""
        },
        "target": "test target",
        "affected_files": ["website/content/example.json"],
        "declarations": [],
        "reuse_plan": {
            "classification": "out_of_scope",
            "decision": "out_of_scope",
            "searched_existing": [],
            "reused_declarations": [],
            "new_shared_declarations": [],
            "known_consumers": [],
            "planned_consumers": [],
            "no_duplicate_wrapper": True,
            "decision_reason": "tooling-only fixture"
        },
        "reader_contract": {
            "source_anchor_visible": False,
            "natural_language_formula_proof": False,
            "hidden_assumptions_visible": False,
            "source_vs_lean_delta_visible": False,
            "lean_folded": False,
            "dependencies_visible": False,
            "remaining_boundary_visible": False
        },
        "semantic_roundtrip": {
            "required": False,
            "status": "not-required",
            "formalizer": "fixture",
            "blind_decoder": "",
            "source_reviewer": "",
            "verdict": "not-required",
            "remaining_semantic_delta": "n/a"
        },
        "graph_contribution": {
            "lean_graph": "no-change-with-reason",
            "overview_graph": "updated",
            "functor_hypergraph": "none-found-with-reason",
            "functor_reason": "fixture does not add mathematics",
            "focus_targets": [],
            "visual_review": "fixture",
            "edge_semantics": "formal-solid; overlays-dashed"
        },
        "progress_updates": {
            "teaching_route": "no-change: fixture",
            "banditrlwiki": "no-change: fixture",
            "results_ledger": "no-change: fixture",
            "roadmap": "no-change: fixture",
            "website_surfaces": ["fixture"]
        },
        "truth_boundary": "fixture only",
        "verification": {
            "focused_checks": [],
            "bandit_check": "fixture",
            "site_build": "fixture",
            "site_check": "fixture",
            "independent_review": "fixture"
        },
        "contributor": {"name": "fixture", "role": "test"}
    }


def validate(payload: dict) -> list[str]:
    with tempfile.TemporaryDirectory() as directory:
        path = Path(directory) / "contract.json"
        path.write_text(json.dumps(payload), encoding="utf-8")
        _data, errors = contract.validate_contract(path)
        return errors


class ContributorContractTests(unittest.TestCase):
    def test_internal_design_contract_can_be_valid(self) -> None:
        self.assertEqual(validate(base_contract()), [])

    def test_source_facing_requires_distinct_accepted_reviewers(self) -> None:
        payload = base_contract()
        payload["source_facing"] = True
        payload["source"]["kind"] = "paper"
        payload["reader_contract"] = {
            key: True for key in contract.READER_REQUIRED
        }
        payload["semantic_roundtrip"] = {
            "required": True,
            "status": "accepted",
            "formalizer": "same-agent",
            "blind_decoder": "same-agent",
            "source_reviewer": "reviewer",
            "verdict": "accepted",
            "remaining_semantic_delta": "none"
        }
        errors = validate(payload)
        self.assertTrue(any("roles must be distinct" in error for error in errors))

    def test_new_shared_requires_two_consumers(self) -> None:
        payload = base_contract()
        payload["reuse_plan"]["classification"] = "missing"
        payload["reuse_plan"]["decision"] = "new_shared"
        payload["reuse_plan"]["new_shared_declarations"] = ["BanditRLProof.Shared.foo"]
        payload["reuse_plan"]["planned_consumers"] = ["route:a"]
        errors = validate(payload)
        self.assertTrue(any("at least two named consumers" in error for error in errors))


if __name__ == "__main__":
    unittest.main()
