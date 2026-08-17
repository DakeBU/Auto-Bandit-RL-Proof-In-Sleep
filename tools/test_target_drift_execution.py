#!/usr/bin/env python3
"""Tests for the result-free target-drift execution preparation layer."""

from __future__ import annotations

import json
import sys
import unittest
from pathlib import Path


TOOLS = Path(__file__).resolve().parent
ROOT = TOOLS.parent
sys.path.insert(0, str(TOOLS))

import prepare_target_drift_execution as prepare  # noqa: E402


class TargetDriftExecutionTest(unittest.TestCase):
    def test_template_and_prompts_validate_while_unfrozen(self) -> None:
        prepare.check_template(
            ROOT / "evaluation" / "target-drift-v1" / "execution-template.json"
        )

    def test_unset_paths_excludes_human_readable_ledger(self) -> None:
        value = {
            "model": {"id": "UNSET"},
            "sealed_agent_view": {"aggregate_sha256": "UNSET"},
            "unresolved_fields": ["UNSET is descriptive here"],
        }
        self.assertEqual(
            prepare.unset_paths(value),
            ["model.id", "sealed_agent_view.aggregate_sha256"],
        )

    def test_agent_case_strips_adjudication_keys(self) -> None:
        challenges = json.loads(
            (ROOT / "evaluation" / "target-drift-v1" / "challenges.json")
            .read_text(encoding="utf-8")
        )["cases"]
        case = challenges[0]
        source = {
            "sha256": case["source_sha256"],
            "resolved_path": "C:/sealed/source.pdf",
        }
        agent_case = prepare.sanitized_case(case, source)
        forbidden = {
            "faithful_contract",
            "expected_affected_fields",
            "drift_class",
            "stratum",
        }
        self.assertFalse(forbidden & agent_case.keys())
        self.assertEqual(agent_case["proposed_requirement"], case["injected_drift"])

    def test_every_source_revision_has_a_frozen_hash(self) -> None:
        source_manifest = json.loads(
            (ROOT / "evaluation" / "target-drift-v1" / "source-files.template.json")
            .read_text(encoding="utf-8")
        )
        for source in source_manifest["sources"]:
            digest = source["sha256"]
            self.assertEqual(len(digest), 64)
            self.assertTrue(all(character in "0123456789abcdef" for character in digest))


if __name__ == "__main__":
    unittest.main()
