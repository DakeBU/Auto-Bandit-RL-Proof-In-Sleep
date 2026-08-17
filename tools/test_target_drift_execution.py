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
        paired_payload = json.loads(
            (ROOT / "evaluation" / "target-drift-v2" / "paired-requirements.json")
            .read_text(encoding="utf-8")
        )
        paired = paired_payload["cases"][0]
        agent_case = prepare.sanitized_case(
            case, source, paired, paired_payload["common_template"]
        )
        forbidden = {
            "faithful_contract",
            "expected_affected_fields",
            "drift_class",
            "stratum",
        }
        self.assertFalse(forbidden & agent_case.keys())
        self.assertIn(paired["injected_drift_value"], agent_case["injected_drift_requirement"])
        self.assertIn(paired["source_faithful_value"], agent_case["source_faithful_requirement"])
        prefix = "The proposed Lean target assigns the source-critical field"
        self.assertTrue(agent_case["source_faithful_requirement"].startswith(prefix))
        self.assertTrue(agent_case["injected_drift_requirement"].startswith(prefix))

    def test_v2_requirement_assignment_is_balanced_and_condition_paired(self) -> None:
        variants = [
            prepare.requirement_variant(case_index, replicate_index)
            for case_index in range(30)
            for replicate_index in range(5)
        ]
        self.assertEqual(variants.count("source_faithful"), 75)
        self.assertEqual(variants.count("injected_drift"), 75)

    def test_aggregate_digest_changes_for_every_sealed_component(self) -> None:
        config = {
            "sealed_agent_view": {"aggregate_sha256": "UNSET"},
            "model": {"immutable_version": "v1"},
        }
        components = prepare.digest_components(
            config,
            {"cases": []},
            {"runs": []},
            b"challenges",
            b"paired requirements",
            b"protocol",
            b"sources",
            {"source.pdf": b"pdf"},
            b"rubric",
            b"policy",
            b"adapter contract",
            b"grader prompt",
            b"text-only prompt",
            {condition: condition.encode() for condition in prepare.CONDITIONS},
            {"runner.py": b"runner"},
        )
        baseline, _ = prepare.aggregate_digest(components)
        for name in components:
            changed = dict(components)
            changed[name] += b"x"
            digest, _ = prepare.aggregate_digest(changed)
            self.assertNotEqual(digest, baseline, name)

    def test_preseal_and_frozen_status_have_the_same_normalized_config(self) -> None:
        preseal = {
            "execution_status": "preseal_ready",
            "sealed_agent_view": {"aggregate_sha256": "UNSET"},
            "unresolved_fields": ["sealed_agent_view.aggregate_sha256"],
        }
        frozen = {
            "execution_status": "frozen_ready",
            "sealed_agent_view": {"aggregate_sha256": "a" * 64},
            "unresolved_fields": [],
        }
        self.assertEqual(
            prepare.normalized_config_for_digest(preseal),
            prepare.normalized_config_for_digest(frozen),
        )

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
