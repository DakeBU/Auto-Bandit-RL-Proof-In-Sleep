#!/usr/bin/env python3
"""Focused tests for the target-drift primary-grading blindness boundary."""

from __future__ import annotations

import copy
import sys
import unittest
from pathlib import Path


TOOLS = Path(__file__).resolve().parent
sys.path.insert(0, str(TOOLS))

import assemble_target_drift_grades as assemble  # noqa: E402
import prepare_target_drift_grading as grading  # noqa: E402


class TargetDriftGradingBlindnessTest(unittest.TestCase):
    def setUp(self) -> None:
        self.usage = {
            "input_tokens": 101,
            "cached_input_tokens": 11,
            "cache_write_input_tokens": 3,
            "output_tokens": 29,
            "reasoning_output_tokens": 7,
            "tool_calls": 5,
            "build_attempts": 2,
            "recovery_tool_calls": 1,
            "infrastructure_retries": 0,
            "wall_seconds": 14.5,
            "orchestrator_wall_seconds": 15.0,
            "model_cost_usd": 0.0123,
        }

    def test_primary_checker_evidence_strips_resource_metadata_recursively(self) -> None:
        raw = {
            "checker_pass": True,
            "neutral_build": {
                "exit_code": 0,
                "timed_out": False,
                "wall_seconds": 4.2,
                "nested": {"tool_calls": 3, "status": "completed"},
            },
            "execution_usage": copy.deepcopy(self.usage),
        }

        blind = grading.strip_primary_metadata(raw)
        grading.require_primary_metadata_blind(blind, "test packet")

        self.assertEqual(blind["neutral_build"]["exit_code"], 0)
        self.assertFalse(blind["neutral_build"]["timed_out"])
        self.assertEqual(blind["neutral_build"]["nested"], {"status": "completed"})
        self.assertNotIn("execution_usage", blind)
        self.assertNotIn("wall_seconds", blind["neutral_build"])

    def test_primary_packet_rejects_cost_time_token_and_tool_metadata(self) -> None:
        for key in sorted(grading.FORBIDDEN_PRIMARY_METADATA_KEYS):
            with self.subTest(key=key), self.assertRaises(SystemExit):
                grading.require_primary_metadata_blind(
                    {"neutral_checker": {"nested": {key: 1}}}, "test packet"
                )

    def test_primary_packet_rejects_direct_condition_and_run_identifiers(self) -> None:
        for payload in (
            {"condition": "abrl"},
            {"requirement_variant": "injected_drift"},
            {"semantic_run_id": "RUN-test"},
            {"neutral_checker": {"opaque_run_id": "OPAQUE-test"}},
            {"prompt_path": "prompts/abrl.md"},
        ):
            with self.subTest(payload=payload), self.assertRaises(SystemExit):
                grading.require_primary_metadata_blind(payload, "test packet")

        grading.require_primary_metadata_blind(
            {"grader_response_schema": {"condition_guess": ["abrl"]}},
            "test response schema",
        )

    def test_operator_mapping_restores_metrics_to_analysis_record(self) -> None:
        mapping_item = {
            "grade_id": "GRADE-test",
            "semantic_run_id": "RUN-test",
            "condition": "abrl",
            "requirement_variant": "source_faithful",
            "execution_metrics": copy.deepcopy(self.usage),
            "workflow_compliance_pass": True,
        }
        primary_packet = {
            "grade_id": "GRADE-test",
            "neutral_checker": {"checker_pass": True},
        }
        grading.require_primary_metadata_blind(primary_packet, "test packet")

        assembled_record = {
            "semantic_run_id": mapping_item["semantic_run_id"],
            "execution_metrics": assemble.operator_execution_metrics(mapping_item),
            "workflow_compliance_pass": assemble.operator_workflow_compliance(mapping_item),
        }

        self.assertNotIn("execution_metrics", primary_packet)
        self.assertNotIn("workflow_compliance_pass", primary_packet["neutral_checker"])
        self.assertEqual(assembled_record["execution_metrics"], self.usage)
        self.assertTrue(assembled_record["workflow_compliance_pass"])

    def test_operator_mapping_requires_execution_metrics(self) -> None:
        with self.assertRaises(SystemExit):
            assemble.operator_execution_metrics({"grade_id": "GRADE-missing"})

    def test_operator_mapping_requires_workflow_compliance(self) -> None:
        with self.assertRaises(SystemExit):
            assemble.operator_workflow_compliance({"grade_id": "GRADE-missing"})


if __name__ == "__main__":
    unittest.main()
