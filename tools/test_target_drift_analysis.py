#!/usr/bin/env python3

from __future__ import annotations

import sys
import unittest
from pathlib import Path


TOOLS = Path(__file__).resolve().parent
sys.path.insert(0, str(TOOLS))

import analyze_target_drift_execution as analysis  # noqa: E402
import prepare_target_drift_execution as prepare  # noqa: E402


class TargetDriftAnalysisTest(unittest.TestCase):
    def synthetic_records(self) -> list[dict]:
        records = []
        sources = ["paper-a", "paper-b", "paper-c"]
        for case_index in range(30):
            case_id = f"case-{case_index}"
            if case_index < 18:
                source_id = sources[case_index // 6]
                stratum = "paper_derived"
            else:
                source_id = "textbook"
                stratum = "textbook_control"
            for replicate_index in range(5):
                variant = prepare.requirement_variant(case_index, replicate_index)
                for condition in analysis.CONDITIONS:
                    records.append({
                        "semantic_run_id": f"{case_id}-{condition}-{replicate_index}",
                        "case_id": case_id,
                        "source_id": source_id,
                        "stratum": stratum,
                        "condition": condition,
                        "replicate": replicate_index,
                        "requirement_variant": variant,
                        "primary_pass": condition == "abrl",
                        "false_rejection": False,
                        "faithful_formal_completion": condition == "abrl",
                        "drift_detected": variant == "injected_drift" and condition == "abrl",
                        "unsupported_evidence_claim": False,
                        "source_amendment_required": False,
                        "artifact_replay_success": True,
                        "execution_metrics": {
                            "input_tokens": 10,
                            "output_tokens": 5,
                            "tool_calls": 2,
                            "build_attempts": 1,
                            "recovery_tool_calls": 0,
                            "infrastructure_retries": 0,
                            "wall_seconds": 1.0,
                            "orchestrator_wall_seconds": 1.1,
                            "cost_usd": 0.01,
                        },
                        "grader_condition_guesses": {
                            "grader-a": "compile_only",
                            "grader-b": condition,
                        },
                    })
        return records

    def test_target_level_analysis_uses_balanced_variants(self) -> None:
        result = analysis.analyze(
            {"records": self.synthetic_records()},
            seed=7,
            bootstrap_replicates=100,
            permutation_replicates=32768,
        )
        self.assertEqual(result["run_count"], 450)
        self.assertEqual(result["target_count"], 30)
        self.assertEqual(result["primary"]["point_estimate"], 1.0)
        self.assertEqual(
            result["primary"]["hierarchical_bootstrap_95_interval"], [1.0, 1.0]
        )
        self.assertEqual(result["primary"]["permutation_assignments"], 32768)
        for condition, rates in result["requirement_variant_rates"].items():
            expected = 1.0 if condition == "abrl" else 0.0
            self.assertEqual(rates["injected_drift_primary_pass_rate"], expected)
            self.assertEqual(rates["source_faithful_primary_pass_rate"], expected)
        self.assertEqual(result["grader_condition_guess_accuracy"]["grader-b"], 1.0)


if __name__ == "__main__":
    unittest.main()
