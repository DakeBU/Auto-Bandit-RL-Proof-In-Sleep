#!/usr/bin/env python3

from __future__ import annotations

import hashlib
import json
import sys
import unittest
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
TOOLS = Path(__file__).resolve().parent
sys.path.insert(0, str(TOOLS))

import analyze_target_drift_execution as analysis  # noqa: E402
import prepare_target_drift_execution as prepare  # noqa: E402


class TargetDriftAnalysisTest(unittest.TestCase):
    def synthetic_records(self, outcome=None) -> list[dict]:
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
                    record = {
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
                        "drift_detected": (
                            variant == "injected_drift" and condition == "abrl"
                        ),
                        "unsupported_evidence_claim": False,
                        "source_amendment_required": False,
                        "artifact_replay_success": True,
                        "execution_metrics": {
                            "input_tokens": 10,
                            "cached_input_tokens": 2,
                            "cache_write_input_tokens": 1,
                            "output_tokens": 5,
                            "reasoning_output_tokens": 1,
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
                    }
                    if outcome is not None:
                        record.update(outcome(case_index, replicate_index, variant, condition))
                    records.append(record)
        return records

    def analyze(self, records: list[dict], bootstrap_replicates: int = 100) -> dict:
        return analysis.analyze(
            {"records": records},
            seed=7,
            bootstrap_replicates=bootstrap_replicates,
            permutation_replicates=32768,
        )

    def test_fixed_benchmark_analysis_machine_checks_all_success_gates(self) -> None:
        result = self.analyze(self.synthetic_records())
        self.assertEqual(result["run_count"], 450)
        self.assertEqual(result["target_count"], 30)
        primary = result["primary"]
        self.assertEqual(primary["point_estimate"], 1.0)
        self.assertEqual(
            primary["fixed_benchmark_invocation_bootstrap_95_interval"], [1.0, 1.0]
        )
        self.assertEqual(primary["estimand_population"], "the fixed set of 30 frozen targets only")
        self.assertIn("not provider seeds", primary["replicate_semantics"])
        sign_flip = primary["exact_sign_flip_15_unit_sensitivity"]
        self.assertEqual(sign_flip["enumerated_assignments"], 32768)
        self.assertAlmostEqual(sign_flip["two_sided_pvalue"], 1 / 16384)
        self.assertEqual(sign_flip["status"], "preregistered_sensitivity_analysis")
        self.assertTrue(primary["success_rule"]["all_required_gates_passed"])
        self.assertEqual(primary["success_rule"]["status"], "passed")
        self.assertTrue(all(
            gate["passed"] for gate in primary["success_rule"]["gates"].values()
        ))
        self.assertEqual(
            set(primary["leave_one_paper_out_fixed_benchmark_point_estimates"]),
            {"paper-a", "paper-b", "paper-c"},
        )
        target_rates = result["target_weighted_variant_rates"]["conditions"]
        self.assertEqual(
            result["target_weighted_variant_rates"]["analysis_role"],
            "target_weighted_fixed_benchmark_inferential_reporting",
        )
        self.assertEqual(target_rates["abrl"]["injected_drift_detection_sensitivity"], 1.0)
        self.assertEqual(target_rates["abrl"]["faithful_request_specificity"], 1.0)
        raw = result["raw_run_weighted_variant_counts_and_rates"]
        self.assertEqual(raw["status"], "descriptive_only")
        self.assertEqual(raw["conditions"]["abrl"]["run_count"], 150)

    def test_null_effect_has_zero_interval_unit_pvalue_and_failed_success(self) -> None:
        def null(_case, _replicate, _variant, condition):
            return {
                "primary_pass": False,
                "faithful_formal_completion": False,
                "drift_detected": False,
                "grader_condition_guesses": {
                    "grader-a": "compile_only", "grader-b": condition,
                },
            }

        result = self.analyze(self.synthetic_records(null))
        primary = result["primary"]
        self.assertEqual(primary["point_estimate"], 0.0)
        self.assertEqual(
            primary["fixed_benchmark_invocation_bootstrap_95_interval"], [0.0, 0.0]
        )
        self.assertEqual(
            primary["exact_sign_flip_15_unit_sensitivity"]["two_sided_pvalue"], 1.0
        )
        self.assertFalse(primary["success_rule"]["all_required_gates_passed"])
        self.assertFalse(
            primary["success_rule"]["gates"]["interval_lower_above_zero"]["passed"]
        )

    def test_mixed_target_effect_is_equal_target_weighted(self) -> None:
        def mixed(case, _replicate, _variant, condition):
            if condition == "abrl":
                value = case % 2 == 0
            elif condition == "source_aware_blueprint":
                value = case % 3 == 0
            else:
                value = False
            return {
                "primary_pass": value,
                "faithful_formal_completion": value,
            }

        result = self.analyze(self.synthetic_records(mixed))
        self.assertAlmostEqual(result["primary"]["point_estimate"], 1 / 6)
        self.assertEqual(
            result["primary"]["fixed_benchmark_invocation_bootstrap_95_interval"],
            [1 / 6, 1 / 6],
        )
        by_stratum = result["primary_source_stratified_condition_means"]["by_stratum"]
        self.assertEqual(set(by_stratum), {"paper_derived", "textbook_control"})

    def test_target_weighted_and_raw_run_weighted_variant_rates_are_distinct(self) -> None:
        def unequal(case, _replicate, variant, condition):
            return {
                "drift_detected": (
                    condition == "abrl" and variant == "injected_drift" and case % 2 == 0
                )
            }

        result = self.analyze(self.synthetic_records(unequal))
        target_rate = result["target_weighted_variant_rates"]["conditions"]["abrl"][
            "injected_drift_detection_sensitivity"
        ]
        raw = result["raw_run_weighted_variant_counts_and_rates"]["conditions"]["abrl"]
        raw_rate = raw["injected_drift"]["drift_detected"]["rate"]
        self.assertEqual(target_rate, 0.5)
        self.assertEqual(raw_rate, 0.6)
        self.assertEqual(raw["injected_drift"]["drift_detected"]["count"], 45)

    def test_non_2_3_variant_cell_is_rejected(self) -> None:
        records = self.synthetic_records()
        cell = [
            record for record in records
            if record["case_id"] == "case-0" and record["condition"] == "abrl"
        ]
        faithful = next(
            record for record in cell if record["requirement_variant"] == "source_faithful"
        )
        faithful["requirement_variant"] = "injected_drift"
        with self.assertRaises(SystemExit):
            self.analyze(records)

    def test_exact_sign_flip_uses_fifteen_dependence_units(self) -> None:
        differences = {f"case-{index}": 1.0 for index in range(30)}
        metadata = {
            f"case-{index}": {
                "source_id": (
                    f"paper-{index // 6}" if index < 18 else "textbook"
                ),
                "stratum": "paper_derived" if index < 18 else "textbook_control",
            }
            for index in range(30)
        }
        pvalue, assignments = analysis.source_aware_exact_sign_flip_pvalue(
            differences, metadata
        )
        self.assertEqual(assignments, 32768)
        self.assertAlmostEqual(pvalue, 1 / 16384)
        boundary = analysis.sign_flip_sensitivity_record(pvalue, assignments)
        self.assertEqual(boundary["dependence_units"], 15)
        self.assertIn("not an estimate for a population", boundary["inference_boundary"])

    def test_wrong_fixed_cluster_structure_is_rejected(self) -> None:
        records = self.synthetic_records()
        for record in records:
            if record["case_id"] == "case-0":
                record["source_id"] = "paper-b"
        with self.assertRaises(SystemExit):
            self.analyze(records)

    def test_benjamini_hochberg_known_fixture(self) -> None:
        adjusted = analysis.benjamini_hochberg({
            "a": 0.01, "b": 0.04, "c": 0.03, "d": 0.20,
        })
        self.assertAlmostEqual(adjusted["a"], 0.04)
        self.assertAlmostEqual(adjusted["b"], 0.04 * 4 / 3)
        self.assertAlmostEqual(adjusted["c"], 0.04 * 4 / 3)
        self.assertAlmostEqual(adjusted["d"], 0.20)

    def test_success_rule_fails_a_negative_leave_one_paper_out_gate(self) -> None:
        rates = analysis.target_weighted_variant_rates(self.synthetic_records())
        record = analysis.primary_success_record(
            [0.1, 0.2], {"paper-a": 0.1, "paper-b": -0.01, "paper-c": 0.2}, rates
        )
        self.assertEqual(record["status"], "failed")
        self.assertFalse(record["gates"]["leave_one_paper_out_nonnegative"]["passed"])
        self.assertTrue(record["gates"]["interval_lower_above_zero"]["passed"])

    def test_malformed_execution_metric_is_rejected(self) -> None:
        for field, value in (
            ("input_tokens", -1),
            ("tool_calls", 1.5),
            ("orchestrator_wall_seconds", -0.1),
            ("wall_seconds", float("nan")),
            ("cost_usd", float("inf")),
        ):
            with self.subTest(field=field):
                records = self.synthetic_records()
                records[0]["execution_metrics"][field] = value
                with self.assertRaises(SystemExit):
                    self.analyze(records)

        records = self.synthetic_records()
        records[0]["execution_metrics"]["cached_input_tokens"] = 11
        with self.assertRaises(SystemExit):
            self.analyze(records)

    def test_method_amendment_is_result_free_and_hash_bound(self) -> None:
        amendment_path = (
            ROOT / "evaluation" / "target-drift-v2"
            / "method-amendment-fixed-benchmark-itt-2026-08-26.json"
        )
        amendment = json.loads(amendment_path.read_text(encoding="utf-8"))
        self.assertEqual(amendment["suite_id"], "ABRL-TARGET-DRIFT-V2")
        self.assertEqual(
            amendment["status"], "hash_bound_pre_execution_method_amendment_results_absent"
        )
        timing = amendment["timing_and_claim_boundary"]
        self.assertFalse(timing["primary_model_outcomes_observed"])
        self.assertFalse(timing["external_comparator_outcomes_observed"])
        self.assertFalse(timing["provider_calls_for_evaluation_observed"])
        amendment_sha256 = hashlib.sha256(amendment_path.read_bytes()).hexdigest()
        readme = (amendment_path.parent / "README.md").read_text(encoding="utf-8")
        self.assertIn(amendment_sha256, readme)
        for binding in amendment["bindings"].values():
            path = ROOT / binding["path"]
            self.assertEqual(hashlib.sha256(path.read_bytes()).hexdigest(), binding["sha256"])


if __name__ == "__main__":
    unittest.main()
