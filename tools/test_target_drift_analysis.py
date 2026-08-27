#!/usr/bin/env python3

from __future__ import annotations

import contextlib
import io
import json
import hashlib
import os
import random
import sys
import tempfile
import unittest
from pathlib import Path
from unittest import mock


TOOLS = Path(__file__).resolve().parent
ROOT = TOOLS.parent
sys.path.insert(0, str(TOOLS))

import analyze_target_drift_execution as analysis  # noqa: E402
import assemble_target_drift_grades as assemble  # noqa: E402
import prepare_target_drift_grading as grading  # noqa: E402
import prepare_target_drift_execution as prepare  # noqa: E402


class TargetDriftAnalysisTest(unittest.TestCase):
    def synthetic_records(self, outcome=None) -> list[dict]:
        if outcome is None:
            outcome = lambda condition, _case, _replicate, _variant: condition == "abrl"
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
                    primary_pass = outcome(
                        condition, case_index, replicate_index, variant
                    )
                    records.append({
                        "semantic_run_id": f"{case_id}-{condition}-{replicate_index}",
                        "case_id": case_id,
                        "source_id": source_id,
                        "stratum": stratum,
                        "condition": condition,
                        "replicate": replicate_index,
                        "requirement_variant": variant,
                        "primary_pass": primary_pass,
                        "false_rejection": False,
                        "faithful_formal_completion": primary_pass,
                        "drift_detected": variant == "injected_drift" and primary_pass,
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
                    })
        return records

    def paired(self, records: list[dict]) -> dict[str, dict[str, list[float]]]:
        return analysis.paired_primary_invocations(records)

    def test_execution_template_freezes_matching_primary_analysis(self) -> None:
        config = json.loads((
            ROOT / "evaluation" / "target-drift-v2" / "execution-template.json"
        ).read_text(encoding="utf-8"))
        frozen = config["analysis"]
        self.assertIn("fixed-30-target", frozen["primary_estimand"])
        self.assertIn("variant-preserving paired-invocation", frozen["primary_interval"])
        self.assertEqual(
            frozen["primary_pairing_key"],
            ["case_id", "replicate", "requirement_variant"],
        )
        self.assertEqual(
            frozen["primary_interval_method_id"],
            analysis.PRIMARY_BOOTSTRAP_METHOD_ID,
        )
        self.assertNotIn("hierarchical bootstrap", frozen["primary_interval"])

    def test_analyzer_entrypoint_rejects_primary_contract_drift(self) -> None:
        config = json.loads((
            ROOT / "evaluation" / "target-drift-v2" / "execution-template.json"
        ).read_text(encoding="utf-8"))
        frozen = config["analysis"]
        analysis.validate_primary_analysis_config(frozen)
        changed = dict(frozen)
        changed["primary_success_rule"] = "declare success from the point estimate"
        with self.assertRaises(SystemExit):
            analysis.validate_primary_analysis_config(changed)

    def test_complete_analyzer_requires_the_bound_grader_export(self) -> None:
        with tempfile.TemporaryDirectory() as raw_root:
            root = Path(raw_root)
            pack = root / "pack"
            execution_code = pack / "execution_code"
            execution_code.mkdir(parents=True)
            (root / "runs").mkdir()
            output = root / "analysis.json"
            completion_ledger_path = root / "completion-ledger.json"

            analyzer_path = Path(analysis.__file__).resolve()
            prepare_path = Path(prepare.__file__).resolve()
            analyzer_hash = hashlib.sha256(analyzer_path.read_bytes()).hexdigest()
            prepare_hash = hashlib.sha256(prepare_path.read_bytes()).hexdigest()
            (execution_code / analyzer_path.name).write_bytes(analyzer_path.read_bytes())
            (execution_code / prepare_path.name).write_bytes(prepare_path.read_bytes())

            template = json.loads((
                ROOT / "evaluation" / "target-drift-v2" / "execution-template.json"
            ).read_text(encoding="utf-8"))
            frozen_analysis = dict(template["analysis"])
            frozen_analysis["script_sha256"] = analyzer_hash
            config = {
                "suite_id": "ABRL-TARGET-DRIFT-V2",
                "analysis": frozen_analysis,
                "sealed_agent_view": {"materializer_sha256": prepare_hash},
            }
            (pack / "execution_config.json").write_text(
                json.dumps(config), encoding="utf-8"
            )
            (pack / "aggregate.sha256").write_text("1" * 64 + "\n", encoding="ascii")
            completion_ledger_path.write_text(
                json.dumps({"primary_analysis_permitted": True}), encoding="utf-8"
            )

            argv = [
                str(analyzer_path),
                "--pack", str(pack),
                "--runs-root", str(root / "runs"),
                "--completion-ledger", str(completion_ledger_path),
                "--grading-pack", str(root / "internal-grading-pack"),
                "--grades", str(root / "grades.json"),
                "--output", str(output),
            ]
            with contextlib.ExitStack() as stack:
                stack.enter_context(mock.patch.object(sys, "argv", argv))
                stack.enter_context(mock.patch.object(analysis.prepare, "verify_pack"))
                stack.enter_context(mock.patch.object(analysis.completion, "self_verify"))
                stack.enter_context(mock.patch.object(
                    analysis.completion, "validate_ledger_against_runs"
                ))
                with self.assertRaisesRegex(
                    SystemExit,
                    "complete analysis requires --grading-pack, --grader-export, --grades",
                ):
                    analysis.main()

            self.assertFalse(os.path.lexists(output))

    def test_analyzer_reconstructs_and_rejects_a_forged_grade_ledger(self) -> None:
        sealed_pack_sha256 = "1" * 64
        grading_pack_sha256 = "2" * 64
        grader_export_sha256 = "3" * 64
        runtime_sha256 = "4" * 64
        probe_sha256 = "5" * 64
        policy_id = "complete-only-v1"
        policy_sha256 = "6" * 64

        with tempfile.TemporaryDirectory() as raw_root:
            root = Path(raw_root)
            pack = root / "pack"
            execution_code = pack / "execution_code"
            execution_code.mkdir(parents=True)
            runs_root = root / "runs"
            grading_pack = root / "internal-grading-pack"
            grader_export = root / "grader-export"
            for path in (runs_root, grading_pack, grader_export):
                path.mkdir()

            analyzer_path = Path(analysis.__file__).resolve()
            prepare_path = Path(prepare.__file__).resolve()
            grading_path = Path(grading.__file__).resolve()
            assembler_path = Path(assemble.__file__).resolve()
            source_hashes = {
                path.name: hashlib.sha256(path.read_bytes()).hexdigest()
                for path in (analyzer_path, prepare_path, grading_path, assembler_path)
            }
            for source in (analyzer_path, prepare_path, grading_path, assembler_path):
                (execution_code / source.name).write_bytes(source.read_bytes())

            config = json.loads((
                ROOT / "evaluation" / "target-drift-v2" / "execution-template.json"
            ).read_text(encoding="utf-8"))
            config["analysis"]["script_sha256"] = source_hashes[analyzer_path.name]
            config["analysis"]["grade_assembler_sha256"] = source_hashes[
                assembler_path.name
            ]
            config["sealed_agent_view"]["materializer_sha256"] = source_hashes[
                prepare_path.name
            ]
            config["grading"]["packet_materializer_sha256"] = source_hashes[
                grading_path.name
            ]
            config["posthoc_checker"]["mode"] = "production"
            config["posthoc_checker"]["runtime_config_sha256"] = runtime_sha256
            config["posthoc_checker"][
                "isolation_probe_report_sha256"
            ] = probe_sha256
            (pack / "execution_config.json").write_text(
                json.dumps(config), encoding="utf-8"
            )
            (pack / "aggregate.sha256").write_text(
                sealed_pack_sha256 + "\n", encoding="ascii"
            )

            completion_ledger_path = root / "completion-ledger.json"
            completion_ledger = {
                "primary_analysis_permitted": True,
                "missing_run_policy_id": policy_id,
                "missing_run_policy_sha256": policy_sha256,
            }
            completion_ledger_path.write_text(
                json.dumps(completion_ledger, sort_keys=True) + "\n",
                encoding="utf-8",
            )
            completion_sha256 = prepare.sha256_file(completion_ledger_path)

            internal = {
                "manifest": {
                    "aggregate_sha256": grading_pack_sha256,
                    "completion_ledger_sha256": completion_sha256,
                    "missing_run_policy_id": policy_id,
                    "missing_run_policy_sha256": policy_sha256,
                    "result_eligible": True,
                    "checker_mode": "production",
                    "checker_runtime_config_sha256": runtime_sha256,
                    "isolation_probe_report_sha256": probe_sha256,
                },
            }
            forged_ledger = {
                "schema_version": 2,
                "sealed_pack_sha256": sealed_pack_sha256,
                "grading_pack_sha256": grading_pack_sha256,
                "grader_export_sha256": grader_export_sha256,
                "grade_assembler_sha256": source_hashes[assembler_path.name],
                "completion_ledger_sha256": completion_sha256,
                "missing_run_policy_id": policy_id,
                "missing_run_policy_sha256": policy_sha256,
                "result_eligible": True,
                "checker_mode": "production",
                "checker_runtime_config_sha256": runtime_sha256,
                "isolation_probe_report_sha256": probe_sha256,
                "records": [{"forged": True}],
            }
            grade_ledger_path = root / "forged-grades.json"
            grade_ledger_path.write_bytes(grading.canonical_json_bytes(forged_ledger))
            response_paths = [root / "response-a.json", root / "response-b.json"]
            for path in response_paths:
                path.write_text("{}\n", encoding="utf-8")
            adjudication_path = root / "adjudication.json"
            adjudication_path.write_text("{}\n", encoding="utf-8")
            output = root / "analysis.json"

            def reconstruct(command, **_kwargs):
                rebuilt_path = Path(command[command.index("--output") + 1])
                rebuilt_path.write_bytes(b'{"canonical": true}\n')
                return mock.Mock(returncode=0, stdout="", stderr="")

            argv = [
                str(analyzer_path),
                "--pack", str(pack),
                "--runs-root", str(runs_root),
                "--completion-ledger", str(completion_ledger_path),
                "--grading-pack", str(grading_pack),
                "--grader-export", str(grader_export),
                "--grades", str(grade_ledger_path),
                "--grader-response", str(response_paths[0]),
                "--grader-response", str(response_paths[1]),
                "--adjudication", str(adjudication_path),
                "--output", str(output),
            ]
            with contextlib.ExitStack() as stack:
                stack.enter_context(mock.patch.object(sys, "argv", argv))
                stack.enter_context(mock.patch.object(analysis.prepare, "verify_pack"))
                stack.enter_context(mock.patch.object(analysis.completion, "self_verify"))
                stack.enter_context(mock.patch.object(
                    analysis.completion, "validate_ledger_against_runs"
                ))
                stack.enter_context(mock.patch.object(
                    analysis.prepare,
                    "checker_runtime_config_sha256",
                    return_value=runtime_sha256,
                ))
                stack.enter_context(mock.patch.object(
                    analysis.grading,
                    "validate_internal_grading_pack_against_runs",
                    return_value=internal,
                ))
                stack.enter_context(mock.patch.object(
                    analysis.grading,
                    "validate_grader_export",
                    return_value={"grader_export_sha256": grader_export_sha256},
                ))
                subprocess_mock = stack.enter_context(mock.patch.object(
                    analysis.subprocess, "run", side_effect=reconstruct
                ))
                analyze_mock = stack.enter_context(mock.patch.object(analysis, "analyze"))
                with self.assertRaisesRegex(
                    SystemExit,
                    "supplied grade ledger differs from sealed-input reconstruction",
                ):
                    analysis.main()

            subprocess_mock.assert_called_once()
            analyze_mock.assert_not_called()
            self.assertFalse(os.path.lexists(output))

    def test_analysis_output_must_be_separate_from_every_input_tree(self) -> None:
        with tempfile.TemporaryDirectory() as raw_root:
            root = Path(raw_root)
            pack = root / "pack"
            execution_code = pack / "execution_code"
            execution_code.mkdir(parents=True)
            sources = {
                "sealed pack": pack,
                "runs root": root / "runs",
                "internal grading-pack": root / "internal",
                "grader-only export": root / "export",
            }
            for label, path in sources.items():
                if label != "sealed pack":
                    path.mkdir()

            analyzer_path = Path(analysis.__file__).resolve()
            prepare_path = Path(prepare.__file__).resolve()
            (execution_code / analyzer_path.name).write_bytes(analyzer_path.read_bytes())
            (execution_code / prepare_path.name).write_bytes(prepare_path.read_bytes())
            config = json.loads((
                ROOT / "evaluation" / "target-drift-v2" / "execution-template.json"
            ).read_text(encoding="utf-8"))
            config["analysis"]["script_sha256"] = hashlib.sha256(
                analyzer_path.read_bytes()
            ).hexdigest()
            config["sealed_agent_view"]["materializer_sha256"] = hashlib.sha256(
                prepare_path.read_bytes()
            ).hexdigest()
            (pack / "execution_config.json").write_text(
                json.dumps(config), encoding="utf-8"
            )
            (pack / "aggregate.sha256").write_text("1" * 64 + "\n", encoding="ascii")
            completion_ledger_path = root / "completion-ledger.json"
            completion_ledger_path.write_text(
                json.dumps({"primary_analysis_permitted": True}) + "\n",
                encoding="utf-8",
            )

            for label, source in sources.items():
                output = source / "analysis.json"
                argv = [
                    str(analyzer_path),
                    "--pack", str(pack),
                    "--runs-root", str(sources["runs root"]),
                    "--completion-ledger", str(completion_ledger_path),
                    "--grading-pack", str(sources["internal grading-pack"]),
                    "--grader-export", str(sources["grader-only export"]),
                    "--grades", str(root / "grades.json"),
                    "--grader-response", str(root / "response-a.json"),
                    "--grader-response", str(root / "response-b.json"),
                    "--adjudication", str(root / "adjudication.json"),
                    "--output", str(output),
                ]
                with self.subTest(input_tree=label), contextlib.ExitStack() as stack:
                    stack.enter_context(mock.patch.object(sys, "argv", argv))
                    stack.enter_context(mock.patch.object(
                        analysis.prepare, "verify_pack"
                    ))
                    stack.enter_context(mock.patch.object(
                        analysis.completion, "self_verify"
                    ))
                    stack.enter_context(mock.patch.object(
                        analysis.completion, "validate_ledger_against_runs"
                    ))
                    with self.assertRaisesRegex(SystemExit, "must be separate trees"):
                        analysis.main()
                self.assertFalse(os.path.lexists(output))

    def test_analyzer_cli_rejects_expected_count_override(self) -> None:
        argv = [
            "analyze_target_drift_execution.py",
            "--pack", "pack",
            "--runs-root", "runs",
            "--completion-ledger", "completion.json",
            "--output", "analysis.json",
            "--expected-count", "1",
        ]
        stderr = io.StringIO()
        with mock.patch.object(sys, "argv", argv), contextlib.redirect_stderr(
            stderr
        ), self.assertRaises(SystemExit) as raised:
            analysis.main()
        self.assertEqual(raised.exception.code, 2)
        self.assertIn("unrecognized arguments: --expected-count 1", stderr.getvalue())

    def test_complete_analysis_reports_fixed_target_paired_bootstrap(self) -> None:
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
            result["primary"][
                "fixed_target_variant_preserving_paired_invocation_bootstrap_95_interval"
            ],
            [1.0, 1.0],
        )
        self.assertIn("fixed-30-target", result["primary"]["estimand"])
        self.assertEqual(result["schema_version"], analysis.ANALYSIS_SCHEMA_VERSION)
        self.assertEqual(
            result["primary"]["bootstrap_method_id"],
            analysis.PRIMARY_BOOTSTRAP_METHOD_ID,
        )
        self.assertEqual(
            result["primary"]["success_rule"],
            prepare.PRIMARY_ANALYSIS_SUCCESS_RULE,
        )
        self.assertIn("new independent invocations", result["primary"]["generalization_scope"])
        self.assertIn("does not imply shared provider RNG", result["primary"]["pairing_interpretation"])
        sensitivity = result["primary"]["sensitivity_analyses"]
        self.assertEqual(
            sensitivity["source_aware_exact_sign_flip"]["assignments"], 32768
        )
        self.assertEqual(
            result["primary"]["variant_quota_patterns"],
            {
                "injected_drift=2;source_faithful=3": 15,
                "injected_drift=3;source_faithful=2": 15,
            },
        )
        for condition, rates in result["requirement_variant_rates"].items():
            expected = 1.0 if condition == "abrl" else 0.0
            self.assertEqual(rates["injected_drift_primary_pass_rate"], expected)
            self.assertEqual(rates["source_faithful_primary_pass_rate"], expected)
        self.assertEqual(result["grader_condition_guess_accuracy"]["grader-b"], 1.0)

    def test_missing_primary_pair_fails_closed(self) -> None:
        records = self.synthetic_records()
        record = next(
            record for record in records
            if record["case_id"] == "case-0"
            and record["replicate"] == 0
            and record["condition"] == "abrl"
        )
        record["condition"] = "compile_only"
        with self.assertRaisesRegex(SystemExit, "missing a condition"):
            analysis.analyze(
                {"records": records}, 1, 1, 32768
            )

    def test_duplicate_primary_pair_fails_closed(self) -> None:
        records = self.synthetic_records()
        duplicate = next(
            record for record in records
            if record["case_id"] == "case-1"
            and record["replicate"] == 1
            and record["condition"] == "abrl"
        )
        duplicate["case_id"] = "case-0"
        duplicate["replicate"] = 0
        with self.assertRaisesRegex(SystemExit, "duplicate abrl member"):
            analysis.analyze(
                {"records": records}, 1, 1, 32768
            )

    def test_variant_misalignment_within_pair_fails_closed(self) -> None:
        records = self.synthetic_records()
        record = next(
            record for record in records
            if record["case_id"] == "case-0"
            and record["replicate"] == 0
            and record["condition"] == "abrl"
        )
        record["requirement_variant"] = "source_faithful"
        with self.assertRaisesRegex(SystemExit, "disagrees on requirement variant"):
            analysis.analyze(
                {"records": records}, 1, 1, 32768
            )

    def test_variant_quota_is_preserved_per_target(self) -> None:
        paired = self.paired(self.synthetic_records())
        for case_index in range(30):
            expected_injected = 3 if case_index % 2 == 0 else 2
            self.assertEqual(
                len(paired[f"case-{case_index}"]["injected_drift"]),
                expected_injected,
            )
            self.assertEqual(
                len(paired[f"case-{case_index}"]["source_faithful"]),
                5 - expected_injected,
            )

    def test_fixed_seed_is_reproducible_for_heterogeneous_pairs(self) -> None:
        def outcome(condition, case_index, replicate_index, _variant):
            if condition == "abrl":
                return (case_index + 2 * replicate_index) % 4 != 0
            if condition == "source_aware_blueprint":
                return (2 * case_index + replicate_index) % 5 == 0
            return False

        records = self.synthetic_records(outcome)
        paired = self.paired(records)
        first = analysis.fixed_target_variant_preserving_paired_bootstrap(
            paired, seed=1907, replicates=64
        )
        repeated = analysis.fixed_target_variant_preserving_paired_bootstrap(
            paired, seed=1907, replicates=64
        )
        different_seed = analysis.fixed_target_variant_preserving_paired_bootstrap(
            paired, seed=1908, replicates=64
        )
        random.Random(44).shuffle(records)
        reordered = analysis.fixed_target_variant_preserving_paired_bootstrap(
            self.paired(records), seed=1907, replicates=64
        )
        self.assertEqual(first, repeated)
        self.assertEqual(first, reordered)
        self.assertNotEqual(first, different_seed)

    def test_point_estimate_matches_paired_invocation_arithmetic(self) -> None:
        def outcome(condition, case_index, replicate_index, _variant):
            if condition == "abrl":
                return (case_index + replicate_index) % 3 != 0
            if condition == "source_aware_blueprint":
                return (case_index * 2 + replicate_index) % 4 == 0
            return False

        records = self.synthetic_records(outcome)
        paired = self.paired(records)
        point = sum(
            float(outcome("abrl", case_index, replicate_index,
                          prepare.requirement_variant(case_index, replicate_index)))
            - float(outcome("source_aware_blueprint", case_index, replicate_index,
                            prepare.requirement_variant(case_index, replicate_index)))
            for case_index in range(30)
            for replicate_index in range(5)
        ) / 150
        self.assertAlmostEqual(
            sum(analysis.target_paired_differences(paired).values()) / 30,
            point,
        )

    def test_null_sample_has_zero_point_and_interval(self) -> None:
        def outcome(condition, case_index, replicate_index, _variant):
            if condition in analysis.PRIMARY_CONDITIONS:
                return (case_index + replicate_index) % 2 == 0
            return False

        paired = self.paired(self.synthetic_records(outcome))
        self.assertEqual(set(analysis.target_paired_differences(paired).values()), {0.0})
        self.assertEqual(
            set(analysis.fixed_target_variant_preserving_paired_bootstrap(
                paired, seed=17, replicates=64
            )),
            {0.0},
        )

    def test_variant_effect_keeps_frozen_three_two_allocations(self) -> None:
        def outcome(condition, _case_index, _replicate_index, variant):
            return condition == "abrl" and variant == "injected_drift"

        paired = self.paired(self.synthetic_records(outcome))
        point = sum(analysis.target_paired_differences(paired).values()) / 30
        draws = analysis.fixed_target_variant_preserving_paired_bootstrap(
            paired, seed=23, replicates=64
        )
        self.assertEqual(point, 0.5)
        self.assertEqual(set(draws), {0.5})


if __name__ == "__main__":
    unittest.main()
