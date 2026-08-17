#!/usr/bin/env python3
"""Unit tests for opaque preparation, neutral checking, and blind packaging."""

from __future__ import annotations

import sys
import tempfile
import unittest
from pathlib import Path
from unittest import mock


TOOLS = Path(__file__).resolve().parent
sys.path.insert(0, str(TOOLS))

import check_target_drift_run as checker  # noqa: E402
import assemble_target_drift_grades as assembler  # noqa: E402
import prepare_target_drift_grading as grading  # noqa: E402
import run_target_drift_execution as runner  # noqa: E402


class TargetDriftRuntimeTest(unittest.TestCase):
    def test_opaque_ids_are_deterministic_and_do_not_echo_semantics(self) -> None:
        semantic = "DBOBW-01-ALGORITHM-IDENTITY--abrl--replicate-7"
        first = runner.opaque_id("run", "a" * 64, semantic)
        second = runner.opaque_id("run", "a" * 64, semantic)
        self.assertEqual(first, second)
        self.assertNotIn("DBOBW", first)
        self.assertRegex(first, r"^RUN-[0-9a-f]{20}$")

    def test_prompt_rendering_removes_every_placeholder(self) -> None:
        template = " ".join(
            (
                "{{CASE_ID}}",
                "{{SOURCE_ID}}",
                "{{SOURCE_LOCATOR}}",
                "{{SOURCE_PACKET_PATH}}",
                "{{PROPOSED_REQUIREMENT}}",
                "{{WORKSPACE_PATH}}",
            )
        )
        rendered = runner.render_prompt(
            template,
            "CASE-opaque",
            "SOURCE-opaque",
            "Lemma 4.2",
            Path("source.pdf"),
            "preserve the exact target",
            Path("workspace"),
        )
        self.assertNotIn("{{", rendered)
        self.assertIn("CASE-opaque", rendered)
        self.assertIn("preserve the exact target", rendered)

    def test_forbidden_scan_finds_semantic_identifier(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            (root / "prompt.md").write_text("DBOBW-01-ALGORITHM-IDENTITY", encoding="utf-8")
            hits = runner.scan_forbidden(root, ["DBOBW-01-ALGORITHM-IDENTITY"])
            self.assertEqual(hits[0]["path"], "prompt.md")

    def test_agent_manifest_excludes_infrastructure_lake_cache(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            (root / "workspace" / ".lake").mkdir(parents=True)
            (root / "workspace" / ".lake" / "cache.olean").write_bytes(b"cache")
            (root / "prompt.md").write_text("prompt", encoding="utf-8")
            self.assertEqual(
                [entry["path"] for entry in runner.file_manifest(root)],
                ["prompt.md"],
            )
            self.assertEqual(
                runner.manifest_sha256(runner.file_manifest(root)),
                grading.manifest_sha256(grading.agent_manifest(root)),
            )

    def test_neutral_checker_flags_proof_escape_hatches(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            path = root / "Unsafe.lean"
            path.write_text(
                "axiom bad : False\nconstant hidden : False\ntheorem t : True := by sorry\n",
                encoding="utf-8",
            )
            hits = checker.scan_lean(root, ["Unsafe.lean"])
            self.assertEqual({hit["kind"] for hit in hits}, {"axiom", "constant", "sorry"})

    def test_public_abrl_locator_is_not_scanned_but_agent_provenance_is(self) -> None:
        packet = {
            "source_locator": "ABRL textbook-card chapter 7",
            "agent_final_status": "partial",
            "public_declarations": [],
            "primary_grader_rationale": "The requested inequality remains unproved.",
            "source_amendment": None,
            "lean_artifacts": [],
        }
        grading.require_blind_text(grading.agent_generated_blind_fields(packet), "packet")
        packet["primary_grader_rationale"] = "The ABRL promotion gate passed."
        with self.assertRaises(SystemExit):
            grading.require_blind_text(grading.agent_generated_blind_fields(packet), "packet")

    def test_axiom_parser_distinguishes_kernel_axioms_from_new_constants(self) -> None:
        output = "t depends on axioms: [propext, Classical.choice, hiddenProof]"
        self.assertEqual(
            checker.parsed_axioms(output),
            {"propext", "Classical.choice", "hiddenProof"},
        )

    def test_adapter_usage_must_match_trace_counts_and_budgets(self) -> None:
        response = {
            "provider_request_ids": ["request-1"],
            "usage": {
                "input_tokens": 10,
                "output_tokens": 5,
                "tool_calls": 1,
                "build_attempts": 1,
                "recovery_tool_calls": 1,
                "infrastructure_retries": 0,
                "wall_seconds": 2.0,
                "cost_usd": 0.01,
            }
        }
        events = [
            {"sequence": 0, "kind": "build_attempt", "success": False},
            {"sequence": 1, "kind": "tool_call", "recovery_phase": True},
            {"sequence": 2, "kind": "usage_summary", "usage": response["usage"]},
        ]
        job = {
            "budgets": {
                "maximum_input_tokens": 20,
                "maximum_output_tokens": 20,
                "maximum_tool_calls": 2,
                "maximum_build_attempts": 2,
                "wall_clock_seconds": 5,
                "maximum_model_retries": 0,
                "maximum_cost_usd": 1.0,
            },
            "retry_policy": {
                "infrastructure_retry_limit": 0,
                "semantic_failure_retries": 0,
            },
        }
        self.assertEqual(runner.validate_usage(response, events, job)["tool_calls"], 1)
        events[0] = {"sequence": 0, "kind": "build_attempt", "success": True}
        with self.assertRaises(SystemExit):
            runner.validate_usage(response, events, job)

    def test_provider_retry_trace_binds_request_ids_and_reason_budget(self) -> None:
        usage = {
            "input_tokens": 10,
            "output_tokens": 5,
            "tool_calls": 0,
            "build_attempts": 0,
            "recovery_tool_calls": 0,
            "infrastructure_retries": 1,
            "wall_seconds": 2.0,
            "cost_usd": 0.01,
        }
        response = {"provider_request_ids": ["request-1", "request-2"], "usage": usage}
        events = [
            {"sequence": 0, "kind": "provider_retry", "reason": "infrastructure"},
            {"sequence": 1, "kind": "usage_summary", "usage": usage},
        ]
        job = {
            "budgets": {
                "maximum_input_tokens": 20,
                "maximum_output_tokens": 20,
                "maximum_tool_calls": 2,
                "maximum_build_attempts": 2,
                "wall_clock_seconds": 5,
                "maximum_model_retries": 1,
                "maximum_cost_usd": 1.0,
            },
            "retry_policy": {
                "infrastructure_retry_limit": 1,
                "semantic_failure_retries": 0,
            },
        }
        self.assertEqual(runner.validate_usage(response, events, job)[
            "infrastructure_retries"
        ], 1)
        response["provider_request_ids"].append("untraced-request")
        with self.assertRaises(SystemExit):
            runner.validate_usage(response, events, job)

    def test_unexpected_executor_exception_records_terminal_failure(self) -> None:
        pack = Path("pack")
        run = Path("run")
        with mock.patch.object(runner, "execute_run", side_effect=FileNotFoundError("missing")):
            with mock.patch.object(runner, "record_operator_failure") as record:
                with self.assertRaises(FileNotFoundError):
                    runner.execute_or_record_failure(pack, run)
                record.assert_called_once_with(run, "FileNotFoundError: missing")

    def test_invented_source_critical_field_is_rejected(self) -> None:
        grade = {
            "drift_detected": True,
            "false_rejection": False,
            "source_critical_fields": ["invented-field"],
        }
        with self.assertRaises(SystemExit):
            assembler.validate_variant_fields(grade, "injected_drift", {"algorithm identity"})

    def test_grading_digest_is_name_and_payload_sensitive(self) -> None:
        baseline = grading.digest_payloads({"a": b"one", "b": b"two"})
        self.assertNotEqual(baseline, grading.digest_payloads({"a": b"ONE", "b": b"two"}))
        self.assertNotEqual(baseline, grading.digest_payloads({"x": b"one", "b": b"two"}))

    def test_cohen_kappa_handles_agreement_and_degenerate_labels(self) -> None:
        self.assertEqual(assembler.cohen_kappa([True, False], [True, False]), 1.0)
        self.assertIsNone(assembler.cohen_kappa([True, True], [True, True]))


if __name__ == "__main__":
    unittest.main()
