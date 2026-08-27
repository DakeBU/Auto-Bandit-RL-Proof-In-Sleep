#!/usr/bin/env python3
"""Focused tests for the target-drift primary-grading blindness boundary."""

from __future__ import annotations

import copy
import contextlib
import hashlib
import io
import json
import os
import sys
import tempfile
import unittest
from pathlib import Path
from unittest import mock


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

    def test_workspace_relative_paths_reject_windows_alias_semantics(self) -> None:
        self.assertEqual(
            grading.safe_workspace_relative(
                "BanditRLProof/Valid.lean", "portable test"
            ).as_posix(),
            "BanditRLProof/Valid.lean",
        )
        for value in (
            "C:/escape.lean",
            "C:escape.lean",
            "foo:bar.lean",
            "NUL.lean",
            "dir/COM1.txt",
            "trail. /x.lean",
            "bad*/x.lean",
            "double//slash.lean",
            "dot/./segment.lean",
            "control\x00.lean",
        ):
            with self.subTest(value=value), self.assertRaises(SystemExit):
                grading.safe_workspace_relative(value, "portable test")

    def test_workspace_file_bytes_are_bound_to_completed_agent_manifest(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            workspace = Path(temporary) / "workspace"
            workspace.mkdir()
            source = workspace / "Valid.lean"
            original = b"theorem valid : True := by trivial\n"
            source.write_bytes(original)
            manifest = {
                "workspace/Valid.lean": {
                    "path": "workspace/Valid.lean",
                    "bytes": len(original),
                    "sha256": hashlib.sha256(original).hexdigest(),
                }
            }
            relative = grading.safe_workspace_relative("Valid.lean", "manifest test")
            self.assertEqual(
                grading.read_manifest_bound_file(
                    workspace,
                    relative,
                    "workspace/Valid.lean",
                    manifest,
                    "manifest-bound test file",
                ),
                original,
            )
            source.write_bytes(b"x" * len(original))
            with self.assertRaises(SystemExit):
                grading.read_manifest_bound_file(
                    workspace,
                    relative,
                    "workspace/Valid.lean",
                    manifest,
                    "manifest-bound test file",
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

    @staticmethod
    def grade(grade_id: str) -> dict:
        return {
            "grade_id": grade_id,
            **{label: False for label in assemble.BINARY_LABELS},
            "rationale": "The supplied evidence does not establish completion.",
            "source_critical_fields": [],
            "condition_guess": "compile_only",
            "condition_guess_confidence": 0.5,
        }

    def test_grader_response_is_bound_to_internal_and_export_digests(self) -> None:
        grade_id = "GRADE-0123456789abcdef0123"
        response = {
            "schema_version": grading.GRADER_RESPONSE_SCHEMA_VERSION,
            "grader_id": "grader-a",
            "grading_pack_sha256": "1" * 64,
            "grader_export_sha256": "2" * 64,
            "grader_prompt_sha256": "3" * 64,
            "grades": [self.grade(grade_id)],
        }
        indexed = assemble.by_grade_id(
            response,
            {grade_id},
            grading_pack_sha256="1" * 64,
            grader_export_sha256="2" * 64,
            grader_prompt_sha256="3" * 64,
        )
        self.assertEqual(set(indexed), {grade_id})

        for field in (
            "grading_pack_sha256",
            "grader_export_sha256",
            "grader_prompt_sha256",
        ):
            changed = copy.deepcopy(response)
            changed[field] = "f" * 64
            with self.subTest(field=field), self.assertRaises(SystemExit):
                assemble.by_grade_id(
                    changed,
                    {grade_id},
                    grading_pack_sha256="1" * 64,
                    grader_export_sha256="2" * 64,
                    grader_prompt_sha256="3" * 64,
                )

    def test_adjudication_rejects_a_different_grader_export_digest(self) -> None:
        packet_ids = {f"GRADE-{index:020x}" for index in range(450)}
        grading_pack_sha256 = "1" * 64
        grader_export_sha256 = "2" * 64
        prompt_sha256 = "3" * 64
        sealed_pack_sha256 = "4" * 64
        graders = ["grader-a", "grader-b"]

        with tempfile.TemporaryDirectory() as raw_root:
            root = Path(raw_root)
            pack = root / "pack"
            execution_code = pack / "execution_code"
            execution_code.mkdir(parents=True)
            runs_root = root / "runs"
            internal_root = root / "internal-grading-pack"
            export_root = root / "grader-export"
            runs_root.mkdir()
            internal_root.mkdir()
            export_root.mkdir()
            output = root / "analysis-records.json"
            response_paths = [root / f"response-{index}.json" for index in range(2)]
            adjudication_path = root / "adjudication.json"

            assembler_path = Path(assemble.__file__).resolve()
            prepare_path = Path(assemble.prepare.__file__).resolve()
            grading_path = Path(grading.__file__).resolve()
            script_hashes = {
                assembler_path.name: hashlib.sha256(assembler_path.read_bytes()).hexdigest(),
                prepare_path.name: hashlib.sha256(prepare_path.read_bytes()).hexdigest(),
                grading_path.name: hashlib.sha256(grading_path.read_bytes()).hexdigest(),
            }
            for source in (assembler_path, prepare_path, grading_path):
                (execution_code / source.name).write_bytes(source.read_bytes())

            config = {
                "suite_id": "ABRL-TARGET-DRIFT-V2",
                "analysis": {
                    "grade_assembler_sha256": script_hashes[assembler_path.name],
                },
                "sealed_agent_view": {
                    "materializer_sha256": script_hashes[prepare_path.name],
                },
                "grading": {
                    "packet_materializer_sha256": script_hashes[grading_path.name],
                    "grader_conflict_policy": (
                        "adjudicate every disagreement on a primary or secondary "
                        "binary label or the structured source-critical field list"
                    ),
                    "primary_grader_ids": graders,
                    "grader_prompt_sha256": prompt_sha256,
                    "adjudicator_id": "adjudicator-a",
                },
            }
            (pack / "execution_config.json").write_text(
                json.dumps(config), encoding="utf-8"
            )
            (pack / "aggregate.sha256").write_text(
                sealed_pack_sha256 + "\n", encoding="ascii"
            )

            grades = [self.grade(grade_id) for grade_id in sorted(packet_ids)]
            for grader_id, path in zip(graders, response_paths):
                path.write_text(json.dumps({
                    "schema_version": grading.GRADER_RESPONSE_SCHEMA_VERSION,
                    "grader_id": grader_id,
                    "grading_pack_sha256": grading_pack_sha256,
                    "grader_export_sha256": grader_export_sha256,
                    "grader_prompt_sha256": prompt_sha256,
                    "grades": grades,
                }), encoding="utf-8")
            adjudication_path.write_text(json.dumps({
                "schema_version": grading.GRADER_RESPONSE_SCHEMA_VERSION,
                "grading_pack_sha256": grading_pack_sha256,
                "grader_export_sha256": "f" * 64,
                "grader_prompt_sha256": prompt_sha256,
                "adjudicator_id": "adjudicator-a",
                "grades": [],
            }), encoding="utf-8")

            internal = {
                "manifest": {
                    "aggregate_sha256": grading_pack_sha256,
                    "packet_count": 450,
                },
                "mapping": [],
                "packets": {},
                "packet_ids": packet_ids,
            }
            argv = [
                str(assembler_path),
                "--pack", str(pack),
                "--runs-root", str(runs_root),
                "--grading-pack", str(internal_root),
                "--grader-export", str(export_root),
                "--grader-response", str(response_paths[0]),
                "--grader-response", str(response_paths[1]),
                "--adjudication", str(adjudication_path),
                "--output", str(output),
            ]
            with contextlib.ExitStack() as stack:
                stack.enter_context(mock.patch.object(sys, "argv", argv))
                stack.enter_context(mock.patch.object(assemble.prepare, "verify_pack"))
                stack.enter_context(mock.patch.object(
                    assemble.prepare,
                    "checker_runtime_config_sha256",
                    return_value="5" * 64,
                ))
                stack.enter_context(mock.patch.object(
                    grading, "validate_internal_grading_pack_against_runs",
                    return_value=internal,
                ))
                stack.enter_context(mock.patch.object(
                    grading,
                    "validate_grader_export",
                    return_value={"grader_export_sha256": grader_export_sha256},
                ))
                with self.assertRaisesRegex(
                    SystemExit, "adjudication names a different grader-only export digest"
                ):
                    assemble.main()

            self.assertFalse(os.path.lexists(output))

    def test_internal_pack_bytes_must_reconstruct_from_checked_runs(self) -> None:
        """A self-consistent pack cannot substitute for the checked-run truth."""
        config = {
            "suite_id": "ABRL-TARGET-DRIFT-V2",
            "grading": {
                "packet_order_seed": 1907,
                "grader_prompt_sha256": "1" * 64,
            },
            "posthoc_checker": {
                "isolation_probe_report_sha256": "2" * 64,
            },
        }
        completion_ledger = {
            "missing_run_policy_id": "complete-only-v1",
            "missing_run_policy_sha256": "3" * 64,
        }
        completion_payload = grading.canonical_json_bytes(completion_ledger)
        packet = {
            "schema_version": 1,
            "source_locator": {"kind": "public-source"},
            "frozen_contract": {"statement": "frozen theorem contract"},
            "proposed_requirement": "prove the stated theorem",
            "expected_affected_fields": [],
            "agent_final_status": "completed",
            "public_declarations": [],
            "primary_grader_rationale": "The public evidence is sufficient.",
            "source_amendment": None,
            "lean_artifacts": [],
            "neutral_checker": {"checker_pass": True},
            "grader_response_schema": {"condition_guess": ["compile_only"]},
        }
        collected = [{
            "semantic_run_id": "RUN-0001",
            "condition": "abrl",
            "requirement_variant": "source_faithful",
            "execution_metrics": copy.deepcopy(self.usage),
            "workflow_compliance_pass": True,
            "packet": packet,
        }]
        sealed_pack_sha256 = "4" * 64
        runtime_sha256 = "5" * 64
        payloads, manifest = grading.build_internal_grading_payloads(
            collected,
            config,
            sealed_pack_sha256,
            completion_payload,
            completion_ledger,
            runtime_sha256,
        )
        packet_payloads = {
            name: payload
            for name, payload in payloads.items()
            if name.startswith("packets/")
        }
        packet_id = Path(next(iter(packet_payloads))).stem
        internal = {
            "manifest": manifest,
            "manifest_payload": payloads["packet-manifest.json"],
            "packet_payloads": packet_payloads,
            "packet_ids": {packet_id},
            "packets": {
                packet_id: grading.json_from_bytes(
                    next(iter(packet_payloads.values())), "test grading packet"
                )
            },
            "mapping_payload": payloads["operator-mapping.json"],
            "mapping": grading.json_from_bytes(
                payloads["operator-mapping.json"], "test operator mapping"
            )["mapping"],
            "completion_payload": completion_payload,
            "completion_ledger": completion_ledger,
        }

        mutations = {
            "packet": lambda record: record["packet"].__setitem__(
                "proposed_requirement", "a forged requirement"
            ),
            "mapping": lambda record: record.__setitem__("condition", "compile_only"),
        }
        with tempfile.TemporaryDirectory() as raw_root:
            root = Path(raw_root)
            pack = root / "pack"
            runs_root = root / "runs"
            grading_pack = root / "internal-grading-pack"
            for path in (pack, runs_root, grading_pack):
                path.mkdir()
            for label, mutate in mutations.items():
                with self.subTest(mismatch=label):
                    reconstructed = copy.deepcopy(collected)
                    mutate(reconstructed[0])
                    call_order: list[str] = []

                    def validate_ledger(*_args, **_kwargs) -> None:
                        call_order.append("ledger")

                    def collect(*_args, **_kwargs):
                        call_order.append("collect")
                        return reconstructed

                    with contextlib.ExitStack() as stack:
                        stack.enter_context(mock.patch.object(
                            grading,
                            "validate_internal_grading_pack",
                            return_value=internal,
                        ))
                        stack.enter_context(mock.patch.object(
                            grading.completion,
                            "validate_ledger_against_runs",
                            side_effect=validate_ledger,
                        ))
                        stack.enter_context(mock.patch.object(
                            grading,
                            "collect_grading_records_from_runs",
                            side_effect=collect,
                        ))
                        stack.enter_context(mock.patch.object(
                            grading.prepare,
                            "checker_runtime_config_sha256",
                            return_value=runtime_sha256,
                        ))
                        with self.assertRaisesRegex(
                            SystemExit,
                            "internal grading-pack bytes do not reconstruct from checked runs",
                        ):
                            grading.validate_internal_grading_pack_against_runs(
                                pack,
                                runs_root,
                                grading_pack,
                                config,
                                expected_count=1,
                            )
                    self.assertEqual(call_order, ["ledger", "collect"])

    def test_grade_assembler_output_must_be_separate_from_every_input_tree(self) -> None:
        with tempfile.TemporaryDirectory() as raw_root:
            root = Path(raw_root)
            sources = {
                "sealed pack": root / "pack",
                "runs root": root / "runs",
                "internal grading-pack": root / "internal",
                "grader-only export": root / "export",
            }
            for path in sources.values():
                path.mkdir()
            responses = [root / "response-a.json", root / "response-b.json"]
            adjudication = root / "adjudication.json"
            for path in (*responses, adjudication):
                path.write_text("{}\n", encoding="utf-8")

            for label, source in sources.items():
                output = source / "grades.json"
                argv = [
                    str(Path(assemble.__file__).resolve()),
                    "--pack", str(sources["sealed pack"]),
                    "--runs-root", str(sources["runs root"]),
                    "--grading-pack", str(sources["internal grading-pack"]),
                    "--grader-export", str(sources["grader-only export"]),
                    "--grader-response", str(responses[0]),
                    "--grader-response", str(responses[1]),
                    "--adjudication", str(adjudication),
                    "--output", str(output),
                ]
                with self.subTest(input_tree=label), mock.patch.object(
                    sys, "argv", argv
                ), self.assertRaisesRegex(SystemExit, "must be separate trees"):
                    assemble.main()
                self.assertFalse(os.path.lexists(output))

    def test_grading_and_assembler_clis_reject_expected_count_override(self) -> None:
        cases = (
            (
                grading.main,
                [
                    "prepare_target_drift_grading.py",
                    "--pack", "pack",
                    "--runs-root", "runs",
                    "--completion-ledger", "completion.json",
                    "--output", "grading-pack",
                    "--expected-count", "1",
                ],
            ),
            (
                assemble.main,
                [
                    "assemble_target_drift_grades.py",
                    "--pack", "pack",
                    "--runs-root", "runs",
                    "--grading-pack", "grading-pack",
                    "--grader-export", "grader-export",
                    "--grader-response", "response-a.json",
                    "--grader-response", "response-b.json",
                    "--adjudication", "adjudication.json",
                    "--output", "grades.json",
                    "--expected-count", "1",
                ],
            ),
        )
        for entrypoint, argv in cases:
            with self.subTest(entrypoint=entrypoint.__module__):
                stderr = io.StringIO()
                with mock.patch.object(sys, "argv", argv), contextlib.redirect_stderr(
                    stderr
                ), self.assertRaises(SystemExit) as raised:
                    entrypoint()
                self.assertEqual(raised.exception.code, 2)
                self.assertIn("unrecognized arguments: --expected-count 1", stderr.getvalue())


if __name__ == "__main__":
    unittest.main()
