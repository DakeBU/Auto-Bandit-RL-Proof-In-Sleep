#!/usr/bin/env python3
"""Focused tests for the physically isolated target-drift grader export."""

from __future__ import annotations

import contextlib
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

import prepare_target_drift_grading as grading  # noqa: E402
import prepare_target_drift_execution as prepare  # noqa: E402
import export_target_drift_grader_pack as exporter  # noqa: E402


class TargetDriftGraderExportTest(unittest.TestCase):
    GRADE_ID = "GRADE-0123456789abcdef0123"
    PACKET_NAME = f"packets/{GRADE_ID}.json"

    def packet(self, grade_id: str | None = None) -> dict:
        return {
            "grade_id": grade_id or self.GRADE_ID,
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

    @staticmethod
    def encode(value: object) -> bytes:
        return (json.dumps(value, sort_keys=True) + "\n").encode("utf-8")

    def internal(self) -> dict:
        packet_payload = self.encode(self.packet())
        packet_payloads = {self.PACKET_NAME: packet_payload}
        return {
            "manifest": {
                "suite_id": "ABRL-TARGET-DRIFT-V2",
                "packet_count": 1,
                "sealed_pack_sha256": "1" * 64,
                "aggregate_sha256": "2" * 64,
                "packet_aggregate_sha256": grading.digest_payloads(packet_payloads),
                "packet_sha256": {
                    self.PACKET_NAME: grading.sha256_bytes(packet_payload),
                },
            },
            "packet_payloads": packet_payloads,
        }

    def test_strict_json_accepts_only_a_finite_object_with_unique_keys(self) -> None:
        self.assertEqual(
            grading.json_from_bytes(b'{"ok": true}', "test JSON"),
            {"ok": True},
        )
        invalid_payloads = (
            b'{"same": 1, "same": 2}',
            b'{"value": NaN}',
            b'{"value": Infinity}',
            b'[1, 2, 3]',
            b'\xff',
        )
        for payload in invalid_payloads:
            with self.subTest(payload=payload), self.assertRaises(SystemExit):
                grading.json_from_bytes(payload, "test JSON")

    def test_packet_path_and_embedded_grade_id_are_bound(self) -> None:
        payload = self.encode(self.packet())
        packet_ids, packets = grading.validate_packet_payloads(
            {self.PACKET_NAME: payload}, expected_count=1,
        )
        self.assertEqual(packet_ids, {self.GRADE_ID})
        self.assertEqual(packets[self.GRADE_ID]["grade_id"], self.GRADE_ID)

        invalid_names = (
            f"../{self.GRADE_ID}.json",
            f"packets/../{self.GRADE_ID}.json",
            f"/packets/{self.GRADE_ID}.json",
            f"C:/packets/{self.GRADE_ID}.json",
            f"packets\\{self.GRADE_ID}.json",
            f"packets/{self.GRADE_ID}.json/extra",
            "packets/GRADE-0123456789ABCDEF0123.json",
        )
        for name in invalid_names:
            with self.subTest(name=name), self.assertRaisesRegex(
                SystemExit, "invalid grading packet path"
            ):
                grading.validate_packet_payloads({name: payload}, expected_count=1)

        different_id = "GRADE-fedcba9876543210fedc"
        with self.assertRaisesRegex(SystemExit, "embedded grade ID differ"):
            grading.validate_packet_payloads(
                {self.PACKET_NAME: self.encode(self.packet(different_id))},
                expected_count=1,
            )

    def test_export_is_an_exact_positive_allowlist_with_bound_digests(self) -> None:
        internal = self.internal()
        prompt = b"Grade only the supplied public evidence.\n"
        rubric = b'{"no_results": true}\n'
        payloads, manifest = grading.build_grader_export_payloads(
            internal, prompt, rubric,
        )

        expected_files = {
            self.PACKET_NAME,
            "grader-prompt.md",
            "grading-rubric.json",
            grading.GRADER_EXPORT_RESPONSE_TEMPLATE,
            grading.GRADER_EXPORT_MANIFEST,
        }
        self.assertEqual(set(payloads), expected_files)
        self.assertNotIn("operator-mapping.json", payloads)
        self.assertNotIn("completion-ledger.json", payloads)

        core = {
            self.PACKET_NAME: payloads[self.PACKET_NAME],
            "grader-prompt.md": prompt,
            "grading-rubric.json": rubric,
        }
        response = grading.json_from_bytes(
            payloads[grading.GRADER_EXPORT_RESPONSE_TEMPLATE],
            "response template",
        )
        self.assertEqual(
            manifest["grader_export_sha256"], grading.digest_payloads(core)
        )
        self.assertEqual(
            response["grader_export_sha256"], manifest["grader_export_sha256"]
        )
        self.assertEqual(
            response["grading_pack_sha256"],
            internal["manifest"]["aggregate_sha256"],
        )
        self.assertEqual(response["schema_version"], grading.GRADER_RESPONSE_SCHEMA_VERSION)
        self.assertEqual(
            manifest["response_template_sha256"],
            grading.sha256_bytes(payloads[grading.GRADER_EXPORT_RESPONSE_TEMPLATE]),
        )
        distributable = {
            name: payload
            for name, payload in payloads.items()
            if name != grading.GRADER_EXPORT_MANIFEST
        }
        self.assertEqual(
            manifest["export_aggregate_sha256"],
            grading.digest_payloads(distributable),
        )
        for attestation in (
            "recursive_blindness_scan_passed",
            "operator_only_files_absent",
        ):
            self.assertIs(manifest[attestation], True)
        for included in (
            "operator_mapping_included",
            "completion_ledger_included",
            "execution_metrics_included",
            "workflow_compliance_included",
            "condition_or_variant_labels_included",
        ):
            self.assertIs(manifest[included], False)

    def test_exact_tree_rejects_an_extra_file(self) -> None:
        with tempfile.TemporaryDirectory() as raw_root:
            root = Path(raw_root)
            grading.write_payload_tree(root, {
                "allowed.json": b"{}\n",
                "operator-mapping.json": b"{}\n",
            })
            with self.assertRaisesRegex(SystemExit, "positive allowlist"):
                grading.read_plain_tree(root, {"allowed.json"}, "test export")

    def test_exact_tree_rejects_hardlinks(self) -> None:
        with tempfile.TemporaryDirectory() as raw_root:
            root = Path(raw_root)
            original = root / "original.json"
            alias = root / "alias.json"
            original.write_bytes(b"{}\n")
            try:
                os.link(original, alias)
            except (NotImplementedError, OSError) as error:
                self.skipTest(f"hardlinks unavailable on this filesystem: {error}")
            with self.assertRaisesRegex(SystemExit, "multiply linked"):
                grading.read_plain_tree(
                    root, {"original.json", "alias.json"}, "test export"
                )

    def test_exact_tree_rejects_symlinks_when_supported(self) -> None:
        with tempfile.TemporaryDirectory() as raw_root:
            root = Path(raw_root)
            original = root / "original.json"
            alias = root / "alias.json"
            original.write_bytes(b"{}\n")
            try:
                alias.symlink_to(original)
            except (NotImplementedError, OSError) as error:
                self.skipTest(f"symlinks unavailable on this platform: {error}")
            with self.assertRaisesRegex(SystemExit, "link or reparse point"):
                grading.read_plain_tree(
                    root, {"original.json", "alias.json"}, "test export"
                )

    def test_payload_writer_is_exclusive_on_repeated_materialization(self) -> None:
        with tempfile.TemporaryDirectory() as raw_root:
            root = Path(raw_root)
            grading.write_payload_tree(root, {"response-template.json": b"{}\n"})
            with self.assertRaisesRegex(SystemExit, "cannot write grading artifact"):
                grading.write_payload_tree(root, {"response-template.json": b"{}\n"})

    def test_v2_sealed_execution_code_inventory_contains_exporter(self) -> None:
        config = json.loads(
            (prepare.SUITE.parent / "target-drift-v2" / "execution-template.json")
            .read_text(encoding="utf-8")
        )
        paths = prepare.execution_code_paths(config)
        self.assertEqual(
            paths["export_target_drift_grader_pack.py"],
            Path(exporter.__file__).resolve(),
        )

    def test_exporter_runtime_rejects_sealed_code_drift(self) -> None:
        current_exporter = Path(exporter.__file__).resolve()
        current_grading = Path(grading.__file__).resolve()
        current_prepare = Path(prepare.__file__).resolve()
        with tempfile.TemporaryDirectory() as raw_root:
            pack = Path(raw_root) / "FROZEN-PACK"
            sealed_code = pack / "execution_code"
            sealed_code.mkdir(parents=True)
            for source in (current_exporter, current_grading, current_prepare):
                (sealed_code / source.name).write_bytes(source.read_bytes())
            config = {
                "suite_id": "ABRL-TARGET-DRIFT-V2",
                "execution_status": "frozen_ready",
                "grading": {
                    "grader_exporter": "tools/export_target_drift_grader_pack.py",
                    "packet_materializer_sha256": exporter.sha256_file(current_grading),
                },
                "sealed_agent_view": {
                    "materializer_sha256": exporter.sha256_file(current_prepare),
                },
            }
            with mock.patch.object(exporter.prepare, "verify_pack"), mock.patch.object(
                exporter, "load", return_value=config
            ):
                self.assertIs(exporter.verify_runtime(pack), config)

                sealed_exporter = sealed_code / current_exporter.name
                sealed_exporter.write_bytes(current_exporter.read_bytes() + b"# drift\n")
                with self.assertRaisesRegex(SystemExit, "differs from the sealed exporter"):
                    exporter.verify_runtime(pack)

                sealed_exporter.write_bytes(current_exporter.read_bytes())
                sealed_grading = sealed_code / current_grading.name
                sealed_grading.write_bytes(current_grading.read_bytes() + b"# drift\n")
                with self.assertRaisesRegex(
                    SystemExit, "sealed grading materializer differs"
                ):
                    exporter.verify_runtime(pack)

    def test_grader_export_output_must_be_separate_from_every_input_tree(self) -> None:
        with tempfile.TemporaryDirectory() as raw_root:
            root = Path(raw_root)
            sources = {
                "sealed pack": root / "pack",
                "runs root": root / "runs",
                "internal grading-pack": root / "internal",
            }
            for path in sources.values():
                path.mkdir()

            for label, source in sources.items():
                output = source / "grader-export"
                with self.subTest(input_tree=label), self.assertRaisesRegex(
                    SystemExit, "must be separate trees"
                ):
                    grading.materialize_grader_export(
                        sources["sealed pack"],
                        sources["runs root"],
                        sources["internal grading-pack"],
                        output,
                        {},
                        expected_count=1,
                    )
                self.assertFalse(os.path.lexists(output))

    def test_exporter_cli_rejects_expected_count_override(self) -> None:
        argv = [
            "export_target_drift_grader_pack.py",
            "create",
            "--pack", "pack",
            "--runs-root", "runs",
            "--grading-pack", "grading-pack",
            "--output", "grader-export",
            "--expected-count", "1",
        ]
        stderr = io.StringIO()
        with mock.patch.object(sys, "argv", argv), contextlib.redirect_stderr(
            stderr
        ), self.assertRaises(SystemExit) as raised:
            exporter.main()
        self.assertEqual(raised.exception.code, 2)
        self.assertIn("unrecognized arguments: --expected-count 1", stderr.getvalue())


if __name__ == "__main__":
    unittest.main()
