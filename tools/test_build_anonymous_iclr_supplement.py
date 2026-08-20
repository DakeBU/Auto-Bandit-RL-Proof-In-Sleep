import importlib.util
import hashlib
import json
import subprocess
import sys
import tempfile
import unittest
import zipfile
from pathlib import Path
from unittest import mock


SCRIPT = Path(__file__).resolve().with_name("build_anonymous_iclr_supplement.py")
SPEC = importlib.util.spec_from_file_location("anonymous_supplement_builder", str(SCRIPT))
BUILDER = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(BUILDER)


class AnonymousSupplementTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.temp = tempfile.TemporaryDirectory()
        cls.root = Path(cls.temp.name)
        cls.first = cls.root / "first.zip"
        cls.second = cls.root / "second.zip"
        cls.first_result = BUILDER.build_archive(
            cls.first, allow_missing_graph=True
        )
        cls.second_result = BUILDER.build_archive(
            cls.second, allow_missing_graph=True
        )

    @classmethod
    def tearDownClass(cls):
        cls.temp.cleanup()

    def test_archive_is_reproducible(self):
        self.assertEqual(self.first.read_bytes(), self.second.read_bytes())
        self.assertEqual(self.first_result["sha256"], self.second_result["sha256"])

    def test_payload_is_stable_under_crlf_checkout_presentation(self):
        expected = BUILDER.build_payload(allow_missing_graph=True)
        original_read = BUILDER.read_regular

        def crlf_read(rel):
            data = original_read(rel)
            if not BUILDER.is_text_payload_path(rel):
                return data
            normalized = data.replace(b"\r\n", b"\n").replace(b"\r", b"\n")
            return normalized.replace(b"\n", b"\r\n")

        with mock.patch.object(BUILDER, "read_regular", side_effect=crlf_read):
            crlf_payload = BUILDER.build_payload(allow_missing_graph=True)
        self.assertEqual(expected, crlf_payload)
        self.assertTrue(all(
            b"\r" not in data
            for rel, data in expected.items()
            if BUILDER.is_text_payload_path(rel)
        ))

    def test_crlf_proof_graph_report_is_rebound_to_packaged_bytes(self):
        source_report = json.loads((
            BUILDER.REPO_ROOT / "research-wiki" / "proof-graph"
            / "benchmark_report.json"
        ).read_text(encoding="utf-8"))
        graph = {
            "schema_version": 1,
            "counts": source_report["graph"]["counts"],
        }
        graph_bytes = (
            json.dumps(graph, indent=2, sort_keys=True) + "\n"
        ).encode("utf-8").replace(b"\n", b"\r\n")
        graph_path = self.root / "crlf-proof-graph.json"
        report_path = self.root / "crlf-proof-report.json"
        graph_path.write_bytes(graph_bytes)
        source_report["graph"]["sha256"] = hashlib.sha256(graph_bytes).hexdigest()
        report_path.write_bytes((
            json.dumps(source_report, indent=2, sort_keys=True) + "\n"
        ).encode("utf-8").replace(b"\n", b"\r\n"))

        payload = BUILDER.build_payload(graph_path, report_path)
        packaged_graph = payload[
            "evidence/proof-graph/current-proof-graph.json"
        ]
        packaged_report = json.loads(payload[
            "evidence/proof-graph/current-benchmark-report.json"
        ].decode("utf-8"))
        self.assertNotIn(b"\r", packaged_graph)
        self.assertEqual(
            packaged_report["graph"]["sha256"],
            hashlib.sha256(packaged_graph).hexdigest(),
        )

    def test_archive_has_expected_positive_allowlist(self):
        with zipfile.ZipFile(str(self.first)) as archive:
            names = set(archive.namelist())
        prefix = BUILDER.ARCHIVE_ROOT + "/"
        self.assertIn(prefix + "BanditRLProof.lean", names)
        self.assertIn(prefix + "Tests.lean", names)
        self.assertIn(prefix + "Tests/DelayedFeedbackPaperAuditCanary.lean", names)
        self.assertIn(prefix + "evidence/claim-ledger.json", names)
        self.assertIn(prefix + "artifact/verify_artifact.py", names)
        self.assertIn(prefix + "tools/prepare_target_drift_checker_image.py", names)
        self.assertIn(prefix + "tools/target_drift_checker_cache_manifest.py", names)
        self.assertIn(
            prefix + "evaluation/target-drift-v2/checker-image-candidate-record.json",
            names,
        )
        self.assertFalse(any("32137509103" in name for name in names))
        self.assertIn(
            prefix + "research-wiki/proof-graph/benchmark_report.json", names
        )
        self.assertIn(
            prefix + "research-wiki/proof-graph/proof_cost.schema.json", names
        )
        self.assertFalse(any("website/_site" in name for name in names))
        self.assertFalse(any("contributors.json" in name for name in names))
        self.assertFalse(any(name.endswith(".pdf") for name in names))
        self.assertFalse(any(".git/" in name for name in names))

    def test_extracted_verifier_passes(self):
        destination = self.root / "extracted"
        with zipfile.ZipFile(str(self.first)) as archive:
            archive.extractall(str(destination))
        artifact = destination / BUILDER.ARCHIVE_ROOT
        result = subprocess.run(
            [sys.executable, "artifact/verify_artifact.py"],
            cwd=str(artifact),
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            encoding="utf-8",
        )
        self.assertEqual(result.returncode, 0, msg=result.stdout + result.stderr)
        report = json.loads(result.stdout)
        self.assertTrue(report["artifact_verified"])
        self.assertFalse(report["target_drift_results_present"])

    def test_extracted_verifier_rejects_unmanifested_file(self):
        # Keep the path short enough for the longest Lean module on Windows.
        destination = self.root / "extra"
        with zipfile.ZipFile(str(self.first)) as archive:
            archive.extractall(str(destination))
        artifact = destination / BUILDER.ARCHIVE_ROOT
        (artifact / "unexpected-output.json").write_text("{}\n", encoding="utf-8")
        result = subprocess.run(
            [sys.executable, "artifact/verify_artifact.py"],
            cwd=str(artifact),
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            encoding="utf-8",
        )
        self.assertNotEqual(result.returncode, 0)
        self.assertIn("unmanifested extracted file", result.stdout + result.stderr)

    def test_claim_ledger_has_conservative_counts(self):
        payload = BUILDER.build_payload(allow_missing_graph=True)
        ledger = json.loads(payload["evidence/claim-ledger.json"].decode("utf-8"))
        self.assertEqual(ledger["delayed_feedback"]["implementation_facing_declaration_count"], 88)
        self.assertEqual(
            ledger["delayed_feedback"]["diagnostic_conditional_repair_declaration_count"],
            19,
        )
        self.assertEqual(ledger["delayed_feedback"]["source_audit_declaration_count"], 107)
        self.assertFalse(ledger["delayed_feedback"]["paper_endpoint_verified"])
        self.assertEqual(ledger["source_records"][BUILDER.DELAYED_DIAGNOSTIC_ID]["status"], "partial")
        self.assertEqual(
            ledger["source_records"]["TARGET-DRIFT-V2-CONTROLLED-EVALUATION"]["status"],
            "planned",
        )
        direct_textbook_records = {
            "TEXTBOOK-PART-IV-THEOREM-13-1-GAUSSIAN-MINIMAX",
            "TEXTBOOK-PART-IV-CH15-SAME-POLICY-HISTORY-KL-DECOMPOSITION",
            "TEXTBOOK-PART-IV-CH15-GAUSSIAN-MINIMAX-LOWER-BOUND",
        }
        textbook_row = next(
            row for row in ledger["table_rows"]
            if row["artifact"] == "Textbook Chapters 13--17"
        )
        self.assertTrue(
            direct_textbook_records.issubset(set(textbook_row["source_record_ids"]))
        )
        for record_id in direct_textbook_records:
            self.assertEqual(ledger["source_records"][record_id]["status"], "compiled")

    def test_public_base_is_replaced_by_anonymous_tree_binding(self):
        payload = BUILDER.build_payload(allow_missing_graph=True)
        joined = b"\n".join(payload.values()).lower()
        self.assertNotIn(BUILDER.PUBLIC_WORKSPACE_BASE_COMMIT.encode("ascii"), joined)
        self.assertNotIn(
            b"cb5d50be148c691cc595ed9fd2f535c42506fada", joined
        )
        base = json.loads(
            payload["evidence/anonymous-base-manifest.json"].decode("utf-8")
        )
        self.assertFalse(base["git_object_database_included"])
        self.assertFalse(base["materializable_by_target_drift_runner"])
        readme = payload["evaluation/target-drift-v2/README.md"].decode("utf-8")
        self.assertIn("non-Git", readme)
        self.assertNotIn("the public base immediately", readme)
        self.assertNotIn(BUILDER.PUBLIC_CANDIDATE_RUN_ID, readme)
        candidate = json.loads(payload[
            "evaluation/target-drift-v2/checker-image-candidate-record.json"
        ].decode("utf-8"))
        self.assertEqual(
            candidate["workflow_run"]["id"], "<redacted-public-run-id>"
        )
        self.assertEqual(
            candidate["workflow_run"]["head_commit"],
            "<anonymous-builder-snapshot>",
        )

    def test_result_free_evaluation_allowlist_is_closed(self):
        tracked = BUILDER.git_tracked_files()
        tracked.add("evaluation/target-drift-v2/run-result.json")
        with self.assertRaisesRegex(ValueError, "unreviewed evaluation file"):
            BUILDER.evaluation_files(tracked)

    def test_identity_and_host_path_markers_are_rejected(self):
        with self.assertRaises(ValueError):
            BUILDER.require_anonymous_bytes("bad.txt", b"github.com/DakeBU/project")
        with self.assertRaises(ValueError):
            BUILDER.require_anonymous_bytes("bad.txt", b"C:/Users/example/file")
        with self.assertRaises(ValueError):
            BUILDER.require_anonymous_bytes("bad.txt", b"person@example.edu")
        BUILDER.require_anonymous_bytes("good.txt", b"https://example.org/paper.pdf")

    def test_cli_requires_a_bound_graph_and_report(self):
        with self.assertRaises(ValueError):
            BUILDER.build_payload()


if __name__ == "__main__":
    unittest.main()
