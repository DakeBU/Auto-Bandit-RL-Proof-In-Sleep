import importlib.util
import json
import subprocess
import sys
import tempfile
import unittest
import zipfile
from pathlib import Path


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

    def test_archive_has_expected_positive_allowlist(self):
        with zipfile.ZipFile(str(self.first)) as archive:
            names = set(archive.namelist())
        prefix = BUILDER.ARCHIVE_ROOT + "/"
        self.assertIn(prefix + "BanditRLProof.lean", names)
        self.assertIn(prefix + "Tests.lean", names)
        self.assertIn(prefix + "Tests/DelayedFeedbackPaperAuditCanary.lean", names)
        self.assertIn(prefix + "evidence/claim-ledger.json", names)
        self.assertIn(prefix + "artifact/verify_artifact.py", names)
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
