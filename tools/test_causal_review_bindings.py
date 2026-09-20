"""Regression checks for stale commit bindings and missing semantic coverage."""
import copy
import json
from pathlib import Path
import subprocess
import tempfile
import unittest

from check_causal_review_bindings import check, digest, NORMALIZATION, source_digest, ROOT, RECEIPT


class ReviewBindingsTests(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.addCleanup(self.tmp.cleanup)
        self.root = Path(self.tmp.name)
        self.path = self.root / "A.lean"
        self.path.write_bytes(b"def a := 1\n")
        def git(*args):
            return subprocess.check_output(["git", "-C", str(self.root), *args], stderr=subprocess.DEVNULL).decode().strip()
        git("init")
        git("-c", "core.autocrlf=false", "add", "A.lean")
        git("-c", "user.name=Test", "-c", "user.email=test@example.invalid", "commit", "-m", "fixture")
        self.receipt = {"code_commit": git("rev-parse", "HEAD"), "normalization": NORMALIZATION,
            "production_hashes_lf": {"A.lean": source_digest(self.path.read_bytes())},
            "review_hashes": {"blind.md": digest(b"blind"), "source.md": digest(b"source")},
            "semantic_reviews": [{"formalizer": "a", "blind_decoder": "b", "source_reviewer": "c",
                "verdict": "accepted", "files": ["A.lean"], "blind_report": "blind.md", "source_report": "source.md"}]}

    def test_line_endings_only_are_equivalent(self):
        self.path.write_bytes(b"def a := 1\r\n")
        self.assertTrue(check(self.root, self.receipt)["reviewed_file_hashes_verified"])

    def test_historical_stale_hash_fails(self):
        self.receipt["production_hashes_lf"]["A.lean"] = "0" * 64
        with self.assertRaisesRegex(ValueError, "commit hash mismatch"):
            check(self.root, self.receipt)

    def test_forged_current_hash_cannot_hide_commit_drift(self):
        self.path.write_bytes(b"def a := 2\n")
        self.receipt["production_hashes_lf"]["A.lean"] = source_digest(self.path.read_bytes())
        with self.assertRaisesRegex(ValueError, "commit hash mismatch"):
            check(self.root, self.receipt)

    def test_uncommitted_drift_fails(self):
        self.path.write_bytes(b"def a := 2\n")
        with self.assertRaisesRegex(ValueError, "working-tree hash mismatch"):
            check(self.root, self.receipt)

    def test_missing_coverage_and_same_actor_fail(self):
        for change in ({"files": []}, {"source_reviewer": "a"}, {"source_reviewer": "a "},
                       {"source_report": "missing.md"}, {"source_report": "blind.md"}):
            data = copy.deepcopy(self.receipt)
            data["semantic_reviews"][0].update(change)
            with self.assertRaises(ValueError):
                check(self.root, data)

    def test_tree_cannot_impersonate_commit(self):
        self.receipt["code_commit"] = subprocess.check_output(
            ["git", "-C", str(self.root), "rev-parse", "HEAD^{tree}"]).decode().strip()
        with self.assertRaisesRegex(ValueError, "commit object"):
            check(self.root, self.receipt)

    def test_malformed_review_hash_fails_without_private_reports(self):
        self.receipt["review_hashes"]["source.md"] = "not-a-hash"
        with self.assertRaisesRegex(ValueError, "invalid review SHA256"):
            check(self.root, self.receipt)

    def test_private_report_drift_fails(self):
        (self.root / "blind.md").write_bytes(b"blind")
        (self.root / "source.md").write_bytes(b"source")
        self.assertTrue(check(self.root, self.receipt, self.root)["private_review_reports_verified"])
        (self.root / "source.md").write_bytes(b"changed")
        with self.assertRaisesRegex(ValueError, "review report mismatch"):
            check(self.root, self.receipt, self.root)


class LiveCausalReceiptTests(unittest.TestCase):
    def test_current_causal_review_bindings(self):
        receipt = json.loads((ROOT / RECEIPT).read_text(encoding="utf-8"))
        # Independent inventory prevents deleting an obligation from BOTH the
        # bindings and the coverage metadata to make a reduced packet pass.
        modules = ("OrderedLaw", "MarginalLaw", "Importance", "Allocation", "OptimalAllocation",
                   "Sampling", "SampleMGF", "Tuning", "Confidence", "Recommendation",
                   "ExpectedRegret", "AllocationRegret")
        expected = {f"BanditRLProof/Algorithms/Causal{x}.lean" for x in modules}
        expected.add("Tests/CausalNoisyGraphCanary.lean")
        self.assertEqual(set(receipt["production_hashes_lf"]), expected)
        self.assertTrue(check(ROOT, receipt)["reviewed_file_hashes_verified"])


if __name__ == "__main__":
    unittest.main()
