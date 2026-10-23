"""Source-qualified catalogue ranges must preserve complete actual definitions."""
import hashlib
import json
import tempfile
import unittest
from pathlib import Path
from unittest.mock import patch

from website.scripts import build_site as site


class SourceDeclarationBoundaryTests(unittest.TestCase):
    SOURCE = (
        "namespace Example\n"
        "def state (initial : Nat) : Nat → Nat\n"
        "  | 0 => initial\n"
        "  | t + 1 => state initial t + 1\n"
        "\n/-- Next theorem, excluded from the definition. -/\n"
        "theorem state_zero (initial : Nat) : state initial 0 = initial := by rfl\n"
        "end Example\n"
    )

    def setUp(self):
        self.temporary = tempfile.TemporaryDirectory()
        self.addCleanup(self.temporary.cleanup)
        self.root = Path(self.temporary.name)
        self.content = self.root / "website/content"
        self.content.mkdir(parents=True)
        self.file = self.root / "BanditRLProof/Example.lean"
        self.file.parent.mkdir()
        self.file.write_bytes(self.SOURCE.encode())
        self.entry = {
            "full_name": "Example.state", "file": "BanditRLProof/Example.lean",
            "file_sha256": hashlib.sha256(self.file.read_bytes()).hexdigest(),
            "start_line": 2, "end_line": 4,
            "block_LF_sha256": self.block_hash(4), "reason": "Reviewed complete source range",
        }
        self.root_patch = patch.object(site, "ROOT", self.root)
        self.content_patch = patch.object(site, "CONTENT_DIR", self.content)
        self.root_patch.start()
        self.content_patch.start()
        self.addCleanup(self.root_patch.stop)
        self.addCleanup(self.content_patch.stop)

    def block_hash(self, end):
        return hashlib.sha256("\n".join(self.SOURCE.splitlines()[1:end]).encode()).hexdigest()

    def configure(self, entries=None):
        (self.content / "declaration-boundaries.json").write_text(
            json.dumps({"schema_version": 1, "entries": entries or [self.entry]}), encoding="utf-8"
        )

    def test_complete_definition_excludes_neighbor_and_preserves_theorem(self):
        before = site.scan_module(self.file)["declarations"]
        self.configure()
        after = site.scan_lean_tree()[0]["declarations"]
        self.assertEqual(after[0]["statement"], " ".join(s.strip() for s in self.SOURCE.splitlines()[1:4]))
        self.assertNotIn("theorem", after[0]["statement"])
        self.assertEqual(after[1], before[1])
        self.assertEqual({k: v for k, v in after[0].items() if k != "statement"},
                         {k: v for k, v in before[0].items() if k != "statement"})

    def test_stale_file_and_block_pins_fail_closed(self):
        for key in ("file_sha256", "block_LF_sha256"):
            with self.subTest(key=key):
                original = self.entry[key]
                self.entry[key] = "0" * 64
                self.configure()
                with self.assertRaisesRegex(ValueError, "Stale"):
                    site.scan_lean_tree()
                self.entry[key] = original

    def test_truncation_rejected_even_with_matching_rehashed_block(self):
        self.entry.update(end_line=3, block_LF_sha256=self.block_hash(3))
        self.configure()
        with self.assertRaisesRegex(ValueError, "skips source code"):
            site.scan_lean_tree()

    def test_wrong_file_name_or_start_is_not_silently_ignored(self):
        for key, bad in (("file", "BanditRLProof/Missing.lean"),
                         ("full_name", "Example.missing"), ("start_line", 1)):
            with self.subTest(key=key):
                original = self.entry[key]
                self.entry[key] = bad
                self.configure()
                with self.assertRaises(ValueError):
                    site.scan_lean_tree()
                self.entry[key] = original

    def test_duplicate_or_invalid_metadata_rejected(self):
        self.configure([self.entry, self.entry.copy()])
        with self.assertRaisesRegex(ValueError, "duplicate"):
            site.scan_lean_tree()
        self.entry["end_line"] = True
        self.configure()
        with self.assertRaisesRegex(ValueError, "Invalid"):
            site.scan_lean_tree()

    def test_missing_optional_config_keeps_default_statements(self):
        module = site.scan_lean_tree()[0]
        self.assertEqual(module, site.scan_module(self.file, []))
        self.assertEqual(module["declarations"][0]["statement"], site.compact_statement(self.SOURCE.splitlines(), 1))


if __name__ == "__main__":
    unittest.main()
