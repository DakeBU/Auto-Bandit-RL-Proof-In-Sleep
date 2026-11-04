"""Source-qualified catalogue ranges must preserve complete actual definitions."""
import copy
import hashlib
import json
import tempfile
import unittest
from pathlib import Path
from unittest.mock import patch

from website.scripts import build_site as site
from website.scripts import check_site as site_check


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

    def test_result_let_signature_preserves_copyable_source_header(self):
        header = (
            "theorem pair (n : Nat := 2) :\n"
            "    /- The result has two local values. -/\n"
            "    let x := n\n"
            "    let y := x + 1\n"
            "    y = n + 1"
        )
        source = header + " := by rfl\ntheorem next : True := by trivial\n"
        self.assertEqual(site.compact_statement(source.splitlines(), 0), header)
        ordinary = "theorem plain (n : Nat := 2) : n = n := by rfl"
        self.assertEqual(site.compact_statement([ordinary], 0),
                         "theorem plain (n : Nat := 2) : n = n")

    def test_graph_keeps_exact_multiline_statement_beyond_preview_limit(self):
        header = (
            "theorem long_result :\n"
            "    /- " + "source context " * 80 + "-/\n"
            "    let x := 2\n"
            "    let y := x + 1\n"
            "    y = 3"
        )
        self.file.write_text(header + " := by rfl\n", encoding="utf-8")
        module = site.scan_module(self.file, [])
        module.update(chapter="example", chapter_title="Example")
        declaration = module["declarations"][0]
        declaration.update(chapter="example", chapter_title="Example", module_slug=module["slug"], module=module["name"])
        self.assertEqual(declaration["statement"], header)
        chapter = dict(slug="example", short_title="Example", title="Example",
                       status="partial", summary="Example")
        report = dict(graph=dict(counts=dict(project_nodes=0, edges=0)),
                      benchmark_contract=dict(root_count=0), benchmarks=[])
        output = self.root / "generated"
        with patch.object(site, "SITE_REGISTRY", {"books": [], "settings": []}), \
             patch.object(site, "SITE_MEMBERSHIPS", {}), \
             patch.object(site, "layout", return_value=""), \
             patch.object(site, "write_page"):
            site.build_lean_graph(output, [module], [declaration], [chapter], [], [],
                                  {"chapters": []}, report,
                                  {"cng_candidate": {"status": "prototype"}}, False, "test")
        graph = json.loads((output / "lean-graph/graph.json").read_text(encoding="utf-8"))
        node = next(n for n in graph["nodes"]
                    if n["id"] == "declaration:" + declaration["full_name"])
        self.assertEqual(node["statement"], declaration["statement"])
        self.assertGreater(len(node["statement"]), 900)
        shard = json.loads((output / "lean-graph" / node["shard"]).read_text(encoding="utf-8"))
        self.assertEqual(next(n for n in shard["nodes"] if n["id"] == node["id"])["statement"], header)

    def test_oversized_graph_branch_defers_and_checks_exact_statements(self):
        header = "theorem large :\n    /- " + "context " * 850 + "-/\n    let x := 2\n    x = 2"
        self.file.write_text(header + " := by rfl\n", encoding="utf-8")
        module = site.scan_module(self.file, [])
        original = module["declarations"][0]
        declarations = []
        for index in range(150):
            declaration = copy.deepcopy(original)
            declaration["full_name"] = f"Example.large{index}"
            declaration["anchor"] = f"decl-{index}"
            declaration.update(chapter="example", chapter_title="Example",
                               module_slug=module["slug"], module=module["name"])
            declarations.append(declaration)
        module.update(chapter="example", chapter_title="Example", declarations=declarations)
        chapter = dict(slug="example", short_title="Example", title="Example",
                       status="partial", summary="Example")
        report = dict(graph=dict(counts=dict(project_nodes=0, edges=0)),
                      benchmark_contract=dict(root_count=0), benchmarks=[])
        output = self.root / "deferred"
        with patch.object(site, "SITE_REGISTRY", {"books": [], "settings": []}), \
             patch.object(site, "SITE_MEMBERSHIPS", {}), \
             patch.object(site, "layout", return_value=""), patch.object(site, "write_page"):
            site.build_lean_graph(output, [module], declarations, [chapter], [], [],
                                  {"chapters": []}, report,
                                  {"cng_candidate": {"status": "prototype"}}, False, "test")
        root = output / "lean-graph"
        shards = [root / "overview.json"] + list((root / "views").glob("*.json")) + list((root / "modules").glob("*.json"))
        sidecars = list((root / "statements").glob("*.json"))
        self.assertEqual(len(sidecars), 1)
        self.assertTrue(all(p.stat().st_size <= 1_200_000 for p in shards + sidecars))
        payload = json.loads(sidecars[0].read_text(encoding="utf-8"))
        self.assertEqual(payload["statements"]["declaration:Example.large0"], header)
        self.assertEqual(site_check.check_graph_exact_statement_payloads(output, shards), [])
        original_text = sidecars[0].read_text(encoding="utf-8")
        for replacement in ({"schema_version": 1, "statements": {}},
                            {"schema_version": 1, "statements": {**payload["statements"], "declaration:extra": header}},
                            {"schema_version": 1, "statements": {**payload["statements"], "declaration:Example.large0": "wrong"}},
                            {"schema_version": 1, "statements": {**payload["statements"], "declaration:Example.large0": 7}}):
            sidecars[0].write_text(json.dumps(replacement), encoding="utf-8")
            self.assertTrue(site_check.check_graph_exact_statement_payloads(output, shards))
        sidecars[0].write_text(original_text + " " * 1_200_000, encoding="utf-8")
        self.assertTrue(site_check.check_graph_exact_statement_payloads(output, shards))
        sidecars[0].unlink()
        self.assertTrue(site_check.check_graph_exact_statement_payloads(output, shards))
        sidecars[0].write_text(original_text, encoding="utf-8")
        orphan = root / "statements" / ("0" * 32 + ".json")
        orphan.write_text(original_text, encoding="utf-8")
        self.assertTrue(site_check.check_graph_exact_statement_payloads(output, shards))
        orphan.unlink()
        branch = next(p for p in shards if '"statement_source"' in p.read_text())
        original_branch = branch.read_text()
        for source in ("../escape.json", 7):
            data = json.loads(original_branch)
            next(n for n in data["nodes"] if "statement_source" in n)["statement_source"] = source
            branch.write_text(json.dumps(data), encoding="utf-8")
            self.assertTrue(site_check.check_graph_exact_statement_payloads(output, shards))
        data = json.loads(original_branch)
        next(n for n in data["nodes"] if "statement_source" in n)["statement"] = header
        branch.write_text(json.dumps(data), encoding="utf-8")
        self.assertTrue(site_check.check_graph_exact_statement_payloads(output, shards))

    def test_missing_optional_config_keeps_default_statements(self):
        module = site.scan_lean_tree()[0]
        self.assertEqual(module, site.scan_module(self.file, []))
        self.assertEqual(module["declarations"][0]["statement"], site.compact_statement(self.SOURCE.splitlines(), 1))

    def test_assignment_definition_exposes_exact_body_only_when_requested(self):
        self.SOURCE = self.SOURCE.replace(
            "def state (initial : Nat) : Nat → Nat\n  | 0 => initial\n  | t + 1 => state initial t + 1",
            "def state (initial : Nat) (t : Nat) : Nat :=\n  match t with\n  | 0 => initial\n  | n + 1 => state initial n + 1",
        )
        self.file.write_bytes(self.SOURCE.encode())
        self.entry.update(
            end_line=5, file_sha256=hashlib.sha256(self.file.read_bytes()).hexdigest(),
            block_LF_sha256=self.block_hash(5), include_definition_body=True,
        )
        before = site.scan_module(self.file, [])["declarations"]
        self.configure()
        after = site.scan_lean_tree()[0]["declarations"]
        self.assertEqual(after[0]["statement"], "\n".join(self.SOURCE.splitlines()[1:5]))
        self.assertNotIn("match", before[0]["statement"])
        self.assertEqual(after[1], before[1])
        self.entry.update(end_line=4, block_LF_sha256=self.block_hash(4))
        self.configure()
        with self.assertRaisesRegex(ValueError, "skips source code"):
            site.scan_lean_tree()

    def configure_abbreviation(self, prefix="noncomputable abbrev"):
        self.SOURCE = (
            "namespace Example\n"
            + prefix + " state (initial : Nat) : Nat → Nat :=\n"
            "  fun t => initial + t\n"
            "\n/-- Neighbor must remain unchanged. -/\n"
            "theorem state_zero (initial : Nat) : state initial 0 = initial := by rfl\n"
            "end Example\n"
        )
        self.file.write_bytes(self.SOURCE.encode())
        self.entry.update(end_line=3, file_sha256=hashlib.sha256(self.file.read_bytes()).hexdigest(),
                          block_LF_sha256=self.block_hash(3), include_definition_body=True)

    def test_abbreviation_body_is_opt_in_and_preserves_neighbor_and_metadata(self):
        self.configure_abbreviation()
        before = site.scan_module(self.file, [])["declarations"]
        self.configure()
        after = site.scan_lean_tree()[0]["declarations"]
        self.assertEqual(after[0]["kind"], "abbrev")
        self.assertEqual(after[0]["statement"], "\n".join(self.SOURCE.splitlines()[1:3]))
        self.assertNotIn("fun t", before[0]["statement"])
        self.assertEqual(after[1], before[1])
        self.assertEqual({k:v for k,v in after[0].items() if k != "statement"},
                         {k:v for k,v in before[0].items() if k != "statement"})
        self.entry["include_definition_body"] = False
        self.configure()
        self.assertNotIn("fun t", site.scan_lean_tree()[0]["declarations"][0]["statement"])

    def test_abbreviation_truncation_and_neighbor_overlap_fail_closed(self):
        self.configure_abbreviation()
        for end in (2, 6):
            with self.subTest(end=end):
                self.entry.update(end_line=end, block_LF_sha256=self.block_hash(end))
                self.configure()
                with self.assertRaises(ValueError):
                    site.scan_lean_tree()

    def test_abbreviation_stale_pins_fail_closed(self):
        self.configure_abbreviation()
        for key in ("file_sha256", "block_LF_sha256"):
            with self.subTest(key=key):
                original = self.entry[key]
                self.entry[key] = "0" * 64
                self.configure()
                with self.assertRaisesRegex(ValueError, "Stale"):
                    site.scan_lean_tree()
                self.entry[key] = original

    def test_private_abbreviation_remains_ineligible(self):
        self.configure_abbreviation("private abbrev")
        self.configure()
        with self.assertRaises(ValueError):
            site.scan_lean_tree()

    def test_definition_body_flag_requires_boolean(self):
        self.entry["include_definition_body"] = "true"
        self.configure()
        with self.assertRaisesRegex(ValueError, "Invalid"):
            site.scan_lean_tree()


if __name__ == "__main__":
    unittest.main()
