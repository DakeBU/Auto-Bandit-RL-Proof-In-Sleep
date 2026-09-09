"""Regression gates for shared book/setting references, without invoking Lean."""
import copy
import json
import unittest

from website.scripts import build_site as site
from website.scripts.book_registry import build_registry, membership_index


class BookRegistryTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.config = site.load_json(site.CONTENT_DIR / "books.json")
        cls.chapters = site.load_json(site.CONTENT_DIR / "chapters.json")["chapters"]
        cls.spine = site.load_json(site.CONTENT_DIR / "textbook_spine.json")
        cls.wiki = site.load_json(site.CONTENT_DIR / "banditrlwiki.json")
        modules = site.scan_lean_tree()
        site.assign_chapters(modules, cls.chapters)
        cls.declarations = [d for m in modules for d in m["declarations"]]

    def registry(self, config=None, wiki=None, declarations=None, verified=False):
        return build_registry(config or self.config, self.chapters, self.spine,
                              wiki or self.wiki, declarations or self.declarations,
                              verified, "fixture-commit")

    def test_one_identity_across_books_preserves_every_indexed_declaration(self):
        registry = self.registry()
        nodes = membership_index(registry)
        self.assertEqual(len(nodes), len(self.declarations))
        shared = [n for n in nodes.values() if len(n["books"]) > 1]
        self.assertTrue(shared)
        rl = next(c for c in registry["chapters"] if c["id"] == "teaching:finite-horizon-rl")
        self.assertTrue(rl["node_ids"])
        for key in rl["node_ids"]:
            self.assertIn("bandit", nodes[key]["books"])
            self.assertIn("reinforcement-learning", nodes[key]["books"])
            self.assertEqual("source", nodes[key]["status"])

    def test_duplicate_canonical_id_fails_before_export(self):
        with self.assertRaisesRegex(ValueError, "duplicate canonical ID"):
            self.registry(declarations=self.declarations + [self.declarations[0]])

    def test_duplicate_books_and_dangling_chapter_refs_are_rejected(self):
        config = copy.deepcopy(self.config)
        config["books"].append(config["books"][0])
        with self.assertRaisesRegex(ValueError, "duplicate book"):
            self.registry(config=config)
        config = copy.deepcopy(self.config)
        config["books"][1]["chapter_refs"].append("teaching:missing")
        with self.assertRaisesRegex(ValueError, "invalid chapter reference"):
            self.registry(config=config)

    def test_invalid_setting_and_case_references_are_rejected(self):
        wiki = copy.deepcopy(self.wiki)
        wiki["topics"][0]["related_cases"].append("unknown-case")
        with self.assertRaisesRegex(ValueError, "unknown related case"):
            self.registry(wiki=wiki)
        wiki = copy.deepcopy(self.wiki)
        wiki["topics"].append(wiki["topics"][0])
        with self.assertRaisesRegex(ValueError, "duplicate topic"):
            self.registry(wiki=wiki)

    def test_gate_changes_evidence_only_not_identity_or_membership(self):
        preview = membership_index(self.registry())
        verified = membership_index(self.registry(verified=True))
        self.assertEqual(preview.keys(), verified.keys())
        for key, node in preview.items():
            other = verified[key]
            self.assertEqual({k: v for k, v in node.items() if k != "status"},
                             {k: v for k, v in other.items() if k != "status"})
            self.assertEqual("stated" if node["status"] == "stated" else "compiled", other["status"])

    def test_new_topics_have_no_claimed_results_or_compiled_counts(self):
        registry = self.registry(verified=True)
        self.assertEqual(10, len(self.wiki["topics"]))
        topic_ids = {t["id"] for t in self.wiki["topics"]}
        for setting in registry["settings"]:
            if setting["id"] in topic_ids:
                self.assertEqual([], setting["node_ids"])
                self.assertEqual("source-audit-pending", setting["status"])
        method = next(t for t in self.wiki["topics"] if t["id"] == "thompson-bayesian")
        self.assertEqual("method", method["kind"])
        self.assertIn("cross-setting", method["tags"])
        self.assertEqual(12, len(self.wiki["comparison_fields"]))

    def test_source_versions_and_planned_book_boundaries(self):
        books = {b["id"]: b for b in self.config["books"]}
        self.assertEqual(4, len(books))
        self.assertIn("June 27, 2026", books["reinforcement-learning"]["source"]["version"])
        self.assertTrue(books["online-learning"]["source"]["url"].endswith("v10"))
        self.assertIsNone(books["conformal-prediction"]["source"])
        for key in books.keys() - {"bandit"}:
            self.assertEqual("planned", books[key]["status"])

    def test_navigation_has_one_current_page_and_shared_chapter_context(self):
        saved = (site.SITE_CHAPTERS, site.SITE_BOOKS, site.SITE_TEXTBOOK_SPINE, site.SITE_REGISTRY)
        try:
            site.SITE_CHAPTERS, site.SITE_BOOKS = self.chapters, self.config
            site.SITE_TEXTBOOK_SPINE, site.SITE_REGISTRY = self.spine, self.registry()
            for path, key in [("chapters/finite-horizon-rl/index.html", "finite-horizon-rl"),
                              ("textbook-spine/chapter-17-high-probability/index.html", "textbook-spine"),
                              ("books/bandit/index.html", "bandit")]:
                source = site.layout(path, "Fixture", "", [], key, False, "fixture")
                nav = source.split('<nav class="sidebar-nav"', 1)[1].split('</nav>', 1)[0]
                self.assertEqual(1, nav.count('aria-current="page"'))
                self.assertNotIn("Learn · Book map", nav)
                self.assertNotIn("Textbook spine · Part IV", nav)
                self.assertEqual(10, nav.count('class="book-nav-link"'))
                self.assertEqual(5, nav.count('class="spine-nav-link"'))
            breadcrumb = site.render_book_breadcrumb("chapters/finite-horizon-rl/index.html")
            self.assertIn("Reinforcement Learning Book", breadcrumb)
        finally:
            site.SITE_CHAPTERS, site.SITE_BOOKS, site.SITE_TEXTBOOK_SPINE, site.SITE_REGISTRY = saved


if __name__ == "__main__":
    unittest.main()
