from __future__ import annotations

import json
import unittest
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]


def load(path: str) -> dict:
    return json.loads((ROOT / path).read_text(encoding="utf-8"))


class BanditTaxonomyTechniqueTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls) -> None:
        cls.atlas = load("website/public-repo/data/setting-atlas.json")
        cls.techniques = load("website/content/bandit_technique_map.json")
        cls.functor = load("website/content/functor_hypergraph.json")
        cls.frontier = load("website/public-repo/data/frontier-problems.json")
        cls.screening = load("website/content/frontier_source_audits.json")
        cls.settings = {item["id"]: item for item in cls.atlas["entries"]}
        cls.technique_by_id = {item["id"]: item for item in cls.techniques["techniques"]}
        cls.functor_by_id = {item["id"]: item for item in cls.functor["families"]}

    def test_requested_bandit_landscape_is_canonicalized(self) -> None:
        required = {
            "mab",
            "single-objective",
            "regret-minimization",
            "best-arm-identification",
            "ballooning",
            "causal",
            "combinatorial",
            "constrained",
            "contextual",
            "convex-bandits",
            "dueling",
            "dynamic-nonstationary",
            "factored",
            "federated",
            "gp-ucb",
            "generalized-linear",
            "graphical",
            "heavy-tailed",
            "lipschitz",
            "llm-bandits",
            "matching",
            "matrix-low-rank",
            "missing-outcome",
            "model-selection",
            "multi-agent",
            "multi-bandit",
            "multi-fidelity",
            "mnl",
            "parameter-free",
            "safe-bandits",
            "semi-adversarial",
            "thresholding",
            "thompson",
            "unimodal",
            "variance-aware",
            "corruption-tolerant",
            "multi-objective",
            "quantum-bandits",
        }
        self.assertEqual(required - set(self.settings), set())

    def test_slb_is_alias_of_linear_and_only_unresolved_aliases_remain_quarantined(self) -> None:
        self.assertIn("SLB", self.settings["linear"].get("aliases", []))
        ambiguous = {item["id"] for item in self.atlas["entries"] if item["kind"] == "ambiguous"}
        self.assertEqual(ambiguous, {"omdp-alias", "transform-alias"})

    def test_every_technique_setting_and_functor_reference_resolves(self) -> None:
        for technique in self.techniques["techniques"]:
            with self.subTest(technique=technique["id"]):
                missing_settings = set(technique.get("setting_ids", [])) - set(self.settings)
                self.assertEqual(missing_settings, set())
                self.assertIn(technique["functor_family"], self.functor_by_id)

    def test_every_functor_technique_reference_resolves(self) -> None:
        for family in self.functor["families"]:
            for technique_id in family.get("technique_ids", []):
                with self.subTest(family=family["id"], technique=technique_id):
                    self.assertIn(technique_id, self.technique_by_id)

    def test_quantum_bandit_cross_library_contract_is_explicit(self) -> None:
        quantum = self.settings["quantum-bandits"]
        self.assertEqual(quantum["site_status"], "cross-library-route")
        self.assertEqual(
            quantum["cross_library"]["project"],
            "ASPBE / QuantumComputinglib",
        )
        self.assertTrue((ROOT / "docs/quantum-bandit-cross-library-protocol.md").exists())
        technique = self.technique_by_id["quantum-estimation-testing"]
        projects = {item["project"] for item in technique["cross_library"]}
        self.assertIn("ASPBE / QuantumComputinglib", projects)
        self.assertIn("Hayata-Yamasaki-Group/lean-quantum", projects)
        self.assertIn("Timeroot/Lean-QuantumInfo", projects)

    def test_colt_2023_screening_does_not_inflate_core_bandit_frontier(self) -> None:
        collection = next(
            item
            for item in self.screening["collections"]
            if item["id"] == "colt-2023-open-problems"
        )
        self.assertEqual(len(collection["items"]), 5)
        self.assertEqual(collection["core_bandit_rl_count"], 0)
        self.assertTrue(all(not item["core_bandit_rl"] for item in collection["items"]))
        sparse = next(
            item
            for item in collection["items"]
            if item["title"] == "Learning sparse linear concepts by priming the features"
        )
        self.assertEqual(sparse["project_route"], "book:online-learning")
        frontier = next(
            item
            for item in self.frontier["problems"]
            if item["id"] == "sparse-linear-priming-online-regret"
        )
        self.assertFalse(frontier["core_bandit_rl"])
        self.assertEqual(frontier["route_target"], "book:online-learning")


if __name__ == "__main__":
    unittest.main()
