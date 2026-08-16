import json
import unittest
from pathlib import Path

from tools.proof_graph_lab import (
    backward_compression_gain,
    canonical_motif_colors,
    conditional_residual_vector,
    heldout_transfer_gain,
    HypergraphRelaxation,
    lean_check_time_record,
    pareto_relation,
    ProofGraph,
    proof_structural_grade,
    ZDD,
    minimal_support_family,
    semantic_dag_metrics,
    validate_export,
)


def fixture_graph():
    nodes = [
        {
            "name": name,
            "scope": "project" if not name.startswith("Mathlib.") else "external",
            "status": "compiled",
            "namespace": name.rsplit(".", 1)[0],
            "module": name.rsplit(".", 1)[0],
            "source": name.rsplit(".", 1)[0].replace(".", "/") + ".lean",
            "kind": "theorem",
        }
        for name in ["P.left", "P.right", "P.root", "P.shared", "Mathlib.ext"]
    ]
    edges = [
        {"source": "P.left", "target": "P.shared", "kind": "value", "also_in_value": False, "target_scope": "project"},
        {"source": "P.right", "target": "P.shared", "kind": "type", "also_in_value": True, "target_scope": "project"},
        {"source": "P.root", "target": "Mathlib.ext", "kind": "type", "also_in_value": False, "target_scope": "external"},
        {"source": "P.root", "target": "P.left", "kind": "value", "also_in_value": False, "target_scope": "project"},
        {"source": "P.root", "target": "P.right", "kind": "value", "also_in_value": False, "target_scope": "project"},
    ]
    return {
        "schema_version": 1,
        "status_vocabulary": ["compiled", "prototype", "partial", "planned", "blocked"],
        "extraction": {
            "source": "compiled-environment",
            "dependency_semantics": "direct-constant-occurrence",
            "deterministic": True,
        },
        "counts": {"project_nodes": 4, "external_boundary_nodes": 1, "edges": 5, "module_imports": 0},
        "nodes": nodes,
        "edges": edges,
        "module_imports": [],
    }


class ProofGraphTests(unittest.TestCase):
    def test_export_contract_and_project_closure(self):
        raw = fixture_graph()
        validate_export(raw)
        graph = ProofGraph.from_json(raw)
        self.assertEqual(
            graph.project_closure("P.root"),
            frozenset({"P.root", "P.left", "P.right", "P.shared"}),
        )
        self.assertIn(("P.right", "P.shared", "type+value"), graph.project_edges)

    def test_type_plus_value_role_is_not_collapsed_to_type_only(self):
        both_raw = fixture_graph()
        both = ProofGraph.from_json(both_raw)
        type_only_raw = __import__("copy").deepcopy(both_raw)
        edge = next(
            row
            for row in type_only_raw["edges"]
            if row["source"] == "P.right" and row["target"] == "P.shared"
        )
        edge["also_in_value"] = False
        type_only = ProofGraph.from_json(type_only_raw)
        self.assertNotEqual(both.project_edges, type_only.project_edges)
        self.assertIn(("P.right", "P.shared", "type"), type_only.project_edges)

    def test_semantic_condensation_handles_cycles(self):
        vertices = frozenset({"a", "b", "c"})
        edges = (("a", "b", "value"), ("b", "a", "type"), ("b", "c", "value"))
        metrics = semantic_dag_metrics(vertices, edges)
        self.assertEqual(metrics["components"], 2)
        self.assertEqual(metrics["cyclic_components"], 1)
        self.assertEqual(metrics["depth"], 2)

    def test_zdd_round_trip_and_zero_suppression(self):
        family = (
            frozenset({"a", "c"}),
            frozenset({"b"}),
            frozenset(),
        )
        order = ["a", "b", "c"]
        zdd, root = ZDD.from_family(family, order)
        decoded = {
            frozenset(order[index] for index in support)
            for support in zdd.enumerate_indices(root)
        }
        self.assertEqual(decoded, set(family))
        self.assertEqual(zdd.family_count(root), len(family))
        self.assertTrue(all(row is None or row[2] != ZDD.ZERO for row in zdd.nodes))

    def test_minimal_support_family(self):
        family = minimal_support_family(
            [frozenset({"a"}), frozenset({"a", "b"}), frozenset({"c"})]
        )
        self.assertEqual(set(family), {frozenset({"a"}), frozenset({"c"})})

    def test_every_concrete_completion_maps_and_bounds_are_admissible(self):
        relaxation = HypergraphRelaxation(
            obligations={
                "o1": (frozenset({"a"}), frozenset({"shared", "x"})),
                "o2": (frozenset({"b"}), frozenset({"shared", "y"})),
                "o3": (frozenset({"z"}),),
            },
            weights={name: 1 for name in ["a", "b", "shared", "x", "y", "z"]},
        )
        completions = list(relaxation.concrete_completions())
        self.assertTrue(completions)
        for support, selection in completions:
            self.assertTrue(relaxation.maps_to_relaxed_solution(support, selection))
        optimum = relaxation.exact_optimum()
        single = relaxation.max_single_obligation_lower_bound()
        packed, _obligations = relaxation.disjoint_obligation_pack_lower_bound()
        self.assertLessEqual(single, optimum)
        self.assertLessEqual(packed, optimum)

    def test_no_negative_cost_or_reuse_credit(self):
        relaxation = HypergraphRelaxation(
            obligations={"o": (frozenset({"shared"}),)}, weights={"shared": 1}
        )
        self.assertEqual(relaxation.exact_optimum(), 1)
        self.assertEqual(relaxation.mip_contract()["objective"], "minimize nonnegative fixed vertex charges")

    def test_hypergraph_contract_rejects_unsafe_inputs(self):
        with self.assertRaisesRegex(ValueError, "nonnegative integer"):
            HypergraphRelaxation(
                obligations={"o": (frozenset({"a"}),)}, weights={"a": -1}
            )
        with self.assertRaisesRegex(ValueError, "no support alternatives"):
            HypergraphRelaxation(obligations={"o": ()}, weights={})
        with self.assertRaisesRegex(ValueError, "without fixed charges"):
            HypergraphRelaxation(
                obligations={"o": (frozenset({"missing"}),)}, weights={}
            )

    def test_conditional_residual_ignores_raw_node_names(self):
        frozen = {
            "lemma_motifs": ["motif-a"],
            "support_hyperedges": ["edge-a"],
            "obligation_types": ["measurability"],
            "composition_constraints": [],
        }
        candidate = {
            "lemma_motifs": ["motif-a", "motif-b"],
            "support_hyperedges": ["edge-a"],
            "obligation_types": ["measurability", "quotient-geometry"],
            "composition_constraints": ["shared-shift"],
        }
        vector = conditional_residual_vector(frozen, candidate)
        self.assertEqual(vector["lemma_motifs"]["residual_signature_count"], 1)
        self.assertEqual(vector["support_hyperedges"]["residual_signature_count"], 0)
        self.assertEqual(
            vector["lemma_motifs"]["irreducibility_status"],
            "not-established-by-residual-set-difference",
        )
        self.assertNotIn("new_nodes", vector)

    def test_canonical_motif_colors_ignore_declaration_names(self):
        raw = fixture_graph()
        graph = ProofGraph.from_json(raw)
        renamed = __import__("copy").deepcopy(raw)
        rename = {
            "P.root": "Q.r",
            "P.left": "Q.l",
            "P.right": "Q.x",
            "P.shared": "Q.s",
        }
        for node in renamed["nodes"]:
            node["name"] = rename.get(node["name"], node["name"])
        for edge in renamed["edges"]:
            edge["source"] = rename.get(edge["source"], edge["source"])
            edge["target"] = rename.get(edge["target"], edge["target"])
        renamed["nodes"].sort(
            key=lambda node: (0 if node["scope"] == "project" else 1, node["name"])
        )
        renamed["edges"].sort(key=lambda edge: (edge["source"], edge["target"], edge["kind"]))
        renamed_graph = ProofGraph.from_json(renamed)
        self.assertEqual(
            sorted(canonical_motif_colors(graph).values()),
            sorted(canonical_motif_colors(renamed_graph).values()),
        )

    def test_pareto_relation_is_non_scalar(self):
        before = {"lemmas": 4, "depth": 5, "reuse": 0.25}
        after = {"lemmas": 3, "depth": 5, "reuse": 0.5}
        self.assertEqual(
            pareto_relation(before, after, minimize=["lemmas", "depth"], maximize=["reuse"]),
            "after-dominates",
        )
        mixed = {"lemmas": 2, "depth": 7, "reuse": 0.5}
        self.assertEqual(
            pareto_relation(before, mixed, minimize=["lemmas", "depth"], maximize=["reuse"]),
            "incomparable",
        )

    def test_backward_and_heldout_vectors_keep_dimensions(self):
        backward = backward_compression_gain(
            {
                "union_fixed_charge": 10,
                "standalone_fixed_charge_sum": 15,
                "maximum_depth": 6,
                "shared_support": 3,
                "explanation_motifs": 5,
            },
            {
                "union_fixed_charge": 8,
                "standalone_fixed_charge_sum": 11,
                "maximum_depth": 4,
                "shared_support": 5,
                "explanation_motifs": 3,
            },
        )
        self.assertEqual(backward["union_fixed_charge_reduction"], 2)
        heldout = heldout_transfer_gain(
            {
                "new_declarations": 4,
                "dag_depth": 7,
                "proof_term_proxy": 20,
                "check_time_seconds": 3.0,
                "open_obligations": 2,
            },
            {
                "new_declarations": 2,
                "dag_depth": 5,
                "proof_term_proxy": 15,
                "check_time_seconds": 2.5,
                "open_obligations": 1,
            },
            unlocked_obligations=["o2"],
        )
        self.assertEqual(heldout["unlocked_obligations"], ["o2"])

    def test_check_time_keeps_local_protocol(self):
        measurements = {
            "protocol": {"repetitions": 1, "interpretation": "local only"},
            "benchmarks": {
                "route": {
                    "source": "Route.lean",
                    "seconds": 1.25,
                    "command": "lean Route.lean",
                }
            },
        }
        record = lean_check_time_record(measurements, "route")
        self.assertEqual(record["status"], "measured-local-wall-clock")
        self.assertEqual(record["seconds"], 1.25)
        self.assertEqual(record["interpretation"], "local only")
        self.assertIsNone(lean_check_time_record(measurements, "missing")["seconds"])

    def test_versioned_timing_records_match_cost_schema(self):
        root = Path(__file__).resolve().parents[1]
        schema = json.loads(
            (root / "research-wiki/proof-graph/proof_cost.schema.json").read_text(
                encoding="utf-8"
            )
        )
        report = json.loads(
            (root / "research-wiki/proof-graph/benchmark_report.json").read_text(
                encoding="utf-8"
            )
        )
        timing_schema = schema["properties"]["lean_check_time"]
        allowed_keys = set(timing_schema["properties"])
        allowed_statuses = set(timing_schema["properties"]["status"]["enum"])
        for benchmark in report["benchmarks"]:
            timing = benchmark["proof_cost_vector"]["lean_check_time"]
            self.assertLessEqual(set(timing), allowed_keys)
            self.assertIn(timing["status"], allowed_statuses)

    def test_versioned_graph_and_novelty_artifacts_are_cross_consistent(self):
        root = Path(__file__).resolve().parents[1]
        artifact_dir = root / "research-wiki/proof-graph"

        def read(name):
            return json.loads((artifact_dir / name).read_text(encoding="utf-8"))

        benchmark = read("benchmark_report.json")
        benchmark_config = read("benchmark_roots.json")
        candidate = read("cng_candidate_evaluation.json")
        candidate_config = read("cng_candidate_roots.json")
        novelty = read("novelty_audit.json")

        frozen_hash = benchmark["graph"]["sha256"].lower()
        self.assertEqual(novelty["freeze_library_at_t"]["proof_graph_sha256"].lower(), frozen_hash)
        self.assertEqual(candidate["graphs"]["frozen"]["sha256"].lower(), frozen_hash)
        benchmark_counts = benchmark["graph"]["counts"]
        self.assertEqual(candidate["graphs"]["frozen"]["counts"], benchmark_counts)
        for key in ("project_nodes", "external_boundary_nodes", "edges"):
            self.assertEqual(novelty["freeze_library_at_t"][key], benchmark_counts[key])

        self.assertEqual(
            benchmark["benchmark_contract"]["root_count"],
            len(benchmark_config["benchmarks"]),
        )
        self.assertEqual(
            novelty["cng_candidate"]["compiled_leaves"], candidate_config["roots"]
        )
        self.assertEqual(
            candidate["candidate_support"]["root_count"], len(candidate_config["roots"])
        )
        proxy = candidate["fixed_canonicalization_proxy"]
        novelty_proxy = novelty["novelty_vector"]["conditional_residual"]["result"]
        self.assertEqual(
            proxy["color_signatures_absent_from_frozen_library"],
            novelty_proxy["new_color_signatures"],
        )
        self.assertEqual(
            proxy["direct_support_signatures_absent_from_frozen_library"],
            novelty_proxy["new_direct_support_signatures"],
        )

    def test_neutral_grade_requires_transfer_for_reusable_abstraction(self):
        self.assertEqual(
            proof_structural_grade(
                target_is_new=True,
                has_residual_route=False,
                backward_gain=False,
                heldout_gain=False,
                cross_family_gain=False,
            ),
            "coverage extension",
        )
        self.assertEqual(
            proof_structural_grade(
                target_is_new=False,
                has_residual_route=True,
                backward_gain=True,
                heldout_gain=True,
                cross_family_gain=False,
            ),
            "reusable abstraction",
        )


if __name__ == "__main__":
    unittest.main()
