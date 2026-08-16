#!/usr/bin/env python3
"""Proof-graph benchmarking, ZDD support families, and safe hypergraph bounds.

The dependent Lean proof state is intentionally absent from this module.  A ZDD here represents
only a family of finite support sets over a fixed declaration universe.  The hypergraph/MIP layer is
a library-planning relaxation, not a Lean elaborator.
"""

from __future__ import annotations

import argparse
import hashlib
import itertools
import json
import math
import time
import tracemalloc
from collections import Counter, defaultdict, deque
from dataclasses import dataclass
from pathlib import Path
from typing import Any, Iterable, Mapping, Sequence


STATUS_VOCABULARY = ("compiled", "prototype", "partial", "planned", "blocked")


def _canonical_json_bytes(value: Any) -> bytes:
    return json.dumps(value, ensure_ascii=False, sort_keys=True, separators=(",", ":")).encode("utf-8")


def _sha256_json(value: Any) -> str:
    return hashlib.sha256(_canonical_json_bytes(value)).hexdigest()


def load_json(path: Path) -> Any:
    with path.open("r", encoding="utf-8") as stream:
        return json.load(stream)


def write_json(path: Path, value: Any) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    with path.open("w", encoding="utf-8", newline="\n") as stream:
        json.dump(value, stream, ensure_ascii=False, sort_keys=True, indent=2)
        stream.write("\n")


@dataclass(frozen=True)
class ProofGraph:
    raw: Mapping[str, Any]
    nodes: Mapping[str, Mapping[str, Any]]
    project_adjacency: Mapping[str, tuple[str, ...]]
    project_edges: tuple[tuple[str, str, str], ...]

    @classmethod
    def from_json(cls, raw: Mapping[str, Any]) -> "ProofGraph":
        validate_export(raw)
        nodes = {row["name"]: row for row in raw["nodes"]}
        adjacency: dict[str, set[str]] = defaultdict(set)
        edges: list[tuple[str, str, str]] = []
        for edge in raw["edges"]:
            if edge["target_scope"] != "project":
                continue
            source = edge["source"]
            target = edge["target"]
            role = (
                "type+value"
                if edge["kind"] == "type" and edge["also_in_value"]
                else edge["kind"]
            )
            adjacency[source].add(target)
            edges.append((source, target, role))
        frozen_adjacency = {
            source: tuple(sorted(targets)) for source, targets in adjacency.items()
        }
        return cls(
            raw=raw,
            nodes=nodes,
            project_adjacency=frozen_adjacency,
            project_edges=tuple(sorted(edges)),
        )

    def project_closure(self, root: str) -> frozenset[str]:
        node = self.nodes.get(root)
        if node is None:
            raise ValueError(f"benchmark root is absent from graph: {root}")
        if node["scope"] != "project":
            raise ValueError(f"benchmark root is not project-owned: {root}")
        seen: set[str] = set()
        pending = [root]
        while pending:
            current = pending.pop()
            if current in seen:
                continue
            seen.add(current)
            pending.extend(self.project_adjacency.get(current, ()))
        return frozenset(seen)

    def induced_edges(self, vertices: frozenset[str]) -> tuple[tuple[str, str, str], ...]:
        return tuple(
            edge for edge in self.project_edges if edge[0] in vertices and edge[1] in vertices
        )


def validate_export(raw: Mapping[str, Any]) -> None:
    if raw.get("schema_version") != 1:
        raise ValueError("unsupported proof-graph schema_version")
    extraction = raw.get("extraction", {})
    if extraction.get("source") != "compiled-environment":
        raise ValueError("graph is not marked as compiled-environment data")
    if extraction.get("dependency_semantics") != "direct-constant-occurrence":
        raise ValueError("graph dependency semantics are not direct constant occurrence")
    if extraction.get("deterministic") is not True:
        raise ValueError("graph is not marked deterministic")
    if tuple(raw.get("status_vocabulary", ())) != STATUS_VOCABULARY:
        raise ValueError("status vocabulary drift")

    nodes = raw.get("nodes")
    edges = raw.get("edges")
    imports = raw.get("module_imports")
    if not isinstance(nodes, list) or not isinstance(edges, list) or not isinstance(imports, list):
        raise ValueError("nodes, edges, and module_imports must be arrays")
    node_names = [node["name"] for node in nodes]
    if len(node_names) != len(set(node_names)):
        raise ValueError("duplicate node names")
    node_keys = [
        (0 if node["scope"] == "project" else 1, node["name"])
        for node in nodes
    ]
    if node_keys != sorted(node_keys):
        raise ValueError("nodes are not deterministically sorted by scope/name")
    for node in nodes:
        if node["scope"] not in {"project", "external"}:
            raise ValueError(f"unsupported node scope: {node['scope']}")
        if node.get("status") != "compiled":
            raise ValueError(f"environment node is not marked compiled: {node['name']}")
        for required in ("namespace", "module", "source", "kind"):
            if required not in node:
                raise ValueError(f"node is missing {required}: {node['name']}")
    project_names = {node["name"] for node in nodes if node["scope"] == "project"}
    all_names = set(node_names)
    edge_keys: list[tuple[str, str, str]] = []
    edge_pairs: set[tuple[str, str]] = set()
    for edge in edges:
        if edge["source"] not in project_names:
            raise ValueError(f"edge source is not a project node: {edge['source']}")
        if edge["target"] not in all_names:
            raise ValueError(f"edge target is absent: {edge['target']}")
        if edge["kind"] not in {"type", "value"}:
            raise ValueError(f"unsupported edge kind: {edge['kind']}")
        if edge["also_in_value"] and edge["kind"] != "type":
            raise ValueError("also_in_value is valid only on a type-precedence edge")
        target_scope = "project" if edge["target"] in project_names else "external"
        if edge["target_scope"] != target_scope:
            raise ValueError(f"edge target_scope mismatch: {edge['target']}")
        pair = (edge["source"], edge["target"])
        if pair in edge_pairs:
            raise ValueError(f"type/value precedence violated by duplicate pair: {pair}")
        edge_pairs.add(pair)
        edge_keys.append((edge["source"], edge["target"], edge["kind"]))
    if edge_keys != sorted(edge_keys):
        raise ValueError("edges are not deterministically sorted")

    import_keys = [
        (
            row["source"],
            row["target"],
            row["import_all"],
            row["exported"],
            row["meta"],
        )
        for row in imports
    ]
    if import_keys != sorted(import_keys):
        raise ValueError("module imports are not deterministically sorted")
    if len(import_keys) != len(set(import_keys)):
        raise ValueError("duplicate module import rows")

    counts = raw.get("counts", {})
    expected_counts = {
        "project_nodes": len(project_names),
        "external_boundary_nodes": len(all_names - project_names),
        "edges": len(edges),
        "module_imports": len(imports),
    }
    if counts != expected_counts:
        raise ValueError(f"count mismatch: expected {expected_counts}, got {counts}")


def strongly_connected_components(
    vertices: Iterable[str], edges: Iterable[tuple[str, str, str]]
) -> list[tuple[str, ...]]:
    """Iterative Kosaraju SCC decomposition with deterministic component contents."""

    ordered_vertices = sorted(set(vertices))
    adjacency: dict[str, list[str]] = {vertex: [] for vertex in ordered_vertices}
    reverse: dict[str, list[str]] = {vertex: [] for vertex in ordered_vertices}
    for source, target, _kind in edges:
        adjacency[source].append(target)
        reverse[target].append(source)
    for values in adjacency.values():
        values.sort()
    for values in reverse.values():
        values.sort()

    visited: set[str] = set()
    finish: list[str] = []
    for start in ordered_vertices:
        if start in visited:
            continue
        visited.add(start)
        stack: list[tuple[str, int]] = [(start, 0)]
        while stack:
            node, index = stack[-1]
            neighbours = adjacency[node]
            if index < len(neighbours):
                target = neighbours[index]
                stack[-1] = (node, index + 1)
                if target not in visited:
                    visited.add(target)
                    stack.append((target, 0))
            else:
                stack.pop()
                finish.append(node)

    assigned: set[str] = set()
    components: list[tuple[str, ...]] = []
    for start in reversed(finish):
        if start in assigned:
            continue
        component: list[str] = []
        pending = [start]
        assigned.add(start)
        while pending:
            node = pending.pop()
            component.append(node)
            for target in reverse[node]:
                if target not in assigned:
                    assigned.add(target)
                    pending.append(target)
        components.append(tuple(sorted(component)))
    return components


def semantic_dag_metrics(
    vertices: frozenset[str], edges: tuple[tuple[str, str, str], ...]
) -> dict[str, int]:
    components = strongly_connected_components(vertices, edges)
    component_of = {
        vertex: index for index, component in enumerate(components) for vertex in component
    }
    dag: dict[int, set[int]] = {index: set() for index in range(len(components))}
    indegree = [0] * len(components)
    self_loops = 0
    for source, target, _kind in edges:
        source_component = component_of[source]
        target_component = component_of[target]
        if source_component == target_component:
            if source == target:
                self_loops += 1
            continue
        if target_component not in dag[source_component]:
            dag[source_component].add(target_component)
            indegree[target_component] += 1

    queue = deque(index for index, value in enumerate(indegree) if value == 0)
    depth = [1] * len(components)
    visited_components = 0
    while queue:
        component = queue.popleft()
        visited_components += 1
        for target in sorted(dag[component]):
            depth[target] = max(depth[target], depth[component] + 1)
            indegree[target] -= 1
            if indegree[target] == 0:
                queue.append(target)
    if visited_components != len(components):
        raise AssertionError("SCC condensation must be acyclic")
    return {
        "raw_nodes": len(vertices),
        "raw_edges": len(edges),
        "components": len(components),
        "component_edges": sum(map(len, dag.values())),
        "cyclic_components": sum(len(component) > 1 for component in components) + self_loops,
        "depth": max(depth, default=0),
    }


def minimal_support_family(family: Iterable[frozenset[str]]) -> tuple[frozenset[str], ...]:
    unique = sorted(set(family), key=lambda support: (len(support), tuple(sorted(support))))
    minimal: list[frozenset[str]] = []
    for support in unique:
        if any(existing <= support for existing in minimal):
            continue
        minimal.append(support)
    return tuple(minimal)


class ZDD:
    """Tiny replaceable ZDD backend for fixed-universe finite support families."""

    ZERO = 0
    ONE = 1

    def __init__(self, variable_count: int) -> None:
        self.variable_count = variable_count
        self.nodes: list[tuple[int, int, int] | None] = [None, None]
        self.unique: dict[tuple[int, int, int], int] = {}

    def make(self, variable: int, low: int, high: int) -> int:
        if high == self.ZERO:
            return low
        key = (variable, low, high)
        existing = self.unique.get(key)
        if existing is not None:
            return existing
        node = len(self.nodes)
        self.nodes.append(key)
        self.unique[key] = node
        return node

    @classmethod
    def from_family(
        cls, family: Sequence[frozenset[str]], variable_order: Sequence[str]
    ) -> tuple["ZDD", int]:
        index = {variable: position for position, variable in enumerate(variable_order)}
        if len(index) != len(variable_order):
            raise ValueError("ZDD variable order contains duplicates")

        trie: list[dict[str, Any]] = [{"terminal": False, "children": {}}]
        for support in family:
            missing = support - index.keys()
            if missing:
                raise ValueError(f"support contains variables outside universe: {sorted(missing)[:3]}")
            current = 0
            for variable in sorted((index[name] for name in support)):
                child = trie[current]["children"].get(variable)
                if child is None:
                    child = len(trie)
                    trie[current]["children"][variable] = child
                    trie.append({"terminal": False, "children": {}})
                current = child
            trie[current]["terminal"] = True

        zdd = cls(len(variable_order))
        encoded = [cls.ZERO] * len(trie)
        for trie_node in range(len(trie) - 1, -1, -1):
            row = trie[trie_node]
            result = cls.ONE if row["terminal"] else cls.ZERO
            for variable, child in sorted(row["children"].items(), reverse=True):
                result = zdd.make(variable, result, encoded[child])
            encoded[trie_node] = result
        return zdd, encoded[0]

    def family_count(self, root: int) -> int:
        memo = {self.ZERO: 0, self.ONE: 1}
        pending = [(root, False)]
        while pending:
            node, expanded = pending.pop()
            if node in memo:
                continue
            row = self.nodes[node]
            assert row is not None
            _variable, low, high = row
            if expanded:
                memo[node] = memo[low] + memo[high]
            else:
                pending.append((node, True))
                if low not in memo:
                    pending.append((low, False))
                if high not in memo:
                    pending.append((high, False))
        return memo[root]

    def enumerate_indices(self, root: int) -> set[frozenset[int]]:
        result: set[frozenset[int]] = set()
        pending: list[tuple[int, tuple[int, ...]]] = [(root, ())]
        while pending:
            node, chosen = pending.pop()
            if node == self.ZERO:
                continue
            if node == self.ONE:
                result.add(frozenset(chosen))
                continue
            row = self.nodes[node]
            assert row is not None
            variable, low, high = row
            pending.append((low, chosen))
            pending.append((high, chosen + (variable,)))
        return result

    def serialized_proxy_bytes(self, root: int) -> int:
        rows = [
            {"id": node, "variable": row[0], "low": row[1], "high": row[2]}
            for node, row in enumerate(self.nodes)
            if row is not None
        ]
        return len(_canonical_json_bytes({"root": root, "nodes": rows}))


def zdd_experiments(family: Sequence[frozenset[str]]) -> dict[str, Any]:
    frequency = Counter(variable for support in family for variable in support)
    universe = sorted(frequency)
    first_seen = list(dict.fromkeys(variable for support in family for variable in sorted(support)))
    orders = {
        "lexical": universe,
        "frequency_desc": sorted(universe, key=lambda name: (-frequency[name], name)),
        "frequency_asc": sorted(universe, key=lambda name: (frequency[name], name)),
        "first_seen": first_seen,
    }
    explicit_rows = [sorted(support) for support in family]
    explicit_serialized_bytes = len(_canonical_json_bytes(explicit_rows))
    explicit_memberships = sum(map(len, family))
    rows: list[dict[str, Any]] = []
    for label, order in orders.items():
        tracemalloc.start()
        started = time.perf_counter()
        zdd, root = ZDD.from_family(family, order)
        elapsed = time.perf_counter() - started
        _current, peak = tracemalloc.get_traced_memory()
        tracemalloc.stop()
        family_count = zdd.family_count(root)
        if family_count != len(family):
            raise AssertionError(f"ZDD family-count mismatch for {label}")
        nonterminal_nodes = len(zdd.nodes) - 2
        rows.append(
            {
                "order": label,
                "nonterminal_nodes": nonterminal_nodes,
                "family_count": family_count,
                "build_seconds": elapsed,
                "tracemalloc_peak_bytes": peak,
                "serialized_proxy_bytes": zdd.serialized_proxy_bytes(root),
                "membership_to_node_ratio": (
                    explicit_memberships / nonterminal_nodes if nonterminal_nodes else None
                ),
            }
        )
    return {
        "status": "prototype",
        "semantics": "fixed-universe-minimal-support-family-only",
        "dependent_proof_state_inside_zdd": False,
        "explicit_set_baseline": {
            "family_count": len(family),
            "universe_size": len(universe),
            "membership_entries": explicit_memberships,
            "serialized_bytes": explicit_serialized_bytes,
        },
        "orders": rows,
    }


@dataclass(frozen=True)
class HypergraphRelaxation:
    obligations: Mapping[str, tuple[frozenset[str], ...]]
    weights: Mapping[str, int]

    def __post_init__(self) -> None:
        for vertex, weight in self.weights.items():
            if not isinstance(weight, int) or isinstance(weight, bool) or weight < 0:
                raise ValueError(f"vertex weight must be a nonnegative integer: {vertex}")
        for obligation, alternatives in self.obligations.items():
            if not alternatives:
                raise ValueError(f"obligation has no support alternatives: {obligation}")
            missing = sorted(
                vertex
                for alternative in alternatives
                for vertex in alternative
                if vertex not in self.weights
            )
            if missing:
                raise ValueError(
                    f"obligation {obligation} has vertices without fixed charges: {missing}"
                )

    def concrete_completions(self) -> Iterable[tuple[frozenset[str], dict[str, int]]]:
        labels = sorted(self.obligations)
        choices = [range(len(self.obligations[label])) for label in labels]
        for selected in itertools.product(*choices):
            union: set[str] = set()
            selection: dict[str, int] = {}
            for label, alternative in zip(labels, selected):
                selection[label] = alternative
                union.update(self.obligations[label][alternative])
            yield frozenset(union), selection

    def concrete_cost(self, support: frozenset[str]) -> int:
        return sum(self.weights[vertex] for vertex in support)

    def maps_to_relaxed_solution(
        self, support: frozenset[str], selection: Mapping[str, int]
    ) -> bool:
        """Check the canonical concrete-to-relaxed 0/1 mapping.

        Set x_v=1 exactly on the concrete union and y_(o,e)=1 on each selected alternative.
        The relaxation constraints are sum_e y_(o,e)>=1 and x_v>=y_(o,e) for v in e.
        """

        for obligation, alternatives in self.obligations.items():
            selected = selection.get(obligation)
            if selected is None or not 0 <= selected < len(alternatives):
                return False
            if not alternatives[selected] <= support:
                return False
        return True

    def exact_optimum(self) -> int:
        return min(self.concrete_cost(support) for support, _selection in self.concrete_completions())

    def max_single_obligation_lower_bound(self) -> int:
        """Admissible bound: max_o min_e cost(e).

        Every concrete completion selects an alternative for every obligation and its union contains
        that alternative.  Nonnegative vertex weights therefore make each per-obligation minimum a
        lower bound; taking their maximum preserves admissibility.
        """

        minima = []
        for alternatives in self.obligations.values():
            minima.append(min(self.concrete_cost(alternative) for alternative in alternatives))
        return max(minima, default=0)

    def disjoint_obligation_pack_lower_bound(self) -> tuple[int, tuple[str, ...]]:
        """Greedy admissible strengthening using obligations with disjoint alternative universes."""

        universes = {
            obligation: frozenset().union(*alternatives)
            for obligation, alternatives in self.obligations.items()
        }
        chosen: list[str] = []
        occupied: set[str] = set()
        bound = 0
        candidates = sorted(
            self.obligations,
            key=lambda obligation: (
                -min(self.concrete_cost(edge) for edge in self.obligations[obligation]),
                obligation,
            ),
        )
        for obligation in candidates:
            if occupied.isdisjoint(universes[obligation]):
                chosen.append(obligation)
                occupied.update(universes[obligation])
                bound += min(
                    self.concrete_cost(edge) for edge in self.obligations[obligation]
                )
        return bound, tuple(chosen)

    def mip_contract(self) -> dict[str, Any]:
        alternatives = sum(len(values) for values in self.obligations.values())
        incidences = sum(
            len(edge) for alternatives_ in self.obligations.values() for edge in alternatives_
        )
        return {
            "status": "prototype",
            "role": "library-planning-and-scheduling-only",
            "lean_elaborator": False,
            "binary_vertex_variables": len(self.weights),
            "binary_alternative_variables": alternatives,
            "obligation_cover_constraints": len(self.obligations),
            "alternative_vertex_link_constraints": incidences,
            "objective": "minimize nonnegative fixed vertex charges",
            "relaxation": "replace binary x/y domains by [0,1]",
        }


def pareto_relation(
    before: Mapping[str, float],
    after: Mapping[str, float],
    *,
    minimize: Sequence[str],
    maximize: Sequence[str],
) -> str:
    """Compare proof-cost vectors without scalarization."""

    keys = tuple(minimize) + tuple(maximize)
    missing = [key for key in keys if key not in before or key not in after]
    if missing:
        raise ValueError(f"Pareto comparison missing dimensions: {missing}")
    after_no_worse = all(after[key] <= before[key] for key in minimize) and all(
        after[key] >= before[key] for key in maximize
    )
    before_no_worse = all(before[key] <= after[key] for key in minimize) and all(
        before[key] >= after[key] for key in maximize
    )
    after_strict = any(after[key] < before[key] for key in minimize) or any(
        after[key] > before[key] for key in maximize
    )
    before_strict = any(before[key] < after[key] for key in minimize) or any(
        before[key] > after[key] for key in maximize
    )
    if after_no_worse and after_strict:
        return "after-dominates"
    if before_no_worse and before_strict:
        return "before-dominates"
    if after_no_worse and before_no_worse:
        return "equal"
    return "incomparable"


def conditional_residual_vector(
    frozen: Mapping[str, Iterable[str]], candidate: Mapping[str, Iterable[str]]
) -> dict[str, Any]:
    """Name-independent residual categories after conditioning on a frozen library.

    Callers supply canonical motif, hyperedge, obligation-type, and composition-constraint
    signatures.  Raw declaration names and raw new-node counts are intentionally not inputs.
    """

    dimensions = (
        "lemma_motifs",
        "support_hyperedges",
        "obligation_types",
        "composition_constraints",
    )
    residual: dict[str, Any] = {}
    for dimension in dimensions:
        frozen_values = set(frozen.get(dimension, ()))
        candidate_values = set(candidate.get(dimension, ()))
        new_values = sorted(candidate_values - frozen_values)
        residual[dimension] = {
            "residual_signature_count": len(new_values),
            "signature_digests": [hashlib.sha256(value.encode("utf-8")).hexdigest() for value in new_values],
            "irreducibility_status": "not-established-by-residual-set-difference",
        }
    return residual


def canonical_motif_colors(graph: ProofGraph, rounds: int = 2) -> dict[str, str]:
    """Name-independent finite-round colors for project declaration neighborhoods.

    This is a canonicalization proxy, not a claim that equal colors imply semantic equivalence or
    that a new color is irreducible mathematical structure.
    """

    project = sorted(name for name, node in graph.nodes.items() if node["scope"] == "project")
    outgoing: dict[str, list[tuple[str, str]]] = defaultdict(list)
    incoming: dict[str, list[tuple[str, str]]] = defaultdict(list)
    for source, target, kind in graph.project_edges:
        outgoing[source].append((kind, target))
        incoming[target].append((kind, source))
    colors = {
        name: _sha256_json({"scope": "project", "kind": graph.nodes[name].get("kind", "unknown")})
        for name in project
    }
    for _round in range(rounds):
        next_colors: dict[str, str] = {}
        for name in project:
            next_colors[name] = _sha256_json(
                {
                    "self": colors[name],
                    "out": sorted((kind, colors[target]) for kind, target in outgoing.get(name, ())),
                    "in": sorted((kind, colors[source]) for kind, source in incoming.get(name, ())),
                }
            )
        colors = next_colors
    return colors


def canonical_direct_support_signatures(
    graph: ProofGraph, colors: Mapping[str, str]
) -> dict[str, str]:
    """Canonicalize direct project support hyperedges without declaration names."""

    by_source: dict[str, list[tuple[str, str]]] = defaultdict(list)
    for source, target, kind in graph.project_edges:
        by_source[source].append((kind, colors[target]))
    return {
        name: _sha256_json(sorted(by_source.get(name, ())))
        for name, node in graph.nodes.items()
        if node["scope"] == "project"
    }


def candidate_audit_report(
    frozen: ProofGraph,
    candidate: ProofGraph,
    benchmark_config: Mapping[str, Any],
    candidate_config: Mapping[str, Any],
    frozen_path: Path,
    candidate_path: Path,
    candidate_rerun_path: Path | None = None,
) -> dict[str, Any]:
    """Compare a post-freeze candidate without treating declaration count as novelty."""

    frozen_project = {
        name for name, node in frozen.nodes.items() if node["scope"] == "project"
    }
    candidate_project = {
        name for name, node in candidate.nodes.items() if node["scope"] == "project"
    }
    added = frozenset(candidate_project - frozen_project)
    removed = frozenset(frozen_project - candidate_project)
    frozen_edges = set(frozen.project_edges)
    candidate_edges = set(candidate.project_edges)
    added_edges = sorted(candidate_edges - frozen_edges)
    removed_edges = sorted(frozen_edges - candidate_edges)

    rounds = int(candidate_config["canonicalization"]["rounds"])
    frozen_colors = canonical_motif_colors(frozen, rounds)
    candidate_colors = canonical_motif_colors(candidate, rounds)
    frozen_color_universe = set(frozen_colors.values())
    added_colors = {candidate_colors[name] for name in added}
    residual_colors = sorted(added_colors - frozen_color_universe)
    frozen_support_signatures = set(
        canonical_direct_support_signatures(frozen, frozen_colors).values()
    )
    candidate_support_signatures = canonical_direct_support_signatures(candidate, candidate_colors)
    added_support_signatures = {candidate_support_signatures[name] for name in added}
    residual_support_signatures = sorted(added_support_signatures - frozen_support_signatures)

    benchmark_rows: list[dict[str, Any]] = []
    candidate_closures: dict[str, frozenset[str]] = {}
    all_structural_support_unchanged = True
    for benchmark in benchmark_config["benchmarks"]:
        root = benchmark["root"]
        before = frozen.project_closure(root)
        after = candidate.project_closure(root)
        before_edges = frozen.induced_edges(before)
        after_edges = candidate.induced_edges(after)
        structural_support_unchanged = before == after and before_edges == after_edges
        all_structural_support_unchanged = (
            all_structural_support_unchanged and structural_support_unchanged
        )
        candidate_closures[benchmark["id"]] = after
        benchmark_rows.append(
            {
                "id": benchmark["id"],
                "root": root,
                "structural_support_unchanged": structural_support_unchanged,
                "before_support_digest": _sha256_json(sorted(before)),
                "after_support_digest": _sha256_json(sorted(after)),
                "before_semantic_dag": semantic_dag_metrics(before, before_edges),
                "after_semantic_dag": semantic_dag_metrics(after, after_edges),
                "candidate_declarations_in_after_support": len(after & added),
            }
        )

    roots = candidate_config["roots"]
    root_closures = {root: candidate.project_closure(root) for root in roots}
    support_union = frozenset().union(*root_closures.values())
    support_edges = candidate.induced_edges(support_union)
    existing_to_candidate = sorted(
        edge for edge in candidate.project_edges if edge[0] in frozen_project and edge[1] in added
    )
    heldout_id = candidate_config["heldout_benchmark_id"]
    heldout_support = candidate_closures[heldout_id]
    proof_proxy = sum(
        int(candidate.nodes[name].get("value_expr_objects", 0)) for name in support_union
    )

    candidate_hash = hashlib.sha256(candidate_path.read_bytes()).hexdigest()
    determinism = {"status": "not-supplied"}
    if candidate_rerun_path is not None:
        rerun_hash = hashlib.sha256(candidate_rerun_path.read_bytes()).hexdigest()
        byte_equal = (
            candidate_hash == rerun_hash
            and candidate_path.stat().st_size == candidate_rerun_path.stat().st_size
        )
        if not byte_equal:
            raise ValueError("candidate graph rerun is not byte-deterministic")
        determinism = {
            "status": "verified-by-independent-rerun",
            "rerun_sha256": rerun_hash,
            "byte_equal": True,
            "length_bytes": candidate_path.stat().st_size,
        }

    return {
        "schema_version": 1,
        "status": "prototype-observation",
        "claim_boundary": (
            "This report does not establish CNG proof-structural novelty. Canonical colors and "
            "support signatures are name-independent structural proxies, not irreducibility proofs."
        ),
        "graphs": {
            "frozen": {
                "sha256": hashlib.sha256(frozen_path.read_bytes()).hexdigest(),
                "counts": frozen.raw["counts"],
            },
            "candidate": {
                "sha256": candidate_hash,
                "counts": candidate.raw["counts"],
                "determinism": determinism,
            },
        },
        "raw_graph_delta_not_a_novelty_metric": {
            "added_project_declarations": len(added),
            "removed_project_declarations": len(removed),
            "added_project_edges": len(added_edges),
            "removed_project_edges": len(removed_edges),
            "added_declaration_digest": _sha256_json(sorted(added)),
            "added_edge_digest": _sha256_json(added_edges),
        },
        "fixed_canonicalization_proxy": {
            "version": candidate_config["canonicalization"]["version"],
            "rounds": rounds,
            "name_independent": True,
            "warning": candidate_config["canonicalization"]["warning"],
            "added_declaration_color_count": len(added_colors),
            "color_signatures_absent_from_frozen_library": len(residual_colors),
            "residual_color_digests": residual_colors,
            "added_direct_support_signature_count": len(added_support_signatures),
            "direct_support_signatures_absent_from_frozen_library": len(
                residual_support_signatures
            ),
            "residual_direct_support_digests": residual_support_signatures,
            "irreducible_structure_established": False,
        },
        "candidate_support": {
            "root_count": len(roots),
            "union_project_declarations": len(support_union),
            "new_project_declarations_in_union": len(support_union & added),
            "reused_frozen_declarations_in_union": len(support_union & frozen_project),
            "semantic_dag": semantic_dag_metrics(support_union, support_edges),
            "proof_term_object_proxy_sum": proof_proxy,
            "root_support_digests": {
                root: _sha256_json(sorted(closure)) for root, closure in sorted(root_closures.items())
            },
        },
        "existing_benchmark_stability": {
            "all_structural_support_unchanged": all_structural_support_unchanged,
            "benchmarks": benchmark_rows,
        },
        "novelty_vector_current_evidence": {
            "conditional_residual": {
                "status": "prototype-proxy-only",
                "result": "new canonical colors/support signatures observed; semantic irreducibility not established",
            },
            "backward_compression_gain": {
                "status": "not-demonstrated",
                "existing_to_candidate_dependency_edges": len(existing_to_candidate),
                "frozen_benchmark_structural_support_unchanged": (
                    all_structural_support_unchanged
                ),
            },
            "proof_cost_pareto_frontier_shift": {
                "status": "not-assessed-all-dimensions",
                "structural_support_relation": (
                    "equal" if all_structural_support_unchanged else "changed"
                ),
                "full_cost_vector_relation": "not-assessed",
                "unmeasured_dimensions": ["Lean check time", "open obligations"],
                "candidate_dominance_established": False,
            },
            "heldout_transfer_gain": {
                "status": "not-demonstrated",
                "heldout_benchmark_id": heldout_id,
                "candidate_declarations_in_heldout_support": len(heldout_support & added),
                "unlocked_obligations": [],
            },
            "target_novelty": {
                "status": "not-assessed",
                "separate_from_proof_novelty": True,
            },
        },
        "structural_discovery_established": False,
        "neutral_grade": None,
        "scope_boundary": candidate_config["scope_boundary"],
    }


def backward_compression_gain(
    before: Mapping[str, float], after: Mapping[str, float]
) -> dict[str, float]:
    """Positive values mean existing routes became smaller/shallower/more shared."""

    return {
        "union_fixed_charge_reduction": before["union_fixed_charge"] - after["union_fixed_charge"],
        "standalone_charge_reduction": before["standalone_fixed_charge_sum"]
        - after["standalone_fixed_charge_sum"],
        "maximum_depth_reduction": before["maximum_depth"] - after["maximum_depth"],
        "shared_support_gain": after["shared_support"] - before["shared_support"],
        "explanation_motif_reduction": before["explanation_motifs"] - after["explanation_motifs"],
    }


def heldout_transfer_gain(
    before: Mapping[str, float], after: Mapping[str, float], *, unlocked_obligations: Sequence[str]
) -> dict[str, Any]:
    """Report held-out changes dimension-by-dimension; do not collapse to one score."""

    return {
        "new_declaration_reduction": before["new_declarations"] - after["new_declarations"],
        "dag_depth_reduction": before["dag_depth"] - after["dag_depth"],
        "proof_term_proxy_reduction": before["proof_term_proxy"] - after["proof_term_proxy"],
        "check_time_reduction_seconds": before["check_time_seconds"] - after["check_time_seconds"],
        "open_obligation_reduction": before["open_obligations"] - after["open_obligations"],
        "unlocked_obligations": sorted(set(unlocked_obligations)),
    }


def proof_structural_grade(
    *,
    target_is_new: bool,
    has_residual_route: bool,
    backward_gain: bool,
    heldout_gain: bool,
    cross_family_gain: bool,
) -> str:
    """Neutral proposed labels; a human review is still required before publication."""

    if cross_family_gain and backward_gain and heldout_gain:
        return "cross-family conceptual compression"
    if backward_gain and heldout_gain:
        return "reusable abstraction"
    if has_residual_route:
        return "new proof route"
    if backward_gain:
        return "library consolidation"
    # A novel target may still have domain value even when it reuses known proof structure.
    _ = target_is_new
    return "coverage extension"


def lean_check_time_record(
    measurements: Mapping[str, Any] | None, benchmark_id: str
) -> dict[str, Any]:
    """Return an auditable local timing record without inventing missing data."""

    if not measurements:
        return {"status": "not-measured-by-exporter", "seconds": None}
    row = measurements.get("benchmarks", {}).get(benchmark_id)
    if not row:
        return {"status": "not-measured-for-benchmark", "seconds": None}
    return {
        "status": "measured-local-wall-clock",
        "seconds": float(row["seconds"]),
        "source": row["source"],
        "command": row["command"],
        "repetitions": int(measurements["protocol"]["repetitions"]),
        "interpretation": measurements["protocol"]["interpretation"],
    }


def benchmark_report(
    graph: ProofGraph,
    config: Mapping[str, Any],
    graph_path: Path,
    measurements: Mapping[str, Any] | None = None,
) -> dict[str, Any]:
    benchmark_rows = config.get("benchmarks", [])
    if not benchmark_rows:
        raise ValueError("benchmark config has no benchmarks")
    closures: dict[str, frozenset[str]] = {}
    per_benchmark: list[dict[str, Any]] = []
    for benchmark in benchmark_rows:
        label = benchmark["id"]
        root = benchmark["root"]
        closure = graph.project_closure(root)
        closures[label] = closure
        edges = graph.induced_edges(closure)
        proof_objects = sum(int(graph.nodes[name]["value_expr_objects"]) for name in closure)
        per_benchmark.append(
            {
                "id": label,
                "algorithm": benchmark["algorithm"],
                "root": root,
                "root_module": graph.nodes[root]["module"],
                "root_source": graph.nodes[root]["source"],
                "status": graph.nodes[root]["status"],
                "target_contract": benchmark["target_contract"],
                "project_support_digest": _sha256_json(sorted(closure)),
                "proof_cost_vector": {
                    "new_declaration_count": 0,
                    "reused_compiled_declaration_count": len(closure),
                    "shared_fixed_charge_policy": "charged-once-in-union",
                    "semantic_dag": semantic_dag_metrics(closure, edges),
                    "proof_term_object_proxy_sum": proof_objects,
                    "lean_check_time": lean_check_time_record(measurements, label),
                    "open_obligations": [],
                },
            }
        )

    occurrence = Counter(name for closure in closures.values() for name in closure)
    union = frozenset(occurrence)
    shared = frozenset(name for name, count in occurrence.items() if count >= 2)
    for row in per_benchmark:
        support = closures[row["id"]]
        reused = support & shared
        row["proof_cost_vector"]["reuse_coverage"] = {
            "shared_declarations": len(reused),
            "support_declarations": len(support),
            "ratio": len(reused) / len(support) if support else 0.0,
        }

    family = minimal_support_family(closures.values())
    weights = {vertex: 1 for vertex in union}
    relaxation = HypergraphRelaxation(
        obligations={label: (support,) for label, support in closures.items()},
        weights=weights,
    )
    for support, selection in relaxation.concrete_completions():
        if not relaxation.maps_to_relaxed_solution(support, selection):
            raise AssertionError("benchmark concrete completion did not map to relaxed solution")
    exact = relaxation.exact_optimum()
    single = relaxation.max_single_obligation_lower_bound()
    packed, packed_obligations = relaxation.disjoint_obligation_pack_lower_bound()
    if single > exact or packed > exact:
        raise AssertionError("admissible lower bound exceeded exact benchmark optimum")

    return {
        "schema_version": 1,
        "status": "prototype",
        "graph": {
            "path_hint": graph_path.name,
            "sha256": hashlib.sha256(graph_path.read_bytes()).hexdigest(),
            "counts": graph.raw["counts"],
            "extraction": graph.raw["extraction"],
        },
        "benchmark_contract": {
            "status": "compiled-roots-observed-by-prototype",
            "root_count": len(per_benchmark),
            "excluded_scope": config.get("excluded_scope", []),
            "mathematical_theorems_modified": False,
        },
        "measurement_contract": (
            {
                "status": measurements["status"],
                "protocol": measurements["protocol"],
                "environment": measurements["environment"],
            }
            if measurements
            else {"status": "not-supplied"}
        ),
        "benchmarks": per_benchmark,
        "shared_library": {
            "standalone_fixed_charge_sum": sum(len(support) for support in closures.values()),
            "union_fixed_charge": len(union),
            "shared_declaration_count": len(shared),
            "charge_policy": "each declaration has nonnegative fixed charge and is charged once in the union",
            "negative_reuse_reward": False,
        },
        "zdd": zdd_experiments(family),
        "hypergraph": {
            "status": "prototype",
            "concrete_completion_maps_to_relaxation": True,
            "unit_fixed_charge_exact_optimum": exact,
            "admissible_lower_bounds": {
                "max_single_obligation_min_bundle": single,
                "greedy_disjoint_obligation_pack": packed,
                "packed_obligations": list(packed_obligations),
            },
            "safe_pruning_contract": "call a bound safe only after establishing LB(s) <= OPT_remaining(s)",
            "safe_pruning_established_for_reported_bounds": True,
            "mip": relaxation.mip_contract(),
        },
        "limitations": [
            "Direct environment dependencies are not elaborator traces and do not unfold external declarations.",
            "Unit fixed charges are a benchmark prototype, not a universal scalar proof cost.",
            "ZDD nodes encode only fixed-universe support families; dependent proof states remain outside.",
            "MIP/LP objects plan library support and scheduling; they do not model Lean elaboration.",
        ],
    }


def _command_validate(args: argparse.Namespace) -> int:
    raw = load_json(args.graph)
    validate_export(raw)
    print(json.dumps({"ok": True, "counts": raw["counts"]}, sort_keys=True))
    return 0


def _command_benchmark(args: argparse.Namespace) -> int:
    graph_path = args.graph.resolve()
    graph = ProofGraph.from_json(load_json(graph_path))
    measurements = load_json(args.measurements) if args.measurements else None
    report = benchmark_report(graph, load_json(args.config), graph_path, measurements)
    write_json(args.output, report)
    print(json.dumps({"ok": True, "output": str(args.output), "status": report["status"]}, sort_keys=True))
    return 0


def _command_candidate_audit(args: argparse.Namespace) -> int:
    frozen_path = args.frozen.resolve()
    candidate_path = args.candidate.resolve()
    frozen = ProofGraph.from_json(load_json(frozen_path))
    candidate = ProofGraph.from_json(load_json(candidate_path))
    report = candidate_audit_report(
        frozen,
        candidate,
        load_json(args.benchmark_config),
        load_json(args.candidate_config),
        frozen_path,
        candidate_path,
        args.candidate_rerun.resolve() if args.candidate_rerun else None,
    )
    write_json(args.output, report)
    print(
        json.dumps(
            {
                "ok": True,
                "output": str(args.output),
                "structural_discovery_established": report["structural_discovery_established"],
            },
            sort_keys=True,
        )
    )
    return 0


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description=__doc__)
    subparsers = parser.add_subparsers(dest="command", required=True)
    validate = subparsers.add_parser("validate-export", help="validate an exported graph")
    validate.add_argument("--graph", type=Path, required=True)
    validate.set_defaults(handler=_command_validate)
    benchmark = subparsers.add_parser("benchmark", help="build benchmark/ZDD/hypergraph summary")
    benchmark.add_argument("--graph", type=Path, required=True)
    benchmark.add_argument("--config", type=Path, required=True)
    benchmark.add_argument("--output", type=Path, required=True)
    benchmark.add_argument(
        "--measurements",
        type=Path,
        help="optional local timing/environment observations",
    )
    benchmark.set_defaults(handler=_command_benchmark)
    candidate = subparsers.add_parser(
        "candidate-audit",
        help="compare a post-freeze candidate without treating raw nodes as novelty",
    )
    candidate.add_argument("--frozen", type=Path, required=True)
    candidate.add_argument("--candidate", type=Path, required=True)
    candidate.add_argument(
        "--candidate-rerun",
        type=Path,
        help="optional independently exported graph required to be byte-identical",
    )
    candidate.add_argument("--benchmark-config", type=Path, required=True)
    candidate.add_argument("--candidate-config", type=Path, required=True)
    candidate.add_argument("--output", type=Path, required=True)
    candidate.set_defaults(handler=_command_candidate_audit)
    return parser


def main(argv: Sequence[str] | None = None) -> int:
    args = build_parser().parse_args(argv)
    return args.handler(args)


if __name__ == "__main__":
    raise SystemExit(main())
