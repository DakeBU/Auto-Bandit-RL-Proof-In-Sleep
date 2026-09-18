#!/usr/bin/env python3
"""Diff-aware ABRL contributor-contract gate.

This checker intentionally uses only the Python standard library. It does not
certify the mathematics; it fails closed when a substantive repository delta is
not bound to a source/reuse/reader/semantic/graph/progress integration manifest.
"""

from __future__ import annotations

import argparse
import json
import os
import subprocess
import sys
from pathlib import Path
from typing import Any

ROOT = Path(__file__).resolve().parents[1]
CONTRACT_DIR = ROOT / "research-wiki" / "contribution-contracts"

PRODUCTION_PREFIXES = (
    "BanditRLProof/",
    "website/content/",
    "website/scripts/",
    "website/static/",
    "website/public-repo/banditrlwiki/",
    "website/public-repo/lean-graph/",
    "website/public-repo/data/",
    "research-wiki/papers/",
    "research-wiki/open-problems/",
    "research-wiki/theory-tree/",
    "research-wiki/proof-graph/",
)
PRODUCTION_EXACT = {
    "BanditRLProof.lean",
    "website/BOOKS.md",
    "AGENTS.md",
    "CONTRIBUTING.md",
    ".agents/prompts/collaborator-contribution.md",
    ".agents/skills/bandit-semantic-roundtrip/SKILL.md",
    ".agents/skills/bandit-substantive-advance/SKILL.md",
    "docs/contribution-contract.schema.json",
    "docs/contributor-codex-contract.md",
    "docs/theorem-publication-protocol.md",
    "tools/check_contributor_contract.py",
    "tools/test_contributor_contract.py",
    ".github/CODEOWNERS",
    ".github/pull_request_template.md",
    ".github/ISSUE_TEMPLATE/lemma-proposal.yml",
    ".github/workflows/contributor-contract.yml",
    ".github/workflows/documentation.yml",
    "website/README.md",
    "website/public-repo/.github/ISSUE_TEMPLATE/lemma-proposal.yml",
    "research-wiki/contribution-contracts/README.md",
}
CONTRACT_PREFIX = "research-wiki/contribution-contracts/"

TOP_REQUIRED = {
    "schema_version",
    "id",
    "route",
    "frontier_cell",
    "source_facing",
    "source",
    "target",
    "affected_files",
    "declarations",
    "reuse_plan",
    "reader_contract",
    "semantic_roundtrip",
    "graph_contribution",
    "progress_updates",
    "truth_boundary",
    "verification",
    "contributor",
}
REUSE_REQUIRED = {
    "classification",
    "decision",
    "searched_existing",
    "reused_declarations",
    "new_shared_declarations",
    "known_consumers",
    "planned_consumers",
    "no_duplicate_wrapper",
    "decision_reason",
}
READER_REQUIRED = {
    "source_anchor_visible",
    "natural_language_formula_proof",
    "hidden_assumptions_visible",
    "source_vs_lean_delta_visible",
    "lean_folded",
    "dependencies_visible",
    "remaining_boundary_visible",
}
SEMANTIC_REQUIRED = {
    "required",
    "status",
    "formalizer",
    "blind_decoder",
    "source_reviewer",
    "verdict",
    "remaining_semantic_delta",
}
GRAPH_REQUIRED = {
    "lean_graph",
    "overview_graph",
    "functor_hypergraph",
    "functor_reason",
    "focus_targets",
    "visual_review",
    "edge_semantics",
}
PROGRESS_REQUIRED = {
    "teaching_route",
    "banditrlwiki",
    "results_ledger",
    "roadmap",
    "website_surfaces",
}
VERIFY_REQUIRED = {
    "focused_checks",
    "bandit_check",
    "site_build",
    "site_check",
    "independent_review",
}

LEAN_STATES = {"new-node", "reuse-only", "integration-node", "no-change-with-reason"}
OVERVIEW_STATES = {"updated", "no-change-with-reason"}
FUNCTOR_STATES = {"none-found-with-reason", "candidate-published", "stabilized"}
SEMANTIC_STATES = {
    "not-required",
    "planned",
    "blind-reconstructed",
    "source-reviewed",
    "accepted",
    "rejected",
}
REUSE_CLASS = {"reuse", "adapt", "missing", "out_of_scope"}
REUSE_DECISION = {
    "reuse_existing",
    "adapt_existing",
    "new_route_local",
    "new_shared",
    "out_of_scope",
}


def run_git(*args: str) -> str:
    proc = subprocess.run(
        ["git", *args],
        cwd=ROOT,
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
    )
    if proc.returncode:
        raise RuntimeError(proc.stderr.strip() or f"git {' '.join(args)} failed")
    return proc.stdout


def diff_entries(base: str) -> list[tuple[str, str]]:
    raw = run_git("diff", "--name-status", f"{base}...HEAD")
    entries: list[tuple[str, str]] = []
    for line in raw.splitlines():
        if not line.strip():
            continue
        parts = line.split("\t")
        status = parts[0]
        # Renames/copies report old and new path; cover the destination.
        path = parts[-1]
        entries.append((status, path))
    return entries


def is_production(path: str) -> bool:
    if path.startswith(CONTRACT_PREFIX):
        return False
    return path in PRODUCTION_EXACT or any(path.startswith(prefix) for prefix in PRODUCTION_PREFIXES)


def changed_contract_paths(entries: list[tuple[str, str]]) -> list[str]:
    return [
        path
        for status, path in entries
        if status != "D"
        and path.startswith(CONTRACT_PREFIX)
        and path.endswith(".json")
        and not path.endswith("schema.json")
    ]


def require_keys(obj: Any, keys: set[str], where: str, errors: list[str]) -> None:
    if not isinstance(obj, dict):
        errors.append(f"{where}: expected object")
        return
    missing = sorted(keys - set(obj))
    if missing:
        errors.append(f"{where}: missing keys {', '.join(missing)}")


def nonempty_string(value: Any) -> bool:
    return isinstance(value, str) and bool(value.strip())


def string_list(value: Any) -> bool:
    return isinstance(value, list) and all(isinstance(item, str) for item in value)


def validate_contract(path: Path) -> tuple[dict[str, Any] | None, list[str]]:
    errors: list[str] = []
    try:
        data = json.loads(path.read_text(encoding="utf-8"))
    except Exception as exc:
        return None, [f"{path.relative_to(ROOT)}: invalid JSON: {exc}"]

    require_keys(data, TOP_REQUIRED, str(path.relative_to(ROOT)), errors)
    if errors:
        return data, errors

    if data.get("schema_version") != "2.0":
        errors.append(f"{path.relative_to(ROOT)}: schema_version must be 2.0")
    for key in ("id", "route", "frontier_cell", "target", "truth_boundary"):
        if not nonempty_string(data.get(key)):
            errors.append(f"{path.relative_to(ROOT)}: {key} must be non-empty")
    if not isinstance(data.get("source_facing"), bool):
        errors.append(f"{path.relative_to(ROOT)}: source_facing must be boolean")
    if not string_list(data.get("affected_files")) or not data["affected_files"]:
        errors.append(f"{path.relative_to(ROOT)}: affected_files must be a non-empty string list")
    if not string_list(data.get("declarations")):
        errors.append(f"{path.relative_to(ROOT)}: declarations must be a string list")

    source = data.get("source")
    require_keys(source, {"kind", "title", "version", "anchor", "url"}, f"{path}:source", errors)
    if isinstance(source, dict):
        for key in ("kind", "title", "version", "anchor"):
            if not nonempty_string(source.get(key)):
                errors.append(f"{path.relative_to(ROOT)}: source.{key} must be non-empty")

    reuse = data.get("reuse_plan")
    require_keys(reuse, REUSE_REQUIRED, f"{path}:reuse_plan", errors)
    if isinstance(reuse, dict):
        if reuse.get("classification") not in REUSE_CLASS:
            errors.append(f"{path.relative_to(ROOT)}: invalid reuse_plan.classification")
        if reuse.get("decision") not in REUSE_DECISION:
            errors.append(f"{path.relative_to(ROOT)}: invalid reuse_plan.decision")
        for key in (
            "searched_existing",
            "reused_declarations",
            "new_shared_declarations",
            "known_consumers",
            "planned_consumers",
        ):
            if not string_list(reuse.get(key)):
                errors.append(f"{path.relative_to(ROOT)}: reuse_plan.{key} must be a string list")
        if reuse.get("no_duplicate_wrapper") is not True:
            errors.append(f"{path.relative_to(ROOT)}: no_duplicate_wrapper must be true")
        if not nonempty_string(reuse.get("decision_reason")):
            errors.append(f"{path.relative_to(ROOT)}: decision_reason must be non-empty")
        if reuse.get("decision") == "new_shared":
            consumers = list(reuse.get("known_consumers") or []) + list(reuse.get("planned_consumers") or [])
            if len(set(consumers)) < 2:
                errors.append(
                    f"{path.relative_to(ROOT)}: new_shared requires at least two named consumers"
                )

    reader = data.get("reader_contract")
    require_keys(reader, READER_REQUIRED, f"{path}:reader_contract", errors)
    if isinstance(reader, dict) and data.get("source_facing"):
        false_fields = [key for key in READER_REQUIRED if reader.get(key) is not True]
        if false_fields:
            errors.append(
                f"{path.relative_to(ROOT)}: source-facing reader contract incomplete: "
                + ", ".join(sorted(false_fields))
            )

    semantic = data.get("semantic_roundtrip")
    require_keys(semantic, SEMANTIC_REQUIRED, f"{path}:semantic_roundtrip", errors)
    if isinstance(semantic, dict):
        if semantic.get("status") not in SEMANTIC_STATES:
            errors.append(f"{path.relative_to(ROOT)}: invalid semantic_roundtrip.status")
        if data.get("source_facing"):
            if semantic.get("required") is not True:
                errors.append(f"{path.relative_to(ROOT)}: source-facing contribution requires semantic audit")
            if semantic.get("status") != "accepted":
                errors.append(
                    f"{path.relative_to(ROOT)}: source-facing contribution must reach semantic status accepted"
                )
            for key in ("formalizer", "blind_decoder", "source_reviewer", "verdict"):
                if not nonempty_string(semantic.get(key)):
                    errors.append(f"{path.relative_to(ROOT)}: semantic_roundtrip.{key} must be non-empty")
            actors = {
                semantic.get("formalizer"),
                semantic.get("blind_decoder"),
                semantic.get("source_reviewer"),
            }
            if len(actors) != 3:
                errors.append(f"{path.relative_to(ROOT)}: semantic audit roles must be distinct")
        elif semantic.get("required") is False and semantic.get("status") != "not-required":
            errors.append(
                f"{path.relative_to(ROOT)}: non-required semantic audit must use status not-required"
            )

    graph = data.get("graph_contribution")
    require_keys(graph, GRAPH_REQUIRED, f"{path}:graph_contribution", errors)
    if isinstance(graph, dict):
        if graph.get("lean_graph") not in LEAN_STATES:
            errors.append(f"{path.relative_to(ROOT)}: invalid graph_contribution.lean_graph")
        if graph.get("overview_graph") not in OVERVIEW_STATES:
            errors.append(f"{path.relative_to(ROOT)}: invalid graph_contribution.overview_graph")
        if graph.get("functor_hypergraph") not in FUNCTOR_STATES:
            errors.append(f"{path.relative_to(ROOT)}: invalid graph_contribution.functor_hypergraph")
        if graph.get("edge_semantics") != "formal-solid; overlays-dashed":
            errors.append(f"{path.relative_to(ROOT)}: edge_semantics must preserve formal/overlay distinction")
        if not nonempty_string(graph.get("functor_reason")):
            errors.append(f"{path.relative_to(ROOT)}: functor_reason must be non-empty")
        if not string_list(graph.get("focus_targets")):
            errors.append(f"{path.relative_to(ROOT)}: focus_targets must be a string list")
        if not nonempty_string(graph.get("visual_review")):
            errors.append(f"{path.relative_to(ROOT)}: visual_review must be non-empty")

    progress = data.get("progress_updates")
    require_keys(progress, PROGRESS_REQUIRED, f"{path}:progress_updates", errors)
    if isinstance(progress, dict):
        for key in ("teaching_route", "banditrlwiki", "results_ledger", "roadmap"):
            if not nonempty_string(progress.get(key)):
                errors.append(f"{path.relative_to(ROOT)}: progress_updates.{key} must be non-empty")
        if not string_list(progress.get("website_surfaces")) or not progress["website_surfaces"]:
            errors.append(f"{path.relative_to(ROOT)}: website_surfaces must be non-empty")

    verification = data.get("verification")
    require_keys(verification, VERIFY_REQUIRED, f"{path}:verification", errors)
    if isinstance(verification, dict):
        if not string_list(verification.get("focused_checks")):
            errors.append(f"{path.relative_to(ROOT)}: focused_checks must be a string list")
        for key in ("bandit_check", "site_build", "site_check", "independent_review"):
            if not nonempty_string(verification.get(key)):
                errors.append(f"{path.relative_to(ROOT)}: verification.{key} must be non-empty")

    contributor = data.get("contributor")
    require_keys(contributor, {"name", "role"}, f"{path}:contributor", errors)
    if isinstance(contributor, dict):
        if not nonempty_string(contributor.get("name")) or not nonempty_string(contributor.get("role")):
            errors.append(f"{path.relative_to(ROOT)}: contributor name/role must be non-empty")

    return data, errors


def resolve_base(args: argparse.Namespace) -> str:
    if args.base:
        return args.base
    if args.ci:
        base = os.environ.get("CONTRIBUTOR_BASE", "").strip()
        if not base or set(base) == {"0"}:
            raise RuntimeError("CONTRIBUTOR_BASE is missing/zero; contributor gate fails closed")
        return base
    raise RuntimeError("pass --base BASE_COMMIT or --ci")


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--base", help="Git base commit/ref for the diff-aware contract check")
    parser.add_argument("--ci", action="store_true", help="read base from CONTRIBUTOR_BASE")
    args = parser.parse_args()

    try:
        base = resolve_base(args)
        # Verify that the base exists before interpreting an empty diff.
        run_git("rev-parse", "--verify", f"{base}^{{commit}}")
        entries = diff_entries(base)
    except Exception as exc:
        print(f"CONTRIBUTOR CONTRACT FAILED: {exc}", file=sys.stderr)
        return 2

    production = sorted({path for _status, path in entries if is_production(path)})
    contracts = changed_contract_paths(entries)

    print(f"contributor base: {base}")
    print(f"changed paths: {len(entries)}")
    print(f"affected production paths: {len(production)}")
    print(f"changed contribution contracts: {len(contracts)}")

    if not production:
        print("Contributor contract: N/A (no affected production/publication surfaces).")
        return 0
    if not contracts:
        print("CONTRIBUTOR CONTRACT FAILED", file=sys.stderr)
        print(
            "Substantive production/publication changes require a changed "
            "research-wiki/contribution-contracts/*.json manifest.",
            file=sys.stderr,
        )
        for path in production:
            print(f" - uncovered: {path}", file=sys.stderr)
        return 1

    errors: list[str] = []
    covered: set[str] = set()
    ids: set[str] = set()
    for rel in contracts:
        path = ROOT / rel
        data, contract_errors = validate_contract(path)
        errors.extend(contract_errors)
        if not data:
            continue
        cid = data.get("id")
        if cid in ids:
            errors.append(f"{rel}: duplicate contribution id {cid}")
        ids.add(cid)
        covered.update(data.get("affected_files") or [])

    uncovered = [path for path in production if path not in covered]
    if uncovered:
        errors.append(
            "production paths missing from all changed contribution manifests: "
            + ", ".join(uncovered)
        )

    if errors:
        print("CONTRIBUTOR CONTRACT FAILED", file=sys.stderr)
        for error in errors:
            print(f" - {error}", file=sys.stderr)
        return 1

    print("Contributor contract passed.")
    for path in production:
        print(f" - covered: {path}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
