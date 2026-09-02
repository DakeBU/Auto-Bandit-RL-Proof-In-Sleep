#!/usr/bin/env python3
"""Build the post-hoc, frozen-target SGB interface-frontier trace."""

from __future__ import annotations

import argparse
import csv
import hashlib
import io
import json
import subprocess
import sys
from pathlib import Path


REPO_ROOT = Path(__file__).resolve().parents[1]
FREEZE_PATH = "research-wiki/papers/sgb-phase-transition-round13-freeze.json"
FRONTIER_PATH = "runs/active_frontier.json"
DECLARATION_INDEX_PATH = (
    "research-wiki/retrieval-index/local_lean_declarations.json"
)
THEOREM_AUDIT_PATH = "research-wiki/papers/theorem-audit-comparison.json"
DEFAULT_JSON = (
    REPO_ROOT / "research-wiki" / "papers" /
    "sgb-theorem2-interface-frontier-trace.json"
)
DEFAULT_CSV = (
    REPO_ROOT / "research-wiki" / "papers" /
    "sgb-theorem2-interface-frontier-trace.csv"
)
TARGET_KEYS = (
    "task_id",
    "source_sha256",
    "selection_timing",
    "replacement_policy",
    "core_target",
    "bounded_companion",
    "nonacceptable_substitutions",
)
EXPECTED_TARGET_SHA256 = (
    "26833d037458820fee79bf9be9e2d1f35771db06c69f80aeeeacc60070ac5c22"
)
EXPECTED_ROUTE = "SGB Theorem 2"
SGB_AUDIT_ID = "stochastic-gradient-bandit-source-frozen-audit"


def run_git(*args: str) -> str:
    result = subprocess.run(
        ["git", "-C", str(REPO_ROOT), *args],
        check=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        text=True,
        encoding="utf-8",
    )
    return result.stdout


def load_json_text(text: str):
    return json.loads(text.lstrip("\ufeff"))


def load_json(path: Path):
    return load_json_text(path.read_text(encoding="utf-8-sig"))


def git_history(path: str, ref: str) -> list[str]:
    return [
        item for item in run_git(
            "log", "--reverse", "--format=%H", ref, "--", path
        ).splitlines() if item
    ]


def git_json(commit: str, path: str):
    return load_json_text(run_git("show", "{}:{}".format(commit, path)))


def canonical_target_projection(document) -> bytes:
    projection = {key: document[key] for key in TARGET_KEYS}
    return json.dumps(
        projection,
        ensure_ascii=False,
        sort_keys=True,
        separators=(",", ":"),
    ).encode("utf-8")


def target_freeze_record(ref: str):
    revisions = git_history(FREEZE_PATH, ref)
    digests = []
    for commit in revisions:
        document = git_json(commit, FREEZE_PATH)
        digests.append(hashlib.sha256(
            canonical_target_projection(document)
        ).hexdigest())
    if not digests or len(set(digests)) != 1:
        raise ValueError("frozen target projection changed across revisions")
    if digests[0] != EXPECTED_TARGET_SHA256:
        raise ValueError("unexpected frozen target projection SHA-256")
    return {
        "projection_fields": list(TARGET_KEYS),
        "canonicalization": (
            "UTF-8 JSON with sorted keys, compact separators, and Unicode preserved"
        ),
        "sha256": digests[0],
        "history_revision_count": len(revisions),
        "excluded_mutable_fields": [
            "schema_version",
            "frozen_at_utc",
            "repository_base",
            "source_card",
            "source_title",
            "source_url",
            "status_at_freeze",
            "current_verified_status",
        ],
    }


def frontier_states(ref: str):
    states = []
    last_key = None
    for commit in git_history(FRONTIER_PATH, ref):
        document = git_json(commit, FRONTIER_PATH)
        if EXPECTED_ROUTE not in document.get("root_objective", ""):
            continue
        leaf = document["current_leaf"]
        verifier = document.get("last_accepted_verifier", {})
        key = (
            leaf.get("id"),
            leaf.get("status"),
            verifier.get("lean"),
        )
        if key == last_key:
            continue
        states.append({
            "ordinal": len(states) + 1,
            "git_commit": commit,
            "updated_at": document.get("updated_at"),
            "next_interface": leaf.get("id"),
            "next_interface_status": leaf.get("status"),
            "next_interface_statement_hash": leaf.get("statement_hash"),
            "source_status": leaf.get("source_status"),
            "dependencies": leaf.get("dependencies", []),
            "last_accepted_declaration": verifier.get("lean"),
            "last_accepted_run_id": verifier.get("run_id"),
        })
        last_key = key
    if len(states) < 2:
        raise ValueError("fewer than two SGB frontier states were found")
    return states


def indexed_declarations():
    document = load_json(REPO_ROOT / DECLARATION_INDEX_PATH)
    return {
        row["full_name"]: row
        for row in document["declarations"]
        if row.get("full_name")
    }


def statement_fences():
    rows = {}
    fence_root = REPO_ROOT / "runs" / "statement-fences"
    for path in sorted(fence_root.glob("*.json")):
        document = load_json(path)
        declaration = document.get("declaration")
        if declaration:
            rows[declaration] = {
                "path": path.relative_to(REPO_ROOT).as_posix(),
                "statement_hash": document.get("statement_hash"),
            }
    return rows


def closure_declaration(previous, current):
    accepted = current.get("last_accepted_declaration")
    if accepted and accepted != previous.get("last_accepted_declaration"):
        return accepted
    for dependency in current.get("dependencies", []):
        if dependency.get("status") in ("compiled", "accepted"):
            return dependency.get("name")
    raise ValueError(
        "frontier transition has no named compiled declaration: {}".format(
            current.get("next_interface")
        )
    )


def endpoint_verified():
    document = load_json(REPO_ROOT / THEOREM_AUDIT_PATH)
    rows = document.get("rows") or document.get("audits") or []
    for row in rows:
        if row.get("id") == SGB_AUDIT_ID:
            value = row.get("theorem_two_endpoint_verified")
            if type(value) is not bool:
                raise ValueError("Theorem-2 endpoint status is not boolean")
            return value
    raise ValueError("SGB theorem-audit row is missing")


def build_trace(ref: str = "HEAD"):
    states = frontier_states(ref)
    declarations = indexed_declarations()
    fences = statement_fences()
    transitions = []
    for previous, current in zip(states, states[1:]):
        declaration = closure_declaration(previous, current)
        indexed = declarations.get(declaration)
        if indexed is None:
            raise ValueError(
                "closure declaration is absent from the Lean index: " + declaration
            )
        fence = fences.get(declaration)
        transitions.append({
            "ordinal": len(transitions) + 1,
            "git_commit": current["git_commit"],
            "closed_interface": previous["next_interface"],
            "closed_target_statement_hash": (
                previous["next_interface_statement_hash"]
            ),
            "compiled_declaration": declaration,
            "compiled_declaration_file": indexed.get("file"),
            "compiled_declaration_line": indexed.get("line"),
            "statement_fence": fence,
            "next_interface": current["next_interface"],
        })
    terminal = endpoint_verified()
    if terminal:
        raise ValueError("trace boundary changed: Theorem 2 is now verified")
    return {
        "schema_version": 1,
        "record_id": "sgb-theorem2-frozen-frontier-trace-v1",
        "evidence_type": (
            "post-hoc-machine-auditable-single-route-interface-progress"
        ),
        "route": "source-frozen K=2 stochastic-gradient-bandit Theorem 2",
        "target_freeze": target_freeze_record(ref),
        "frontier_summary": {
            "state_count": len(states),
            "dependency_ordered_closure_count": len(transitions),
            "initial_interface": states[0]["next_interface"],
            "current_interface": states[-1]["next_interface"],
            "theorem_two_endpoint_verified": terminal,
            "statement_fence_count": sum(
                row["statement_fence"] is not None for row in transitions
            ),
        },
        "states": states,
        "transitions": transitions,
        "nonclaims": [
            "This is one post-hoc longitudinal route trace, not a benchmark.",
            "It does not establish harness superiority, proof-search speedup, or a causal effect.",
            "A compiled dependency closure is not the frozen Theorem-2 terminal.",
            "The initial native-prefix closure has declaration-index and typed-canary evidence but no separate statement-fence JSON.",
        ],
    }


def json_bytes(trace) -> bytes:
    return (
        json.dumps(trace, ensure_ascii=False, indent=2, sort_keys=True) + "\n"
    ).encode("utf-8")


def csv_bytes(trace) -> bytes:
    output = io.StringIO(newline="")
    fields = (
        "ordinal",
        "git_commit",
        "closed_interface",
        "compiled_declaration",
        "statement_fence_status",
        "next_interface",
    )
    writer = csv.DictWriter(output, fieldnames=fields, lineterminator="\n")
    writer.writeheader()
    for row in trace["transitions"]:
        writer.writerow({
            "ordinal": row["ordinal"],
            "git_commit": row["git_commit"],
            "closed_interface": row["closed_interface"],
            "compiled_declaration": row["compiled_declaration"],
            "statement_fence_status": (
                "present" if row["statement_fence"] else "not-separately-recorded"
            ),
            "next_interface": row["next_interface"],
        })
    return output.getvalue().encode("utf-8")


def compare_or_write(path: Path, data: bytes, check: bool):
    if check:
        if not path.is_file() or path.read_bytes() != data:
            raise ValueError("stale interface-frontier trace: " + str(path))
        return
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_bytes(data)


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--ref", default="HEAD")
    parser.add_argument("--output-json", type=Path, default=DEFAULT_JSON)
    parser.add_argument("--output-csv", type=Path, default=DEFAULT_CSV)
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args(argv)
    trace = build_trace(args.ref)
    compare_or_write(args.output_json, json_bytes(trace), args.check)
    compare_or_write(args.output_csv, csv_bytes(trace), args.check)
    print(json.dumps({
        "target_sha256": trace["target_freeze"]["sha256"],
        **trace["frontier_summary"],
        "mode": "check" if args.check else "write",
    }, sort_keys=True))
    return 0


if __name__ == "__main__":
    sys.exit(main())
