"""Reproduce descriptive extended-topic evidence; never labels it a controlled run.

Usage: python tools/extended_topics_evidence.py --graph PATH --output PATH
This tool builds the root and runs the existing exporter. It requires a clean
tracked checkout and verifies that each reused project's module is unchanged
from the frozen base. It reports direct references, not causal productivity.
"""
from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
import subprocess

BASE = "eedcda1db4d84f6bd69ec6ee50e174f6cf4056ac"
ROOT = Path(__file__).resolve().parents[1]
PREFIX = "BanditRLProof.HeavyTail."


def git(*args: str) -> str:
    return subprocess.check_output(["git", "-C", str(ROOT), *args], text=True).strip()


def analyze(graph: dict, commit: str) -> dict:
    if graph.get("extraction", {}).get("source") != "compiled-environment":
        raise ValueError("a compiled-environment export is required")
    nodes = {n["name"]: n for n in graph["nodes"]}
    new = {n for n in nodes if n.startswith(PREFIX)}
    if not new:
        raise ValueError("graph does not contain the new declarations")
    edges = [e for e in graph["edges"] if e["source"] in new]
    reused = []
    checked = set()
    for e in edges:
        if e["target_scope"] != "project" or e["target"] in new:
            continue
        path = nodes[e["target"]]["source"]["file"]
        if path not in checked:
            old = git("rev-parse", f"{BASE}:{path}")
            current = git("rev-parse", f"{commit}:{path}")
            if old != current:
                raise ValueError(f"claimed frozen-base module changed: {path}")
            checked.add(path)
        reused.append(e)
    return {
        "schema_version": 1,
        "kind": "descriptive_development_case",
        "base_commit": BASE,
        "source_commit": commit,
        "controlled_runs": [],
        "controlled_effect_estimate": None,
        "observable_tokens": None,
        "endpoint_complete": False,
        "mandatory_open_obligations": [
            "two-sided bias-plus-tail tuning at source thresholds",
            "measurable causal robust-UCB history and policy",
            "adaptive fixed-count tail union with actual estimator",
            "selection-count and expected-regret assembly",
            "independent semantic review",
        ],
        "new_declarations": sorted(new),
        "direct_frozen_library_references": reused,
        "direct_edges": edges,
        "semantics": "type and value constant occurrences, not teaching edges or utility scores",
    }


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--graph", required=True, type=Path)
    parser.add_argument("--output", required=True, type=Path)
    args = parser.parse_args()
    head = git("rev-parse", "HEAD")
    if git("status", "--porcelain", "--untracked-files=no"):
        raise SystemExit("commit tracked edits before generating evidence")
    untracked = git("ls-files", "--others", "--exclude-standard", "BanditRLProof", "Tests")
    if untracked:
        raise SystemExit("commit new Lean sources before generating evidence")
    subprocess.run(["lake", "build", "BanditRLProof"], cwd=ROOT, check=True)
    args.graph = args.graph.resolve()
    args.graph.parent.mkdir(parents=True, exist_ok=True)
    subprocess.run(["lake", "env", "lean", "--run", "tools/ProofGraphExport.lean",
                    "--compact", str(args.graph)], cwd=ROOT, check=True)
    if git("rev-parse", "HEAD") != head or git("status", "--porcelain", "--untracked-files=no"):
        raise SystemExit("source changed during export")
    raw = args.graph.read_bytes()
    report = analyze(json.loads(raw), head)
    report["graph_sha256"] = hashlib.sha256(raw).hexdigest()
    report["protocol_sha256"] = hashlib.sha256(
        (ROOT / "docs/extended-topics/PROTOCOL.md").read_bytes()).hexdigest()
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(report, indent=2, ensure_ascii=False) + "\n", encoding="utf-8")
    print(json.dumps({k: report[k] for k in (
        "kind", "source_commit", "endpoint_complete", "controlled_effect_estimate")}, indent=2))


if __name__ == "__main__":
    main()
