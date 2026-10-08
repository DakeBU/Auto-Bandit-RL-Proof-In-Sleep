"""Bind the focused compiled graph to actual source files and Git snapshots.

This records provenance, not theorem admission or a fresh compilation claim.
"""
from __future__ import annotations

import hashlib
import json
import subprocess
from collections import Counter
from pathlib import Path


HERE = Path(__file__).resolve().parent
BANDIT = HERE.parents[1]
QUANTUM = BANDIT.parent / "quantum"


def git(root: Path, *args: str) -> str:
    return subprocess.check_output(["git", "-C", str(root), *args], text=True).strip()


def main() -> None:
    graph_path = HERE / "evidence/proof-term-graph.json"
    graph = json.loads(graph_path.read_text(encoding="utf-8"))
    modules = sorted({n["module"] for n in graph["nodes"] if n["scope"] == "project"})
    sources = {}
    for module in modules:
        root = QUANTUM if module.startswith("QuantumBlockEncoding.") else (
            BANDIT if module.startswith("BanditRLProof.") else HERE)
        path = root / (module.replace(".", "/") + ".lean")
        raw = path.read_bytes()
        normalized = raw.replace(b"\r\n", b"\n")
        sources[module] = {
            "repository": "quantum" if root == QUANTUM else "bandit",
            "relative_path": path.relative_to(QUANTUM if root == QUANTUM else BANDIT).as_posix(),
            "raw_sha256": hashlib.sha256(raw).hexdigest(),
            "lf_sha256": hashlib.sha256(normalized).hexdigest(),
            "git_blob": git(QUANTUM if root == QUANTUM else BANDIT,
                            "hash-object", str(path)),
        }
    canaries = {}
    for root, relative in (
        (QUANTUM, "ABEISTests/QuantumBanditBornCanary.lean"),
        (QUANTUM, "ABEISTests/QuantumQueryWordCanary.lean"),
        (QUANTUM, "ABEISTests/BasisHellingerCanary.lean"),
        (QUANTUM, "ABEISTests/ResetBlockProcessCanary.lean"),
        (BANDIT, "Tests/QuantumConfidenceCanary.lean"),
        (BANDIT, "research/quantum-bandit/Canary.lean"),
    ):
        raw = (root / relative).read_bytes()
        canaries[relative] = {
            "repository": "quantum" if root == QUANTUM else "bandit",
            "raw_sha256": hashlib.sha256(raw).hexdigest(),
            "lf_sha256": hashlib.sha256(raw.replace(b"\r\n", b"\n")).hexdigest(),
        }
    report = {
        "schema_version": 1,
        "meaning": "actual source provenance and proof-term graph; not publication admission",
        "repositories": {
            name: {"head_at_inventory": git(root, "rev-parse", "HEAD"),
                   "branch": git(root, "branch", "--show-current"),
                   "toolchain": (root / "lean-toolchain").read_text().strip(),
                   "manifest_sha256": hashlib.sha256((root / "lake-manifest.json").read_bytes()).hexdigest()}
            for name, root in (("bandit", BANDIT), ("quantum", QUANTUM))
        },
        "sources": sources,
        "canaries": canaries,
        "graph": {
            "path": "evidence/proof-term-graph.json",
            "sha256": hashlib.sha256(graph_path.read_bytes()).hexdigest(),
            "nodes_by_scope": dict(Counter(n["scope"] for n in graph["nodes"])),
            "edges": len(graph["edges"]),
            "module_import_edges": len(graph["module_imports"]),
            "sorryAx_nodes": [n["name"] for n in graph["nodes"] if "sorryAx" in n["name"]],
        },
        "declaration_records": [
            {"name": n["name"], "module": n["module"], "kind": n["kind"],
             "source": n.get("source"),
             "kernel_status": "compiled focused leaf",
             "publication_status": "draft; consult source review for seal coverage",
             "dependencies": [e for e in graph["edges"] if e.get("source") == n["name"]]}
            for n in graph["nodes"] if n["scope"] == "project"
        ],
    }
    (HERE / "evidence/source-artifacts.json").write_text(
        json.dumps(report, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
    print(json.dumps(report["graph"], indent=2))


if __name__ == "__main__":
    main()
