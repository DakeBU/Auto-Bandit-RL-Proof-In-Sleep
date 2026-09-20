"""Audit historical HOO reuse and production receipts; no experiments are run.

Pass --graph to relocate the pinned compiled graph. The default graph location
comes from hoo-compiled-references.json and requires the local evidence archive.
Git history through the initial base and both recorded snapshots is required.
"""
import argparse
from collections import Counter
import hashlib
import json
from pathlib import Path
import subprocess

from export_hoo_dependencies import MODULES

ROOT = Path(__file__).resolve().parents[2]
RUN = Path(__file__).resolve().parent
BASE = "eedcda1db4d84f6bd69ec6ee50e174f6cf4056ac"


def require(condition, message):
    if not condition:
        raise ValueError(message)


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def git(*args):
    return subprocess.run(["git", *args], cwd=ROOT, capture_output=True)


def blob(commit, path):
    result = git("rev-parse", "--verify", commit + ":" + path)
    return result.stdout.decode().strip() if result.returncode == 0 else None


def summarize(graph_path=None):
    names = ["hoo-compiled-references", "hoo-production-review",
             "hoo-production-validation", "logli-source-disposition"]
    receipts = {name: json.loads((RUN / (name + ".json")).read_text(encoding="utf-8"))
                for name in names}
    old = receipts["hoo-compiled-references"]
    validation = receipts["hoo-production-validation"]
    graph_path = graph_path or Path(old["graph"]["path"])
    require(sha(graph_path) == old["graph"]["sha256"], "Compiled graph SHA mismatch")
    graph = json.loads(graph_path.read_text(encoding="utf-8"))
    nodes = {node["name"]: node for node in graph["nodes"]}
    require(len(nodes) == len(graph["nodes"]), "Duplicate graph nodes")
    require(all(e["source"] in nodes and e["target"] in nodes for e in graph["edges"]),
            "Dangling graph edge")
    modules = {"BanditRLProof." + name for name in MODULES}
    focused = {name for name, node in nodes.items() if node["module"] in modules}
    foreign_sources = {e["source"] for e in graph["edges"]} - focused
    exported_seeds = focused | foreign_sources
    counts = {"focused_nodes": len(exported_seeds), "boundary_nodes": len(nodes) - len(exported_seeds),
              "edges": len(graph["edges"]), "module_imports": len(graph["module_imports"])}
    require(counts == graph["counts"] == old["counts"], "Graph counts disagree")
    require(foreign_sources == {"BanditRLProof.Concentration.HasCondMGFUpperBoundAt.congr_simp"},
            "Historical duplicate-generated-declaration boundary changed")
    pairs = sorted([
        {"source": e["source"], "target": e["target"],
         "target_file": nodes[e["target"]]["source"]["file"]}
        for e in graph["edges"]
        if (e["kind"] == "value" or e.get("also_in_value") is True)
        and nodes[e["target"]]["scope"] == "project"
        and nodes[e["target"]]["module"] not in modules
    ], key=lambda e: (e["source"], e["target"]))
    require(len({(e["source"], e["target"]) for e in pairs}) == len(pairs), "Duplicate pairs")
    require(len(pairs) == old["external_to_HOO_project_proof_reference_pairs"], "Pair count mismatch")
    require(sorted({e["target"] for e in pairs}) == old["external_to_HOO_project_proof_targets"],
            "Target set mismatch")
    raw_pairs = pairs
    pairs = [e for e in raw_pairs if e["source"] in focused]
    for commit in [BASE, old["source_commit"], validation["code_and_site_commit"]]:
        require(git("cat-file", "-e", commit + "^{commit}").returncode == 0,
                "Missing Git commit " + commit)
    files = []
    for path in sorted({e["target_file"] for e in pairs}):
        initial, historical = blob(BASE, path), blob(old["source_commit"], path)
        require(historical is not None, "Missing historical source " + path)
        category = ("absent-at-initial-base" if initial is None else
                    "unchanged-from-initial-base" if initial == historical else
                    "present-but-modified-since-initial-base")
        files.append({"path": path, "initial_blob": initial, "historical_blob": historical,
                      "category": category,
                      "proof_reference_pairs": sum(e["target_file"] == path for e in pairs),
                      "distinct_targets": len({e["target"] for e in pairs if e["target_file"] == path})})
    # Bind recorded raw working-file hashes to the commit, explicitly allowing CRLF/LF normalization.
    bindings = []
    code = validation["code_and_site_commit"]
    for field in ["production_hashes", "site_input_hashes"]:
        for path, expected in validation[field].items():
            result = git("show", code + ":" + path)
            require(result.returncode == 0, "Missing production snapshot: " + path)
            committed = result.stdout
            local = (ROOT / path).read_bytes()
            require(hashlib.sha256(local).hexdigest() == expected, "Recorded working-file SHA mismatch: " + path)
            require(local.replace(b"\r\n", b"\n") == committed.replace(b"\r\n", b"\n"),
                    "Working-file content differs from production commit: " + path)
            bindings.append({"path": path, "recorded_working_file_sha256": expected,
                             "git_blob_sha256": hashlib.sha256(committed).hexdigest(),
                             "byte_identical": local == committed, "equal_after_crlf_normalization": True})
    require(sha(RUN / "hoo-production-review.json") == validation["semantic_receipt"]["sha256"],
            "Semantic receipt mismatch")
    return {
        "kind": "descriptive-development-evidence-not-controlled-evaluation",
        "initial_frozen_base": BASE,
        "compiled_snapshot": {"source_commit": old["source_commit"],
            "graph_sha256": old["graph"]["sha256"], "counts": counts,
            "scope": old["scope"], "module_count": len(modules),
            "raw_export_external_project_proof_reference_pairs": len(raw_pairs),
            "ownership_filtered_proof_reference_pairs": len(pairs),
            "ownership_filtered_focused_nodes": len(focused),
            "excluded_foreign_source_pairs": [e for e in raw_pairs if e["source"] not in focused],
            "distinct_targets_including_generated_declarations": len({e["target"] for e in pairs}),
            "pairs": pairs, "owning_file_provenance": files,
            "file_category_counts": dict(sorted(Counter(f["category"] for f in files).items()))},
        "production_snapshot": {"code_and_site_commit": code,
            "recorded_gates": validation["gates"], "rerun_by_this_script": False,
            "working_file_hashes_verified_and_bound_to_commit": True, "file_bindings": bindings},
        "receipt_sha256": {name + ".json": sha(RUN / (name + ".json")) for name in names},
        "limitations": [
            "Graph excludes the later HOORewardFamily module; no current full-module count is inferred",
            "Historical exporter seeds include a duplicate generated congr_simp owned by ConcentrationSubGaussian; its outgoing pair is excluded from HOO reuse",
            "File-level provenance does not establish declaration-level availability in modified files",
            "Generated auxiliary declarations are included; targets are not independent human lemmas",
            "Pairs are direct graph relations, not syntax-use counts, effort saved or independent trials",
            "Recorded gates are historical; this script verifies committed bytes and does not rerun Lean",
            "Private review/log archives are not included or revalidated by this summary",
            "Recorded production hashes are raw working-file hashes, including mixed line endings; Git comparison normalizes CRLF to LF explicitly",
        ],
        "controlled_runs": [], "efficiency_effect_estimate": None,
        "completed_topics": 0, "all_topic_evaluation_complete": False,
    }


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--graph", type=Path)
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    output = json.dumps(summarize(args.graph), indent=2) + "\n"
    if args.output:
        args.output.write_text(output, encoding="utf-8")
    else:
        print(output, end="")
