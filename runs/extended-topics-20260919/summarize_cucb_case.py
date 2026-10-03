"""Export and summarize the accepted CUCB compiled graph, without efficiency claims.

Run at the pinned snapshot or with byte-equivalent reviewed CUCB/library inputs.
--export creates a focused compiled export; otherwise --graph replays its summary.
The graph and receipt paths can be relocated together. No Lean source is modified.
"""
import argparse
from collections import Counter
import hashlib
import json
from pathlib import Path
import subprocess

ROOT = Path(__file__).resolve().parents[2]
RUN = Path(__file__).resolve().parent
SNAPSHOT = "b79f236c648c087f49c982f964f9b9e763d5b0e4"
BASE = "eedcda1db4d84f6bd69ec6ee50e174f6cf4056ac"


def require(condition, message):
    if not condition:
        raise ValueError(message)


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def git(*args):
    return subprocess.run(["git", *args], cwd=ROOT, capture_output=True)


def blob(commit, path):
    result = git("ls-tree", "-z", commit, "--", path)
    require(result.returncode == 0, "Git tree lookup failed: " + commit + ":" + path)
    if not result.stdout:
        return None
    rows = result.stdout.rstrip(b"\0").split(b"\0")
    require(len(rows) == 1, "Ambiguous Git tree path: " + path)
    metadata, actual_path = rows[0].split(b"\t", 1)
    mode, kind, oid = metadata.split()
    require(kind == b"blob" and actual_path.decode("utf-8") == path,
            "Not an exact Git file: " + path)
    return oid.decode("ascii")


def inputs():
    for commit in [BASE, SNAPSHOT]:
        require(git("cat-file", "-e", commit + "^{commit}").returncode == 0,
                "Required Git history missing: " + commit)
    semantic = json.loads((RUN / "cucb-semantic-review.json").read_text(encoding="utf-8"))
    paths = sorted(p for p in semantic["production_and_canary_hashes"]
                   if p.startswith("BanditRLProof/Algorithms/CUCB"))
    require(len(paths) == 38, "Accepted production module scope changed")
    for path, expected in semantic["production_and_canary_hashes"].items():
        require(sha(ROOT / path) == expected, "Reviewed file drift: " + path)
        committed = git("show", SNAPSHOT + ":" + path)
        require(committed.returncode == 0, "Missing snapshot file: " + path)
        require((ROOT / path).read_bytes().replace(b"\r\n", b"\n") ==
                committed.stdout.replace(b"\r\n", b"\n"), "Snapshot content drift: " + path)
    return paths


def export(graph_path, paths):
    # Require all tracked Lean inputs, the toolchain and dependency manifest to
    # match the pinned snapshot, not just the 38 reviewed owner modules.
    delta = git("diff", SNAPSHOT, "--", "*.lean", "lean-toolchain", "lake-manifest.json")
    require(delta.returncode == 0 and not delta.stdout, "Compiled input differs from snapshot")
    source = (ROOT / "tools/ProofGraphExport.lean").read_text(encoding="utf-8")
    names = "#[" + ", ".join("`" + p[:-5].replace("/", ".") for p in paths) + "]"
    selected = "(" + names + " : Array Name)"
    replacements = [
        ("if isProjectModule moduleName then", "if " + selected + ".contains moduleName then", 2),
        ("        result := result.insert declName",
         "        if (moduleOf? env declName).any (fun owner => " + selected + ".contains owner) then\n"
         "          result := result.insert declName", 1),
        ('if edge.targetScope == "external" && (env.find? edge.target).isSome then',
         'if !projectDecls.contains edge.target && (env.find? edge.target).isSome then', 1),
        ('nodeJson env declName "external"',
         'nodeJson env declName (if isProjectDecl env declName then "project" else "external")', 1),
        ('"project-direct-with-external-boundary"', '"cucb-owned-direct-with-all-boundary-nodes"', 1),
        ('"project_nodes"', '"focused_nodes"', 1),
        ('"external_boundary_nodes"', '"boundary_nodes"', 1),
    ]
    for old, new, count in replacements:
        require(source.count(old) == count, "Exporter shape changed: " + old)
        source = source.replace(old, new)
    graph_path.parent.mkdir(parents=True, exist_ok=True)
    lean = graph_path.with_suffix(".lean")
    lean.write_text(source, encoding="utf-8")
    build = subprocess.run(["lake", "build", "BanditRLProof"], cwd=ROOT,
                           stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    build_log = graph_path.with_suffix(".build.log")
    build_log.write_bytes(build.stdout)
    require(build.returncode == 0, "Public-root build failed; see " + str(build_log))
    subprocess.run(["lake", "env", "lean", "--run", str(lean), "--compact", str(graph_path)],
                   cwd=ROOT, check=True)
    graph_path.with_suffix(".provenance.json").write_text(json.dumps({
        "source_commit": SNAPSHOT, "graph_sha256": sha(graph_path),
        "generated_exporter_sha256": sha(lean),
        "base_exporter_sha256": sha(ROOT / "tools/ProofGraphExport.lean"),
        "root_build_command": "lake build BanditRLProof", "root_build_exit_code": 0,
        "root_build_log_sha256": sha(build_log),
        "tracked_lean_toolchain_manifest_match_snapshot": True,
        "limits": "Incremental Lake build, not a clean-room toolchain rebuild or full harness rerun"
    }, indent=2) + "\n", encoding="utf-8")


def summarize(graph_path, paths, expected_hash):
    require(sha(graph_path) == expected_hash, "Graph hash mismatch")
    provenance_path = graph_path.with_suffix(".provenance.json")
    extraction = json.loads(provenance_path.read_text(encoding="utf-8"))
    require(extraction["source_commit"] == SNAPSHOT and
            extraction["graph_sha256"] == expected_hash and
            extraction["root_build_exit_code"] == 0, "Extraction provenance mismatch")
    require(sha(graph_path.with_suffix(".lean")) == extraction["generated_exporter_sha256"],
            "Generated exporter hash mismatch")
    require(sha(graph_path.with_suffix(".build.log")) == extraction["root_build_log_sha256"],
            "Root build log hash mismatch")
    graph = json.loads(graph_path.read_text(encoding="utf-8"))
    require(graph["extraction"]["closure"] == "cucb-owned-direct-with-all-boundary-nodes",
            "Wrong graph scope")
    nodes = {n["name"]: n for n in graph["nodes"]}
    require(len(nodes) == len(graph["nodes"]), "Duplicate nodes")
    modules = {p[:-5].replace("/", ".") for p in paths}
    focused = {name for name, n in nodes.items() if n["module"] in modules}
    require(all(e["source"] in focused and e["target"] in nodes for e in graph["edges"]),
            "Foreign source or dangling target")
    require(len({(e["source"], e["target"]) for e in graph["edges"]}) == len(graph["edges"]),
            "Duplicate direct pair")
    counts = {"focused_nodes": len(focused), "boundary_nodes": len(nodes)-len(focused),
              "edges": len(graph["edges"]), "module_imports": len(graph["module_imports"])}
    require(counts == graph["counts"], "Graph count mismatch")
    pairs = sorted([{"source": e["source"], "target": e["target"],
                     "source_file": nodes[e["source"]]["source"]["file"],
                     "edge_kind": e["kind"], "also_in_value": e.get("also_in_value", False),
                     "target_file": nodes[e["target"]]["source"]["file"]}
                    for e in graph["edges"]
                    if (e["kind"] == "value" or e.get("also_in_value") is True)
                    and nodes[e["target"]]["scope"] == "project"
                    and e["target"] not in focused], key=lambda e: (e["source"], e["target"]))
    provenance = []
    for path in sorted({e["target_file"] for e in pairs}):
        before, now = blob(BASE, path), blob(SNAPSHOT, path)
        require(now is not None, "Missing target owner at snapshot: " + path)
        category = ("absent-at-initial-base" if before is None else
                    "unchanged-from-initial-base" if before == now else "modified-since-initial-base")
        provenance.append({"path": path, "initial_blob": before, "snapshot_blob": now,
                           "category": category,
                           "addition_commits": git("log", "--diff-filter=A", "--format=%H %s",
                                                   SNAPSHOT, "--", path).stdout.decode("utf-8").splitlines(),
                           "proof_reference_pairs": sum(e["target_file"] == path for e in pairs)})
    validation_path = RUN / "cucb-production-validation.json"
    validation = json.loads(validation_path.read_text(encoding="utf-8"))
    return {"kind": "descriptive-development-evidence-not-controlled-evaluation",
            "source_commit": SNAPSHOT, "initial_frozen_base": BASE,
            "graph_sha256": expected_hash, "module_paths": paths, "counts": counts,
            "extraction_provenance_sha256": sha(provenance_path),
            "extraction_root_build": extraction,
            "external_project_proof_reference_pairs": len(pairs),
            "distinct_targets_including_generated": len({e["target"] for e in pairs}),
            "pairs": pairs, "owning_file_provenance": provenance,
            "category_pairs": dict(sorted(Counter({c: sum(f["proof_reference_pairs"] for f in provenance
                                                      if f["category"] == c)
                                                   for c in {f["category"] for f in provenance}}).items())),
            "semantic_receipt_sha256": sha(RUN / "cucb-semantic-review.json"),
            "production_validation_sha256": sha(validation_path),
            "recorded_production_commit": validation["code_and_site_commit"],
            "recorded_gates": validation["gates"], "full_gates_rerun_by_this_script": False,
            "limitations": ["Direct constant-reference pairs, not use frequency or effort saved",
                            "Generated auxiliary declarations remain included",
                            "File-level provenance does not prove declaration availability in modified files",
                            "Includes finite-model production examples; excludes six Tests modules as seeds",
                            "Reading memberships and imports are not proof-dependency edges",
                            "Export runs an incremental public-root build; Tests/full harness are not rerun",
                            "Graph replay requires Git history, generated exporter, provenance and root-build log",
                            "Private review/log archives are not revalidated by this summary"],
            "controlled_runs": [], "efficiency_effect_estimate": None,
            "completed_topics": 0, "all_topic_evaluation_complete": False}


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--graph", type=Path, required=True)
    parser.add_argument("--graph-sha256")
    parser.add_argument("--export", action="store_true")
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    paths = inputs()
    graph_path = args.graph.resolve()
    if args.export:
        export(graph_path, paths)
    else:
        require(args.graph_sha256 is not None, "Replay requires --graph-sha256")
    expected = args.graph_sha256 or sha(graph_path)
    args.output.write_text(json.dumps(summarize(graph_path, paths, expected), indent=2) + "\n",
                           encoding="utf-8")
    print("Wrote CUCB descriptive summary; no controlled runs or efficiency estimate.")
