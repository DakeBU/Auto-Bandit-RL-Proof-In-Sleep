"""Reproduce descriptive case statistics; this script does not run experiments."""
import hashlib
import json
import subprocess
from pathlib import Path
ROOT = Path(__file__).resolve().parents[2]
BASE = "eedcda1db4d84f6bd69ec6ee50e174f6cf4056ac"
RUN = ROOT / "runs/extended-topics-20260919"

def blob(commit, path):
    result = subprocess.run(["git", "rev-parse", "--verify", commit + ":" + path],
                            cwd=ROOT, capture_output=True, text=True)
    return result.stdout.strip() if result.returncode == 0 else None

def summarize():
    names = ["source-confidence-reuse", "clipping-reuse", "source-regret-validation",
             "clipping-review-validation", "counterexample-validation", "heavy-tail-mapping-validation"]
    data = {n: json.loads((RUN / (n + ".json")).read_text(encoding="utf-8")) for n in names}
    original = data["source-confidence-reuse"]
    files = []
    for path, expected in original["unchanged_reused_source_blobs"].items():
        at_source = blob(original["source_commit"], path)
        at_comparison = blob(original["comparison_base"], path)
        assert at_source == at_comparison == expected, path
        initial = blob(BASE, path)
        files.append({"path": path, "development_snapshot_blob": expected,
                      "initial_base_blob": initial,
                      "unchanged_since_initial_base": initial == expected,
                      "initial_base_contains_file": initial is not None})
    references = original["direct_reused_project_proof_references"]
    for e in references:
        assert e["kind"] == "value" or e.get("also_in_value") is True
    clip = data["clipping-reuse"]
    assert len(clip["project_proof_references"]) == 113
    assert data["counterexample-validation"]["mathematical_witness"]["literal_positive_gap_sum_negated"]
    mapping = data["heavy-tail-mapping-validation"]
    assert mapping["gates"]["full_harness"] and mapping["gates"]["site_check"]
    return {"kind": "descriptive-development-case-not-controlled-evaluation",
            "initial_frozen_base": BASE,
            "source_confidence_snapshot": {
                "source_commit": original["source_commit"], "comparison_base": original["comparison_base"],
                "new_declarations_at_snapshot": len(original["new_declarations"]),
                "direct_project_proof_references": len(references),
                "distinct_project_targets": len({r["target"] for r in references}),
                "reuse_file_provenance": files,
                "scope": "Historical confidence development snapshot; not latest sharp producer or full regret endpoint"},
            "clipping_snapshot": {"source_commit": clip["source_commit"],
                "graph_counts": clip["graph_counts"],
                "project_proof_references": len(clip["project_proof_references"]),
                "scope": clip["scope"], "all_references_are_initial_base_reuse": False},
            "latest_joint_validation": {"source_commit": mapping["source_commit"],
                "gate_code_commit": mapping["gate_code_commit"], "gates": mapping["gates"]},
            "receipt_sha256": {n + ".json": hashlib.sha256((RUN / (n + ".json")).read_bytes()).hexdigest() for n in names},
            "controlled_runs": [], "efficiency_effect_estimate": None,
            "completed_topics": 0, "all_topic_evaluation_complete": False}

if __name__ == "__main__":
    print(json.dumps(summarize(), indent=2))
