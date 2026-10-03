"""Reproduce the five-module compiled clipping dependency export.

Usage: python export_clipping_dependencies.py OUTPUT_DIRECTORY [--prepare-only]
The output is a direct graph with complete boundary nodes, not transitive closure.
"""
import argparse
from pathlib import Path
import subprocess

MODULES = ["HeavyTailClipping", "HeavyTailClippedMoments", "HeavyTailClippedConfidence",
           "HeavyTailClippedScheduled", "HeavyTailClippedTransfer"]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("output_directory", type=Path)
    parser.add_argument("--prepare-only", action="store_true")
    args = parser.parse_args()
    root = Path(__file__).resolve().parents[2]
    source = (root / "tools/ProofGraphExport.lean").read_text(encoding="utf-8")
    names = "#[" + ", ".join("`BanditRLProof." + name for name in MODULES) + "]"
    replacements = [
        ("if isProjectModule moduleName then", f"if ({names} : Array Name).contains moduleName then", 2),
        ('if edge.targetScope == "external" && (env.find? edge.target).isSome then',
         'if !projectDecls.contains edge.target && (env.find? edge.target).isSome then', 1),
        ('nodeJson env declName "external"',
         'nodeJson env declName (if isProjectDecl env declName then "project" else "external")', 1),
        ('"project-direct-with-external-boundary"',
         '"five-clipping-modules-direct-with-all-boundary-nodes"', 1),
        ('"project_nodes"', '"focused_nodes"', 1),
        ('"external_boundary_nodes"', '"boundary_nodes"', 1),
    ]
    for old, new, expected in replacements:
        if source.count(old) != expected:
            raise SystemExit(f"Exporter shape changed: expected {expected} occurrences of {old!r}")
        source = source.replace(old, new)
    output = args.output_directory.resolve()
    output.mkdir(parents=True, exist_ok=True)
    lean = output / "ClippingGraphExport.lean"
    lean.write_text(source, encoding="utf-8")
    if not args.prepare_only:
        subprocess.run(["lake", "env", "lean", "--run", str(lean), "--compact",
                        str(output / "clipping-direct-graph.json")], cwd=root, check=True)


if __name__ == "__main__":
    main()
