"""Render a selected direct proof-reference diagram from the evidence report."""
import argparse
import json
from pathlib import Path

p = argparse.ArgumentParser(description=__doc__)
p.add_argument("report", type=Path)
p.add_argument("output", type=Path)
a = p.parse_args()
r = json.loads(a.report.read_text(encoding="utf-8"))
prefix = "BanditRLProof.HeavyTail."
base = {
    "BanditRLProof.UCB.sumRewards_rewardFromArmStream_eq_armPrefixSum",
    "BanditRLProof.Concentration.exp_le_one_add_self_add_sq_of_abs_le_one",
    "BanditRLProof.Concentration.HasMGFUpperBoundAt.measure_ge_le_exp_add",
}
edges = [e for e in r["direct_edges"]
         if (e["kind"] == "value" or e.get("also_in_value"))
         and (e["target"].startswith(prefix) or e["target"] in base)
         and "_proof_" not in e["source"] and "_proof_" not in e["target"]]
names = sorted({e[k] for e in edges for k in ("source", "target")})
ids = {name: f"n{i}" for i, name in enumerate(names)}
lines = [f"# Compiled proof references at `{r['source_commit']}`", "",
         "Selected direct proof-value references; arrow points to a dependency.",
         "Type-only references and external Mathlib references remain in the JSON report.",
         "This is not a teaching graph or a utility score.", "", "```mermaid", "flowchart TD"]
for name in names:
    label = name.removeprefix(prefix) if name.startswith(prefix) else name.removeprefix("BanditRLProof.")
    lines.append(f'  {ids[name]}["{label}"]')
for e in edges:
    label = "type+value" if e.get("also_in_value") else "value"
    lines.append(f'  {ids[e["source"]]} -->|"{label}"| {ids[e["target"]]}')
lines.append("  classDef frozen fill:#e2e8f0,stroke:#475569")
for name in names:
    if name in base:
        lines.append(f"  class {ids[name]} frozen")
lines += ["```", "", f"Raw compiled graph SHA-256: `{r['graph_sha256']}`.", ""]
a.output.write_text("\n".join(lines), encoding="utf-8")
