"""Verify Chapter 1 frozen statements and ambient definition contexts.
Compilation and semantic/chapter acceptance are separate gates.
"""
import hashlib
import json
from pathlib import Path
import abrl_lifecycle as lifecycle
ROOT = Path(__file__).resolve().parents[1]
CONTRACT = ROOT / "docs/contracts/online-book-v1"
CONTEXTS = {
    "lemma-1-2-context.json": "OnlineLearningFoundations",
    "mean-context.json": "OnlineLearningMean",
    "ftl-context.json": "OnlineLearningFTL",
    "stochastic-context.json": "OnlineLearningStochastic",
    "regret-context-v2.json": "OnlineLearningRegret",
    "asymptotic-context.json": "OnlineLearningAsymptotic",
    "information-context.json": "OnlineLearningInformation",
    "iid-context.json": "OnlineLearningIID",
    "history-context.json": "OnlineLearningHistory",
}
def check():
    findings, reports, contexts = [], [], []
    for name, module in CONTEXTS.items():
        data = json.loads((CONTRACT / name).read_text(encoding="utf-8"))
        prefix = data["prefix"]
        digest = hashlib.sha256(prefix.encode()).hexdigest()
        expected = data.get("sha256", data.get("prefix_sha256"))
        source = (ROOT / "BanditRLProof" / (module + ".lean")).read_text(encoding="utf-8-sig")
        ok = source.startswith(prefix) and digest == expected
        contexts.append({"context": name, "ok": ok, "sha256": digest})
        if not ok: findings.append("Context changed: " + name)
    placeholder_scan_done = False
    for path in sorted(CONTRACT.glob("*.json")):
        data = json.loads(path.read_text(encoding="utf-8"))
        if "statement_hash" not in data or path.name == "lemma_1_2.json": continue
        # One full-root placeholder scan plus every immutable-header check.
        report = lifecycle.safe_verify(ROOT, data, lean_files=[] if placeholder_scan_done else None)
        placeholder_scan_done = True
        reports.append(report)
        if not report["ok"]: findings.append("Fence failed: " + path.name)
    return {"ok": not findings, "frozen_interfaces": len(reports),
            "contexts": contexts, "fences": reports, "findings": findings}
if __name__ == "__main__":
    result = check()
    print(json.dumps(result, indent=2))
    raise SystemExit(0 if result["ok"] else 1)
