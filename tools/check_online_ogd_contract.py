"""Check the OGD freeze against definitions, original headers, and native fences.

This is a statement/definition guard, not a substitute for Lean or semantic review.
Run from any directory; a failed metadata repair cannot silently refreeze a target.
"""
import hashlib
import json
from pathlib import Path

import abrl_lifecycle as lifecycle


ROOT = Path(__file__).resolve().parents[1]
CONTRACT = ROOT / "docs/contracts/online-ogd-v1"


def check():
    findings = []
    definitions = json.loads((CONTRACT / "definitions.json").read_text(encoding="utf-8"))
    source = (ROOT / definitions["file"]).read_text(encoding="utf-8-sig")
    prefix = source.split("/-- The projection exists", 1)[0]
    digest = hashlib.sha256(prefix.encode()).hexdigest()
    if prefix != definitions["prefix"] or digest != definitions["sha256"]:
        findings.append("Frozen definitions, ambient typeclasses, or imports changed")
    reports = []
    for path in sorted((CONTRACT / "fences").glob("*.json")):
        fence = json.loads(path.read_text(encoding="utf-8"))
        original = json.loads((CONTRACT / path.name).read_text(encoding="utf-8"))
        for key in ("statement", "statement_hash", "declaration", "file"):
            if fence[key] != original[key]:
                findings.append(f"Metadata repair changed {key}: {path.name}")
        report = lifecycle.safe_verify(ROOT, fence)
        reports.append(report)
        if not report["ok"]:
            findings.append(f"Native fence check failed: {path.name}")
    if len(reports) != 10:
        findings.append("Expected all ten frozen public theorem interfaces")
    return {"ok": not findings, "definitions_sha256": digest,
            "frozen_interfaces": len(reports), "findings": findings, "fences": reports}


if __name__ == "__main__":
    result = check()
    print(json.dumps(result, indent=2))
    raise SystemExit(0 if result["ok"] else 1)
