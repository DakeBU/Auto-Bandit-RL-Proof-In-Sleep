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
TRANSPORT = CONTRACT / "annotation-transport-v1.json"
TRANSPORT_SHA256 = "306dfbcaa2f662518ae4faadb0237ffe006625a249cd9375c72cc843c7ee17d7"

def annotation_end(raw, offset):
    # Within a Lean block comment, nested /- and -/ delimiters determine depth.
    # Quotes, backticks and -- are ordinary comment text, not lexical escapes.
    if raw[offset:offset + 3] != b"/-!":
        raise ValueError("Expected exactly one module documentation block")
    i, depth = offset + 2, 1
    while i < len(raw):
        if raw[i:i + 2] == b"/-":
            depth += 1
            i += 2
        elif raw[i:i + 2] == b"-/":
            depth -= 1
            i += 2
            if depth == 0:
                return i
        else:
            i += 1
    raise ValueError("Unclosed annotation")

def verify_annotation_transport(name, module, data, raw, manifest):
    rows = manifest["rows"]
    if len(rows) != 6 or len({r["context"] for r in rows}) != 6:
        raise ValueError("Invalid exact six-row manifest")
    matches = [r for r in rows if r["context"] == name and r["module"] == module]
    if len(matches) != 1:
        return False
    row = matches[0]
    original = data["prefix"].encode("utf-8")
    expected = data.get("sha256", data.get("prefix_sha256"))
    if hashlib.sha256(original).hexdigest() != expected or expected != row["frozen_prefix_sha256"]:
        return False
    published = bytes.fromhex(row["published_LF_prefix_hex"])
    if hashlib.sha256(published).hexdigest() != row["published_LF_prefix_sha256"]:
        return False
    offset = row["insertion_offset_LF_bytes"]
    inserted = bytes.fromhex(row["inserted_LF_hex"])
    end = annotation_end(inserted, 0)
    if inserted[end:] != b"\n\n" or hashlib.sha256(inserted).hexdigest() != row["inserted_LF_sha256"]:
        return False
    if published != original[:offset] + inserted + original[offset:]:
        return False
    if published[:offset] + published[offset + len(inserted):] != original:
        return False
    # Only two explicitly sealed Git-LF / observed-working-RAW forms. No general
    # stripping, whitespace normalization, comment erasure or prefix search.
    variants = row["published_RAW_variants"]
    if len(variants) not in (1, 2):
        return False
    for variant in variants:
        exact = bytes.fromhex(variant["hex"])
        if hashlib.sha256(exact).hexdigest() != variant["sha256"]:
            return False
        if exact.replace(b"\r\n", b"\n") != published:
            return False
    return any(raw.startswith(bytes.fromhex(v["hex"])) for v in variants)

def check():
    findings, reports, contexts = [], [], []
    transport_raw = TRANSPORT.read_bytes()
    if hashlib.sha256(transport_raw).hexdigest() != TRANSPORT_SHA256:
        raise ValueError("Unreviewed annotation transport manifest")
    transport = json.loads(transport_raw)
    for name, module in CONTEXTS.items():
        data = json.loads((CONTRACT / name).read_text(encoding="utf-8"))
        prefix = data["prefix"]
        digest = hashlib.sha256(prefix.encode()).hexdigest()
        expected = data.get("sha256", data.get("prefix_sha256"))
        source = (ROOT / "BanditRLProof" / (module + ".lean")).read_text(encoding="utf-8-sig")
        raw = (ROOT / "BanditRLProof" / (module + ".lean")).read_bytes()
        transported = verify_annotation_transport(name, module, data, raw, transport)
        has_transport = any(row["context"] == name for row in transport["rows"])
        ok = transported if has_transport else (source.startswith(prefix) and digest == expected)
        contexts.append({"context": name, "ok": ok, "sha256": digest, "exact_annotation_transport": transported})
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
