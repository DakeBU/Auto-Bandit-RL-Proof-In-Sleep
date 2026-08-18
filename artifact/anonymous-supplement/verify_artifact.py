#!/usr/bin/env python3
"""Verify the anonymous ABRL artifact without trusting its authoring tree."""

import argparse
import hashlib
import json
import re
import sys
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
MANIFEST_PATH = ROOT / "ARTIFACT_MANIFEST.json"

BLOCKED_BYTES = (
    b"dake" + b"bu",
    b"dake" + b" bu",
    b"ji" + b" cheng",
    b"bo" + b" xue",
    b"atsushi" + b" nitanda",
    b"hau-san" + b" wong",
    b"qingfu" + b" zhang",
    b"city university" + b" of hong kong",
    b"auto-bandit-rl" + b"-proof-in-sleep",
    b"git." + b"overleaf.com",
    b"6a3f743d1f1f53f9" + b"6990c557",
    b"d43bfeee56fb0c1c35cf" + b"5af9fc1a7fdc3e0c37b9",
    b"cb5d50be148c691cc595" + b"ed9fd2f535c42506fada",
)
WINDOWS_PATH = re.compile(
    br"(?i)(?<![a-z])[a-z]:[\\/](?:users[\\/][^\\/\s]+|home[\\/][^\\/\s]+|wt[\\/]|code[\\/])"
)
HOST_HOME = re.compile(br"(?i)/(?:home|users)/[^/\s]+/")
EMAIL = re.compile(br"(?i)\b[a-z0-9._%+-]+@[a-z0-9.-]+\.[a-z]{2,}\b")


def fail(message):
    raise SystemExit("artifact verification failed: " + message)


def sha256(path):
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        for chunk in iter(lambda: handle.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


def require_anonymous(path):
    data = path.read_bytes()
    lowered = data.lower()
    for marker in BLOCKED_BYTES:
        if marker in lowered:
            fail("identity marker in {}: {}".format(path.relative_to(ROOT), marker.decode("ascii")))
    if WINDOWS_PATH.search(data):
        fail("absolute Windows path in {}".format(path.relative_to(ROOT)))
    if HOST_HOME.search(data):
        fail("absolute host home path in {}".format(path.relative_to(ROOT)))
    if EMAIL.search(data):
        fail("email address in {}".format(path.relative_to(ROOT)))


def load_json(path):
    try:
        return json.loads(path.read_text(encoding="utf-8"))
    except (OSError, ValueError) as exc:
        fail("cannot parse {}: {}".format(path.relative_to(ROOT), exc))


def verify_manifest():
    manifest = load_json(MANIFEST_PATH)
    require_anonymous(MANIFEST_PATH)
    if manifest.get("schema_version") != 1:
        fail("unsupported manifest schema")
    entries = manifest.get("files")
    if not isinstance(entries, list) or not entries:
        fail("manifest has no payload files")
    seen = set()
    tree_digest = hashlib.sha256()
    for entry in entries:
        rel = entry.get("path")
        if not isinstance(rel, str) or rel.startswith(("/", "\\")) or ".." in Path(rel).parts:
            fail("unsafe manifest path: {!r}".format(rel))
        if rel in seen:
            fail("duplicate manifest path: " + rel)
        seen.add(rel)
        path = ROOT / rel
        if not path.is_file() or path.is_symlink():
            fail("missing or non-regular payload file: " + rel)
        if path.stat().st_size != entry.get("bytes"):
            fail("size mismatch: " + rel)
        if sha256(path) != entry.get("sha256"):
            fail("SHA-256 mismatch: " + rel)
        require_anonymous(path)
        tree_digest.update(rel.encode("utf-8") + b"\0")
        tree_digest.update(entry["sha256"].encode("ascii") + b"\0")
        tree_digest.update(str(entry["bytes"]).encode("ascii") + b"\n")
    if tree_digest.hexdigest() != manifest.get("source_tree_digest"):
        fail("source-tree digest mismatch")
    actual = set()
    for path in ROOT.rglob("*"):
        if path.is_symlink():
            fail("symlink in extracted artifact: " + str(path.relative_to(ROOT)))
        if path.is_file():
            actual.add(path.relative_to(ROOT).as_posix())
    expected = seen | {"ARTIFACT_MANIFEST.json"}
    extras = sorted(actual - expected)
    missing = sorted(expected - actual)
    if extras:
        fail("unmanifested extracted file: " + ", ".join(extras[:8]))
    if missing:
        fail("manifested file is absent: " + ", ".join(missing[:8]))
    return manifest


def verify_claim_ledger():
    ledger = load_json(ROOT / "evidence" / "claim-ledger.json")
    index = load_json(ROOT / "evidence" / "local_lean_declarations.json")
    declarations = index.get("declarations")
    if not isinstance(declarations, list):
        fail("declaration index has no declarations list")
    names = {row.get("full_name") for row in declarations}
    names.update(ledger["index_counts"].get("generated_declaration_exceptions", []))
    if len(declarations) != ledger["index_counts"]["source_declarations"]:
        fail("declaration-index count drift")

    records = ledger.get("source_records", {})
    impl_ids = ledger["delayed_feedback"]["implementation_facing_ids"]
    diagnostic_id = ledger["delayed_feedback"]["diagnostic_id"]
    if any(records[item]["status"] != "compiled" for item in impl_ids):
        fail("implementation-facing delayed status is not compiled")
    impl_count = sum(len(records[item]["declarations"]) for item in impl_ids)
    if impl_count != 88:
        fail("delayed implementation count is {}, expected 88".format(impl_count))
    diagnostic = records[diagnostic_id]
    if diagnostic["status"] != "partial" or len(diagnostic["declarations"]) != 11:
        fail("D.10--D.12 diagnostic boundary drift")

    missing_names = []
    for record in records.values():
        for name in record.get("declarations", []):
            if name not in names:
                missing_names.append(name)
    if missing_names:
        fail("claim ledger references missing declarations: " + ", ".join(sorted(missing_names)[:8]))

    planned = records[ledger["matched_workflow_study"]["source_record_id"]]
    if planned["status"] != "planned" or planned["declarations"]:
        fail("target-drift study is not a zero-result planned record")
    if ledger["matched_workflow_study"].get("numerical_results_present") is not False:
        fail("target-drift result boundary is not explicit")

    graph = ledger["proof_graph"]
    expected = {
        "standalone_fixed_charge_sum": 1238,
        "union_fixed_charge": 1046,
        "shared_declaration_count": 175,
        "best_zdd_nonterminal_nodes": 1163,
        "cng_root_count": 8,
    }
    for key, value in expected.items():
        if graph.get(key) != value:
            fail("proof-graph evidence drift for {}".format(key))


def verify_source_freeze():
    freeze = load_json(ROOT / "evidence" / "source-freeze.json")
    papers = freeze.get("papers", [])
    if len(papers) != 3:
        fail("source freeze must contain exactly three papers")
    statuses = {row.get("initial_status") for row in papers}
    if "source_frozen_not_started" not in statuses or "source_frozen_reserve_not_started" not in statuses:
        fail("source-freeze non-completion statuses are missing")
    for paper in papers:
        digest = paper.get("camera_ready_sha256", "")
        if not re.fullmatch(r"[0-9a-f]{64}", digest):
            fail("invalid source PDF digest")
        if not paper.get("camera_ready_url", "").startswith("https://"):
            fail("source PDF URL is not HTTPS")


def verify_anonymous_base(manifest):
    base = load_json(ROOT / "evidence" / "anonymous-base-manifest.json")
    if base.get("git_object_database_included") is not False:
        fail("anonymous supplement must not contain a Git object database")
    if base.get("materializable_by_target_drift_runner") is not False:
        fail("target-drift materialization boundary is not explicit")
    digest = hashlib.sha256()
    for row in base.get("files", []):
        path = ROOT / row["path"]
        if not path.is_file() or sha256(path) != row["sha256"]:
            fail("anonymous base file mismatch: " + row["path"])
        digest.update(row["path"].encode("utf-8") + b"\0")
        digest.update(row["sha256"].encode("ascii") + b"\n")
    if digest.hexdigest() != base.get("tree_sha256"):
        fail("anonymous base tree digest mismatch")
    if manifest.get("anonymous_base", {}).get("tree_sha256") != base.get("tree_sha256"):
        fail("manifest/anonymous-base digest mismatch")
    if manifest.get("anonymous_base", {}).get("target_drift_materialization_ready") is not False:
        fail("manifest overstates target-drift materialization readiness")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.parse_args()
    manifest = verify_manifest()
    verify_claim_ledger()
    verify_source_freeze()
    verify_anonymous_base(manifest)
    print(json.dumps({
        "artifact_verified": True,
        "file_count": len(manifest["files"]),
        "source_tree_digest": manifest["source_tree_digest"],
        "proof_graph_included": manifest["proof_graph"]["included"],
        "target_drift_results_present": False,
    }, sort_keys=True))
    return 0


if __name__ == "__main__":
    sys.exit(main())
