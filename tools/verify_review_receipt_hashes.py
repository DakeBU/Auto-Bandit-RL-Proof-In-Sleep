"""Portable verification of reviewed-file hashes in review/validation receipts.

Receipts under ``runs/`` bind reviewed Lean files with a ``production_hashes``
(or ``lean_files_sha256``) map of path -> SHA-256.  Historically those values
were computed from one checkout's working-tree bytes, so the same receipt can
verify on one machine and fail on another purely because of CRLF/LF or mixed
line endings.  This script checks each entry against every rendering of the
committed content and reports a canonical, line-ending-independent value.

An entry is *bound* when the recorded hash equals the SHA-256 of one of:
  - the LF-normalized working-tree bytes,
  - the CRLF rendering of that content,
  - the raw working-tree bytes (covers mixed endings),
and the LF-normalized working-tree content equals the LF-normalized
``git show HEAD:<path>`` blob.  The canonical value is the LF-normalized hash.

Usage:
  python tools/verify_review_receipt_hashes.py RECEIPT.json [...]
  python tools/verify_review_receipt_hashes.py --glob "runs/extended-topics-20260919/causal-*.json"
  ... --write-rebinding OUT.json   # emit a normalization record

Exit status is 0 when every entry is bound, 1 otherwise.  The script never
modifies receipts; it only reads and, optionally, writes a new record.
"""
from __future__ import annotations

import argparse
import glob
import hashlib
import json
import os
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
HASH_KEYS = ("production_hashes", "lean_files_sha256")


def sha(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def to_lf(data: bytes) -> bytes:
    return data.replace(b"\r\n", b"\n")


def git_blob(path: str) -> bytes | None:
    proc = subprocess.run(["git", "show", f"HEAD:{path}"], cwd=ROOT, capture_output=True)
    return proc.stdout if proc.returncode == 0 else None


def git_oid(path: str) -> str | None:
    proc = subprocess.run(["git", "rev-parse", f"HEAD:{path}"], cwd=ROOT, capture_output=True, text=True)
    return proc.stdout.strip() if proc.returncode == 0 else None


def head_commit() -> str:
    return subprocess.run(["git", "rev-parse", "HEAD"], cwd=ROOT, capture_output=True, text=True).stdout.strip()


def classify(path: str, recorded: str, other_roots: list[Path] | None = None) -> dict:
    entry: dict = {"path": path, "recorded_sha256": recorded}
    wt = ROOT / path
    if not wt.exists():
        entry.update(status="missing-in-working-tree", bound=False)
        return entry
    raw = wt.read_bytes()
    lf = to_lf(raw)
    crlf = lf.replace(b"\n", b"\r\n")
    blob = git_blob(path)
    # Optional read-only attestation from other checkouts of the same commit:
    # a recorded hash may be the raw bytes of a working tree with mixed line
    # endings, which no clean checkout can reproduce.  Record whether such a
    # checkout exists and whether its normalized content equals HEAD's blob.
    cross = []
    for other in other_roots or []:
        candidate = other / path
        if not candidate.exists():
            continue
        other_raw = candidate.read_bytes()
        cross.append({
            "checkout": str(other),
            "raw_sha256_matches_recorded": sha(other_raw) == recorded,
            "lf_matches_head_blob": blob is not None and to_lf(other_raw) == to_lf(blob),
        })
    if cross:
        entry["cross_checkout"] = cross
    entry["canonical_lf_sha256"] = sha(lf)
    entry["git_blob_oid"] = git_oid(path)
    entry["working_tree_endings"] = (
        "mixed" if (b"\r\n" in raw and b"\n" in raw.replace(b"\r\n", b"")) else ("CRLF" if b"\r\n" in raw else "LF")
    )
    entry["working_tree_matches_head_blob_modulo_eol"] = blob is not None and to_lf(blob) == lf
    if recorded == sha(lf):
        rendering = "lf"
    elif recorded == sha(crlf):
        rendering = "crlf"
    elif recorded == sha(raw):
        rendering = "raw-working-tree"
    else:
        rendering = None
    entry["recorded_rendering"] = rendering
    entry["bound_via_cross_checkout"] = any(
        c["raw_sha256_matches_recorded"] and c["lf_matches_head_blob"] for c in cross)
    bound_here = rendering is not None and entry["working_tree_matches_head_blob_modulo_eol"]
    entry["bound"] = bound_here or entry["bound_via_cross_checkout"]
    if bound_here:
        entry["status"] = "bound"
    elif entry["bound_via_cross_checkout"]:
        entry["status"] = "bound-via-cross-checkout-raw-bytes"
    else:
        entry["status"] = "content-drift" if rendering is None else "working-tree-differs-from-head"
    return entry


def load_receipt(path: Path) -> tuple[str, dict]:
    data = json.loads(path.read_text(encoding="utf-8"))
    for key in HASH_KEYS:
        if isinstance(data.get(key), dict) and data[key]:
            return key, data[key]
    return "", {}


def main(argv: list[str]) -> int:
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("receipts", nargs="*", help="receipt JSON paths (relative to repository root)")
    parser.add_argument("--glob", action="append", default=[], help="glob pattern relative to repository root")
    parser.add_argument("--write-rebinding", metavar="OUT", help="write a normalization record to OUT (must not exist)")
    parser.add_argument("--also-checkout", action="append", default=[], metavar="DIR",
                        help="another read-only checkout of the same commit whose raw bytes may explain a recorded hash")
    parser.add_argument("--quiet", action="store_true")
    args = parser.parse_args(argv)
    other_roots = [Path(p) for p in args.also_checkout]

    paths = [Path(p) for p in args.receipts]
    for pattern in args.glob:
        paths.extend(Path(p) for p in sorted(glob.glob(str(ROOT / pattern))))
    paths = [p if p.is_absolute() else ROOT / p for p in paths]
    if not paths:
        parser.error("no receipts given")

    report = {"schema_version": 1, "kind": "review-receipt-hash-normalization", "head_commit": head_commit(),
              "canonical_rule": "sha256 of LF-normalized file bytes; equals sha256 of the git blob when the file is committed with LF",
              "cross_checkouts": [{"path": str(p), "head_commit": subprocess.run(
                  ["git", "-C", str(p), "rev-parse", "HEAD"], capture_output=True, text=True).stdout.strip()}
                  for p in other_roots],
              "receipts": []}
    all_bound = True
    for path in paths:
        key, hashes = load_receipt(path)
        rel = os.path.relpath(path, ROOT).replace(os.sep, "/")
        if not hashes:
            if not args.quiet:
                print(f"== {rel}: no {'/'.join(HASH_KEYS)} block; skipped")
            continue
        entries = [classify(p, h, other_roots) for p, h in hashes.items()]
        bound = all(e["bound"] for e in entries)
        all_bound &= bound
        report["receipts"].append({"receipt": rel, "hash_key": key, "receipt_sha256": sha(path.read_bytes()),
                                   "all_bound": bound, "entries": entries})
        if not args.quiet:
            print(f"== {rel} ({key}) {'OK' if bound else 'NOT BOUND'}")
            for e in entries:
                print(f"   {e['status']:<22} {e.get('recorded_rendering') or '-':<18} {e.get('working_tree_endings','-'):<6} {e['path']}")
    if args.write_rebinding:
        out = Path(args.write_rebinding)
        out = out if out.is_absolute() else ROOT / out
        if out.exists():
            print(f"refusing to overwrite existing {out}", file=sys.stderr)
            return 2
        out.parent.mkdir(parents=True, exist_ok=True)
        with open(out, "w", encoding="utf-8", newline="\n") as handle:
            handle.write(json.dumps(report, indent=2) + "\n")
        if not args.quiet:
            print(f"wrote {os.path.relpath(out, ROOT)}")
    return 0 if all_bound else 1


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
