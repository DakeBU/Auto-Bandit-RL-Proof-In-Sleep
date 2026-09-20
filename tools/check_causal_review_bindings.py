"""Check the additive causal review receipt against Git and the working tree.

Hashes cover UTF-8 source bytes after CRLF/bare-CR to LF conversion only.
This checks evidence identity, not mathematical validity. Historical receipts
remain immutable; the additive receipt identifies which bindings it supersedes.
Private review reports are checked only when --review-dir is supplied.
"""
from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path, PurePosixPath
import re
import subprocess


ROOT = Path(__file__).resolve().parents[1]
RECEIPT = "runs/extended-topics-20260920/causal-review-rebinding.json"
NORMALIZATION = "utf8-crlf-and-cr-to-lf-only"


def digest(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def source_digest(data: bytes) -> str:
    data.decode("utf-8", errors="strict")
    return digest(data.replace(b"\r\n", b"\n").replace(b"\r", b"\n"))


def relative_file(root: Path, name: str) -> Path:
    path = PurePosixPath(name)
    if (not name or path.is_absolute() or ".." in path.parts
            or "\\" in name or ":" in name):
        raise ValueError(f"unsafe relative path: {name}")
    target = root.joinpath(*path.parts)
    target.resolve().relative_to(root.resolve())
    return target


def check(root: Path, receipt: dict, review_dir: Path | None = None) -> dict:
    if receipt.get("normalization") != NORMALIZATION:
        raise ValueError("missing or unsupported source normalization")
    commit = receipt.get("code_commit", "")
    if not re.fullmatch(r"[0-9a-f]{40}", commit):
        raise ValueError("code_commit must be a full immutable Git commit")
    kind = subprocess.check_output(["git", "-C", str(root), "cat-file", "-t", commit]).strip()
    if kind != b"commit":
        raise ValueError("code_commit must identify a commit object")
    files = receipt.get("production_hashes_lf", {})
    if not files:
        raise ValueError("empty production bindings")
    errors = []
    for name, expected in files.items():
        target = relative_file(root, name)
        if not re.fullmatch(r"[0-9a-f]{64}", expected):
            raise ValueError(f"invalid SHA256: {name}")
        blob = subprocess.check_output(
            ["git", "-C", str(root), "show", f"{commit}:{name}"])
        if source_digest(blob) != expected:
            errors.append(f"commit hash mismatch: {name}")
        if source_digest(target.read_bytes()) != expected:
            errors.append(f"working-tree hash mismatch: {name}")
    covered = set()
    groups = receipt.get("semantic_reviews", [])
    if not groups:
        raise ValueError("missing semantic review groups")
    report_names = set(receipt.get("review_hashes", {}))
    for name, expected in receipt.get("review_hashes", {}).items():
        relative_file(review_dir or root, name)
        if not isinstance(expected, str) or not re.fullmatch(r"[0-9a-f]{64}", expected):
            raise ValueError(f"invalid review SHA256: {name}")
    for group in groups:
        roles = [group.get(k) for k in ("formalizer", "blind_decoder", "source_reviewer")]
        if not all(isinstance(x, str) and x.strip() == x and x for x in roles) or len(set(roles)) != 3:
            raise ValueError("semantic review roles must be present and distinct")
        if group.get("verdict") not in ("accepted", "accepted-with-explicit-delta"):
            raise ValueError("semantic review is not accepted")
        for field in ("blind_report", "source_report"):
            if group.get(field) not in report_names:
                raise ValueError(f"unbound {field}")
        if group["blind_report"] == group["source_report"]:
            raise ValueError("blind and source reports must be distinct")
        names = group.get("files", [])
        if not names or not set(names).issubset(files):
            raise ValueError("review group has empty or unbound file coverage")
        covered.update(names)
    if covered != set(files):
        raise ValueError("not every production binding has semantic review coverage")
    for name, expected in receipt.get("historical_receipt_hashes_lf", {}).items():
        if source_digest(relative_file(root, name).read_bytes()) != expected:
            errors.append(f"historical receipt modified: {name}")
    if review_dir is not None:
        for name, expected in receipt["review_hashes"].items():
            if digest(relative_file(review_dir, name).read_bytes()) != expected:
                errors.append(f"review report mismatch: {name}")
    if errors:
        raise ValueError("\n".join(errors))
    return {"code_commit": commit, "files_verified": len(files),
            "reviewed_file_hashes_verified": True,
            "private_review_reports_verified": review_dir is not None,
            "normalization": NORMALIZATION,
            "semantic_scope": "identity and declared coverage only; not proof of review quality"}


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--repo", type=Path, default=ROOT)
    parser.add_argument("--receipt", type=Path)
    parser.add_argument("--review-dir", type=Path)
    args = parser.parse_args()
    path = args.receipt or args.repo / RECEIPT
    try:
        receipt = json.loads(path.read_text(encoding="utf-8"))
        print(json.dumps(check(args.repo, receipt, args.review_dir), indent=2))
    except (ValueError, OSError, subprocess.CalledProcessError) as exc:
        print(f"causal review binding check FAILED: {exc}")
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
