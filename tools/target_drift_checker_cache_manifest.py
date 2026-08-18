#!/usr/bin/env python3
"""Create or verify the byte-complete immutable checker-cache manifest."""

from __future__ import annotations

import argparse
import hashlib
import json
import os
import re
import stat
from pathlib import Path
from typing import Any


SUITE_ID = "ABRL-TARGET-DRIFT-V2"
SCHEMA_VERSION = 1
SHA256 = re.compile(r"[0-9a-f]{64}")
COMMIT = re.compile(r"[0-9a-f]{40}")
PROVENANCE_FIELDS = {
    "workspace_base_commit", "source_files_aggregate_sha256",
    "build_input_manifest_sha256", "checker_image_recipe_sha256",
    "base_image_digest", "lean_toolchain_sha256",
}


def require(condition: bool, message: str) -> None:
    if not condition:
        raise SystemExit(f"target-drift checker-cache manifest failed: {message}")


def sha256_file(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        for block in iter(lambda: handle.read(1024 * 1024), b""):
            digest.update(block)
    return digest.hexdigest()


def canonical_json_bytes(value: Any) -> bytes:
    return json.dumps(
        value, sort_keys=True, separators=(",", ":"), ensure_ascii=False
    ).encode("utf-8")


def require_plain_tree(root: Path) -> None:
    require(root.is_dir() and not root.is_symlink(), "cache root is missing or linked")
    root_info = root.lstat()
    require(stat.S_ISDIR(root_info.st_mode), "cache root is not a directory")
    for path in root.rglob("*"):
        info = path.lstat()
        reparse = bool(getattr(info, "st_file_attributes", 0) & 0x400)
        require(not stat.S_ISLNK(info.st_mode) and not reparse,
                f"cache contains a link/reparse point: {path}")
        require(stat.S_ISDIR(info.st_mode) or stat.S_ISREG(info.st_mode),
                f"cache contains a special file: {path}")
        if stat.S_ISREG(info.st_mode):
            require(info.st_nlink == 1,
                    f"cache contains a multiply linked file: {path}")


def cache_files(root: Path) -> list[dict[str, Any]]:
    require_plain_tree(root)
    entries: list[dict[str, Any]] = []
    paths = [item for item in root.rglob("*") if item.is_file()]
    for path in sorted(paths, key=lambda item: item.relative_to(root).as_posix()):
        entries.append({
            "path": path.relative_to(root).as_posix(),
            "bytes": path.stat().st_size,
            "sha256": sha256_file(path),
        })
    require(bool(entries), "cache is empty")
    return entries


def aggregate_sha256(entries: list[dict[str, Any]]) -> str:
    return hashlib.sha256(canonical_json_bytes(entries)).hexdigest()


def validate_provenance(provenance: Any) -> dict[str, str]:
    require(isinstance(provenance, dict) and set(provenance) == PROVENANCE_FIELDS,
            "cache provenance has the wrong schema")
    require(COMMIT.fullmatch(provenance["workspace_base_commit"]) is not None,
            "cache provenance workspace commit is malformed")
    for field in PROVENANCE_FIELDS - {"workspace_base_commit"}:
        require(isinstance(provenance[field], str)
                and SHA256.fullmatch(provenance[field]) is not None,
                f"cache provenance {field} is malformed")
    require(provenance["base_image_digest"].startswith("sha256:") is False,
            "cache provenance base image digest must omit the sha256: prefix")
    return provenance


def manifest_for(root: Path, provenance: dict[str, str]) -> dict[str, Any]:
    entries = cache_files(root)
    return {
        "schema_version": SCHEMA_VERSION,
        "suite_id": SUITE_ID,
        "cache_root": ".lake",
        "provenance": validate_provenance(provenance),
        "files": entries,
        "aggregate_sha256": aggregate_sha256(entries),
    }


def validate_manifest_shape(payload: Any) -> dict[str, Any]:
    require(isinstance(payload, dict)
            and set(payload) == {
                "schema_version", "suite_id", "cache_root", "files",
                "aggregate_sha256", "provenance",
            }, "manifest has the wrong top-level schema")
    require(payload["schema_version"] == SCHEMA_VERSION
            and payload["suite_id"] == SUITE_ID
            and payload["cache_root"] == ".lake",
            "manifest identity differs from the frozen checker contract")
    validate_provenance(payload["provenance"])
    files = payload["files"]
    require(isinstance(files, list) and bool(files), "manifest files must be nonempty")
    previous = ""
    for entry in files:
        require(isinstance(entry, dict)
                and set(entry) == {"path", "bytes", "sha256"}
                and isinstance(entry["path"], str)
                and bool(entry["path"])
                and not entry["path"].startswith("/")
                and ".." not in Path(entry["path"]).parts
                and isinstance(entry["bytes"], int)
                and not isinstance(entry["bytes"], bool)
                and entry["bytes"] >= 0
                and isinstance(entry["sha256"], str)
                and SHA256.fullmatch(entry["sha256"]) is not None,
                "manifest contains a malformed file entry")
        require(entry["path"] > previous, "manifest file paths are not strictly sorted")
        previous = entry["path"]
    require(payload["aggregate_sha256"] == aggregate_sha256(files),
            "manifest aggregate digest is invalid")
    return payload


def load_manifest(path: Path) -> dict[str, Any]:
    require(path.is_file() and not path.is_symlink(), "manifest is missing or linked")
    try:
        payload = json.loads(path.read_text(encoding="utf-8"))
    except (UnicodeDecodeError, json.JSONDecodeError) as error:
        raise SystemExit(f"target-drift checker-cache manifest failed: invalid JSON: {error}")
    return validate_manifest_shape(payload)


def write_new(path: Path, payload: dict[str, Any]) -> None:
    require(not path.exists(), f"refusing to overwrite {path}")
    path.parent.mkdir(parents=True, exist_ok=True)
    flags = os.O_WRONLY | os.O_CREAT | os.O_EXCL
    descriptor = os.open(path, flags, 0o644)
    try:
        with os.fdopen(descriptor, "w", encoding="utf-8", newline="\n") as handle:
            json.dump(payload, handle, indent=2, sort_keys=True, ensure_ascii=False)
            handle.write("\n")
    except BaseException:
        path.unlink(missing_ok=True)
        raise


def main() -> None:
    parser = argparse.ArgumentParser()
    subparsers = parser.add_subparsers(dest="command", required=True)
    create = subparsers.add_parser("create")
    create.add_argument("--root", type=Path, required=True)
    create.add_argument("--output", type=Path, required=True)
    create.add_argument("--workspace-base-commit", required=True)
    create.add_argument("--source-files-aggregate-sha256", required=True)
    create.add_argument("--build-input-manifest-sha256", required=True)
    create.add_argument("--checker-image-recipe-sha256", required=True)
    create.add_argument("--base-image-digest", required=True)
    create.add_argument("--lean-toolchain-sha256", required=True)
    verify = subparsers.add_parser("verify")
    verify.add_argument("--root", type=Path, required=True)
    verify.add_argument("--manifest", type=Path, required=True)
    args = parser.parse_args()

    root = args.root.resolve()
    if args.command == "create":
        output = args.output.resolve()
        require(root not in output.parents and output != root,
                "manifest output must not be inside the cache it describes")
        payload = manifest_for(root, {
            "workspace_base_commit": args.workspace_base_commit,
            "source_files_aggregate_sha256": args.source_files_aggregate_sha256,
            "build_input_manifest_sha256": args.build_input_manifest_sha256,
            "checker_image_recipe_sha256": args.checker_image_recipe_sha256,
            "base_image_digest": (
                args.base_image_digest[7:]
                if args.base_image_digest.startswith("sha256:")
                else args.base_image_digest
            ),
            "lean_toolchain_sha256": args.lean_toolchain_sha256,
        })
        write_new(output, payload)
        print(json.dumps({
            "status": "created",
            "manifest": str(output),
            "manifest_sha256": sha256_file(output),
            "files": len(payload["files"]),
            "bytes": sum(item["bytes"] for item in payload["files"]),
        }, sort_keys=True))
        return

    manifest_path = args.manifest.resolve()
    payload = load_manifest(manifest_path)
    actual = manifest_for(root, payload["provenance"])
    require(payload == actual, "cache bytes differ from the frozen manifest")
    print(json.dumps({
        "status": "verified",
        "manifest": str(manifest_path),
        "manifest_sha256": sha256_file(manifest_path),
        "files": len(payload["files"]),
        "bytes": sum(item["bytes"] for item in payload["files"]),
    }, sort_keys=True))


if __name__ == "__main__":
    main()
