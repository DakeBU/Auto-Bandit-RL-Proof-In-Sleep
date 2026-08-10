#!/usr/bin/env python3
"""Validate public lemma packets and build their static registry."""

from __future__ import annotations

import argparse
import json
import re
from pathlib import Path
from typing import Any


STATUS = {"proposed", "in-review", "lean-checked", "integrated"}
ID_RE = re.compile(r"^[a-z0-9]+(?:-[a-z0-9]+)*$")


def nested(packet: dict[str, Any], *keys: str) -> Any:
    value: Any = packet
    for key in keys:
        if not isinstance(value, dict) or key not in value:
            return None
        value = value[key]
    return value


def nonempty(packet: dict[str, Any], *keys: str) -> bool:
    value = nested(packet, *keys)
    return isinstance(value, str) and bool(value.strip())


def validate(path: Path, packet: dict[str, Any]) -> list[str]:
    errors: list[str] = []
    packet_id = packet.get("id")
    if packet.get("schema_version") != "1.0":
        errors.append("schema_version must be 1.0")
    if not isinstance(packet_id, str) or not ID_RE.fullmatch(packet_id):
        errors.append("id must be lowercase kebab-case")
    elif path.stem != packet_id:
        errors.append(f"filename must be {packet_id}.json")
    if packet.get("status") not in STATUS:
        errors.append(f"status must be one of {sorted(STATUS)}")
    for keys in [
        ("title",),
        ("domain",),
        ("mathematics", "plain"),
        ("mathematics", "latex"),
        ("provenance", "source"),
        ("contributor", "name"),
        ("contributor", "credit"),
    ]:
        if not nonempty(packet, *keys):
            errors.append(".".join(keys) + " must be filled")
    imports = nested(packet, "lean", "imports")
    code = nested(packet, "lean", "code")
    dependencies = nested(packet, "lean", "dependencies")
    if not isinstance(imports, list) or not all(isinstance(item, str) for item in imports):
        errors.append("lean.imports must be a string array")
    if not isinstance(code, str):
        errors.append("lean.code must be a string")
    if not isinstance(dependencies, list) or not all(isinstance(item, str) for item in dependencies):
        errors.append("lean.dependencies must be a string array")
    if nested(packet, "license", "spdx") != "MIT" or nested(packet, "license", "agreed") is not True:
        errors.append("license must be MIT and license.agreed must be true")
    if packet.get("draft_missing_fields"):
        errors.append("remove draft_missing_fields before submission")
    if packet.get("status") in {"lean-checked", "integrated"} and nested(packet, "verification", "accepted") is not True:
        errors.append("lean-checked and integrated packets require verification.accepted=true")
    return errors


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--root", type=Path, default=Path(__file__).resolve().parent.parent)
    args = parser.parse_args()
    root = args.root.resolve()
    entries_dir = root / "community" / "entries"
    registry_path = root / "community" / "registry.json"
    packets: list[dict[str, Any]] = []
    errors: list[str] = []
    for path in sorted(entries_dir.glob("*.json")):
        try:
            packet = json.loads(path.read_text(encoding="utf-8"))
        except (OSError, json.JSONDecodeError) as error:
            errors.append(f"{path.relative_to(root)}: {error}")
            continue
        if not isinstance(packet, dict):
            errors.append(f"{path.relative_to(root)}: packet root must be an object")
            continue
        for error in validate(path, packet):
            errors.append(f"{path.relative_to(root)}: {error}")
        packets.append(packet)
    ids = [packet.get("id") for packet in packets]
    duplicates = sorted({packet_id for packet_id in ids if ids.count(packet_id) > 1})
    if duplicates:
        errors.append(f"duplicate packet ids: {duplicates}")
    if errors:
        print("COMMUNITY REGISTRY CHECK FAILED")
        for error in errors:
            print(f"- {error}")
        return 1
    payload = {
        "schema_version": "1.0",
        "entry_count": len(packets),
        "entries": sorted(packets, key=lambda packet: packet["id"]),
    }
    registry_path.parent.mkdir(parents=True, exist_ok=True)
    registry_path.write_text(json.dumps(payload, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
    print(f"COMMUNITY REGISTRY PASSED: {len(packets)} packet(s)")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
