#!/usr/bin/env python3
"""Create or verify a physically separate target-drift primary-grader export."""

from __future__ import annotations

import argparse
import hashlib
import json
import sys
from pathlib import Path
from typing import Any


TOOLS = Path(__file__).resolve().parent
sys.path.insert(0, str(TOOLS))

import prepare_target_drift_execution as prepare  # noqa: E402
import prepare_target_drift_grading as grading  # noqa: E402


def load(path: Path) -> dict[str, Any]:
    return json.loads(path.read_text(encoding="utf-8"))


def require(condition: bool, message: str) -> None:
    if not condition:
        raise SystemExit(f"target-drift grader export failed: {message}")


def sha256_file(path: Path) -> str:
    return hashlib.sha256(
        grading.read_plain_file(path, f"sealed-code component {path.name}")
    ).hexdigest()


def verify_runtime(pack: Path) -> dict[str, Any]:
    prepare.verify_pack(pack)
    config = load(pack / "execution_config.json")
    require(config.get("suite_id") == "ABRL-TARGET-DRIFT-V2",
            "grader export requires a v2 pack")
    require(config.get("execution_status") == "frozen_ready",
            "grader export requires a frozen_ready pack")
    require(config["grading"].get("grader_exporter")
            == "tools/export_target_drift_grader_pack.py",
            "frozen config names a different grader exporter")

    current = Path(__file__).resolve()
    sealed_current = pack / "execution_code" / current.name
    require(sealed_current.is_file() and sha256_file(current) == sha256_file(sealed_current),
            "invoked grader exporter differs from the sealed exporter")

    grading_path = Path(grading.__file__).resolve()
    grading_hash = config["grading"]["packet_materializer_sha256"]
    require(sha256_file(grading_path) == grading_hash,
            "imported grading materializer differs from frozen hash")
    require(sha256_file(pack / "execution_code" / grading_path.name) == grading_hash,
            "sealed grading materializer differs from frozen hash")

    prepare_path = Path(prepare.__file__).resolve()
    prepare_hash = config["sealed_agent_view"]["materializer_sha256"]
    require(sha256_file(prepare_path) == prepare_hash,
            "imported pack verifier differs from frozen hash")
    require(sha256_file(pack / "execution_code" / prepare_path.name) == prepare_hash,
            "sealed pack verifier differs from frozen hash")
    return config


def main() -> None:
    parser = argparse.ArgumentParser()
    subparsers = parser.add_subparsers(dest="command", required=True)
    for name in ("create", "verify"):
        command = subparsers.add_parser(name)
        command.add_argument("--pack", type=Path, required=True)
        command.add_argument("--runs-root", type=Path, required=True)
        command.add_argument("--grading-pack", type=Path, required=True)
        if name == "create":
            command.add_argument("--output", type=Path, required=True)
        else:
            command.add_argument("--grader-export", type=Path, required=True)
    args = parser.parse_args()

    pack = args.pack.resolve()
    config = verify_runtime(pack)
    if args.command == "create":
        manifest = grading.materialize_grader_export(
            pack,
            args.runs_root,
            args.grading_pack,
            args.output,
            config,
            expected_count=grading.PRODUCTION_PACKET_COUNT,
        )
        print(
            "materialized physically separate grader-only export: "
            f"packets={manifest['packet_count']}, "
            f"grader_input_sha256={manifest['grader_export_sha256']}, "
            f"non_manifest_export_sha256={manifest['export_aggregate_sha256']}"
        )
    else:
        manifest = grading.validate_grader_export(
            pack,
            args.runs_root,
            args.grading_pack,
            args.grader_export,
            config,
            expected_count=grading.PRODUCTION_PACKET_COUNT,
        )
        print(
            "verified physically separate grader-only export: "
            f"packets={manifest['packet_count']}, "
            f"grader_input_sha256={manifest['grader_export_sha256']}, "
            f"non_manifest_export_sha256={manifest['export_aggregate_sha256']}"
        )


if __name__ == "__main__":
    main()
