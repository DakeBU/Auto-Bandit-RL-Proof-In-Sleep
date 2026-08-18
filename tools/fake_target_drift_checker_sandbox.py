#!/usr/bin/env python3
"""Deterministic host-only fixture for the checker-sandbox protocol.

This script provides no OS isolation and cannot satisfy the production gate.
It exists only to exercise argv, sanitized request, response, artifact, and hash
plumbing on Windows and CI without Docker.
"""

from __future__ import annotations

import argparse
import json
import os
import subprocess
import sys
import tempfile
import time
from pathlib import Path
from typing import Any


TOOLS = Path(__file__).resolve().parent
sys.path.insert(0, str(TOOLS))

import check_target_drift_run as controller  # noqa: E402


def load(path: Path) -> dict[str, Any]:
    return json.loads(path.read_text(encoding="utf-8"))


def dump(path: Path, value: Any) -> None:
    path.write_text(
        json.dumps(value, indent=2, sort_keys=True, ensure_ascii=False) + "\n",
        encoding="utf-8",
    )


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "--action", choices=("run", "cleanup", "inspect", "cleanup-label", "inspect-label"),
        default="run",
    )
    parser.add_argument("--request", type=Path)
    parser.add_argument("--response", type=Path)
    parser.add_argument("--base-snapshot", type=Path)
    parser.add_argument("--patch", type=Path)
    parser.add_argument("--output", type=Path)
    parser.add_argument("--cidfile", type=Path, required=True)
    parser.add_argument("--checker-id")
    parser.add_argument("--checker-version")
    parser.add_argument("--checker-attempt-label")
    parser.add_argument("--image-digest")
    parser.add_argument("--runtime-config-sha256")
    parser.add_argument("--isolation-attestation")
    parser.add_argument("--controller-worker-attestation")
    parser.add_argument("--inner-checker", type=Path)
    parser.add_argument("--inspect-absent-exit-code", type=int, default=3)
    args = parser.parse_args()

    active = args.cidfile.with_name(args.cidfile.name + ".active")
    label_active = args.cidfile.with_name(f"{args.checker_attempt_label}.active")
    if args.action == "inspect":
        raise SystemExit(0 if active.is_file() else args.inspect_absent_exit_code)
    if args.action == "inspect-label":
        raise SystemExit(0 if label_active.is_file() else args.inspect_absent_exit_code)
    if args.action == "cleanup":
        active.unlink(missing_ok=True)
        raise SystemExit(0)
    if args.action == "cleanup-label":
        label_active.unlink(missing_ok=True)
        raise SystemExit(0)

    required = (
        args.request, args.response, args.base_snapshot, args.patch, args.output,
        args.checker_id, args.checker_version, args.image_digest,
        args.checker_attempt_label, args.runtime_config_sha256, args.isolation_attestation,
        args.controller_worker_attestation, args.inner_checker,
    )
    if any(value is None for value in required):
        raise SystemExit("run action requires the complete checker fixture contract")

    request = load(args.request)
    args.cidfile.write_text(f"excluded-fixture-{os.getpid()}\n", encoding="ascii")
    active.write_text("active\n", encoding="ascii")
    label_active.write_text("active\n", encoding="ascii")
    started = time.monotonic()
    with tempfile.TemporaryDirectory(prefix="abrl-checker-fixture-work-") as temporary:
        process = subprocess.run(
            [
                sys.executable,
                str(args.inner_checker.resolve()),
                "--request", str(args.request.resolve()),
                "--base-snapshot", str(args.base_snapshot.resolve()),
                "--patch", str(args.patch.resolve()),
                "--output", str(args.output.resolve()),
                "--work-dir", str(Path(temporary).resolve()),
            ],
            stdout=subprocess.PIPE,
            stderr=subprocess.STDOUT,
            text=True,
            encoding="utf-8",
            errors="replace",
            check=False,
        )
    log_dir = args.output / "logs"
    log_dir.mkdir(exist_ok=True)
    (log_dir / "inner-process.log").write_text(process.stdout, encoding="utf-8")
    if process.returncode != 0:
        raise SystemExit(process.returncode)
    artifacts = controller.regular_artifact_manifest(
        args.output.resolve(), int(request["resource_limits"]["maximum_output_bytes"])
    )
    result_path = args.output / "checker-result.json"
    dump(args.response, {
        "schema_version": 1,
        "opaque_run_id": request["opaque_run_id"],
        "checker_attempt_id": request["checker_attempt_id"],
        "checker_attempt_label": args.checker_attempt_label,
        "request_sha256": controller.sha256(args.request),
        "checker_id": args.checker_id,
        "checker_version": args.checker_version,
        "inner_checker_sha256": controller.sha256(args.inner_checker),
        "checker_contract_sha256": request["checker_contract_sha256"],
        "checker_runtime_config_sha256": args.runtime_config_sha256,
        "container_image_digest": args.image_digest,
        "filesystem_network_process_attestation": args.isolation_attestation,
        "controller_worker_separation_attestation": args.controller_worker_attestation,
        "termination": "completed",
        "checker_result_sha256": controller.sha256(result_path),
        "artifact_manifest": artifacts,
        "artifact_aggregate_sha256": controller.artifact_aggregate(artifacts),
        "process_exit_code": process.returncode,
        "measured_wall_seconds": round(time.monotonic() - started, 6),
    })


if __name__ == "__main__":
    main()
