#!/usr/bin/env python3
"""Credential broker and adapter driver for the production-action candidate.

Only the fixed, offline fixture mode is enabled in tracked source.  It consumes
the root-brokered fake ``auth.json`` descriptor, materializes that one file in
worker-owned tmpfs for the trusted Codex adapter, launches the in-image
``codex_target_drift_adapter.py`` with sealed argv, removes the temporary auth
copy, and reports hashes of result-free artifacts.  Real production execution
is intentionally absent until the external final-image gate is satisfied.
"""

from __future__ import annotations

import argparse
import errno
import hashlib
import json
import os
import stat
import subprocess
from pathlib import Path
from typing import Any


SUITE_ID = "ABRL-TARGET-DRIFT-V2"
EXPECTED_MODE = "result_free_production_action_fixture_v1"
AUTH_FD_ENV = "ABRL_RESULT_FREE_AUTH_FD"
EXPECTED_AUTH = b"RESULT_FREE_SENTINEL_DO_NOT_USE\n"
ADAPTER = Path("/usr/local/lib/abrl/codex_target_drift_adapter.py")
MAX_ADAPTER_OUTPUT_BYTES = 1024 * 1024


def require(condition: bool, message: str) -> None:
    if not condition:
        raise SystemExit(f"target-drift agent action driver failed: {message}")


def regular_single_file(path: Path, label: str) -> Path:
    info = path.lstat()
    require(stat.S_ISREG(info.st_mode) and not path.is_symlink()
            and info.st_nlink == 1, f"{label} is not one regular nonlink file")
    return path


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def file_manifest(directory: Path) -> list[dict[str, Any]]:
    require(directory.is_dir() and not directory.is_symlink(),
            "adapter output is not a plain directory")
    records: list[dict[str, Any]] = []
    for path in sorted(directory.iterdir(), key=lambda item: item.name):
        regular_single_file(path, f"adapter output {path.name}")
        payload = path.read_bytes()
        records.append({
            "path": path.name,
            "bytes": len(payload),
            "sha256": hashlib.sha256(payload).hexdigest(),
        })
    return records


def consume_fake_auth(target: Path) -> dict[str, Any]:
    descriptor_text = os.environ.pop(AUTH_FD_ENV, "")
    require(descriptor_text.isascii() and descriptor_text.isdigit(),
            "brokered auth descriptor is absent or malformed")
    descriptor = int(descriptor_text)
    info = os.fstat(descriptor)
    require(stat.S_ISREG(info.st_mode) and info.st_nlink == 1,
            "brokered auth descriptor is not one regular file")
    try:
        os.write(descriptor, b"forbidden")
    except OSError as error:
        write_errno = error.errno
    else:
        write_errno = None
    require(write_errno == errno.EBADF,
            "brokered auth descriptor is not read-only")
    chunks: list[bytes] = []
    try:
        while True:
            block = os.read(descriptor, 4096)
            if not block:
                break
            chunks.append(block)
            require(sum(len(item) for item in chunks) <= 4096,
                    "brokered auth fixture exceeds its size ceiling")
    finally:
        os.close(descriptor)
    payload = b"".join(chunks)
    require(payload == EXPECTED_AUTH,
            "only the fixed fake auth fixture is accepted")
    require(not target.exists(), "temporary provider auth directory already exists")
    target.mkdir(mode=0o700)
    auth = target / "auth.json"
    with auth.open("xb") as stream:
        stream.write(payload)
        stream.flush()
        os.fsync(stream.fileno())
    auth.chmod(0o400)
    return {
        "bytes": len(payload),
        "sha256": hashlib.sha256(payload).hexdigest(),
        "read_only_descriptor": True,
        "descriptor_closed_before_adapter_launch": True,
        "environment_marker_removed_before_adapter_launch": True,
    }


def remove_auth_tree(directory: Path) -> None:
    auth = regular_single_file(directory / "auth.json", "temporary auth.json")
    auth.chmod(0o600)
    auth.unlink()
    directory.rmdir()


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--request", type=Path, required=True)
    parser.add_argument("--response", type=Path, required=True)
    parser.add_argument("--trace", type=Path, required=True)
    parser.add_argument("--agent-mount", type=Path, required=True)
    parser.add_argument("--adapter-id", required=True)
    parser.add_argument("--adapter-version", required=True)
    parser.add_argument("--model-id", required=True)
    parser.add_argument("--immutable-model-version", required=True)
    parser.add_argument("--image-digest", required=True)
    parser.add_argument("--budget-attestation", required=True)
    parser.add_argument("--isolation-attestation", required=True)
    parser.add_argument("--request-sha256", required=True)
    args = parser.parse_args()

    require(os.environ.get("ABRL_OUTER_COMPONENT_MODE") == EXPECTED_MODE,
            "only the fixed result-free fixture mode is enabled")
    require(ADAPTER.is_file() and not ADAPTER.is_symlink(),
            "in-image Codex adapter is absent or linked")
    request = regular_single_file(args.request, "fixture request")
    require(sha256(request) == args.request_sha256,
            "fixture request differs from the sealed hash")
    agent = args.agent_mount.resolve()
    require(agent == Path("/agent/run") and request.resolve() == agent / "request.json",
            "fixture agent or request path differs")
    adapter_evidence = agent / "adapter"
    require(args.response.parent.resolve() == adapter_evidence
            and args.trace.parent.resolve() == adapter_evidence
            and not adapter_evidence.exists(),
            "fixture adapter evidence paths differ or already exist")
    adapter_evidence.mkdir(mode=0o700)
    provider_auth = Path("/codex-home/provider-auth")
    handoff = consume_fake_auth(provider_auth)
    command = [
        "/usr/bin/python3", str(ADAPTER),
        "--request", str(args.request),
        "--response", str(args.response),
        "--trace", str(args.trace),
        "--agent-mount", str(args.agent_mount),
        "--adapter-id", args.adapter_id,
        "--adapter-version", args.adapter_version,
        "--model-id", args.model_id,
        "--immutable-model-version", args.immutable_model_version,
        "--image-digest", args.image_digest,
        "--budget-attestation", args.budget_attestation,
        "--isolation-attestation", args.isolation_attestation,
    ]
    environment = {
        "PATH": "/usr/local/bin:/usr/bin:/bin",
        "HOME": "/tmp",
        "CODEX_HOME": "/codex-home",
        "PYTHONDONTWRITEBYTECODE": "1",
        "LANG": "C.UTF-8",
        "ABRL_OUTER_COMPONENT_MODE": EXPECTED_MODE,
    }
    try:
        outcome = subprocess.run(
            command, stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
            check=False, timeout=45, env=environment,
        )
    finally:
        remove_auth_tree(provider_auth)
    require(len(outcome.stdout) <= MAX_ADAPTER_OUTPUT_BYTES,
            "adapter diagnostic output is oversized")
    if outcome.returncode != 0:
        os.write(2, outcome.stdout)
    require(outcome.returncode == 0,
            f"in-image Codex adapter failed with exit {outcome.returncode}")
    response = regular_single_file(args.response, "adapter response")
    trace = regular_single_file(args.trace, "adapter trace")
    attestation = {
        "schema_version": 1,
        "suite_id": SUITE_ID,
        "status": "passed_result_free_production_action_driver_fixture",
        "primary_result_eligible": False,
        "provider_execution_enabled": False,
        "provider_request_or_model_invocation_occurred": False,
        "network_access_allowed": False,
        "adapter_path": str(ADAPTER),
        "adapter_sha256": sha256(ADAPTER),
        "request_sha256": sha256(request),
        "response_sha256": sha256(response),
        "trace_sha256": sha256(trace),
        "output_manifest": file_manifest(agent / "output"),
        "fake_auth_handoff": handoff,
        "temporary_auth_removed": not provider_auth.exists(),
    }
    print(json.dumps(attestation, sort_keys=True, separators=(",", ":")), flush=True)


if __name__ == "__main__":
    main()
