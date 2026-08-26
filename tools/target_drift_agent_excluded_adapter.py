#!/usr/bin/env python3
"""Provider-disabled adapter for the agent-container execution component.

This executable deliberately mirrors the production adapter argv and artifact
surface while accepting only one checked-in, result-ineligible request.  It
consumes a fixed fake auth descriptor, performs no subprocess or network call,
and emits zero-usage component evidence.  It is not a model provider, a Lean
formalization run, an infrastructure smoke, or a primary evaluation result.
"""

from __future__ import annotations

import argparse
import errno
import hashlib
import json
import os
import stat
import time
from pathlib import Path
from typing import Any


SUITE_ID = "ABRL-TARGET-DRIFT-V2"
AUTH_FD_ENV = "ABRL_RESULT_FREE_AUTH_FD"
EXPECTED_AUTH = b"RESULT_FREE_SENTINEL_DO_NOT_USE\n"
EXPECTED_MODE = "result_free_excluded_execute_v1"
EXPECTED_REQUEST: dict[str, Any] = {
    "schema_version": 1,
    "suite_id": SUITE_ID,
    "opaque_run_id": "result-free-agent-container-excluded-component",
    "execution_purpose": "agent_container_excluded_provider_component",
    "primary_result_eligible": False,
    "replicate": 0,
    "provider_runtime": {
        "kind": "excluded_fixture",
        "provider_execution_enabled": False,
        "credential_access_allowed": False,
        "network_access_allowed": False,
        "model_call_budget": 0,
    },
    "model": {
        "model_id": "excluded-provider-no-model",
        "immutable_version": "excluded-provider-no-model",
    },
    "pricing": {
        "currency": "USD",
        "unit": "per_million_tokens",
        "input_tokens": 0,
        "cached_input_tokens": 0,
        "cache_write_input_tokens": 0,
        "output_tokens": 0,
    },
    "budgets": {
        "maximum_input_tokens": 0,
        "maximum_output_tokens": 0,
        "maximum_tool_calls": 0,
        "maximum_build_attempts": 0,
        "wall_clock_seconds": 30,
        "maximum_model_retries": 0,
        "maximum_cost_usd": 0,
    },
    "retry_policy": {
        "semantic_failure_retries": 0,
        "infrastructure_retry_limit": 0,
    },
    "result_contract": {
        "agent_output_directory": "/agent/run/output",
        "required_files": [
            "result.json",
            "lean-diff.patch",
            "build.log",
            "explanation.md",
            "workflow-compliance.json",
        ],
        "optional_files": [],
        "workflow_id": "excluded_provider_component",
        "workflow_evidence_files": [],
    },
}
USAGE_INTEGER_FIELDS = (
    "input_tokens", "cached_input_tokens", "cache_write_input_tokens",
    "output_tokens", "reasoning_output_tokens", "tool_calls",
    "build_attempts", "recovery_tool_calls", "infrastructure_retries",
)


def require(condition: bool, message: str) -> None:
    if not condition:
        raise SystemExit(f"target-drift excluded adapter failed: {message}")


def sha256_bytes(payload: bytes) -> str:
    return hashlib.sha256(payload).hexdigest()


def regular_file(path: Path, label: str) -> Path:
    require(path.is_file() and not path.is_symlink(), f"{label} is not a plain file")
    info = path.lstat()
    require(stat.S_ISREG(info.st_mode) and info.st_nlink == 1,
            f"{label} is linked or special")
    return path


def read_json(path: Path, label: str) -> tuple[dict[str, Any], bytes]:
    payload = regular_file(path, label).read_bytes()
    try:
        value = json.loads(payload.decode("utf-8", errors="strict"))
    except (UnicodeDecodeError, json.JSONDecodeError) as error:
        raise SystemExit(
            f"target-drift excluded adapter failed: invalid {label} JSON"
        ) from error
    require(isinstance(value, dict), f"{label} must be one JSON object")
    return value, payload


def write_new_bytes(path: Path, payload: bytes) -> None:
    require(path.parent.is_dir() and not path.parent.is_symlink(),
            f"output parent is absent or linked: {path.name}")
    descriptor = os.open(path, os.O_WRONLY | os.O_CREAT | os.O_EXCL, 0o600)
    with os.fdopen(descriptor, "wb") as stream:
        stream.write(payload)
        stream.flush()
        os.fsync(stream.fileno())


def write_new_text(path: Path, text: str) -> None:
    write_new_bytes(path, text.encode("utf-8"))


def write_new_json(path: Path, value: Any) -> None:
    write_new_text(
        path,
        json.dumps(value, indent=2, sort_keys=True, ensure_ascii=False) + "\n",
    )


def validate_request(request: dict[str, Any]) -> None:
    require(request == EXPECTED_REQUEST,
            "request differs from the single excluded-provider component fixture")


def consume_brokered_fake_auth() -> dict[str, Any]:
    raw_descriptor = os.environ.pop(AUTH_FD_ENV, None)
    require(
        isinstance(raw_descriptor, str)
        and raw_descriptor.isdecimal()
        and str(int(raw_descriptor)) == raw_descriptor
        and int(raw_descriptor) >= 3,
        "one canonical fake-auth descriptor was not supplied",
    )
    descriptor = int(raw_descriptor)
    info = os.fstat(descriptor)
    require(stat.S_ISREG(info.st_mode) and info.st_nlink == 1,
            "fake-auth descriptor is not one regular file")
    try:
        os.write(descriptor, b"forbidden")
    except OSError as error:
        write_errno = error.errno
    else:
        write_errno = None
    require(write_errno == errno.EBADF, "fake-auth descriptor is writable")
    payload = bytearray()
    try:
        while len(payload) <= len(EXPECTED_AUTH):
            block = os.read(descriptor, len(EXPECTED_AUTH) + 1 - len(payload))
            if not block:
                break
            payload.extend(block)
    finally:
        os.close(descriptor)
    require(bytes(payload) == EXPECTED_AUTH, "fake-auth descriptor bytes differ")
    try:
        os.fstat(descriptor)
    except OSError as error:
        closed_errno = error.errno
    else:
        closed_errno = None
    require(closed_errno == errno.EBADF, "fake-auth descriptor remained open")
    return {
        "bytes": len(payload),
        "sha256": sha256_bytes(bytes(payload)),
        "read_only_descriptor": True,
        "descriptor_closed_before_adapter_work": True,
        "environment_marker_removed_before_adapter_work": AUTH_FD_ENV not in os.environ,
    }


def read_denial_errno(path: Path) -> int | None:
    try:
        path.read_bytes()
    except OSError as error:
        return error.errno
    return None


def file_manifest(root: Path) -> list[dict[str, Any]]:
    records: list[dict[str, Any]] = []
    for path in sorted(root.iterdir(), key=lambda item: item.name):
        regular_file(path, f"component output {path.name}")
        payload = path.read_bytes()
        records.append({
            "path": path.name,
            "bytes": len(payload),
            "sha256": sha256_bytes(payload),
        })
    return records


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
            "excluded-execution component mode is absent")
    agent = args.agent_mount.resolve()
    require(agent.is_dir() and not agent.is_symlink(), "agent mount is not a plain directory")
    request_path = args.request.resolve()
    require(request_path == agent / "request.json", "request is outside the agent mount")
    response_path = args.response.resolve()
    trace_path = args.trace.resolve()
    require(response_path.parent == agent / "adapter"
            and trace_path.parent == agent / "adapter"
            and response_path.name == "response.json"
            and trace_path.name == "trace.jsonl",
            "adapter evidence paths differ from the fixed component layout")
    request, request_bytes = read_json(request_path, "sealed request")
    require(sha256_bytes(request_bytes) == args.request_sha256,
            "sealed request hash differs from the invocation contract")
    validate_request(request)
    require(args.adapter_id == "abrl-agent-excluded-component"
            and args.adapter_version == "1"
            and args.model_id == request["model"]["model_id"]
            and args.immutable_model_version == request["model"]["immutable_version"],
            "adapter or excluded-model identity differs")
    require(args.budget_attestation == "zero-provider-zero-model-zero-cost"
            and args.isolation_attestation
            == "network-none-fixed-fake-auth-result-ineligible",
            "component attestations differ")
    require(args.image_digest.startswith("sha256:") and len(args.image_digest) == 71,
            "component image digest is malformed")

    started = time.monotonic()
    handoff = consume_brokered_fake_auth()
    auth_errno = read_denial_errno(Path("/run/secrets/provider-auth"))
    control_errno = read_denial_errno(Path("/control/root-only-sentinel"))
    require(auth_errno in {errno.EACCES, errno.EPERM}
            and control_errno in {errno.EACCES, errno.EPERM},
            "worker can read the outer auth or root-control mount")

    adapter_dir = agent / "adapter"
    output = agent / "output"
    require(not adapter_dir.exists() and not output.exists(),
            "adapter/output surface already exists")
    adapter_dir.mkdir(mode=0o700)
    output.mkdir(mode=0o700)
    write_new_json(output / "result.json", {
        "schema_version": 1,
        "opaque_run_id": request["opaque_run_id"],
        "final_status": "blocked",
        "public_declarations": [],
        "primary_grader_rationale": (
            "Provider-disabled agent-container component only; no Lean target, "
            "model call, build, or formalization result was attempted."
        ),
    })
    write_new_text(output / "lean-diff.patch", "")
    write_new_text(
        output / "build.log",
        "Excluded-provider agent-container component: no Lean build executed.\n",
    )
    write_new_text(
        output / "explanation.md",
        "Result-ineligible excluded-provider component evidence; no model result.\n",
    )
    write_new_json(output / "workflow-compliance.json", {
        "schema_version": 1,
        "opaque_run_id": request["opaque_run_id"],
        "workflow_id": request["result_contract"]["workflow_id"],
        "evidence_files": [],
        "component_only": True,
        "primary_result_eligible": False,
    })

    wall = round(max(0.0, time.monotonic() - started), 6)
    usage: dict[str, int | float] = {field: 0 for field in USAGE_INTEGER_FIELDS}
    usage["wall_seconds"] = wall
    usage["cost_usd"] = 0.0
    trace = [{"sequence": 0, "kind": "usage_summary", "usage": usage}]
    trace_bytes = (
        json.dumps(trace[0], sort_keys=True, separators=(",", ":")) + "\n"
    ).encode("utf-8")
    write_new_bytes(trace_path, trace_bytes)
    response = {
        "schema_version": 1,
        "opaque_run_id": request["opaque_run_id"],
        "adapter_id": args.adapter_id,
        "adapter_version": args.adapter_version,
        "model_id": args.model_id,
        "immutable_model_version": args.immutable_model_version,
        "replicate": request["replicate"],
        "container_or_sandbox_image_digest": args.image_digest,
        "budget_enforcement_attestation": args.budget_attestation,
        "filesystem_network_process_attestation": args.isolation_attestation,
        "termination": "completed",
        "model_invocations": [{
            "attempt": 1,
            "transport": "excluded_fixture",
            "observable_id_kind": "fixture",
            "observable_id": "excluded-provider-agent-container-component",
            "process_exit_code": 0,
            "wall_seconds": wall,
            "usage_observed": True,
        }],
        "usage": usage,
    }
    write_new_json(response_path, response)
    output_manifest = file_manifest(output)
    attestation = {
        "schema_version": 1,
        "suite_id": SUITE_ID,
        "status": "passed_result_free_excluded_adapter_component",
        "primary_result_eligible": False,
        "provider_execution_enabled": False,
        "provider_request_or_model_invocation_occurred": False,
        "network_access_allowed": False,
        "fake_auth_handoff": handoff,
        "outer_auth_read_errno": auth_errno,
        "root_control_read_errno": control_errno,
        "request_sha256": sha256_bytes(request_bytes),
        "response_sha256": sha256_bytes(response_path.read_bytes()),
        "trace_sha256": sha256_bytes(trace_bytes),
        "output_manifest": output_manifest,
    }
    print(json.dumps(attestation, sort_keys=True, separators=(",", ":")), flush=True)


if __name__ == "__main__":
    main()
