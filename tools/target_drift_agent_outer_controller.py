#!/usr/bin/env python3
"""Trusted root controller for result-free agent-boundary components.

The controller accepts no caller-supplied command.  It copies one read-only
agent-input tree into disposable tmpfs and brokers one read-only fake
``auth.json`` descriptor to a child that is irreversibly dropped to uid/gid
10002.  The root parent closes its descriptor as soon as the child exists,
validates either the fixed offline probe or one sealed excluded-provider adapter
execution, and writes only root-control evidence.  Neither mode accepts a real
credential or permits a provider/model call.
"""

from __future__ import annotations

import errno
import hashlib
import json
import os
import re
import shutil
import stat
import subprocess
import sys
from pathlib import Path
from typing import Any


INPUT_ROOT = Path("/input/agent")
AUTH_SOURCE = Path("/run/secrets/provider-auth")
WORKSPACE = Path("/agent")
CODEX_HOME = Path("/codex-home")
CONTROL = Path("/control")
WORKER_UID = 10002
WORKER_GID = 10002
MAX_INPUT_FILES = 64
MAX_INPUT_BYTES = 4 * 1024 * 1024
WORKER_PROBE = "/usr/local/lib/abrl/target_drift_agent_outer_probe.py"
EXCLUDED_ADAPTER = "/usr/local/lib/abrl/target_drift_agent_excluded_adapter.py"
EXCLUDED_CONTRACT = Path(
    "/usr/local/share/abrl/agent-excluded-execution-contract.json"
)
CONTROL_SENTINEL = CONTROL / "root-only-sentinel"
CONTROL_SENTINEL_BYTES = b"RESULT_FREE_ROOT_CONTROL_SENTINEL\n"
MAX_DIAGNOSTIC_BYTES = 8192
AUTH_FD_ENV = "ABRL_RESULT_FREE_AUTH_FD"
EXPECTED_AUTH = b"RESULT_FREE_SENTINEL_DO_NOT_USE\n"
PROBE_MODE = "result_free_probe_v1"
EXCLUDED_EXECUTE_MODE = "result_free_excluded_execute_v1"
IMAGE_DIGEST_ENV = "ABRL_OUTER_COMPONENT_IMAGE_DIGEST"


def require(condition: bool, message: str) -> None:
    if not condition:
        raise SystemExit(f"target-drift agent outer controller failed: {message}")


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def regular_single_file(path: Path, label: str) -> Path:
    info = path.lstat()
    require(stat.S_ISREG(info.st_mode) and not path.is_symlink()
            and info.st_nlink == 1, f"{label} is not one regular nonlink file")
    return path


def copy_agent_input(source: Path, target: Path) -> list[dict[str, Any]]:
    require(source.is_dir() and not source.is_symlink(),
            "agent input is not a plain directory")
    target.mkdir(mode=0o700)
    records: list[dict[str, Any]] = []
    total = 0
    for path in sorted(source.rglob("*"), key=lambda item: item.as_posix()):
        relative = path.relative_to(source)
        require(".." not in relative.parts, "agent input contains unsafe path")
        destination = target / relative
        info = path.lstat()
        require(not path.is_symlink(), "agent input contains a symbolic link")
        if stat.S_ISDIR(info.st_mode):
            destination.mkdir(mode=0o700)
            continue
        require(stat.S_ISREG(info.st_mode) and info.st_nlink == 1,
                "agent input contains a linked or special file")
        total += info.st_size
        require(len(records) < MAX_INPUT_FILES and total <= MAX_INPUT_BYTES,
                "agent input exceeds the component ceiling")
        with path.open("rb") as source_stream, destination.open("xb") as target_stream:
            shutil.copyfileobj(source_stream, target_stream, 1024 * 1024)
        require(destination.stat().st_size == info.st_size,
                "agent input copy changed size")
        records.append({
            "path": relative.as_posix(), "bytes": info.st_size,
            "sha256": sha256(destination),
        })
    require(records == [{
        "path": "input.txt", "bytes": len(b"RESULT_FREE_AGENT_INPUT\n"),
        "sha256": hashlib.sha256(b"RESULT_FREE_AGENT_INPUT\n").hexdigest(),
    }], "component probe accepts exactly the frozen fake agent input")
    return records


def load_excluded_contract(
    contract_path: Path = EXCLUDED_CONTRACT,
    adapter_path: Path = Path(EXCLUDED_ADAPTER),
) -> dict[str, Any]:
    contract = json.loads(
        regular_single_file(contract_path, "excluded-execution contract").read_text(
            encoding="utf-8"
        )
    )
    require(
        contract.get("schema_version") == 1
        and contract.get("suite_id") == "ABRL-TARGET-DRIFT-V2"
        and contract.get("status")
        == "result_free_excluded_provider_component_contract"
        and contract.get("execution_mode") == EXCLUDED_EXECUTE_MODE
        and contract.get("execution_status_boundary")
        == "primary_execution_not_started"
        and contract.get("primary_result_eligible") is False
        and contract.get("provider_execution_enabled") is False,
        "excluded-execution contract identity or evidence boundary differs",
    )
    request = contract.get("request", {})
    adapter = contract.get("adapter", {})
    require(
        request.get("container_path") == "/agent/run/request.json"
        and isinstance(request.get("sha256"), str)
        and len(request["sha256"]) == 64
        and adapter.get("container_path") == EXCLUDED_ADAPTER
        and isinstance(adapter.get("sha256"), str)
        and adapter["sha256"] == sha256(
            regular_single_file(adapter_path, "excluded-execution adapter")
        )
        and adapter.get("adapter_id") == "abrl-agent-excluded-component"
        and adapter.get("adapter_version") == "1",
        "excluded-execution request or adapter binding differs",
    )
    argv = adapter.get("argv")
    require(
        isinstance(argv, list)
        and all(isinstance(item, str) and item for item in argv)
        and argv[:2] == ["/usr/bin/python3", EXCLUDED_ADAPTER]
        and argv.count("{{IMAGE_DIGEST}}") == 1,
        "excluded-execution adapter argv is malformed",
    )
    return contract


def copy_excluded_request(
    source: Path, target: Path, contract: dict[str, Any],
) -> list[dict[str, Any]]:
    require(source.is_dir() and not source.is_symlink(),
            "excluded-execution input is not a plain directory")
    members = list(source.iterdir())
    require(len(members) == 1 and members[0].name == "request.json",
            "excluded-execution input accepts exactly request.json")
    request = regular_single_file(members[0], "excluded-execution request")
    payload = request.read_bytes()
    require(hashlib.sha256(payload).hexdigest() == contract["request"]["sha256"],
            "excluded-execution request differs from the sealed contract")
    decoded = json.loads(payload.decode("utf-8", errors="strict"))
    require(
        decoded.get("suite_id") == "ABRL-TARGET-DRIFT-V2"
        and decoded.get("execution_purpose")
        == "agent_container_excluded_provider_component"
        and decoded.get("primary_result_eligible") is False
        and decoded.get("provider_runtime", {}).get("kind") == "excluded_fixture"
        and decoded.get("provider_runtime", {}).get(
            "provider_execution_enabled"
        ) is False
        and decoded.get("provider_runtime", {}).get("credential_access_allowed")
        is False
        and decoded.get("provider_runtime", {}).get("network_access_allowed")
        is False
        and decoded.get("provider_runtime", {}).get("model_call_budget") == 0,
        "excluded-execution request weakens the provider/result boundary",
    )
    target.mkdir(mode=0o700)
    target_request = target / "request.json"
    with request.open("rb") as source_stream, target_request.open("xb") as target_stream:
        shutil.copyfileobj(source_stream, target_stream, 1024 * 1024)
    return [{
        "path": "request.json",
        "bytes": len(payload),
        "sha256": hashlib.sha256(payload).hexdigest(),
    }]


def source_is_read_only(path: Path) -> bool:
    try:
        descriptor = os.open(path, os.O_WRONLY | os.O_APPEND)
    except OSError as error:
        return error.errno in {errno.EROFS, errno.EACCES, errno.EPERM}
    else:
        os.close(descriptor)
        return False


def drop_worker() -> None:
    os.setgroups([])
    os.setgid(WORKER_GID)
    os.setuid(WORKER_UID)
    os.umask(0o077)


def dump_atomic(path: Path, payload: Any) -> None:
    temporary = path.with_name(path.name + ".tmp")
    with temporary.open("x", encoding="utf-8", newline="\n") as stream:
        json.dump(payload, stream, indent=2, sort_keys=True)
        stream.write("\n")
        stream.flush()
        os.fsync(stream.fileno())
    os.replace(temporary, path)


def persist_worker_failure(
    control: Path, return_code: int, output: bytes,
) -> None:
    """Persist bounded result-free diagnostics without echoing fake inputs."""
    require(len(output) <= 1024 * 1024, "worker output is oversized")
    diagnostic = output[-MAX_DIAGNOSTIC_BYTES:].decode(
        "utf-8", errors="backslashreplace"
    ).replace(
        "RESULT_FREE_SENTINEL_DO_NOT_USE", "<fixed-fake-auth-sentinel>"
    ).replace(
        "RESULT_FREE_AGENT_INPUT", "<fixed-fake-agent-input>"
    )
    payload = {
        "schema_version": 1,
        "suite_id": "ABRL-TARGET-DRIFT-V2",
        "status": "failed_result_free_worker_component",
        "return_code": return_code,
        "stdout_bytes": len(output),
        "stdout_sha256": hashlib.sha256(output).hexdigest(),
        "diagnostic_tail": diagnostic,
    }
    dump_atomic(control / "worker-probe-failure.json", payload)
    sys.stderr.write("result-free worker diagnostic tail:\n" + diagnostic + "\n")
    sys.stderr.flush()


def run_worker_with_brokered_auth(
    auth_descriptor: int, environment: dict[str, str],
    command: list[str] | None = None, timeout_seconds: int = 45,
) -> subprocess.CompletedProcess[bytes]:
    command = command or ["/usr/bin/python3", WORKER_PROBE]
    require(command and all(isinstance(item, str) and item for item in command),
            "worker command is malformed")
    try:
        process = subprocess.Popen(
            command, preexec_fn=drop_worker,
            pass_fds=(auth_descriptor,), env=environment,
            stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
        )
    finally:
        # Popen returns only after the fork/exec error pipe closes.  The child
        # owns the sole remaining descriptor before it can launch Codex.
        os.close(auth_descriptor)
    try:
        output, _ = process.communicate(timeout=timeout_seconds)
    except subprocess.TimeoutExpired:
        process.kill()
        output, _ = process.communicate()
        persist_worker_failure(CONTROL, process.returncode, output)
        raise SystemExit(
            "target-drift agent outer controller failed: worker timed out"
        )
    return subprocess.CompletedProcess(command, process.returncode, output)


def run_component_probe() -> None:
    require(os.geteuid() == 0 and os.getegid() == 0,
            "controller must start as root")
    require(CONTROL.is_dir() and not CONTROL.is_symlink(),
            "root control output is not a plain directory")
    CONTROL.chmod(0o700)
    require(WORKSPACE.is_dir() and CODEX_HOME.is_dir(),
            "disposable tmpfs mounts are absent")
    auth = regular_single_file(AUTH_SOURCE, "outer auth sentinel")
    require(auth.read_bytes() == EXPECTED_AUTH,
            "only the frozen fake auth sentinel is accepted")
    auth_read_only = source_is_read_only(auth)
    input_read_only = source_is_read_only(INPUT_ROOT / "input.txt")
    require(auth_read_only and input_read_only,
            "outer auth and agent input must be mounted read-only")
    with CONTROL_SENTINEL.open("xb") as stream:
        stream.write(CONTROL_SENTINEL_BYTES)
        stream.flush()
        os.fsync(stream.fileno())
    CONTROL_SENTINEL.chmod(0o400)
    control_sentinel_info = CONTROL_SENTINEL.lstat()
    require(stat.S_ISREG(control_sentinel_info.st_mode)
            and control_sentinel_info.st_uid == 0
            and control_sentinel_info.st_gid == 0
            and stat.S_IMODE(control_sentinel_info.st_mode) == 0o400,
            "root control sentinel identity or mode differs")
    copied_records = copy_agent_input(INPUT_ROOT, WORKSPACE / "input")
    for path in [WORKSPACE, *(WORKSPACE.rglob("*"))]:
        os.chown(path, WORKER_UID, WORKER_GID)
    auth_descriptor = os.open(
        auth, os.O_RDONLY | getattr(os, "O_CLOEXEC", 0)
    )
    worker_environment = os.environ.copy()
    worker_environment[AUTH_FD_ENV] = str(auth_descriptor)
    outcome = run_worker_with_brokered_auth(
        auth_descriptor, worker_environment
    )
    require(len(outcome.stdout) <= 1024 * 1024, "worker output is oversized")
    if outcome.returncode != 0:
        persist_worker_failure(CONTROL, outcome.returncode, outcome.stdout)
    require(outcome.returncode == 0,
            f"fixed worker probe failed with exit {outcome.returncode}")
    observation_path = regular_single_file(
        WORKSPACE / "worker-observation.json", "worker observation"
    )
    observation = json.loads(observation_path.read_text(encoding="utf-8"))
    require(observation.get("status") == "passed_result_free_worker_component"
            and observation.get("worker_uid") == WORKER_UID
            and observation.get("worker_gid") == WORKER_GID
            and int(observation.get("worker_effective_capabilities_hex", "1"), 16) == 0,
            "worker observation does not prove the fixed privilege boundary")
    model = observation.get("model_shell", {})
    require(isinstance(model, dict)
            and model.get("trusted_auth_fd_env_absent") is True
            and model.get("trusted_auth_fd_target_absent") is True
            and model.get("outer_auth_mount_unreadable") is True
            and model.get("outer_auth_mount_read_errno")
            in {errno.EACCES, errno.EPERM}
            and model.get("root_control_output_unreadable") is True
            and model.get("root_control_output_read_errno")
            in {errno.EACCES, errno.EPERM}
            and int(model.get("effective_capabilities_hex", "1"), 16) == 0,
            "nested shell could observe an outer secret/control path")
    handoff = observation.get("trusted_client_fake_auth_handoff", {})
    require(isinstance(handoff, dict)
            and handoff.get("bytes") == len(EXPECTED_AUTH)
            and handoff.get("sha256")
            == hashlib.sha256(EXPECTED_AUTH).hexdigest()
            and handoff.get("read_only_descriptor") is True
            and handoff.get("descriptor_closed_before_sandbox") is True
            and handoff.get("environment_marker_removed_before_sandbox") is True,
            "worker report does not prove the one-time fake-auth handoff")
    report = {
        "schema_version": 1,
        "suite_id": "ABRL-TARGET-DRIFT-V2",
        "status": "passed_result_free_outer_boundary_component",
        "controller_pid": os.getpid(),
        "controller_parent_pid": os.getppid(),
        "controller_uid": os.geteuid(),
        "controller_gid": os.getegid(),
        "worker_uid": WORKER_UID,
        "worker_gid": WORKER_GID,
        "outer_auth_single_read_only_file": auth_read_only,
        "agent_input_single_tree_read_only": input_read_only,
        "agent_input_copy_manifest": copied_records,
        "root_control_sentinel": {
            "path": str(CONTROL_SENTINEL),
            "mode": "0400",
            "uid": control_sentinel_info.st_uid,
            "gid": control_sentinel_info.st_gid,
            "bytes": len(CONTROL_SENTINEL_BYTES),
            "sha256": hashlib.sha256(CONTROL_SENTINEL_BYTES).hexdigest(),
        },
        "disposable_codex_home": str(CODEX_HOME),
        "trusted_client_fake_auth_handoff": observation.get(
            "trusted_client_fake_auth_handoff"
        ),
        "disposable_agent_workspace": str(WORKSPACE),
        "worker_observation": observation,
        "nonclaims": [
            "The auth file is a fixed fake sentinel; no provider credential was used.",
            "The one-time read-only file-descriptor handoff is a component probe, not the Codex provider authentication path.",
            "Codex sandbox was exercised offline; no model invocation occurred.",
            "This component probe does not publish or seal a production agent image."
        ],
    }
    dump_atomic(CONTROL / "controller-report.json", report)


def load_json_artifact(path: Path, label: str) -> dict[str, Any]:
    try:
        value = json.loads(regular_single_file(path, label).read_text(encoding="utf-8"))
    except (UnicodeDecodeError, json.JSONDecodeError) as error:
        raise SystemExit(
            f"target-drift agent outer controller failed: invalid {label} JSON"
        ) from error
    require(isinstance(value, dict), f"{label} must be one JSON object")
    return value


def excluded_output_manifest(
    output: Path, expected_names: set[str], *, expected_uid: int | None = None,
) -> list[dict[str, Any]]:
    require(output.is_dir() and not output.is_symlink(),
            "excluded adapter output is not a plain directory")
    members = {path.name: path for path in output.iterdir()}
    require(set(members) == expected_names,
            "excluded adapter output file set differs from the contract")
    records: list[dict[str, Any]] = []
    for name, path in sorted(members.items()):
        regular_single_file(path, f"excluded adapter output {name}")
        info = path.lstat()
        if expected_uid is not None:
            require(info.st_uid == expected_uid,
                    f"excluded adapter output owner differs: {name}")
        payload = path.read_bytes()
        records.append({
            "path": name,
            "bytes": len(payload),
            "sha256": hashlib.sha256(payload).hexdigest(),
        })
    return records


def validate_excluded_execution_artifacts(
    run_root: Path, contract: dict[str, Any], request: dict[str, Any],
    worker_output: bytes, *, expected_uid: int | None = None,
) -> dict[str, Any]:
    """Validate the complete provider-disabled response/trace/output surface."""
    require(len(worker_output) <= 1024 * 1024,
            "excluded adapter stdout is oversized")
    lines = worker_output.decode("utf-8", errors="strict").splitlines()
    require(len(lines) == 1 and lines[0],
            "excluded adapter must emit one attestation JSON line")
    attestation = json.loads(lines[0])
    require(isinstance(attestation, dict), "excluded adapter attestation is not an object")
    adapter_dir = run_root / "adapter"
    require(adapter_dir.is_dir() and not adapter_dir.is_symlink(),
            "excluded adapter evidence directory is absent or linked")
    adapter_members = {path.name: path for path in adapter_dir.iterdir()}
    require(set(adapter_members) == {"response.json", "trace.jsonl"},
            "excluded adapter evidence file set differs")
    for name, path in adapter_members.items():
        regular_single_file(path, f"excluded adapter {name}")
        if expected_uid is not None:
            require(path.lstat().st_uid == expected_uid,
                    f"excluded adapter evidence owner differs: {name}")
    response_path = adapter_members["response.json"]
    trace_path = adapter_members["trace.jsonl"]
    response = load_json_artifact(response_path, "excluded adapter response")
    trace_lines = trace_path.read_text(encoding="utf-8").splitlines()
    require(len(trace_lines) == 1 and trace_lines[0],
            "excluded adapter trace must contain one event")
    trace = [json.loads(trace_lines[0])]
    usage = response.get("usage")
    zero_fields = {
        "input_tokens", "cached_input_tokens", "cache_write_input_tokens",
        "output_tokens", "reasoning_output_tokens", "tool_calls",
        "build_attempts", "recovery_tool_calls", "infrastructure_retries",
        "cost_usd",
    }
    require(
        response.get("schema_version") == 1
        and response.get("opaque_run_id") == request["opaque_run_id"]
        and response.get("adapter_id") == contract["adapter"]["adapter_id"]
        and response.get("adapter_version") == contract["adapter"]["adapter_version"]
        and response.get("model_id") == "excluded-provider-no-model"
        and response.get("immutable_model_version") == "excluded-provider-no-model"
        and response.get("replicate") == 0
        and response.get("budget_enforcement_attestation")
        == contract["adapter"]["budget_attestation"]
        and response.get("filesystem_network_process_attestation")
        == contract["adapter"]["isolation_attestation"]
        and response.get("termination") == "completed"
        and isinstance(usage, dict)
        and set(usage) == zero_fields | {"wall_seconds"}
        and all(usage[field] == 0 for field in zero_fields)
        and isinstance(usage["wall_seconds"], (int, float))
        and not isinstance(usage["wall_seconds"], bool)
        and usage["wall_seconds"] >= 0,
        "excluded adapter response identity, attestation, or zero-usage ledger differs",
    )
    invocations = response.get("model_invocations")
    require(
        isinstance(invocations, list) and len(invocations) == 1
        and invocations[0].get("transport") == "excluded_fixture"
        and invocations[0].get("observable_id_kind") == "fixture"
        and invocations[0].get("process_exit_code") == 0
        and invocations[0].get("usage_observed") is True,
        "excluded adapter fixture-attempt ledger is malformed",
    )
    require(trace == [{"sequence": 0, "kind": "usage_summary", "usage": usage}],
            "excluded adapter trace differs from the one-event zero-usage contract")
    expected_outputs = set(contract["required_output_files"])
    output_manifest = excluded_output_manifest(
        run_root / "output", expected_outputs, expected_uid=expected_uid,
    )
    result = load_json_artifact(run_root / "output/result.json", "component result")
    workflow = load_json_artifact(
        run_root / "output/workflow-compliance.json", "component workflow record"
    )
    require(
        result.get("opaque_run_id") == request["opaque_run_id"]
        and result.get("final_status") == "blocked"
        and result.get("public_declarations") == []
        and workflow.get("opaque_run_id") == request["opaque_run_id"]
        and workflow.get("workflow_id") == "excluded_provider_component"
        and workflow.get("evidence_files") == []
        and workflow.get("component_only") is True
        and workflow.get("primary_result_eligible") is False
        and (run_root / "output/lean-diff.patch").read_bytes() == b""
        and (run_root / "output/build.log").read_text(encoding="utf-8")
        == "Excluded-provider agent-container component: no Lean build executed.\n",
        "excluded adapter output promotes a result or differs from the fixed surface",
    )
    handoff = attestation.get("fake_auth_handoff", {})
    require(
        attestation.get("status")
        == "passed_result_free_excluded_adapter_component"
        and attestation.get("primary_result_eligible") is False
        and attestation.get("provider_execution_enabled") is False
        and attestation.get("provider_request_or_model_invocation_occurred") is False
        and attestation.get("network_access_allowed") is False
        and attestation.get("request_sha256") == contract["request"]["sha256"]
        and attestation.get("response_sha256")
        == hashlib.sha256(response_path.read_bytes()).hexdigest()
        and attestation.get("trace_sha256")
        == hashlib.sha256(trace_path.read_bytes()).hexdigest()
        and attestation.get("output_manifest") == output_manifest
        and isinstance(handoff, dict)
        and handoff.get("bytes") == len(EXPECTED_AUTH)
        and handoff.get("sha256") == hashlib.sha256(EXPECTED_AUTH).hexdigest()
        and handoff.get("read_only_descriptor") is True
        and handoff.get("descriptor_closed_before_adapter_work") is True
        and handoff.get("environment_marker_removed_before_adapter_work") is True,
        "excluded adapter attestation does not prove the fake-auth/no-provider boundary",
    )
    return {
        "adapter_response": response,
        "adapter_trace": trace,
        "adapter_stdout_sha256": hashlib.sha256(worker_output).hexdigest(),
        "output_manifest": output_manifest,
        "fake_auth_handoff": handoff,
        "provider_execution_enabled": False,
        "provider_request_or_model_invocation_occurred": False,
        "primary_result_eligible": False,
    }


def run_excluded_execute_component() -> None:
    require(os.geteuid() == 0 and os.getegid() == 0,
            "controller must start as root")
    require(CONTROL.is_dir() and not CONTROL.is_symlink(),
            "root control output is not a plain directory")
    CONTROL.chmod(0o700)
    require(WORKSPACE.is_dir() and CODEX_HOME.is_dir(),
            "disposable tmpfs mounts are absent")
    contract = load_excluded_contract()
    image_digest = os.environ.get(IMAGE_DIGEST_ENV, "")
    require(re.fullmatch(r"sha256:[0-9a-f]{64}", image_digest) is not None,
            "excluded-execution image digest is absent or malformed")
    auth = regular_single_file(AUTH_SOURCE, "outer auth sentinel")
    require(auth.read_bytes() == EXPECTED_AUTH,
            "only the frozen fake auth sentinel is accepted")
    auth_read_only = source_is_read_only(auth)
    input_read_only = source_is_read_only(INPUT_ROOT / "request.json")
    require(auth_read_only and input_read_only,
            "outer auth and excluded request must be mounted read-only")
    with CONTROL_SENTINEL.open("xb") as stream:
        stream.write(CONTROL_SENTINEL_BYTES)
        stream.flush()
        os.fsync(stream.fileno())
    CONTROL_SENTINEL.chmod(0o400)
    sentinel_info = CONTROL_SENTINEL.lstat()
    require(
        stat.S_ISREG(sentinel_info.st_mode)
        and sentinel_info.st_uid == 0
        and sentinel_info.st_gid == 0
        and stat.S_IMODE(sentinel_info.st_mode) == 0o400,
        "root control sentinel identity or mode differs",
    )
    run_root = WORKSPACE / "run"
    copied_records = copy_excluded_request(INPUT_ROOT, run_root, contract)
    for path in [WORKSPACE, *(WORKSPACE.rglob("*"))]:
        os.chown(path, WORKER_UID, WORKER_GID)
    command = [
        image_digest if item == "{{IMAGE_DIGEST}}" else item
        for item in contract["adapter"]["argv"]
    ]
    require("{{IMAGE_DIGEST}}" not in command,
            "excluded adapter argv retained an unresolved image placeholder")
    auth_descriptor = os.open(auth, os.O_RDONLY | getattr(os, "O_CLOEXEC", 0))
    worker_environment = {
        "PATH": "/usr/local/bin:/usr/bin:/bin",
        "HOME": "/tmp",
        "CODEX_HOME": str(CODEX_HOME),
        "PYTHONDONTWRITEBYTECODE": "1",
        "LANG": "C.UTF-8",
        "ABRL_OUTER_COMPONENT_MODE": EXCLUDED_EXECUTE_MODE,
        AUTH_FD_ENV: str(auth_descriptor),
    }
    outcome = run_worker_with_brokered_auth(
        auth_descriptor, worker_environment, command=command, timeout_seconds=45,
    )
    if outcome.returncode != 0:
        persist_worker_failure(CONTROL, outcome.returncode, outcome.stdout)
    require(outcome.returncode == 0,
            f"excluded adapter component failed with exit {outcome.returncode}")
    request = load_json_artifact(run_root / "request.json", "copied request")
    evidence = validate_excluded_execution_artifacts(
        run_root, contract, request, outcome.stdout, expected_uid=WORKER_UID,
    )
    report = {
        "schema_version": 1,
        "suite_id": "ABRL-TARGET-DRIFT-V2",
        "status": "passed_result_free_excluded_execute_component",
        "execution_status_boundary": "primary_execution_not_started",
        "controller_pid": os.getpid(),
        "controller_parent_pid": os.getppid(),
        "controller_uid": os.geteuid(),
        "controller_gid": os.getegid(),
        "worker_uid": WORKER_UID,
        "worker_gid": WORKER_GID,
        "container_image_digest": image_digest,
        "outer_auth_single_read_only_file": auth_read_only,
        "agent_input_single_tree_read_only": input_read_only,
        "agent_input_copy_manifest": copied_records,
        "root_control_sentinel": {
            "path": str(CONTROL_SENTINEL),
            "mode": "0400",
            "uid": sentinel_info.st_uid,
            "gid": sentinel_info.st_gid,
            "bytes": len(CONTROL_SENTINEL_BYTES),
            "sha256": hashlib.sha256(CONTROL_SENTINEL_BYTES).hexdigest(),
        },
        "adapter_command_argv": command,
        "adapter_command_sha256": hashlib.sha256(
            json.dumps(command, separators=(",", ":")).encode("utf-8")
        ).hexdigest(),
        "execution_evidence": evidence,
        "nonclaims": [
            "The auth file was the fixed fake sentinel; no provider credential was read.",
            "The excluded adapter made no provider request, model invocation, subprocess, network call, or Lean build.",
            "This is result-ineligible component evidence, not the real infrastructure smoke or a primary run.",
            "The 450-run primary evaluation remains execution_not_started."
        ],
    }
    dump_atomic(CONTROL / "controller-report.json", report)


def main() -> None:
    mode = os.environ.get("ABRL_OUTER_COMPONENT_MODE")
    require(mode in {PROBE_MODE, EXCLUDED_EXECUTE_MODE},
            "component mode environment is absent or unknown")
    if mode == PROBE_MODE:
        run_component_probe()
    else:
        run_excluded_execute_component()


if __name__ == "__main__":
    main()
