#!/usr/bin/env python3
"""Trusted root controller for a result-free agent outer-boundary candidate.

The controller accepts no caller-supplied command.  It copies one read-only
agent-input tree into disposable tmpfs and brokers one read-only fake
``auth.json`` descriptor to a child that is irreversibly dropped to uid/gid
10002.  The root parent closes its descriptor as soon as the child exists,
validates the fixed offline probe, and writes only root-control evidence.
"""

from __future__ import annotations

import errno
import hashlib
import json
import os
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
CONTROL_SENTINEL = CONTROL / "root-only-sentinel"
CONTROL_SENTINEL_BYTES = b"RESULT_FREE_ROOT_CONTROL_SENTINEL\n"
MAX_DIAGNOSTIC_BYTES = 8192
AUTH_FD_ENV = "ABRL_RESULT_FREE_AUTH_FD"
EXPECTED_AUTH = b"RESULT_FREE_SENTINEL_DO_NOT_USE\n"


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
) -> subprocess.CompletedProcess[bytes]:
    command = ["/usr/bin/python3", WORKER_PROBE]
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
        output, _ = process.communicate(timeout=45)
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


def main() -> None:
    require(os.environ.get("ABRL_OUTER_COMPONENT_MODE") == "result_free_probe_v1",
            "component mode environment is absent")
    run_component_probe()


if __name__ == "__main__":
    main()
