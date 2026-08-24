#!/usr/bin/env python3
"""Trusted, provider-free worker for the agent outer-boundary candidate."""

from __future__ import annotations

import errno
import hashlib
import json
import os
import stat
import subprocess
import sys
from pathlib import Path


WORKER_UID = 10002
WORKER_GID = 10002
MODEL_PROBE = "/usr/local/lib/abrl/target_drift_agent_model_probe.py"
AUTH_FD_ENV = "ABRL_RESULT_FREE_AUTH_FD"
EXPECTED_AUTH = b"RESULT_FREE_SENTINEL_DO_NOT_USE\n"
MAX_DIAGNOSTIC_BYTES = 8192


def require(condition: bool, message: str) -> None:
    if not condition:
        raise SystemExit(f"target-drift outer worker probe failed: {message}")


def cap_eff() -> str:
    for line in Path("/proc/self/status").read_text(encoding="ascii").splitlines():
        if line.startswith("CapEff:"):
            return line.split(":", 1)[1].strip()
    raise SystemExit("target-drift outer worker probe failed: CapEff is absent")


def consume_brokered_fake_auth() -> dict[str, object]:
    raw_descriptor = os.environ.pop(AUTH_FD_ENV, None)
    require(
        isinstance(raw_descriptor, str)
        and raw_descriptor.isdecimal()
        and str(int(raw_descriptor)) == raw_descriptor
        and int(raw_descriptor) >= 3,
        "root broker did not supply one canonical auth descriptor",
    )
    descriptor = int(raw_descriptor)
    info = os.fstat(descriptor)
    require(
        stat.S_ISREG(info.st_mode) and info.st_nlink == 1,
        "brokered auth descriptor is not one regular file",
    )
    write_errno = None
    try:
        os.write(descriptor, b"forbidden")
    except OSError as error:
        write_errno = error.errno
    require(write_errno == errno.EBADF, "brokered auth descriptor is writable")
    payload = b""
    try:
        while len(payload) <= len(EXPECTED_AUTH):
            chunk = os.read(descriptor, len(EXPECTED_AUTH) + 1 - len(payload))
            if not chunk:
                break
            payload += chunk
    finally:
        os.close(descriptor)
    require(payload == EXPECTED_AUTH, "brokered fake auth bytes differ")
    try:
        os.fstat(descriptor)
    except OSError as error:
        closed_errno = error.errno
    else:
        closed_errno = None
    require(closed_errno == errno.EBADF, "brokered auth descriptor stayed open")
    return {
        "bytes": len(payload),
        "sha256": hashlib.sha256(payload).hexdigest(),
        "read_only_descriptor": True,
        "descriptor_closed_before_sandbox": True,
        "environment_marker_removed_before_sandbox": AUTH_FD_ENV not in os.environ,
    }


def diagnostic_tail(output: bytes) -> str:
    return output[-MAX_DIAGNOSTIC_BYTES:].decode(
        "utf-8", errors="backslashreplace"
    ).replace(
        "RESULT_FREE_SENTINEL_DO_NOT_USE", "<fixed-fake-auth-sentinel>"
    ).replace(
        "RESULT_FREE_AGENT_INPUT", "<fixed-fake-agent-input>"
    )


def main() -> None:
    require(os.geteuid() == WORKER_UID and os.getegid() == WORKER_GID,
            "worker identity differs from the fixed non-root identity")
    effective_caps = cap_eff()
    require(int(effective_caps, 16) == 0, "worker retained an effective capability")
    auth_handoff = consume_brokered_fake_auth()
    copied_input = Path("/agent/input/input.txt")
    require(copied_input.read_text(encoding="utf-8")
            == "RESULT_FREE_AGENT_INPUT\n", "copied input differs")
    command = [
        "/usr/local/bin/codex", "sandbox", "linux",
        "--permissions-profile", ":workspace",
        "--config", "sandbox_workspace_write.network_access=false",
        "--config", 'shell_environment_policy.inherit="none"',
        "--config", "allow_login_shell=false", "--cd", "/agent", "--",
        "/usr/bin/python3", MODEL_PROBE,
    ]
    outcome = subprocess.run(
        command, stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
        check=False, timeout=30,
    )
    if outcome.returncode != 0:
        sys.stderr.write(
            "offline Codex sandbox diagnostic tail:\n"
            + diagnostic_tail(outcome.stdout) + "\n"
        )
        sys.stderr.flush()
    require(outcome.returncode == 0, "offline Codex sandbox probe failed")
    require(len(outcome.stdout) <= 1024 * 1024, "sandbox output is oversized")
    model_observation = json.loads(
        (Path("/agent") / "model-observation.json").read_text(encoding="utf-8")
    )
    expected_true = {
        "copied_agent_input_readable", "workspace_write_succeeded",
        "trusted_auth_fd_env_absent", "trusted_auth_fd_target_absent",
        "outer_auth_mount_unreadable",
        "root_control_output_unreadable", "read_only_agent_input_immutable",
        "network_denied",
    }
    if not all(model_observation.get(key) is True for key in expected_true):
        sys.stderr.write(
            "typed model-shell boundary observation:\n"
            + json.dumps(model_observation, sort_keys=True) + "\n"
        )
        sys.stderr.flush()
    require(all(model_observation.get(key) is True for key in expected_true),
            "model-shell boundary observation failed")
    require(model_observation.get("outer_auth_mount_read_errno")
            in {errno.EACCES, errno.EPERM},
            "outer auth denial was not EACCES or EPERM")
    require(model_observation.get("uid") == WORKER_UID
            and model_observation.get("gid") == WORKER_GID,
            "nested sandbox reports the wrong worker identity")
    require(int(model_observation.get("effective_capabilities_hex", "1"), 16) == 0,
            "nested sandbox retained an effective capability")
    worker_observation = {
        "schema_version": 1,
        "status": "passed_result_free_worker_component",
        "worker_uid": os.geteuid(),
        "worker_gid": os.getegid(),
        "worker_effective_capabilities_hex": effective_caps,
        "trusted_client_auth_readable": True,
        "trusted_client_fake_auth_handoff": auth_handoff,
        "model_shell": model_observation,
        "sandbox_command_argv": command,
    }
    (Path("/agent") / "worker-observation.json").write_text(
        json.dumps(worker_observation, indent=2, sort_keys=True) + "\n",
        encoding="utf-8",
    )


if __name__ == "__main__":
    main()
