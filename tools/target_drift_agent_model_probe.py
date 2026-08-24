#!/usr/bin/env python3
"""Untrusted-shell view used by the result-free outer-boundary probe.

This program is executed by ``codex sandbox linux`` without contacting a
provider.  It records only boundary observations; it is not an agent, a model
invocation, or an evaluation result.
"""

from __future__ import annotations

import errno
import json
import os
import socket
from pathlib import Path


def read_denial_errno(path: Path):
    try:
        path.read_bytes()
    except OSError as error:
        return error.errno
    return None


def denied_write(path: Path) -> bool:
    try:
        path.write_text("forbidden\n", encoding="utf-8")
    except OSError:
        return True
    return False


def parse_effective_capabilities(status: str) -> str:
    for line in status.splitlines():
        if line.startswith("CapEff:"):
            value = line.split(":", 1)[1].strip()
            int(value, 16)
            return value
    raise SystemExit("model-shell probe failed: CapEff is absent")


def effective_capabilities_hex() -> str:
    return parse_effective_capabilities(
        Path("/proc/self/status").read_text(encoding="ascii")
    )


def main() -> None:
    workspace = Path("/agent")
    copied_input = workspace / "input" / "input.txt"
    workspace_write = workspace / "model-workspace-write.txt"
    workspace_write.write_text("ok\n", encoding="utf-8")
    network_denied = False
    network_errno = None
    try:
        sock = socket.socket(socket.AF_INET, socket.SOCK_STREAM)
    except OSError as error:
        network_errno = error.errno
        network_denied = error.errno in {errno.EPERM, errno.EACCES}
    else:
        sock.settimeout(0.5)
        try:
            sock.connect(("203.0.113.1", 9))
        except OSError as error:
            network_errno = error.errno
            network_denied = error.errno in {
                errno.EPERM, errno.EACCES, errno.ENETUNREACH,
                errno.EHOSTUNREACH,
            }
        finally:
            sock.close()
    disposable_auth_errno = read_denial_errno(Path("/codex-home/auth.json"))
    outer_auth_errno = read_denial_errno(Path("/run/secrets/provider-auth"))
    root_control_errno = read_denial_errno(
        Path("/control/root-only-sentinel")
    )
    observation = {
        "uid": os.geteuid(),
        "gid": os.getegid(),
        "effective_capabilities_hex": effective_capabilities_hex(),
        "copied_agent_input_readable": copied_input.read_text(
            encoding="utf-8"
        ) == "RESULT_FREE_AGENT_INPUT\n",
        "workspace_write_succeeded": workspace_write.read_text(
            encoding="utf-8"
        ) == "ok\n",
        "disposable_auth_unreadable": disposable_auth_errno is not None,
        "disposable_auth_read_errno": disposable_auth_errno,
        "outer_auth_mount_unreadable": outer_auth_errno is not None,
        "outer_auth_mount_read_errno": outer_auth_errno,
        "root_control_output_unreadable": root_control_errno in {
            errno.EACCES, errno.EPERM,
        },
        "root_control_output_read_errno": root_control_errno,
        "read_only_agent_input_immutable": denied_write(
            Path("/input/agent/input.txt")
        ),
        "network_denied": network_denied,
        "network_errno": network_errno,
    }
    (workspace / "model-observation.json").write_text(
        json.dumps(observation, sort_keys=True) + "\n", encoding="utf-8"
    )


if __name__ == "__main__":
    main()
