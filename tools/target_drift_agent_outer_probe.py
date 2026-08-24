#!/usr/bin/env python3
"""Trusted, provider-free worker for the agent outer-boundary candidate."""

from __future__ import annotations

import json
import os
import subprocess
from pathlib import Path


WORKER_UID = 10002
WORKER_GID = 10002
MODEL_PROBE = "/usr/local/lib/abrl/target_drift_agent_model_probe.py"


def require(condition: bool, message: str) -> None:
    if not condition:
        raise SystemExit(f"target-drift outer worker probe failed: {message}")


def cap_eff() -> str:
    for line in Path("/proc/self/status").read_text(encoding="ascii").splitlines():
        if line.startswith("CapEff:"):
            return line.split(":", 1)[1].strip()
    raise SystemExit("target-drift outer worker probe failed: CapEff is absent")


def main() -> None:
    require(os.geteuid() == WORKER_UID and os.getegid() == WORKER_GID,
            "worker identity differs from the fixed non-root identity")
    effective_caps = cap_eff()
    require(int(effective_caps, 16) == 0, "worker retained an effective capability")
    auth = Path("/codex-home/auth.json")
    require(auth.is_file() and auth.read_text(encoding="ascii")
            == "RESULT_FREE_SENTINEL_DO_NOT_USE\n",
            "trusted client cannot read the disposable auth sentinel")
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
    require(outcome.returncode == 0, "offline Codex sandbox probe failed")
    require(len(outcome.stdout) <= 1024 * 1024, "sandbox output is oversized")
    model_observation = json.loads(
        (Path("/agent") / "model-observation.json").read_text(encoding="utf-8")
    )
    expected_true = {
        "copied_agent_input_readable", "workspace_write_succeeded",
        "disposable_auth_unreadable", "outer_auth_mount_unreadable",
        "root_control_output_unreadable", "read_only_agent_input_immutable",
        "network_denied",
    }
    require(all(model_observation.get(key) is True for key in expected_true),
            "model-shell boundary observation failed")
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
        "model_shell": model_observation,
        "sandbox_command_argv": command,
    }
    (Path("/agent") / "worker-observation.json").write_text(
        json.dumps(worker_observation, indent=2, sort_keys=True) + "\n",
        encoding="utf-8",
    )


if __name__ == "__main__":
    main()
