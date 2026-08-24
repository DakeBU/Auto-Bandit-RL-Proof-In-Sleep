#!/usr/bin/env python3
"""Canonical Docker launcher for a result-free agent outer-boundary probe.

This launcher deliberately has no production/model action.  It accepts one
fixed fake auth file and one fixed fake agent input, verifies an exact local
image digest and its trusted in-image bytes, then runs the component probe with
a root PID-1 control plane and a capability-free uid/gid 10002 worker.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import os
import re
import stat
import subprocess
import sys
import tempfile
import time
import uuid
from pathlib import Path
from typing import Any


TOOLS = Path(__file__).resolve().parent
ROOT = TOOLS.parent
sys.path.insert(0, str(TOOLS))

import launch_target_drift_checker_container as checker_launcher  # noqa: E402


SUITE_ID = "ABRL-TARGET-DRIFT-V2"
APPARMOR_PROFILE = "abrl-target-drift-codex"
PID1 = "/usr/local/bin/abrl-agent-pid1"
OUTER_CONTROLLER = "/usr/local/lib/abrl/target_drift_agent_outer_controller.py"
OUTER_PROBE = "/usr/local/lib/abrl/target_drift_agent_outer_probe.py"
MODEL_PROBE = "/usr/local/lib/abrl/target_drift_agent_model_probe.py"
EXPECTED_AUTH = b"RESULT_FREE_SENTINEL_DO_NOT_USE\n"
EXPECTED_INPUT = b"RESULT_FREE_AGENT_INPUT\n"
MAX_OUTPUT_BYTES = 4 * 1024 * 1024
CONTROL_EVIDENCE_NAMES = {
    "root-only-sentinel",
    "pid1-ready.json",
    "pid1-exit.json",
    "controller-report.json",
}


def require(condition: bool, message: str) -> None:
    if not condition:
        raise SystemExit(f"target-drift agent launcher failed: {message}")


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def regular_file(path: Path, label: str) -> Path:
    require(path.is_absolute() and path.exists() and not path.is_symlink(),
            f"{label} must be an absolute existing nonlink")
    info = path.lstat()
    reparse = bool(getattr(info, "st_file_attributes", 0) & 0x400)
    require(stat.S_ISREG(info.st_mode) and not reparse and info.st_nlink == 1,
            f"{label} must be one regular file")
    return path


def plain_empty_directory(path: Path, label: str) -> Path:
    require(path.is_absolute() and path.is_dir() and not path.is_symlink(),
            f"{label} must be an absolute plain directory")
    require(not any(path.iterdir()), f"{label} must start empty")
    return path


def validate_inputs(agent_input: Path, auth: Path, control: Path) -> None:
    require(agent_input.is_absolute() and agent_input.is_dir()
            and not agent_input.is_symlink(), "agent input must be a plain directory")
    members = list(agent_input.iterdir())
    require(len(members) == 1 and members[0].name == "input.txt",
            "component probe accepts exactly input.txt")
    require(regular_file(members[0], "agent input").read_bytes()
            == EXPECTED_INPUT, "agent input is not the frozen fake input")
    require(regular_file(auth, "auth sentinel").name == "auth.json"
            and auth.read_bytes() == EXPECTED_AUTH,
            "component probe accepts only the frozen fake auth.json")
    plain_empty_directory(control, "root control output")


def validate_control_evidence(
    control: Path, *, expected_uid: int = 0, expected_gid: int = 0,
) -> dict[str, Path]:
    """Fail closed on the complete persistent root-control output surface."""
    require(control.is_dir() and not control.is_symlink(),
            "root control output ceased to be a plain directory")
    members = {path.name: path for path in control.iterdir()}
    require(set(members) == CONTROL_EVIDENCE_NAMES,
            "root control output contains an absent or undeclared evidence file")
    for name, path in members.items():
        info = path.lstat()
        require(stat.S_ISREG(info.st_mode) and not path.is_symlink()
                and info.st_nlink == 1 and info.st_uid == expected_uid
                and info.st_gid == expected_gid,
                f"root control evidence is not one root-owned regular file: {name}")
    sentinel_info = members["root-only-sentinel"].lstat()
    require(stat.S_IMODE(sentinel_info.st_mode) == 0o400,
            "root control sentinel is not mode 0400")
    for name in CONTROL_EVIDENCE_NAMES - {"root-only-sentinel"}:
        require(stat.S_IMODE(members[name].lstat().st_mode) == 0o644,
                f"root control JSON evidence is not mode 0644: {name}")
    return members


def validate_sbom(path: Path) -> dict[str, Any]:
    payload = json.loads(regular_file(path, "agent image SBOM").read_text(
        encoding="utf-8"
    ))
    require(payload.get("schema_version") == 1
            and payload.get("suite_id") == SUITE_ID
            and payload.get("status")
            == "provider_client_image_built_probe_pending_results_absent"
            and re.fullmatch(r"sha256:[0-9a-f]{64}",
                             payload.get("container_image_digest", "")),
            "agent image SBOM is not a result-free built candidate")
    required = {
        "controller_sha256", "outer_controller_sha256",
        "outer_probe_sha256", "model_probe_sha256",
    }
    require(all(re.fullmatch(r"[0-9a-f]{64}", payload.get(key, ""))
                for key in required), "agent image SBOM omits outer-boundary bytes")
    source_bindings = {
        "controller_sha256": TOOLS / "target_drift_agent_pid1.py",
        "outer_controller_sha256": TOOLS / "target_drift_agent_outer_controller.py",
        "outer_probe_sha256": TOOLS / "target_drift_agent_outer_probe.py",
        "model_probe_sha256": TOOLS / "target_drift_agent_model_probe.py",
    }
    require(all(
        payload[key] == sha256(regular_file(source, key))
        for key, source in source_bindings.items()
    ), "agent image SBOM differs from the checked-out controller/probe sources")
    return payload


def docker_output(command: list[str]) -> bytes:
    outcome = subprocess.run(
        command, stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
        check=False, timeout=120,
    )
    require(outcome.returncode == 0 and len(outcome.stdout) <= MAX_OUTPUT_BYTES,
            f"Docker command failed: {outcome.stdout[-1000:]!r}")
    return outcome.stdout


def verify_image(runtime: Path, sbom: dict[str, Any], label: str) -> None:
    digest = sbom["container_image_digest"]
    inspected = json.loads(docker_output([
        str(runtime), "image", "inspect", digest, "--format", "{{json .}}",
    ]).decode("utf-8"))
    require(inspected.get("Id") == digest
            and inspected.get("Config", {}).get("Entrypoint")
            == ["python3", PID1]
            and inspected.get("Config", {}).get("User") in {"", "0", "0:0"},
            "image digest, root identity, or PID-1 entrypoint differs")
    name = f"abrl-agent-image-audit-{uuid.uuid4().hex}"
    created = docker_output([
        str(runtime), "create", "--network", "none", "--name", name,
        "--label", f"abrl.agent_outer_probe={label}", "--entrypoint",
        "/bin/true", digest,
    ]).decode("ascii").strip()
    require(re.fullmatch(r"[A-Za-z0-9_.-]+", created) is not None,
            "image-audit container id is malformed")
    try:
        with tempfile.TemporaryDirectory(prefix="abrl-agent-outer-audit-") as directory:
            for source, key in (
                (PID1, "controller_sha256"),
                (OUTER_CONTROLLER, "outer_controller_sha256"),
                (OUTER_PROBE, "outer_probe_sha256"),
                (MODEL_PROBE, "model_probe_sha256"),
            ):
                target = Path(directory) / key
                docker_output([str(runtime), "cp", f"{created}:{source}", str(target)])
                require(sha256(regular_file(target.resolve(), source)) == sbom[key],
                        f"in-image {source} differs from the SBOM")
    finally:
        docker_output([str(runtime), "rm", "--force", created])


def docker_command(
    runtime: Path, digest: str, agent_input: Path, auth: Path,
    control: Path, label: str,
) -> list[str]:
    """Return the only executable outer-boundary component command."""
    return [
        str(runtime), "run", "--rm", "--pull", "never", "--read-only",
        "--network", "bridge", "--cap-drop", "ALL",
        "--cap-add", "SETUID", "--cap-add", "SETGID",
        "--cap-add", "CHOWN", "--cap-add", "DAC_OVERRIDE",
        "--cap-add", "FOWNER",
        "--security-opt", "no-new-privileges=true",
        "--security-opt", "seccomp=unconfined",
        "--security-opt", f"apparmor={APPARMOR_PROFILE}",
        "--user", "0:0", "--pids-limit", "96", "--memory", "1024m",
        "--cpus", "1", "--stop-timeout", "5", "--label",
        f"abrl.agent_outer_probe={label}", "--interactive",
        "--env", "ABRL_OUTER_COMPONENT_MODE=result_free_probe_v1",
        "--env", "HOME=/tmp", "--env", "CODEX_HOME=/codex-home",
        "--env", "PYTHONDONTWRITEBYTECODE=1",
        "--mount", f"type=bind,src={agent_input},dst=/input/agent,readonly",
        "--mount", f"type=bind,src={auth},dst=/run/secrets/provider-auth,readonly",
        "--mount", f"type=bind,src={control},dst=/control",
        "--tmpfs", "/agent:rw,nosuid,nodev,size=64m,mode=0700,uid=10002,gid=10002",
        "--tmpfs", "/codex-home:rw,nosuid,nodev,noexec,size=16m,mode=0700,uid=10002,gid=10002",
        "--tmpfs", "/tmp:rw,nosuid,nodev,size=64m,mode=1777",
        "--entrypoint", "python3", digest, PID1,
        "--ready-file", "/control/pid1-ready.json",
        "--exit-file", "/control/pid1-exit.json", "--", "python3",
        OUTER_CONTROLLER,
    ]


def run_with_control(command: list[str], output: Path) -> None:
    with output.open("xb") as log:
        process = subprocess.Popen(
            command, stdin=subprocess.PIPE, stdout=log,
            stderr=subprocess.STDOUT,
        )
        assert process.stdin is not None
        process.stdin.write(b"result-free-host-control\n")
        process.stdin.flush()
        deadline = time.monotonic() + 90
        while process.poll() is None and time.monotonic() < deadline:
            time.sleep(0.05)
        if process.poll() is None:
            process.stdin.close()
            process.wait(timeout=15)
            raise SystemExit("target-drift agent launcher failed: component probe timed out")
        try:
            process.stdin.close()
        except BrokenPipeError:
            pass
        require(process.returncode == 0, "outer-boundary container failed")
    require(output.stat().st_size <= MAX_OUTPUT_BYTES,
            "outer-boundary container log is oversized")


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--image-sbom", type=Path, required=True)
    parser.add_argument("--agent-input", type=Path, required=True)
    parser.add_argument("--auth-sentinel", type=Path, required=True)
    parser.add_argument("--control-output", type=Path, required=True)
    parser.add_argument("--apparmor-source", type=Path, required=True)
    parser.add_argument("--report", type=Path, required=True)
    parser.add_argument("--probe-commit", required=True)
    args = parser.parse_args()
    require(sys.platform.startswith("linux"), "component probe requires Linux")
    require(re.fullmatch(r"[0-9a-f]{40}", args.probe_commit) is not None,
            "probe commit must be a full Git commit")
    apparmor = regular_file(
        Path(os.path.abspath(args.apparmor_source)), "AppArmor source"
    )
    require(f"profile {APPARMOR_PROFILE} flags=(unconfined)" in apparmor.read_text(
        encoding="utf-8"
    ), "AppArmor source does not define the frozen profile")
    agent_input = Path(os.path.abspath(args.agent_input))
    auth = Path(os.path.abspath(args.auth_sentinel))
    control = Path(os.path.abspath(args.control_output))
    validate_inputs(agent_input, auth, control)
    report_path = Path(os.path.abspath(args.report))
    require(report_path.parent.is_dir() and not report_path.parent.is_symlink(),
            "report parent must be a plain existing directory")
    require(not report_path.exists(), "report already exists")
    sbom_path = Path(os.path.abspath(args.image_sbom))
    sbom = validate_sbom(sbom_path)
    runtime = checker_launcher.canonical_docker_executable()
    before = checker_launcher.runtime_identity(runtime)
    label = "result-free-" + uuid.uuid4().hex
    verify_image(runtime, sbom, label)
    command = docker_command(
        runtime, sbom["container_image_digest"], agent_input, auth, control, label
    )
    log = report_path.with_name(report_path.stem + "-container.log")
    require(not log.exists(), "container log already exists")
    run_with_control(command, log)
    after = checker_launcher.runtime_identity(runtime)
    require(before == after, "Docker runtime identity changed during the probe")
    control_evidence = validate_control_evidence(control)
    controller_report_path = regular_file(
        control_evidence["controller-report.json"], "controller report"
    )
    controller_report = json.loads(controller_report_path.read_text(encoding="utf-8"))
    require(controller_report.get("status")
            == "passed_result_free_outer_boundary_component",
            "root controller did not report a passing component probe")
    worker_observation = controller_report.get("worker_observation", {})
    require(controller_report.get("controller_uid") == 0
            and controller_report.get("controller_gid") == 0
            and controller_report.get("worker_uid") == 10002
            and controller_report.get("worker_gid") == 10002
            and isinstance(worker_observation, dict)
            and worker_observation.get("worker_uid") == 10002
            and worker_observation.get("worker_gid") == 10002
            and int(worker_observation.get(
                "worker_effective_capabilities_hex", "1"
            ), 16) == 0,
            "controller report does not bind the root-to-worker transition")
    model_observation = worker_observation.get("model_shell", {})
    require(isinstance(model_observation, dict)
            and int(model_observation.get(
                "effective_capabilities_hex", "1"
            ), 16) == 0,
            "nested command sandbox retained an effective capability")
    sentinel = controller_report.get("root_control_sentinel", {})
    require(isinstance(sentinel, dict)
            and sentinel.get("path") == "/control/root-only-sentinel"
            and sentinel.get("mode") == "0400"
            and sentinel.get("uid") == 0
            and sentinel.get("gid") == 0
            and sentinel.get("bytes")
            == len(b"RESULT_FREE_ROOT_CONTROL_SENTINEL\n")
            and sentinel.get("sha256") == hashlib.sha256(
                b"RESULT_FREE_ROOT_CONTROL_SENTINEL\n"
            ).hexdigest(), "root control sentinel binding is malformed")
    ready_path = regular_file(
        control_evidence["pid1-ready.json"], "PID-1 ready ledger"
    )
    exit_path = regular_file(
        control_evidence["pid1-exit.json"], "PID-1 exit ledger"
    )
    exit_ledger = json.loads(exit_path.read_text(encoding="utf-8"))
    require(exit_ledger.get("reason") == "child_exited"
            and exit_ledger.get("child_return_code") == 0,
            "PID-1 ledger does not record a clean controlled child exit")
    report = {
        "schema_version": 1,
        "suite_id": SUITE_ID,
        "status": "passed_result_free_outer_launcher_component_candidate",
        "probe_commit": args.probe_commit,
        "container_image_digest": sbom["container_image_digest"],
        "image_sbom_sha256": sha256(sbom_path),
        "docker_runtime_identity": before,
        "docker_command_argv": command,
        "docker_command_sha256": hashlib.sha256(json.dumps(
            command, separators=(",", ":")
        ).encode("utf-8")).hexdigest(),
        "source_bindings": {
            "host_launcher_sha256": sha256(Path(__file__).resolve()),
            "apparmor_source_sha256": sha256(apparmor),
            "controller_report_sha256": sha256(controller_report_path),
            "pid1_ready_ledger_sha256": sha256(ready_path),
            "pid1_exit_ledger_sha256": sha256(exit_path),
        },
        "controller_report": controller_report,
        "container_log_sha256": sha256(log),
        "nonclaims": [
            "The mounted auth.json was a fixed fake sentinel, not a provider credential.",
            "No provider request or model invocation occurred.",
            "The image is local and unpublished; this is not a production seal or real smoke."
        ],
    }
    descriptor = os.open(report_path, os.O_WRONLY | os.O_CREAT | os.O_EXCL, 0o644)
    with os.fdopen(descriptor, "w", encoding="utf-8", newline="\n") as stream:
        json.dump(report, stream, indent=2, sort_keys=True)
        stream.write("\n")
    print(json.dumps({
        "status": report["status"], "report": str(report_path),
        "container_image_digest": report["container_image_digest"],
    }, sort_keys=True))


if __name__ == "__main__":
    main()
