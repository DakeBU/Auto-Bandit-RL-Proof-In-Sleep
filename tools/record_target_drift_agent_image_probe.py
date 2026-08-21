#!/usr/bin/env python3
"""Record result-free inner-sandbox evidence for an exact agent-image digest."""

from __future__ import annotations

import argparse
import errno
import hashlib
import ipaddress
import json
import os
import re
import socket
import stat
import subprocess
import sys
import tempfile
import uuid
from pathlib import Path
from typing import Any


TOOLS = Path(__file__).resolve().parent
ROOT = TOOLS.parent
sys.path.insert(0, str(TOOLS))

import launch_target_drift_checker_container as checker_launcher  # noqa: E402
import prepare_target_drift_agent_image as agent_image  # noqa: E402


SUITE_ID = "ABRL-TARGET-DRIFT-V2"
MAX_OUTPUT_BYTES = 4 * 1024 * 1024
NETWORK_CONTROL_HOST = "registry.npmjs.org"
NETWORK_CONTROL_PORT = 443


def require(condition: bool, message: str) -> None:
    if not condition:
        raise SystemExit(f"target-drift agent-image probe failed: {message}")


def sha256_file(path: Path) -> str:
    return agent_image.sha256_file(path)


def regular_file(path: Path, label: str) -> Path:
    info = path.lstat()
    reparse = bool(getattr(info, "st_file_attributes", 0) & 0x400)
    require(stat.S_ISREG(info.st_mode) and not path.is_symlink()
            and not reparse and info.st_nlink == 1,
            f"{label} is not a single-linked regular file")
    return path


def dump_new(path: Path, value: Any) -> None:
    require(not path.exists(), f"refusing to overwrite {path}")
    path.parent.mkdir(parents=True, exist_ok=True)
    descriptor = os.open(path, os.O_WRONLY | os.O_CREAT | os.O_EXCL, 0o644)
    with os.fdopen(descriptor, "w", encoding="utf-8", newline="\n") as stream:
        json.dump(value, stream, indent=2, sort_keys=True)
        stream.write("\n")


def docker_run(command: list[str], timeout: int = 120) -> bytes:
    outcome = subprocess.run(
        command, stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
        check=False, timeout=timeout,
    )
    require(len(outcome.stdout) <= MAX_OUTPUT_BYTES,
            "sandbox probe output exceeded the evidence ceiling")
    require(outcome.returncode == 0,
            f"sandbox probe command failed ({outcome.returncode}): "
            f"{outcome.stdout[-2000:]!r}")
    return outcome.stdout


def probe_source(network_control_ipv4: str) -> bytes:
    ipaddress.IPv4Address(network_control_ipv4)
    template = '''\
import errno, json, os, pathlib, socket, time

root = pathlib.Path("/workspace")
allowed = root / "workspace-write-ok.txt"
allowed.write_text("ok\\n", encoding="utf-8")
secret = pathlib.Path("/run/secrets/provider-auth")
try:
    secret.read_bytes()
    secret_readable = True
except (OSError, PermissionError):
    secret_readable = False
outside = pathlib.Path("/opt/abrl-codex/probe-write-must-fail")
outside_write_errno = None
try:
    outside.write_text("forbidden\\n", encoding="utf-8")
except OSError as error:
    outside_write_errno = error.errno
network_denied = False
network_error_errno = None
network_error_name = ""
sock = socket.socket(socket.AF_INET, socket.SOCK_STREAM)
sock.settimeout(1.0)
network_started = time.monotonic()
try:
    sock.connect(("__ABRL_CONTROL_IPV4__", __ABRL_CONTROL_PORT__))
except OSError as error:
    network_error_errno = error.errno
    network_error_name = errno.errorcode.get(error.errno, type(error).__name__)
    network_denied = error.errno in {errno.ENETUNREACH, errno.EHOSTUNREACH}
finally:
    sock.close()
network_elapsed_seconds = time.monotonic() - network_started
proc_ids = sorted(name for name in os.listdir("/proc") if name.isdigit())
payload = {
    "workspace_write_succeeded": allowed.read_text(encoding="utf-8") == "ok\\n",
    "provider_auth_unreadable": not secret_readable,
    "persistent_outside_workspace_write_denied": outside_write_errno in (
        errno.EROFS, errno.EACCES, errno.EPERM
    ),
    "persistent_outside_workspace_write_errno": outside_write_errno,
    "network_denied": network_denied,
    "network_error_errno": network_error_errno,
    "network_error_name": network_error_name,
    "network_elapsed_seconds": network_elapsed_seconds,
    "openai_api_key_absent": "OPENAI_API_KEY" not in os.environ,
    "fresh_pid_namespace": "1" in proc_ids and len(proc_ids) <= 8,
    "observed_proc_ids": proc_ids,
}
(root / "probe-observation.json").write_text(
    json.dumps(payload, sort_keys=True) + "\\n", encoding="utf-8"
)
'''
    return template.replace(
        "__ABRL_CONTROL_IPV4__", network_control_ipv4
    ).replace(
        "__ABRL_CONTROL_PORT__", str(NETWORK_CONTROL_PORT)
    ).encode("utf-8")


def resolve_control_ipv4() -> str:
    addresses = sorted({
        item[4][0] for item in socket.getaddrinfo(
            NETWORK_CONTROL_HOST, NETWORK_CONTROL_PORT,
            socket.AF_INET, socket.SOCK_STREAM,
        )
    })
    require(bool(addresses), "network-control host has no IPv4 address")
    value = addresses[0]
    ipaddress.IPv4Address(value)
    return value


def run_inner_sandbox_probe(
    runtime: Path, image_digest: str, work_dir: Path,
) -> tuple[dict[str, Any], list[str], bytes, list[str], bytes, str]:
    work_dir.mkdir()
    work_dir.chmod(0o700)
    workspace = work_dir / "workspace"
    workspace.mkdir()
    workspace.chmod(0o777)
    network_control_ipv4 = resolve_control_ipv4()
    source_bytes = probe_source(network_control_ipv4)
    source = workspace / "probe.py"
    source.write_bytes(source_bytes)
    source.chmod(0o444)
    secret = work_dir / "provider-auth"
    secret.write_text("RESULT_FREE_SENTINEL_DO_NOT_USE\n", encoding="ascii", newline="\n")
    secret.chmod(0o400)
    control_command = [
        str(runtime), "run", "--rm", "--pull", "never", "--read-only",
        "--network", "bridge", "--cap-drop", "ALL",
        "--security-opt", "no-new-privileges=true", "--user", "10002:10002",
        "--entrypoint", "python3", image_digest, "-c",
        (
            "import socket; s=socket.create_connection(("
            f"{network_control_ipv4!r},{NETWORK_CONTROL_PORT}),5); s.close(); "
            "print('outer-network-control-ok')"
        ),
    ]
    control_output = docker_run(control_command)
    require(control_output.strip() == b"outer-network-control-ok",
            "outer container network control did not reach the frozen endpoint")
    command = [
        str(runtime), "run", "--rm", "--pull", "never", "--read-only",
        "--network", "bridge", "--cap-drop", "ALL",
        "--security-opt", "no-new-privileges=true",
        "--security-opt", "seccomp=unconfined",
        "--security-opt", "apparmor=unconfined",
        "--user", "10002:10002", "--pids-limit", "64", "--memory", "512m",
        "--cpus", "1", "--tmpfs", "/tmp:rw,nosuid,nodev,size=64m,mode=1777",
        "--env", "HOME=/tmp", "--env", "CODEX_HOME=/tmp/codex-home",
        "--mount", f"type=bind,src={workspace.resolve()},dst=/workspace",
        "--mount", f"type=bind,src={secret.resolve()},dst=/run/secrets/provider-auth,readonly",
        "--entrypoint", "/usr/local/bin/codex", image_digest,
        "sandbox", "linux", "--config", 'sandbox_mode="workspace-write"',
        "--config", "sandbox_workspace_write.network_access=false",
        "--config", 'shell_environment_policy.inherit="none"',
        "--config", "allow_login_shell=false", "-C", "/workspace", "--",
        "python3", "/workspace/probe.py",
    ]
    output = docker_run(command)
    observation_path = regular_file(
        workspace / "probe-observation.json", "inner-sandbox observation"
    )
    observation = json.loads(observation_path.read_text(encoding="utf-8"))
    expected_true = {
        "workspace_write_succeeded", "provider_auth_unreadable", "network_denied",
        "persistent_outside_workspace_write_denied", "openai_api_key_absent",
        "fresh_pid_namespace",
    }
    require(all(observation.get(field) is True for field in expected_true),
            "one or more inner-sandbox observations failed")
    require(observation.get("network_error_errno") in {
        errno.ENETUNREACH, errno.EHOSTUNREACH,
    }, "inner-sandbox network failure was not an explicit route denial")
    return (
        observation, command, output, control_command, control_output,
        network_control_ipv4,
    )


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--image-sbom", type=Path, required=True)
    parser.add_argument("--work-dir", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--probe-commit", required=True)
    args = parser.parse_args()
    require(sys.platform.startswith("linux"), "agent-image probe requires Linux")
    require(re.fullmatch(r"[0-9a-f]{40}", args.probe_commit) is not None,
            "probe commit must be a full lowercase Git commit")
    sbom_path = regular_file(args.image_sbom.resolve(), "agent image SBOM")
    sbom = json.loads(sbom_path.read_text(encoding="utf-8"))
    require(sbom.get("schema_version") == 1
            and sbom.get("suite_id") == SUITE_ID
            and sbom.get("status")
            == "provider_client_image_built_probe_pending_results_absent"
            and re.fullmatch(r"sha256:[0-9a-f]{64}",
                             sbom.get("container_image_digest", "")) is not None,
            "agent image SBOM identity/status is malformed")
    require(not args.work_dir.exists(), "probe work directory already exists")
    runtime = checker_launcher.canonical_docker_executable()
    identity = checker_launcher.runtime_identity(runtime)
    image_digest = sbom["container_image_digest"]
    inspected = json.loads(docker_run([
        str(runtime), "image", "inspect", image_digest, "--format", "{{json .}}",
    ]).decode("utf-8"))
    require(inspected.get("Id") == image_digest
            and inspected.get("Config", {}).get("Entrypoint")
            == ["python3", agent_image.CONTROLLER_PATH],
            "agent image digest or PID-1 entrypoint differs from the SBOM")
    (
        observation, command, raw_output, control_command, control_output,
        network_control_ipv4,
    ) = run_inner_sandbox_probe(runtime, image_digest, args.work_dir)
    output_log = args.output.with_name(args.output.stem + "-stdout.log")
    require(not output_log.exists(), "probe stdout ledger already exists")
    output_log.write_bytes(raw_output)
    control_log = args.output.with_name(args.output.stem + "-network-control.log")
    require(not control_log.exists(), "network-control ledger already exists")
    control_log.write_bytes(control_output)
    report = {
        "schema_version": 1,
        "suite_id": SUITE_ID,
        "status": "passed_result_free_candidate",
        "probe_commit": args.probe_commit,
        "container_image_digest": image_digest,
        "image_sbom_sha256": sha256_file(sbom_path),
        "codex_version": sbom["codex_version"],
        "codex_executable_sha256": sbom["codex_executable_sha256"],
        "lean_version": sbom["lean_version"],
        "lake_version": sbom["lake_version"],
        "checker_cache_manifest_sha256": sbom["checker_cache_manifest_sha256"],
        "runtime": identity,
        "sandbox_command_argv": command,
        "sandbox_command_sha256": hashlib.sha256(
            json.dumps(command, sort_keys=False, separators=(",", ":")).encode("utf-8")
        ).hexdigest(),
        "outer_network_control_argv": control_command,
        "outer_network_control_sha256": hashlib.sha256(
            json.dumps(control_command, sort_keys=False, separators=(",", ":")).encode(
                "utf-8"
            )
        ).hexdigest(),
        "outer_network_control": {
            "host": NETWORK_CONTROL_HOST,
            "resolved_ipv4": network_control_ipv4,
            "address_family": "AF_INET",
            "port": NETWORK_CONTROL_PORT,
            "reachable_before_inner_sandbox": True,
            "stdout_sha256": sha256_file(control_log),
        },
        "observations": observation,
        "probe_source_sha256": hashlib.sha256(
            probe_source(network_control_ipv4)
        ).hexdigest(),
        "probe_stdout_sha256": sha256_file(output_log),
        "source_bindings": {
            "probe_runner_sha256": sha256_file(Path(__file__).resolve()),
            "agent_image_builder_sha256": sha256_file(
                TOOLS / "prepare_target_drift_agent_image.py"
            ),
            "agent_image_recipe_sha256": sha256_file(
                ROOT / "evaluation/target-drift-v2/agent-image.Containerfile"
            ),
            "agent_image_source_lock_sha256": sha256_file(
                ROOT / "evaluation/target-drift-v2/agent-image-sources.json"
            ),
            "agent_sandbox_contract_sha256": sha256_file(
                ROOT / "evaluation/target-drift-v2/agent-sandbox-contract.json"
            ),
            "agent_image_workflow_sha256": sha256_file(
                ROOT / ".github/workflows/target-drift-agent-image.yml"
            ),
            "controller_source_sha256": sha256_file(
                TOOLS / "target_drift_agent_pid1.py"
            ),
            "adapter_source_sha256": sha256_file(
                TOOLS / "codex_target_drift_adapter.py"
            ),
        },
        "nonclaims": [
            "No provider credential was supplied and no model invocation occurred.",
            "The probe exercises the exact image's offline Codex Linux sandbox, not the full adapter-to-provider path.",
            "The real one-case-by-three-condition smoke and all 450 primary runs remain unrun."
        ],
    }
    dump_new(args.output, report)
    print(json.dumps(report, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
