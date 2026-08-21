#!/usr/bin/env python3
"""Run and record the result-free PID-1 agent lifecycle crash probe."""

from __future__ import annotations

import argparse
import hashlib
import json
import os
import re
import shutil
import signal
import stat
import subprocess
import sys
import time
import uuid
from pathlib import Path
from typing import Any


SCHEMA_VERSION = 1
SUITE_ID = "ABRL-TARGET-DRIFT-V2"
CONTROLLER = "/usr/local/bin/abrl-agent-pid1"
MAX_LEDGER_BYTES = 4 * 1024 * 1024


def require(condition: bool, message: str) -> None:
    if not condition:
        raise SystemExit(f"target-drift agent lifecycle probe failed: {message}")


def sha256_bytes(payload: bytes) -> str:
    return hashlib.sha256(payload).hexdigest()


def sha256(path: Path) -> str:
    return sha256_bytes(path.read_bytes())


def canonical_bytes(value: Any) -> bytes:
    return json.dumps(value, sort_keys=True, separators=(",", ":")).encode("utf-8")


def dump_atomic(path: Path, value: Any) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    temporary = path.with_name(path.name + ".tmp")
    with temporary.open("w", encoding="utf-8", newline="\n") as stream:
        json.dump(value, stream, indent=2, sort_keys=True)
        stream.write("\n")
        stream.flush()
        os.fsync(stream.fileno())
    os.replace(temporary, path)


def regular_file(path: Path, label: str) -> Path:
    info = path.lstat()
    reparse = bool(getattr(info, "st_file_attributes", 0) & 0x400)
    require(stat.S_ISREG(info.st_mode) and not path.is_symlink()
            and not reparse and info.st_nlink == 1, f"{label} is not a plain file")
    return path


def docker_executable() -> Path:
    text = shutil.which("docker")
    require(text is not None, "Docker CLI is unavailable")
    runtime = Path(text).resolve()
    require(runtime.name in {"docker", "docker.exe"}, "runtime is not Docker")
    if os.name != "nt":
        require(runtime in {Path("/usr/bin/docker"), Path("/usr/local/bin/docker")},
                "Docker CLI is outside allowlisted installation roots")
    return regular_file(runtime, "Docker CLI")


def checked(command: list[str], timeout: int = 30,
            allow_empty: bool = False) -> subprocess.CompletedProcess[bytes]:
    result = subprocess.run(
        command, stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
        check=False, timeout=timeout,
    )
    require(len(result.stdout) <= MAX_LEDGER_BYTES
            and (allow_empty or bool(result.stdout)),
            "Docker command output is empty or oversized")
    return result


def docker_identity(runtime: Path) -> dict[str, Any]:
    version = checked([str(runtime), "version", "--format", "{{json .}}"])
    require(version.returncode == 0, "Docker version query failed")
    daemon = checked([
        str(runtime), "info", "--format",
        "{{json .ID}}|{{json .Driver}}|{{json .SecurityOptions}}",
    ])
    require(daemon.returncode == 0, "Docker daemon query failed")
    return {
        "runtime_executable": str(runtime),
        "runtime_executable_sha256": sha256(runtime),
        "runtime_version_output_sha256": sha256_bytes(version.stdout),
        "daemon_identity_output_sha256": sha256_bytes(daemon.stdout),
    }


def image_identity(runtime: Path, image_digest: str, base_image: str,
                   controller_sha256: str) -> dict[str, Any]:
    require(re.fullmatch(r"sha256:[0-9a-f]{64}", image_digest) is not None,
            "image is not digest pinned")
    require(re.fullmatch(r"[^\s@]+@sha256:[0-9a-f]{64}", base_image) is not None,
            "base image is not repository-and-digest pinned")
    inspected = checked([
        str(runtime), "image", "inspect", image_digest, "--format", "{{json .}}",
    ])
    require(inspected.returncode == 0, "image inspection failed")
    payload = json.loads(inspected.stdout.decode("utf-8"))
    config = payload.get("Config")
    require(payload.get("Id") == image_digest and isinstance(config, dict),
            "image ID differs from requested digest")
    require(config.get("Entrypoint") == ["python3", CONTROLLER],
            "image entrypoint is not the PID-1 controller")
    audit_name = f"abrl-agent-lifecycle-audit-{uuid.uuid4().hex}"
    created = checked([
        str(runtime), "create", "--name", audit_name, "--entrypoint", "/bin/true",
        image_digest,
    ])
    require(created.returncode == 0, "image audit container creation failed")
    cid = created.stdout.decode("ascii").strip()
    try:
        temporary = Path(os.environ.get("RUNNER_TEMP", "/tmp")) / (
            f"abrl-agent-controller-{uuid.uuid4().hex}.py"
        )
        copied = checked(
            [str(runtime), "cp", f"{cid}:{CONTROLLER}", str(temporary)],
            allow_empty=True,
        )
        require(copied.returncode == 0 and temporary.is_file()
                and sha256(temporary) == controller_sha256,
                "in-image PID-1 controller differs from the source seal")
        temporary.unlink()
    finally:
        removed = checked([str(runtime), "rm", "--force", cid])
        require(removed.returncode == 0, "image audit container cleanup failed")
    return {
        "image_digest": image_digest,
        "base_image": base_image,
        "entrypoint": ["python3", CONTROLLER],
        "controller_sha256": controller_sha256,
    }


def label_ids(runtime: Path, label: str) -> list[str]:
    outcome = subprocess.run([
        str(runtime), "ps", "--all", "--quiet", "--no-trunc",
        "--filter", f"label=abrl.agent_lifecycle_attempt={label}",
    ], stdout=subprocess.PIPE, stderr=subprocess.PIPE, check=False)
    require(outcome.returncode == 0, "Docker label inspection failed")
    return [line for line in outcome.stdout.decode("ascii").splitlines() if line]


def wait_file(path: Path, deadline: float) -> None:
    while time.monotonic() < deadline:
        if path.is_file() and path.stat().st_size:
            return
        time.sleep(0.05)
    require(False, f"timed out waiting for {path.name}")


def run_probe(runtime: Path, image_digest: str, controller_sha256: str,
              output: Path) -> dict[str, Any]:
    output.mkdir(parents=True)
    if os.name != "nt":
        output.chmod(0o777)
    label = f"lifecycle-{uuid.uuid4().hex}"
    cidfile = output / "container.cid"
    ready = output / "controller-ready.json"
    exit_record = output / "controller-exit.json"
    fixture = output / "fixture.json"
    heartbeat = output / "escape-heartbeat.txt"
    command = [
        str(runtime), "run", "--pull", "never", "--rm", "-i", "--read-only",
        "--network", "none", "--cap-drop", "ALL",
        "--security-opt", "no-new-privileges=true", "--user", "65532:65532",
        "--pids-limit", "64", "--memory", "256m", "--cpus", "1",
        "--cidfile", str(cidfile.resolve()),
        "--label", f"abrl.agent_lifecycle_attempt={label}",
        "--mount", f"type=bind,src={output.resolve()},dst=/evidence",
        "--tmpfs", "/tmp:rw,nosuid,nodev,size=32m",
        image_digest,
        "--ready-file", "/evidence/controller-ready.json",
        "--exit-file", "/evidence/controller-exit.json", "--",
        "python3", CONTROLLER, "--probe-fixture-child", "/evidence",
    ]
    started = time.monotonic()
    docker = subprocess.Popen(
        command, stdin=subprocess.PIPE, stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
    )
    failure: BaseException | None = None
    try:
        wait_file(ready, started + 20)
        wait_file(fixture, started + 20)
        wait_file(heartbeat, started + 20)
        cid = cidfile.read_text(encoding="ascii").strip()
        require(re.fullmatch(r"[0-9a-f]{12,64}", cid) is not None,
                "cidfile contains an invalid container ID")
        before = heartbeat.read_text(encoding="ascii")
        # Abruptly lose the host-side controller/client.  Docker stdin closes;
        # the in-image PID 1 observes EOF and exits, so the namespace must die.
        os.kill(docker.pid, signal.SIGKILL)
        docker.wait(timeout=10)
        deadline = time.monotonic() + 15
        while time.monotonic() < deadline and label_ids(runtime, label):
            time.sleep(0.1)
        require(not label_ids(runtime, label),
                "container survived loss of the host control channel")
        time.sleep(0.3)
        after = heartbeat.read_text(encoding="ascii")
        require(after == before or int(after) >= int(before), "heartbeat is malformed")
        frozen = after
        time.sleep(0.3)
        require(heartbeat.read_text(encoding="ascii") == frozen,
                "escaped descendant continued after container removal")
        wait_file(exit_record, time.monotonic() + 2)
        ready_payload = json.loads(ready.read_text(encoding="utf-8"))
        fixture_payload = json.loads(fixture.read_text(encoding="utf-8"))
        exit_payload = json.loads(exit_record.read_text(encoding="utf-8"))
        require(ready_payload.get("controller_pid") == 1,
                "controller did not run as PID 1")
        require(exit_payload.get("reason") == "control_channel_eof",
                "PID-1 controller did not bind termination to control-channel loss")
        require(fixture_payload.get("escaped_session_pid")
                == fixture_payload.get("escaped_process_group"),
                "fixture did not create an independent session/process group")
        return {
            "schema_version": SCHEMA_VERSION,
            "suite_id": SUITE_ID,
            "status": "passed",
            "probe": "host_control_loss_reaps_pid_namespace_v1",
            "attempt_label": label,
            "container_id": cid,
            "command_sha256": sha256_bytes(canonical_bytes(command)),
            "controller_observation": ready_payload,
            "controller_exit_observation": exit_payload,
            "fixture_observation": fixture_payload,
            "escaped_descendant_heartbeat_frozen": True,
            "container_absent_after_control_loss": True,
            "measured_wall_seconds": round(time.monotonic() - started, 6),
        }
    except BaseException as error:
        failure = error
        raise
    finally:
        ids = label_ids(runtime, label)
        if ids:
            subprocess.run([str(runtime), "rm", "--force", *ids], check=False)
        if docker.poll() is None:
            docker.kill()
        if failure is not None:
            dump_atomic(output / "probe-failure.json", {
                "schema_version": SCHEMA_VERSION,
                "suite_id": SUITE_ID,
                "status": "failed",
                "failure": str(failure),
                "attempt_label": label,
                "command_sha256": sha256_bytes(canonical_bytes(command)),
            })


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--image-digest", required=True)
    parser.add_argument("--base-image", required=True)
    parser.add_argument("--controller-source", type=Path, required=True)
    parser.add_argument("--output-dir", type=Path, required=True)
    parser.add_argument("--report", type=Path, required=True)
    args = parser.parse_args()
    require(sys.platform.startswith("linux"), "probe requires a Linux Docker host")
    controller = regular_file(args.controller_source.resolve(), "controller source")
    runtime = docker_executable()
    identity = docker_identity(runtime)
    image = image_identity(
        runtime, args.image_digest, args.base_image, sha256(controller)
    )
    probe = run_probe(runtime, args.image_digest, sha256(controller), args.output_dir)
    report = {
        **probe,
        "runtime": identity,
        "image": image,
        "nonclaims": [
            "This result-free probe is not a provider or model invocation.",
            "It does not freeze the final provider-capable agent image or experiment seal.",
            "It proves only the recorded image/runtime/command lifecycle boundary.",
        ],
    }
    dump_atomic(args.report, report)
    print(json.dumps(report, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
