#!/usr/bin/env python3
"""Sealed Docker launcher for the target-drift checker boundary.

Production callers do not provide arbitrary sandbox argv.  They use the
templates generated here; every action re-verifies the host Python executable,
Docker executable, client/server version ledger, and daemon identity before it
constructs an allowlisted command.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import os
import platform
import re
import shutil
import stat
import subprocess
import sys
import tempfile
import uuid
from pathlib import Path
from typing import Any


ABSENT_EXIT_CODE = 3
MAX_RUNTIME_LEDGER_BYTES = 1024 * 1024
# A complete Mathlib/Lake cache contains well over 100k files.  Its
# byte-complete JSON manifest is intentionally much larger than a command or
# inspect ledger, so it receives a separate hard cap while remaining hash-bound.
MAX_CACHE_MANIFEST_BYTES = 64 * 1024 * 1024
INNER_CHECKER_PATH = "/usr/local/lib/abrl/check_target_drift_inner.py"
CONTROLLER_PATH = "/usr/local/bin/abrl-checker-controller"
CHECKER_CACHE_ROOT = "/opt/abrl-checker-cache/.lake"
CHECKER_CACHE_MANIFEST_PATH = "/opt/abrl-checker-cache/cache-manifest.json"
CHECKER_BUILD_INPUT_MANIFEST_PATH = (
    "/opt/abrl-checker-cache/build-input-manifest.json"
)


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def require(condition: bool, message: str) -> None:
    if not condition:
        raise SystemExit(f"checker container launcher failed: {message}")


def regular_protected_file(path: Path, expected_sha256: str, label: str) -> Path:
    require(path.is_absolute() and path.exists() and not path.is_symlink(),
            f"{label} must be an existing absolute nonlink path")
    info = path.lstat()
    reparse = bool(getattr(info, "st_file_attributes", 0) & 0x400)
    require(stat.S_ISREG(info.st_mode) and not reparse and info.st_nlink == 1,
            f"{label} must be one unlinked regular file")
    require(sha256(path) == expected_sha256, f"{label} hash differs from the seal")
    return path


def regular_executable(path: Path, expected_sha256: str, label: str) -> Path:
    path = regular_protected_file(path, expected_sha256, label)
    if os.name != "nt":
        require(os.access(path, os.X_OK), f"{label} is not executable")
    return path


def capped_output(command: list[str]) -> bytes:
    process = subprocess.run(
        command, stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
        timeout=30, check=False,
    )
    require(process.returncode == 0, f"runtime identity command failed: {command[1]}")
    require(0 < len(process.stdout) <= MAX_RUNTIME_LEDGER_BYTES,
            "runtime identity output is empty or oversized")
    return process.stdout


def canonical_docker_executable() -> Path:
    discovered = shutil.which("docker")
    require(discovered is not None, "Docker CLI is not available on the canonical PATH")
    path = Path(discovered).resolve()
    require(path.name.lower() in {"docker", "docker.exe"},
            "canonical container runtime must be the Docker CLI")
    if os.name == "nt":
        program_files = {
            Path(value).resolve()
            for name in ("ProgramFiles", "ProgramW6432")
            if (value := os.environ.get(name))
        }
        allowed = {
            root / "Docker" / "Docker" / "resources" / "bin" / "docker.exe"
            for root in program_files
        }
    elif platform.system() == "Darwin":
        allowed = {
            Path("/Applications/Docker.app/Contents/Resources/bin/docker"),
            Path("/usr/local/bin/docker"),
        }
    else:
        allowed = {Path("/usr/bin/docker"), Path("/usr/local/bin/docker")}
    require(path in {candidate.resolve() for candidate in allowed if candidate.exists()},
            "Docker CLI is outside the audited installation roots")
    return path


def runtime_signature_identity(runtime: Path) -> str:
    if os.name != "nt":
        payload = json.dumps({
            "platform": platform.system(), "runtime_path": str(runtime.resolve()),
            "verification": "absolute allowlisted package path plus frozen executable hash",
        }, sort_keys=True, separators=(",", ":")).encode("utf-8")
        return hashlib.sha256(payload).hexdigest()
    powershell = Path(
        os.environ.get("SystemRoot", r"C:\Windows")
    ) / "System32" / "WindowsPowerShell" / "v1.0" / "powershell.exe"
    require(powershell.is_file(), "system PowerShell is unavailable for Authenticode")
    script = (
        "$s=Get-AuthenticodeSignature -LiteralPath $args[0]; "
        "[pscustomobject]@{Status=[string]$s.Status;"
        "Thumbprint=[string]$s.SignerCertificate.Thumbprint;"
        "Subject=[string]$s.SignerCertificate.Subject}|ConvertTo-Json -Compress"
    )
    raw = capped_output([
        str(powershell), "-NoProfile", "-NonInteractive", "-Command", script, str(runtime),
    ])
    try:
        signature = json.loads(raw.decode("utf-8-sig"))
    except (UnicodeDecodeError, json.JSONDecodeError) as error:
        raise SystemExit(f"checker container launcher failed: bad Authenticode ledger: {error}")
    require(signature.get("Status") == "Valid"
            and re.fullmatch(r"[0-9A-Fa-f]{40,64}", signature.get("Thumbprint", ""))
            and "docker" in signature.get("Subject", "").lower(),
            "Docker CLI Authenticode signature is not valid for Docker")
    return hashlib.sha256(raw).hexdigest()


def runtime_identity(runtime: Path) -> dict[str, str]:
    signature_sha256 = runtime_signature_identity(runtime)
    version = capped_output([str(runtime), "version", "--format", "{{json .}}"])
    daemon = capped_output([
        str(runtime), "info", "--format",
        "{{json .ID}}|{{json .Driver}}|{{json .DockerRootDir}}|{{json .SecurityOptions}}",
    ])
    try:
        version_payload = json.loads(version.decode("utf-8"))
        info_parts = daemon.decode("utf-8").strip().split("|", 3)
        daemon_id, storage_driver, docker_root, security_options = (
            json.loads(part) for part in info_parts
        )
    except (UnicodeDecodeError, json.JSONDecodeError, ValueError) as error:
        raise SystemExit(f"checker container launcher failed: malformed Docker identity: {error}")
    require(isinstance(version_payload, dict)
            and isinstance(version_payload.get("Client"), dict)
            and isinstance(version_payload.get("Server"), dict),
            "Docker identity omits client/server ledgers")
    client_version = version_payload["Client"].get("Version")
    server_version = version_payload["Server"].get("Version")
    server_os = version_payload["Server"].get("Os")
    require(all(isinstance(value, str) and value for value in (
        client_version, server_version, server_os, daemon_id, storage_driver, docker_root,
    )) and isinstance(security_options, list),
            "Docker identity fields have the wrong schema")
    return {
        "runtime_id": "docker",
        "runtime_version": f"client={client_version};server={server_version};os={server_os}",
        "runtime_signature_output_sha256": signature_sha256,
        "runtime_version_output_sha256": hashlib.sha256(version).hexdigest(),
        "daemon_identity_output_sha256": hashlib.sha256(daemon).hexdigest(),
    }


def verify_runtime(args: argparse.Namespace) -> Path:
    # The launcher is interpreted by the separately sealed Python executable;
    # it is intentionally tracked as an ordinary 100644 source file.  Requiring
    # a POSIX execute bit here rejects a clean Git checkout before Docker can
    # create a cidfile, even though the file is never execve'd directly.
    regular_protected_file(
        Path(__file__).resolve(), args.launcher_sha256, "checker host launcher"
    )
    regular_executable(
        Path(sys.executable).resolve(), args.host_python_sha256, "host Python executable"
    )
    runtime = regular_executable(
        Path(args.runtime_executable), args.runtime_executable_sha256,
        "Docker runtime executable",
    )
    require(args.runtime_kind == "docker", "only the audited Docker launcher is supported")
    require(runtime.resolve() == canonical_docker_executable(),
            "Docker runtime differs from the canonical PATH executable")
    identity = runtime_identity(runtime)
    require(identity["runtime_version_output_sha256"] == args.runtime_version_output_sha256,
            "Docker client/server version ledger differs from the seal")
    require(identity["runtime_signature_output_sha256"]
            == args.runtime_signature_output_sha256,
            "Docker executable signature/path ledger differs from the seal")
    require(identity["daemon_identity_output_sha256"] == args.daemon_identity_output_sha256,
            "Docker daemon identity/security ledger differs from the seal")
    return runtime


def common_template(checker: dict[str, Any], launcher_path: Path) -> list[str]:
    return [
        checker["host_python_executable"], str(launcher_path.resolve()),
        "--launcher-sha256", checker["host_launcher_sha256"],
        "--host-python-sha256", checker["host_python_executable_sha256"],
        "--runtime-kind", checker["container_runtime_kind"],
        "--runtime-executable", checker["container_runtime_executable"],
        "--runtime-executable-sha256", checker["container_runtime_executable_sha256"],
        "--runtime-version-output-sha256", checker["runtime_version_output_sha256"],
        "--runtime-signature-output-sha256", checker[
            "runtime_signature_output_sha256"
        ],
        "--daemon-identity-output-sha256", checker["daemon_identity_output_sha256"],
        "--controller-entrypoint-sha256", checker["controller_entrypoint_sha256"],
        "--inner-checker-sha256", checker["inner_checker_sha256"],
        "--cache-manifest-sha256", checker["checker_cache_manifest_sha256"],
        "--build-input-manifest-sha256", checker[
            "checker_image_build_input_manifest_sha256"
        ],
        "--image-digest", "{{CHECKER_IMAGE_DIGEST}}",
        "--attempt-label", "{{CHECKER_ATTEMPT_LABEL}}",
        "--cidfile", "{{CIDFILE}}",
    ]


def command_templates(checker: dict[str, Any], launcher_path: Path) -> dict[str, list[str]]:
    common = common_template(checker, launcher_path)
    return {
        "sandbox_command_argv": [
            *common, "--action", "run",
            "--request", "{{CHECKER_REQUEST_PATH}}",
            "--base-snapshot", "{{BASE_SNAPSHOT_PATH}}",
            "--patch", "{{PATCH_PATH}}",
            "--output", "{{CHECKER_OUTPUT_DIR}}",
            "--response", "{{CHECKER_RESPONSE_PATH}}",
            "--controller-entrypoint", checker["controller_entrypoint"],
            "--controller-uid", checker["controller_uid"],
            "--memory-mb", str(checker["budgets"]["memory_mb"]),
            "--pids-limit", str(checker["budgets"]["pids_limit"]),
            "--cpus", str(checker["budgets"]["cpus"]),
        ],
        "sandbox_cleanup_argv": [*common, "--action", "cleanup-cid"],
        "sandbox_inspect_argv": [*common, "--action", "inspect-cid"],
        "sandbox_cleanup_by_label_argv": [*common, "--action", "cleanup-label"],
        "sandbox_inspect_by_label_argv": [*common, "--action", "inspect-label"],
    }


def worker_command_prefix(checker: dict[str, Any]) -> list[str]:
    """Return the only production worker transition accepted by the checker."""
    worker_uid, worker_gid = checker["worker_uid"].split(":", 1)
    return [
        checker["controller_entrypoint"], "--worker-exec",
        "--uid", worker_uid, "--gid", worker_gid, "--",
    ]


def read_cid(path: Path) -> str:
    require(path.is_file() and not path.is_symlink(), "cidfile is missing or linked")
    text = path.read_text(encoding="ascii").strip()
    require(re.fullmatch(r"[A-Za-z0-9_.-]+", text) is not None,
            "cidfile contains an unsafe container ID")
    return text


def run_checked(command: list[str]) -> subprocess.CompletedProcess[bytes]:
    return subprocess.run(command, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, check=False)


def label_ids(runtime: Path, label: str) -> list[str]:
    outcome = run_checked([
        str(runtime), "ps", "--all", "--quiet", "--no-trunc",
        "--filter", f"label=abrl.checker_attempt={label}",
    ])
    require(outcome.returncode == 0, "Docker label inspection failed")
    return [line.strip() for line in outcome.stdout.decode("ascii").splitlines() if line.strip()]


def validate_image_inspect(payload: Any, image_digest: str, controller: str) -> None:
    require(isinstance(payload, dict) and payload.get("Id") == image_digest,
            "Docker image ID differs from the frozen digest")
    config = payload.get("Config")
    require(isinstance(config, dict)
            and config.get("Entrypoint") == [controller]
            and config.get("User") in {"0", "0:0", ""},
            "Docker image entrypoint/controller identity is not frozen")


def verify_image_contents(runtime: Path, args: argparse.Namespace) -> None:
    """Inspect and extract trusted checker bytes without executing the image."""
    inspected = run_checked([
        str(runtime), "image", "inspect", args.image_digest, "--format", "{{json .}}",
    ])
    require(inspected.returncode == 0 and 0 < len(inspected.stdout) <= MAX_RUNTIME_LEDGER_BYTES,
            "Docker image inspection failed")
    try:
        payload = json.loads(inspected.stdout.decode("utf-8"))
    except (UnicodeDecodeError, json.JSONDecodeError) as error:
        raise SystemExit(f"checker container launcher failed: malformed image inspect: {error}")
    validate_image_inspect(payload, args.image_digest, args.controller_entrypoint)

    audit_name = f"abrl-checker-image-audit-{uuid.uuid4().hex}"
    created = run_checked([
        str(runtime), "create", "--network", "none", "--name", audit_name,
        "--label", f"abrl.checker_attempt={args.attempt_label}",
        "--entrypoint", "/bin/true", args.image_digest,
    ])
    require(created.returncode == 0, "Docker image-audit container creation failed")
    cid = created.stdout.decode("ascii", errors="strict").strip()
    require(re.fullmatch(r"[A-Za-z0-9_.-]+", cid) is not None,
            "Docker image-audit container ID is invalid")
    failure = None
    try:
        with tempfile.TemporaryDirectory(prefix="abrl-checker-image-audit-") as directory:
            root = Path(directory)
            controller_copy = root / "controller.py"
            inner_copy = root / "inner.py"
            cache_manifest_copy = root / "cache-manifest.json"
            build_input_copy = root / "build-input-manifest.json"
            for source, target in (
                (args.controller_entrypoint, controller_copy),
                (INNER_CHECKER_PATH, inner_copy),
                (CHECKER_CACHE_MANIFEST_PATH, cache_manifest_copy),
                (CHECKER_BUILD_INPUT_MANIFEST_PATH, build_input_copy),
            ):
                copied = run_checked([str(runtime), "cp", f"{cid}:{source}", str(target)])
                require(copied.returncode == 0, f"Docker image audit could not extract {source}")
            require(controller_copy.is_file()
                    and controller_copy.stat().st_size <= MAX_RUNTIME_LEDGER_BYTES
                    and sha256(controller_copy) == args.controller_entrypoint_sha256,
                    "in-image controller bytes differ from the seal")
            require(inner_copy.is_file()
                    and inner_copy.stat().st_size <= MAX_RUNTIME_LEDGER_BYTES
                    and sha256(inner_copy) == args.inner_checker_sha256,
                    "in-image inner-checker bytes differ from the seal")
            require(cache_manifest_copy.is_file()
                    and cache_manifest_copy.stat().st_size <= MAX_CACHE_MANIFEST_BYTES
                    and sha256(cache_manifest_copy) == args.cache_manifest_sha256,
                    "in-image Lake cache manifest differs from the seal")
            require(build_input_copy.is_file()
                    and build_input_copy.stat().st_size <= MAX_RUNTIME_LEDGER_BYTES
                    and sha256(build_input_copy) == args.build_input_manifest_sha256,
                    "in-image checker build-input manifest differs from the seal")
    except BaseException as error:
        failure = error
    finally:
        removed = run_checked([str(runtime), "rm", "--force", cid])
        absent = run_checked([str(runtime), "container", "inspect", cid])
        require(removed.returncode == 0 and absent.returncode != 0,
                "Docker image-audit container cleanup was not proven complete")
    if failure is not None:
        raise failure


def docker_run_command(args: argparse.Namespace, runtime: Path) -> list[str]:
    """Construct the fixed, least-privilege production container command."""
    response_dir = args.response.resolve().parent
    return [
        str(runtime), "run", "--pull", "never", "--init", "--read-only",
        "--network", "none", "--cap-drop", "ALL",
        # The trusted root controller needs SETUID/SETGID to enter the sealed
        # worker identity.  FOWNER/DAC_OVERRIDE are restricted to sealing the
        # runner-owned output/response bind mounts before that transition.
        # Model-authored code is never executed before setuid/setgid clear the
        # effective capability set; the seven-probe response measures CapEff=0.
        "--cap-add", "SETUID", "--cap-add", "SETGID",
        "--cap-add", "FOWNER", "--cap-add", "DAC_OVERRIDE",
        "--security-opt", "no-new-privileges=true", "--user", args.controller_uid,
        "--pids-limit", str(args.pids_limit), "--memory", f"{args.memory_mb}m",
        "--cpus", str(args.cpus), "--cidfile", str(args.cidfile.resolve()),
        "--label", f"abrl.checker_attempt={args.attempt_label}",
        "--env", "PYTHONDONTWRITEBYTECODE=1", "--env", "HOME=/work/home",
        "--mount", f"type=bind,src={args.request.resolve()},dst=/input/request.json,readonly",
        "--mount", f"type=bind,src={args.base_snapshot.resolve()},dst=/input/base,readonly",
        "--mount", f"type=bind,src={args.patch.resolve()},dst=/input/submission.patch,readonly",
        "--mount", f"type=bind,src={args.output.resolve()},dst=/output",
        "--mount", f"type=bind,src={response_dir},dst=/response",
        "--tmpfs", f"/work:rw,nosuid,nodev,size={args.memory_mb}m",
        "--entrypoint", args.controller_entrypoint, args.image_digest,
        "--request", "/input/request.json", "--base-snapshot", "/input/base",
        "--patch", "/input/submission.patch", "--output", "/output",
        "--response", f"/response/{args.response.name}", "--work-dir", "/work",
    ]


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--action", choices=(
        "run", "inspect-cid", "cleanup-cid", "inspect-label", "cleanup-label",
    ), required=True)
    parser.add_argument("--host-python-sha256", required=True)
    parser.add_argument("--launcher-sha256", required=True)
    parser.add_argument("--runtime-kind", required=True)
    parser.add_argument("--runtime-executable", required=True)
    parser.add_argument("--runtime-executable-sha256", required=True)
    parser.add_argument("--runtime-version-output-sha256", required=True)
    parser.add_argument("--runtime-signature-output-sha256", required=True)
    parser.add_argument("--daemon-identity-output-sha256", required=True)
    parser.add_argument("--controller-entrypoint-sha256", required=True)
    parser.add_argument("--inner-checker-sha256", required=True)
    parser.add_argument("--cache-manifest-sha256", required=True)
    parser.add_argument("--build-input-manifest-sha256", required=True)
    parser.add_argument("--image-digest", required=True)
    parser.add_argument("--attempt-label", required=True)
    parser.add_argument("--cidfile", type=Path, required=True)
    parser.add_argument("--request", type=Path)
    parser.add_argument("--base-snapshot", type=Path)
    parser.add_argument("--patch", type=Path)
    parser.add_argument("--output", type=Path)
    parser.add_argument("--response", type=Path)
    parser.add_argument("--controller-entrypoint")
    parser.add_argument("--controller-uid")
    parser.add_argument("--memory-mb", type=int)
    parser.add_argument("--pids-limit", type=int)
    parser.add_argument("--cpus", type=float)
    args = parser.parse_args()
    runtime = verify_runtime(args)
    label = args.attempt_label
    require(re.fullmatch(r"[A-Za-z0-9_.-]{1,128}", label) is not None,
            "checker attempt label is unsafe")
    if args.action == "inspect-label":
        raise SystemExit(0 if label_ids(runtime, label) else ABSENT_EXIT_CODE)
    if args.action == "cleanup-label":
        ids = label_ids(runtime, label)
        if ids:
            outcome = run_checked([str(runtime), "rm", "--force", *ids])
            require(outcome.returncode == 0, "Docker label cleanup failed")
        raise SystemExit(0)
    if args.action == "inspect-cid":
        cid = read_cid(args.cidfile)
        outcome = run_checked([str(runtime), "container", "inspect", cid])
        raise SystemExit(0 if outcome.returncode == 0 else ABSENT_EXIT_CODE)
    if args.action == "cleanup-cid":
        cid = read_cid(args.cidfile)
        outcome = run_checked([str(runtime), "rm", "--force", cid])
        if outcome.returncode != 0:
            inspect = run_checked([str(runtime), "container", "inspect", cid])
            require(inspect.returncode != 0, "Docker cid cleanup failed")
        raise SystemExit(0)

    required = (
        args.request, args.base_snapshot, args.patch, args.output, args.response,
        args.controller_entrypoint, args.controller_uid, args.memory_mb,
        args.pids_limit, args.cpus,
    )
    require(all(value is not None for value in required), "run action is missing an input")
    require(re.fullmatch(r"sha256:[0-9a-f]{64}", args.image_digest) is not None,
            "checker image is not digest pinned")
    require(args.controller_uid == "0:0",
            "production controller must start as the sealed root controller")
    require(args.controller_entrypoint == CONTROLLER_PATH,
            "production controller entrypoint differs from the sealed path")
    verify_image_contents(runtime, args)
    command = docker_run_command(args, runtime)
    os.execv(str(runtime), command)


if __name__ == "__main__":
    main()
