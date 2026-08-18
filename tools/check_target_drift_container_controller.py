#!/usr/bin/env python3
"""Trusted in-image controller for normal checker runs and isolation probes."""

from __future__ import annotations

import argparse
import hashlib
import json
import os
import shutil
import socket
import stat
import subprocess
import sys
import time
from pathlib import Path
from typing import Any


INNER_CHECKER = Path("/usr/local/lib/abrl/check_target_drift_inner.py")
CONTROLLER = Path("/usr/local/bin/abrl-checker-controller")
CHECKER_CACHE_ROOT = Path("/opt/abrl-checker-cache/.lake")
CHECKER_CACHE_MANIFEST = Path("/opt/abrl-checker-cache/cache-manifest.json")
MAX_ID = 2 ** 31 - 1


def require(condition: bool, message: str) -> None:
    if not condition:
        raise SystemExit(f"checker container controller failed: {message}")


def load(path: Path) -> dict[str, Any]:
    value = json.loads(path.read_text(encoding="utf-8"))
    require(isinstance(value, dict), "request must be a JSON object")
    return value


def dump_atomic(path: Path, value: Any) -> None:
    temporary = path.with_name(path.name + ".tmp")
    temporary.write_text(
        json.dumps(value, indent=2, sort_keys=True, ensure_ascii=False) + "\n",
        encoding="utf-8",
    )
    os.replace(temporary, path)


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def canonical_bytes(value: Any) -> bytes:
    return json.dumps(value, sort_keys=True, separators=(",", ":"), ensure_ascii=False).encode()


def artifact_manifest(root: Path, maximum_bytes: int) -> list[dict[str, Any]]:
    entries: list[dict[str, Any]] = []
    total = 0
    for path in sorted(root.rglob("*")):
        info = path.lstat()
        relative = path.relative_to(root).as_posix()
        require(not stat.S_ISLNK(info.st_mode),
                f"output contains a link: {relative}")
        require(stat.S_ISDIR(info.st_mode) or stat.S_ISREG(info.st_mode),
                f"output contains a special file: {relative}")
        if stat.S_ISREG(info.st_mode):
            require(info.st_nlink == 1,
                    f"output contains a multiply linked file: {relative}")
            total += info.st_size
            require(total <= maximum_bytes, "output exceeds byte budget")
            entries.append({"path": relative, "bytes": info.st_size, "sha256": sha256(path)})
    return entries


def artifact_aggregate(entries: list[dict[str, Any]]) -> str:
    digest = hashlib.sha256()
    for entry in entries:
        payload = canonical_bytes(entry)
        digest.update(len(payload).to_bytes(8, "big"))
        digest.update(payload)
    return digest.hexdigest()


def worker_attempt(prefix: list[str], path: Path) -> bool:
    script = (
        "from pathlib import Path; import sys; p=Path(sys.argv[1]); "
        "p.parent.mkdir(parents=True, exist_ok=True); p.write_text('worker-write')"
    )
    outcome = subprocess.run(
        [*prefix, sys.executable, "-c", script, str(path)],
        stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL, check=False,
    )
    return outcome.returncode == 0


def validate_worker_prefix(prefix: Any) -> list[str]:
    require(isinstance(prefix, list) and len(prefix) == 7
            and all(isinstance(item, str) and item for item in prefix),
            "worker prefix has the wrong schema")
    require(prefix[0] == "/usr/local/bin/abrl-checker-controller"
            and prefix[1:3] == ["--worker-exec", "--uid"]
            and prefix[4] == "--gid" and prefix[6] == "--",
            "worker prefix does not invoke the sealed privilege transition")
    require(prefix[3].isdigit() and prefix[5].isdigit()
            and 0 < int(prefix[3]) <= MAX_ID and 0 < int(prefix[5]) <= MAX_ID,
            "worker prefix UID/GID is invalid")
    return prefix


def name_visible(filename: str) -> bool:
    for root, directories, files in os.walk("/", topdown=True):
        directories[:] = [
            name for name in directories
            if Path(root, name).as_posix() not in {"/proc", "/sys", "/dev"}
        ]
        if filename in files:
            return True
    return False


def worker_exec(argv: list[str]) -> None:
    """Irreversibly drop the trusted controller child to the Lean worker."""
    parser = argparse.ArgumentParser()
    parser.add_argument("--uid", type=int, required=True)
    parser.add_argument("--gid", type=int, required=True)
    parser.add_argument("command", nargs=argparse.REMAINDER)
    args = parser.parse_args(argv)
    command = args.command[1:] if args.command[:1] == ["--"] else args.command
    require(os.geteuid() == 0, "worker transition must begin in the trusted root controller")
    require(0 < args.uid <= MAX_ID and 0 < args.gid <= MAX_ID,
            "worker UID/GID must be positive numeric identities")
    require(bool(command) and all(isinstance(item, str) and item for item in command),
            "worker transition requires a command")
    os.setgroups([])
    os.setgid(args.gid)
    os.setuid(args.uid)
    require(os.geteuid() == args.uid and os.getegid() == args.gid,
            "worker privilege transition did not take effect")
    os.execvp(command[0], command)


def run_probe(request: dict[str, Any], base: Path, patch: Path,
              output: Path, response: Path, work: Path) -> None:
    require(CONTROLLER.is_file()
            and sha256(CONTROLLER) == request["controller_entrypoint_sha256"],
            "in-image controller differs from the request")
    contract = request["probe_contract"]
    prefix = validate_worker_prefix(request["worker_command_prefix"])
    work.chmod(0o711)
    replay = work / "replay"
    shutil.copytree(base, replay)
    apply = subprocess.run(
        ["git", "apply", str(patch)], cwd=replay,
        stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL, check=False,
    )
    require(apply.returncode == 0, "probe patch did not apply")
    controller_input = work / "controller-input"
    controller_input.mkdir(mode=0o700)
    for path in replay.rglob("*"):
        if path.is_dir():
            path.chmod(0o555)
        if path.is_file():
            path.chmod(0o444)
    replay.chmod(0o555)
    output.chmod(0o700)
    response.parent.chmod(0o700)
    writes = {
        "request": worker_attempt(prefix, Path("/input/request.json")),
        "base_snapshot": worker_attempt(prefix, Path("/input/base/ProbeSource.lean")),
        "patch": worker_attempt(prefix, Path("/input/submission.patch")),
        "cidfile": worker_attempt(prefix, Path("/forbidden/container.cid")),
        "patched_source": worker_attempt(prefix, replay / "ProbeSource.lean"),
        "controller_input": worker_attempt(prefix, controller_input / "worker-write"),
        "checker_output": worker_attempt(prefix, output / "worker-write"),
        "checker_response": worker_attempt(prefix, response),
    }
    network_succeeded = False
    network_script = (
        "import socket; socket.create_connection(('example.com',443),timeout=3)"
    )
    network = subprocess.run(
        [*prefix, sys.executable, "-c", network_script],
        stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL, check=False,
    )
    network_succeeded = network.returncode == 0
    subprocess.Popen(
        [*prefix, sys.executable, "-c", "import time; time.sleep(600)"],
        stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL,
    )
    dump_atomic(response, {
        "schema_version": 1,
        "mode": "checker_isolation_probe",
        "probe_nonce": request["probe_nonce"],
        "checker_attempt_label": request["checker_attempt_label"],
        "checker_runtime_config_sha256": request["checker_runtime_config_sha256"],
        "container_image_digest": request["container_image_digest"],
        "controller_entrypoint_sha256": request["controller_entrypoint_sha256"],
        "process_exit_code": 0,
        "observations": {
            "network_request_succeeded": network_succeeded,
            "host_sentinel_visible": name_visible(
                contract["forbidden_host_sentinel_filename"]
            ),
            "operator_ground_truth_visible": name_visible(
                contract["forbidden_operator_ground_truth_filename"]
            ),
            "worker_write_succeeded": writes,
            "background_probe_started": True,
        },
    })


def run_normal(request_path: Path, request: dict[str, Any], base: Path, patch: Path,
               output: Path, response: Path, work: Path) -> None:
    require(CONTROLLER.is_file()
            and sha256(CONTROLLER) == request["controller_entrypoint_sha256"],
            "in-image controller differs from the request")
    validate_worker_prefix(request["worker_command_prefix"])
    require(INNER_CHECKER.is_file() and sha256(INNER_CHECKER) == request["inner_checker_sha256"],
            "in-image inner checker differs from the request")
    require(CHECKER_CACHE_ROOT.is_dir() and CHECKER_CACHE_MANIFEST.is_file()
            and sha256(CHECKER_CACHE_MANIFEST)
            == request["checker_cache_manifest_sha256"],
            "in-image Lake cache manifest differs from the request")
    output.chmod(0o700)
    response.parent.chmod(0o700)
    # Worker children may traverse into the explicitly prepared replay/cache
    # paths but cannot create entries at the work-root boundary.
    work.chmod(0o711)
    started = time.monotonic()
    process = subprocess.run([
        sys.executable, str(INNER_CHECKER),
        "--request", str(request_path), "--base-snapshot", str(base),
        "--patch", str(patch), "--output", str(output), "--work-dir", str(work),
        "--cache-root", str(CHECKER_CACHE_ROOT),
        "--cache-manifest", str(CHECKER_CACHE_MANIFEST),
    ], stdout=subprocess.PIPE, stderr=subprocess.STDOUT, check=False)
    logs = output / "logs"
    logs.mkdir(exist_ok=True)
    (logs / "inner-controller.log").write_bytes(process.stdout)
    require(process.returncode == 0, "inner checker process failed")
    manifest = artifact_manifest(output, request["resource_limits"]["maximum_output_bytes"])
    result_path = output / "checker-result.json"
    require(result_path.is_file(), "inner checker did not produce checker-result.json")
    dump_atomic(response, {
        "schema_version": 1,
        "opaque_run_id": request["opaque_run_id"],
        "checker_attempt_id": request["checker_attempt_id"],
        "checker_attempt_label": request["checker_attempt_label"],
        "request_sha256": sha256(request_path),
        "checker_id": request["checker_id"],
        "checker_version": request["checker_version"],
        "inner_checker_sha256": request["inner_checker_sha256"],
        "controller_entrypoint_sha256": request["controller_entrypoint_sha256"],
        "checker_contract_sha256": request["checker_contract_sha256"],
        "checker_runtime_config_sha256": request["checker_runtime_config_sha256"],
        "container_image_digest": request["container_image_digest"],
        "filesystem_network_process_attestation": request[
            "filesystem_network_process_attestation"
        ],
        "controller_worker_separation_attestation": request[
            "controller_worker_separation_attestation"
        ],
        "termination": "completed",
        "checker_result_sha256": sha256(result_path),
        "artifact_manifest": manifest,
        "artifact_aggregate_sha256": artifact_aggregate(manifest),
        "process_exit_code": process.returncode,
        "measured_wall_seconds": round(time.monotonic() - started, 6),
    })


def main() -> None:
    if sys.argv[1:2] == ["--worker-exec"]:
        worker_exec(sys.argv[2:])
        return
    parser = argparse.ArgumentParser()
    parser.add_argument("--request", type=Path, required=True)
    parser.add_argument("--base-snapshot", type=Path, required=True)
    parser.add_argument("--patch", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--response", type=Path, required=True)
    parser.add_argument("--work-dir", type=Path, required=True)
    args = parser.parse_args()
    request = load(args.request)
    if request.get("mode") == "checker_isolation_probe":
        run_probe(request, args.base_snapshot, args.patch, args.output, args.response, args.work_dir)
    else:
        run_normal(
            args.request, request, args.base_snapshot, args.patch,
            args.output, args.response, args.work_dir,
        )


if __name__ == "__main__":
    main()
