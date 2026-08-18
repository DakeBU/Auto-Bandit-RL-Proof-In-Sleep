#!/usr/bin/env python3
"""Prepare and, on an audited Docker host, build the production checker image."""

from __future__ import annotations

import argparse
import hashlib
import json
import os
import re
import shutil
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

import launch_target_drift_checker_container as launcher  # noqa: E402
import target_drift_checker_cache_manifest as cache_manifest  # noqa: E402


SUITE_ID = "ABRL-TARGET-DRIFT-V2"
FULL_COMMIT = re.compile(r"[0-9a-f]{40}")
DIGEST_IMAGE = re.compile(r"[^\s@]+@sha256:[0-9a-f]{64}")
IMAGE_TAG = re.compile(r"[A-Za-z0-9][A-Za-z0-9._/-]*(?::[A-Za-z0-9._-]+)?")
SOURCE_PATHS = (
    "BanditRLProof",
    "BanditRLProof.lean",
    "Tests",
    "Tests.lean",
    "lake-manifest.json",
    "lakefile.lean",
    "lean-toolchain",
    "LICENSE",
)
TOOLCHAIN_PROBE_SOURCE = b"import Init\n#check Nat\n"
DOCKER_COMMAND_TIMEOUT_SECONDS = 120
DOCKER_BUILD_TIMEOUT_SECONDS = 2 * 60 * 60
MAX_DOCKER_COMMAND_OUTPUT_BYTES = 4 * 1024 * 1024
MAX_DOCKER_BUILD_LOG_BYTES = 256 * 1024 * 1024
CONTEXT_INPUTS = {
    "Containerfile": ROOT / "evaluation" / "target-drift-v2" / "checker-image.Containerfile",
    "check_target_drift_container_controller.py": (
        TOOLS / "check_target_drift_container_controller.py"
    ),
    "check_target_drift_inner.py": TOOLS / "check_target_drift_inner.py",
    "target_drift_checker_cache_manifest.py": (
        TOOLS / "target_drift_checker_cache_manifest.py"
    ),
}
BUILDER_PATH = Path(__file__).resolve()


def require(condition: bool, message: str) -> None:
    if not condition:
        raise SystemExit(f"target-drift checker-image preparation failed: {message}")


def sha256_file(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        for block in iter(lambda: handle.read(1024 * 1024), b""):
            digest.update(block)
    return digest.hexdigest()


def canonical_bytes(value: Any) -> bytes:
    return json.dumps(
        value, sort_keys=True, separators=(",", ":"), ensure_ascii=False
    ).encode("utf-8")


def aggregate(entries: list[dict[str, Any]]) -> str:
    return hashlib.sha256(canonical_bytes(entries)).hexdigest()


def git_blob_sha1(payload: bytes) -> str:
    header = f"blob {len(payload)}\0".encode("ascii")
    return hashlib.sha1(header + payload).hexdigest()


def git(*arguments: str, text: bool = True) -> str | bytes:
    outcome = subprocess.run(
        ["git", *arguments], cwd=ROOT, stdout=subprocess.PIPE,
        stderr=subprocess.PIPE, text=text, check=False,
    )
    require(outcome.returncode == 0,
            f"git {' '.join(arguments)} failed: "
            f"{outcome.stderr.strip() if text else outcome.stderr[:500]!r}")
    return outcome.stdout


def require_commit(commit: str) -> None:
    require(FULL_COMMIT.fullmatch(commit) is not None,
            "workspace base must be a lowercase full Git commit")
    git("cat-file", "-e", f"{commit}^{{commit}}")


def repo_relative(path: Path) -> str:
    resolved = path.resolve()
    require(ROOT.resolve() in resolved.parents,
            f"provenance input is outside the repository: {resolved}")
    return resolved.relative_to(ROOT.resolve()).as_posix()


def checkout_source_bytes(path: Path) -> bytes:
    # Git attributes make the committed Linux image input LF-stable.  Treat a
    # Windows checkout's CRLF presentation as the same source while retaining
    # a separate raw source hash in the runtime seal.
    return path.read_bytes().replace(b"\r\n", b"\n")


def committed_input(commit: str, path: Path) -> tuple[bytes, dict[str, str]]:
    relative = repo_relative(path)
    try:
        payload = git("show", f"{commit}:{relative}", text=False)
        object_id = git("rev-parse", f"{commit}:{relative}").strip()
    except SystemExit:
        return b"", {"path": relative, "git_object": "UNTRACKED", "sha256": "UNSET"}
    assert isinstance(payload, bytes) and isinstance(object_id, str)
    payload = payload.replace(b"\r\n", b"\n")
    return payload, {
        "path": relative,
        "git_object": object_id,
        "sha256": hashlib.sha256(payload).hexdigest(),
    }


def archived_tree_entries(commit: str) -> list[dict[str, str]]:
    raw = git("ls-tree", "-r", "-z", commit, "--", *SOURCE_PATHS, text=False)
    assert isinstance(raw, bytes)
    entries: list[dict[str, str]] = []
    for record in raw.split(b"\0"):
        if not record:
            continue
        metadata, encoded_path = record.split(b"\t", 1)
        mode, kind, object_id = metadata.decode("ascii").split(" ")
        path = encoded_path.decode("utf-8")
        require(kind == "blob" and mode in {"100644", "100755"},
                f"base allowlist contains a non-regular Git object: {path} ({mode} {kind})")
        entries.append({"path": path, "mode": mode, "git_object": object_id})
    require(bool(entries), "base allowlist is empty")
    present = {entry["path"].split("/", 1)[0] for entry in entries}
    for source in SOURCE_PATHS:
        if "/" not in source:
            require(source in present, f"base commit omits required path {source}")
    return sorted(entries, key=lambda entry: entry["path"])


def git_blob_payloads(entries: list[dict[str, str]]) -> dict[str, bytes]:
    """Read raw Git blobs in one batch, bypassing checkout/archive EOL filters."""
    process = subprocess.Popen(
        ["git", "cat-file", "--batch"], cwd=ROOT,
        stdin=subprocess.PIPE, stdout=subprocess.PIPE, stderr=subprocess.PIPE,
    )
    assert process.stdin is not None and process.stdout is not None
    try:
        payloads: dict[str, bytes] = {}
        for entry in entries:
            # Request and consume one object at a time.  Writing the complete
            # request set first can deadlock when Git fills the stdout pipe
            # before it has consumed all stdin on repositories with long files.
            process.stdin.write((entry["git_object"] + "\n").encode("ascii"))
            process.stdin.flush()
            header = process.stdout.readline().decode("ascii").strip().split(" ")
            require(len(header) == 3
                    and header[0] == entry["git_object"]
                    and header[1] == "blob"
                    and header[2].isdigit(),
                    f"git cat-file returned a malformed header for {entry['path']}")
            size = int(header[2])
            payload = process.stdout.read(size)
            require(len(payload) == size and process.stdout.read(1) == b"\n",
                    f"git cat-file truncated {entry['path']}")
            require(git_blob_sha1(payload) == entry["git_object"],
                    f"Git blob digest mismatch for {entry['path']}")
            payloads[entry["path"]] = payload
        process.stdin.close()
        stderr = process.stderr.read() if process.stderr is not None else b""
        require(process.wait() == 0, f"git cat-file --batch failed: {stderr[:500]!r}")
        process.stdout.close()
        if process.stderr is not None:
            process.stderr.close()
        return payloads
    finally:
        if process.poll() is None:
            process.kill()
            process.wait()


def parse_lean_toolchain(payload: bytes) -> str:
    text = payload.decode("utf-8", errors="strict").strip()
    match = re.fullmatch(
        r"leanprover/lean4:v([0-9]+\.[0-9]+\.[0-9]+(?:[-+][^\s]+)?)", text
    )
    require(match is not None, "lean-toolchain does not name a supported Lean release")
    return match.group(1)


def lean_toolchain_release(commit: str) -> str:
    entry = next(
        item for item in archived_tree_entries(commit) if item["path"] == "lean-toolchain"
    )
    return parse_lean_toolchain(git_blob_payloads([entry])["lean-toolchain"])


def parse_lean_version_output(output: str) -> str:
    match = re.fullmatch(
        r"Lean \(version ([0-9]+\.[0-9]+\.[0-9]+(?:[-+][^,\s)]+)?), [^)]+\)",
        output.strip(),
    )
    require(match is not None, "Lean --version output has an unexpected shape")
    return match.group(1)


def parse_lake_lean_version_output(output: str) -> str:
    match = re.fullmatch(
        r"Lake version [^\r\n]+ \(Lean version "
        r"([0-9]+\.[0-9]+\.[0-9]+(?:[-+][^\s)]+)?)\)",
        output.strip(),
    )
    require(match is not None, "lake --version output has an unexpected shape")
    return match.group(1)


def source_records_from_git(commit: str) -> list[dict[str, Any]]:
    """Recompute the public baseline manifest directly from frozen Git objects."""
    require_commit(commit)
    tree_entries = archived_tree_entries(commit)
    file_bytes = git_blob_payloads(tree_entries)
    records: list[dict[str, Any]] = []
    for entry in tree_entries:
        payload = file_bytes[entry["path"]]
        require(git_blob_sha1(payload) == entry["git_object"],
                f"Git archive object mismatch for {entry['path']}")
        records.append({
            "path": entry["path"], "bytes": len(payload),
            "sha256": hashlib.sha256(payload).hexdigest(),
            "mode": entry["mode"], "git_object": entry["git_object"],
        })
    return records


def validate_build_input_payload(
    payload: Any, *, expected_workspace_commit: str | None = None,
    expected_orchestrator_commit: str | None = None,
) -> dict[str, Any]:
    require(isinstance(payload, dict)
            and payload.get("schema_version") == 1
            and payload.get("suite_id") == SUITE_ID
            and payload.get("status") == "prepared_unbuilt",
            "production build-input manifest identity/status is malformed")
    workspace_commit = payload.get("workspace_base_commit", "")
    orchestrator_commit = payload.get("orchestrator_commit", "")
    require(FULL_COMMIT.fullmatch(workspace_commit) is not None
            and FULL_COMMIT.fullmatch(orchestrator_commit) is not None,
            "build-input commit provenance is malformed")
    require(expected_workspace_commit is None
            or workspace_commit == expected_workspace_commit,
            "build-input workspace commit differs from the execution protocol")
    require(expected_orchestrator_commit is None
            or orchestrator_commit == expected_orchestrator_commit,
            "build-input orchestrator commit differs from the sealed execution code")
    require(payload.get("dirty_test_fixture_inputs") == [],
            "production build input contains dirty fixture markers")
    require(payload.get("source_allowlist") == list(SOURCE_PATHS),
            "build-input source allowlist differs from the frozen policy")
    expected_source = source_records_from_git(workspace_commit)
    require(payload.get("source_files") == expected_source
            and payload.get("source_files_aggregate_sha256") == aggregate(expected_source),
            "build-input source bytes do not match workspace_base_commit")

    provenance = payload.get("orchestrator_inputs")
    expected_paths = [*CONTEXT_INPUTS.values(), BUILDER_PATH]
    expected_provenance: list[dict[str, str]] = []
    context_inputs: list[dict[str, Any]] = []
    target_names = {repo_relative(path): name for name, path in CONTEXT_INPUTS.items()}
    for path in expected_paths:
        committed, record = committed_input(orchestrator_commit, path)
        require(record["git_object"] != "UNTRACKED",
                f"orchestrator commit omits image input {record['path']}")
        expected_provenance.append(record)
        if record["path"] in target_names:
            context_inputs.append({
                "path": target_names[record["path"]], "bytes": len(committed),
                "sha256": hashlib.sha256(committed).hexdigest(),
            })
    expected_provenance.sort(key=lambda item: item["path"])
    require(provenance == expected_provenance,
            "build-input orchestrator file ledger differs from Git")

    expected_context = [
        {"path": f"checker-base/{item['path']}", "bytes": item["bytes"],
         "sha256": item["sha256"]}
        for item in expected_source
    ] + context_inputs
    expected_context.sort(key=lambda item: item["path"])
    require(payload.get("context_files") == expected_context
            and payload.get("context_files_aggregate_sha256") == aggregate(expected_context),
            "build-input context ledger differs from the two frozen Git snapshots")
    require(DIGEST_IMAGE.fullmatch(payload.get("lean_base_image", "")) is not None
            and payload.get("lean_base_image_digest")
            == payload["lean_base_image"].rsplit("@", 1)[1],
            "build-input base image is not digest-pinned")
    return payload


def file_manifest(root: Path, excluded: set[str] | None = None) -> list[dict[str, Any]]:
    excluded = excluded or set()
    entries: list[dict[str, Any]] = []
    paths = [item for item in root.rglob("*") if item.is_file()]
    for path in sorted(paths, key=lambda item: item.relative_to(root).as_posix()):
        relative = path.relative_to(root).as_posix()
        if relative in excluded:
            continue
        require(not path.is_symlink(), f"context contains a linked file: {relative}")
        entries.append({
            "path": relative,
            "bytes": path.stat().st_size,
            "sha256": sha256_file(path),
        })
    return entries


def write_new_json(path: Path, value: Any) -> None:
    require(not path.exists(), f"refusing to overwrite {path}")
    path.parent.mkdir(parents=True, exist_ok=True)
    descriptor = os.open(path, os.O_WRONLY | os.O_CREAT | os.O_EXCL, 0o644)
    try:
        with os.fdopen(descriptor, "w", encoding="utf-8", newline="\n") as handle:
            json.dump(value, handle, indent=2, sort_keys=True, ensure_ascii=False)
            handle.write("\n")
    except BaseException:
        path.unlink(missing_ok=True)
        raise


def prepare_context(
    commit: str, base_image: str, output: Path, *, allow_dirty_test_fixture: bool = False
) -> None:
    require_commit(commit)
    require(DIGEST_IMAGE.fullmatch(base_image) is not None,
            "Lean base image must be a digest-pinned name@sha256:... reference")
    output = output.resolve()
    require(not output.exists(), f"refusing to overwrite context directory {output}")
    require(output.parent.is_dir(), "context parent directory does not exist")
    tree_entries = archived_tree_entries(commit)
    orchestrator_commit = str(git("rev-parse", "HEAD")).strip()
    require_commit(orchestrator_commit)
    provenance: list[dict[str, str]] = []
    committed_payloads: dict[str, bytes] = {}
    dirty_inputs: list[str] = []
    for path in [*CONTEXT_INPUTS.values(), BUILDER_PATH]:
        committed, record = committed_input(orchestrator_commit, path)
        current = checkout_source_bytes(path)
        if record["git_object"] == "UNTRACKED" or committed != current:
            dirty_inputs.append(record["path"])
            record["sha256"] = hashlib.sha256(current).hexdigest()
            committed_payloads[record["path"]] = current
        else:
            committed_payloads[record["path"]] = committed
        provenance.append(record)
    require(not dirty_inputs or allow_dirty_test_fixture,
            "checker-image inputs differ from the current Git commit: "
            + ", ".join(dirty_inputs))
    if os.name == "nt":
        longest = max(len(entry["path"]) for entry in tree_entries)
        require(len(str(output)) + len("\\checker-base\\") + longest < 240,
                "Windows checker context path is too long; use a short path such as "
                "C:\\abrl-checker-context")

    temporary = Path(tempfile.mkdtemp(prefix=f".{output.name}-", dir=output.parent))
    try:
        checker_base = temporary / "checker-base"
        checker_base.mkdir()
        blob_payloads = git_blob_payloads(tree_entries)
        for entry in tree_entries:
            target = checker_base / Path(entry["path"])
            target.parent.mkdir(parents=True, exist_ok=True)
            target.write_bytes(blob_payloads[entry["path"]])
            target.chmod(0o755 if entry["mode"] == "100755" else 0o644)
        extracted = file_manifest(checker_base)
        require([item["path"] for item in extracted]
                == [item["path"] for item in tree_entries],
                "extracted base snapshot differs from the frozen Git allowlist")

        for target_name, source in CONTEXT_INPUTS.items():
            require(source.is_file(), f"missing context input {source}")
            # Build from the orchestrator Git object on a clean run.  The only
            # bypass is an explicitly marked, unbuildable unit-test fixture.
            data = committed_payloads[repo_relative(source)]
            (temporary / target_name).write_bytes(data)

        context_entries = file_manifest(temporary)
        tree_by_path = {item["path"]: item for item in tree_entries}
        source_entries = [
            {
                "path": item["path"], "bytes": item["bytes"],
                "sha256": item["sha256"],
                "mode": tree_by_path[item["path"]]["mode"],
                "git_object": tree_by_path[item["path"]]["git_object"],
            }
            for item in extracted
        ]
        manifest = {
            "schema_version": 1,
            "suite_id": SUITE_ID,
            "status": (
                "test_fixture_unbuildable" if dirty_inputs else "prepared_unbuilt"
            ),
            "workspace_base_commit": commit,
            "orchestrator_commit": orchestrator_commit,
            "orchestrator_inputs": sorted(provenance, key=lambda item: item["path"]),
            "dirty_test_fixture_inputs": sorted(dirty_inputs),
            "lean_base_image": base_image,
            "lean_base_image_digest": base_image.rsplit("@", 1)[1],
            "source_allowlist": list(SOURCE_PATHS),
            "source_files": source_entries,
            "source_files_aggregate_sha256": aggregate(source_entries),
            "context_files": context_entries,
            "context_files_aggregate_sha256": aggregate(context_entries),
            "nonclaim": (
                "This deterministic context is not a built checker image, a passed "
                "isolation probe, or a model execution result."
            ),
        }
        write_new_json(temporary / "checker-image-build-input.json", manifest)
        os.replace(temporary, output)
    except BaseException:
        shutil.rmtree(temporary, ignore_errors=True)
        raise
    print(json.dumps({
        "status": "test_fixture_unbuildable" if dirty_inputs else "prepared_unbuilt",
        "context": str(output),
        "workspace_base_commit": commit,
        "source_files": len(tree_entries),
        "build_input_manifest_sha256": sha256_file(
            output / "checker-image-build-input.json"
        ),
    }, sort_keys=True))


def validate_context(
    context: Path, *, require_current_provenance: bool = False,
    allow_test_fixture: bool = False,
) -> dict[str, Any]:
    context = context.resolve()
    cache_manifest.require_plain_tree(context)
    manifest_path = context / "checker-image-build-input.json"
    require(manifest_path.is_file() and not manifest_path.is_symlink(),
            "build-input manifest is missing or linked")
    payload = json.loads(manifest_path.read_text(encoding="utf-8"))
    require(isinstance(payload, dict)
            and payload.get("schema_version") == 1
            and payload.get("suite_id") == SUITE_ID
            and payload.get("status") in {"prepared_unbuilt", "test_fixture_unbuildable"}
            and FULL_COMMIT.fullmatch(payload.get("workspace_base_commit", ""))
            and FULL_COMMIT.fullmatch(payload.get("orchestrator_commit", ""))
            and DIGEST_IMAGE.fullmatch(payload.get("lean_base_image", "")),
            "build-input manifest identity is malformed")
    require(payload["status"] == "prepared_unbuilt" or allow_test_fixture,
            "unit-test build context is explicitly ineligible for image construction")
    dirty = payload.get("dirty_test_fixture_inputs")
    provenance = payload.get("orchestrator_inputs")
    require(isinstance(dirty, list) and all(isinstance(item, str) for item in dirty)
            and isinstance(provenance, list) and bool(provenance),
            "build-input provenance ledger is malformed")
    if payload["status"] == "prepared_unbuilt":
        require(dirty == [], "production build context contains dirty-input markers")
    actual = file_manifest(context, {"checker-image-build-input.json"})
    require(actual == payload.get("context_files")
            and aggregate(actual) == payload.get("context_files_aggregate_sha256"),
            "build context bytes differ from the frozen input manifest")
    source = file_manifest(context / "checker-base")
    source_records = payload.get("source_files")
    require(isinstance(source_records, list)
            and all(isinstance(item, dict) and set(item) == {
                "path", "bytes", "sha256", "mode", "git_object"
            } for item in source_records),
            "checker base source manifest has the wrong schema")
    source_projection = [
        {"path": item["path"], "bytes": item["bytes"], "sha256": item["sha256"]}
        for item in source_records
    ]
    require(source == source_projection
            and aggregate(source_records) == payload.get("source_files_aggregate_sha256"),
            "checker base snapshot differs from the frozen input manifest")
    require_commit(payload["workspace_base_commit"])
    expected_tree = archived_tree_entries(payload["workspace_base_commit"])
    require([
        {"path": item["path"], "mode": item["mode"], "git_object": item["git_object"]}
        for item in source_records
    ] == expected_tree, "checker base Git objects differ from workspace_base_commit")
    for item in source_records:
        data = (context / "checker-base" / Path(item["path"])).read_bytes()
        require(git_blob_sha1(data) == item["git_object"],
                f"checker base bytes differ from Git object {item['path']}")
    require(payload["lean_base_image_digest"]
            == payload["lean_base_image"].rsplit("@", 1)[1],
            "base image digest differs from its pinned reference")
    if require_current_provenance:
        head = str(git("rev-parse", "HEAD")).strip()
        require(head == payload["orchestrator_commit"],
                "current Git commit differs from the image build provenance")
        expected_paths = {
            repo_relative(path): path for path in [*CONTEXT_INPUTS.values(), BUILDER_PATH]
        }
        require({item.get("path") for item in provenance} == set(expected_paths),
                "image build provenance omits or adds an orchestrator input")
        for record in provenance:
            path = expected_paths[record["path"]]
            committed, actual_record = committed_input(head, path)
            require(actual_record == record
                    and committed == checkout_source_bytes(path),
                    f"orchestrator input is dirty or changed: {record['path']}")
        if payload["status"] == "prepared_unbuilt":
            validate_build_input_payload(
                payload,
                expected_workspace_commit=payload["workspace_base_commit"],
                expected_orchestrator_commit=head,
            )
    return payload


def run_to_capped_file(
    command: list[str], handle: Any, *, timeout_seconds: int, max_bytes: int,
) -> int:
    """Run without a shell while bounding time and bytes written by Docker."""
    process = subprocess.Popen(command, stdout=handle, stderr=subprocess.STDOUT)
    deadline = time.monotonic() + timeout_seconds
    failure: str | None = None
    try:
        while process.poll() is None:
            size = os.fstat(handle.fileno()).st_size
            if size > max_bytes:
                failure = f"output exceeded {max_bytes} bytes"
                process.kill()
                break
            if time.monotonic() >= deadline:
                failure = f"command exceeded {timeout_seconds} seconds"
                process.kill()
                break
            time.sleep(0.1)
        try:
            returncode = process.wait(timeout=30)
        except subprocess.TimeoutExpired:
            process.kill()
            returncode = process.wait(timeout=30)
            failure = failure or "process did not exit after termination"
        size = os.fstat(handle.fileno()).st_size
        if size > max_bytes:
            failure = failure or f"output exceeded {max_bytes} bytes"
        require(failure is None, f"Docker command failed closed: {failure}")
        return returncode
    except BaseException:
        if process.poll() is None:
            process.kill()
            process.wait(timeout=30)
        raise


def docker_checked(command: list[str], log: Path | None = None) -> bytes:
    if log is None:
        with tempfile.TemporaryFile(mode="w+b") as handle:
            returncode = run_to_capped_file(
                command, handle,
                timeout_seconds=DOCKER_COMMAND_TIMEOUT_SECONDS,
                max_bytes=MAX_DOCKER_COMMAND_OUTPUT_BYTES,
            )
            handle.seek(0)
            output = handle.read(MAX_DOCKER_COMMAND_OUTPUT_BYTES + 1)
        require(returncode == 0,
                f"Docker command failed: {' '.join(command[:3])}: {output[:1000]!r}")
        return output
    require(not log.exists(), f"refusing to overwrite build log {log}")
    with log.open("xb") as handle:
        returncode = run_to_capped_file(
            command, handle,
            timeout_seconds=DOCKER_BUILD_TIMEOUT_SECONDS,
            max_bytes=MAX_DOCKER_BUILD_LOG_BYTES,
        )
    require(returncode == 0, f"Docker image build failed; inspect {log}")
    return b""


def docker_cleanup_absent(runtime: Path, container_name: str) -> None:
    """Best-effort removal followed by a fail-closed proof of absence."""
    subprocess.run(
        [str(runtime), "rm", "--force", container_name], stdout=subprocess.DEVNULL,
        stderr=subprocess.DEVNULL, timeout=DOCKER_COMMAND_TIMEOUT_SECONDS, check=False,
    )
    # `inspect != 0` is not an absence proof: daemon/permission failures also
    # return nonzero.  A successful, exact-name inventory with no ID is.
    inventory = subprocess.run(
        [str(runtime), "ps", "--all", "--quiet", "--no-trunc",
         "--filter", f"name=^/{container_name}$"],
        stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
        timeout=DOCKER_COMMAND_TIMEOUT_SECONDS, check=False,
    )
    require(inventory.returncode == 0
            and len(inventory.stdout) <= MAX_DOCKER_COMMAND_OUTPUT_BYTES
            and inventory.stdout.strip() == b"",
            f"Docker audit-container absence was not proven: {container_name}")


def offline_image_command(
    runtime: Path, image_digest: str, probe_root: Path,
    executable: str, arguments: list[str],
) -> bytes:
    audit_name = f"abrl-checker-toolchain-{uuid.uuid4().hex}"
    try:
        return docker_checked([
            str(runtime), "run", "--name", audit_name, "--pull", "never",
            "--network", "none", "--read-only", "--cap-drop", "ALL",
            "--security-opt", "no-new-privileges=true", "--user", "10002:10002",
            "--pids-limit", "32", "--memory", "512m", "--cpus", "1",
            "--tmpfs", "/tmp:rw,nosuid,nodev,size=16m", "--env", "HOME=/tmp",
            "--mount", f"type=bind,src={probe_root.resolve()},dst=/probe,readonly",
            "--workdir", "/probe", "--entrypoint", executable,
            image_digest, *arguments,
        ])
    finally:
        docker_cleanup_absent(runtime, audit_name)


def trusted_version(
    runtime: Path, image_digest: str, probe_root: Path, executable: str
) -> str:
    output = offline_image_command(
        runtime, image_digest, probe_root, executable, ["--version"]
    )
    require(0 < len(output) <= launcher.MAX_RUNTIME_LEDGER_BYTES,
            f"{executable} version output is empty or oversized")
    return output.decode("utf-8", errors="strict").strip()


def offline_toolchain_probe(
    runtime: Path, image_digest: str, lean_toolchain_bytes: bytes
) -> dict[str, str]:
    release = parse_lean_toolchain(lean_toolchain_bytes)
    with tempfile.TemporaryDirectory(prefix="abrl-checker-toolchain-probe-") as directory:
        probe_root = Path(directory)
        # TemporaryDirectory is 0700 on Linux.  The probe deliberately runs as
        # the restricted worker UID, so the read-only bind source must be
        # traversable without granting it any write permission.
        probe_root.chmod(0o755)
        (probe_root / "lean-toolchain").write_bytes(lean_toolchain_bytes)
        (probe_root / "ToolchainProbe.lean").write_bytes(TOOLCHAIN_PROBE_SOURCE)
        if os.name != "nt":
            (probe_root / "lean-toolchain").chmod(0o444)
            (probe_root / "ToolchainProbe.lean").chmod(0o444)
        output = offline_image_command(
            runtime, image_digest, probe_root, "lean", ["ToolchainProbe.lean"]
        )
        require(len(output) <= launcher.MAX_RUNTIME_LEDGER_BYTES,
                "offline Lean probe output is oversized")
        lean_version = trusted_version(runtime, image_digest, probe_root, "lean")
        lake_version = trusted_version(runtime, image_digest, probe_root, "lake")
        python_version = trusted_version(runtime, image_digest, probe_root, "python3")
    require(parse_lean_version_output(lean_version) == release,
            "final image Lean version differs from the frozen lean-toolchain release")
    require(parse_lake_lean_version_output(lake_version) == release,
            "final image Lake is not bound to the frozen Lean release")
    return {
        "toolchain_release": release,
        "offline_toolchain_probe": "passed_network_none_as_worker",
        "toolchain_probe_source_sha256": hashlib.sha256(
            TOOLCHAIN_PROBE_SOURCE
        ).hexdigest(),
        "lean_version": lean_version,
        "lake_version": lake_version,
        "python_version": python_version,
    }


def extract_image_file(runtime: Path, image_digest: str, source: str, target: Path) -> None:
    audit_name = f"abrl-checker-build-audit-{uuid.uuid4().hex}"
    failure: BaseException | None = None
    try:
        created = docker_checked([
            str(runtime), "create", "--network", "none", "--name", audit_name,
            "--entrypoint", "/bin/true", image_digest,
        ]).decode("ascii").strip()
        require(re.fullmatch(r"[A-Za-z0-9_.-]+", created) is not None,
                "Docker image-audit container ID is invalid")
        docker_checked([str(runtime), "cp", f"{created}:{source}", str(target)])
    except BaseException as error:
        failure = error
    finally:
        docker_cleanup_absent(runtime, audit_name)
    if failure is not None:
        raise failure


def build_image(
    context: Path, image_tag: str, sbom_output: Path,
    cache_manifest_output: Path, build_log: Path,
) -> None:
    require(IMAGE_TAG.fullmatch(image_tag) is not None, "image tag is malformed")
    source_context = context.resolve()
    source_manifest = validate_context(source_context, require_current_provenance=True)
    sbom_output = sbom_output.resolve()
    cache_manifest_output = cache_manifest_output.resolve()
    build_log = build_log.resolve()
    for output in (sbom_output, cache_manifest_output, build_log):
        require(source_context not in output.parents,
                "image outputs must be outside the immutable build context")
    require(not sbom_output.exists(), f"refusing to overwrite {sbom_output}")
    require(not cache_manifest_output.exists(),
            f"refusing to overwrite {cache_manifest_output}")
    runtime = launcher.canonical_docker_executable()
    runtime_digest = sha256_file(runtime)
    identity = launcher.runtime_identity(runtime)
    require("os=linux" in identity["runtime_version"],
            "checker image must be built by a Linux Docker daemon")

    # Docker never reads the operator-visible context directly.  Snapshot it to
    # a random sibling, validate the snapshot, build only that copy, and verify
    # it again after Docker has finished consuming it.  A concurrent mutation
    # therefore cannot be accepted into the SBOM/hash chain.
    snapshot_holder = tempfile.TemporaryDirectory(prefix=".ai-", dir=source_context.parent)
    context = Path(snapshot_holder.name).resolve()
    shutil.copytree(source_context, context, dirs_exist_ok=True)
    manifest = validate_context(context, require_current_provenance=True)
    require(manifest == source_manifest, "private build snapshot differs from input context")

    with tempfile.TemporaryDirectory(prefix="abrl-checker-image-build-") as directory:
        iidfile = Path(directory) / "image-id.txt"
        docker_checked([
            str(runtime), "build", "--pull=false", "--no-cache",
            "--build-arg", f"LEAN_BASE_IMAGE={manifest['lean_base_image']}",
            "--build-arg", f"WORKSPACE_BASE_COMMIT={manifest['workspace_base_commit']}",
            "--build-arg", (
                "SOURCE_FILES_AGGREGATE_SHA256="
                + manifest["source_files_aggregate_sha256"]
            ),
            "--build-arg", (
                "BUILD_INPUT_MANIFEST_SHA256="
                + sha256_file(context / "checker-image-build-input.json")
            ),
            "--build-arg", (
                "CHECKER_IMAGE_RECIPE_SHA256=" + sha256_file(context / "Containerfile")
            ),
            "--build-arg", f"BASE_IMAGE_DIGEST={manifest['lean_base_image_digest']}",
            "--build-arg", "LEAN_TOOLCHAIN_SHA256=" + next(
                item["sha256"] for item in manifest["source_files"]
                if item["path"] == "lean-toolchain"
            ),
            "--iidfile", str(iidfile), "--tag", image_tag,
            "--file", str(context / "Containerfile"), str(context),
        ], build_log)
        require(iidfile.is_file(), "Docker build did not publish an image ID")
        image_digest = iidfile.read_text(encoding="ascii").strip()
    require(validate_context(context, require_current_provenance=True) == manifest,
            "private build context changed while Docker consumed it")
    require(re.fullmatch(r"sha256:[0-9a-f]{64}", image_digest) is not None,
            "Docker build returned a nonimmutable image ID")

    inspected = json.loads(docker_checked([
        str(runtime), "image", "inspect", image_digest, "--format", "{{json .}}",
    ]).decode("utf-8"))
    launcher.validate_image_inspect(inspected, image_digest, launcher.CONTROLLER_PATH)

    with tempfile.TemporaryDirectory(prefix="abrl-checker-image-extract-") as directory:
        extracted = Path(directory) / "cache-manifest.json"
        build_input_extracted = Path(directory) / "build-input-manifest.json"
        extract_image_file(
            runtime, image_digest, launcher.CHECKER_CACHE_MANIFEST_PATH, extracted
        )
        extract_image_file(
            runtime, image_digest,
            "/opt/abrl-checker-cache/build-input-manifest.json",
            build_input_extracted,
        )
        require(build_input_extracted.read_bytes()
                == (context / "checker-image-build-input.json").read_bytes(),
                "in-image build-input manifest differs from the frozen context")
        cache_payload = cache_manifest.load_manifest(extracted)
        cache_manifest_sha256 = sha256_file(extracted)
        expected_cache_provenance = {
            "workspace_base_commit": manifest["workspace_base_commit"],
            "source_files_aggregate_sha256": manifest[
                "source_files_aggregate_sha256"
            ],
            "build_input_manifest_sha256": sha256_file(
                context / "checker-image-build-input.json"
            ),
            "checker_image_recipe_sha256": sha256_file(context / "Containerfile"),
            "base_image_digest": manifest["lean_base_image_digest"].split(":", 1)[1],
            "lean_toolchain_sha256": next(
                item["sha256"] for item in manifest["source_files"]
                if item["path"] == "lean-toolchain"
            ),
        }
        require(cache_payload["provenance"] == expected_cache_provenance,
                "in-image cache provenance differs from the frozen build input")
        cache_manifest_bytes = extracted.read_bytes()

    audit_args = argparse.Namespace(
        image_digest=image_digest,
        controller_entrypoint=launcher.CONTROLLER_PATH,
        attempt_label=f"ABRL-IMAGE-BUILD-{uuid.uuid4().hex}",
        controller_entrypoint_sha256=sha256_file(
            context / "check_target_drift_container_controller.py"
        ),
        inner_checker_sha256=sha256_file(context / "check_target_drift_inner.py"),
        cache_manifest_sha256=cache_manifest_sha256,
        build_input_manifest_sha256=sha256_file(
            context / "checker-image-build-input.json"
        ),
    )
    launcher.verify_image_contents(runtime, audit_args)
    toolchain_probe = offline_toolchain_probe(
        runtime, image_digest, (context / "checker-base" / "lean-toolchain").read_bytes()
    )
    descriptor = os.open(
        cache_manifest_output, os.O_WRONLY | os.O_CREAT | os.O_EXCL, 0o644
    )
    try:
        with os.fdopen(descriptor, "wb") as handle:
            handle.write(cache_manifest_bytes)
    except BaseException:
        cache_manifest_output.unlink(missing_ok=True)
        raise

    sbom = {
        "schema_version": 1,
        "suite_id": SUITE_ID,
        "status": "built_manifest_verified_probe_pending",
        "container_image_digest": image_digest,
        "checker_image_recipe_sha256": sha256_file(context / "Containerfile"),
        "controller_entrypoint_sha256": sha256_file(
            context / "check_target_drift_container_controller.py"
        ),
        "inner_checker_sha256": sha256_file(context / "check_target_drift_inner.py"),
        "cache_manifest_tool_sha256": sha256_file(
            context / "target_drift_checker_cache_manifest.py"
        ),
        "image_context_builder_sha256": sha256_file(Path(__file__).resolve()),
        "build_input_manifest_sha256": sha256_file(
            context / "checker-image-build-input.json"
        ),
        "source_snapshot_manifest_sha256": manifest[
            "source_files_aggregate_sha256"
        ],
        "workspace_base_commit": manifest["workspace_base_commit"],
        "controller_uid": "0:0",
        "worker_uid": "10002:10002",
        "base_image_digest": manifest["lean_base_image_digest"],
        "base_image_reference": manifest["lean_base_image"],
        "toolchain_release": toolchain_probe["toolchain_release"],
        "offline_toolchain_probe": toolchain_probe["offline_toolchain_probe"],
        "toolchain_probe_source_sha256": toolchain_probe[
            "toolchain_probe_source_sha256"
        ],
        "lean_version": toolchain_probe["lean_version"],
        "lake_version": toolchain_probe["lake_version"],
        "python_version": toolchain_probe["python_version"],
        "lake_cache_manifest_sha256": cache_manifest_sha256,
        "checker_cache_root": launcher.CHECKER_CACHE_ROOT,
        "checker_cache_manifest_path": launcher.CHECKER_CACHE_MANIFEST_PATH,
        "docker_executable_sha256": runtime_digest,
        "docker_runtime_identity": identity,
        "image_build_log_sha256": sha256_file(build_log),
        "nonclaim": (
            "The controller, inner checker, build input, and cache manifest were built "
            "and extracted from the image; cache provenance was checked. This record "
            "does not replace the seven production isolation probes and is not a model run."
        ),
    }
    write_new_json(sbom_output, sbom)
    print(json.dumps({
        "status": "built_manifest_verified_probe_pending",
        "container_image_digest": image_digest,
        "sbom": str(sbom_output),
        "sbom_sha256": sha256_file(sbom_output),
        "cache_manifest": str(cache_manifest_output),
        "cache_manifest_sha256": cache_manifest_sha256,
        "build_log_sha256": sha256_file(build_log),
    }, sort_keys=True))


def main() -> None:
    parser = argparse.ArgumentParser()
    subparsers = parser.add_subparsers(dest="command", required=True)
    prepare = subparsers.add_parser("prepare-context")
    prepare.add_argument("--workspace-base-commit", required=True)
    prepare.add_argument("--lean-base-image", required=True)
    prepare.add_argument("--output", type=Path, required=True)
    verify = subparsers.add_parser("verify-context")
    verify.add_argument("--context", type=Path, required=True)
    build = subparsers.add_parser("build-image")
    build.add_argument("--context", type=Path, required=True)
    build.add_argument("--image-tag", required=True)
    build.add_argument("--sbom-output", type=Path, required=True)
    build.add_argument("--cache-manifest-output", type=Path, required=True)
    build.add_argument("--build-log", type=Path, required=True)
    args = parser.parse_args()

    if args.command == "prepare-context":
        prepare_context(args.workspace_base_commit, args.lean_base_image, args.output)
    elif args.command == "verify-context":
        payload = validate_context(args.context)
        print(json.dumps({
            "status": "verified_unbuilt",
            "context": str(args.context.resolve()),
            "workspace_base_commit": payload["workspace_base_commit"],
            "build_input_manifest_sha256": sha256_file(
                args.context.resolve() / "checker-image-build-input.json"
            ),
        }, sort_keys=True))
    else:
        build_image(
            args.context, args.image_tag, args.sbom_output,
            args.cache_manifest_output, args.build_log,
        )


if __name__ == "__main__":
    main()
