#!/usr/bin/env python3
"""Prepare and build the result-free provider-client-capable agent image.

The image is layered on the already cache-complete checker image.  The Codex
registry tarball is verified and reduced to an explicit member allowlist before
Docker receives the context.  This tool never accepts provider credentials and
never invokes a model.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import os
import re
import shutil
import stat
import subprocess
import sys
import tarfile
import tempfile
from pathlib import Path, PurePosixPath
from typing import Any


TOOLS = Path(__file__).resolve().parent
ROOT = TOOLS.parent
sys.path.insert(0, str(TOOLS))

import launch_target_drift_checker_container as checker_launcher  # noqa: E402
import prepare_target_drift_checker_image as checker_image  # noqa: E402


SUITE_ID = "ABRL-TARGET-DRIFT-V2"
FULL_COMMIT = re.compile(r"[0-9a-f]{40}")
IMAGE_DIGEST = re.compile(r"sha256:[0-9a-f]{64}")
IMAGE_REFERENCE = re.compile(r"[A-Za-z0-9][A-Za-z0-9._/-]*(?::[A-Za-z0-9._-]+)?")
SOURCE_LOCK = ROOT / "evaluation/target-drift-v2/agent-image-sources.json"
CONTEXT_INPUTS = {
    "Containerfile": ROOT / "evaluation/target-drift-v2/agent-image.Containerfile",
    "target_drift_agent_pid1.py": TOOLS / "target_drift_agent_pid1.py",
    "codex_target_drift_adapter.py": TOOLS / "codex_target_drift_adapter.py",
    "target_drift_agent_excluded_adapter.py": (
        TOOLS / "target_drift_agent_excluded_adapter.py"
    ),
    "target_drift_agent_outer_controller.py": (
        TOOLS / "target_drift_agent_outer_controller.py"
    ),
    "target_drift_agent_outer_probe.py": TOOLS / "target_drift_agent_outer_probe.py",
    "target_drift_agent_model_probe.py": TOOLS / "target_drift_agent_model_probe.py",
    "agent-excluded-execution-contract.json": (
        ROOT / "evaluation/target-drift-v2/agent-excluded-execution-contract.json"
    ),
    "agent-excluded-execution-request.json": (
        ROOT / "evaluation/target-drift-v2/agent-excluded-execution-request.json"
    ),
    "agent-image-sources.json": SOURCE_LOCK,
}
BUILDER_PATH = Path(__file__).resolve()
CODEX_INSTALL_ROOT = "/opt/abrl-codex"
CONTROLLER_PATH = "/usr/local/bin/abrl-agent-pid1"
ADAPTER_PATH = "/usr/local/lib/abrl/codex_target_drift_adapter.py"
EXCLUDED_ADAPTER_PATH = (
    "/usr/local/lib/abrl/target_drift_agent_excluded_adapter.py"
)
OUTER_CONTROLLER_PATH = "/usr/local/lib/abrl/target_drift_agent_outer_controller.py"
OUTER_PROBE_PATH = "/usr/local/lib/abrl/target_drift_agent_outer_probe.py"
MODEL_PROBE_PATH = "/usr/local/lib/abrl/target_drift_agent_model_probe.py"
EXCLUDED_CONTRACT_PATH = (
    "/usr/local/share/abrl/agent-excluded-execution-contract.json"
)
CODEX_PATH = "/opt/abrl-codex/codex"
MAX_PACKAGE_BYTES = 128 * 1024 * 1024


def require(condition: bool, message: str) -> None:
    if not condition:
        raise SystemExit(f"target-drift agent-image preparation failed: {message}")


def load(path: Path) -> dict[str, Any]:
    return json.loads(path.read_text(encoding="utf-8"))


def sha256_file(path: Path) -> str:
    return checker_image.sha256_file(path)


def sha512_file(path: Path) -> str:
    digest = hashlib.sha512()
    with path.open("rb") as stream:
        for block in iter(lambda: stream.read(1024 * 1024), b""):
            digest.update(block)
    return digest.hexdigest()


def regular_file(path: Path, label: str) -> Path:
    info = path.lstat()
    reparse = bool(getattr(info, "st_file_attributes", 0) & 0x400)
    require(stat.S_ISREG(info.st_mode) and not path.is_symlink()
            and not reparse and info.st_nlink == 1,
            f"{label} is not a single-linked regular file")
    return path


def write_new_json(path: Path, value: Any) -> None:
    require(not path.exists(), f"refusing to overwrite {path}")
    path.parent.mkdir(parents=True, exist_ok=True)
    descriptor = os.open(path, os.O_WRONLY | os.O_CREAT | os.O_EXCL, 0o644)
    try:
        with os.fdopen(descriptor, "w", encoding="utf-8", newline="\n") as stream:
            json.dump(value, stream, indent=2, sort_keys=True, ensure_ascii=False)
            stream.write("\n")
    except BaseException:
        path.unlink(missing_ok=True)
        raise


def write_new_bytes(path: Path, value: bytes) -> None:
    require(not path.exists(), f"refusing to overwrite {path}")
    path.parent.mkdir(parents=True, exist_ok=True)
    descriptor = os.open(path, os.O_WRONLY | os.O_CREAT | os.O_EXCL, 0o644)
    try:
        with os.fdopen(descriptor, "wb") as stream:
            stream.write(value)
    except BaseException:
        path.unlink(missing_ok=True)
        raise


def validate_source_lock(payload: Any) -> dict[str, Any]:
    require(isinstance(payload, dict)
            and payload.get("schema_version") == 1
            and payload.get("suite_id") == SUITE_ID
            and payload.get("status") == "result_free_source_lock"
            and payload.get("platform") == "x86_64-unknown-linux-musl",
            "agent-image source lock identity is malformed")
    codex = payload.get("codex_cli")
    require(isinstance(codex, dict)
            and re.fullmatch(r"[0-9]+\.[0-9]+\.[0-9]+", codex.get("version", ""))
            and codex.get("package") == f"@openai/codex@{codex.get('version')}-linux-x64"
            and re.fullmatch(r"https://registry\.npmjs\.org/@openai/codex/-/"
                             r"codex-[0-9.]+-linux-x64\.tgz",
                             codex.get("tarball_url", ""))
            and re.fullmatch(r"sha512-[A-Za-z0-9+/]+={0,2}",
                             codex.get("sha512_sri", ""))
            and re.fullmatch(r"[0-9a-f]{128}", codex.get("sha512_hex", "")),
            "Codex package source lock is malformed")
    decoded = __import__("base64").b64decode(
        codex["sha512_sri"].split("-", 1)[1], validate=True
    ).hex()
    require(decoded == codex["sha512_hex"],
            "Codex SRI and hexadecimal SHA-512 disagree")
    members = codex.get("required_members")
    require(isinstance(members, dict) and set(members) == {
        "codex", "bwrap", "rg", "package_json",
    } and all(isinstance(value, str)
              and PurePosixPath(value).parts[:1] == ("package",)
              and ".." not in PurePosixPath(value).parts
              for value in members.values()),
            "Codex package member allowlist is malformed")
    return payload


def verify_codex_package(package: Path, lock: dict[str, Any]) -> dict[str, bytes]:
    regular_file(package, "Codex registry tarball")
    require(package.stat().st_size <= MAX_PACKAGE_BYTES,
            "Codex registry tarball exceeds the frozen size ceiling")
    codex = lock["codex_cli"]
    require(sha512_file(package) == codex["sha512_hex"],
            "Codex registry tarball differs from the frozen SHA-512")
    required = {value: key for key, value in codex["required_members"].items()}
    extracted: dict[str, bytes] = {}
    with tarfile.open(package, "r:gz") as archive:
        members = archive.getmembers()
        names = [member.name for member in members]
        require(len(names) == len(set(names)), "Codex tarball repeats a member name")
        for member in members:
            path = PurePosixPath(member.name)
            require(not path.is_absolute() and ".." not in path.parts,
                    f"Codex tarball contains an unsafe path: {member.name}")
            require(not member.issym() and not member.islnk(),
                    f"Codex tarball contains a linked member: {member.name}")
            if member.name in required:
                require(member.isfile(),
                        f"allowlisted Codex member is not regular: {member.name}")
                handle = archive.extractfile(member)
                require(handle is not None, f"cannot read Codex member {member.name}")
                extracted[required[member.name]] = handle.read()
    require(set(extracted) == set(codex["required_members"]),
            "Codex tarball omits an allowlisted member")
    package_json = json.loads(extracted["package_json"].decode("utf-8"))
    require(package_json.get("name") == "@openai/codex"
            and package_json.get("version") == codex["version"] + "-linux-x64",
            "Codex native package identity differs from the source lock")
    return extracted


def current_commit() -> str:
    value = subprocess.check_output(
        ["git", "rev-parse", "HEAD"], cwd=ROOT, text=True
    ).strip()
    require(FULL_COMMIT.fullmatch(value) is not None, "HEAD is not a full commit")
    return value


def committed_context_inputs(commit: str) -> tuple[list[dict[str, str]], dict[str, bytes]]:
    records: list[dict[str, str]] = []
    payloads: dict[str, bytes] = {}
    for target, path in [*CONTEXT_INPUTS.items(), ("builder", BUILDER_PATH)]:
        payload, record = checker_image.committed_input(commit, path)
        require(record["git_object"] != "UNTRACKED",
                f"agent-image input is absent from {commit}: {record['path']}")
        require(payload == checker_image.checkout_source_bytes(path),
                f"agent-image input differs from {commit}: {record['path']}")
        records.append(record)
        payloads[target] = payload
    records.sort(key=lambda item: item["path"])
    return records, payloads


def validate_checker_evidence(
    checker_digest: str, checker_sbom: Path, checker_cache_manifest: Path,
    checker_build_input: Path, *, expected_orchestrator_commit: str | None = None,
) -> tuple[dict[str, Any], dict[str, Any], dict[str, Any]]:
    checker_payload = load(regular_file(checker_sbom, "checker image SBOM"))
    build_input_payload = checker_image.validate_build_input_payload(
        load(regular_file(checker_build_input, "checker image build input")),
        expected_orchestrator_commit=expected_orchestrator_commit,
    )
    cache_payload = checker_image.cache_manifest.load_manifest(
        regular_file(checker_cache_manifest, "checker cache manifest")
    )
    require(
        checker_payload.get("schema_version") == 1
        and checker_payload.get("suite_id") == SUITE_ID
        and checker_payload.get("status") == "built_manifest_verified_probe_pending"
        and checker_payload.get("container_image_digest") == checker_digest,
        "checker SBOM does not bind the requested cache-complete image",
    )
    build_input_sha256 = sha256_file(checker_build_input)
    cache_sha256 = sha256_file(checker_cache_manifest)
    require(
        checker_payload.get("build_input_manifest_sha256") == build_input_sha256
        and checker_payload.get("lake_cache_manifest_sha256") == cache_sha256
        and checker_payload.get("workspace_base_commit")
        == build_input_payload["workspace_base_commit"]
        and checker_payload.get("source_snapshot_manifest_sha256")
        == build_input_payload["source_files_aggregate_sha256"],
        "checker SBOM disagrees with its raw build-input/cache sidecars",
    )
    lean_toolchain_sha256 = next(
        item["sha256"] for item in build_input_payload["source_files"]
        if item["path"] == "lean-toolchain"
    )
    require(
        cache_payload["provenance"] == {
            "workspace_base_commit": build_input_payload["workspace_base_commit"],
            "source_files_aggregate_sha256": build_input_payload[
                "source_files_aggregate_sha256"
            ],
            "build_input_manifest_sha256": build_input_sha256,
            "checker_image_recipe_sha256": checker_payload[
                "checker_image_recipe_sha256"
            ],
            "base_image_digest": checker_payload["base_image_digest"].split(":", 1)[1],
            "lean_toolchain_sha256": lean_toolchain_sha256,
        },
        "checker cache provenance disagrees with the raw checker evidence",
    )
    return checker_payload, cache_payload, build_input_payload


def prepare_context(
    checker_reference: str, checker_digest: str, checker_sbom: Path,
    checker_cache_manifest: Path, checker_build_input: Path,
    codex_package: Path, output: Path,
) -> None:
    require(IMAGE_REFERENCE.fullmatch(checker_reference) is not None,
            "checker image reference must be a local immutable build tag")
    require(IMAGE_DIGEST.fullmatch(checker_digest) is not None,
            "checker image digest is malformed")
    checker_sbom = checker_sbom.resolve()
    checker_cache_manifest = checker_cache_manifest.resolve()
    checker_build_input = checker_build_input.resolve()
    commit = current_commit()
    checker_payload, _, checker_build_payload = validate_checker_evidence(
        checker_digest, checker_sbom, checker_cache_manifest, checker_build_input,
        expected_orchestrator_commit=commit,
    )
    lean_toolchain_record = next(
        item for item in checker_build_payload["source_files"]
        if item["path"] == "lean-toolchain"
    )
    lean_toolchain_bytes = checker_image.git(
        "cat-file", "blob", lean_toolchain_record["git_object"], text=False
    )
    assert isinstance(lean_toolchain_bytes, bytes)
    require(
        hashlib.sha256(lean_toolchain_bytes).hexdigest()
        == lean_toolchain_record["sha256"]
        and checker_image.git_blob_sha1(lean_toolchain_bytes)
        == lean_toolchain_record["git_object"],
        "checker lean-toolchain Git object differs from the raw build input",
    )
    checker_toolchain_release = checker_image.parse_lean_toolchain(
        lean_toolchain_bytes
    )
    require(
        checker_payload.get("toolchain_release") == checker_toolchain_release
        and checker_image.parse_lean_version_output(
            checker_payload.get("lean_version", "")
        ) == checker_toolchain_release
        and checker_image.parse_lake_lean_version_output(
            checker_payload.get("lake_version", "")
        ) == checker_toolchain_release
        and checker_payload.get("offline_toolchain_probe")
        == "passed_network_none_as_worker",
        "checker SBOM toolchain evidence differs from the frozen Git object",
    )
    lock = validate_source_lock(load(SOURCE_LOCK))
    package_members = verify_codex_package(codex_package.resolve(), lock)
    provenance, inputs = committed_context_inputs(commit)
    output = output.resolve()
    require(not output.exists(), f"refusing to overwrite context {output}")
    require(output.parent.is_dir(), "agent-image context parent is missing")

    temporary = Path(tempfile.mkdtemp(prefix=f".{output.name}-", dir=output.parent))
    try:
        for target in CONTEXT_INPUTS:
            if target == "agent-image-sources.json":
                continue
            (temporary / target).write_bytes(inputs[target])
        checker_dir = temporary / "checker-evidence"
        checker_dir.mkdir()
        for name, source in {
            "checker-image-sbom.json": checker_sbom,
            "checker-cache-manifest.json": checker_cache_manifest,
            "checker-image-build-input.json": checker_build_input,
        }.items():
            (checker_dir / name).write_bytes(source.read_bytes())
        (checker_dir / "lean-toolchain").write_bytes(lean_toolchain_bytes)
        codex_dir = temporary / "codex"
        codex_dir.mkdir()
        for name, payload in package_members.items():
            target = "package.json" if name == "package_json" else name
            (codex_dir / target).write_bytes(payload)
        context_files = checker_image.file_manifest(temporary)
        manifest = {
            "schema_version": 1,
            "suite_id": SUITE_ID,
            "status": "prepared_unbuilt_result_free",
            "orchestrator_commit": commit,
            "checker_image_reference": checker_reference,
            "checker_image_digest": checker_digest,
            "checker_image_sbom_sha256": sha256_file(checker_sbom),
            "checker_cache_manifest_sha256": sha256_file(checker_cache_manifest),
            "checker_build_input_sha256": sha256_file(checker_build_input),
            "checker_workspace_base_commit": checker_build_payload[
                "workspace_base_commit"
            ],
            "checker_source_snapshot_manifest_sha256": checker_payload[
                "source_snapshot_manifest_sha256"
            ],
            "checker_toolchain_release": checker_toolchain_release,
            "checker_lean_version": checker_payload["lean_version"],
            "checker_lake_version": checker_payload["lake_version"],
            "checker_python_version": checker_payload["python_version"],
            "source_lock_sha256": sha256_file(SOURCE_LOCK),
            "codex_version": lock["codex_cli"]["version"],
            "codex_package": lock["codex_cli"]["package"],
            "codex_package_sha512": sha512_file(codex_package),
            "codex_members": {
                name: {"bytes": len(payload), "sha256": hashlib.sha256(payload).hexdigest()}
                for name, payload in sorted(package_members.items())
            },
            "orchestrator_inputs": provenance,
            "context_files": context_files,
            "context_files_aggregate_sha256": checker_image.aggregate(context_files),
            "nonclaim": (
                "This context contains no credential and makes no provider or model call. "
                "It is a build input for a result-free agent-image candidate."
            ),
        }
        write_new_json(temporary / "agent-image-build-input.json", manifest)
        temporary.rename(output)
    except BaseException:
        shutil.rmtree(temporary, ignore_errors=True)
        raise
    print(json.dumps({
        "status": manifest["status"], "context": str(output),
        "manifest_sha256": sha256_file(output / "agent-image-build-input.json"),
    }, sort_keys=True))


def validate_context(context: Path, *, current_provenance: bool = True) -> dict[str, Any]:
    context = context.resolve()
    require(context.is_dir() and not context.is_symlink(),
            "agent-image context is not a plain directory")
    manifest_path = regular_file(
        context / "agent-image-build-input.json", "agent-image build input"
    )
    payload = load(manifest_path)
    require(payload.get("schema_version") == 1
            and payload.get("suite_id") == SUITE_ID
            and payload.get("status") == "prepared_unbuilt_result_free"
            and FULL_COMMIT.fullmatch(payload.get("orchestrator_commit", "")) is not None
            and IMAGE_REFERENCE.fullmatch(payload.get("checker_image_reference", ""))
            is not None
            and IMAGE_DIGEST.fullmatch(payload.get("checker_image_digest", "")) is not None,
            "agent-image build input identity is malformed")
    lock = validate_source_lock(load(SOURCE_LOCK))
    require(payload.get("source_lock_sha256") == sha256_file(SOURCE_LOCK)
            and payload.get("codex_version") == lock["codex_cli"]["version"]
            and payload.get("codex_package") == lock["codex_cli"]["package"]
            and payload.get("codex_package_sha512") == lock["codex_cli"]["sha512_hex"],
            "agent-image source-lock binding differs")
    checker_dir = context / "checker-evidence"
    checker_sbom = regular_file(
        checker_dir / "checker-image-sbom.json", "context checker image SBOM"
    )
    checker_cache = regular_file(
        checker_dir / "checker-cache-manifest.json", "context checker cache manifest"
    )
    checker_build_input = regular_file(
        checker_dir / "checker-image-build-input.json",
        "context checker image build input",
    )
    lean_toolchain = regular_file(
        checker_dir / "lean-toolchain", "context checker lean-toolchain"
    )
    checker_payload, _, checker_build_payload = validate_checker_evidence(
        payload["checker_image_digest"], checker_sbom, checker_cache,
        checker_build_input,
        expected_orchestrator_commit=payload["orchestrator_commit"],
    )
    require(
        payload.get("checker_image_sbom_sha256") == sha256_file(checker_sbom)
        and payload.get("checker_cache_manifest_sha256") == sha256_file(checker_cache)
        and payload.get("checker_build_input_sha256")
        == sha256_file(checker_build_input)
        and payload.get("checker_workspace_base_commit")
        == checker_build_payload["workspace_base_commit"]
        and payload.get("checker_source_snapshot_manifest_sha256")
        == checker_payload["source_snapshot_manifest_sha256"],
        "agent-image checker evidence binding differs",
    )
    lean_toolchain_record = next(
        item for item in checker_build_payload["source_files"]
        if item["path"] == "lean-toolchain"
    )
    lean_toolchain_bytes = lean_toolchain.read_bytes()
    checker_toolchain_release = checker_image.parse_lean_toolchain(
        lean_toolchain_bytes
    )
    require(
        hashlib.sha256(lean_toolchain_bytes).hexdigest()
        == lean_toolchain_record["sha256"]
        and checker_image.git_blob_sha1(lean_toolchain_bytes)
        == lean_toolchain_record["git_object"]
        and payload.get("checker_toolchain_release")
        == checker_toolchain_release
        and payload.get("checker_lean_version") == checker_payload.get("lean_version")
        and payload.get("checker_lake_version") == checker_payload.get("lake_version")
        and payload.get("checker_python_version")
        == checker_payload.get("python_version")
        and checker_image.parse_lean_version_output(
            checker_payload.get("lean_version", "")
        ) == checker_toolchain_release
        and checker_image.parse_lake_lean_version_output(
            checker_payload.get("lake_version", "")
        ) == checker_toolchain_release
        and checker_payload.get("offline_toolchain_probe")
        == "passed_network_none_as_worker",
        "agent-image checker toolchain binding differs",
    )
    excluded_contract_path = regular_file(
        context / "agent-excluded-execution-contract.json",
        "excluded-execution contract",
    )
    excluded_request_path = regular_file(
        context / "agent-excluded-execution-request.json",
        "excluded-execution request",
    )
    excluded_adapter_path = regular_file(
        context / "target_drift_agent_excluded_adapter.py",
        "excluded-execution adapter",
    )
    excluded_contract = load(excluded_contract_path)
    excluded_request = load(excluded_request_path)
    require(
        excluded_contract.get("schema_version") == 1
        and excluded_contract.get("suite_id") == SUITE_ID
        and excluded_contract.get("status")
        == "result_free_excluded_provider_component_contract"
        and excluded_contract.get("primary_result_eligible") is False
        and excluded_contract.get("provider_execution_enabled") is False
        and excluded_contract.get("request", {}).get("sha256")
        == sha256_file(excluded_request_path)
        and excluded_contract.get("adapter", {}).get("sha256")
        == sha256_file(excluded_adapter_path)
        and excluded_request.get("primary_result_eligible") is False
        and excluded_request.get("provider_runtime", {}).get(
            "provider_execution_enabled"
        ) is False
        and excluded_request.get("provider_runtime", {}).get("model_call_budget") == 0,
        "excluded-execution contract/request/adapter binding is invalid",
    )
    files = checker_image.file_manifest(
        context, excluded={"agent-image-build-input.json"}
    )
    require(payload.get("context_files") == files
            and payload.get("context_files_aggregate_sha256")
            == checker_image.aggregate(files),
            "agent-image context bytes differ from the build input")
    expected_members = {}
    for name in ("codex", "bwrap", "rg", "package_json"):
        target = "package.json" if name == "package_json" else name
        path = regular_file(context / "codex" / target, f"Codex member {name}")
        expected_members[name] = {"bytes": path.stat().st_size, "sha256": sha256_file(path)}
    require(payload.get("codex_members") == expected_members,
            "extracted Codex members differ from the frozen ledger")
    if current_provenance:
        require(payload["orchestrator_commit"] == current_commit(),
                "agent-image context belongs to another orchestrator commit")
        provenance, _ = committed_context_inputs(payload["orchestrator_commit"])
        require(payload.get("orchestrator_inputs") == provenance,
                "agent-image orchestrator provenance differs from Git")
    return payload


def docker_output(command: list[str], *, timeout: int = 120) -> bytes:
    process = subprocess.run(
        command, stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
        check=False, timeout=timeout,
    )
    require(process.returncode == 0,
            f"Docker command failed ({process.returncode}): {process.stdout[-2000:]!r}")
    require(len(process.stdout) <= checker_image.MAX_DOCKER_COMMAND_OUTPUT_BYTES,
            "Docker command output exceeded the evidence ceiling")
    return process.stdout


def validate_codex_version_output(payload: bytes, expected_version: str) -> str:
    """Require one exact Codex version line in bounded Docker output.

    Docker writes daemon notices to stderr, and ``docker_output`` deliberately
    preserves stderr together with stdout for the evidence boundary.  Those
    notices must not make the source-locked client version look different, but
    neither may an absent or duplicated version observation pass.
    """
    try:
        text = payload.decode("utf-8", errors="strict")
    except UnicodeDecodeError as exc:
        raise SystemExit(
            "target-drift agent-image preparation failed: "
            "in-image Codex version output is not UTF-8"
        ) from exc
    expected = f"codex-cli {expected_version}"
    identity_lines = [
        line for line in text.splitlines()
        if re.fullmatch(r"codex-cli\s+\S+", line) is not None
    ]
    require(identity_lines == [expected],
            "in-image Codex version differs from the source lock")
    return expected


def extract_image(runtime: Path, image_digest: str, source: str) -> bytes:
    with tempfile.TemporaryDirectory(prefix="abrl-agent-image-extract-") as directory:
        target = Path(directory) / "artifact"
        checker_image.extract_image_file(runtime, image_digest, source, target)
        regular_file(target, f"in-image {source}")
        return target.read_bytes()


def build_image(
    context: Path, image_tag: str, sbom_output: Path, build_log: Path,
) -> None:
    require(IMAGE_REFERENCE.fullmatch(image_tag) is not None, "agent image tag is malformed")
    source_context = context.resolve()
    source_manifest = validate_context(source_context)
    sbom_output = sbom_output.resolve()
    build_log = build_log.resolve()
    codex_version_output_path = sbom_output.with_name(
        "agent-codex-version-output.log"
    )
    require(not sbom_output.exists() and not build_log.exists()
            and not codex_version_output_path.exists(),
            "agent-image output already exists")
    runtime = checker_launcher.canonical_docker_executable()
    identity = checker_launcher.runtime_identity(runtime)
    require("os=linux" in identity["runtime_version"],
            "agent image must be built by a Linux Docker daemon")
    inspected_base = json.loads(docker_output([
        str(runtime), "image", "inspect", source_manifest["checker_image_reference"],
        "--format", "{{json .}}",
    ]).decode("utf-8"))
    require(inspected_base.get("Id") == source_manifest["checker_image_digest"],
            "local checker tag does not resolve to the frozen base digest")

    holder = tempfile.TemporaryDirectory(prefix=".agent-image-", dir=source_context.parent)
    context = Path(holder.name).resolve()
    shutil.copytree(source_context, context, dirs_exist_ok=True)
    manifest = validate_context(context)
    require(manifest == source_manifest, "private agent build snapshot differs")
    with tempfile.TemporaryDirectory(prefix="abrl-agent-image-iid-") as directory:
        iid = Path(directory) / "image-id.txt"
        checker_image.docker_checked([
            str(runtime), "build", "--pull=false", "--no-cache", "--network=none",
            "--build-arg", f"CHECKER_BASE_IMAGE={manifest['checker_image_reference']}",
            "--iidfile", str(iid), "--tag", image_tag,
            "--file", str(context / "Containerfile"), str(context),
        ], build_log)
        require(iid.is_file(), "Docker did not publish an agent image ID")
        image_digest = iid.read_text(encoding="ascii").strip()
    require(IMAGE_DIGEST.fullmatch(image_digest) is not None,
            "Docker returned a mutable agent image identity")
    require(validate_context(context) == manifest,
            "agent-image context changed while Docker consumed it")
    inspected = json.loads(docker_output([
        str(runtime), "image", "inspect", image_digest, "--format", "{{json .}}",
    ]).decode("utf-8"))
    require(inspected.get("Id") == image_digest
            and inspected.get("Config", {}).get("Entrypoint")
            == ["python3", CONTROLLER_PATH],
            "agent image identity or PID-1 entrypoint is wrong")

    extracted = {
        "codex": extract_image(runtime, image_digest, CODEX_PATH),
        "bwrap": extract_image(
            runtime, image_digest, CODEX_INSTALL_ROOT + "/codex-resources/bwrap"
        ),
        "rg": extract_image(runtime, image_digest, CODEX_INSTALL_ROOT + "/path/rg"),
        "package_json": extract_image(
            runtime, image_digest, CODEX_INSTALL_ROOT + "/package.json"
        ),
        "controller": extract_image(runtime, image_digest, CONTROLLER_PATH),
        "adapter": extract_image(runtime, image_digest, ADAPTER_PATH),
        "excluded_adapter": extract_image(
            runtime, image_digest, EXCLUDED_ADAPTER_PATH
        ),
        "outer_controller": extract_image(
            runtime, image_digest, OUTER_CONTROLLER_PATH
        ),
        "outer_probe": extract_image(runtime, image_digest, OUTER_PROBE_PATH),
        "model_probe": extract_image(runtime, image_digest, MODEL_PROBE_PATH),
        "excluded_contract": extract_image(
            runtime, image_digest, EXCLUDED_CONTRACT_PATH
        ),
        "cache_manifest": extract_image(
            runtime, image_digest, checker_launcher.CHECKER_CACHE_MANIFEST_PATH
        ),
    }
    for name in ("codex", "bwrap", "rg", "package_json"):
        require(hashlib.sha256(extracted[name]).hexdigest()
                == manifest["codex_members"][name]["sha256"],
                f"in-image Codex {name} differs from the prepared context")
    require(hashlib.sha256(extracted["controller"]).hexdigest()
            == sha256_file(context / "target_drift_agent_pid1.py")
            and hashlib.sha256(extracted["adapter"]).hexdigest()
            == sha256_file(context / "codex_target_drift_adapter.py"),
            "in-image controller or adapter differs from the context")
    excluded_contract = json.loads(extracted["excluded_contract"].decode("utf-8"))
    require(
        hashlib.sha256(extracted["excluded_adapter"]).hexdigest()
        == sha256_file(context / "target_drift_agent_excluded_adapter.py")
        == excluded_contract.get("adapter", {}).get("sha256")
        and hashlib.sha256(extracted["excluded_contract"]).hexdigest()
        == sha256_file(context / "agent-excluded-execution-contract.json")
        and excluded_contract.get("request", {}).get("sha256")
        == sha256_file(context / "agent-excluded-execution-request.json"),
        "in-image excluded-execution contract, adapter, or request binding differs",
    )
    require(
        hashlib.sha256(extracted["outer_controller"]).hexdigest()
        == sha256_file(context / "target_drift_agent_outer_controller.py")
        and hashlib.sha256(extracted["outer_probe"]).hexdigest()
        == sha256_file(context / "target_drift_agent_outer_probe.py")
        and hashlib.sha256(extracted["model_probe"]).hexdigest()
        == sha256_file(context / "target_drift_agent_model_probe.py"),
        "in-image outer-boundary components differ from the context",
    )
    require(hashlib.sha256(extracted["cache_manifest"]).hexdigest()
            == manifest["checker_cache_manifest_sha256"],
            "agent image inherited a different Lean cache manifest")

    codex_version_output = docker_output([
        str(runtime), "run", "--rm", "--pull", "never", "--network", "none",
        "--read-only", "--cap-drop", "ALL", "--security-opt",
        "no-new-privileges=true", "--entrypoint", "/usr/local/bin/codex",
        image_digest, "--version",
    ])
    codex_version = validate_codex_version_output(
        codex_version_output, manifest["codex_version"]
    )
    write_new_bytes(codex_version_output_path, codex_version_output)
    toolchain_probe = checker_image.offline_toolchain_probe(
        runtime, image_digest,
        regular_file(
            context / "checker-evidence" / "lean-toolchain",
            "private checker lean-toolchain",
        ).read_bytes(),
    )
    require(
        toolchain_probe["toolchain_release"]
        == manifest["checker_toolchain_release"]
        and toolchain_probe["lean_version"] == manifest["checker_lean_version"]
        and toolchain_probe["lake_version"] == manifest["checker_lake_version"]
        and toolchain_probe["python_version"] == manifest["checker_python_version"],
        "agent image changed the inherited offline toolchain",
    )
    lean_version = toolchain_probe["lean_version"]
    lake_version = toolchain_probe["lake_version"]

    sbom = {
        "schema_version": 1,
        "suite_id": SUITE_ID,
        "status": "provider_client_image_built_probe_pending_results_absent",
        "container_image_digest": image_digest,
        "checker_base_image_digest": manifest["checker_image_digest"],
        "checker_image_sbom_sha256": manifest["checker_image_sbom_sha256"],
        "checker_cache_manifest_sha256": manifest["checker_cache_manifest_sha256"],
        "checker_build_input_sha256": manifest["checker_build_input_sha256"],
        "workspace_base_commit": manifest["checker_workspace_base_commit"],
        "source_snapshot_manifest_sha256": manifest[
            "checker_source_snapshot_manifest_sha256"
        ],
        "agent_image_recipe_sha256": sha256_file(context / "Containerfile"),
        "agent_image_build_input_sha256": sha256_file(
            context / "agent-image-build-input.json"
        ),
        "agent_image_builder_sha256": sha256_file(Path(__file__).resolve()),
        "source_lock_sha256": manifest["source_lock_sha256"],
        "codex_package": manifest["codex_package"],
        "codex_package_sha512": manifest["codex_package_sha512"],
        "codex_executable_sha256": hashlib.sha256(extracted["codex"]).hexdigest(),
        "codex_version": codex_version,
        "codex_version_output_artifact": codex_version_output_path.name,
        "codex_version_output_sha256": hashlib.sha256(
            codex_version_output
        ).hexdigest(),
        "bundled_bwrap_sha256": hashlib.sha256(extracted["bwrap"]).hexdigest(),
        "bundled_rg_sha256": hashlib.sha256(extracted["rg"]).hexdigest(),
        "controller_sha256": hashlib.sha256(extracted["controller"]).hexdigest(),
        "adapter_sha256": hashlib.sha256(extracted["adapter"]).hexdigest(),
        "excluded_adapter_sha256": hashlib.sha256(
            extracted["excluded_adapter"]
        ).hexdigest(),
        "excluded_execution_contract_sha256": hashlib.sha256(
            extracted["excluded_contract"]
        ).hexdigest(),
        "excluded_execution_request_sha256": excluded_contract["request"]["sha256"],
        "outer_controller_sha256": hashlib.sha256(
            extracted["outer_controller"]
        ).hexdigest(),
        "outer_probe_sha256": hashlib.sha256(extracted["outer_probe"]).hexdigest(),
        "model_probe_sha256": hashlib.sha256(extracted["model_probe"]).hexdigest(),
        "lean_version": lean_version,
        "lake_version": lake_version,
        "python_version": toolchain_probe["python_version"],
        "toolchain_release": toolchain_probe["toolchain_release"],
        "offline_toolchain_probe": toolchain_probe["offline_toolchain_probe"],
        "toolchain_probe_source_sha256": toolchain_probe[
            "toolchain_probe_source_sha256"
        ],
        "docker_executable_sha256": sha256_file(runtime),
        "docker_runtime_identity": identity,
        "image_build_log_sha256": sha256_file(build_log),
        "nonclaims": [
            "No provider credential was supplied and no model invocation occurred.",
            "The image is an unpublished result-free candidate until its inner sandbox and PID-1 lifecycle probes pass on this exact digest.",
            "A passing candidate is not the real one-case-by-three-condition smoke or any primary evaluation result."
        ]
    }
    write_new_json(sbom_output, sbom)
    print(json.dumps({
        "status": sbom["status"], "container_image_digest": image_digest,
        "sbom": str(sbom_output), "sbom_sha256": sha256_file(sbom_output),
        "build_log_sha256": sha256_file(build_log),
    }, sort_keys=True))


def main() -> None:
    parser = argparse.ArgumentParser()
    commands = parser.add_subparsers(dest="command", required=True)
    prepare = commands.add_parser("prepare-context")
    prepare.add_argument("--checker-image-reference", required=True)
    prepare.add_argument("--checker-image-digest", required=True)
    prepare.add_argument("--checker-sbom", type=Path, required=True)
    prepare.add_argument("--checker-cache-manifest", type=Path, required=True)
    prepare.add_argument("--checker-build-input", type=Path, required=True)
    prepare.add_argument("--codex-package", type=Path, required=True)
    prepare.add_argument("--output", type=Path, required=True)
    verify = commands.add_parser("verify-context")
    verify.add_argument("--context", type=Path, required=True)
    build = commands.add_parser("build-image")
    build.add_argument("--context", type=Path, required=True)
    build.add_argument("--image-tag", required=True)
    build.add_argument("--sbom-output", type=Path, required=True)
    build.add_argument("--build-log", type=Path, required=True)
    args = parser.parse_args()
    if args.command == "prepare-context":
        prepare_context(
            args.checker_image_reference, args.checker_image_digest,
            args.checker_sbom, args.checker_cache_manifest,
            args.checker_build_input, args.codex_package, args.output,
        )
    elif args.command == "verify-context":
        payload = validate_context(args.context)
        print(json.dumps({
            "status": "verified", "context": str(args.context.resolve()),
            "manifest_sha256": sha256_file(
                args.context.resolve() / "agent-image-build-input.json"
            ),
            "codex_version": payload["codex_version"],
        }, sort_keys=True))
    else:
        build_image(args.context, args.image_tag, args.sbom_output, args.build_log)


if __name__ == "__main__":
    main()
