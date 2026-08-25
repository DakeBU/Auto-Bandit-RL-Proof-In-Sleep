#!/usr/bin/env python3
"""Result-free preflight for the pinned LeanFlow external comparator.

This module deliberately cannot execute LeanFlow.  Its only successful mode
checks local Git identity, byte-pinned source files, and the already-audited
CLI safety facts.  The Python adapter contains no credential-reading path and
imports or calls no network or provider client.  It does execute a locally
resolved Git binary for two ``rev-parse`` queries; that executable and OS-level
network isolation are not attested.  The adapter reports no proof/formalization
outcome, and ``execute`` always fails before reading the contract or touching
an output path.
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
from pathlib import Path, PurePosixPath
from typing import Any, Callable, Dict, Sequence


ADAPTER_ID = "leanflow-real-preflight"
ADAPTER_VERSION = "1"
PREFLIGHT_MODE = "result-free-preflight"
EXECUTE_MODE = "execute"
FAILURE_PREFIX = "LeanFlow result-free preflight failed"

EXPECTED_TOP_LEVEL_FIELDS = {
    "schema_version",
    "suite_id",
    "comparator_id",
    "adapter_id",
    "adapter_version",
    "status",
    "purpose",
    "existing_external_plan_status",
    "sealed_by_existing_external_plumbing",
    "source_identity",
    "observed_cli_contract",
    "clean_room_audit",
    "preflight_capability",
    "request_schema",
    "response_schema",
    "trace_schema",
    "forbidden_output_basenames",
    "unmet_production_gates",
    "nonclaims",
}

EXPECTED_TRACE_KINDS = [
    "preflight_started",
    "contract_validated",
    "local_git_identity_validated",
    "pinned_source_files_validated",
    "pinned_cli_policy_audited",
    "preflight_summary",
]

EXPECTED_GIT_PROBES = (
    ("rev-parse", "--verify", "HEAD"),
    ("rev-parse", "--verify", "HEAD^{tree}"),
)

EXPECTED_CLEAN_ROOM_AUDIT = {
    "status": "no_web_requirement_not_met_by_pinned_cli",
    "required_boundary": "research_web_and_public_repository_search_disabled",
    "facts": [
        "README.md lines 104-107 state that --clean-room retains general web and paper search.",
        "core/toolsets.py lines 151-159 include the web toolset in leanflow-prove-worker.",
        (
            "leanflow_cli/workflow.py lines 637-644 set solution-research denial but not "
            "repository-research denial."
        ),
        (
            "tests/leanflow/test_workflow_swarm.py lines 284-285 assert that "
            "repository-research denial is absent while solution-research denial is enabled."
        ),
    ],
    "no_web_overlay_frozen": False,
    "provider_only_network_containment_frozen": False,
    "public_repository_research_denial_frozen": False,
    "production_requirement_satisfied": False,
}

EXPECTED_UNMET_PRODUCTION_GATES = [
    "Freeze and disclose either an upstream no-web LeanFlow interface or a minimal audited no-web overlay.",
    "Freeze provider-only network containment and prove that all non-provider egress fails closed.",
    (
        "Freeze the exact provider, model, settings, credentials boundary, prices, budgets, "
        "runtime, image, and process-tree isolation."
    ),
    (
        "Implement and validate aggregation of every foreground and auxiliary model call "
        "without inventing missing usage."
    ),
    "Freeze the neutral checker, graders, analysis, completion ledger, and production result schema.",
    (
        "Pass one real-infrastructure smoke that is permanently result-ineligible before "
        "any 30-run calibration."
    ),
]

EXPECTED_NONCLAIMS = [
    "This contract does not execute LeanFlow or a model provider.",
    (
        "The Python adapter contains no credential-reading path and imports or calls no "
        "network or provider client."
    ),
    (
        "The preflight executes two local Git identity queries; that Git executable is "
        "observed but not pre-frozen, and its OS-level behavior is not attested."
    ),
    "OS-level network isolation is not attested by this preflight.",
    (
        "This contract does not report a Lean proof, checker result, score, cost, or "
        "comparison outcome."
    ),
    (
        "Passing this preflight does not satisfy the real-infrastructure smoke or permit a "
        "result-eligible run."
    ),
]


class PreflightError(RuntimeError):
    """One fail-closed preflight invariant was not satisfied."""


def require(condition: bool, message: str) -> None:
    if not condition:
        raise PreflightError(message)


def sha256_bytes(value: bytes) -> str:
    return hashlib.sha256(value).hexdigest()


def sha256_file(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        while chunk := handle.read(1024 * 1024):
            digest.update(chunk)
    return digest.hexdigest()


def load_regular_object(path: Path, label: str) -> dict[str, Any]:
    info = path.lstat()
    require(stat.S_ISREG(info.st_mode) and not path.is_symlink(),
            f"{label} is not a plain regular file")
    require(info.st_nlink == 1, f"{label} is hard-linked")
    value = json.loads(path.read_text(encoding="utf-8"))
    require(isinstance(value, dict), f"{label} must contain one JSON object")
    return value


def _safe_relative_path(raw: Any, label: str) -> PurePosixPath:
    require(isinstance(raw, str) and raw, f"{label} must be a nonempty string")
    value = PurePosixPath(raw)
    require(not value.is_absolute() and ".." not in value.parts and "." not in value.parts,
            f"{label} must be a normalized relative POSIX path")
    require("\\" not in raw, f"{label} must use POSIX separators")
    require(value.as_posix() == raw, f"{label} must be normalized")
    return value


def validate_contract(contract: dict[str, Any]) -> None:
    require(set(contract) == EXPECTED_TOP_LEVEL_FIELDS,
            "contract fields differ from the exact candidate schema")
    require(contract["schema_version"] == 1, "contract schema_version must be 1")
    require(contract["suite_id"] == "ABRL-TARGET-DRIFT-V2", "suite differs")
    require(contract["comparator_id"] == "leanflow_external", "comparator differs")
    require(contract["adapter_id"] == ADAPTER_ID, "adapter_id differs")
    require(contract["adapter_version"] == ADAPTER_VERSION, "adapter_version differs")
    require(contract["status"] == "candidate_result_free_preflight_only",
            "contract is not a result-free preflight candidate")
    require(
        contract["purpose"]
        == "audit_a_real_leanflow_checkout_without_leanflow_or_provider_execution_and_without_adapter_credential_or_network_client_code",
        "contract purpose differs",
    )
    require(contract["existing_external_plan_status"] == "planned_unrun_result_free",
            "external plan is not recorded as planned and unrun")
    require(contract["sealed_by_existing_external_plumbing"] is False,
            "candidate must not claim existing production sealing")

    capability = contract["preflight_capability"]
    require(capability == {
        "allowed_mode": PREFLIGHT_MODE,
        "adapter_credential_read_path_present": False,
        "adapter_network_client_path_present": False,
        "adapter_provider_client_path_present": False,
        "leanflow_process_allowed": False,
        "provider_process_allowed": False,
        "formalization_execution_allowed": False,
        "git_local_identity_probe_allowed": True,
        "allowed_git_subcommands": [
            "rev-parse --verify HEAD",
            "rev-parse --verify HEAD^{tree}",
        ],
        "local_git_executable_pre_frozen": False,
        "os_network_isolation_attested": False,
        "execution_enabled": False,
        "production_eligible": False,
        "result_eligible": False,
    }, "preflight capability does not preserve the exact result-free boundary")

    clean_room = contract["clean_room_audit"]
    require(clean_room == EXPECTED_CLEAN_ROOM_AUDIT,
            "clean-room audit differs from the exact unresolved boundary")

    response_schema = contract["response_schema"]
    require(response_schema == {
        "status": "result_free_preflight_completed",
        "result_eligible": False,
        "adapter_provider_client_called": False,
        "adapter_started_leanflow": False,
        "adapter_credential_read_path_present": False,
        "adapter_network_client_path_present": False,
        "local_git_executable_pre_frozen": False,
        "os_network_isolation_attested": False,
        "formalization_outcome_reported": False,
        "production_gate_passed": False,
    }, "response schema crosses the result-free boundary")
    trace_schema = contract["trace_schema"]
    require(trace_schema == {
        "format": "UTF-8 JSON Lines",
        "event_kinds_in_order": EXPECTED_TRACE_KINDS,
        "model_or_formalization_content": "forbidden",
    }, "trace schema differs")
    request_schema = contract["request_schema"]
    require(request_schema == {
        "mode": PREFLIGHT_MODE,
        "required_cli_arguments": [
            "--contract", "--source-root", "--response", "--trace",
        ],
        "unknown_cli_arguments": "rejected",
    }, "request schema differs")
    require(set(contract["forbidden_output_basenames"]) == {
        "external-comparator-results.json",
        "leanflow-external-completion-ledger.json",
    }, "production output basename boundary differs")
    require(contract["unmet_production_gates"] == EXPECTED_UNMET_PRODUCTION_GATES,
            "production blockers are incomplete")
    require(contract["nonclaims"] == EXPECTED_NONCLAIMS,
            "nonclaims are incomplete")

    require(contract["observed_cli_contract"] == {
        "install_command": "./scripts/install-internal.sh",
        "doctor_command": "leanflow doctor",
        "prove_command_shape": (
            "leanflow workflow prove <FILE> --provider <PROVIDER> --model <MODEL> "
            "--no-parallel --clean-room"
        ),
        "project_registration_command": "leanflow project init",
        "project_state_path": ".leanflow/workflow-state",
        "verified_exit_code": 0,
        "runtime_failure_exit_code": 1,
        "unresolved_exit_code": 2,
        "disproof_exit_code": 3,
        "interrupt_exit_code": 130,
    }, "observed CLI contract differs")

    source = contract["source_identity"]
    required_source_fields = {
        "repository_url", "repository_commit", "repository_tree_sha1",
        "repository_commit_time_utc", "license", "project_name",
        "project_version", "python_requires", "cli_entrypoint",
        "agent_entrypoint", "lock_path", "lock_sha256", "pinned_files",
    }
    require(isinstance(source, dict) and set(source) == required_source_fields,
            "source identity fields differ")
    require(source["repository_url"] == "https://github.com/epfl-lara/LeanFlow",
            "repository URL differs")
    require(re.fullmatch(r"[0-9a-f]{40}", source["repository_commit"]) is not None,
            "repository commit is malformed")
    require(re.fullmatch(r"[0-9a-f]{40}", source["repository_tree_sha1"]) is not None,
            "repository tree is malformed")
    require(source["license"] == "Apache-2.0", "license differs")
    require(source["project_name"] == "leanflow-agent", "project name differs")
    require(source["cli_entrypoint"] == "leanflow_cli.main:main"
            and source["agent_entrypoint"] == "leanflow_agent:main",
            "CLI entrypoints differ")
    require(re.fullmatch(r"[0-9a-f]{64}", source["lock_sha256"]) is not None,
            "lock SHA-256 is malformed")
    lock_path = _safe_relative_path(source["lock_path"], "lock_path")

    pinned = source["pinned_files"]
    require(isinstance(pinned, list) and len(pinned) >= 2,
            "pinned file inventory is incomplete")
    seen: set[str] = set()
    lock_record: dict[str, Any] | None = None
    for index, record in enumerate(pinned):
        require(isinstance(record, dict)
                and set(record) == {"path", "bytes", "sha256"},
                f"pinned_files[{index}] fields differ")
        relative = _safe_relative_path(record["path"], f"pinned_files[{index}].path")
        normalized = relative.as_posix()
        require(normalized not in seen, "pinned file paths are not unique")
        seen.add(normalized)
        require(isinstance(record["bytes"], int)
                and not isinstance(record["bytes"], bool)
                and record["bytes"] >= 0,
                f"pinned_files[{index}].bytes is invalid")
        require(isinstance(record["sha256"], str)
                and re.fullmatch(r"[0-9a-f]{64}", record["sha256"]) is not None,
                f"pinned_files[{index}].sha256 is malformed")
        if relative == lock_path:
            lock_record = record
    require(lock_record is not None
            and lock_record["sha256"] == source["lock_sha256"],
            "lock file is not consistently byte-pinned")
    require("pyproject.toml" in seen, "pyproject.toml is not pinned")


def _git_environment() -> dict[str, str]:
    """Return a minimal local-only Git environment without credential variables."""
    allowed_host_keys = ("PATH", "PATHEXT", "SYSTEMROOT", "WINDIR", "COMSPEC", "TMP", "TEMP")
    env = {key: os.environ[key] for key in allowed_host_keys if key in os.environ}
    env.update({
        "GIT_CONFIG_NOSYSTEM": "1",
        "GIT_CONFIG_GLOBAL": os.devnull,
        "GIT_TERMINAL_PROMPT": "0",
        "GCM_INTERACTIVE": "never",
        "GIT_OPTIONAL_LOCKS": "0",
        "GIT_NO_LAZY_FETCH": "1",
        "GIT_NO_REPLACE_OBJECTS": "1",
        "LC_ALL": "C",
        "LANG": "C",
    })
    return env


def _run_git_probe(git: Path, source_root: Path, probe: tuple[str, ...]) -> str:
    require(probe in EXPECTED_GIT_PROBES, "attempted a non-allowlisted Git probe")
    argv = [
        str(git),
        "-c", "credential.helper=",
        "-c", "core.askPass=",
        "-c", "core.fsmonitor=false",
        "-C", str(source_root),
        *probe,
    ]
    completed = subprocess.run(
        argv,
        cwd=source_root,
        env=_git_environment(),
        stdin=subprocess.DEVNULL,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        text=True,
        encoding="utf-8",
        errors="replace",
        timeout=10,
        check=False,
    )
    require(completed.returncode == 0,
            f"local Git identity probe failed with exit {completed.returncode}")
    value = completed.stdout.strip().lower()
    require(re.fullmatch(r"[0-9a-f]{40}", value) is not None,
            "local Git identity probe returned a malformed object ID")
    return value


def local_git_identity(source_root: Path) -> dict[str, Any]:
    require((source_root / ".git").exists(), "source root has no local Git metadata")
    git_name = shutil.which("git", path=os.environ.get("PATH"))
    require(git_name is not None, "git executable is unavailable for the local identity probe")
    git = Path(git_name).resolve(strict=True)
    info = git.stat()
    require(stat.S_ISREG(info.st_mode), "git executable is not a regular file")
    require(git.name.lower() in {"git", "git.exe"}, "resolved Git executable name differs")
    commit = _run_git_probe(git, source_root, EXPECTED_GIT_PROBES[0])
    tree = _run_git_probe(git, source_root, EXPECTED_GIT_PROBES[1])
    return {
        "repository_commit": commit,
        "repository_tree_sha1": tree,
        "git_executable_sha256": sha256_file(git),
        "local_git_probe_count": 2,
    }


def _plain_source_file(source_root: Path, relative: PurePosixPath) -> Path:
    candidate = source_root.joinpath(*relative.parts)
    resolved = candidate.resolve(strict=True)
    try:
        resolved.relative_to(source_root)
    except ValueError as exc:
        raise PreflightError(
            f"pinned source path escapes the source root: {relative.as_posix()}"
        ) from exc
    cursor = source_root
    for part in relative.parts:
        cursor = cursor / part
        require(not cursor.is_symlink(),
                f"pinned source path uses a symlink: {relative.as_posix()}")
    info = resolved.lstat()
    require(stat.S_ISREG(info.st_mode),
            f"pinned source path is not a regular file: {relative.as_posix()}")
    require(info.st_nlink == 1,
            f"pinned source path is hard-linked: {relative.as_posix()}")
    return resolved


def validate_pinned_source_files(
    source_root: Path, source_identity: dict[str, Any],
) -> list[dict[str, Any]]:
    observed: list[dict[str, Any]] = []
    by_path: dict[str, Path] = {}
    for record in source_identity["pinned_files"]:
        relative = _safe_relative_path(record["path"], "pinned source path")
        path = _plain_source_file(source_root, relative)
        require(path.stat().st_size == record["bytes"],
                f"pinned source byte length differs: {relative.as_posix()}")
        digest = sha256_file(path)
        require(digest == record["sha256"],
                f"pinned source SHA-256 differs: {relative.as_posix()}")
        by_path[relative.as_posix()] = path
        observed.append({
            "path": relative.as_posix(),
            "bytes": record["bytes"],
            "sha256": digest,
        })

    pyproject_text = by_path["pyproject.toml"].read_text(encoding="utf-8")
    project_match = re.search(
        r"(?ms)^\[project\]\s*$\n(.*?)(?=^\[|\Z)", pyproject_text,
    )
    scripts_match = re.search(
        r"(?ms)^\[project\.scripts\]\s*$\n(.*?)(?=^\[|\Z)", pyproject_text,
    )
    require(project_match is not None, "pyproject project table is missing")
    require(scripts_match is not None, "pyproject scripts table is missing")

    def scalar(block: str, key: str) -> str:
        match = re.search(
            rf"(?m)^{re.escape(key)}\s*=\s*\"([^\"]*)\"\s*$", block,
        )
        require(match is not None, f"pyproject field {key} is missing")
        return match.group(1)

    project_block = project_match.group(1)
    scripts_block = scripts_match.group(1)
    require(scalar(project_block, "name") == source_identity["project_name"],
            "pyproject project name differs")
    require(scalar(project_block, "version") == source_identity["project_version"],
            "pyproject project version differs")
    require(scalar(project_block, "requires-python") == source_identity["python_requires"],
            "pyproject Python requirement differs")
    require(scalar(scripts_block, "leanflow") == source_identity["cli_entrypoint"]
            and scalar(scripts_block, "leanflow-agent")
            == source_identity["agent_entrypoint"],
            "pyproject CLI entrypoints differ")
    return observed


def _safe_output_path(path: Path, forbidden_names: set[str], label: str) -> Path:
    absolute = path.absolute()
    require(absolute.name not in forbidden_names,
            f"{label} uses a production output basename")
    require(not absolute.exists() and not absolute.is_symlink(),
            f"refusing to overwrite {label}")
    parent = absolute.parent
    require(parent.exists() and parent.is_dir() and not parent.is_symlink(),
            f"{label} parent must be an existing plain directory")
    require(parent.resolve(strict=True) == parent,
            f"{label} parent resolves through a link or junction")
    return absolute


def write_new_outputs(
    response_path: Path,
    trace_path: Path,
    response: dict[str, Any],
    trace: list[dict[str, Any]],
    forbidden_names: set[str],
) -> None:
    response_target = _safe_output_path(response_path, forbidden_names, "response path")
    trace_target = _safe_output_path(trace_path, forbidden_names, "trace path")
    require(response_target != trace_target, "response and trace paths must differ")
    response_bytes = (json.dumps(
        response, indent=2, sort_keys=True, ensure_ascii=False,
    ) + "\n").encode("utf-8")
    trace_bytes = b"".join(
        (json.dumps(event, sort_keys=True, ensure_ascii=False) + "\n").encode("utf-8")
        for event in trace
    )

    response_fd: int | None = None
    trace_fd: int | None = None
    response_created = False
    trace_created = False
    try:
        response_fd = os.open(response_target, os.O_WRONLY | os.O_CREAT | os.O_EXCL, 0o600)
        response_created = True
        trace_fd = os.open(trace_target, os.O_WRONLY | os.O_CREAT | os.O_EXCL, 0o600)
        trace_created = True
        with os.fdopen(response_fd, "wb") as response_handle:
            response_fd = None
            response_handle.write(response_bytes)
        with os.fdopen(trace_fd, "wb") as trace_handle:
            trace_fd = None
            trace_handle.write(trace_bytes)
    except Exception:
        if response_fd is not None:
            os.close(response_fd)
        if trace_fd is not None:
            os.close(trace_fd)
        for target, created in (
            (response_target, response_created), (trace_target, trace_created),
        ):
            if not created:
                continue
            try:
                target.unlink(missing_ok=True)
            except OSError:
                pass
        raise


GitIdentityProbe = Callable[[Path], Dict[str, Any]]


def run_preflight(
    contract_path: Path,
    source_root: Path,
    response_path: Path,
    trace_path: Path,
    *,
    git_identity_probe: GitIdentityProbe = local_git_identity,
) -> dict[str, Any]:
    contract_input = contract_path.absolute()
    contract = load_regular_object(contract_input, "adapter contract")
    validate_contract(contract)
    contract_sha256 = sha256_file(contract_input)

    root_input = source_root.absolute()
    require(root_input.exists() and root_input.is_dir() and not root_input.is_symlink(),
            "source root must be an existing plain directory")
    root = root_input.resolve(strict=True)
    forbidden_names = set(contract["forbidden_output_basenames"])
    # Validate output destinations before the local Git subprocess is allowed.
    response_target = _safe_output_path(response_path, forbidden_names, "response path")
    trace_target = _safe_output_path(trace_path, forbidden_names, "trace path")
    require(response_target != trace_target, "response and trace paths must differ")

    identity = git_identity_probe(root)
    source = contract["source_identity"]
    require(identity.get("repository_commit") == source["repository_commit"],
            "local checkout commit differs from the pinned LeanFlow commit")
    require(identity.get("repository_tree_sha1") == source["repository_tree_sha1"],
            "local checkout tree differs from the pinned LeanFlow tree")
    require(identity.get("local_git_probe_count") == 2,
            "local Git identity probe count differs")
    require(re.fullmatch(r"[0-9a-f]{64}", str(
        identity.get("git_executable_sha256", ""),
    )) is not None, "Git executable attestation is malformed")

    observed_files = validate_pinned_source_files(root, source)
    lock_record = next(
        record for record in observed_files if record["path"] == source["lock_path"]
    )
    require(lock_record["sha256"] == source["lock_sha256"],
            "observed lock hash differs from the source identity")

    blockers = list(contract["unmet_production_gates"])
    response = {
        "schema_version": 1,
        "suite_id": contract["suite_id"],
        "comparator_id": contract["comparator_id"],
        "adapter_id": ADAPTER_ID,
        "adapter_version": ADAPTER_VERSION,
        "status": "result_free_preflight_completed",
        "result_eligible": False,
        "production_eligible": False,
        "adapter_provider_client_called": False,
        "adapter_started_leanflow": False,
        "adapter_credential_read_path_present": False,
        "adapter_network_client_path_present": False,
        "local_git_executable_pre_frozen": False,
        "os_network_isolation_attested": False,
        "formalization_outcome_reported": False,
        "production_gate_passed": False,
        "contract_sha256": contract_sha256,
        "source_identity": {
            "repository_commit": identity["repository_commit"],
            "repository_tree_sha1": identity["repository_tree_sha1"],
            "project_version": source["project_version"],
            "python_requires": source["python_requires"],
            "lock_sha256": lock_record["sha256"],
            "pinned_file_count": len(observed_files),
        },
        "local_preflight": {
            "git_executable_sha256": identity["git_executable_sha256"],
            "git_identity_probe_count": identity["local_git_probe_count"],
            "model_invocations": 0,
            "git_executable_pre_frozen": False,
            "git_os_level_behavior_attested": False,
        },
        "gates": {
            "pinned_commit_validated": True,
            "pinned_tree_validated": True,
            "pinned_files_validated": True,
            "pinned_lock_validated": True,
            "pinned_project_metadata_validated": True,
            "no_web_overlay_frozen": False,
            "provider_only_network_containment_frozen": False,
            "public_repository_research_denial_frozen": False,
            "local_git_executable_pre_frozen": False,
            "os_network_isolation_attested": False,
            "production_execution_enabled": False,
        },
        "unmet_production_gates": blockers,
    }
    trace = [
        {"sequence": 0, "kind": "preflight_started"},
        {
            "sequence": 1,
            "kind": "contract_validated",
            "contract_sha256": contract_sha256,
        },
        {
            "sequence": 2,
            "kind": "local_git_identity_validated",
            "repository_commit": identity["repository_commit"],
            "repository_tree_sha1": identity["repository_tree_sha1"],
            "git_identity_probe_count": 2,
        },
        {
            "sequence": 3,
            "kind": "pinned_source_files_validated",
            "pinned_file_count": len(observed_files),
            "lock_sha256": lock_record["sha256"],
        },
        {
            "sequence": 4,
            "kind": "pinned_cli_policy_audited",
            "clean_room_status": contract["clean_room_audit"]["status"],
            "no_web_overlay_frozen": False,
            "provider_only_network_containment_frozen": False,
        },
        {
            "sequence": 5,
            "kind": "preflight_summary",
            "result_eligible": False,
            "adapter_provider_client_called": False,
            "adapter_started_leanflow": False,
            "adapter_credential_read_path_present": False,
            "adapter_network_client_path_present": False,
            "local_git_executable_pre_frozen": False,
            "os_network_isolation_attested": False,
            "formalization_outcome_reported": False,
            "production_gate_passed": False,
        },
    ]
    require([event["kind"] for event in trace] == EXPECTED_TRACE_KINDS,
            "internal trace grammar differs from the contract")
    write_new_outputs(
        response_target, trace_target, response, trace, forbidden_names,
    )
    return response


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser()
    parser.add_argument("--mode", required=True, choices=[PREFLIGHT_MODE, EXECUTE_MODE])
    parser.add_argument("--contract", type=Path)
    parser.add_argument("--source-root", type=Path)
    parser.add_argument("--response", type=Path)
    parser.add_argument("--trace", type=Path)
    return parser


def main(argv: Sequence[str] | None = None) -> int:
    args = build_parser().parse_args(argv)
    if args.mode == EXECUTE_MODE:
        print(
            f"{FAILURE_PREFIX}: execute is disabled; no-web and production isolation "
            "gates are unresolved",
            file=sys.stderr,
        )
        return 2
    try:
        require(args.contract is not None, "--contract is required for preflight")
        require(args.source_root is not None, "--source-root is required for preflight")
        require(args.response is not None, "--response is required for preflight")
        require(args.trace is not None, "--trace is required for preflight")
        run_preflight(
            args.contract, args.source_root, args.response, args.trace,
        )
    except (OSError, ValueError, json.JSONDecodeError,
            subprocess.SubprocessError, PreflightError) as exc:
        print(f"{FAILURE_PREFIX}: {exc}", file=sys.stderr)
        return 2
    print(
        "LeanFlow result-free preflight completed: pinned source checked, "
        "0 model calls; adapter has no credential/network/provider client path; "
        "local Git and OS network isolation remain unattested; production gate closed"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
