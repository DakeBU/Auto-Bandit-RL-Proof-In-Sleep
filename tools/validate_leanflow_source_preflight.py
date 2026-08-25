#!/usr/bin/env python3
"""Validate LeanFlow pinned-source preflight artifacts as non-results.

This validator is intentionally independent of ``leanflow_target_drift_adapter``.
It checks the tracked workflow boundary plus the emitted response and trace.  It
does not import or execute LeanFlow, Git, a model/provider client, or a network
client.  A successful validation only attests that the pinned public source was
audited by the result-free adapter; it is not an evaluation outcome.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import os
import re
import stat
import sys
from pathlib import Path
from typing import Any, Sequence, cast


ROOT = Path(__file__).resolve().parents[1]
DEFAULT_CONTRACT = (
    ROOT / "evaluation" / "target-drift-v2" / "leanflow-real-adapter-contract.json"
)
DEFAULT_WORKFLOW = ROOT / ".github" / "workflows" / "leanflow-source-preflight.yml"
ADAPTER_PATH = ROOT / "tools" / "leanflow_target_drift_adapter.py"
VALIDATOR_PATH = Path(__file__).resolve()

EXPECTED_REPOSITORY = "https://github.com/epfl-lara/LeanFlow"
EXPECTED_COMMIT = "72a58a5ffe3d26710e8e0a5d0f4e9bcaab3fed4d"
EXPECTED_TREE = "5db00ff277884f8df1f0379b4f1418abcd32f31c"
EXPECTED_LOCK_SHA256 = "24528271319eb9778b260d4e5a39577b387bb41cc1f4d0ffc94139dae890d580"
EXPECTED_ABRL_GITHUB_REPOSITORY = "DakeBU/Auto-Bandit-RL-Proof-In-Sleep"
CHECKOUT_ACTION_SHA = "d23441a48e516b6c34aea4fa41551a30e30af803"
UPLOAD_ACTION_SHA = "ea165f8d65b6e75b540449e92b4886f43607fa02"
EXPECTED_WORKFLOW_SHA256 = "69cb85f9cb19135890f50bdf5e82fbc80740b0b779162f9abf178824c0961323"
EXPECTED_WORKFLOW_NAME = "LeanFlow pinned-source preflight (result-free, not results)"
EXPECTED_ADAPTER_ID = "leanflow-real-preflight"
EXPECTED_ADAPTER_VERSION = "1"
EXPECTED_STATUS = "result_free_preflight_completed"
EXPECTED_PINNED_FILES = [
    {
        "path": "pyproject.toml",
        "bytes": 14607,
        "sha256": "dc252ca57f819b5b4d6d4e0482c2b34c76e68ae054035872f11aed13bf462ed2",
    },
    {
        "path": "uv.lock",
        "bytes": 1187018,
        "sha256": EXPECTED_LOCK_SHA256,
    },
    {
        "path": "README.md",
        "bytes": 12404,
        "sha256": "84103f2972142b7db0119d9cf07f1d109ad3fe7aa3dd10fd0949133145ad30f9",
    },
    {
        "path": "core/toolsets.py",
        "bytes": 7060,
        "sha256": "8d38f4c91c6a95ad39353ad6886fa62bc68e6d3537a5b8324a52163d5064a81e",
    },
    {
        "path": "leanflow_cli/workflow.py",
        "bytes": 33961,
        "sha256": "59832123ff5c6f2f4709a5767efee250aa631d57792c97819e19e8aa79c82f6f",
    },
    {
        "path": "tests/leanflow/test_workflow_swarm.py",
        "bytes": 39685,
        "sha256": "2793df187873b071ed26682cf2f8e3a646ac85afef52f2899e508ef3bd0e644a",
    },
    {
        "path": "LICENSE",
        "bytes": 11350,
        "sha256": "5bd32a575cd52db63e009f10f036d3d3d0dad3985c07913491150cf0dfa01753",
    },
]
EXPECTED_TRACE_KINDS = [
    "preflight_started",
    "contract_validated",
    "local_git_identity_validated",
    "pinned_source_files_validated",
    "pinned_cli_policy_audited",
    "preflight_summary",
]

RESPONSE_FIELDS = {
    "schema_version",
    "suite_id",
    "comparator_id",
    "adapter_id",
    "adapter_version",
    "status",
    "result_eligible",
    "production_eligible",
    "adapter_provider_client_called",
    "adapter_started_leanflow",
    "adapter_credential_read_path_present",
    "adapter_network_client_path_present",
    "local_git_executable_pre_frozen",
    "os_network_isolation_attested",
    "formalization_outcome_reported",
    "production_gate_passed",
    "contract_sha256",
    "source_identity",
    "local_preflight",
    "gates",
    "unmet_production_gates",
}

FALSE_RESPONSE_FIELDS = (
    "result_eligible",
    "production_eligible",
    "adapter_provider_client_called",
    "adapter_started_leanflow",
    "adapter_credential_read_path_present",
    "adapter_network_client_path_present",
    "local_git_executable_pre_frozen",
    "os_network_isolation_attested",
    "formalization_outcome_reported",
    "production_gate_passed",
)

SUMMARY_FALSE_FIELDS = (
    "result_eligible",
    "adapter_provider_client_called",
    "adapter_started_leanflow",
    "adapter_credential_read_path_present",
    "adapter_network_client_path_present",
    "local_git_executable_pre_frozen",
    "os_network_isolation_attested",
    "formalization_outcome_reported",
    "production_gate_passed",
)

EXPECTED_GATE_VALUES = {
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
}

PROVENANCE_FIELDS = {
    "mode",
    "status",
    "abrl_github_sha",
    "github_run_id",
    "github_run_attempt",
    "github_event_name",
    "github_ref",
    "github_workflow",
    "github_workflow_ref",
    "github_repository",
    "github_server_url",
    "github_run_url",
    "main_push_artifact_upload_permitted",
    "artifact_digest",
    "ci_evidence_eligible",
    "required_external_verification",
    "nonclaim",
}

WORKFLOW_REQUIRED_LITERALS = (
    f"name: {EXPECTED_WORKFLOW_NAME}",
    "permissions:\n  contents: read",
    "persist-credentials: false",
    f"uses: actions/checkout@{CHECKOUT_ACTION_SHA} # v6",
    f"LEANFLOW_REPOSITORY: {EXPECTED_REPOSITORY}",
    f"LEANFLOW_COMMIT: {EXPECTED_COMMIT}",
    "fetch --no-tags --depth=1 origin \"${LEANFLOW_COMMIT}\"",
    "-c core.autocrlf=false",
    "remote remove origin",
    "python3 tools/leanflow_target_drift_adapter.py",
    "--mode result-free-preflight",
    "python3 tools/validate_leanflow_source_preflight.py",
    "--provenance-mode github-actions",
    "--github-sha \"${GITHUB_SHA}\"",
    (
        "if: github.repository == 'DakeBU/Auto-Bandit-RL-Proof-In-Sleep' && "
        "github.event_name == 'push' && github.ref == 'refs/heads/main'"
    ),
    f"uses: actions/upload-artifact@{UPLOAD_ACTION_SHA} # v4",
    "name: leanflow-source-preflight-not-results-${{ github.run_id }}-${{ github.run_attempt }}",
    "if-no-files-found: error",
    "SOURCE_PREFLIGHT_ARTIFACT_DIGEST: ${{ steps.source-preflight-upload.outputs.artifact-digest }}",
)

WORKFLOW_FORBIDDEN_PATTERNS = (
    (r"\b(?:curl|wget)\b", "a general network client"),
    (r"\b(?:pip|pip3)\s+install\b", "a dependency installer"),
    (r"\buv\s+(?:run|sync|pip)\b", "a LeanFlow-capable dependency runner"),
    (r"\bleanflow(?:-agent)?\s+(?:doctor|workflow|project|run|prove)\b", "LeanFlow execution"),
    (r"\b(?:openai|anthropic|litellm)\b", "a provider client"),
    (r"\b(?:Invoke-WebRequest|Invoke-RestMethod)\b", "a PowerShell network client"),
    (r"\$\{\{\s*secrets\.", "a GitHub secret reference"),
    (r"\$\{\{\s*secrets\s*\[", "a bracket-form GitHub secret reference"),
    (r"\$\{\{\s*github\.token\b", "the implicit GitHub token"),
    (r"\bpython3?\s+-c\b", "an inline Python escape surface"),
    (r"\burllib\b", "a Python network-client escape surface"),
    (r"\bpull_request_target\s*:", "a privileged pull-request trigger"),
    (r"(?mi)^\s*(?:api[_-]?key|token|password|credential)\s*:", "a credential environment key"),
)


class ValidationError(RuntimeError):
    """One source-preflight or non-result invariant failed."""


def require(condition: bool, message: str) -> None:
    if not condition:
        raise ValidationError(message)


def sha256_bytes(value: bytes) -> str:
    return hashlib.sha256(value).hexdigest()


def sha256_file(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        while chunk := handle.read(1024 * 1024):
            digest.update(chunk)
    return digest.hexdigest()


def _plain_file(path: Path, label: str) -> Path:
    absolute = path.absolute()
    info = absolute.lstat()
    require(stat.S_ISREG(info.st_mode) and not absolute.is_symlink(),
            f"{label} is not a plain regular file")
    require(info.st_nlink == 1, f"{label} is hard-linked")
    return absolute


def load_object(path: Path, label: str) -> dict[str, Any]:
    value = json.loads(_plain_file(path, label).read_text(encoding="utf-8"))
    require(isinstance(value, dict), f"{label} must contain one JSON object")
    return value


def load_trace(path: Path) -> list[dict[str, Any]]:
    text = _plain_file(path, "trace").read_text(encoding="utf-8")
    require(text.endswith("\n"), "trace must end with one newline")
    lines = text.splitlines()
    require(len(lines) == len(EXPECTED_TRACE_KINDS),
            "trace event count differs from the frozen grammar")
    events: list[dict[str, Any]] = []
    for index, line in enumerate(lines):
        require(bool(line), f"trace line {index + 1} is empty")
        value = json.loads(line)
        require(isinstance(value, dict), f"trace line {index + 1} is not an object")
        events.append(value)
    return events


def validate_contract_boundary(contract: dict[str, Any]) -> None:
    require(contract.get("schema_version") == 1, "contract schema differs")
    require(contract.get("suite_id") == "ABRL-TARGET-DRIFT-V2",
            "contract suite differs")
    require(contract.get("comparator_id") == "leanflow_external",
            "contract comparator differs")
    require(contract.get("adapter_id") == EXPECTED_ADAPTER_ID
            and contract.get("adapter_version") == EXPECTED_ADAPTER_VERSION,
            "contract adapter identity differs")
    require(contract.get("status") == "candidate_result_free_preflight_only",
            "contract is not a result-free source preflight")
    require(contract.get("existing_external_plan_status") == "planned_unrun_result_free",
            "contract no longer records the comparator as unrun")
    require(contract.get("sealed_by_existing_external_plumbing") is False,
            "source preflight must not claim production sealing")

    source = contract.get("source_identity")
    require(isinstance(source, dict), "contract source identity is absent")
    require(source.get("repository_url") == EXPECTED_REPOSITORY,
            "contract repository differs")
    require(source.get("repository_commit") == EXPECTED_COMMIT,
            "contract commit differs")
    require(source.get("repository_tree_sha1") == EXPECTED_TREE,
            "contract tree differs")
    require(source.get("repository_commit_time_utc") == "2026-08-11T02:39:36Z"
            and source.get("license") == "Apache-2.0"
            and source.get("project_name") == "leanflow-agent"
            and source.get("project_version") == "0.3.0"
            and source.get("python_requires") == ">=3.11"
            and source.get("cli_entrypoint") == "leanflow_cli.main:main"
            and source.get("agent_entrypoint") == "leanflow_agent:main",
            "contract pinned source metadata differs")
    require(source.get("lock_path") == "uv.lock"
            and source.get("lock_sha256") == EXPECTED_LOCK_SHA256,
            "contract pinned lock identity differs")
    pinned = source.get("pinned_files")
    require(pinned == EXPECTED_PINNED_FILES,
            "contract pinned-file inventory differs")

    capability = contract.get("preflight_capability")
    require(isinstance(capability, dict), "contract capability is absent")
    for key in (
        "adapter_credential_read_path_present",
        "adapter_network_client_path_present",
        "adapter_provider_client_path_present",
        "leanflow_process_allowed",
        "provider_process_allowed",
        "formalization_execution_allowed",
        "execution_enabled",
        "production_eligible",
        "result_eligible",
    ):
        require(capability.get(key) is False, f"contract capability {key} is not false")
    clean_room = contract.get("clean_room_audit")
    require(isinstance(clean_room, dict)
            and clean_room.get("no_web_overlay_frozen") is False
            and clean_room.get("production_requirement_satisfied") is False,
            "contract improperly claims a no-web overlay or production readiness")


def validate_workflow(path: Path) -> dict[str, Any]:
    workflow_path = _plain_file(path, "source-preflight workflow")
    workflow_sha256 = sha256_file(workflow_path)
    require(workflow_sha256 == EXPECTED_WORKFLOW_SHA256,
            "workflow bytes differ from the exact trusted-main snapshot")
    text = workflow_path.read_text(encoding="utf-8").replace("\r\n", "\n")
    for literal in WORKFLOW_REQUIRED_LITERALS:
        require(literal in text, f"workflow is missing required boundary: {literal}")
    for pattern, label in WORKFLOW_FORBIDDEN_PATTERNS:
        require(re.search(pattern, text) is None, f"workflow contains {label}")

    action_refs = re.findall(r"(?m)^\s*uses:\s*([^\s#]+)", text)
    require(action_refs == [
        f"actions/checkout@{CHECKOUT_ACTION_SHA}",
        f"actions/upload-artifact@{UPLOAD_ACTION_SHA}",
    ], "workflow action SHAs differ from pinned checkout v6 and upload v4")
    object_ids = re.findall(r"\b[0-9a-f]{40}\b", text)
    require(object_ids == [CHECKOUT_ACTION_SHA, EXPECTED_COMMIT, UPLOAD_ACTION_SHA],
            "workflow action SHAs or LeanFlow source commit differ")
    urls = re.findall(r"https://[^\s\"']+", text)
    require(urls == [EXPECTED_REPOSITORY],
            "workflow contains an unexpected source URL")

    fetch_marker = "fetch --no-tags --depth=1 origin \"${LEANFLOW_COMMIT}\""
    remove_marker = "remote remove origin"
    adapter_marker = "python3 tools/leanflow_target_drift_adapter.py"
    validator_marker = "python3 tools/validate_leanflow_source_preflight.py"
    upload_marker = f"uses: actions/upload-artifact@{UPLOAD_ACTION_SHA}"
    positions = [text.index(marker) for marker in (
        fetch_marker, remove_marker, adapter_marker, validator_marker, upload_marker,
    )]
    require(positions == sorted(positions),
            "workflow does not remove the remote before adapter and validator execution")
    require(text.count(" fetch ") == 1 and " clone " not in text,
            "workflow contains more than one source acquisition command")
    require("--attestation \"${ARTIFACT_DIR}/source-preflight-validation.json\"" in text,
            "workflow does not emit the independent validation attestation")
    trusted_main_condition = (
        "if: github.repository == 'DakeBU/Auto-Bandit-RL-Proof-In-Sleep' && "
        "github.event_name == 'push' && github.ref == 'refs/heads/main'"
    )
    require(text.count(trusted_main_condition) == 2,
            "artifact upload and digest summary are not trusted-repository main-push-only")
    return {
        "path": workflow_path.relative_to(ROOT).as_posix(),
        "sha256": workflow_sha256,
    }


def validate_response(
    response: dict[str, Any], contract: dict[str, Any], contract_sha256: str,
) -> None:
    require(set(response) == RESPONSE_FIELDS, "response fields differ from the exact schema")
    require(response["schema_version"] == 1, "response schema differs")
    require(response["suite_id"] == contract["suite_id"]
            and response["comparator_id"] == contract["comparator_id"],
            "response study identity differs")
    require(response["adapter_id"] == EXPECTED_ADAPTER_ID
            and response["adapter_version"] == EXPECTED_ADAPTER_VERSION,
            "response adapter identity differs")
    require(response["status"] == EXPECTED_STATUS,
            "response is not a completed result-free source preflight")
    for field in FALSE_RESPONSE_FIELDS:
        require(response[field] is False, f"response {field} is not false")
    require(response["contract_sha256"] == contract_sha256,
            "response contract hash differs")

    source = contract["source_identity"]
    require(response["source_identity"] == {
        "repository_commit": EXPECTED_COMMIT,
        "repository_tree_sha1": EXPECTED_TREE,
        "project_version": source["project_version"],
        "python_requires": source["python_requires"],
        "lock_sha256": source["lock_sha256"],
        "pinned_file_count": len(source["pinned_files"]),
    }, "response source identity differs from the pinned contract")
    local = response["local_preflight"]
    require(isinstance(local, dict) and set(local) == {
        "git_executable_sha256",
        "git_identity_probe_count",
        "model_invocations",
        "git_executable_pre_frozen",
        "git_os_level_behavior_attested",
    }, "response local-preflight schema differs")
    require(re.fullmatch(r"[0-9a-f]{64}", str(local["git_executable_sha256"]))
            is not None, "response Git executable hash is malformed")
    require(local["git_identity_probe_count"] == 2
            and local["model_invocations"] == 0
            and local["git_executable_pre_frozen"] is False
            and local["git_os_level_behavior_attested"] is False,
            "response local-preflight facts differ")
    require(response["gates"] == EXPECTED_GATE_VALUES,
            "response gates cross the source-preflight boundary")
    require(response["unmet_production_gates"] == contract["unmet_production_gates"],
            "response omits or changes production blockers")


def validate_trace(
    events: list[dict[str, Any]], response: dict[str, Any],
    contract: dict[str, Any], contract_sha256: str,
) -> None:
    require([event.get("sequence") for event in events] == list(range(6)),
            "trace sequence differs")
    require([event.get("kind") for event in events] == EXPECTED_TRACE_KINDS,
            "trace event order differs")
    expected_fields = (
        {"sequence", "kind"},
        {"sequence", "kind", "contract_sha256"},
        {"sequence", "kind", "repository_commit", "repository_tree_sha1",
         "git_identity_probe_count"},
        {"sequence", "kind", "pinned_file_count", "lock_sha256"},
        {"sequence", "kind", "clean_room_status", "no_web_overlay_frozen",
         "provider_only_network_containment_frozen"},
        {"sequence", "kind", *SUMMARY_FALSE_FIELDS},
    )
    for index, (event, fields) in enumerate(zip(events, expected_fields)):
        require(set(event) == fields, f"trace event {index} fields differ")

    require(events[1]["contract_sha256"] == contract_sha256,
            "trace contract hash differs")
    require(events[2]["repository_commit"] == EXPECTED_COMMIT
            and events[2]["repository_tree_sha1"] == EXPECTED_TREE
            and events[2]["git_identity_probe_count"] == 2,
            "trace Git identity differs")
    source = contract["source_identity"]
    require(events[3]["pinned_file_count"] == len(source["pinned_files"])
            and events[3]["lock_sha256"] == source["lock_sha256"],
            "trace pinned-file identity differs")
    require(events[4] == {
        "sequence": 4,
        "kind": "pinned_cli_policy_audited",
        "clean_room_status": contract["clean_room_audit"]["status"],
        "no_web_overlay_frozen": False,
        "provider_only_network_containment_frozen": False,
    }, "trace clean-room boundary differs")
    for field in SUMMARY_FALSE_FIELDS:
        require(events[5][field] is False, f"trace summary {field} is not false")
        require(events[5][field] == response[field],
                f"trace summary {field} differs from response")


def build_provenance(
    mode: str = "local",
    *,
    github_sha: str | None = None,
    github_run_id: str | None = None,
    github_run_attempt: str | None = None,
    github_event_name: str | None = None,
    github_ref: str | None = None,
    github_workflow: str | None = None,
    github_workflow_ref: str | None = None,
    github_repository: str | None = None,
    github_server_url: str | None = None,
) -> dict[str, Any]:
    values = {
        "abrl_github_sha": github_sha,
        "github_run_id": github_run_id,
        "github_run_attempt": github_run_attempt,
        "github_event_name": github_event_name,
        "github_ref": github_ref,
        "github_workflow": github_workflow,
        "github_workflow_ref": github_workflow_ref,
        "github_repository": github_repository,
        "github_server_url": github_server_url,
    }
    require(mode in {"local", "github-actions"}, "unknown provenance mode")
    if mode == "local":
        require(all(value is None for value in values.values()),
                "local provenance must not accept GitHub context")
        return {
            "mode": "local",
            "status": "local_non_evidence",
            **values,
            "github_run_url": None,
            "main_push_artifact_upload_permitted": False,
            "artifact_digest": None,
            "ci_evidence_eligible": False,
            "required_external_verification": [],
            "nonclaim": (
                "Local validation has no GitHub-run provenance and cannot be cited as "
                "CI evidence."
            ),
        }

    require(all(isinstance(value, str) and value for value in values.values()),
            "GitHub Actions provenance requires every context field")
    github_sha = cast(str, github_sha)
    github_run_id = cast(str, github_run_id)
    github_run_attempt = cast(str, github_run_attempt)
    github_event_name = cast(str, github_event_name)
    github_ref = cast(str, github_ref)
    github_workflow = cast(str, github_workflow)
    github_workflow_ref = cast(str, github_workflow_ref)
    github_repository = cast(str, github_repository)
    github_server_url = cast(str, github_server_url)
    require(re.fullmatch(r"[0-9a-f]{40}", github_sha) is not None,
            "ABRL github.sha is malformed")
    require(github_run_id.isdecimal() and int(github_run_id) > 0,
            "GitHub run_id is malformed")
    require(github_run_attempt.isdecimal() and int(github_run_attempt) > 0,
            "GitHub run_attempt is malformed")
    require(github_event_name in {"push", "pull_request", "workflow_dispatch"},
            "GitHub event is outside the workflow trigger allowlist")
    require(github_ref.startswith("refs/"), "GitHub ref is malformed")
    require(github_workflow == EXPECTED_WORKFLOW_NAME,
            "GitHub workflow name differs")
    require(github_repository == EXPECTED_ABRL_GITHUB_REPOSITORY,
            "GitHub repository differs from the trusted ABRL repository")
    workflow_ref_prefix = (
        f"{github_repository}/.github/workflows/leanflow-source-preflight.yml@"
    )
    require(github_workflow_ref.startswith(workflow_ref_prefix)
            and len(github_workflow_ref) > len(workflow_ref_prefix),
            "GitHub workflow_ref does not bind the tracked workflow")
    require(github_server_url == "https://github.com",
            "GitHub server URL differs from the public trusted-run boundary")
    run_url = (
        f"{github_server_url}/{github_repository}/actions/runs/{github_run_id}"
    )
    main_push = github_event_name == "push" and github_ref == "refs/heads/main"
    return {
        "mode": "github-actions",
        "status": (
            "main_push_candidate_requires_trusted_run_url_and_artifact_digest"
            if main_push else "check_only_non_evidence"
        ),
        **values,
        "github_run_url": run_url,
        "main_push_artifact_upload_permitted": main_push,
        "artifact_digest": None,
        "ci_evidence_eligible": False,
        "required_external_verification": (
            [
                "Confirm github_run_url belongs to the trusted repository and protected main.",
                "Confirm the run used the trusted main commit containing the frozen workflow bytes.",
                (
                    "Record the artifact-digest emitted by the pinned "
                    "actions/upload-artifact action on that run."
                ),
            ] if main_push else []
        ),
        "nonclaim": (
            "This in-artifact context can be changed with repository code and is not "
            "self-authenticating; CI evidence additionally requires the trusted run URL "
            "and the pinned upload action's external artifact digest."
        ),
    }


def validate_provenance(provenance: Any) -> dict[str, Any]:
    require(isinstance(provenance, dict), "provenance must be one JSON object")
    require(set(provenance) == PROVENANCE_FIELDS,
            "provenance fields differ from the exact schema")
    mode = provenance["mode"]
    if mode == "local":
        expected = build_provenance()
    elif mode == "github-actions":
        expected = build_provenance(
            "github-actions",
            github_sha=provenance["abrl_github_sha"],
            github_run_id=provenance["github_run_id"],
            github_run_attempt=provenance["github_run_attempt"],
            github_event_name=provenance["github_event_name"],
            github_ref=provenance["github_ref"],
            github_workflow=provenance["github_workflow"],
            github_workflow_ref=provenance["github_workflow_ref"],
            github_repository=provenance["github_repository"],
            github_server_url=provenance["github_server_url"],
        )
    else:
        raise ValidationError("provenance mode differs from the exact schema")
    require(provenance == expected,
            "provenance semantics differ from the reconstructed canonical object")
    return expected


def build_attestation(
    contract_path: Path,
    response_path: Path,
    trace_path: Path,
    workflow: dict[str, Any],
    provenance: dict[str, Any],
) -> dict[str, Any]:
    return {
        "schema_version": 1,
        "artifact_kind": "leanflow_pinned_source_preflight_not_evaluation_results",
        "status": "result_free_source_preflight_artifacts_validated",
        "suite_id": "ABRL-TARGET-DRIFT-V2",
        "comparator_id": "leanflow_external",
        "result_eligible": False,
        "production_eligible": False,
        "leanflow_started": False,
        "model_invocations": 0,
        "provider_client_called": False,
        "formalization_outcome_reported": False,
        "source_identity": {
            "repository_url": EXPECTED_REPOSITORY,
            "repository_commit": EXPECTED_COMMIT,
            "repository_tree_sha1": EXPECTED_TREE,
        },
        "artifact_sha256": {
            "adapter": sha256_file(_plain_file(ADAPTER_PATH, "source-preflight adapter")),
            "contract": sha256_file(contract_path),
            "response": sha256_file(response_path),
            "trace": sha256_file(trace_path),
            "validator": sha256_file(_plain_file(
                VALIDATOR_PATH, "source-preflight validator",
            )),
            "workflow": workflow["sha256"],
        },
        "workflow_path": workflow["path"],
        "provenance": provenance,
        "nonclaim": (
            "This validates pinned-source preflight structure only; it is not a LeanFlow "
            "run, proof, score, comparison, or production-readiness result."
        ),
    }


def validate_artifacts(
    contract_path: Path,
    response_path: Path,
    trace_path: Path,
    workflow_path: Path = DEFAULT_WORKFLOW,
    provenance: dict[str, Any] | None = None,
) -> dict[str, Any]:
    contract_file = _plain_file(contract_path, "adapter contract")
    response_file = _plain_file(response_path, "response")
    trace_file = _plain_file(trace_path, "trace")
    contract = load_object(contract_file, "adapter contract")
    response = load_object(response_file, "response")
    events = load_trace(trace_file)
    validate_contract_boundary(contract)
    workflow = validate_workflow(workflow_path)
    contract_sha256 = sha256_file(contract_file)
    validate_response(response, contract, contract_sha256)
    validate_trace(events, response, contract, contract_sha256)
    if provenance is None:
        provenance = build_provenance()
    provenance = validate_provenance(provenance)
    return build_attestation(
        contract_file, response_file, trace_file, workflow, provenance,
    )


def write_new_object(path: Path, value: dict[str, Any]) -> None:
    target = path.absolute()
    require(not target.exists() and not target.is_symlink(),
            "refusing to overwrite attestation")
    parent = target.parent
    require(parent.exists() and parent.is_dir() and not parent.is_symlink(),
            "attestation parent must be an existing plain directory")
    payload = (json.dumps(
        value, indent=2, sort_keys=True, ensure_ascii=False,
    ) + "\n").encode("utf-8")
    fd = os.open(target, os.O_WRONLY | os.O_CREAT | os.O_EXCL, 0o600)
    try:
        with os.fdopen(fd, "wb") as handle:
            handle.write(payload)
    except Exception:
        try:
            target.unlink(missing_ok=True)
        except OSError:
            pass
        raise


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser()
    parser.add_argument("--contract", type=Path, default=DEFAULT_CONTRACT)
    parser.add_argument("--response", type=Path, required=True)
    parser.add_argument("--trace", type=Path, required=True)
    parser.add_argument("--workflow", type=Path, default=DEFAULT_WORKFLOW)
    parser.add_argument("--attestation", type=Path)
    parser.add_argument(
        "--provenance-mode", choices=["local", "github-actions"], default="local",
    )
    parser.add_argument("--github-sha")
    parser.add_argument("--github-run-id")
    parser.add_argument("--github-run-attempt")
    parser.add_argument("--github-event-name")
    parser.add_argument("--github-ref")
    parser.add_argument("--github-workflow")
    parser.add_argument("--github-workflow-ref")
    parser.add_argument("--github-repository")
    parser.add_argument("--github-server-url")
    return parser


def main(argv: Sequence[str] | None = None) -> int:
    args = build_parser().parse_args(argv)
    try:
        provenance = build_provenance(
            args.provenance_mode,
            github_sha=args.github_sha,
            github_run_id=args.github_run_id,
            github_run_attempt=args.github_run_attempt,
            github_event_name=args.github_event_name,
            github_ref=args.github_ref,
            github_workflow=args.github_workflow,
            github_workflow_ref=args.github_workflow_ref,
            github_repository=args.github_repository,
            github_server_url=args.github_server_url,
        )
        attestation = validate_artifacts(
            args.contract, args.response, args.trace, args.workflow, provenance,
        )
        if args.attestation is not None:
            write_new_object(args.attestation, attestation)
    except (OSError, ValueError, json.JSONDecodeError, ValidationError) as exc:
        print(f"LeanFlow source-preflight validation failed: {exc}", file=sys.stderr)
        return 2
    print(
        "LeanFlow pinned-source preflight artifacts valid and result-free: "
        f"commit {EXPECTED_COMMIT[:12]}, 0 model calls, no formalization outcome"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
