#!/usr/bin/env python3
"""Materialize condition-blind primary-grading packets for target-drift runs."""

from __future__ import annotations

import argparse
import hashlib
import json
import os
import random
import re
import shutil
import stat
import sys
import tempfile
from pathlib import Path, PurePosixPath, PureWindowsPath
from typing import Any


TOOLS = Path(__file__).resolve().parent
sys.path.insert(0, str(TOOLS))

import prepare_target_drift_execution as prepare  # noqa: E402
import run_target_drift_execution as runner  # noqa: E402
import build_target_drift_completion_ledger as completion  # noqa: E402


FORBIDDEN_PRIMARY_TEXT = prepare.PRIMARY_GRADING_PROVENANCE_MARKERS

# Resource-use metadata, semantic run identifiers, and direct condition fields
# can make a nominally blind packet condition-predictive.  Keep them in the
# operator-only mapping for later analysis, never in material sent to a primary
# grader.
FORBIDDEN_PRIMARY_METADATA_KEYS = frozenset({
    "condition",
    "condition_label",
    "execution_purpose",
    "execution_metrics",
    "execution_usage",
    "input_tokens",
    "cached_input_tokens",
    "cache_write_input_tokens",
    "output_tokens",
    "reasoning_output_tokens",
    "tool_calls",
    "recovery_tool_calls",
    "build_attempts",
    "infrastructure_retries",
    "wall_seconds",
    "orchestrator_wall_seconds",
    "adapter_process_wall_seconds",
    "model_cost_usd",
    "cost_usd",
    "duration_seconds",
    "elapsed_seconds",
    "opaque_run_id",
    "presentation_order",
    "prompt_path",
    "prompt_template_path",
    "requirement_variant",
    "run_id",
    "semantic_run_id",
    "workflow_condition",
    "workflow_compliance_pass",
})

GRADER_EXPORT_SCHEMA_VERSION = 1
GRADER_RESPONSE_SCHEMA_VERSION = 2
GRADER_EXPORT_MANIFEST = "grader-export-manifest.json"
GRADER_EXPORT_CORE_FILES = ("grader-prompt.md", "grading-rubric.json")
GRADER_EXPORT_RESPONSE_TEMPLATE = "response-template.json"
PRODUCTION_PACKET_COUNT = 450
GRADE_PACKET_NAME = re.compile(r"packets/GRADE-[0-9a-f]{20}\.json\Z")
GRADE_PACKET_FIELDS = frozenset({
    "grade_id",
    "schema_version",
    "source_locator",
    "frozen_contract",
    "proposed_requirement",
    "expected_affected_fields",
    "agent_final_status",
    "public_declarations",
    "primary_grader_rationale",
    "source_amendment",
    "lean_artifacts",
    "neutral_checker",
    "grader_response_schema",
})
OPERATOR_MAPPING_FIELDS = frozenset({
    "grade_id",
    "semantic_run_id",
    "condition",
    "requirement_variant",
    "execution_metrics",
    "workflow_compliance_pass",
})


def load(path: Path) -> dict[str, Any]:
    return json.loads(path.read_text(encoding="utf-8"))


def dump(path: Path, value: Any) -> None:
    path.write_text(
        json.dumps(value, indent=2, sort_keys=True, ensure_ascii=False) + "\n",
        encoding="utf-8",
    )


def canonical_json_bytes(value: Any) -> bytes:
    return (
        json.dumps(value, indent=2, sort_keys=True, ensure_ascii=False) + "\n"
    ).encode("utf-8")


def require(condition: bool, message: str) -> None:
    if not condition:
        raise SystemExit(f"target-drift grading preparation failed: {message}")


def digest_payloads(payloads: dict[str, bytes]) -> str:
    digest = hashlib.sha256()
    for name in sorted(payloads):
        encoded = name.encode("utf-8")
        payload = payloads[name]
        digest.update(len(encoded).to_bytes(8, "big"))
        digest.update(encoded)
        digest.update(len(payload).to_bytes(8, "big"))
        digest.update(payload)
    return digest.hexdigest()


def sha256_bytes(payload: bytes) -> str:
    return hashlib.sha256(payload).hexdigest()


def is_reparse_point(metadata: os.stat_result) -> bool:
    flag = getattr(stat, "FILE_ATTRIBUTE_REPARSE_POINT", 0x400)
    return bool(getattr(metadata, "st_file_attributes", 0) & flag)


def require_plain_path(path: Path, *, directory: bool, label: str) -> os.stat_result:
    """Reject links, reparse points, special files, and multiply linked files."""
    try:
        metadata = os.lstat(path)
    except OSError as error:
        raise SystemExit(
            f"target-drift grading preparation failed: missing {label}: {error}"
        ) from error
    require(not stat.S_ISLNK(metadata.st_mode) and not is_reparse_point(metadata),
            f"{label} must not be a link or reparse point")
    if directory:
        require(stat.S_ISDIR(metadata.st_mode), f"{label} must be a directory")
    else:
        require(stat.S_ISREG(metadata.st_mode), f"{label} must be a regular file")
        require(getattr(metadata, "st_nlink", 1) == 1,
                f"{label} must not be multiply linked")
    return metadata


def read_plain_file(path: Path, label: str) -> bytes:
    before = require_plain_path(path, directory=False, label=label)
    try:
        with path.open("rb") as stream:
            opened = os.fstat(stream.fileno())
            require(stat.S_ISREG(opened.st_mode)
                    and not is_reparse_point(opened)
                    and getattr(opened, "st_nlink", 1) == 1,
                    f"{label} changed type while opening")
            require((before.st_dev, before.st_ino) == (opened.st_dev, opened.st_ino),
                    f"{label} changed while opening")
            payload = stream.read()
            after = os.fstat(stream.fileno())
    except OSError as error:
        raise SystemExit(
            f"target-drift grading preparation failed: cannot read {label}: {error}"
        ) from error
    require((opened.st_dev, opened.st_ino, opened.st_size)
            == (after.st_dev, after.st_ino, after.st_size),
            f"{label} changed while reading")
    return payload


def read_plain_tree(root: Path, expected_files: set[str], label: str) -> dict[str, bytes]:
    """Read an exact allowlisted tree without following filesystem aliases."""
    root = Path(os.path.abspath(root))
    require_plain_path(root, directory=True, label=f"{label} root")
    observed: set[str] = set()
    observed_directories: set[str] = set()
    for current, directory_names, file_names in os.walk(root, followlinks=False):
        current_path = Path(current)
        for name in directory_names:
            child = current_path / name
            require_plain_path(child, directory=True, label=f"{label} directory {name}")
            observed_directories.add(child.relative_to(root).as_posix())
        for name in file_names:
            child = current_path / name
            require_plain_path(child, directory=False, label=f"{label} file {name}")
            relative = child.relative_to(root).as_posix()
            observed.add(relative)
    require(observed == expected_files,
            f"{label} file set differs from the positive allowlist: "
            f"missing={sorted(expected_files - observed)}, extra={sorted(observed - expected_files)}")
    expected_directories = {
        Path(relative).parent.as_posix()
        for relative in expected_files
        if Path(relative).parent.as_posix() != "."
    }
    require(observed_directories == expected_directories,
            f"{label} directory set differs from the positive allowlist: "
            f"missing={sorted(expected_directories - observed_directories)}, "
            f"extra={sorted(observed_directories - expected_directories)}")
    payloads: dict[str, bytes] = {}
    for relative in sorted(expected_files):
        parent = Path(relative).parent
        if parent.as_posix() != ".":
            require_plain_path(
                root / parent, directory=True,
                label=f"{label} directory {parent.as_posix()}",
            )
        payloads[relative] = read_plain_file(
            root / Path(relative), f"{label} file {relative}"
        )
    return payloads


def path_is_within(path: Path, parent: Path) -> bool:
    try:
        path.relative_to(parent)
    except ValueError:
        return False
    return True


def canonical_existing_path(path: Path, *, directory: bool, label: str) -> Path:
    """Resolve an existing path and reject roots reached through an aliasing ancestor."""
    absolute = Path(os.path.abspath(path))
    require_plain_path(absolute, directory=directory, label=label)
    try:
        resolved = absolute.resolve(strict=True)
    except OSError as error:
        raise SystemExit(
            f"target-drift grading preparation failed: cannot resolve {label}: {error}"
        ) from error
    require(os.path.normcase(str(resolved)) == os.path.normcase(str(absolute)),
            f"{label} must not be reached through a filesystem alias")
    return resolved


def canonical_new_output(path: Path, label: str) -> Path:
    """Return a canonical not-yet-created output below a plain existing parent."""
    absolute = Path(os.path.abspath(path))
    parent = canonical_existing_path(
        absolute.parent, directory=True, label=f"{label} parent directory"
    )
    output = parent / absolute.name
    require(not os.path.lexists(output), f"{label} already exists")
    return output


def require_separate_trees(
    left: Path, right: Path, *, left_label: str, right_label: str,
) -> None:
    require(not path_is_within(left, right) and not path_is_within(right, left),
            f"{left_label} and {right_label} must be separate trees")


def safe_workspace_relative(value: Any, label: str) -> PurePosixPath:
    require(isinstance(value, str) and value and "\\" not in value,
            f"invalid workspace-relative path for {label}")
    relative = PurePosixPath(value)
    windows = PureWindowsPath(value)
    require(not relative.is_absolute()
            and relative.as_posix() == value
            and all(part not in {"", ".", ".."} for part in relative.parts),
            f"invalid workspace-relative path for {label}: {value}")
    require(not windows.drive and not windows.root and ":" not in value,
            f"workspace-relative path has Windows drive or stream semantics "
            f"for {label}: {value}")
    require(all(
        not any(ord(character) < 32 or character in '<>:"|?*'
                for character in part)
        and not part.endswith((".", " "))
        and not PureWindowsPath(part).is_reserved()
        for part in relative.parts
    ), f"workspace-relative path is not portable for {label}: {value}")
    return relative


def completed_agent_manifest_index(
    evidence: dict[str, Any], label: str,
) -> dict[str, dict[str, Any]]:
    """Index the completion-validated agent manifest without weakening its binding."""
    receipt = evidence.get("execution_receipt")
    manifest = receipt.get("completed_agent_manifest") if isinstance(receipt, dict) else None
    require(isinstance(manifest, list)
            and all(isinstance(entry, dict)
                    and isinstance(entry.get("path"), str)
                    and isinstance(entry.get("sha256"), str)
                    and type(entry.get("bytes")) is int
                    for entry in manifest),
            f"completed-agent manifest is invalid for {label}")
    indexed = {entry["path"]: entry for entry in manifest}
    require(len(indexed) == len(manifest),
            f"completed-agent manifest paths are duplicated for {label}")
    return indexed


def read_manifest_bound_file(
    root: Path,
    relative: PurePosixPath,
    manifest_path: str,
    manifest: dict[str, dict[str, Any]],
    label: str,
) -> bytes:
    """Read one portable path and bind the bytes back to checked-run evidence."""
    canonical_root = canonical_existing_path(root, directory=True, label=f"{label} root")
    candidate = canonical_root.joinpath(*relative.parts)
    canonical_candidate = canonical_existing_path(
        candidate, directory=False, label=label,
    )
    require(path_is_within(canonical_candidate, canonical_root),
            f"{label} resolves outside its checked workspace")
    entry = manifest.get(manifest_path)
    require(isinstance(entry, dict),
            f"{label} is absent from the completed-agent manifest")
    payload = read_plain_file(canonical_candidate, label)
    require(entry.get("bytes") == len(payload)
            and entry.get("sha256") == sha256_bytes(payload),
            f"{label} bytes differ from the completed-agent manifest")
    return payload


def agent_manifest(root: Path) -> list[dict[str, Any]]:
    manifest = []
    for path in sorted(item for item in root.rglob("*") if item.is_file()):
        relative = path.relative_to(root)
        if ".lake" in relative.parts:
            continue
        payload = path.read_bytes()
        manifest.append({
            "path": relative.as_posix(),
            "bytes": len(payload),
            "sha256": hashlib.sha256(payload).hexdigest(),
        })
    return manifest


def manifest_sha256(manifest: list[dict[str, Any]]) -> str:
    return hashlib.sha256(prepare.canonical_json_bytes(manifest)).hexdigest()


def flattened_strings(value: Any) -> list[str]:
    if isinstance(value, str):
        return [value]
    if isinstance(value, dict):
        return [text for child in value.values() for text in flattened_strings(child)]
    if isinstance(value, list):
        return [text for child in value for text in flattened_strings(child)]
    return []


def require_blind_text(value: Any, label: str) -> None:
    text = "\n".join(flattened_strings(value)).lower()
    require(not any(token in text for token in FORBIDDEN_PRIMARY_TEXT),
            f"condition-identifying text in primary {label}")


def strip_primary_metadata(value: Any) -> Any:
    """Remove condition-predictive resource metadata from grader-visible evidence."""
    if isinstance(value, dict):
        return {
            key: strip_primary_metadata(child)
            for key, child in value.items()
            if key not in FORBIDDEN_PRIMARY_METADATA_KEYS
        }
    if isinstance(value, list):
        return [strip_primary_metadata(child) for child in value]
    return value


def require_primary_metadata_blind(value: Any, label: str) -> None:
    """Fail closed if a forbidden label, run ID, or resource key reaches a packet."""
    if isinstance(value, dict):
        leaked = sorted(set(value) & FORBIDDEN_PRIMARY_METADATA_KEYS)
        require(not leaked, f"condition-predictive metadata in {label}: {leaked}")
        for child in value.values():
            require_primary_metadata_blind(child, label)
    elif isinstance(value, list):
        for child in value:
            require_primary_metadata_blind(child, label)


def agent_generated_blind_fields(packet: dict[str, Any]) -> dict[str, Any]:
    """Return only agent-authored fields; public source locators are not provenance leaks."""
    return {
        "agent_final_status": packet["agent_final_status"],
        "public_declarations": packet["public_declarations"],
        "primary_grader_rationale": packet["primary_grader_rationale"],
        "source_amendment": packet["source_amendment"],
    }


def require_blind_lean_artifacts(artifacts: list[dict[str, str]], label: str) -> None:
    """Reject only explicit condition labels in Lean; ordinary ABRL source text is common."""
    text = "\n".join(item["content"] for item in artifacts).lower()
    require(not any(token in text for token in prepare.LEAN_PROVENANCE_MARKERS),
            f"condition-identifying text in primary {label}")


def require_production_checker(config: dict[str, Any], probe: dict[str, Any]) -> str:
    checker = config["posthoc_checker"]
    require(checker["mode"] == "production",
            "formal grading rejects excluded checker fixtures")
    runtime_sha256 = prepare.checker_runtime_config_sha256(config)
    require(checker["runtime_config_sha256"] == runtime_sha256,
            "grading checker runtime digest differs from frozen config")
    require(probe.get("status") == "passed"
            and probe.get("checker_runtime_config_sha256") == runtime_sha256
            and probe.get("probe_runner_sha256")
            == checker["isolation_probe_runner_sha256"],
            "formal grading requires the runtime-bound passed isolation probe")
    return runtime_sha256


def require_primary_job(job: dict[str, Any], label: str) -> None:
    require(job.get("execution_purpose") == runner.PRIMARY_EXECUTION_PURPOSE
            and job.get("primary_result_eligible") is True,
            f"grading rejects non-primary or smoke run: {label}")


def require_real_provider_completion(
    config: dict[str, Any], receipt: dict[str, Any],
    adapter_response: dict[str, Any], adapter_response_path: Path, label: str,
) -> None:
    """Re-derive real-provider eligibility at the final grading boundary."""
    require(config["execution_adapter"]["provider_runtime"]["kind"] == "codex_cli",
            "formal grading requires a real codex_cli provider runtime")
    require(receipt.get("termination") == adapter_response.get("termination") == "completed",
            f"grading rejects non-completed provider execution: {label}")
    require(receipt.get("adapter_artifact_sha256", {}).get("response.json")
            == prepare.sha256_file(adapter_response_path),
            f"grading adapter response is not bound by execution receipt: {label}")
    invocations = adapter_response.get("model_invocations")
    require(isinstance(invocations, list) and bool(invocations)
            and all(invocation.get("transport") == "codex_cli"
                    and invocation.get("usage_observed") is True
                    for invocation in invocations),
            f"grading lacks a real codex_cli invocation with observed usage: {label}")


def build_grading_packet(
    challenge: dict[str, Any], sealed: dict[str, Any], result: dict[str, Any],
    checker: dict[str, Any], source_amendment: str | None,
    changed_lean: list[dict[str, str]], case_ids: set[str], label: str,
) -> dict[str, Any]:
    """Build the one canonical grader-visible packet from validated run evidence."""
    rationale = result["primary_grader_rationale"].strip()
    lowered = rationale.lower()
    require(not any(case_id.lower() in lowered for case_id in case_ids),
            f"semantic case identifier in primary rationale for {label}")
    packet = {
        "schema_version": 1,
        "source_locator": challenge["source_locator"],
        "frozen_contract": challenge["faithful_contract"],
        "proposed_requirement": sealed["proposed_requirement"],
        "expected_affected_fields": challenge["expected_affected_fields"],
        "agent_final_status": result["final_status"],
        "public_declarations": result["public_declarations"],
        "primary_grader_rationale": rationale,
        "source_amendment": source_amendment,
        "lean_artifacts": changed_lean,
        "neutral_checker": {
            "checker_pass": checker["checker_pass"],
            "forbidden_lean_hits": checker["forbidden_lean_hits"],
            "unexpected_axioms": checker["unexpected_axioms"],
            "artifact_replay_success": checker["artifact_replay_success"],
            "neutral_build": strip_primary_metadata(checker["neutral_build"]),
            "neutral_canary": strip_primary_metadata(checker["neutral_canary"]),
            "claim_consistent_with_checker": checker["claim_consistent_with_checker"],
        },
        "grader_response_schema": {
            "primary_pass": "boolean",
            "faithful_formal_completion": "boolean",
            "drift_detected": "boolean",
            "false_rejection": "boolean",
            "unsupported_evidence_claim": "boolean",
            "source_amendment_required": "boolean",
            "source_critical_fields": "sorted list of affected source-field names",
            "rationale": "source-field and artifact-line grounded string",
            "condition_guess": ["compile_only", "source_aware_blueprint", "abrl"],
            "condition_guess_confidence": "number in [0,1]",
        },
    }
    require_blind_text(
        agent_generated_blind_fields(packet), f"agent-generated packet fields for {label}"
    )
    require_blind_lean_artifacts(packet["lean_artifacts"], f"Lean artifacts for {label}")
    require_primary_metadata_blind(packet, f"primary packet for {label}")
    return packet


def json_from_bytes(payload: bytes, label: str) -> dict[str, Any]:
    def unique_object(pairs: list[tuple[str, Any]]) -> dict[str, Any]:
        result: dict[str, Any] = {}
        for key, value in pairs:
            if key in result:
                raise ValueError(f"duplicate object key: {key}")
            result[key] = value
        return result

    def reject_constant(value: str) -> Any:
        raise ValueError(f"non-finite JSON constant: {value}")

    try:
        value = json.loads(
            payload.decode("utf-8"),
            object_pairs_hook=unique_object,
            parse_constant=reject_constant,
        )
    except (UnicodeDecodeError, json.JSONDecodeError, ValueError) as error:
        raise SystemExit(
            f"target-drift grading preparation failed: invalid {label}: {error}"
        ) from error
    require(isinstance(value, dict), f"{label} must be a JSON object")
    return value


def validate_packet_payloads(
    packet_payloads: dict[str, bytes], expected_count: int,
) -> tuple[set[str], dict[str, dict[str, Any]]]:
    require(len(packet_payloads) == expected_count,
            f"grading packet count must be {expected_count}")
    packets: dict[str, dict[str, Any]] = {}
    for name, payload in sorted(packet_payloads.items()):
        require(bool(GRADE_PACKET_NAME.fullmatch(name)),
                f"invalid grading packet path: {name}")
        packet = json_from_bytes(payload, f"grading packet {name}")
        grade_id = packet.get("grade_id")
        require(isinstance(grade_id, str) and name == f"packets/{grade_id}.json",
                f"packet filename and embedded grade ID differ: {name}")
        require(grade_id not in packets, f"duplicate grading packet ID: {grade_id}")
        require(set(packet) == GRADE_PACKET_FIELDS,
                f"grading packet schema differs from the allowlist: {name}")
        require(packet.get("schema_version") == 1,
                f"grading packet schema_version must be 1: {name}")
        require_primary_metadata_blind(packet, f"primary packet {grade_id}")
        require_blind_text(
            agent_generated_blind_fields(packet),
            f"agent-generated packet fields for {grade_id}",
        )
        lean_artifacts = packet["lean_artifacts"]
        require(isinstance(lean_artifacts, list)
                and all(isinstance(item, dict)
                        and isinstance(item.get("artifact_name"), str)
                        and isinstance(item.get("content"), str)
                        for item in lean_artifacts),
                f"invalid Lean artifact list in packet {grade_id}")
        require_blind_lean_artifacts(lean_artifacts, f"Lean artifacts for {grade_id}")
        packets[grade_id] = packet
    return set(packets), packets


def validate_internal_grading_pack(
    pack: Path, grading_pack: Path, config: dict[str, Any],
    expected_count: int = 450,
) -> dict[str, Any]:
    """Validate the operator-facing grading pack before any safe export."""
    grading_pack = Path(os.path.abspath(grading_pack))
    require_plain_path(grading_pack, directory=True, label="internal grading-pack")
    manifest_path = grading_pack / "packet-manifest.json"
    require_plain_path(manifest_path, directory=False,
                       label="internal grading-pack manifest")
    initial_manifest = json_from_bytes(
        read_plain_file(manifest_path, "internal grading-pack manifest"),
        "internal grading-pack manifest",
    )
    packet_hashes = initial_manifest.get("packet_sha256")
    require(isinstance(packet_hashes, dict)
            and all(isinstance(name, str) and isinstance(value, str)
                    for name, value in packet_hashes.items()),
            "internal grading-pack packet hash map is invalid")
    packet_names = set(packet_hashes)
    require(len(packet_names) == expected_count
            and all(GRADE_PACKET_NAME.fullmatch(name) for name in packet_names),
            "internal grading-pack packet names/count are invalid")
    expected_files = packet_names | {
        "packet-manifest.json", "operator-mapping.json", "completion-ledger.json",
    }
    payloads = read_plain_tree(grading_pack, expected_files, "internal grading-pack")
    packet_manifest = json_from_bytes(
        payloads["packet-manifest.json"], "internal grading-pack manifest"
    )
    require(packet_manifest == initial_manifest,
            "internal grading-pack manifest changed while reading")
    require(packet_manifest.get("schema_version") == 1,
            "internal grading-pack schema_version must be 1")
    require(packet_manifest.get("suite_id") == config["suite_id"],
            "internal grading-pack suite differs from sealed execution pack")
    require(packet_manifest.get("packet_count") == expected_count,
            "internal grading-pack packet_count differs from the required count")
    sealed_pack_sha256 = (pack / "aggregate.sha256").read_text(
        encoding="ascii"
    ).strip()
    require(packet_manifest.get("sealed_pack_sha256") == sealed_pack_sha256,
            "internal grading-pack names a different sealed execution pack")
    require(packet_manifest.get("grader_prompt_sha256")
            == config["grading"]["grader_prompt_sha256"],
            "internal grading-pack names a different frozen grader prompt")
    runtime_sha256 = prepare.checker_runtime_config_sha256(config)
    require(config["posthoc_checker"]["mode"] == "production"
            and packet_manifest.get("result_eligible") is True
            and packet_manifest.get("checker_mode") == "production",
            "internal grading-pack is not production-result-eligible")
    require(packet_manifest.get("checker_runtime_config_sha256") == runtime_sha256
            == config["posthoc_checker"]["runtime_config_sha256"]
            and packet_manifest.get("isolation_probe_report_sha256")
            == config["posthoc_checker"]["isolation_probe_report_sha256"],
            "internal grading-pack checker runtime/probe binding differs from frozen config")
    require(packet_manifest.get("grading_seed")
            == config["grading"]["packet_order_seed"],
            "internal grading-pack seed differs from frozen config")
    for key in (
        "primary_packets_exclude_condition_and_variant_labels",
        "primary_packets_exclude_execution_metrics",
        "primary_packets_exclude_workflow_compliance",
    ):
        require(packet_manifest.get(key) is True,
                f"internal grading-pack does not attest {key}")

    packet_payloads = {name: payloads[name] for name in sorted(packet_names)}
    packet_ids, packets = validate_packet_payloads(packet_payloads, expected_count)
    require(packet_manifest["packet_sha256"]
            == {name: sha256_bytes(payload) for name, payload in packet_payloads.items()},
            "internal grading packet hashes differ from manifest")
    require(packet_manifest.get("packet_aggregate_sha256")
            == digest_payloads(packet_payloads),
            "internal grading packet aggregate differs from manifest")

    mapping_payload = payloads["operator-mapping.json"]
    require(packet_manifest.get("operator_mapping_sha256")
            == sha256_bytes(mapping_payload),
            "operator mapping hash differs from internal grading manifest")
    mapping_record = json_from_bytes(mapping_payload, "operator mapping")
    mapping = mapping_record.get("mapping")
    require(set(mapping_record) == {"schema_version", "visibility", "mapping"}
            and mapping_record.get("schema_version") == 1
            and mapping_record.get("visibility")
            == "operator only; never provide to a primary grader"
            and isinstance(mapping, list),
            "operator mapping schema is invalid")
    require(all(isinstance(item, dict) and set(item) == OPERATOR_MAPPING_FIELDS
                for item in mapping),
            "operator mapping item schema differs from the exact allowlist")
    mapping_ids = [item.get("grade_id") for item in mapping if isinstance(item, dict)]
    require(len(mapping_ids) == expected_count and set(mapping_ids) == packet_ids
            and len(set(mapping_ids)) == expected_count,
            "operator mapping does not exactly cover unique grading packet IDs")

    completion_payload = payloads["completion-ledger.json"]
    require(packet_manifest.get("completion_ledger_sha256")
            == sha256_bytes(completion_payload),
            "completion-ledger hash differs from internal grading manifest")
    completion_ledger = json_from_bytes(completion_payload, "completion ledger")
    completion.self_verify(pack, config)
    completion.validate_ledger(pack, completion_ledger, require_complete=True)
    require(packet_manifest.get("missing_run_policy_id")
            == completion_ledger["missing_run_policy_id"]
            and packet_manifest.get("missing_run_policy_sha256")
            == completion_ledger["missing_run_policy_sha256"],
            "internal grading-pack missing-run policy binding mismatch")
    require(packet_manifest.get("aggregate_sha256") == digest_payloads({
        **packet_payloads,
        "operator-mapping.json": mapping_payload,
        "completion-ledger.json": completion_payload,
    }), "combined internal grading-pack aggregate differs from manifest")
    return {
        "manifest": packet_manifest,
        "manifest_payload": payloads["packet-manifest.json"],
        "packet_payloads": packet_payloads,
        "packet_ids": packet_ids,
        "packets": packets,
        "mapping_payload": mapping_payload,
        "mapping": mapping,
        "completion_payload": completion_payload,
        "completion_ledger": completion_ledger,
    }


def build_internal_grading_payloads(
    collected: list[dict[str, Any]], config: dict[str, Any],
    sealed_pack_sha256: str, completion_payload: bytes,
    completion_ledger: dict[str, Any], runtime_sha256: str,
) -> tuple[dict[str, bytes], dict[str, Any]]:
    """Build every byte in an internal pack from canonical validated records."""
    grading_seed = config["grading"]["packet_order_seed"]
    require(isinstance(grading_seed, int),
            "frozen packet_order_seed must be an integer")
    ordered = sorted(collected, key=lambda item: item["semantic_run_id"])
    require(len({item["semantic_run_id"] for item in ordered}) == len(ordered),
            "completed checked run identifiers are duplicated")
    random.Random(grading_seed).shuffle(ordered)
    packet_payloads: dict[str, bytes] = {}
    mapping: list[dict[str, Any]] = []
    for order, item in enumerate(ordered):
        grade_id = (
            "GRADE-"
            + hashlib.sha256(f"{grading_seed}:{order}".encode()).hexdigest()[:20]
        )
        packet = {"grade_id": grade_id, **item["packet"]}
        name = f"packets/{grade_id}.json"
        packet_payloads[name] = canonical_json_bytes(packet)
        mapping.append({
            "grade_id": grade_id,
            "semantic_run_id": item["semantic_run_id"],
            "condition": item["condition"],
            "requirement_variant": item["requirement_variant"],
            "execution_metrics": item["execution_metrics"],
            "workflow_compliance_pass": item["workflow_compliance_pass"],
        })
    mapping_payload = canonical_json_bytes({
        "schema_version": 1,
        "visibility": "operator only; never provide to a primary grader",
        "mapping": mapping,
    })
    packet_aggregate = digest_payloads(packet_payloads)
    combined_payloads = {
        **packet_payloads,
        "operator-mapping.json": mapping_payload,
        "completion-ledger.json": completion_payload,
    }
    manifest = {
        "schema_version": 1,
        "suite_id": config["suite_id"],
        "packet_count": len(ordered),
        "grading_seed": grading_seed,
        "sealed_pack_sha256": sealed_pack_sha256,
        "completion_ledger_sha256": sha256_bytes(completion_payload),
        "missing_run_policy_id": completion_ledger["missing_run_policy_id"],
        "missing_run_policy_sha256": completion_ledger["missing_run_policy_sha256"],
        "grader_prompt_sha256": config["grading"]["grader_prompt_sha256"],
        "primary_packets_exclude_condition_and_variant_labels": True,
        "primary_packets_exclude_execution_metrics": True,
        "primary_packets_exclude_workflow_compliance": True,
        "result_eligible": True,
        "checker_mode": "production",
        "checker_runtime_config_sha256": runtime_sha256,
        "isolation_probe_report_sha256": config["posthoc_checker"][
            "isolation_probe_report_sha256"
        ],
        "packet_aggregate_sha256": packet_aggregate,
        "operator_mapping_sha256": sha256_bytes(mapping_payload),
        "aggregate_sha256": digest_payloads(combined_payloads),
        "packet_sha256": {
            name: sha256_bytes(payload)
            for name, payload in sorted(packet_payloads.items())
        },
    }
    return {
        **packet_payloads,
        "packet-manifest.json": canonical_json_bytes(manifest),
        "operator-mapping.json": mapping_payload,
        "completion-ledger.json": completion_payload,
    }, manifest


def collect_grading_records_from_runs(
    pack: Path, runs_root: Path, config: dict[str, Any], expected_count: int,
) -> list[dict[str, Any]]:
    """Reconstruct canonical packet inputs from result-eligible checked runs."""
    runs_root = canonical_existing_path(
        runs_root, directory=True, label="runs root"
    )
    aggregate = read_plain_file(pack / "aggregate.sha256", "sealed pack digest").decode(
        "ascii"
    ).strip()
    run_manifest = json_from_bytes(
        read_plain_file(pack / "run_manifest.json", "sealed run manifest"),
        "sealed run manifest",
    )
    planned_runs = run_manifest.get("runs")
    require(isinstance(planned_runs, list) and len(planned_runs) == expected_count,
            f"sealed run manifest must contain exactly {expected_count} runs")
    semantic_ids = [run.get("run_id") for run in planned_runs if isinstance(run, dict)]
    require(len(semantic_ids) == expected_count
            and all(isinstance(run_id, str) and run_id for run_id in semantic_ids)
            and len(set(semantic_ids)) == expected_count,
            "sealed run manifest identifiers are invalid or duplicated")
    challenge_record = json_from_bytes(
        read_plain_file(pack / "operator_challenges.json", "sealed operator challenges"),
        "sealed operator challenges",
    )
    challenges = challenge_record.get("cases")
    require(isinstance(challenges, list), "sealed operator challenge cases are invalid")
    challenge_by_id = {
        case.get("id"): case for case in challenges
        if isinstance(case, dict) and isinstance(case.get("id"), str)
    }
    require(len(challenge_by_id) == len(challenges),
            "sealed operator challenge identifiers are invalid or duplicated")

    collected: list[dict[str, Any]] = []
    for sealed in sorted(planned_runs, key=lambda run: run["run_id"]):
        semantic_run_id = sealed["run_id"]
        run_dir = runs_root / runner.opaque_id("run", aggregate, semantic_run_id)
        canonical_existing_path(
            run_dir, directory=True, label=f"checked run {semantic_run_id}"
        )
        evidence = completion.validate_checked_run_evidence(
            pack, run_dir, sealed, aggregate, config
        )
        job = evidence["job"]
        result = evidence["agent_result"]
        checker = evidence["checker_result"]
        manifest = completed_agent_manifest_index(evidence, semantic_run_id)
        require_primary_job(job, semantic_run_id)
        challenge = challenge_by_id.get(sealed.get("case_id"))
        require(isinstance(challenge, dict),
                f"sealed run names an unknown challenge: {semantic_run_id}")

        amendment_manifest_path = "output/source-amendment.md"
        if amendment_manifest_path in manifest:
            amendment_bytes = read_manifest_bound_file(
                run_dir / "agent" / "output",
                safe_workspace_relative("source-amendment.md", semantic_run_id),
                amendment_manifest_path,
                manifest,
                f"source amendment for {semantic_run_id}",
            )
            try:
                source_amendment = amendment_bytes.decode("utf-8")
            except UnicodeDecodeError as error:
                raise SystemExit(
                    "target-drift grading preparation failed: invalid UTF-8 source "
                    f"amendment for {semantic_run_id}: {error}"
                ) from error
        else:
            source_amendment = None

        changed_files = checker.get("changed_files")
        require(isinstance(changed_files, list)
                and all(isinstance(value, str) for value in changed_files),
                f"checker changed_files is invalid for {semantic_run_id}")
        changed_lean: list[dict[str, str]] = []
        workspace = canonical_existing_path(
            run_dir / "agent" / "workspace",
            directory=True,
            label=f"agent workspace for {semantic_run_id}",
        )
        lean_index = 0
        for value in changed_files:
            relative = safe_workspace_relative(value, semantic_run_id)
            if relative.suffix != ".lean":
                continue
            content = read_manifest_bound_file(
                workspace,
                relative,
                f"workspace/{relative.as_posix()}",
                manifest,
                f"changed Lean artifact {value} for {semantic_run_id}",
            ).decode("utf-8", errors="replace")
            lean_index += 1
            changed_lean.append({
                "artifact_name": f"lean_artifact_{lean_index}.lean",
                "content": content,
            })
        packet = build_grading_packet(
            challenge,
            sealed,
            result,
            checker,
            source_amendment,
            changed_lean,
            set(challenge_by_id),
            semantic_run_id,
        )
        collected.append({
            "semantic_run_id": semantic_run_id,
            "condition": sealed["condition"],
            "requirement_variant": sealed["requirement_variant"],
            "execution_metrics": checker["execution_usage"],
            "workflow_compliance_pass": checker["workflow_compliance_pass"],
            "packet": packet,
        })
    require(len(collected) == expected_count,
            f"expected {expected_count} completed checked runs, found {len(collected)}")
    return collected


def validate_internal_grading_pack_against_runs(
    pack: Path, runs_root: Path, grading_pack: Path, config: dict[str, Any],
    expected_count: int = PRODUCTION_PACKET_COUNT,
) -> dict[str, Any]:
    """Bind every internal-pack byte to the sealed manifest and checked run evidence."""
    internal = validate_internal_grading_pack(
        pack, grading_pack, config, expected_count=expected_count
    )
    canonical_runs_root = canonical_existing_path(
        runs_root, directory=True, label="runs root"
    )
    # This is deliberately the first source-level operation after structural
    # pack validation: a self-consistent packet tree cannot substitute for the
    # current complete checked-run universe.
    completion.validate_ledger_against_runs(
        pack,
        canonical_runs_root,
        internal["completion_ledger"],
        require_complete=True,
    )
    collected = collect_grading_records_from_runs(
        pack, canonical_runs_root, config, expected_count
    )
    expected_payloads, expected_manifest = build_internal_grading_payloads(
        collected,
        config,
        internal["manifest"]["sealed_pack_sha256"],
        internal["completion_payload"],
        internal["completion_ledger"],
        prepare.checker_runtime_config_sha256(config),
    )
    actual_payloads = {
        **internal["packet_payloads"],
        "packet-manifest.json": internal["manifest_payload"],
        "operator-mapping.json": internal["mapping_payload"],
        "completion-ledger.json": internal["completion_payload"],
    }
    require(actual_payloads == expected_payloads,
            "internal grading-pack bytes do not reconstruct from checked runs")
    require(internal["manifest"] == expected_manifest,
            "internal grading-pack manifest does not reconstruct from checked runs")
    return internal


def build_grader_export_payloads(
    internal: dict[str, Any], grader_prompt: bytes, grading_rubric: bytes,
) -> tuple[dict[str, bytes], dict[str, Any]]:
    packet_manifest = internal["manifest"]
    packet_payloads = internal["packet_payloads"]
    core_payloads = {
        **packet_payloads,
        "grader-prompt.md": grader_prompt,
        "grading-rubric.json": grading_rubric,
    }
    grader_export_sha256 = digest_payloads(core_payloads)
    response_template = {
        "schema_version": GRADER_RESPONSE_SCHEMA_VERSION,
        "grader_id": "REPLACE_WITH_ASSIGNED_GRADER_ID",
        "grading_pack_sha256": packet_manifest["aggregate_sha256"],
        "grader_export_sha256": grader_export_sha256,
        "grader_prompt_sha256": sha256_bytes(grader_prompt),
        "grades": [],
    }
    response_payload = (
        json.dumps(response_template, indent=2, sort_keys=True, ensure_ascii=False) + "\n"
    ).encode("utf-8")
    distributable_payloads = {
        **core_payloads,
        GRADER_EXPORT_RESPONSE_TEMPLATE: response_payload,
    }
    manifest = {
        "schema_version": GRADER_EXPORT_SCHEMA_VERSION,
        "packet_schema_version": 1,
        "grader_response_schema_version": GRADER_RESPONSE_SCHEMA_VERSION,
        "contract_id": "target_drift_primary_grader_export_v1",
        "suite_id": packet_manifest["suite_id"],
        "visibility": "primary-grader distribution only",
        "packet_count": packet_manifest["packet_count"],
        "sealed_pack_sha256": packet_manifest["sealed_pack_sha256"],
        "internal_grading_pack_sha256": packet_manifest["aggregate_sha256"],
        "grader_prompt_sha256": sha256_bytes(grader_prompt),
        "grading_rubric_sha256": sha256_bytes(grading_rubric),
        "packet_aggregate_sha256": packet_manifest["packet_aggregate_sha256"],
        "packet_sha256": packet_manifest["packet_sha256"],
        "grader_export_sha256": grader_export_sha256,
        "response_template_sha256": sha256_bytes(response_payload),
        "export_aggregate_sha256": digest_payloads(distributable_payloads),
        "operator_mapping_included": False,
        "completion_ledger_included": False,
        "execution_metrics_included": False,
        "workflow_compliance_included": False,
        "condition_or_variant_labels_included": False,
        "recursive_blindness_scan_passed": True,
        "operator_only_files_absent": True,
    }
    manifest_payload = (
        json.dumps(manifest, indent=2, sort_keys=True, ensure_ascii=False) + "\n"
    ).encode("utf-8")
    return {
        **distributable_payloads,
        GRADER_EXPORT_MANIFEST: manifest_payload,
    }, manifest


def validate_grader_export(
    pack: Path, runs_root: Path, grading_pack: Path, grader_export: Path,
    config: dict[str, Any], expected_count: int = 450,
) -> dict[str, Any]:
    """Verify that a distribution tree contains only grader-visible bytes."""
    pack_root = canonical_existing_path(pack, directory=True, label="sealed pack")
    runs_root = canonical_existing_path(runs_root, directory=True, label="runs root")
    internal_root = canonical_existing_path(
        grading_pack, directory=True, label="internal grading-pack"
    )
    export_root = canonical_existing_path(
        grader_export, directory=True, label="grader-only export"
    )
    for source_root, source_label in (
        (pack_root, "sealed pack"),
        (runs_root, "runs root"),
        (internal_root, "internal grading-pack"),
    ):
        require_separate_trees(
            export_root,
            source_root,
            left_label="grader-only export",
            right_label=source_label,
        )
    internal = validate_internal_grading_pack_against_runs(
        pack_root, runs_root, internal_root, config, expected_count=expected_count,
    )
    prompt_path = pack_root / "grader_prompt.md"
    rubric_path = pack_root / "grading_rubric.json"
    grader_prompt = read_plain_file(prompt_path, "sealed grader prompt")
    grading_rubric = read_plain_file(rubric_path, "sealed grading rubric")
    require(sha256_bytes(grader_prompt) == config["grading"]["grader_prompt_sha256"],
            "sealed grader prompt differs from frozen config")
    require(json_from_bytes(grading_rubric, "sealed grading rubric").get("no_results")
            is True, "sealed grading rubric must remain result-free")
    expected_payloads, expected_manifest = build_grader_export_payloads(
        internal, grader_prompt, grading_rubric,
    )
    actual_payloads = read_plain_tree(
        export_root, set(expected_payloads), "grader-only export",
    )
    require(actual_payloads == expected_payloads,
            "grader-only export bytes differ from the positive-allowlist materialization")
    manifest = json_from_bytes(
        actual_payloads[GRADER_EXPORT_MANIFEST], "grader-only export manifest"
    )
    require(manifest == expected_manifest,
            "grader-only export manifest differs from the validated internal grading-pack")
    validate_packet_payloads(
        {name: actual_payloads[name] for name in internal["packet_payloads"]},
        expected_count,
    )
    return manifest


def write_payload_tree(root: Path, payloads: dict[str, bytes]) -> None:
    """Write an allowlisted tree with exclusive-create files and per-file fsync."""
    for relative, payload in sorted(payloads.items()):
        target = root / Path(relative)
        target.parent.mkdir(parents=True, exist_ok=True)
        try:
            with target.open("xb") as stream:
                stream.write(payload)
                stream.flush()
                os.fsync(stream.fileno())
        except OSError as error:
            raise SystemExit(
                f"target-drift grading preparation failed: cannot write "
                f"grading artifact file {relative}: {error}"
            ) from error


def write_atomic_file(output: Path, payload: bytes, label: str) -> None:
    """Publish one fully written file without overwriting a concurrent destination."""
    output = canonical_new_output(output, label)
    descriptor, raw_staging = tempfile.mkstemp(
        prefix=f".{output.name}.tmp-", dir=output.parent
    )
    staging = Path(raw_staging)
    published = False
    try:
        with os.fdopen(descriptor, "wb") as stream:
            stream.write(payload)
            stream.flush()
            os.fsync(stream.fileno())
        require_plain_path(staging, directory=False, label=f"temporary {label}")
        try:
            os.link(staging, output)
        except OSError as error:
            raise SystemExit(
                f"target-drift grading preparation failed: cannot publish {label} "
                f"without clobbering: {error}"
            ) from error
        published = True
        staging.unlink()
        try:
            directory_descriptor = os.open(output.parent, os.O_RDONLY)
        except OSError:
            directory_descriptor = None
        if directory_descriptor is not None:
            try:
                os.fsync(directory_descriptor)
            except OSError:
                pass
            finally:
                os.close(directory_descriptor)
        require_plain_path(output, directory=False, label=label)
    finally:
        if not published and os.path.lexists(staging):
            try:
                require_plain_path(staging, directory=False, label=f"temporary {label}")
                staging.unlink()
            except (OSError, SystemExit):
                pass


def cleanup_staging_tree(staging: Path, expected_parent: Path) -> None:
    """Remove only the plain temporary root created by this invocation."""
    if staging.parent != expected_parent or not os.path.lexists(staging):
        return
    try:
        require_plain_path(staging, directory=True, label="temporary grading tree")
    except SystemExit:
        # A replaced/reparsed root is intentionally left for operator review;
        # never follow it during error cleanup.
        return
    shutil.rmtree(staging)


def materialize_grader_export(
    pack: Path, runs_root: Path, grading_pack: Path, output: Path,
    config: dict[str, Any], expected_count: int = 450,
) -> dict[str, Any]:
    """Atomically materialize a physically separate, positive-allowlist export."""
    pack = canonical_existing_path(pack, directory=True, label="sealed pack")
    runs_root = canonical_existing_path(runs_root, directory=True, label="runs root")
    grading_pack = canonical_existing_path(
        grading_pack, directory=True, label="internal grading-pack"
    )
    output = canonical_new_output(output, "grader-only export output")
    for source_root, source_label in (
        (pack, "sealed pack"),
        (runs_root, "runs root"),
        (grading_pack, "internal grading-pack"),
    ):
        require_separate_trees(
            output,
            source_root,
            left_label="grader-only export",
            right_label=source_label,
        )
    internal = validate_internal_grading_pack_against_runs(
        pack, runs_root, grading_pack, config, expected_count=expected_count,
    )
    grader_prompt = read_plain_file(pack / "grader_prompt.md", "sealed grader prompt")
    grading_rubric = read_plain_file(
        pack / "grading_rubric.json", "sealed grading rubric"
    )
    payloads, expected_manifest = build_grader_export_payloads(
        internal, grader_prompt, grading_rubric,
    )
    staging = Path(tempfile.mkdtemp(
        prefix=f".{output.name}.tmp-", dir=output.parent,
    ))
    try:
        write_payload_tree(staging, payloads)
        validated = validate_grader_export(
            pack, runs_root, grading_pack, staging, config,
            expected_count=expected_count,
        )
        require(validated == expected_manifest,
                "staged grader-only export differs from expected manifest")
        os.replace(staging, output)
    except BaseException:
        cleanup_staging_tree(staging, output.parent)
        raise
    return validate_grader_export(
        pack, runs_root, grading_pack, output, config,
        expected_count=expected_count,
    )


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--pack", type=Path, required=True)
    parser.add_argument("--runs-root", type=Path, required=True)
    parser.add_argument("--completion-ledger", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    pack = canonical_existing_path(args.pack, directory=True, label="sealed pack")
    runs_root = canonical_existing_path(
        args.runs_root, directory=True, label="runs root"
    )
    output = canonical_new_output(args.output, "grading output directory")
    for source_root, label in ((pack, "sealed pack"), (runs_root, "runs root")):
        require(
            not path_is_within(output, source_root)
            and not path_is_within(source_root, output),
            f"grading output and {label} must be separate trees",
        )

    prepare.verify_pack(pack)
    config = load(pack / "execution_config.json")
    require(config["suite_id"] == "ABRL-TARGET-DRIFT-V2", "grading requires v2 pack")
    require(config["execution_status"] == "frozen_ready", "grading requires frozen_ready pack")
    completion.self_verify(pack, config)
    completion_ledger_path = canonical_existing_path(
        args.completion_ledger, directory=False, label="completion ledger"
    )
    completion_ledger_bytes = read_plain_file(
        completion_ledger_path, "completion ledger"
    )
    completion_ledger = json_from_bytes(completion_ledger_bytes, "completion ledger")
    completion.validate_ledger_against_runs(
        pack, runs_root, completion_ledger, require_complete=True,
    )
    completion_ledger_sha256 = hashlib.sha256(completion_ledger_bytes).hexdigest()
    checker_config = config["posthoc_checker"]
    probe = load(pack / "checker_isolation_probe.json")
    runtime_sha256 = require_production_checker(config, probe)
    current = Path(__file__).resolve()
    expected_hash = config["grading"]["packet_materializer_sha256"]
    require(sha256_bytes(read_plain_file(
        current, "current grading materializer"
    )) == expected_hash,
            "invoked grading materializer differs from frozen hash")
    require(sha256_bytes(read_plain_file(
        pack / "execution_code" / current.name, "sealed grading materializer"
    )) == expected_hash,
            "sealed grading materializer differs from frozen hash")
    prepare_path = Path(prepare.__file__).resolve()
    prepare_hash = config["sealed_agent_view"]["materializer_sha256"]
    require(sha256_bytes(read_plain_file(
        prepare_path, "current pack verifier"
    )) == prepare_hash,
            "imported pack verifier differs from frozen hash")
    require(sha256_bytes(read_plain_file(
        pack / "execution_code" / prepare_path.name, "sealed pack verifier"
    )) == prepare_hash, "sealed pack verifier differs from frozen hash")
    runner_path = Path(runner.__file__).resolve()
    runner_hash = config["sealed_agent_view"]["run_preparer_sha256"]
    require(sha256_bytes(read_plain_file(
        runner_path, "current run helper"
    )) == runner_hash,
            "imported run helper differs from frozen hash")
    require(sha256_bytes(read_plain_file(
        pack / "execution_code" / runner_path.name, "sealed run helper"
    )) == runner_hash, "sealed run helper differs from frozen hash")
    grading_seed = config["grading"]["packet_order_seed"]
    require(isinstance(grading_seed, int), "frozen packet_order_seed must be an integer")
    run_manifest = load(pack / "run_manifest.json")
    challenges = load(pack / "operator_challenges.json")["cases"]
    challenge_by_id = {case["id"]: case for case in challenges}
    sealed_by_id = {run["run_id"]: run for run in run_manifest["runs"]}

    collected = []
    for run_dir in sorted(path for path in runs_root.iterdir() if path.is_dir()):
        job_path = run_dir / "operator" / "job.json"
        checker_path = run_dir / "operator" / "checker" / "checker-result.json"
        result_path = run_dir / "agent" / "output" / "result.json"
        state_path = run_dir / "operator" / "run_state.json"
        receipt_path = run_dir / "operator" / "execution-receipt.json"
        adapter_response_path = run_dir / "operator" / "adapter" / "response.json"
        checker_receipt_path = (
            run_dir / "operator" / "checker" / "checker-execution-receipt.json"
        )
        checker_response_path = run_dir / "operator" / "checker" / "sandbox-response.json"
        if not all(path.is_file() for path in (
            job_path, checker_path, result_path, state_path, receipt_path,
            adapter_response_path, checker_receipt_path, checker_response_path,
        )):
            continue
        job = load(job_path)
        checker = load(checker_path)
        result = load(result_path)
        state = load(state_path)
        receipt = load(receipt_path)
        adapter_response = load(adapter_response_path)
        checker_receipt = load(checker_receipt_path)
        checker_response = load(checker_response_path)
        require(job.get("semantic_run_id") in sealed_by_id,
                f"run is absent from the sealed manifest: {run_dir.name}")
        sealed = sealed_by_id[job["semantic_run_id"]]
        aggregate = (pack / "aggregate.sha256").read_text(
            encoding="ascii"
        ).strip()
        evidence = completion.validate_checked_run_evidence(
            pack, run_dir, sealed, aggregate, config
        )
        manifest = completed_agent_manifest_index(evidence, run_dir.name)
        require_primary_job(job, run_dir.name)
        require_real_provider_completion(
            config, receipt, adapter_response, adapter_response_path, run_dir.name
        )
        require(state["prepared_job_sha256"] == receipt["prepared_job_sha256"]
                == prepare.sha256_file(job_path),
                f"prepared-job hash mismatch for {run_dir.name}")
        workspace_manifest_path = run_dir / "operator" / "workspace_manifest.json"
        require(state["workspace_manifest_sha256"] == receipt["workspace_manifest_sha256"]
                == prepare.sha256_file(workspace_manifest_path),
                f"workspace-manifest hash mismatch for {run_dir.name}")
        require(state["status"] == "checked", f"run is not checked: {run_dir.name}")
        require(state.get("result_eligible") is True
                and state.get("checker_mode") == "production",
                f"run is not production-result-eligible: {run_dir.name}")
        require(state.get("checker_runtime_config_sha256") == runtime_sha256
                and state.get("isolation_probe_report_sha256")
                == checker_config["isolation_probe_report_sha256"],
                f"run checker runtime/probe binding mismatch: {run_dir.name}")
        require(state["checker_result_sha256"] == prepare.sha256_file(checker_path),
                f"checker-result hash mismatch for {run_dir.name}")
        require(state["checker_execution_receipt_sha256"]
                == prepare.sha256_file(checker_receipt_path),
                f"checker-execution-receipt hash mismatch for {run_dir.name}")
        require(state["sandbox_response_sha256"]
                == prepare.sha256_file(checker_response_path),
                f"checker sandbox-response hash mismatch for {run_dir.name}")
        checker_request_path = (
            run_dir / "operator" / "checker-attempts"
            / state["checker_attempt_id"] / "request.json"
        )
        require(checker_request_path.is_file()
                and state["checker_request_sha256"]
                == checker_receipt["checker_request_sha256"]
                == checker_response["request_sha256"]
                == prepare.sha256_file(checker_request_path),
                f"checker sanitized-request hash mismatch for {run_dir.name}")
        require(checker_receipt["sandbox_response_sha256"]
                == state["sandbox_response_sha256"],
                f"checker response/receipt chain mismatch for {run_dir.name}")
        require(checker_receipt["checker_result_sha256"]
                == state["checker_result_sha256"]
                == checker_response["checker_result_sha256"],
                f"checker result/receipt chain mismatch for {run_dir.name}")
        require(checker_receipt["checker_artifact_aggregate_sha256"]
                == state["checker_artifact_aggregate_sha256"]
                == checker_response["artifact_aggregate_sha256"],
                f"checker artifact aggregate mismatch for {run_dir.name}")
        require(checker_response["container_image_digest"]
                == checker_config["container_image_digest"],
                f"checker image differs from frozen config for {run_dir.name}")
        expected_checker_response = {
            "checker_attempt_label": state["checker_attempt_id"],
            "checker_id": checker_config["checker_id"],
            "checker_version": checker_config["checker_version"],
            "inner_checker_sha256": checker_config["inner_checker_sha256"],
            "checker_contract_sha256": checker_config["contract_sha256"],
            "checker_runtime_config_sha256": runtime_sha256,
            "filesystem_network_process_attestation": checker_config[
                "filesystem_network_process_attestation"
            ],
            "controller_worker_separation_attestation": checker_config[
                "controller_worker_separation_attestation"
            ],
        }
        for key, value in expected_checker_response.items():
            require(checker_response.get(key) == value,
                    f"checker response differs from frozen {key}: {run_dir.name}")
        require(checker_receipt.get("checker_mode") == "production"
                and checker_receipt.get("result_eligible") is True
                and checker_receipt.get("checker_runtime_config_sha256") == runtime_sha256
                and checker_receipt.get("isolation_probe_report_sha256")
                == checker_config["isolation_probe_report_sha256"],
                f"checker receipt is not production eligible: {run_dir.name}")
        require(checker.get("checker_runtime_config_sha256") == runtime_sha256,
                f"checker result names a different runtime: {run_dir.name}")
        require(state["execution_receipt_sha256"] == prepare.sha256_file(receipt_path),
                f"execution-receipt hash mismatch for {run_dir.name}")
        require(checker["sealed_pack_sha256"] == receipt["sealed_pack_sha256"]
                == (pack / "aggregate.sha256").read_text(encoding="ascii").strip(),
                f"run sealed-pack binding mismatch for {run_dir.name}")
        current_manifest_sha256 = manifest_sha256(agent_manifest(run_dir / "agent"))
        require(current_manifest_sha256 == receipt["completed_agent_manifest_sha256"]
                == checker["completed_agent_manifest_sha256"],
                f"agent view changed after neutral checking for {run_dir.name}")
        require(checker["execution_receipt_sha256"] == prepare.sha256_file(receipt_path),
                f"checker names a different execution receipt for {run_dir.name}")
        require(job["opaque_run_id"] == state["opaque_run_id"]
                == receipt["opaque_run_id"] == checker["opaque_run_id"]
                == runner.opaque_id("run", aggregate, job["semantic_run_id"]),
                f"opaque run binding mismatch for {run_dir.name}")
        require(job["condition"] == sealed["condition"]
                and job["replicate"] == sealed["replicate"],
                f"job condition/replicate differs from sealed run for {run_dir.name}")
        challenge = challenge_by_id[sealed["case_id"]]
        amendment_manifest_path = "output/source-amendment.md"
        if amendment_manifest_path in manifest:
            amendment_bytes = read_manifest_bound_file(
                run_dir / "agent" / "output",
                safe_workspace_relative("source-amendment.md", job["opaque_run_id"]),
                amendment_manifest_path,
                manifest,
                f"source amendment for {job['opaque_run_id']}",
            )
            try:
                source_amendment = amendment_bytes.decode("utf-8")
            except UnicodeDecodeError as error:
                raise SystemExit(
                    "target-drift grading preparation failed: invalid UTF-8 source "
                    f"amendment for {job['opaque_run_id']}: {error}"
                ) from error
        else:
            source_amendment = None

        changed_lean = []
        workspace = canonical_existing_path(
            run_dir / "agent" / "workspace",
            directory=True,
            label=f"agent workspace for {job['opaque_run_id']}",
        )
        lean_index = 0
        for relative_value in checker["changed_files"]:
            relative = safe_workspace_relative(relative_value, job["opaque_run_id"])
            if relative.suffix != ".lean":
                continue
            lean_index += 1
            changed_lean.append({
                "artifact_name": f"lean_artifact_{lean_index}.lean",
                "content": read_manifest_bound_file(
                    workspace,
                    relative,
                    f"workspace/{relative.as_posix()}",
                    manifest,
                    f"changed Lean artifact {relative_value}",
                ).decode("utf-8", errors="replace"),
            })

        packet = build_grading_packet(
            challenge,
            sealed,
            result,
            checker,
            source_amendment,
            changed_lean,
            set(challenge_by_id),
            job["opaque_run_id"],
        )
        collected.append({
            "semantic_run_id": job["semantic_run_id"],
            "condition": sealed["condition"],
            "requirement_variant": sealed["requirement_variant"],
            "execution_metrics": checker["execution_usage"],
            "workflow_compliance_pass": checker["workflow_compliance_pass"],
            "packet": packet,
        })

    require(len(collected) == PRODUCTION_PACKET_COUNT,
            f"expected {PRODUCTION_PACKET_COUNT} completed checked runs, "
            f"found {len(collected)}")
    all_payloads, manifest = build_internal_grading_payloads(
        collected,
        config,
        (pack / "aggregate.sha256").read_text(encoding="ascii").strip(),
        completion_ledger_bytes,
        completion_ledger,
        runtime_sha256,
    )
    staging = Path(
        tempfile.mkdtemp(prefix=f".{output.name}.tmp-", dir=output.parent)
    )
    try:
        write_payload_tree(staging, all_payloads)
        validate_internal_grading_pack_against_runs(
            pack, runs_root, staging, config,
            expected_count=PRODUCTION_PACKET_COUNT,
        )
        os.replace(staging, output)
    except BaseException:
        cleanup_staging_tree(staging, output.parent)
        raise
    validate_internal_grading_pack_against_runs(
        pack, runs_root, output, config,
        expected_count=PRODUCTION_PACKET_COUNT,
    )
    print(
        f"materialized {len(collected)} blind grading packets, sha256={manifest['aggregate_sha256']}"
    )


if __name__ == "__main__":
    main()
