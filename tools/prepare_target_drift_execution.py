#!/usr/bin/env python3
"""Validate or materialize the result-free ABRL target-drift execution pack."""

from __future__ import annotations

import argparse
from datetime import datetime, timedelta, timezone
import hashlib
import json
import os
import random
import re
import shutil
import stat
import subprocess
import sys
import tempfile
from pathlib import Path, PurePosixPath, PureWindowsPath
from typing import Any

import launch_target_drift_checker_container as checker_launcher
import prepare_target_drift_checker_image as checker_image_builder
import target_drift_checker_cache_manifest as checker_cache_manifest
import validate_target_drift_human_contract_external_verification as external_contract_review
import validate_target_drift_human_contract_review as human_contract_review


ROOT = Path(__file__).resolve().parents[1]
SUITE = ROOT / "evaluation" / "target-drift-v1"
CONDITIONS = ("compile_only", "source_aware_blueprint", "abrl")
PRIMARY_ANALYSIS_METHOD_ID = (
    "fixed_30_target_variant_preserving_paired_invocation_bootstrap_v1"
)
PRIMARY_ANALYSIS_SUCCESS_RULE = (
    "lower endpoint of the fixed-target, variant-preserving paired-invocation "
    "bootstrap interval above zero; report faithful-request specificity and "
    "injected-drift sensitivity alongside the primary result"
)
PRIMARY_ANALYSIS_PAIRING_KEY = [
    "case_id", "replicate", "requirement_variant",
]
PRIMARY_ANALYSIS_BOOTSTRAP_REPLICATES = 20000
PRIMARY_ANALYSIS_PERMUTATION_REPLICATES = 32768
METHOD_AMENDMENT_PATH = (
    "evaluation/target-drift-v2/"
    "method-amendment-fixed-target-paired-bootstrap-2026-08-31.json"
)
METHOD_AMENDMENT_SHA256 = (
    "5aed16ea25975786d79792ee194d87c081ec01247dbb1d314da05c8f582fdb9d"
)
METHOD_AMENDMENT_ID = (
    "ABRL-TARGET-DRIFT-FIXED-TARGET-PAIRED-BOOTSTRAP-METHOD-AMENDMENT-2026-08-31"
)
PLACEHOLDERS = (
    "{{CASE_ID}}",
    "{{SOURCE_ID}}",
    "{{SOURCE_LOCATOR}}",
    "{{SOURCE_PACKET_PATH}}",
    "{{PROPOSED_REQUIREMENT}}",
    "{{WORKSPACE_PATH}}",
)
PRIMARY_GRADING_PROVENANCE_MARKERS = (
    "compile-only condition",
    "source-aware blueprint condition",
    "full abrl condition",
    "condition=compile_only",
    "condition=source_aware_blueprint",
    "condition=abrl",
    "promotion gate",
    "proof-blueprint",
    "target-contract",
    "failure ledger",
    "evidence-typed",
    "bounded proof transaction",
)
LEAN_PROVENANCE_MARKERS = PRIMARY_GRADING_PROVENANCE_MARKERS[:6]
TRUST_ANCHOR_CONTRACT_ID = (
    "ABRL-TARGET-DRIFT-V2-EXTERNAL-SIGNER-TRUST-ANCHOR"
)
TRUST_ANCHOR_PRODUCTION_STATUS = (
    "public_pre_outcome_signer_registry_anchor_frozen"
)
TRUST_ANCHOR_PUBLIC_REPOSITORY_URL_POLICY = (
    "credential-free HTTPS GitHub repository URL ending in .git; concrete "
    "repository remains UNSET until a real anchor is preregistered"
)
TRUST_ANCHOR_PUBLIC_REF = "refs/heads/main"
TRUST_ANCHOR_EXCLUDED_STATUS = "excluded_fixture_unanchored"
TRUST_ANCHOR_EXCLUDED_PROOF = b"EXCLUDED FIXTURE - NO GIT TRUST ANCHOR\n"
TRUST_ANCHOR_CLAIM_BOUNDARY = (
    "Git ancestry and byte identity establish only that the signer-registry "
    "bindings were publicly frozen before the later execution commit. They do "
    "not prove trusted wall-clock time, human identity, qualification, "
    "independence, or absence of conflicts; those properties still rely on the "
    "external verifier attestation and escrow evidence."
)
TRUST_ANCHOR_CONTRACT_BOUNDARY = {
    "git_history_establishes": (
        "The named anchor bytes were already present at the named ancestor "
        "commit and remain byte-identical."
    ),
    "git_history_does_not_establish": (
        "That any key holder is human, independent, conflict-free, or qualified, "
        "or that Git commit timestamps are trusted wall-clock timestamps."
    ),
    "identity_qualification_basis_after_anchor": (
        "The independently obtained external verifier attestation and its "
        "public/private escrow evidence, with the external-verifier key pinned "
        "by the prior public anchor."
    ),
    "real_anchor_present_in_this_contract": False,
    "production_execution_eligible": False,
}
TRUST_ANCHOR_REQUIRED_FIELDS = frozenset({
    "schema_version", "contract_id", "anchor_id", "status",
    "anchor_git_commit", "anchor_repository_path", "anchor_registered_at_utc",
    "anchor_public_repository_url", "anchor_public_ref",
    "anchor_public_commit_locator",
    "review_started_before_anchor", "evaluation_outcomes_observed_before_anchor",
    "benchmark_execution_complete_before_anchor", "role_registry_bytes_sha256",
    "role_registry_canonical_sha256", "allowed_signers_bytes_sha256",
    "external_verifier_principal", "external_verifier_public_key_fingerprint",
    "public_escrow_receipt_locator", "public_escrow_receipt_sha256",
    "claim_boundary",
})
HUMAN_REVIEW_SEALED_ROOT = "SEALED/human_source_contract_review"
HUMAN_REVIEW_FILE_BINDINGS = (
    ("protocol", "protocol_sha256", "self-review-protocol.json"),
    ("reviewer_a", "reviewer_a_sha256", "reviewer-a.json"),
    ("reviewer_a_signature", "reviewer_a_signature_sha256", "reviewer-a.sig"),
    ("reviewer_b", "reviewer_b_sha256", "reviewer-b.json"),
    ("reviewer_b_signature", "reviewer_b_signature_sha256", "reviewer-b.sig"),
    ("adjudication", "adjudication_sha256", "adjudication.json"),
    ("adjudication_signature", "adjudication_signature_sha256", "adjudication.sig"),
    ("completion_attestation", "completion_attestation_sha256",
     "self-attested-completion.json"),
    ("external_protocol", "external_protocol_sha256",
     "external-verification-protocol.json"),
    ("external_trust_anchor_contract", "external_trust_anchor_contract_sha256",
     "external-trust-anchor-contract.json"),
    ("external_trust_anchor", "external_trust_anchor_sha256",
     "external-trust-anchor.json"),
    ("external_trust_anchor_git_object_proof",
     "external_trust_anchor_git_object_proof_sha256",
     "external-trust-anchor-git-object-proof.pack"),
    ("role_registry", "role_registry_sha256", "role-registry.json"),
    ("allowed_signers", "allowed_signers_sha256", "allowed_signers"),
    ("external_receipt", "external_receipt_sha256", "external-receipt.json"),
    ("external_receipt_signature", "external_receipt_signature_sha256",
     "external-receipt.sig"),
    ("external_attestation", "external_attestation_sha256",
     "external-attestation.json"),
)
HUMAN_REVIEW_PACKET_FILES = (
    "packet-manifest.json", "reviewer-template.json", "adjudication-template.json",
)
HUMAN_REVIEW_EXPECTED_FILES = frozenset(
    [item[2] for item in HUMAN_REVIEW_FILE_BINDINGS] + list(HUMAN_REVIEW_PACKET_FILES)
)
HUMAN_REVIEW_CONFIG_FIELDS = frozenset({
    "self_attested_prepare_script", "self_attested_prepare_script_sha256",
    "self_attested_validator_script", "self_attested_validator_script_sha256",
    "self_attested_validator_test", "self_attested_validator_test_sha256",
    "execution_finalizer", "execution_finalizer_sha256",
    "review_packet", "review_packet_manifest_sha256",
    "external_validator_script", "external_validator_script_sha256",
    "external_validator_test", "external_validator_test_sha256",
    "required_self_attested_status", "required_external_status",
    "required_external_trust_anchor_status",
    "combined_prerequisite_status", "combined_prerequisite_satisfied",
    "evaluation_outcomes_observed_before_validation",
} | {
    field
    for path_field, hash_field, _ in HUMAN_REVIEW_FILE_BINDINGS
    for field in (path_field, hash_field)
})


def reject_duplicate_keys(pairs: list[tuple[str, Any]]) -> dict[str, Any]:
    value: dict[str, Any] = {}
    for key, item in pairs:
        require(key not in value, f"duplicate JSON key: {key}")
        value[key] = item
    return value


def strict_json_text(text: str, label: str) -> dict[str, Any]:
    try:
        value = json.loads(text, object_pairs_hook=reject_duplicate_keys)
    except json.JSONDecodeError:
        require(False, f"{label} is not valid JSON")
    require(isinstance(value, dict), f"{label} must contain one JSON object")
    return value


def strict_json_bytes(payload: bytes, label: str) -> dict[str, Any]:
    try:
        text = payload.decode("utf-8")
    except UnicodeDecodeError:
        require(False, f"{label} is not valid UTF-8")
    return strict_json_text(text, label)


def load(path: Path) -> dict[str, Any]:
    return strict_json_text(path.read_text(encoding="utf-8"), str(path))


def dump(path: Path, value: Any) -> None:
    path.write_text(
        json.dumps(value, indent=2, sort_keys=True, ensure_ascii=False) + "\n",
        encoding="utf-8",
    )


def require(condition: bool, message: str) -> None:
    if not condition:
        raise SystemExit(f"target-drift preparation failed: {message}")


def sha256_bytes(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def sha256_file(path: Path) -> str:
    return sha256_bytes(path.read_bytes())


def canonical_json_bytes(value: Any) -> bytes:
    return (
        json.dumps(value, indent=2, sort_keys=True, ensure_ascii=False) + "\n"
    ).encode("utf-8")


def portable_hash_locator(label: str, digest: Any) -> str:
    suffix = digest if isinstance(digest, str) and re.fullmatch(
        r"[0-9a-f]{64}", digest
    ) else "UNRESOLVED"
    return f"HOST-BOUND/{label}/sha256/{suffix}"


def opaque_config_binding(value: Any, label: str) -> Any:
    if value == "UNSET":
        return value
    locator = f"REDACTED-OPERATOR/{label}"
    if (isinstance(value, dict)
            and value.get("portable_locator") == locator
            and isinstance(value.get("canonical_sha256"), str)
            and re.fullmatch(r"[0-9a-f]{64}", value["canonical_sha256"])):
        return value
    return {
        "portable_locator": locator,
        "canonical_sha256": sha256_bytes(canonical_json_bytes(value)),
    }


def rewrite_config_strings(value: Any, replacements: dict[str, str]) -> Any:
    if isinstance(value, str):
        rewritten = value
        for source in sorted(replacements, key=len, reverse=True):
            if source and source != "UNSET":
                rewritten = rewritten.replace(source, replacements[source])
        return rewritten
    if isinstance(value, list):
        return [rewrite_config_strings(item, replacements) for item in value]
    if isinstance(value, dict):
        return {
            key: rewrite_config_strings(item, replacements)
            for key, item in value.items()
        }
    return value


def absolute_parent_spellings(path_text: str) -> set[str]:
    """Return POSIX and Windows spellings of an absolute path's parent.

    Audit packs can be prepared on a different operating system from the
    operator that supplied the frozen paths.  Native ``Path`` semantics alone
    therefore miss, for example, a Windows drive path while running on Linux.
    """
    spellings: set[str] = set()
    for path_type in (PurePosixPath, PureWindowsPath):
        candidate = path_type(path_text)
        if not candidate.is_absolute():
            continue
        parent = candidate.parent
        if parent == path_type(candidate.anchor):
            continue
        spellings.add(str(parent))
        spellings.add(parent.as_posix())
    return spellings


def is_cross_platform_absolute(path_text: str) -> bool:
    return (
        PurePosixPath(path_text).is_absolute()
        or PureWindowsPath(path_text).is_absolute()
    )


def sealed_config_for_pack(config: dict[str, Any]) -> dict[str, Any]:
    """Return a portable audit config with no operator-local host paths."""
    packed = json.loads(json.dumps(config))
    replacements: dict[str, str] = {}

    def bind_path(path_text: Any, logical: str) -> None:
        if not isinstance(path_text, str) or path_text == "UNSET":
            return
        def bind_one(source: str) -> None:
            replacements[source] = logical
            for parent in absolute_parent_spellings(source):
                replacements.setdefault(
                    parent, "HOST-BOUND/operator-directory"
                )
        bind_one(path_text)
        try:
            bind_one(str(resolve_repo_path(path_text).resolve()))
        except (OSError, RuntimeError):
            pass

    if "source_files_manifest" in packed:
        bind_path(config.get("source_files_manifest"), "SEALED/source_manifest.json")
        packed["source_files_manifest"] = "SEALED/source_manifest.json"

    entry = packed.get("human_source_contract_validation")
    if isinstance(entry, dict):
        source_entry = config["human_source_contract_validation"]
        bind_path(source_entry.get("review_packet"), HUMAN_REVIEW_SEALED_ROOT)
        entry["review_packet"] = HUMAN_REVIEW_SEALED_ROOT
        for path_field, _, filename in HUMAN_REVIEW_FILE_BINDINGS:
            logical = f"{HUMAN_REVIEW_SEALED_ROOT}/{filename}"
            bind_path(source_entry.get(path_field), logical)
            entry[path_field] = logical

    adapter = packed.get("execution_adapter")
    if isinstance(adapter, dict):
        source_adapter = config["execution_adapter"]
        entrypoint = "SEALED/execution_code/execution_adapter_entrypoint"
        bind_path(source_adapter.get("entrypoint_path"), entrypoint)
        adapter["entrypoint_path"] = entrypoint
        runtime = portable_hash_locator(
            "execution-adapter-runtime", source_adapter.get("runtime_executable_sha256")
        )
        bind_path(source_adapter.get("runtime_executable"), runtime)
        adapter["runtime_executable"] = runtime
        provider = adapter.get("provider_runtime")
        source_provider = source_adapter.get("provider_runtime", {})
        if isinstance(provider, dict):
            provider_runtime = portable_hash_locator(
                "provider-runtime", source_provider.get("executable_sha256")
            )
            bind_path(source_provider.get("executable"), provider_runtime)
            provider["executable"] = provider_runtime
            bind_path(
                source_provider.get("auth_source_path"),
                "OPERATOR-SECRET/provider-auth-source",
            )
            provider["auth_source_path"] = "OPERATOR-SECRET/provider-auth-source"
            for field in (
                "fresh_codex_home_attestation", "process_environment",
                "shell_environment",
            ):
                provider[field] = opaque_config_binding(
                    source_provider.get(field), f"provider-runtime/{field}"
                )
        for field in (
            "budget_enforcement_attestation", "filesystem_network_process_attestation",
        ):
            adapter[field] = opaque_config_binding(
                source_adapter.get(field), f"execution-adapter/{field}"
            )

    checker = packed.get("posthoc_checker")
    if isinstance(checker, dict):
        source_checker = config["posthoc_checker"]
        checker_path_bindings = {
            "driver_path": "SEALED/execution_code/check_target_drift_run.py",
            "inner_checker_path":
                "SEALED/execution_code/check_target_drift_inner.py",
            "isolation_probe_runner_path": (
                "SEALED/execution_code/record_target_drift_checker_isolation_probe.py"
            ),
            "host_launcher_path": (
                "SEALED/execution_code/launch_target_drift_checker_container.py"
            ),
            "host_python_executable": portable_hash_locator(
                "checker-host-python", source_checker.get("host_python_executable_sha256")
            ),
            "container_runtime_executable": portable_hash_locator(
                "checker-container-runtime",
                source_checker.get("container_runtime_executable_sha256"),
            ),
            "checker_image_recipe":
                "SEALED/checker_runtime_artifacts/checker-image.Containerfile",
            "checker_image_sbom":
                "SEALED/checker_runtime_artifacts/checker-image-sbom.json",
            "checker_image_build_input_manifest":
                "SEALED/checker_runtime_artifacts/checker-image-build-input.json",
            "checker_cache_manifest_artifact":
                "SEALED/checker_runtime_artifacts/checker-cache-manifest.json",
            "checker_image_build_log":
                "SEALED/checker_runtime_artifacts/checker-image-build.log",
            "controller_entrypoint_source":
                "SEALED/execution_code/check_target_drift_container_controller.py",
            "isolation_probe_report": "SEALED/checker_isolation_probe.json",
            "isolation_probe_artifacts_dir":
                "SEALED/checker_isolation_probe_artifacts",
        }
        for field, logical in checker_path_bindings.items():
            bind_path(source_checker.get(field), logical)
            checker[field] = logical
        for field in (
            "filesystem_network_process_attestation",
            "controller_worker_separation_attestation",
        ):
            checker[field] = opaque_config_binding(
                source_checker.get(field), f"posthoc-checker/{field}"
            )

    packed = rewrite_config_strings(packed, replacements)
    serialized = json.dumps(packed, sort_keys=True, ensure_ascii=False)
    for source in replacements:
        if source and source != "UNSET" and is_cross_platform_absolute(source):
            require(source not in serialized,
                    f"portable packed config retains operator path {source}")
    return packed


def normalized_config_for_digest(config: dict[str, Any]) -> dict[str, Any]:
    normalized = sealed_config_for_pack(config)
    normalized["execution_status"] = "frozen_ready"
    normalized["sealed_agent_view"]["aggregate_sha256"] = "UNSET"
    normalized["unresolved_fields"] = []
    return normalized


def aggregate_digest(components: dict[str, bytes]) -> tuple[str, list[dict[str, Any]]]:
    digest = hashlib.sha256()
    manifest: list[dict[str, Any]] = []
    for name in sorted(components):
        payload = components[name]
        encoded_name = name.encode("utf-8")
        digest.update(len(encoded_name).to_bytes(8, "big"))
        digest.update(encoded_name)
        digest.update(len(payload).to_bytes(8, "big"))
        digest.update(payload)
        manifest.append({
            "name": name,
            "bytes": len(payload),
            "sha256": sha256_bytes(payload),
        })
    return digest.hexdigest(), manifest


def unset_paths(value: Any, prefix: str = "") -> list[str]:
    paths: list[str] = []
    if value == "UNSET":
        return [prefix or "<root>"]
    if isinstance(value, dict):
        for key, child in value.items():
            if key == "unresolved_fields":
                continue
            child_prefix = f"{prefix}.{key}" if prefix else key
            paths.extend(unset_paths(child, child_prefix))
    elif isinstance(value, list):
        for index, child in enumerate(value):
            paths.extend(unset_paths(child, f"{prefix}[{index}]"))
    return paths


def resolve_repo_path(path_text: str) -> Path:
    path = Path(path_text)
    return path if path.is_absolute() else ROOT / path


def validate_paired_replicates(config: dict[str, Any]) -> list[int]:
    replicates = config.get("randomization", {}).get("paired_replicates")
    require(
        isinstance(replicates, list)
        and all(type(item) is int for item in replicates)
        and replicates == [0, 1, 2, 3, 4],
        "randomization.paired_replicates must equal the ordered integer list "
        "[0, 1, 2, 3, 4]",
    )
    return replicates


def validate_method_amendment(
    config: dict[str, Any], *, require_hashes: bool,
    amendment_bytes: bytes | None = None,
    protocol_bytes: bytes | None = None,
    analysis_script_bytes: bytes | None = None,
    analysis_test_bytes: bytes | None = None,
) -> bytes:
    """Bind the result-free fixed-benchmark method amendment to code and protocol."""
    require(config.get("suite_id") == "ABRL-TARGET-DRIFT-V2",
            "method amendment is defined only for target-drift v2")
    path_text = config.get("method_amendment")
    require(path_text == METHOD_AMENDMENT_PATH,
            "method amendment path differs from the frozen pre-execution amendment")
    path = resolve_repo_path(path_text)
    if amendment_bytes is None:
        require(path.is_file() and not path.is_symlink(),
                "method amendment must be a regular unlinked file")
        amendment_bytes = path.read_bytes()
    expected_sha256 = config.get("method_amendment_sha256")
    require(expected_sha256 == METHOD_AMENDMENT_SHA256,
            "method_amendment_sha256 differs from the frozen pre-execution hash")
    if require_hashes:
        require(sha256_bytes(amendment_bytes) == expected_sha256,
                "method amendment bytes differ from the frozen config hash")
    amendment = strict_json_bytes(amendment_bytes, "method amendment")
    require(
        amendment.get("schema_version") == 1
        and amendment.get("suite_id") == config["suite_id"]
        and amendment.get("amendment_id") == METHOD_AMENDMENT_ID
        and amendment.get("status")
        == "hash_bound_pre_execution_method_amendment_results_absent",
        "method amendment identity or result-free status differs",
    )
    timing = amendment.get("timing_and_claim_boundary", {})
    require(
        timing.get("primary_model_outcomes_observed") is False
        and timing.get("external_comparator_outcomes_observed") is False
        and timing.get("provider_calls_for_evaluation_observed") is False
        and timing.get("human_expert_source_review_complete") is False
        and timing.get("amendment_is_evaluation_result") is False,
        "method amendment timing boundary overstates observed results",
    )
    fixed_method = amendment.get("fixed_method", {})
    analysis = config.get("analysis", {})
    require(
        analysis.get("primary_estimand") == fixed_method.get("primary_estimand")
        and analysis.get("primary_pairing_key")
        == fixed_method.get("primary_pairing_key")
        and analysis.get("primary_interval_method_id")
        == fixed_method.get("primary_interval_method_id")
        and analysis.get("primary_interval") == fixed_method.get("primary_interval")
        and analysis.get("primary_success_rule")
        == fixed_method.get("primary_success_rule")
        and analysis.get("primary_sensitivity_analyses")
        == fixed_method.get("primary_sensitivity_analyses")
        and analysis.get("secondary_pairwise_test")
        == fixed_method.get("secondary_pairwise_test")
        and analysis.get("secondary_multiplicity")
        == fixed_method.get("secondary_multiplicity")
        ,
        "execution analysis text differs from the fixed-benchmark amendment",
    )
    bindings = amendment.get("bindings", {})
    protocol_binding = bindings.get("primary_protocol", {})
    script_binding = bindings.get("analysis_script", {})
    test_binding = bindings.get("analysis_tests", {})
    require(
        protocol_binding.get("path") == config.get("protocol")
        and script_binding.get("path") == analysis.get("script")
        and test_binding.get("path") == analysis.get("test_script"),
        "method amendment protocol, analysis-script, or analysis-test path binding differs",
    )
    if protocol_bytes is None:
        protocol_path = resolve_repo_path(config["protocol"])
        require(protocol_path.is_file(), "method amendment protocol binding is missing")
        protocol_bytes = protocol_path.read_bytes()
    if analysis_script_bytes is None:
        script_path = resolve_repo_path(analysis["script"])
        require(script_path.is_file(), "method amendment analysis script is missing")
        analysis_script_bytes = script_path.read_bytes()
    if analysis_test_bytes is None:
        test_path = resolve_repo_path(analysis["test_script"])
        require(test_path.is_file(), "method amendment analysis test is missing")
        analysis_test_bytes = test_path.read_bytes()
    require(protocol_binding.get("sha256") == sha256_bytes(protocol_bytes),
            "method amendment protocol-byte binding differs")
    require(script_binding.get("sha256") == sha256_bytes(analysis_script_bytes),
            "method amendment analysis-script-byte binding differs")
    require(test_binding.get("sha256") == sha256_bytes(analysis_test_bytes),
            "method amendment analysis-test-byte binding differs")
    configured_script_hash = analysis.get("script_sha256")
    if configured_script_hash != "UNSET":
        require(configured_script_hash == script_binding.get("sha256"),
                "execution config and method amendment name different analysis code")
    require(analysis.get("test_script_sha256") == test_binding.get("sha256"),
            "execution config and method amendment name different analysis tests")
    return amendment_bytes


def packed_method_amendment_bytes(
    pack_dir: Path, config: dict[str, Any],
    execution_code_bytes: dict[str, bytes],
) -> bytes:
    path = pack_dir / "method-amendment.json"
    require(path.is_file() and not path.is_symlink(),
            "sealed pack method amendment is missing or linked")
    require(
        "analyze_target_drift_execution.py" in execution_code_bytes
        and "test_target_drift_analysis.py" in execution_code_bytes,
        "sealed pack omits analysis code bound by the method amendment",
    )
    return validate_method_amendment(
        config,
        require_hashes=True,
        amendment_bytes=path.read_bytes(),
        protocol_bytes=(pack_dir / "protocol.json").read_bytes(),
        analysis_script_bytes=execution_code_bytes[
            "analyze_target_drift_execution.py"
        ],
        analysis_test_bytes=execution_code_bytes["test_target_drift_analysis.py"],
    )


def plain_unlinked_directory(path: Path, label: str) -> Path:
    require(path.is_absolute() and path.exists() and not path.is_symlink(),
            f"{label} must be an existing absolute nonlink directory")
    info = path.lstat()
    reparse = bool(getattr(info, "st_file_attributes", 0) & 0x400)
    require(stat.S_ISDIR(info.st_mode) and not reparse,
            f"{label} must be a plain directory")
    return path


def require_sha256(value: Any, label: str) -> str:
    require(isinstance(value, str) and re.fullmatch(r"[0-9a-f]{64}", value) is not None,
            f"{label} must be a lowercase SHA-256")
    return value


def parse_utc_seconds(value: Any, label: str) -> datetime:
    require(isinstance(value, str) and re.fullmatch(
        r"\d{4}-\d{2}-\d{2}T\d{2}:\d{2}:\d{2}Z", value
    ) is not None, f"{label} must be UTC RFC3339 seconds ending in Z")
    try:
        return datetime.strptime(value, "%Y-%m-%dT%H:%M:%SZ").replace(
            tzinfo=timezone.utc
        )
    except ValueError:
        require(False, f"{label} is not a valid UTC timestamp")
    raise AssertionError("unreachable")


def validate_external_trust_anchor_contract(contract: dict[str, Any]) -> None:
    expected_top = {
        "schema_version", "contract_id", "status", "required_anchor_status",
        "required_public_repository_url_policy", "required_public_ref",
        "required_anchor_claim_boundary", "claim_boundary",
        "required_anchor_fields", "anchor_template",
    }
    require(set(contract) == expected_top,
            "external signer trust-anchor contract schema differs")
    boundary = contract.get("claim_boundary")
    require(
        contract.get("schema_version") == 1
        and contract.get("contract_id") == TRUST_ANCHOR_CONTRACT_ID
        and contract.get("status")
        == "contract_frozen_real_anchor_unset_production_ineligible"
        and contract.get("required_anchor_status")
        == TRUST_ANCHOR_PRODUCTION_STATUS
        and contract.get("required_public_repository_url_policy")
        == TRUST_ANCHOR_PUBLIC_REPOSITORY_URL_POLICY
        and contract.get("required_public_ref") == TRUST_ANCHOR_PUBLIC_REF
        and contract.get("required_anchor_claim_boundary")
        == TRUST_ANCHOR_CLAIM_BOUNDARY
        and boundary == TRUST_ANCHOR_CONTRACT_BOUNDARY,
        "external signer trust-anchor contract identity or claim boundary differs",
    )
    require(set(contract["required_anchor_fields"]) == TRUST_ANCHOR_REQUIRED_FIELDS
            and len(contract["required_anchor_fields"])
            == len(TRUST_ANCHOR_REQUIRED_FIELDS),
            "external signer trust-anchor required-field set differs")
    template = contract.get("anchor_template")
    require(isinstance(template, dict) and set(template) == TRUST_ANCHOR_REQUIRED_FIELDS,
            "external signer trust-anchor template schema differs")
    require(
        template.get("schema_version") == 1
        and template.get("contract_id") == TRUST_ANCHOR_CONTRACT_ID
        and all(
            value == "UNSET"
            for key, value in template.items()
            if key not in {"schema_version", "contract_id"}
        ),
        "external signer trust-anchor template must contain no real anchor material",
    )


def git_command(
    args: list[str], *, cwd: Path, input_bytes: bytes | None = None,
    label: str,
) -> bytes:
    executable = shutil.which("git")
    require(executable is not None, "Git is required for trust-anchor validation")
    process = subprocess.run(
        [executable, *args], cwd=cwd, input=input_bytes,
        stdout=subprocess.PIPE, stderr=subprocess.STDOUT, check=False,
    )
    require(process.returncode == 0, f"{label} failed")
    return process.stdout


def validate_git_object_proof(
    proof_bytes: bytes, anchor: dict[str, Any], anchor_bytes: bytes,
    orchestrator_commit: str,
) -> None:
    """Verify commit ancestry and path membership using only packed Git objects."""
    anchor_commit = anchor["anchor_git_commit"]
    with tempfile.TemporaryDirectory(prefix="abrl-anchor-proof-") as directory:
        repository = Path(directory) / "proof.git"
        git_command(["init", "--bare", "-q", str(repository)], cwd=Path(directory),
                    label="initializing isolated trust-anchor proof repository")
        pack_root = repository / "objects" / "pack"
        pack_root.mkdir(parents=True, exist_ok=True)
        pack_path = pack_root / "anchor-proof.pack"
        pack_path.write_bytes(proof_bytes)
        # index-pack verifies the pack checksum and every object id.  We omit
        # unrelated commit trees intentionally and enforce the exact admissible
        # object inventory below, so repository-wide fsck/--strict is inapplicable.
        git_command(["index-pack", str(pack_path)], cwd=repository,
                    label="indexing trust-anchor Git object proof")
        index_path = pack_path.with_suffix(".idx")
        require(index_path.is_file(), "trust-anchor Git object proof index is missing")
        inventory_output = git_command(
            ["verify-pack", "-v", str(index_path)], cwd=repository,
            label="inventorying trust-anchor Git object proof",
        ).decode("utf-8", errors="strict")
        inventory: dict[str, str] = {}
        for line in inventory_output.splitlines():
            fields = line.split()
            if (len(fields) >= 5 and re.fullmatch(r"[0-9a-f]{40}", fields[0])
                    and fields[1] in {"commit", "tree", "blob", "tag"}):
                require(fields[0] not in inventory,
                        "trust-anchor Git object proof repeats an object")
                inventory[fields[0]] = fields[1]
        require(inventory, "trust-anchor Git object proof contains no objects")
        require(anchor_commit in inventory and inventory[anchor_commit] == "commit",
                "trust-anchor proof omits the anchor commit")
        require(orchestrator_commit in inventory
                and inventory[orchestrator_commit] == "commit",
                "trust-anchor proof omits the execution commit")
        require("tag" not in set(inventory.values()),
                "trust-anchor proof must not include tag objects")

        commit_parents: dict[str, list[str]] = {}
        commit_trees: dict[str, str] = {}
        for object_id, object_type in inventory.items():
            if object_type != "commit":
                continue
            raw = git_command(["cat-file", "commit", object_id], cwd=repository,
                              label="reading trust-anchor proof commit")
            header = raw.split(b"\n\n", 1)[0].decode("utf-8", errors="strict")
            parents: list[str] = []
            tree_id = ""
            for line in header.splitlines():
                if line.startswith("tree "):
                    tree_id = line[5:]
                elif line.startswith("parent "):
                    parents.append(line[7:])
            require(re.fullmatch(r"[0-9a-f]{40}", tree_id) is not None,
                    "trust-anchor proof commit has no canonical tree id")
            require(all(re.fullmatch(r"[0-9a-f]{40}", item) for item in parents),
                    "trust-anchor proof commit has a malformed parent id")
            commit_parents[object_id] = parents
            commit_trees[object_id] = tree_id

        reachable: set[str] = set()
        frontier = [orchestrator_commit]
        while frontier:
            current = frontier.pop()
            if current in reachable:
                continue
            require(current in commit_parents,
                    "trust-anchor proof ancestry has a missing parent commit")
            reachable.add(current)
            frontier.extend(commit_parents[current])
        require(anchor_commit in reachable and anchor_commit != orchestrator_commit,
                "trust-anchor commit must be a strict ancestor of execution commit")
        require(
            {item for item, kind in inventory.items() if kind == "commit"} == reachable,
            "trust-anchor proof contains unrelated or unreachable commit objects",
        )

        repository_path = PurePosixPath(anchor["anchor_repository_path"])
        tree_id = commit_trees[anchor_commit]
        required_noncommit: set[str] = {tree_id}
        parts = repository_path.parts
        require(bool(parts), "trust-anchor repository path is empty")
        for index, part in enumerate(parts):
            output = git_command(
                ["ls-tree", "-z", tree_id, "--", part], cwd=repository,
                label="walking trust-anchor proof tree",
            )
            records = [item for item in output.split(b"\0") if item]
            require(len(records) == 1,
                    "trust-anchor proof path is absent or ambiguous")
            metadata, name = records[0].split(b"\t", 1)
            fields = metadata.decode("ascii").split()
            require(name.decode("utf-8", errors="strict") == part
                    and len(fields) == 3,
                    "trust-anchor proof tree entry differs")
            _, object_type, next_id = fields
            require(re.fullmatch(r"[0-9a-f]{40}", next_id) is not None,
                    "trust-anchor proof tree entry has a malformed object id")
            required_noncommit.add(next_id)
            if index < len(parts) - 1:
                require(object_type == "tree",
                        "trust-anchor proof path parent is not a tree")
                tree_id = next_id
            else:
                require(object_type == "blob",
                        "trust-anchor proof path target is not a blob")
                blob = git_command(["cat-file", "blob", next_id], cwd=repository,
                                   label="reading trust-anchor proof blob")
                require(blob == anchor_bytes,
                        "trust-anchor proof blob differs from packed anchor bytes")
        actual_noncommit = {
            item for item, kind in inventory.items() if kind != "commit"
        }
        require(actual_noncommit == required_noncommit,
                "trust-anchor proof contains unrelated tree or blob objects")


def validate_live_git_anchor(
    anchor: dict[str, Any], anchor_bytes: bytes, orchestrator_commit: str,
) -> None:
    repository_path = anchor["anchor_repository_path"]
    relative = Path(repository_path)
    require(not relative.is_absolute()
            and PurePosixPath(repository_path).as_posix() == repository_path
            and all(part not in {"", ".", ".."}
                    for part in PurePosixPath(repository_path).parts),
            "trust-anchor repository path must be canonical repository-relative POSIX")
    current_path = ROOT.resolve()
    for index, part in enumerate(PurePosixPath(repository_path).parts):
        current_path = current_path / part
        require(current_path.exists() and not current_path.is_symlink(),
                "tracked trust-anchor path is missing or crosses a symlink")
        info = current_path.lstat()
        require(not bool(getattr(info, "st_file_attributes", 0) & 0x400),
                "tracked trust-anchor path crosses a reparse point")
        if index < len(PurePosixPath(repository_path).parts) - 1:
            require(stat.S_ISDIR(info.st_mode),
                    "tracked trust-anchor parent is not a directory")
        else:
            require(stat.S_ISREG(info.st_mode) and info.st_nlink == 1,
                    "tracked trust-anchor must be one unlinked regular file")
    anchor_commit = anchor["anchor_git_commit"]
    origin_url = git_command(["remote", "get-url", "origin"], cwd=ROOT,
                             label="resolving public trust-anchor remote").decode(
                                 "utf-8", errors="strict"
                             ).strip()
    require(origin_url == anchor["anchor_public_repository_url"],
            "trust-anchor origin differs from the preregistered public repository")
    remote_line = git_command(
        ["ls-remote", "--exit-code", "origin", TRUST_ANCHOR_PUBLIC_REF], cwd=ROOT,
        label="checking the live public trust-anchor ref",
    ).decode("ascii", errors="strict").strip().splitlines()
    require(len(remote_line) == 1,
            "public trust-anchor ref lookup is absent or ambiguous")
    remote_fields = remote_line[0].split()
    require(len(remote_fields) == 2
            and re.fullmatch(r"[0-9a-f]{40}", remote_fields[0]) is not None
            and remote_fields[1] == TRUST_ANCHOR_PUBLIC_REF,
            "public trust-anchor ref lookup is malformed")
    public_tip = remote_fields[0]
    git_command(["cat-file", "-e", f"{anchor_commit}^{{commit}}"], cwd=ROOT,
                label="resolving trust-anchor commit")
    git_command(["cat-file", "-e", f"{orchestrator_commit}^{{commit}}"], cwd=ROOT,
                label="resolving execution commit")
    require(anchor_commit != orchestrator_commit,
            "trust-anchor commit must predate the execution commit")
    git_command(["merge-base", "--is-ancestor", anchor_commit, orchestrator_commit],
                cwd=ROOT, label="checking trust-anchor commit ancestry")
    git_command(["cat-file", "-e", f"{public_tip}^{{commit}}"], cwd=ROOT,
                label="resolving live public trust-anchor tip")
    git_command(["merge-base", "--is-ancestor", anchor_commit, public_tip], cwd=ROOT,
                label="checking anchor reachability from the live public ref")
    git_command(["ls-files", "--error-unmatch", "--", repository_path], cwd=ROOT,
                label="checking tracked trust-anchor path")
    frozen_bytes = git_command(
        ["show", f"{anchor_commit}:{repository_path}"], cwd=ROOT,
        label="reading trust-anchor bytes at the frozen commit",
    )
    require(frozen_bytes == anchor_bytes,
            "working trust-anchor bytes differ from the named frozen commit")
    commit_seconds_text = git_command(
        ["show", "-s", "--format=%ct", anchor_commit], cwd=ROOT,
        label="reading trust-anchor commit timestamp",
    ).decode("ascii").strip()
    require(commit_seconds_text.isdigit(),
            "trust-anchor Git commit timestamp is malformed")
    commit_time = datetime.fromtimestamp(int(commit_seconds_text), tz=timezone.utc)
    registered_at = parse_utc_seconds(
        anchor["anchor_registered_at_utc"], "anchor.anchor_registered_at_utc"
    )
    require(commit_time <= registered_at + timedelta(minutes=5),
            "trust-anchor Git timestamp is later than its registration record")


def validate_external_trust_anchor(
    *, contract_bytes: bytes, anchor_bytes: bytes, proof_bytes: bytes,
    registry_bytes: bytes, allowed_signers_bytes_value: bytes,
    receipt_bytes: bytes, orchestrator_commit: str,
    source_anchor_path: str | None,
    allow_excluded_unanchored_fixture: bool,
) -> bool:
    """Return True only for a prior public Git anchor; fixtures stay ineligible."""
    contract = strict_json_bytes(contract_bytes, "external trust-anchor contract")
    validate_external_trust_anchor_contract(contract)
    anchor = strict_json_bytes(anchor_bytes, "external trust anchor")
    registry = strict_json_bytes(registry_bytes, "external role registry")
    receipt = strict_json_bytes(receipt_bytes, "external verifier receipt")
    require(set(anchor) == TRUST_ANCHOR_REQUIRED_FIELDS,
            "external trust-anchor schema differs")
    require(anchor.get("schema_version") == 1
            and anchor.get("contract_id") == TRUST_ANCHOR_CONTRACT_ID,
            "external trust-anchor identity differs")
    require(isinstance(anchor.get("anchor_id"), str)
            and anchor["anchor_id"] not in {"", "UNSET"},
            "external trust-anchor id is missing")
    require(
        anchor.get("review_started_before_anchor") is False
        and anchor.get("evaluation_outcomes_observed_before_anchor") is False
        and anchor.get("benchmark_execution_complete_before_anchor") is False,
        "external trust anchor is not preregistered and result-free",
    )
    require(anchor.get("claim_boundary") == TRUST_ANCHOR_CLAIM_BOUNDARY,
            "external trust-anchor claim boundary differs")
    require_sha256(anchor.get("role_registry_bytes_sha256"),
                   "anchor.role_registry_bytes_sha256")
    require_sha256(anchor.get("role_registry_canonical_sha256"),
                   "anchor.role_registry_canonical_sha256")
    require_sha256(anchor.get("allowed_signers_bytes_sha256"),
                   "anchor.allowed_signers_bytes_sha256")
    require_sha256(anchor.get("public_escrow_receipt_sha256"),
                   "anchor.public_escrow_receipt_sha256")
    require(anchor["role_registry_bytes_sha256"] == sha256_bytes(registry_bytes),
            "trust anchor does not bind exact role-registry bytes")
    require(anchor["role_registry_canonical_sha256"]
            == sha256_bytes(external_contract_review.canonical_bytes(registry)),
            "trust anchor does not bind canonical role-registry bytes")
    require(anchor["allowed_signers_bytes_sha256"]
            == sha256_bytes(allowed_signers_bytes_value),
            "trust anchor does not bind allowed-signers bytes")
    signers = registry.get("signers")
    require(isinstance(signers, list), "external role registry signers are missing")
    verifier_entries = [
        item for item in signers
        if isinstance(item, dict) and item.get("slot") == "external_verifier"
    ]
    require(len(verifier_entries) == 1,
            "external role registry must contain one external verifier")
    verifier = verifier_entries[0]
    require(
        anchor["external_verifier_principal"] == verifier.get("principal")
        and anchor["external_verifier_public_key_fingerprint"]
        == verifier.get("public_key_fingerprint"),
        "trust anchor external-verifier identity or fingerprint differs",
    )
    require(
        anchor["public_escrow_receipt_locator"]
        == receipt.get("public_escrow_reference")
        and anchor["public_escrow_receipt_sha256"]
        == receipt.get("public_escrow_receipt_sha256"),
        "trust anchor public escrow locator or hash differs",
    )
    registered_at = parse_utc_seconds(
        anchor["anchor_registered_at_utc"], "anchor.anchor_registered_at_utc"
    )
    require(anchor["anchor_registered_at_utc"] == registry.get("registered_at_utc"),
            "trust-anchor and role-registry registration times differ")
    verified_at = parse_utc_seconds(
        receipt.get("verified_at_utc"), "receipt.verified_at_utc"
    )
    require(registered_at < verified_at,
            "trust anchor must predate external verification")

    if anchor.get("status") == TRUST_ANCHOR_EXCLUDED_STATUS:
        require(allow_excluded_unanchored_fixture,
                "excluded unanchored signer fixture is not production evidence")
        require(anchor.get("anchor_git_commit") == "UNSET"
                and anchor.get("anchor_repository_path") == "UNSET"
                and anchor.get("anchor_public_repository_url") == "UNSET"
                and anchor.get("anchor_public_ref") == "UNSET"
                and anchor.get("anchor_public_commit_locator") == "UNSET"
                and proof_bytes == TRUST_ANCHOR_EXCLUDED_PROOF,
                "excluded trust-anchor fixture must carry no Git provenance claim")
        return False

    require(anchor.get("status") == TRUST_ANCHOR_PRODUCTION_STATUS,
            "external signer trust anchor has no production-frozen status")
    require(re.fullmatch(r"[0-9a-f]{40}", anchor.get("anchor_git_commit", ""))
            is not None, "trust-anchor commit must be a lowercase full Git commit")
    require(re.fullmatch(r"[0-9a-f]{40}", orchestrator_commit or "") is not None,
            "execution commit must be a lowercase full Git commit")
    public_repository = anchor.get("anchor_public_repository_url")
    require(
        isinstance(public_repository, str)
        and re.fullmatch(r"https://github\.com/[A-Za-z0-9_.-]+/[A-Za-z0-9_.-]+\.git",
                         public_repository) is not None
        and "@" not in public_repository
        and anchor.get("anchor_public_ref") == TRUST_ANCHOR_PUBLIC_REF
        and anchor.get("anchor_public_commit_locator")
        == public_repository[:-4] + "/commit/" + anchor["anchor_git_commit"],
        "trust-anchor public repository, ref, or commit locator differs",
    )
    require(source_anchor_path is None or source_anchor_path == anchor["anchor_repository_path"],
            "configured trust-anchor path differs from its tracked repository path")
    repository_path = anchor["anchor_repository_path"]
    require(
        isinstance(repository_path, str)
        and repository_path == PurePosixPath(repository_path).as_posix()
        and not PurePosixPath(repository_path).is_absolute()
        and bool(PurePosixPath(repository_path).parts)
        and all(part not in {"", ".", ".."}
                for part in PurePosixPath(repository_path).parts),
        "trust-anchor repository path must be canonical repository-relative POSIX",
    )
    validate_git_object_proof(proof_bytes, anchor, anchor_bytes, orchestrator_commit)
    if source_anchor_path is not None:
        validate_live_git_anchor(anchor, anchor_bytes, orchestrator_commit)
    return True


def validate_human_source_contract_config_identity(entry: dict[str, Any]) -> None:
    require(set(entry) == HUMAN_REVIEW_CONFIG_FIELDS,
            "human-review execution-config schema differs")
    expected_paths = {
        "protocol": "evaluation/target-drift-v2/human-source-contract-review-protocol.json",
        "self_attested_prepare_script":
            "tools/prepare_target_drift_human_contract_review.py",
        "self_attested_validator_script":
            "tools/validate_target_drift_human_contract_review.py",
        "self_attested_validator_test":
            "tools/test_target_drift_human_contract_review.py",
        "execution_finalizer": "tools/finalize_target_drift_config.py",
        "external_protocol": (
            "evaluation/target-drift-v2/"
            "human-source-contract-external-verification-protocol.json"
        ),
        "external_trust_anchor_contract": (
            "evaluation/target-drift-v2/"
            "human-source-contract-external-trust-anchor-contract.json"
        ),
        "external_validator_script":
            "tools/validate_target_drift_human_contract_external_verification.py",
        "external_validator_test":
            "tools/test_target_drift_human_contract_external_verification.py",
    }
    require(all(entry.get(field) == value for field, value in expected_paths.items()),
            "human-review public protocol or validator-code path differs")
    require(
        entry.get("required_self_attested_status")
        == human_contract_review.SELF_ATTESTED_STATUS
        and entry.get("required_external_status")
        == external_contract_review.COMPLETED_STATUS
        and entry.get("required_external_trust_anchor_status")
        == "public_pre_outcome_signer_registry_anchor_frozen"
        and entry.get("combined_prerequisite_status")
        == "human_source_contract_prerequisite_satisfied"
        and entry.get("evaluation_outcomes_observed_before_validation") is False,
        "human-review combined gate identity or result-free boundary differs",
    )


def validate_public_human_review_protocols(entry: dict[str, Any]) -> dict[str, bytes]:
    self_protocol_path = regular_unlinked_file(
        resolve_repo_path(entry["protocol"]), "self-attested human-review protocol",
        require_executable=False,
    )
    external_protocol_path = regular_unlinked_file(
        resolve_repo_path(entry["external_protocol"]), "external human-review protocol",
        require_executable=False,
    )
    trust_anchor_contract_path = regular_unlinked_file(
        resolve_repo_path(entry["external_trust_anchor_contract"]),
        "external signer trust-anchor contract", require_executable=False,
    )
    # These calls use duplicate-key-rejecting loaders and enforce the frozen,
    # result-free protocol identities rather than trusting config labels.
    human_contract_review.prepare.validate_inputs(protocol_path=self_protocol_path)
    external_contract_review.validate_protocol(
        external_contract_review.load(external_protocol_path)
    )
    validate_external_trust_anchor_contract(
        strict_json_bytes(
            trust_anchor_contract_path.read_bytes(),
            "external signer trust-anchor contract",
        )
    )
    return {
        "self-review-protocol.json": self_protocol_path.read_bytes(),
        "external-verification-protocol.json": external_protocol_path.read_bytes(),
        "external-trust-anchor-contract.json": trust_anchor_contract_path.read_bytes(),
    }


def require_packed_human_paths(config: dict[str, Any]) -> None:
    entry = config["human_source_contract_validation"]
    require(entry.get("review_packet") == HUMAN_REVIEW_SEALED_ROOT,
            "packed human-review packet path is not the sealed logical path")
    for path_field, _, filename in HUMAN_REVIEW_FILE_BINDINGS:
        require(
            entry.get(path_field) == f"{HUMAN_REVIEW_SEALED_ROOT}/{filename}",
            f"packed human-review path is not sealed for {path_field}",
        )


def validate_packed_human_source_contract_review(
    pack_dir: Path, config: dict[str, Any], *, require_combined_record: bool = True,
    allow_excluded_unanchored_fixture: bool = False,
) -> dict[str, bytes]:
    """Rebuild both review layers and the Git proof from sealed pack bytes."""
    pack_dir = plain_unlinked_directory(
        pack_dir.absolute(), "sealed human-review pack root"
    )
    entry = config.get("human_source_contract_validation")
    require(isinstance(entry, dict),
            "v2 config must define human_source_contract_validation")
    validate_human_source_contract_config_identity({
        **entry,
        # Public-path identity is recorded by hashes in packed configs; restore
        # only the fixed public code/protocol locators for this identity check.
        "protocol": "evaluation/target-drift-v2/human-source-contract-review-protocol.json",
        "external_protocol": (
            "evaluation/target-drift-v2/"
            "human-source-contract-external-verification-protocol.json"
        ),
        "external_trust_anchor_contract": (
            "evaluation/target-drift-v2/"
            "human-source-contract-external-trust-anchor-contract.json"
        ),
    })
    require_packed_human_paths(config)
    review_root = plain_unlinked_directory(
        (pack_dir / "human_source_contract_review").absolute(),
        "sealed human-review evidence root",
    )
    children = list(review_root.iterdir())
    require(all(path.is_file() and not path.is_symlink() for path in children),
            "sealed human-review evidence contains a non-file or linked child")
    require({path.name for path in children} == HUMAN_REVIEW_EXPECTED_FILES,
            "sealed human source-contract review file set differs")
    paths = {
        name: regular_unlinked_file(
            review_root / name, f"sealed human-review {name}", require_executable=False
        )
        for name in HUMAN_REVIEW_EXPECTED_FILES
    }
    evidence = {name: path.read_bytes() for name, path in paths.items()}
    for _, hash_field, filename in HUMAN_REVIEW_FILE_BINDINGS:
        require(entry.get(hash_field) == sha256_bytes(evidence[filename]),
                f"sealed human-review hash mismatch for {filename}")
    require(
        entry.get("review_packet_manifest_sha256")
        == sha256_bytes(evidence["packet-manifest.json"]),
        "sealed human-review packet-manifest hash differs",
    )
    challenge_path = regular_unlinked_file(
        (pack_dir / "operator_challenges.json").absolute(),
        "sealed operator challenges", require_executable=False,
    )
    paired_path = regular_unlinked_file(
        (pack_dir / "paired_requirements.json").absolute(),
        "sealed paired requirements", require_executable=False,
    )
    rebuilt_self = human_contract_review.validate(
        review_root,
        paths["reviewer-a.json"], paths["reviewer-b.json"],
        paths["adjudication.json"],
        protocol_path=paths["self-review-protocol.json"],
        challenge_path=challenge_path, paired_path=paired_path,
    )
    supplied_self = human_contract_review.load(paths["self-attested-completion.json"])
    require(supplied_self == rebuilt_self,
            "self-attested completion differs from rebuilt packed review evidence")
    require(
        rebuilt_self.get("status") == entry["required_self_attested_status"]
        and rebuilt_self.get("benchmark_amendment_required") is False
        and rebuilt_self.get("benchmark_contract_ready_after_external_verification") is True
        and rebuilt_self.get("machine_checked_all_case_contracts_match_frozen_benchmark")
        is True
        and rebuilt_self.get("external_identity_qualification_verification_required") is True
        and rebuilt_self.get("independent_human_expert_validation_complete") is False
        and rebuilt_self.get("production_execution_eligible") is False
        and rebuilt_self.get("evaluation_outcomes_observed") is False
        and rebuilt_self.get("benchmark_execution_complete") is False,
        "self-attested review is amended, overstated, post-outcome, or otherwise ineligible",
    )
    rebuilt_external = external_contract_review.validate(
        paths["external-verification-protocol.json"], review_root,
        paths["reviewer-a.json"], paths["reviewer-a.sig"],
        paths["reviewer-b.json"], paths["reviewer-b.sig"],
        paths["adjudication.json"], paths["adjudication.sig"],
        paths["self-attested-completion.json"], paths["role-registry.json"],
        paths["allowed_signers"], paths["external-receipt.json"],
        paths["external-receipt.sig"],
        review_protocol_path=paths["self-review-protocol.json"],
        challenge_path=challenge_path, paired_path=paired_path,
    )
    supplied_external = external_contract_review.load(paths["external-attestation.json"])
    require(supplied_external == rebuilt_external,
            "external attestation differs from rebuilt packed signed evidence")
    require(
        rebuilt_external.get("status") == entry["required_external_status"]
        and rebuilt_external.get("cryptographically_proven_human") is False
        and rebuilt_external.get("production_execution_eligible") is False
        and rebuilt_external.get("production_execution_eligible_from_this_layer_alone")
        is False
        and rebuilt_external.get("production_trust_anchor_verified") is False
        and rebuilt_external.get("evaluation_outcomes_observed") is False
        and rebuilt_external.get("benchmark_execution_complete") is False,
        "external signed attestation overstates its evidence or is post-outcome",
    )
    production_anchor = validate_external_trust_anchor(
        contract_bytes=evidence["external-trust-anchor-contract.json"],
        anchor_bytes=evidence["external-trust-anchor.json"],
        proof_bytes=evidence["external-trust-anchor-git-object-proof.pack"],
        registry_bytes=evidence["role-registry.json"],
        allowed_signers_bytes_value=evidence["allowed_signers"],
        receipt_bytes=evidence["external-receipt.json"],
        orchestrator_commit=config.get("orchestrator_commit", ""),
        source_anchor_path=None,
        allow_excluded_unanchored_fixture=allow_excluded_unanchored_fixture,
    )
    if production_anchor and require_combined_record:
        require(entry.get("combined_prerequisite_satisfied") is True,
                "execution layer did not record the combined human prerequisite")
    else:
        require(entry.get("combined_prerequisite_satisfied") is False
                or entry.get("combined_prerequisite_satisfied") == "UNSET",
                "combined human prerequisite was claimed before both layers validated")
    return evidence


def validate_human_source_contract_review(
    config: dict[str, Any], *, require_completion: bool,
    require_combined_record: bool = True,
    allow_excluded_unanchored_fixture: bool = False,
) -> dict[str, bytes]:
    """Validate both human-review layers and return the exact validated bytes."""
    entry = config.get("human_source_contract_validation")
    require(isinstance(entry, dict),
            "v2 config must define human_source_contract_validation")
    validate_human_source_contract_config_identity(entry)
    public_protocols = validate_public_human_review_protocols(entry)
    if not require_completion:
        evidence_path_fields = ["review_packet"] + [
            item[0] for item in HUMAN_REVIEW_FILE_BINDINGS
            if item[0] not in {
                "protocol", "external_protocol", "external_trust_anchor_contract",
            }
        ]
        require(all(entry.get(field) == "UNSET" for field in evidence_path_fields),
                "unrun template must not prefill human-review evidence paths")
        require(entry.get("combined_prerequisite_satisfied") == "UNSET",
                "unrun template must not claim the combined human prerequisite")
        return public_protocols

    if require_combined_record:
        require(entry.get("combined_prerequisite_satisfied") is True,
                "preseal requires the execution-layer combined human prerequisite")
    else:
        require(entry.get("combined_prerequisite_satisfied") is False
                or entry.get("combined_prerequisite_satisfied") == "UNSET",
                "combined human prerequisite was claimed before both layers validated")
    packet = plain_unlinked_directory(
        resolve_repo_path(entry["review_packet"]), "human-review packet"
    )
    source_paths: dict[str, Path] = {
        "packet-manifest.json": packet / "packet-manifest.json",
        "reviewer-template.json": packet / "reviewer-template.json",
        "adjudication-template.json": packet / "adjudication-template.json",
    }
    for path_field, _, filename in HUMAN_REVIEW_FILE_BINDINGS:
        source_paths[filename] = resolve_repo_path(entry[path_field])
    evidence: dict[str, bytes] = {}
    for name, path in source_paths.items():
        regular = regular_unlinked_file(
            path, f"human-review source {name}", require_executable=False
        )
        evidence[name] = regular.read_bytes()
    for _, hash_field, filename in HUMAN_REVIEW_FILE_BINDINGS:
        require(entry.get(hash_field) == sha256_bytes(evidence[filename]),
                f"human-review source hash mismatch for {filename}")
    require(
        entry.get("review_packet_manifest_sha256")
        == sha256_bytes(evidence["packet-manifest.json"]),
        "human-review packet-manifest hash differs",
    )
    production_anchor = validate_external_trust_anchor(
        contract_bytes=evidence["external-trust-anchor-contract.json"],
        anchor_bytes=evidence["external-trust-anchor.json"],
        proof_bytes=evidence["external-trust-anchor-git-object-proof.pack"],
        registry_bytes=evidence["role-registry.json"],
        allowed_signers_bytes_value=evidence["allowed_signers"],
        receipt_bytes=evidence["external-receipt.json"],
        orchestrator_commit=config.get("orchestrator_commit", ""),
        source_anchor_path=entry["external_trust_anchor"],
        allow_excluded_unanchored_fixture=allow_excluded_unanchored_fixture,
    )
    if require_combined_record:
        require(production_anchor,
                "combined human prerequisite requires a prior public Git trust anchor")

    # Validate an immutable staged snapshot. The returned bytes are exactly the
    # bytes that both validators consumed, closing the source-path TOCTOU gap.
    with tempfile.TemporaryDirectory(prefix="abrl-human-review-snapshot-") as directory:
        staged_pack = Path(directory)
        staged_review = staged_pack / "human_source_contract_review"
        staged_review.mkdir()
        for name, payload in evidence.items():
            (staged_review / name).write_bytes(payload)
        challenge_path = regular_unlinked_file(
            resolve_repo_path(config["challenge_manifest"]),
            "human-review frozen challenge manifest", require_executable=False,
        )
        paired_path = regular_unlinked_file(
            resolve_repo_path(config["paired_requirements"]),
            "human-review frozen paired requirements", require_executable=False,
        )
        (staged_pack / "operator_challenges.json").write_bytes(challenge_path.read_bytes())
        (staged_pack / "paired_requirements.json").write_bytes(paired_path.read_bytes())
        packed_config = sealed_config_for_pack(config)
        validated = validate_packed_human_source_contract_review(
            staged_pack, packed_config,
            require_combined_record=require_combined_record,
            allow_excluded_unanchored_fixture=allow_excluded_unanchored_fixture,
        )
        require(validated == evidence,
                "staged human-review evidence changed during validation")
    return evidence


def adapter_entrypoint_path(config: dict[str, Any]) -> Path:
    text = config["execution_adapter"]["entrypoint_path"]
    require(isinstance(text, str) and text and text != "UNSET",
            "execution adapter entrypoint path is unresolved")
    relative = Path(text)
    require(not relative.is_absolute(),
            "execution adapter entrypoint must be a repository-relative path")
    root = ROOT.resolve()
    require(relative.parts and all(part not in {"", ".", ".."} for part in relative.parts),
            "execution adapter entrypoint contains a traversal component")
    current = root
    for index, part in enumerate(relative.parts):
        current = current / part
        require(current.exists() and not current.is_symlink(),
                "execution adapter entrypoint path is missing or linked")
        info = current.lstat()
        reparse = bool(getattr(info, "st_file_attributes", 0) & 0x400)
        require(not reparse, "execution adapter entrypoint crosses a reparse point")
        if index < len(relative.parts) - 1:
            require(stat.S_ISDIR(info.st_mode),
                    "execution adapter entrypoint parent is not a directory")
        else:
            require(stat.S_ISREG(info.st_mode) and info.st_nlink == 1,
                    "execution adapter entrypoint must be one unlinked regular file")
    resolved = current.resolve()
    try:
        resolved.relative_to(root)
    except ValueError:
        require(False, "execution adapter entrypoint escapes the repository")
    return resolved


def regular_unlinked_file(
    path: Path, label: str, *, require_executable: bool = True,
) -> Path:
    require(path.is_absolute() and path.exists() and not path.is_symlink(),
            f"{label} must be an existing absolute nonlink path")
    info = path.lstat()
    reparse = bool(getattr(info, "st_file_attributes", 0) & 0x400)
    require(stat.S_ISREG(info.st_mode) and not reparse and info.st_nlink == 1,
            f"{label} must be one unlinked regular file")
    if require_executable and os.name != "nt":
        require(os.access(path, os.X_OK), f"{label} is not executable")
    return path


def checker_runtime_config_payload(config: dict[str, Any]) -> dict[str, Any]:
    """Return the complete, non-self-referential checker runtime boundary.

    The isolation report binds this payload rather than a hand-written subset.
    Derived hashes are read from the current files so the payload can be
    computed before preseal fills the corresponding config fields.
    """
    entry = config["posthoc_checker"]
    if entry.get("mode") == "excluded_fixture":
        return {
            "schema_version": 1,
            "suite_id": config["suite_id"],
            "checker_id": entry["checker_id"],
            "checker_version": entry["checker_version"],
            "mode": "excluded_fixture",
            "runtime_id": entry["runtime_id"],
            "runtime_version": entry["runtime_version"],
            "sandbox_command_argv": entry["sandbox_command_argv"],
            "sandbox_cleanup_argv": entry["sandbox_cleanup_argv"],
            "sandbox_inspect_argv": entry["sandbox_inspect_argv"],
            "sandbox_cleanup_by_label_argv": entry["sandbox_cleanup_by_label_argv"],
            "sandbox_inspect_by_label_argv": entry["sandbox_inspect_by_label_argv"],
            "inspect_absent_exit_code": entry["inspect_absent_exit_code"],
            "container_image_digest": entry["container_image_digest"],
            "budgets": entry["budgets"],
            "worker_command_prefix": entry["worker_command_prefix"],
            "cache_prelude_argv": entry["cache_prelude_argv"],
            "driver_sha256": sha256_file(resolve_repo_path(entry["driver_path"])),
            "inner_checker_sha256": sha256_file(
                resolve_repo_path(entry["inner_checker_path"])
            ),
            "contract_sha256": sha256_file(resolve_repo_path(entry["contract"])),
        }
    launcher_path = resolve_repo_path(entry["host_launcher_path"])
    commands = checker_launcher.command_templates(entry, launcher_path)
    code = {
        "driver_sha256": sha256_file(resolve_repo_path(entry["driver_path"])),
        "inner_checker_sha256": sha256_file(
            resolve_repo_path(entry["inner_checker_path"])
        ),
        "isolation_probe_runner_sha256": sha256_file(
            resolve_repo_path(entry["isolation_probe_runner_path"])
        ),
        "contract_sha256": sha256_file(resolve_repo_path(entry["contract"])),
        "host_launcher_sha256": sha256_file(launcher_path),
        "checker_image_recipe_sha256": sha256_file(
            resolve_repo_path(entry["checker_image_recipe"])
        ),
        "checker_image_sbom_sha256": sha256_file(
            resolve_repo_path(entry["checker_image_sbom"])
        ),
        "checker_image_build_input_manifest_sha256": sha256_file(
            resolve_repo_path(entry["checker_image_build_input_manifest"])
        ),
        "checker_cache_manifest_sha256": sha256_file(
            resolve_repo_path(entry["checker_cache_manifest_artifact"])
        ),
        "checker_image_build_log_sha256": sha256_file(
            resolve_repo_path(entry["checker_image_build_log"])
        ),
        "controller_entrypoint_source_sha256": sha256_file(
            resolve_repo_path(entry["controller_entrypoint_source"])
        ),
        "controller_entrypoint_sha256": entry["controller_entrypoint_sha256"],
        "materializer_sha256": sha256_file(resolve_repo_path(
            config["sealed_agent_view"]["materializer"]
        )),
        "run_preparer_sha256": sha256_file(resolve_repo_path(
            config["sealed_agent_view"]["run_preparer"]
        )),
    }
    return {
        "schema_version": 1,
        "suite_id": config["suite_id"],
        "checker_id": entry["checker_id"],
        "checker_version": entry["checker_version"],
        "mode": entry["mode"],
        "runtime_id": entry["runtime_id"],
        "runtime_version": entry["runtime_version"],
        **commands,
        "host_python_executable": entry["host_python_executable"],
        "host_python_executable_sha256": entry["host_python_executable_sha256"],
        "container_runtime_kind": entry["container_runtime_kind"],
        "container_runtime_executable": entry["container_runtime_executable"],
        "container_runtime_executable_sha256": entry[
            "container_runtime_executable_sha256"
        ],
        "runtime_version_output_sha256": entry["runtime_version_output_sha256"],
        "runtime_signature_output_sha256": entry[
            "runtime_signature_output_sha256"
        ],
        "daemon_identity_output_sha256": entry["daemon_identity_output_sha256"],
        "controller_entrypoint": entry["controller_entrypoint"],
        "controller_uid": entry["controller_uid"],
        "worker_uid": entry["worker_uid"],
        "inspect_absent_exit_code": entry["inspect_absent_exit_code"],
        "container_image_digest": entry["container_image_digest"],
        "filesystem_network_process_attestation": entry[
            "filesystem_network_process_attestation"
        ],
        "controller_worker_separation_attestation": entry[
            "controller_worker_separation_attestation"
        ],
        "checker_cache_root": entry["checker_cache_root"],
        "checker_cache_manifest_path": entry["checker_cache_manifest_path"],
        "checker_cache_manifest_sha256": entry["checker_cache_manifest_sha256"],
        "budgets": entry["budgets"],
        "worker_command_prefix": entry["worker_command_prefix"],
        "cache_prelude_argv": entry["cache_prelude_argv"],
        **code,
    }


def checker_runtime_config_sha256(config: dict[str, Any]) -> str:
    return sha256_bytes(canonical_json_bytes(checker_runtime_config_payload(config)))


def rendered_argv_matches_template(template: list[str], rendered: list[str]) -> bool:
    if len(template) != len(rendered):
        return False
    for source, actual in zip(template, rendered):
        pattern = re.escape(source)
        pattern = re.sub(r"\\\{\\\{[A-Z0-9_]+\\\}\\\}", r".+", pattern)
        if re.fullmatch(pattern, actual) is None:
            return False
    return True


def probe_artifact_bytes(root: Path) -> dict[str, bytes]:
    require(root.is_dir(), "checker isolation-probe artifact directory is missing")
    payloads: dict[str, bytes] = {}
    for path in sorted(root.rglob("*")):
        relative = path.relative_to(root).as_posix()
        info = path.lstat()
        reparse = bool(getattr(info, "st_file_attributes", 0) & 0x400)
        require(not path.is_symlink() and not reparse,
                f"checker isolation-probe artifact is linked: {relative}")
        require(path.is_dir() or path.is_file(),
                f"checker isolation-probe artifact is special: {relative}")
        if path.is_file():
            require(info.st_nlink == 1,
                    f"checker isolation-probe artifact is multiply linked: {relative}")
            payloads[relative] = path.read_bytes()
    require(payloads, "checker isolation-probe artifact directory is empty")
    return payloads


def probe_artifact_manifest(payloads: dict[str, bytes]) -> list[dict[str, Any]]:
    return [
        {"path": name, "bytes": len(payload), "sha256": sha256_bytes(payload)}
        for name, payload in sorted(payloads.items())
    ]


def validate_prompt_templates(config: dict[str, Any], require_hashes: bool) -> None:
    require(set(config["conditions"]) == set(CONDITIONS),
            "condition set must remain compile_only, source_aware_blueprint, abrl")
    for condition in CONDITIONS:
        entry = config["conditions"][condition]
        template_path = resolve_repo_path(entry["prompt_template"])
        require(template_path.is_file(), f"missing prompt template for {condition}")
        text = template_path.read_text(encoding="utf-8")
        for placeholder in PLACEHOLDERS:
            require(placeholder in text,
                    f"{condition} prompt is missing placeholder {placeholder}")
        if require_hashes:
            require(entry["prompt_sha256"] == sha256_file(template_path),
                    f"{condition} prompt hash does not match")


def validate_resource_policy(config: dict[str, Any], require_hash: bool) -> dict[str, Any]:
    policy_path = resolve_repo_path(config["resource_policy"])
    require(policy_path.is_file(), "missing resource policy")
    policy = load(policy_path)
    require(policy["suite_id"] == config["suite_id"], "resource policy suite mismatch")
    require(policy["status"] == "policy_frozen_results_absent",
            "resource policy must remain result-free")
    require(set(policy["conditions"]) == set(CONDITIONS),
            "resource policy condition set differs from execution conditions")
    require(policy["common_isolation"]["attestation_required"] is True,
            "resource policy must require an isolation attestation")
    require(policy["conditions"]["compile_only"]["path_mode"] == "allowlist",
            "compile-only repository view must be an allowlist")
    require(policy["conditions"]["source_aware_blueprint"]["path_mode"] == "allowlist",
            "source-aware repository view must be an allowlist")
    for condition in ("compile_only", "source_aware_blueprint"):
        require(policy["conditions"][condition]["repository_paths"]
                == list(checker_image_builder.SOURCE_PATHS),
                f"{condition} base paths differ from the checker-image baseline")
    require(policy["conditions"]["abrl"]["path_mode"] == "denylist",
            "ABRL repository view must be a denylist")
    require("evaluation" in policy["conditions"]["abrl"]["excluded_repository_paths"],
            "ABRL view must exclude the adjudication/evaluation directory")
    if "workspace_base_commit" in config:
        require(policy["workspace_base_commit"] == config["workspace_base_commit"],
                "resource policy workspace base differs from execution config")
    if require_hash:
        require(config["resource_policy_sha256"] == sha256_file(policy_path),
                "resource policy hash does not match")
    return policy


def validate_missing_run_policy(config: dict[str, Any], require_hash: bool) -> dict[str, Any]:
    entry = config["missing_run_policy"]
    policy_path = resolve_repo_path(entry["policy_path"])
    require(policy_path.is_file(), "missing-run policy file is missing")
    policy = load(policy_path)
    policy_id = "complete_450_no_replacement_no_imputation_v1"
    require(policy.get("schema_version") == 1, "missing-run policy schema_version must be 1")
    require(policy.get("suite_id") == config["suite_id"], "missing-run policy suite mismatch")
    require(policy.get("policy_id") == entry.get("policy_id")
            == config["retry_policy"].get("missing_run_policy") == policy_id,
            "missing-run policy ID mismatch")
    require(policy.get("planned_run_count") == 450,
            "missing-run policy must cover exactly 450 planned runs")
    require(policy.get("schedule_order") == "sealed_presentation_order",
            "missing-run policy must use the sealed presentation order")
    require(policy.get("continuation_after_individual_failure")
            == "continue_remaining_preregistered_runs",
            "missing-run policy must continue the preregistered schedule")
    require(policy.get("automatic_retry_after_terminal_state") == "forbidden",
            "missing-run policy must forbid terminal-state retries")
    require(policy.get("replacement_runs") == "forbidden",
            "missing-run policy must forbid replacement runs")
    require(policy.get("outcome_imputation") == "forbidden",
            "missing-run policy must forbid outcome imputation")
    require(policy.get("result_eligible_state") == {
        "status": "checked", "result_eligible": True, "checker_mode": "production",
    }, "missing-run policy result-eligible state differs")
    require(policy.get("primary_analysis_gate")
            == "exactly_450_result_eligible_graded_records_and_zero_missing_runs",
            "missing-run policy has an unsupported analysis gate")
    require(policy.get("incomplete_run_action")
            == "write_hash_bound_completion_ledger_and_refuse_grading_and_inferential_analysis",
            "missing-run policy incomplete-run action differs")
    require(policy.get("incomplete_analysis_output")
            == "missingness_counts_only_no_effect_estimate_interval_pvalue_or_success_claim",
            "missing-run policy incomplete-analysis output differs")
    require(policy.get("missingness_dimensions") == [
        "state_status", "missing_reason", "condition", "requirement_variant",
    ], "missing-run policy missingness dimensions differ")
    require(set(policy.get("terminal_state_categories", {})) == {
        "not_materialized", "prepared_unrun", "terminal_operator_failure",
        "executed_unchecked", "checker_terminal_failure",
        "checked_fixture_nonexperimental", "integrity_failure", "checked",
    }, "missing-run policy terminal-state categories differ")
    builder = resolve_repo_path(entry["completion_ledger_builder"])
    require(builder.is_file(), "completion-ledger builder is missing")
    schedule_runner = resolve_repo_path(entry["schedule_runner"])
    require(schedule_runner.is_file(), "target-drift schedule runner is missing")
    if require_hash:
        require(entry["policy_sha256"] == sha256_file(policy_path),
                "missing-run policy hash does not match")
        require(entry["completion_ledger_builder_sha256"] == sha256_file(builder),
                "completion-ledger builder hash does not match")
        require(entry["schedule_runner_sha256"] == sha256_file(schedule_runner),
                "schedule-runner hash does not match")
    return policy


def validate_paired_requirements(
    config: dict[str, Any], challenges: list[dict[str, Any]] | None = None
) -> dict[str, Any]:
    path = resolve_repo_path(config["paired_requirements"])
    require(path.is_file(), "missing paired-requirement bank")
    payload = load(path)
    require(payload["suite_id"] == config["suite_id"],
            "paired-requirement suite mismatch")
    require(
        payload["status"] == "paired_wording_amended_pre_execution_results_absent",
        "paired-requirement bank must remain result-free and record the amendment",
    )
    template = payload.get("common_template")
    require(isinstance(template, str) and len(template.split()) >= 12,
            "paired requirements need one substantive common template")
    require(template.count("{{FIELD}}") == 1 and template.count("{{VALUE}}") == 1,
            "paired requirement template must contain one FIELD and one VALUE placeholder")
    entries = payload.get("cases")
    require(isinstance(entries, list) and len(entries) == 30,
            "paired-requirement bank must contain thirty cases")
    require(len({entry.get("case_id") for entry in entries}) == 30,
            "paired-requirement case identifiers must be unique")
    forbidden_markers = (
        "source_faithful", "injected_drift", "faithful variant", "drift variant",
        "implement a lean target that preserves this frozen source contract",
    )
    for entry in entries:
        field = entry.get("field")
        require(isinstance(field, str) and field.strip() == field and field,
                f"empty or untrimmed field for {entry.get('case_id')}")
        for variant in ("source_faithful", "injected_drift"):
            value = entry.get(f"{variant}_value")
            require(isinstance(value, str) and value.strip() and value == value.strip(),
                    f"empty or untrimmed {variant} value for {entry.get('case_id')}")
            rendered = render_paired_requirement(template, field, value)
            require(not any(marker in rendered.lower() for marker in forbidden_markers),
                    f"variant-label/style marker leaked for {entry.get('case_id')}")
    if challenges is not None:
        require(
            [entry["case_id"] for entry in entries] == [case["id"] for case in challenges],
            "paired-requirement order/identity differs from frozen challenges",
        )
    return payload


def render_paired_requirement(template: str, field: str, value: str) -> str:
    rendered = template.replace("{{FIELD}}", field).replace("{{VALUE}}", value)
    require("{{" not in rendered and "}}" not in rendered,
            "paired requirement still contains a template placeholder")
    return rendered


def validate_adapter_contract(config: dict[str, Any], require_hash: bool) -> dict[str, Any]:
    entry = config["execution_adapter"]
    path = resolve_repo_path(entry["contract"])
    require(path.is_file(), "missing execution-adapter contract")
    contract = load(path)
    require(contract.get("schema_version") == 3,
            "adapter contract schema must be version 3")
    require(contract["suite_id"] == config["suite_id"], "adapter-contract suite mismatch")
    require(contract["status"] == "interface_frozen_results_absent",
            "adapter contract must remain result-free")
    require(set(contract["request_schema"]["required"]) == {
        "opaque_run_id", "replicate", "agent_mount", "prompt_path", "model",
        "pricing", "budgets", "retry_policy", "result_contract", "provider_runtime",
    }, "adapter request schema differs from the runner request")
    require(set(contract["response_schema"]["usage_fields"]) == {
        "input_tokens", "cached_input_tokens", "cache_write_input_tokens", "output_tokens",
        "reasoning_output_tokens", "tool_calls", "build_attempts",
        "recovery_tool_calls", "infrastructure_retries", "wall_seconds", "cost_usd",
    }, "adapter usage schema differs from the runner accounting")
    require(set(contract["response_schema"]["model_invocation_fields"]) == {
        "attempt", "transport", "observable_id_kind", "observable_id",
        "process_exit_code", "wall_seconds", "usage_observed",
    }, "adapter model-invocation schema differs from the runner accounting")
    command = entry["command_argv"]
    require(isinstance(command, list) and command and all(isinstance(item, str) for item in command),
            "execution adapter command_argv must be a nonempty string list")
    if require_hash:
        require(entry["contract_sha256"] == sha256_file(path),
                "adapter-contract hash does not match")
        entrypoint = adapter_entrypoint_path(config)
        require(entrypoint.is_file() and not entrypoint.is_symlink(),
                "execution adapter entrypoint is missing or linked")
        require(entry["entrypoint_sha256"] == sha256_file(entrypoint),
                "execution adapter entrypoint hash does not match")
        runtime_text = entry["runtime_executable"]
        require(isinstance(runtime_text, str) and Path(runtime_text).is_absolute(),
                "execution adapter runtime must be an absolute path")
        runtime = regular_unlinked_file(Path(runtime_text).resolve(),
                                        "execution adapter runtime")
        require(Path(runtime_text) == runtime,
                "execution adapter runtime path must already be canonical")
        require(entry["runtime_executable_sha256"] == sha256_file(runtime),
                "execution adapter runtime hash does not match")
        validate_provider_runtime(entry["provider_runtime"], require_hash=True)
        require(command[0] == runtime_text,
                "execution adapter command must begin with the frozen runtime")
        joined = "\0".join(command)
        for placeholder in contract["invocation"]["required_placeholders"]:
            require(placeholder in joined,
                    f"adapter command omits required placeholder {placeholder}")
        require(entry["container_or_sandbox_image_digest"] in joined,
                "adapter command must literally bind the frozen sandbox image digest")
    return contract


def provider_runtime_version_output(executable: Path) -> bytes:
    process = subprocess.run(
        [str(executable), "--version"], stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT, check=False,
    )
    require(process.returncode == 0,
            "provider runtime --version command failed")
    require(bool(process.stdout.strip()),
            "provider runtime --version output is empty")
    return process.stdout


def validate_provider_runtime(
    provider: dict[str, Any], require_hash: bool
) -> Path | None:
    require(isinstance(provider, dict),
            "execution_adapter.provider_runtime must be an object")
    require(provider.get("kind") in {"codex_cli", "excluded_fixture"},
            "provider runtime kind must be codex_cli or excluded_fixture")
    executable_text = provider.get("executable")
    if not require_hash and executable_text == "UNSET":
        return None
    require(isinstance(executable_text, str) and Path(executable_text).is_absolute(),
            "provider runtime executable must be an absolute path")
    executable = regular_unlinked_file(
        Path(executable_text).resolve(), "provider runtime executable"
    )
    require(Path(executable_text) == executable,
            "provider runtime executable path must already be canonical")
    if require_hash:
        require(provider.get("executable_sha256") == sha256_file(executable),
                "provider runtime executable hash does not match")
        output = provider_runtime_version_output(executable)
        require(provider.get("version_output_sha256") == sha256_bytes(output),
                "provider runtime version output hash does not match")
        observed = output.decode("utf-8", errors="strict").strip()
        require(provider.get("version") == observed,
                "provider runtime version text does not match")
        if provider["kind"] == "codex_cli":
            auth_source_text = provider.get("auth_source_path")
            require(isinstance(auth_source_text, str)
                    and Path(auth_source_text).is_absolute(),
                    "Codex provider auth source must be an absolute path")
            auth_source = Path(auth_source_text)
            require(auth_source.resolve() == auth_source,
                    "Codex provider auth source path must already be canonical")
            home_info = auth_source.lstat() if auth_source.exists() else None
            require(auth_source.is_dir() and not auth_source.is_symlink()
                    and home_info is not None
                    and not bool(getattr(home_info, "st_file_attributes", 0) & 0x400),
                    "Codex provider auth source must be a plain directory")
            children = list(auth_source.iterdir())
            require({child.name for child in children} == {"auth.json"},
                    "Codex provider auth source must contain only auth.json")
            regular_unlinked_file(
                auth_source / "auth.json", "Codex provider auth.json",
                require_executable=False,
            )
            attestation = provider.get("fresh_codex_home_attestation")
            require(isinstance(attestation, str) and len(attestation.strip()) >= 20,
                    "Codex provider fresh auth-only CODEX_HOME needs an attestation")
            safe_names = {
                "LANG", "LC_ALL", "PATH", "SYSTEMROOT", "SystemRoot", "TEMP", "TMP",
            }
            for field in ("process_environment", "shell_environment"):
                environment = provider.get(field)
                require(isinstance(environment, dict),
                        f"Codex provider {field} must be an object")
                lowered = set()
                for name, value in environment.items():
                    require(isinstance(name, str) and name in safe_names,
                            f"Codex provider {field} has a non-allowlisted name")
                    require(name.lower() not in lowered,
                            f"Codex provider {field} repeats a name by case")
                    require(isinstance(value, str) and bool(value),
                            f"Codex provider {field}.{name} must be nonempty")
                    lowered.add(name.lower())
            require("path" in {
                name.lower() for name in provider["shell_environment"]
            }, "Codex provider shell_environment must freeze PATH")
    return executable


def validate_codex_cli_configuration(
    provider: dict[str, Any], model: dict[str, Any]
) -> None:
    """Require the frozen CLI to parse the selected reasoning/tier configuration."""
    executable = Path(provider["executable"])
    environment = dict(provider["process_environment"])
    with tempfile.TemporaryDirectory(prefix="abrl-codex-config-probe-") as directory:
        environment["CODEX_HOME"] = directory
        process = subprocess.run([
            str(executable),
            "--config", f"model_reasoning_effort={json.dumps(model['reasoning_effort'])}",
            "--config", f"service_tier={json.dumps(model['service_tier'])}",
            "features", "list",
        ], cwd=ROOT, env=environment, stdout=subprocess.PIPE,
            stderr=subprocess.STDOUT, check=False, timeout=30)
    require(process.returncode == 0,
            "frozen Codex CLI rejects the selected reasoning effort or service tier")


def validate_checker_runtime_preflight(config: dict[str, Any]) -> dict[str, Any]:
    """Validate the executable checker boundary before any probe is launched."""
    entry = config["posthoc_checker"]
    contract_path = resolve_repo_path(entry["contract"])
    require(contract_path.is_file(), "missing checker-sandbox contract")
    contract = load(contract_path)
    require(contract.get("suite_id") == config["suite_id"]
            and contract.get("status") == "interface_frozen_results_absent",
            "checker-sandbox contract identity/status mismatch")
    if entry.get("mode") == "excluded_fixture":
        for field in (
            "sandbox_command_argv", "sandbox_cleanup_argv", "sandbox_inspect_argv",
            "sandbox_cleanup_by_label_argv", "sandbox_inspect_by_label_argv",
        ):
            require(isinstance(entry[field], list) and entry[field]
                    and all(isinstance(item, str) and item for item in entry[field]),
                    f"excluded fixture {field} must be a nonempty argv")
        return contract
    require(entry.get("mode") == "production",
            "checker mode must be production or excluded_fixture")
    launcher_path = resolve_repo_path(entry["host_launcher_path"])
    require(launcher_path.is_file()
            and entry["host_launcher_sha256"] == sha256_file(launcher_path),
            "checker host launcher is missing or differs from the seal")
    generated_commands = checker_launcher.command_templates(entry, launcher_path)
    command_fields = (
        "sandbox_command_argv", "sandbox_cleanup_argv", "sandbox_inspect_argv",
        "sandbox_cleanup_by_label_argv", "sandbox_inspect_by_label_argv",
    )
    for field in command_fields:
        argv = entry[field]
        require(isinstance(argv, list) and argv
                and all(isinstance(item, str) and item for item in argv),
                f"posthoc_checker.{field} must be a nonempty argv")
        require(argv == generated_commands[field],
                f"posthoc_checker.{field} is not the sealed launcher template")
    joined = "\0".join(entry["sandbox_command_argv"])
    for placeholder in contract["invocation"]["required_placeholders"]:
        require(placeholder in joined,
                f"checker sandbox command omits required placeholder {placeholder}")
    route_placeholders = (
        ("sandbox_cleanup_argv", "cleanup_required_placeholder"),
        ("sandbox_inspect_argv", "inspect_required_placeholder"),
        ("sandbox_cleanup_by_label_argv", "label_cleanup_required_placeholder"),
        ("sandbox_inspect_by_label_argv", "label_inspect_required_placeholder"),
    )
    for field, contract_field in route_placeholders:
        require(contract["invocation"][contract_field] in "\0".join(entry[field]),
                f"checker lifecycle route omits {contract['invocation'][contract_field]}")
    require(not any(
        token == "-d" or token == "--detach" or token.startswith("--detach=")
        for token in entry["sandbox_command_argv"]
    ), "checker sandbox command contains detached mode")
    require(entry["mode"] in {"production", "excluded_fixture"},
            "checker mode must be production or excluded_fixture")
    require(re.fullmatch(r"sha256:[0-9a-f]{64}", entry["container_image_digest"])
            is not None, "checker image digest is not immutable")
    require(isinstance(entry["inspect_absent_exit_code"], int)
            and not isinstance(entry["inspect_absent_exit_code"], bool)
            and 0 <= entry["inspect_absent_exit_code"] <= 255,
            "checker absent exit code is invalid")
    require(entry["inspect_absent_exit_code"] == checker_launcher.ABSENT_EXIT_CODE,
            "checker absent exit code differs from the sealed launcher")
    for field in (
        "wall_clock_seconds", "memory_mb", "pids_limit", "maximum_output_bytes",
        "maximum_response_bytes",
    ):
        require(isinstance(entry["budgets"][field], int)
                and not isinstance(entry["budgets"][field], bool)
                and entry["budgets"][field] > 0,
                f"posthoc_checker.budgets.{field} must be positive")
    require(isinstance(entry["budgets"]["cpus"], (int, float))
            and not isinstance(entry["budgets"]["cpus"], bool)
            and entry["budgets"]["cpus"] > 0,
            "posthoc_checker.budgets.cpus must be positive")
    require(all(resolve_repo_path(entry[field]).is_file() for field in (
        "driver_path", "inner_checker_path", "isolation_probe_runner_path",
        "host_launcher_path", "checker_image_recipe", "checker_image_sbom",
        "checker_image_build_input_manifest", "checker_cache_manifest_artifact",
        "checker_image_build_log", "controller_entrypoint_source",
    )), "checker controller/inner/probe-runner file is missing")
    host_python = Path(entry["host_python_executable"])
    require(host_python.resolve() == Path(sys.executable).resolve(),
            "checker host Python differs from the invoking interpreter")
    checker_launcher.regular_executable(
        host_python.resolve(), entry["host_python_executable_sha256"], "host Python"
    )
    runtime = checker_launcher.regular_executable(
        Path(entry["container_runtime_executable"]),
        entry["container_runtime_executable_sha256"], "Docker runtime",
    )
    require(entry["container_runtime_kind"] == "docker",
            "production checker supports only the sealed Docker launcher")
    require(runtime.resolve() == checker_launcher.canonical_docker_executable(),
            "Docker runtime differs from the canonical audited executable")
    identity = checker_launcher.runtime_identity(runtime)
    require(entry["runtime_id"] == identity["runtime_id"]
            and entry["runtime_version"] == identity["runtime_version"]
            and entry["runtime_signature_output_sha256"]
            == identity["runtime_signature_output_sha256"]
            and identity["runtime_version_output_sha256"]
            == entry["runtime_version_output_sha256"]
            and identity["daemon_identity_output_sha256"]
            == entry["daemon_identity_output_sha256"],
            "Docker client/server version or daemon identity changed")
    recipe_path = resolve_repo_path(entry["checker_image_recipe"])
    sbom_path = resolve_repo_path(entry["checker_image_sbom"])
    build_input_path = resolve_repo_path(entry["checker_image_build_input_manifest"])
    cache_manifest_path = resolve_repo_path(entry["checker_cache_manifest_artifact"])
    build_log_path = resolve_repo_path(entry["checker_image_build_log"])
    controller_path = resolve_repo_path(entry["controller_entrypoint_source"])
    require(entry["checker_image_recipe_sha256"] == sha256_file(recipe_path)
            and entry["checker_image_sbom_sha256"] == sha256_file(sbom_path)
            and entry["checker_image_build_input_manifest_sha256"]
            == sha256_file(build_input_path)
            and entry["checker_cache_manifest_sha256"] == sha256_file(cache_manifest_path)
            and entry["checker_image_build_log_sha256"] == sha256_file(build_log_path)
            and entry["controller_entrypoint_source_sha256"]
            == sha256_file(controller_path),
            "checker image provenance artifact/controller hash differs from the seal")
    sbom = load(sbom_path)
    build_input = load(build_input_path)
    current_orchestrator = subprocess.check_output(
        ["git", "rev-parse", "HEAD"], cwd=ROOT, text=True
    ).strip()
    checker_image_builder.validate_build_input_payload(
        build_input,
        expected_workspace_commit=config.get("workspace_base_commit"),
        expected_orchestrator_commit=current_orchestrator,
    )
    cache_payload = checker_cache_manifest.load_manifest(cache_manifest_path)
    lean_toolchain_sha256 = next(
        item["sha256"] for item in build_input["source_files"]
        if item["path"] == "lean-toolchain"
    )
    expected_cache_provenance = {
        "workspace_base_commit": build_input["workspace_base_commit"],
        "source_files_aggregate_sha256": build_input[
            "source_files_aggregate_sha256"
        ],
        "build_input_manifest_sha256": sha256_file(build_input_path),
        "checker_image_recipe_sha256": sha256_file(recipe_path),
        "base_image_digest": build_input["lean_base_image_digest"].split(":", 1)[1],
        "lean_toolchain_sha256": lean_toolchain_sha256,
    }
    require(cache_payload["provenance"] == expected_cache_provenance,
            "checker cache manifest is not bound to the frozen Git baseline")
    validate_checker_image_sbom(
        entry, sbom, sha256_file(resolve_repo_path(entry["inner_checker_path"])),
        config.get("workspace_base_commit"), build_input, cache_payload,
        sha256_file(build_input_path), sha256_file(build_log_path), identity,
        checker_image_builder.lean_toolchain_release(
            build_input["workspace_base_commit"]
        ),
    )
    require(entry["controller_uid"] == "0:0"
            and re.fullmatch(r"[1-9][0-9]*:[1-9][0-9]*", entry["worker_uid"]),
            "checker requires the sealed root controller and a positive worker UID:GID")
    require(entry["controller_entrypoint"] == checker_launcher.CONTROLLER_PATH,
            "checker controller entrypoint differs from the sealed image path")
    if entry["mode"] == "production":
        require(entry["cache_prelude_argv"] == [],
                "production checker cache prelude must be empty")
        require(entry["worker_command_prefix"]
                == checker_launcher.worker_command_prefix(entry),
                "production worker prefix is not the sealed UID/GID transition")
    if entry.get("contract_sha256") != "UNSET":
        require(entry["contract_sha256"] == sha256_file(contract_path),
                "checker contract hash is stale")
    return contract


def validate_checker_image_sbom(
    entry: dict[str, Any], sbom: dict[str, Any], inner_checker_sha256: str,
    workspace_base_commit: str | None = None,
    build_input: dict[str, Any] | None = None,
    cache_manifest: dict[str, Any] | None = None,
    build_input_sha256: str | None = None,
    build_log_sha256: str | None = None,
    current_runtime_identity: dict[str, str] | None = None,
    expected_toolchain_release: str | None = None,
) -> None:
    expected_sbom_fields = {
        "schema_version", "suite_id", "status", "container_image_digest",
        "checker_image_recipe_sha256", "controller_entrypoint_sha256",
        "inner_checker_sha256", "cache_manifest_tool_sha256",
        "image_context_builder_sha256", "build_input_manifest_sha256",
        "source_snapshot_manifest_sha256", "workspace_base_commit",
        "controller_uid", "worker_uid", "base_image_digest", "base_image_reference",
        "toolchain_release", "offline_toolchain_probe",
        "toolchain_probe_source_sha256", "lean_version", "lake_version",
        "python_version",
        "lake_cache_manifest_sha256", "checker_cache_root",
        "checker_cache_manifest_path", "docker_executable_sha256",
        "docker_runtime_identity", "image_build_log_sha256", "nonclaim",
    }
    required_toolchain = (
        "lean_version", "lake_version", "python_version",
    )
    toolchain_complete = all(
        isinstance(sbom.get(name), str)
        and bool(sbom[name].strip())
        and "UNSET" not in sbom[name]
        for name in required_toolchain
    )
    cache_manifest_sha256 = sbom.get("lake_cache_manifest_sha256")
    digest_fields = (
        "cache_manifest_tool_sha256", "image_context_builder_sha256",
        "build_input_manifest_sha256", "source_snapshot_manifest_sha256",
        "image_build_log_sha256", "docker_executable_sha256",
    )
    provenance_complete = all(
        isinstance(sbom.get(name), str)
        and re.fullmatch(r"[0-9a-f]{64}", sbom[name]) is not None
        for name in digest_fields
    )
    base_reference = sbom.get("base_image_reference", "")
    base_commit = sbom.get("workspace_base_commit", "")
    build_runtime = sbom.get("docker_runtime_identity")
    runtime_identity_complete = (
        isinstance(build_runtime, dict)
        and set(build_runtime) == {
            "runtime_id", "runtime_version", "runtime_signature_output_sha256",
            "runtime_version_output_sha256", "daemon_identity_output_sha256",
        }
        and build_runtime.get("runtime_id") == "docker"
        and isinstance(build_runtime.get("runtime_version"), str)
        and bool(build_runtime["runtime_version"].strip())
        and all(
            isinstance(build_runtime.get(name), str)
            and re.fullmatch(r"[0-9a-f]{64}", build_runtime[name]) is not None
            for name in (
                "runtime_signature_output_sha256", "runtime_version_output_sha256",
                "daemon_identity_output_sha256",
            )
        )
    )
    require(set(sbom) == expected_sbom_fields
            and sbom.get("schema_version") == 1
            and sbom.get("suite_id") == "ABRL-TARGET-DRIFT-V2"
            and isinstance(sbom.get("nonclaim"), str)
            and len(sbom["nonclaim"].strip()) >= 40
            and sbom.get("status") == "built_manifest_verified_probe_pending"
            and sbom.get("container_image_digest") == entry["container_image_digest"]
            and sbom.get("checker_image_recipe_sha256")
            == entry["checker_image_recipe_sha256"]
            and sbom.get("controller_entrypoint_sha256")
            == entry["controller_entrypoint_sha256"]
            and sbom.get("inner_checker_sha256")
            == inner_checker_sha256
            and sbom.get("controller_uid") == entry["controller_uid"]
            and sbom.get("worker_uid") == entry["worker_uid"]
            and re.fullmatch(r"sha256:[0-9a-f]{64}", sbom.get("base_image_digest", ""))
            and isinstance(base_reference, str)
            and re.fullmatch(r"[^\s@]+@sha256:[0-9a-f]{64}", base_reference)
            and base_reference.rsplit("@", 1)[1] == sbom.get("base_image_digest")
            and re.fullmatch(r"[0-9a-f]{40}", base_commit) is not None
            and (workspace_base_commit is None or base_commit == workspace_base_commit)
            and provenance_complete
            and runtime_identity_complete
            and sbom.get("cache_manifest_tool_sha256")
            == sha256_file(ROOT / "tools" / "target_drift_checker_cache_manifest.py")
            and sbom.get("image_context_builder_sha256")
            == sha256_file(ROOT / "tools" / "prepare_target_drift_checker_image.py")
            and (build_input is None
                 or sbom.get("build_input_manifest_sha256") == build_input_sha256)
            and (build_input is None
                 or sbom.get("source_snapshot_manifest_sha256")
                 == build_input.get("source_files_aggregate_sha256"))
            and (build_input is None
                 or sbom.get("base_image_reference") == build_input.get("lean_base_image"))
            and (cache_manifest is None
                 or cache_manifest.get("provenance", {}).get(
                     "build_input_manifest_sha256"
                 ) == build_input_sha256)
            and (cache_manifest is None
                 or sbom.get("lake_cache_manifest_sha256")
                 == entry.get("checker_cache_manifest_sha256"))
            and (build_log_sha256 is None
                 or sbom.get("image_build_log_sha256") == build_log_sha256)
            and sbom.get("docker_executable_sha256")
            == entry.get("container_runtime_executable_sha256")
            and (current_runtime_identity is None
                 or build_runtime == current_runtime_identity)
            and (expected_toolchain_release is None
                 or sbom.get("toolchain_release") == expected_toolchain_release)
            and sbom.get("offline_toolchain_probe")
            == "passed_network_none_as_worker"
            and sbom.get("toolchain_probe_source_sha256")
            == sha256_bytes(checker_image_builder.TOOLCHAIN_PROBE_SOURCE)
            and isinstance(sbom.get("toolchain_release"), str)
            and checker_image_builder.parse_lean_version_output(
                sbom.get("lean_version", "")
            ) == sbom["toolchain_release"]
            and checker_image_builder.parse_lake_lean_version_output(
                sbom.get("lake_version", "")
            ) == sbom["toolchain_release"]
            and toolchain_complete
            and isinstance(cache_manifest_sha256, str)
            and re.fullmatch(r"[0-9a-f]{64}", cache_manifest_sha256)
            and sbom.get("checker_cache_root") == entry["checker_cache_root"]
            == checker_launcher.CHECKER_CACHE_ROOT
            and sbom.get("checker_cache_manifest_path")
            == entry["checker_cache_manifest_path"]
            == checker_launcher.CHECKER_CACHE_MANIFEST_PATH
            and cache_manifest_sha256 == entry["checker_cache_manifest_sha256"],
            "checker image SBOM does not bind the image recipe/controller/inner checker")


def validate_checker_contract(config: dict[str, Any], require_hashes: bool) -> dict[str, Any]:
    entry = config["posthoc_checker"]
    if require_hashes:
        validate_checker_runtime_preflight(config)
    contract_path = resolve_repo_path(entry["contract"])
    require(contract_path.is_file(), "missing checker-sandbox contract")
    contract = load(contract_path)
    require(contract["suite_id"] == config["suite_id"],
            "checker-sandbox contract suite mismatch")
    require(contract["status"] == "interface_frozen_results_absent",
            "checker-sandbox contract must remain result-free")
    command = entry["sandbox_command_argv"]
    cleanup = entry["sandbox_cleanup_argv"]
    inspect = entry["sandbox_inspect_argv"]
    cleanup_by_label = entry["sandbox_cleanup_by_label_argv"]
    inspect_by_label = entry["sandbox_inspect_by_label_argv"]
    require(isinstance(command, list) and command
            and all(isinstance(item, str) and item for item in command),
            "checker sandbox_command_argv must be a nonempty string list")
    require(isinstance(cleanup, list) and cleanup
            and all(isinstance(item, str) and item for item in cleanup),
            "checker sandbox_cleanup_argv must be a nonempty string list")
    require(isinstance(inspect, list) and inspect
            and all(isinstance(item, str) and item for item in inspect),
            "checker sandbox_inspect_argv must be a nonempty string list")
    require(isinstance(cleanup_by_label, list) and cleanup_by_label
            and all(isinstance(item, str) and item for item in cleanup_by_label),
            "checker sandbox_cleanup_by_label_argv must be a nonempty string list")
    require(isinstance(inspect_by_label, list) and inspect_by_label
            and all(isinstance(item, str) and item for item in inspect_by_label),
            "checker sandbox_inspect_by_label_argv must be a nonempty string list")
    if not require_hashes:
        return contract
    require(entry["contract_sha256"] == sha256_file(contract_path),
            "checker-sandbox contract hash does not match")
    joined = "\0".join(command)
    for placeholder in contract["invocation"]["required_placeholders"]:
        require(placeholder in joined,
                f"checker sandbox command omits required placeholder {placeholder}")
    require(contract["invocation"]["cleanup_required_placeholder"]
            in "\0".join(cleanup), "checker cleanup command must bind the cidfile")
    require(contract["invocation"]["inspect_required_placeholder"]
            in "\0".join(inspect), "checker inspect command must bind the cidfile")
    require(contract["invocation"]["label_cleanup_required_placeholder"]
            in "\0".join(cleanup_by_label),
            "checker label cleanup command must bind the attempt label")
    require(contract["invocation"]["label_inspect_required_placeholder"]
            in "\0".join(inspect_by_label),
            "checker label inspect command must bind the attempt label")
    forbidden_detach = any(
        token == "-d" or token == "--detach" or token.startswith("--detach=")
        for token in command
    )
    require(not forbidden_detach,
            "checker sandbox command contains a forbidden detached-mode token")
    runtime_sha256 = checker_runtime_config_sha256(config)
    require(entry["runtime_config_sha256"] == runtime_sha256,
            "checker runtime-config digest does not match the complete runtime boundary")
    probe_path = resolve_repo_path(entry["isolation_probe_report"])
    require(probe_path.is_file(), "checker isolation-probe report is missing")
    require(entry["isolation_probe_report_sha256"] == sha256_file(probe_path),
            "checker isolation-probe report hash does not match")
    probe = load(probe_path)
    require(probe.get("suite_id") == config["suite_id"],
            "checker isolation-probe suite mismatch")
    require(probe.get("container_image_digest") == entry["container_image_digest"],
            "checker isolation-probe image differs from frozen config")
    require(probe.get("checker_runtime_config_sha256") == runtime_sha256,
            "checker isolation-probe does not bind the frozen runtime config")
    command_template_sha256 = sha256_bytes(canonical_json_bytes(command))
    require(probe.get("runtime_command_template_sha256") == command_template_sha256,
            "checker isolation-probe does not bind the sandbox command template")
    require(probe.get("probe_runner_sha256")
            == entry["isolation_probe_runner_sha256"],
            "checker isolation-probe does not bind the sealed probe runner")
    probe_artifacts = probe.get("artifact_manifest")
    require(isinstance(probe_artifacts, list) and probe_artifacts,
            "checker isolation-probe artifact manifest is empty")
    require(all(
        isinstance(item, dict)
        and set(item) == {"path", "bytes", "sha256"}
        and isinstance(item["path"], str)
        and isinstance(item["bytes"], int)
        and re.fullmatch(r"[0-9a-f]{64}", item["sha256"]) is not None
        for item in probe_artifacts
    ), "checker isolation-probe artifact manifest is malformed")
    artifact_root = resolve_repo_path(entry["isolation_probe_artifacts_dir"])
    artifact_payloads = probe_artifact_bytes(artifact_root)
    require(probe_artifact_manifest(artifact_payloads) == probe_artifacts,
            "checker isolation-probe artifact bytes differ from the report manifest")
    require(probe.get("checker_id") == entry["checker_id"]
            and probe.get("checker_version") == entry["checker_version"],
            "checker isolation-probe identity differs from frozen config")
    if entry["mode"] == "production":
        require(probe.get("status") == "passed",
                "production checker requires a passed isolation-probe report")
        require(probe.get("controller_entrypoint_sha256")
                == entry["controller_entrypoint_sha256"],
                "production probe does not bind the in-image controller bytes")
        required_probes = {
            "network_denied", "host_sentinel_protected", "operator_ground_truth_absent",
            "checker_outputs_not_worker_writable",
            "patched_source_and_controller_input_read_only",
            "mounted_inputs_and_cidfile_protected", "background_process_reaped",
        }
        results = probe.get("probes", {})
        require(required_probes == set(results)
                and all(results[name] is True for name in required_probes),
                "production checker isolation probes are incomplete or failed")
        nonce = probe.get("probe_nonce")
        attempt_label = probe.get("checker_attempt_label")
        require(isinstance(nonce, str) and re.fullmatch(r"[0-9a-f]{48}", nonce)
                and attempt_label == f"ABRL-PROBE-{nonce}",
                "production checker isolation probe nonce/label is malformed")
        require("host-observations.json" in artifact_payloads,
                "production checker probe omits host observations")
        host_observations = strict_json_bytes(
            artifact_payloads["host-observations.json"], "checker host observations"
        )
        require(host_observations.get("probe_nonce") == nonce
                and host_observations.get("checker_attempt_label") == attempt_label
                and host_observations.get("checker_runtime_config_sha256") == runtime_sha256
                and host_observations.get("container_image_digest")
                == entry["container_image_digest"]
                and host_observations.get("derived_probes") == results,
                "probe report differs from sealed host observations")
        require(rendered_argv_matches_template(
            command, host_observations.get("rendered_sandbox_argv", [])
        ), "probe host ledger did not execute the frozen sandbox argv template")
    else:
        require(entry["mode"] == "excluded_fixture",
                "checker mode must be production or excluded_fixture")
        require(probe.get("status") == "excluded_fixture_nonexperimental",
                "fixture checker requires a nonexperimental probe record")
    return contract


def validate_auxiliary_prompts(config: dict[str, Any], require_hashes: bool) -> None:
    entries = (
        (config["grading"]["grader_prompt"], config["grading"]["grader_prompt_sha256"],
         "grader prompt"),
        (config["wording_audit"]["text_only_prompt"],
         config["wording_audit"]["text_only_prompt_sha256"], "text-only audit prompt"),
    )
    for path_text, expected, label in entries:
        path = resolve_repo_path(path_text)
        require(path.is_file(), f"missing {label}")
        if require_hashes:
            require(expected == sha256_file(path), f"{label} hash does not match")


def execution_code_paths(config: dict[str, Any]) -> dict[str, Path]:
    paths = {
        "prepare_target_drift_execution.py": resolve_repo_path(
            config["sealed_agent_view"]["materializer"]
        ),
        "run_target_drift_execution.py": resolve_repo_path(
            config["sealed_agent_view"]["run_preparer"]
        ),
        "check_target_drift_run.py": resolve_repo_path(
            config["posthoc_checker"]["driver_path"]
        ),
        "check_target_drift_inner.py": resolve_repo_path(
            config["posthoc_checker"]["inner_checker_path"]
        ),
        "record_target_drift_checker_isolation_probe.py": resolve_repo_path(
            config["posthoc_checker"]["isolation_probe_runner_path"]
        ),
        "launch_target_drift_checker_container.py": resolve_repo_path(
            config["posthoc_checker"]["host_launcher_path"]
        ),
        "check_target_drift_container_controller.py": resolve_repo_path(
            config["posthoc_checker"]["controller_entrypoint_source"]
        ),
        "prepare_target_drift_grading.py": resolve_repo_path(
            config["grading"]["packet_materializer"]
        ),
        "assemble_target_drift_grades.py": resolve_repo_path(
            config["analysis"]["grade_assembler"]
        ),
        "analyze_target_drift_execution.py": resolve_repo_path(
            config["analysis"]["script"]
        ),
        "test_target_drift_analysis.py": resolve_repo_path(
            config["analysis"]["test_script"]
        ),
        "audit_target_drift_wording.py": resolve_repo_path(
            config["wording_audit"]["script"]
        ),
        "build_target_drift_completion_ledger.py": resolve_repo_path(
            config["missing_run_policy"]["completion_ledger_builder"]
        ),
        "run_target_drift_schedule.py": resolve_repo_path(
            config["missing_run_policy"]["schedule_runner"]
        ),
        "prepare_target_drift_human_contract_review.py": resolve_repo_path(
            config["human_source_contract_validation"]["self_attested_prepare_script"]
        ),
        "validate_target_drift_human_contract_review.py": resolve_repo_path(
            config["human_source_contract_validation"]["self_attested_validator_script"]
        ),
        "test_target_drift_human_contract_review.py": resolve_repo_path(
            config["human_source_contract_validation"]["self_attested_validator_test"]
        ),
        "finalize_target_drift_config.py": resolve_repo_path(
            config["human_source_contract_validation"]["execution_finalizer"]
        ),
        "validate_target_drift_human_contract_external_verification.py": resolve_repo_path(
            config["human_source_contract_validation"]["external_validator_script"]
        ),
        "test_target_drift_human_contract_external_verification.py": resolve_repo_path(
            config["human_source_contract_validation"]["external_validator_test"]
        ),
    }
    if config["grading"].get("grader_exporter") is not None:
        paths["export_target_drift_grader_pack.py"] = resolve_repo_path(
            config["grading"]["grader_exporter"]
        )
    if config["execution_adapter"].get("entrypoint_path") != "UNSET":
        paths["execution_adapter_entrypoint"] = adapter_entrypoint_path(config)
    return paths


def execution_code_expected_hashes(config: dict[str, Any]) -> dict[str, str]:
    human = config["human_source_contract_validation"]
    expected = {
        "prepare_target_drift_execution.py": config["sealed_agent_view"]["materializer_sha256"],
        "run_target_drift_execution.py": config["sealed_agent_view"]["run_preparer_sha256"],
        "check_target_drift_run.py": config["posthoc_checker"]["driver_sha256"],
        "check_target_drift_inner.py": config["posthoc_checker"]["inner_checker_sha256"],
        "record_target_drift_checker_isolation_probe.py": config["posthoc_checker"][
            "isolation_probe_runner_sha256"
        ],
        "launch_target_drift_checker_container.py": config["posthoc_checker"][
            "host_launcher_sha256"
        ],
        "check_target_drift_container_controller.py": config["posthoc_checker"][
            "controller_entrypoint_source_sha256"
        ],
        "prepare_target_drift_grading.py": config["grading"]["packet_materializer_sha256"],
        "assemble_target_drift_grades.py": config["analysis"]["grade_assembler_sha256"],
        "analyze_target_drift_execution.py": config["analysis"]["script_sha256"],
        "test_target_drift_analysis.py": config["analysis"]["test_script_sha256"],
        "audit_target_drift_wording.py": config["wording_audit"]["script_sha256"],
        "build_target_drift_completion_ledger.py": config["missing_run_policy"][
            "completion_ledger_builder_sha256"
        ],
        "run_target_drift_schedule.py": config["missing_run_policy"][
            "schedule_runner_sha256"
        ],
        "prepare_target_drift_human_contract_review.py": human[
            "self_attested_prepare_script_sha256"
        ],
        "validate_target_drift_human_contract_review.py": human[
            "self_attested_validator_script_sha256"
        ],
        "test_target_drift_human_contract_review.py": human[
            "self_attested_validator_test_sha256"
        ],
        "finalize_target_drift_config.py": human["execution_finalizer_sha256"],
        "validate_target_drift_human_contract_external_verification.py": human[
            "external_validator_script_sha256"
        ],
        "test_target_drift_human_contract_external_verification.py": human[
            "external_validator_test_sha256"
        ],
    }
    if config["execution_adapter"].get("entrypoint_path") != "UNSET":
        expected["execution_adapter_entrypoint"] = config["execution_adapter"][
            "entrypoint_sha256"
        ]
    return expected


def validate_live_pack_verifier_trust_anchor(
    execution_code_bytes: dict[str, bytes],
) -> None:
    """Require the live verifier modules to equal their pack-bound source bytes."""
    live_paths = {
        "prepare_target_drift_execution.py": Path(__file__).resolve(),
        "prepare_target_drift_human_contract_review.py": Path(
            human_contract_review.prepare.__file__
        ).resolve(),
        "validate_target_drift_human_contract_review.py": Path(
            human_contract_review.__file__
        ).resolve(),
        "validate_target_drift_human_contract_external_verification.py": Path(
            external_contract_review.__file__
        ).resolve(),
    }
    for name, path in live_paths.items():
        require(name in execution_code_bytes,
                f"sealed pack omits live verifier source {name}")
        require(execution_code_bytes[name] == path.read_bytes(),
                f"live verifier source differs from pack-bound bytes for {name}")


def validate_execution_code_hashes(config: dict[str, Any], require_hashes: bool) -> None:
    paths = execution_code_paths(config)
    require(all(path.is_file() for path in paths.values()),
            "one or more sealed execution-code files are missing")
    if not require_hashes:
        return
    expected = execution_code_expected_hashes(config)
    for name, path in paths.items():
        if name == "export_target_drift_grader_pack.py":
            # The exporter is bound directly by the sealed-pack component
            # aggregate and rechecks its current bytes against the sealed copy.
            continue
        require(expected[name] == sha256_file(path), f"execution-code hash mismatch for {name}")


def checker_runtime_artifact_paths(config: dict[str, Any]) -> dict[str, Path]:
    checker = config["posthoc_checker"]
    if checker.get("mode") != "production":
        return {}
    return {
        "checker-image.Containerfile": resolve_repo_path(checker["checker_image_recipe"]),
        "checker-image-sbom.json": resolve_repo_path(checker["checker_image_sbom"]),
        "checker-image-build-input.json": resolve_repo_path(
            checker["checker_image_build_input_manifest"]
        ),
        "checker-cache-manifest.json": resolve_repo_path(
            checker["checker_cache_manifest_artifact"]
        ),
        "checker-image-build.log": resolve_repo_path(checker["checker_image_build_log"]),
    }


def checker_runtime_artifact_names(config: dict[str, Any]) -> set[str]:
    if config["posthoc_checker"].get("mode") != "production":
        return set()
    return {
        "checker-image.Containerfile", "checker-image-sbom.json",
        "checker-image-build-input.json", "checker-cache-manifest.json",
        "checker-image-build.log",
    }


def validate_checker_runtime_artifacts(config: dict[str, Any]) -> None:
    paths = checker_runtime_artifact_paths(config)
    if not paths:
        return
    checker = config["posthoc_checker"]
    require(all(path.is_file() for path in paths.values()),
            "checker image provenance artifact is missing")
    require(sha256_file(paths["checker-image.Containerfile"])
            == checker["checker_image_recipe_sha256"],
            "checker image recipe artifact hash differs from config")
    require(sha256_file(paths["checker-image-sbom.json"])
            == checker["checker_image_sbom_sha256"],
            "checker image SBOM artifact hash differs from config")
    require(sha256_file(paths["checker-image-build-input.json"])
            == checker["checker_image_build_input_manifest_sha256"],
            "checker image build-input artifact hash differs from config")
    require(sha256_file(paths["checker-cache-manifest.json"])
            == checker["checker_cache_manifest_sha256"],
            "checker cache-manifest artifact hash differs from config")
    require(sha256_file(paths["checker-image-build.log"])
            == checker["checker_image_build_log_sha256"],
            "checker image build-log artifact hash differs from config")


def validate_frozen_choices(config: dict[str, Any]) -> None:
    def nonempty(value: Any, label: str, minimum: int = 1) -> None:
        require(isinstance(value, str) and len(value.strip()) >= minimum,
                f"{label} must be a substantive nonempty string")

    commit = config["orchestrator_commit"]
    require(isinstance(commit, str) and re.fullmatch(r"[0-9a-f]{40}", commit) is not None,
            "orchestrator_commit must be a lowercase full Git commit")
    model = config["model"]
    for field in (
        "provider", "model_id", "immutable_version", "api_or_runtime",
        "seed_semantics", "reasoning_effort", "service_tier",
        "sampling_control_semantics",
    ):
        nonempty(model[field], f"model.{field}")
    pricing = config["pricing"]
    require(pricing.get("currency") == "USD"
            and pricing.get("unit") == "per_million_tokens",
            "pricing must use USD per million tokens")
    for field in (
        "input_tokens", "cached_input_tokens", "cache_write_input_tokens",
        "output_tokens",
    ):
        require(isinstance(pricing[field], (int, float))
                and not isinstance(pricing[field], bool) and pricing[field] >= 0,
                f"pricing.{field} must be a nonnegative number")
    nonempty(pricing["source_url"], "pricing.source_url")
    nonempty(pricing["effective_date"], "pricing.effective_date")
    require(pricing["output_includes_reasoning_tokens"] is True,
            "pricing must explicitly count reasoning tokens inside output tokens")

    budgets = config["budgets_per_run"]
    for field in (
        "maximum_input_tokens", "maximum_output_tokens", "maximum_tool_calls",
        "maximum_build_attempts", "wall_clock_seconds",
    ):
        require(isinstance(budgets[field], int) and not isinstance(budgets[field], bool)
                and budgets[field] > 0, f"budgets_per_run.{field} must be a positive integer")
    require(isinstance(budgets["maximum_model_retries"], int)
            and not isinstance(budgets["maximum_model_retries"], bool)
            and budgets["maximum_model_retries"] >= 0,
            "budgets_per_run.maximum_model_retries must be a nonnegative integer")
    require(isinstance(budgets["maximum_cost_usd"], (int, float))
            and not isinstance(budgets["maximum_cost_usd"], bool)
            and budgets["maximum_cost_usd"] >= 0,
            "budgets_per_run.maximum_cost_usd must be nonnegative")

    retry = config["retry_policy"]
    require(retry["semantic_failure_retries"] == 0,
            "semantic failures must never be retried")
    require(isinstance(retry["infrastructure_retry_limit"], int)
            and not isinstance(retry["infrastructure_retry_limit"], bool)
            and retry["infrastructure_retry_limit"] >= 0,
            "infrastructure_retry_limit must be a nonnegative integer")
    require(retry["infrastructure_retry_limit"] <= budgets["maximum_model_retries"],
            "infrastructure retry limit exceeds the model-retry budget")
    nonempty(retry["infrastructure_failure_definition"],
             "retry_policy.infrastructure_failure_definition", 20)
    require(retry["missing_run_policy"]
            == "complete_450_no_replacement_no_imputation_v1",
            "retry_policy.missing_run_policy must use the frozen no-imputation policy")

    randomization = config["randomization"]
    validate_paired_replicates(config)
    require(isinstance(randomization["presentation_order_seed"], int)
            and not isinstance(randomization["presentation_order_seed"], bool),
            "presentation_order_seed must be an integer")

    wording = config["wording_audit"]
    nonempty(wording["text_only_model_id"], "wording_audit.text_only_model_id")
    require(isinstance(wording["text_only_accuracy"], (int, float))
            and not isinstance(wording["text_only_accuracy"], bool)
            and 0 <= wording["text_only_accuracy"] <= 1,
            "wording_audit.text_only_accuracy must lie in [0,1]")
    nonempty(wording["independent_blind_reviewer_id"],
             "wording_audit.independent_blind_reviewer_id")
    nonempty(wording["independent_blind_review_attestation"],
             "wording_audit.independent_blind_review_attestation", 20)
    validate_human_source_contract_review(config, require_completion=True)

    adapter = config["execution_adapter"]
    for field in ("adapter_id", "adapter_version"):
        nonempty(adapter[field], f"execution_adapter.{field}")
    require(re.fullmatch(r"sha256:[0-9a-f]{64}",
                         adapter["container_or_sandbox_image_digest"]) is not None,
            "sandbox image digest must be sha256:<64 lowercase hex characters>")
    nonempty(adapter["budget_enforcement_attestation"],
             "execution_adapter.budget_enforcement_attestation", 20)
    nonempty(adapter["filesystem_network_process_attestation"],
             "execution_adapter.filesystem_network_process_attestation", 20)
    validate_provider_runtime(adapter["provider_runtime"], require_hash=True)
    require(adapter["provider_runtime"]["kind"] == "codex_cli",
            "frozen primary execution requires a real codex_cli provider runtime")
    adapter_identity = (adapter["adapter_id"] + " " + adapter["adapter_version"]).lower()
    if adapter["provider_runtime"]["kind"] == "excluded_fixture":
        require(any(marker in adapter_identity for marker in ("fixture", "excluded")),
                "excluded provider runtime requires an explicit fixture adapter identity")
    else:
        require(not any(marker in adapter_identity for marker in ("fixture", "excluded")),
                "codex_cli provider runtime cannot use a fixture adapter identity")
        require(retry["infrastructure_retry_limit"] == 0
                and budgets["maximum_model_retries"] == 0,
                "Codex CLI candidate requires zero adapter-level automatic CLI retries")
        require(retry["infrastructure_failure_definition"] == (
            "codex_cli_nonzero_exit_or_missing_thread_or_missing_terminal_usage_or_"
            "runtime_error_or_forbidden_tool_or_ambiguous_build_accounting"
        ), "Codex CLI infrastructure-failure definition must match the adapter enum")
        validate_codex_cli_configuration(adapter["provider_runtime"], model)

    checker = config["posthoc_checker"]
    for field in ("checker_id", "checker_version", "runtime_id", "runtime_version"):
        nonempty(checker[field], f"posthoc_checker.{field}")
    require(checker["mode"] == "production",
            "frozen primary execution requires the production post-hoc checker")
    require(re.fullmatch(r"sha256:[0-9a-f]{64}", checker["container_image_digest"])
            is not None, "checker image digest must be sha256:<64 lowercase hex>")
    require(re.fullmatch(r"[0-9a-f]{64}", checker["runtime_config_sha256"])
            is not None, "checker runtime_config_sha256 must be a lowercase SHA-256")
    require(isinstance(checker["inspect_absent_exit_code"], int)
            and not isinstance(checker["inspect_absent_exit_code"], bool)
            and 0 <= checker["inspect_absent_exit_code"] <= 255,
            "posthoc_checker.inspect_absent_exit_code must be an exit-code integer")
    nonempty(checker["filesystem_network_process_attestation"],
             "posthoc_checker.filesystem_network_process_attestation", 20)
    nonempty(checker["controller_worker_separation_attestation"],
             "posthoc_checker.controller_worker_separation_attestation", 20)
    checker_budgets = checker["budgets"]
    for field in (
        "wall_clock_seconds", "memory_mb", "pids_limit", "maximum_output_bytes",
        "maximum_response_bytes",
    ):
        require(isinstance(checker_budgets[field], int)
                and not isinstance(checker_budgets[field], bool)
                and checker_budgets[field] > 0,
                f"posthoc_checker.budgets.{field} must be a positive integer")
    require(isinstance(checker_budgets["cpus"], (int, float))
            and not isinstance(checker_budgets["cpus"], bool)
            and checker_budgets["cpus"] > 0,
            "posthoc_checker.budgets.cpus must be positive")
    worker_prefix = checker["worker_command_prefix"]
    require(isinstance(worker_prefix, list)
            and all(isinstance(item, str) and item.strip() for item in worker_prefix),
            "posthoc_checker.worker_command_prefix must be a string list")
    cache_prelude = checker["cache_prelude_argv"]
    require(isinstance(cache_prelude, list)
            and all(isinstance(item, str) and item.strip() for item in cache_prelude),
            "posthoc_checker.cache_prelude_argv must be an argv string list (possibly empty)")
    require(not any("{{" in item or "}}" in item for item in cache_prelude),
            "checker cache prelude must not contain unresolved placeholders")
    if checker["mode"] == "production":
        require(not cache_prelude,
                "production checker cache must come from the immutable image")
        require(bool(worker_prefix),
                "production checker requires a controller/worker command prefix")
        joined_identity = (checker["checker_id"] + " " + checker["checker_version"]).lower()
        require(not any(marker in joined_identity for marker in ("fake", "fixture", "excluded")),
                "production checker identity must not name a fixture")
    else:
        require("fixture" in checker["checker_id"].lower()
                or "excluded" in checker["checker_id"].lower(),
                "excluded checker mode requires an explicit fixture identity")

    grading = config["grading"]
    if config["suite_id"] == "ABRL-TARGET-DRIFT-V2":
        require(grading.get("grader_exporter")
                == "tools/export_target_drift_grader_pack.py",
                "grading.grader_exporter must name the sealed positive-allowlist exporter")
    require(isinstance(grading["packet_order_seed"], int)
            and not isinstance(grading["packet_order_seed"], bool),
            "grading.packet_order_seed must be an integer")
    graders = grading["primary_grader_ids"]
    require(isinstance(graders, list) and len(graders) == 2
            and len(set(graders)) == 2
            and all(isinstance(item, str) and item.strip() for item in graders),
            "grading.primary_grader_ids must contain two unique nonempty strings")
    nonempty(grading["adjudicator_id"], "grading.adjudicator_id")
    require(grading["adjudicator_id"] not in graders,
            "adjudicator must be independent of both primary graders")
    nonempty(grading["grader_blinding_attestation"],
             "grading.grader_blinding_attestation", 20)

    analysis = config["analysis"]
    validate_primary_analysis_contract(analysis)
    require(isinstance(analysis["bootstrap_seed"], int)
            and not isinstance(analysis["bootstrap_seed"], bool),
            "analysis.bootstrap_seed must be an integer")
    require(isinstance(analysis["bootstrap_replicates"], int)
            and analysis["bootstrap_replicates"] >= 1000,
            "analysis.bootstrap_replicates must be at least 1000")
    require(analysis["permutation_replicates"] == 32768,
            "analysis.permutation_replicates must enumerate all 15-unit sign flips")
    validate_method_amendment(config, require_hashes=True)


def validate_primary_analysis_contract(analysis: dict[str, Any]) -> None:
    """Fail closed if a sealed pack changes the prospectively fixed primary rule."""
    require(
        analysis.get("primary_interval_method_id") == PRIMARY_ANALYSIS_METHOD_ID,
        "analysis.primary_interval_method_id differs from the fixed primary method",
    )
    require(
        analysis.get("primary_success_rule") == PRIMARY_ANALYSIS_SUCCESS_RULE,
        "analysis.primary_success_rule differs from the fixed primary rule",
    )
    require(
        analysis.get("primary_pairing_key") == PRIMARY_ANALYSIS_PAIRING_KEY,
        "analysis.primary_pairing_key differs from the fixed primary pairing",
    )
    require(
        analysis.get("bootstrap_replicates") == PRIMARY_ANALYSIS_BOOTSTRAP_REPLICATES,
        "analysis.bootstrap_replicates differs from the fixed primary count",
    )
    require(
        analysis.get("permutation_replicates")
        == PRIMARY_ANALYSIS_PERMUTATION_REPLICATES,
        "analysis.permutation_replicates differs from the fixed exact count",
    )


def digest_components(
    config: dict[str, Any],
    agent_cases: dict[str, Any],
    run_manifest: dict[str, Any],
    challenges_bytes: bytes,
    paired_requirements_bytes: bytes,
    protocol_bytes: bytes,
    method_amendment_bytes: bytes,
    missing_run_policy_bytes: bytes,
    source_manifest_bytes: bytes,
    source_packet_bytes: dict[str, bytes],
    rubric_bytes: bytes,
    resource_policy_bytes: bytes,
    adapter_contract_bytes: bytes,
    checker_contract_bytes: bytes,
    checker_probe_bytes: bytes,
    checker_probe_artifact_bytes: dict[str, bytes],
    checker_runtime_artifact_bytes: dict[str, bytes],
    grader_prompt_bytes: bytes,
    text_only_prompt_bytes: bytes,
    prompt_bytes: dict[str, bytes],
    execution_code_bytes: dict[str, bytes],
    human_source_review_bytes: dict[str, bytes],
) -> dict[str, bytes]:
    components = {
        "agent_cases.json": canonical_json_bytes(agent_cases),
        "run_manifest.json": canonical_json_bytes(run_manifest),
        "execution_config.normalized.json": canonical_json_bytes(
            normalized_config_for_digest(config)
        ),
        "operator_challenges.json": challenges_bytes,
        "paired_requirements.json": paired_requirements_bytes,
        "protocol.json": protocol_bytes,
        "method-amendment.json": method_amendment_bytes,
        "missing-run-policy.json": missing_run_policy_bytes,
        "source_manifest.json": source_manifest_bytes,
        "grading_rubric.json": rubric_bytes,
        "resource_policy.json": resource_policy_bytes,
        "adapter_contract.json": adapter_contract_bytes,
        "checker_sandbox_contract.json": checker_contract_bytes,
        "checker_isolation_probe.json": checker_probe_bytes,
        "grader_prompt.md": grader_prompt_bytes,
        "text_only_audit_prompt.md": text_only_prompt_bytes,
    }
    components.update({
        f"checker_isolation_probe_artifacts/{name}": payload
        for name, payload in checker_probe_artifact_bytes.items()
    })
    components.update({
        f"checker_runtime_artifacts/{name}": payload
        for name, payload in checker_runtime_artifact_bytes.items()
    })
    components.update({
        f"source_packets/{name}": payload
        for name, payload in source_packet_bytes.items()
    })
    components.update({
        f"prompt_templates/{condition}.md": prompt_bytes[condition]
        for condition in CONDITIONS
    })
    components.update({
        f"execution_code/{name}": payload
        for name, payload in execution_code_bytes.items()
    })
    components.update({
        f"human_source_contract_review/{name}": payload
        for name, payload in human_source_review_bytes.items()
    })
    return components


def check_template(config_path: Path) -> None:
    config = load(config_path)
    require(config["suite_id"] in {"ABRL-TARGET-DRIFT-V1", "ABRL-TARGET-DRIFT-V2"},
            "wrong suite id")
    require(config["execution_status"] == "template_unfrozen",
            "checked template must remain template_unfrozen")
    require(bool(config["unresolved_fields"]), "template must enumerate unresolved fields")
    missing = unset_paths(config)
    require(bool(missing), "template unexpectedly contains no UNSET fields")
    validate_prompt_templates(config, require_hashes=False)
    if "resource_policy" in config:
        validate_paired_replicates(config)
        validate_method_amendment(config, require_hashes=True)
        validate_resource_policy(config, require_hash=False)
        validate_missing_run_policy(config, require_hash=False)
        validate_paired_requirements(config)
        validate_adapter_contract(config, require_hash=False)
        validate_checker_contract(config, require_hashes=False)
        validate_auxiliary_prompts(config, require_hashes=False)
        validate_execution_code_hashes(config, require_hashes=False)
        validate_human_source_contract_review(config, require_completion=False)
    else:
        require(config["suite_id"] == "ABRL-TARGET-DRIFT-V1",
                "v2 template must define a resource policy")
    sources = load(resolve_repo_path(config["source_files_manifest"]))
    require(sources["status"] == "template_unfrozen",
            "source manifest must remain template_unfrozen")
    require(len(sources["sources"]) == 4, "expected four frozen-source entries")
    require(
        all(
            isinstance(source["sha256"], str)
            and len(source["sha256"]) == 64
            and all(character in "0123456789abcdef" for character in source["sha256"])
            for source in sources["sources"]
        ),
        "every source template entry must carry a lowercase SHA-256",
    )
    rubric = load(resolve_repo_path(config["grading"]["rubric"]))
    require(rubric["no_results"] is True, "grading rubric must remain result-free")
    print(
        "target-drift execution template "
        f"{config['suite_id']} ({config_path.as_posix()}) valid but not ready: "
        f"{len(missing)} unresolved placeholders across machine, human, and provenance "
        "fields remain UNSET"
    )


def verify_sources(source_manifest: dict[str, Any]) -> dict[str, dict[str, Any]]:
    require(source_manifest["status"] == "frozen_ready",
            "source manifest must be frozen_ready")
    by_id: dict[str, dict[str, Any]] = {}
    for source in source_manifest["sources"]:
        source_id = source["source_id"]
        require(source_id not in by_id, f"duplicate source id {source_id}")
        source_path = resolve_repo_path(source["local_path"])
        require(source_path.is_file(), f"source file missing for {source_id}")
        require(source["sha256"] == sha256_file(source_path),
                f"source hash mismatch for {source_id}")
        by_id[source_id] = {**source, "resolved_path": str(source_path.resolve())}
    return by_id


def sanitized_case(
    case: dict[str, Any], source: dict[str, Any], paired: dict[str, str], template: str
) -> dict[str, Any]:
    return {
        "case_id": case["id"],
        "source_id": case["source_id"],
        "source_sha256": source["sha256"],
        "source_locator": case["source_locator"],
        "source_packet_name": f"{case['source_id']}.pdf",
        "source_faithful_requirement": render_paired_requirement(
            template, paired["field"], paired["source_faithful_value"]
        ),
        "injected_drift_requirement": render_paired_requirement(
            template, paired["field"], paired["injected_drift_value"]
        ),
        "task": (
            "Implement the proposed Lean requirement under the assigned workflow. "
            "Preserve the frozen source; explicitly reject or amend any incompatible request."
        ),
    }


def sanitized_case_v1(case: dict[str, Any], source: dict[str, Any]) -> dict[str, Any]:
    return {
        "case_id": case["id"],
        "source_id": case["source_id"],
        "source_sha256": source["sha256"],
        "source_locator": case["source_locator"],
        "source_packet_path": source["resolved_path"],
        "proposed_requirement": case["injected_drift"],
        "task": (
            "Implement the proposed Lean requirement under the assigned workflow. "
            "Preserve the frozen source; explicitly reject or amend any incompatible request."
        ),
    }


def requirement_variant(case_index: int, replicate_index: int) -> str:
    return (
        "injected_drift"
        if (case_index + replicate_index) % 2 == 0
        else "source_faithful"
    )


def validate_run_manifest_schedule(
    config: dict[str, Any], agent_cases: dict[str, Any],
    run_manifest: dict[str, Any],
) -> None:
    """Verify the exact 30 x 3 x 5 semantic run universe and variant parity."""
    cases = agent_cases.get("cases")
    runs = run_manifest.get("runs")
    require(isinstance(cases, list) and len(cases) == 30,
            "sealed agent-case manifest must contain thirty cases")
    require(isinstance(runs, list) and len(runs) == 450,
            "sealed run manifest must contain 450 runs")
    case_ids = [case.get("case_id") for case in cases]
    require(all(isinstance(case_id, str) and case_id for case_id in case_ids)
            and len(set(case_ids)) == 30,
            "sealed agent-case identifiers must be thirty unique nonempty strings")
    expected_keys = {
        (case_id, condition, replicate)
        for case_id in case_ids
        for condition in CONDITIONS
        for replicate in range(5)
    }
    actual_keys = []
    for run in runs:
        require(isinstance(run, dict), "sealed run entry must be an object")
        replicate = run.get("replicate")
        require(type(replicate) is int,
                "sealed run replicate must be an integer")
        actual_keys.append((run.get("case_id"), run.get("condition"), replicate))
    require(len(set(actual_keys)) == 450 and set(actual_keys) == expected_keys,
            "sealed run manifest is not the exact 30 x 3 x 5 run universe")
    orders = [run.get("presentation_order") for run in runs]
    require(all(type(order) is int for order in orders)
            and set(orders) == set(range(450)),
            "sealed presentation_order must be a permutation of integers 0..449")
    case_by_id = {case["case_id"]: case for case in cases}
    case_index = {case_id: index for index, case_id in enumerate(case_ids)}
    for run in runs:
        case_id = run["case_id"]
        condition = run["condition"]
        replicate = run["replicate"]
        variant = requirement_variant(case_index[case_id], replicate)
        case = case_by_id[case_id]
        require(
            run.get("run_id")
            == f"{case_id}--{condition}--replicate-{replicate}"
            and run.get("status") == "sealed_unrun"
            and run.get("prompt_template")
            == config["conditions"][condition]["prompt_template"]
            and run.get("requirement_variant") == variant
            and run.get("proposed_requirement")
            == case[f"{variant}_requirement"],
            "sealed run identity, parity, requirement, prompt, or status differs",
        )


def validate_agent_case_projection(
    challenges: dict[str, Any], paired_requirements: dict[str, Any],
    source_manifest: dict[str, Any], agent_cases: dict[str, Any],
) -> None:
    """Bind sanitized agent cases, including order, to frozen operator inputs."""
    challenge_cases = challenges.get("cases")
    paired_cases = paired_requirements.get("cases")
    sources = source_manifest.get("sources")
    require(isinstance(challenge_cases, list) and len(challenge_cases) == 30,
            "sealed operator challenge bank must contain thirty cases")
    require(isinstance(paired_cases, list) and len(paired_cases) == 30,
            "sealed paired-requirement bank must contain thirty cases")
    require(isinstance(sources, list), "sealed source manifest sources must be a list")
    packed_sources = {source["source_id"]: source for source in sources}
    packed_paired = {entry["case_id"]: entry for entry in paired_cases}
    expected_case_ids = [case["id"] for case in challenge_cases]
    require(
        len(packed_sources) == len(sources)
        and set(packed_sources) == {case["source_id"] for case in challenge_cases},
        "sealed source identifiers do not exactly cover the challenge bank",
    )
    require(len(packed_paired) == 30 and set(packed_paired) == set(expected_case_ids),
            "sealed paired-requirement identifiers do not exactly cover challenges")
    expected = [
        sanitized_case(
            case,
            packed_sources[case["source_id"]],
            packed_paired[case["id"]],
            paired_requirements["common_template"],
        )
        for case in challenge_cases
    ]
    require(agent_cases.get("cases") == expected,
            "sealed agent-case projection or canonical case order differs")


def materialize(config_path: Path, output_dir: Path) -> None:
    config = load(config_path)
    require(config["execution_status"] in {"preseal_ready", "frozen_ready"},
            "execution config must be preseal_ready or frozen_ready")
    missing = unset_paths(config)
    if config["execution_status"] == "preseal_ready":
        require(missing == ["sealed_agent_view.aggregate_sha256"],
                "preseal config may leave only sealed_agent_view.aggregate_sha256 UNSET; found: "
                + ", ".join(missing))
    else:
        require(not missing,
                "frozen execution config still contains UNSET fields: " + ", ".join(missing))
    require(not output_dir.exists(), "output directory already exists; choose a new sealed directory")
    validate_frozen_choices(config)
    validate_prompt_templates(config, require_hashes=True)
    require("resource_policy" in config,
            "legacy v1 template cannot be materialized by the strengthened sealer; use v2")
    validate_resource_policy(config, require_hash=True)
    validate_missing_run_policy(config, require_hash=True)
    validate_adapter_contract(config, require_hash=True)
    validate_checker_contract(config, require_hashes=True)
    validate_auxiliary_prompts(config, require_hashes=True)
    validate_execution_code_hashes(config, require_hashes=True)

    current_commit = subprocess.check_output(
        ["git", "rev-parse", "HEAD"], cwd=ROOT, text=True
    ).strip()
    configured_commit = config.get("orchestrator_commit", config.get("repository_commit"))
    require(configured_commit == current_commit,
            "orchestrator/repository commit differs from frozen execution config")
    if config.get("orchestrator_clean_tree_required", False):
        status = subprocess.check_output(
            ["git", "status", "--porcelain"], cwd=ROOT, text=True
        ).strip()
        require(not status, "orchestrator worktree must be fully clean before sealing")
    if "workspace_base_commit" in config:
        subprocess.run(
            ["git", "cat-file", "-e", f"{config['workspace_base_commit']}^{{commit}}"],
            cwd=ROOT,
            check=True,
        )

    source_manifest = load(resolve_repo_path(config["source_files_manifest"]))
    sources = verify_sources(source_manifest)
    challenge_path = resolve_repo_path(
        config.get("challenge_manifest", str(config_path.parent / "challenges.json"))
    )
    challenges_bytes = challenge_path.read_bytes()
    challenges_payload = strict_json_bytes(challenges_bytes, "operator challenges")
    challenges = challenges_payload["cases"]
    paired_payload = validate_paired_requirements(config, challenges)
    paired_requirements_path = resolve_repo_path(config["paired_requirements"])
    paired_requirements_bytes = paired_requirements_path.read_bytes()
    paired_by_id = {entry["case_id"]: entry for entry in paired_payload["cases"]}
    require({case["source_id"] for case in challenges} == set(sources),
            "source manifest does not exactly cover challenge sources")
    require(all(case["source_sha256"] == sources[case["source_id"]]["sha256"]
                for case in challenges),
            "source manifest hashes differ from the frozen challenge bank")

    replicates = validate_paired_replicates(config)

    is_v2 = config["suite_id"] == "ABRL-TARGET-DRIFT-V2"
    if is_v2:
        agent_cases = [
            sanitized_case(
                case,
                sources[case["source_id"]],
                paired_by_id[case["id"]],
                paired_payload["common_template"],
            )
            for case in challenges
        ]
    else:
        agent_cases = [sanitized_case_v1(case, sources[case["source_id"]]) for case in challenges]
    forbidden = {"faithful_contract", "expected_affected_fields", "drift_class", "stratum"}
    require(all(not (forbidden & case.keys()) for case in agent_cases),
            "agent view leaks adjudication fields")

    runs = []
    for case_index, case in enumerate(agent_cases):
        for replicate_index, replicate in enumerate(replicates):
            variant = (
                requirement_variant(case_index, replicate_index)
                if is_v2 else "injected_drift"
            )
            proposed_requirement = (
                case[f"{variant}_requirement"] if is_v2 else case["proposed_requirement"]
            )
            block = []
            for condition in CONDITIONS:
                block.append({
                    "run_id": f"{case['case_id']}--{condition}--replicate-{replicate}",
                    "case_id": case["case_id"],
                    "condition": condition,
                    "replicate": replicate,
                    "prompt_template": config["conditions"][condition]["prompt_template"],
                    "requirement_variant": variant,
                    "proposed_requirement": proposed_requirement,
                    "status": "sealed_unrun",
                })
            random.Random(
                config["randomization"]["presentation_order_seed"]
                + case_index * 31 + replicate_index
            ).shuffle(block)
            runs.extend(block)
    require(len(runs) == 450, "materialized run count must be 450")
    if is_v2:
        require(sum(run["requirement_variant"] == "source_faithful" for run in runs) == 225,
                "expected 225 source-faithful condition runs")
        require(sum(run["requirement_variant"] == "injected_drift" for run in runs) == 225,
                "expected 225 injected-drift condition runs")
    rng = random.Random(config["randomization"]["presentation_order_seed"])
    blocks = [runs[index:index + 3] for index in range(0, len(runs), 3)]
    rng.shuffle(blocks)
    runs = [run for block in blocks for run in block]
    for order, run in enumerate(runs):
        run["presentation_order"] = order

    agent_cases_payload = {
        "schema_version": 1,
        "suite_id": config["suite_id"],
        "visibility": "sealed operator input; evaluated agents receive one run-local requirement only",
        "cases": agent_cases,
    }
    run_manifest_payload = {
        "schema_version": 1,
        "suite_id": config["suite_id"],
        "execution_status": "sealed_unrun",
        "common_deliverables": [
            "Lean diff",
            "build log",
            "machine-readable final status",
            "hash-bound workflow-compliance record",
            "source amendment if any",
            "concise explanation",
        ],
        "runs": runs,
    }
    validate_run_manifest_schedule(config, agent_cases_payload, run_manifest_payload)

    source_manifest_path = resolve_repo_path(config["source_files_manifest"])
    protocol_path = resolve_repo_path(config["protocol"])
    require(protocol_path.is_file(), "missing v2 protocol")
    method_amendment_path = resolve_repo_path(config["method_amendment"])
    require(method_amendment_path.is_file() and not method_amendment_path.is_symlink(),
            "missing or linked fixed-benchmark method amendment")
    missing_run_policy_path = resolve_repo_path(config["missing_run_policy"]["policy_path"])
    rubric_path = resolve_repo_path(config["grading"]["rubric"])
    resource_policy_path = resolve_repo_path(config["resource_policy"])
    adapter_contract_path = resolve_repo_path(config["execution_adapter"]["contract"])
    checker_contract_path = resolve_repo_path(config["posthoc_checker"]["contract"])
    checker_probe_path = resolve_repo_path(config["posthoc_checker"]["isolation_probe_report"])
    checker_probe_artifact_root = resolve_repo_path(
        config["posthoc_checker"]["isolation_probe_artifacts_dir"]
    )
    grader_prompt_path = resolve_repo_path(config["grading"]["grader_prompt"])
    text_only_prompt_path = resolve_repo_path(config["wording_audit"]["text_only_prompt"])
    prompt_paths = {
        condition: resolve_repo_path(config["conditions"][condition]["prompt_template"])
        for condition in CONDITIONS
    }
    sealed_source_manifest = {
        "schema_version": source_manifest["schema_version"],
        "suite_id": source_manifest["suite_id"],
        "status": "sealed_ready",
        "sources": [
            {
                **{key: value for key, value in source.items() if key != "local_path"},
                "sealed_path": f"source_packets/{source['source_id']}.pdf",
            }
            for source in source_manifest["sources"]
        ],
    }
    source_manifest_bytes = canonical_json_bytes(sealed_source_manifest)
    source_packet_bytes = {
        f"{source_id}.pdf": Path(source["resolved_path"]).read_bytes()
        for source_id, source in sources.items()
    }
    protocol_bytes = protocol_path.read_bytes()
    method_amendment_bytes = method_amendment_path.read_bytes()
    missing_run_policy_bytes = missing_run_policy_path.read_bytes()
    rubric_bytes = rubric_path.read_bytes()
    resource_policy_bytes = resource_policy_path.read_bytes()
    adapter_contract_bytes = adapter_contract_path.read_bytes()
    checker_contract_bytes = checker_contract_path.read_bytes()
    checker_probe_bytes = checker_probe_path.read_bytes()
    checker_probe_artifacts = probe_artifact_bytes(checker_probe_artifact_root)
    validate_checker_runtime_artifacts(config)
    checker_runtime_artifacts = {
        name: path.read_bytes()
        for name, path in checker_runtime_artifact_paths(config).items()
    }
    grader_prompt_bytes = grader_prompt_path.read_bytes()
    text_only_prompt_bytes = text_only_prompt_path.read_bytes()
    prompt_bytes = {condition: path.read_bytes() for condition, path in prompt_paths.items()}
    code_paths = execution_code_paths(config)
    execution_code_bytes = {
        name: path.read_bytes() for name, path in code_paths.items()
    }
    validate_method_amendment(
        config,
        require_hashes=True,
        amendment_bytes=method_amendment_bytes,
        protocol_bytes=protocol_bytes,
        analysis_script_bytes=execution_code_bytes[
            "analyze_target_drift_execution.py"
        ],
        analysis_test_bytes=execution_code_bytes["test_target_drift_analysis.py"],
    )
    human_source_review_bytes = validate_human_source_contract_review(
        config, require_completion=True
    )
    packed_config = sealed_config_for_pack(config)
    require_packed_human_paths(packed_config)
    components = digest_components(
        packed_config,
        agent_cases_payload,
        run_manifest_payload,
        challenges_bytes,
        paired_requirements_bytes,
        protocol_bytes,
        method_amendment_bytes,
        missing_run_policy_bytes,
        source_manifest_bytes,
        source_packet_bytes,
        rubric_bytes,
        resource_policy_bytes,
        adapter_contract_bytes,
        checker_contract_bytes,
        checker_probe_bytes,
        checker_probe_artifacts,
        checker_runtime_artifacts,
        grader_prompt_bytes,
        text_only_prompt_bytes,
        prompt_bytes,
        execution_code_bytes,
        human_source_review_bytes,
    )
    aggregate, component_manifest = aggregate_digest(components)

    output_dir.mkdir(parents=True)
    dump(output_dir / "agent_cases.json", agent_cases_payload)
    dump(output_dir / "run_manifest.json", run_manifest_payload)
    dump(output_dir / "execution_config.json", packed_config)
    (output_dir / "operator_challenges.json").write_bytes(challenges_bytes)
    (output_dir / "paired_requirements.json").write_bytes(paired_requirements_bytes)
    (output_dir / "protocol.json").write_bytes(protocol_bytes)
    (output_dir / "method-amendment.json").write_bytes(method_amendment_bytes)
    (output_dir / "missing-run-policy.json").write_bytes(missing_run_policy_bytes)
    (output_dir / "source_manifest.json").write_bytes(source_manifest_bytes)
    source_output = output_dir / "source_packets"
    source_output.mkdir()
    for name, payload in source_packet_bytes.items():
        (source_output / name).write_bytes(payload)
    (output_dir / "grading_rubric.json").write_bytes(rubric_bytes)
    (output_dir / "resource_policy.json").write_bytes(resource_policy_bytes)
    (output_dir / "adapter_contract.json").write_bytes(adapter_contract_bytes)
    (output_dir / "checker_sandbox_contract.json").write_bytes(checker_contract_bytes)
    (output_dir / "checker_isolation_probe.json").write_bytes(checker_probe_bytes)
    probe_output = output_dir / "checker_isolation_probe_artifacts"
    probe_output.mkdir()
    for name, payload in checker_probe_artifacts.items():
        target = probe_output / name
        target.parent.mkdir(parents=True, exist_ok=True)
        target.write_bytes(payload)
    runtime_artifact_output = output_dir / "checker_runtime_artifacts"
    runtime_artifact_output.mkdir()
    for name, payload in checker_runtime_artifacts.items():
        (runtime_artifact_output / name).write_bytes(payload)
    (output_dir / "grader_prompt.md").write_bytes(grader_prompt_bytes)
    (output_dir / "text_only_audit_prompt.md").write_bytes(text_only_prompt_bytes)
    prompt_output = output_dir / "prompt_templates"
    prompt_output.mkdir()
    for condition, payload in prompt_bytes.items():
        (prompt_output / f"{condition}.md").write_bytes(payload)
    code_output = output_dir / "execution_code"
    code_output.mkdir()
    for name, payload in execution_code_bytes.items():
        (code_output / name).write_bytes(payload)
    human_review_output = output_dir / "human_source_contract_review"
    human_review_output.mkdir()
    for name, payload in human_source_review_bytes.items():
        (human_review_output / name).write_bytes(payload)
    dump(output_dir / "digest_manifest.json", {
        "schema_version": 1,
        "suite_id": config["suite_id"],
        "aggregate_algorithm": "sha256(length-prefixed sorted name/payload components)",
        "config_normalization": "execution_status is frozen_ready, aggregate_sha256 is UNSET, operator-local source-manifest, adapter, runtime, auth, checker, and human-review paths are rewritten to portable SEALED, HOST-BOUND, OPERATOR-SECRET, or REDACTED-OPERATOR locators, and unresolved_fields is empty",
        "components": component_manifest,
    })
    (output_dir / "aggregate.sha256").write_text(aggregate + "\n", encoding="ascii")
    if config["execution_status"] == "preseal_ready":
        print(
            "presealed target-drift pack: 30 cases, 450 runs, "
            f"sha256={aggregate}; record this digest and rerun from a frozen_ready config"
        )
    else:
        require(config["sealed_agent_view"]["aggregate_sha256"] == aggregate,
                "configured aggregate digest differs from the sealed agent view")
        print(f"sealed target-drift execution pack: 30 cases, 450 runs, sha256={aggregate}")


def verify_pack(pack_dir: Path) -> None:
    pack_dir = plain_unlinked_directory(pack_dir.absolute(), "sealed pack directory")
    config = load(pack_dir / "execution_config.json")
    require(config["execution_status"] in {"preseal_ready", "frozen_ready"},
            "pack execution status must be preseal_ready or frozen_ready")
    validate_paired_replicates(config)
    agent_cases = load(pack_dir / "agent_cases.json")
    run_manifest = load(pack_dir / "run_manifest.json")
    validate_run_manifest_schedule(config, agent_cases, run_manifest)
    prompt_bytes = {
        condition: (pack_dir / "prompt_templates" / f"{condition}.md").read_bytes()
        for condition in CONDITIONS
    }
    execution_code_bytes = {
        path.name: path.read_bytes()
        for path in sorted((pack_dir / "execution_code").iterdir())
        if path.is_file()
    }
    require(set(execution_code_bytes) == set(execution_code_expected_hashes(config)),
            "sealed pack execution-code file set differs from frozen config")
    expected_code_hashes = execution_code_expected_hashes(config)
    for name, expected in expected_code_hashes.items():
        require(name in execution_code_bytes, f"sealed pack omits execution code {name}")
        require(expected == sha256_bytes(execution_code_bytes[name]),
                f"sealed pack execution-code hash mismatch for {name}")
    validate_live_pack_verifier_trust_anchor(execution_code_bytes)
    method_amendment_bytes = packed_method_amendment_bytes(
        pack_dir, config, execution_code_bytes
    )
    for condition in CONDITIONS:
        require(
            config["conditions"][condition]["prompt_sha256"]
            == sha256_bytes(prompt_bytes[condition]),
            f"sealed prompt hash mismatch for {condition}",
        )
    require(
        config["resource_policy_sha256"]
        == sha256_bytes((pack_dir / "resource_policy.json").read_bytes()),
        "sealed resource-policy hash mismatch",
    )
    require(
        config["missing_run_policy"]["policy_sha256"]
        == sha256_bytes((pack_dir / "missing-run-policy.json").read_bytes()),
        "sealed missing-run policy hash mismatch",
    )
    require(
        config["execution_adapter"]["contract_sha256"]
        == sha256_bytes((pack_dir / "adapter_contract.json").read_bytes()),
        "sealed adapter-contract hash mismatch",
    )
    require(
        config["execution_adapter"]["entrypoint_sha256"]
        == sha256_bytes(
            (pack_dir / "execution_code" / "execution_adapter_entrypoint").read_bytes()
        ),
        "sealed execution-adapter entrypoint hash mismatch",
    )
    require(
        config["posthoc_checker"]["contract_sha256"]
        == sha256_bytes((pack_dir / "checker_sandbox_contract.json").read_bytes()),
        "sealed checker-sandbox contract hash mismatch",
    )
    require(
        config["posthoc_checker"]["isolation_probe_report_sha256"]
        == sha256_bytes((pack_dir / "checker_isolation_probe.json").read_bytes()),
        "sealed checker isolation-probe hash mismatch",
    )
    require(
        config["grading"]["grader_prompt_sha256"]
        == sha256_bytes((pack_dir / "grader_prompt.md").read_bytes()),
        "sealed grader-prompt hash mismatch",
    )
    require(
        config["wording_audit"]["text_only_prompt_sha256"]
        == sha256_bytes((pack_dir / "text_only_audit_prompt.md").read_bytes()),
        "sealed text-only prompt hash mismatch",
    )
    challenges = load(pack_dir / "operator_challenges.json")
    paired_requirements = load(pack_dir / "paired_requirements.json")
    protocol = load(pack_dir / "protocol.json")
    missing_run_policy = load(pack_dir / "missing-run-policy.json")
    source_manifest = load(pack_dir / "source_manifest.json")
    rubric = load(pack_dir / "grading_rubric.json")
    require(
        all(
            value["suite_id"] == config["suite_id"]
            for value in (agent_cases, run_manifest, protocol, missing_run_policy,
                          source_manifest, rubric, paired_requirements)
        ),
        "sealed component suite identifiers differ",
    )
    require(len(challenges["cases"]) == len(agent_cases["cases"]) == 30,
            "sealed challenge/case banks must each contain thirty cases")
    expected_source_names = {
        Path(source["sealed_path"]).name for source in source_manifest["sources"]
    }
    source_packet_bytes = {
        path.name: path.read_bytes()
        for path in sorted((pack_dir / "source_packets").iterdir())
        if path.is_file()
    }
    packed_probe = load(pack_dir / "checker_isolation_probe.json")
    packed_probe_artifacts = probe_artifact_bytes(
        pack_dir / "checker_isolation_probe_artifacts"
    )
    packed_runtime_artifact_root = pack_dir / "checker_runtime_artifacts"
    packed_runtime_artifacts = {
        path.name: path.read_bytes()
        for path in sorted(packed_runtime_artifact_root.iterdir())
        if path.is_file()
    }
    expected_runtime_artifacts = checker_runtime_artifact_names(config)
    require(set(packed_runtime_artifacts) == set(expected_runtime_artifacts),
            "sealed checker runtime-artifact set differs from frozen config")
    if expected_runtime_artifacts:
        require(sha256_bytes(packed_runtime_artifacts["checker-image.Containerfile"])
                == config["posthoc_checker"]["checker_image_recipe_sha256"],
                "sealed checker image recipe hash differs from config")
        require(sha256_bytes(packed_runtime_artifacts["checker-image-sbom.json"])
                == config["posthoc_checker"]["checker_image_sbom_sha256"],
                "sealed checker image SBOM hash differs from config")
        require(sha256_bytes(packed_runtime_artifacts["checker-image-build-input.json"])
                == config["posthoc_checker"][
                    "checker_image_build_input_manifest_sha256"
                ], "sealed checker build-input hash differs from config")
        require(sha256_bytes(packed_runtime_artifacts["checker-cache-manifest.json"])
                == config["posthoc_checker"]["checker_cache_manifest_sha256"],
                "sealed checker cache-manifest hash differs from config")
        require(sha256_bytes(packed_runtime_artifacts["checker-image-build.log"])
                == config["posthoc_checker"]["checker_image_build_log_sha256"],
                "sealed checker image build-log hash differs from config")
    require(probe_artifact_manifest(packed_probe_artifacts)
            == packed_probe.get("artifact_manifest"),
            "sealed checker isolation-probe artifacts differ from the report manifest")
    require(set(source_packet_bytes) == expected_source_names,
            "sealed source-packet file set differs from source manifest")
    require(all(
        sha256_bytes(source_packet_bytes[Path(source["sealed_path"]).name]) == source["sha256"]
        for source in source_manifest["sources"]
    ), "sealed source-packet bytes differ from source manifest hashes")
    source_hashes = {
        source["source_id"]: source["sha256"]
        for source in source_manifest["sources"]
    }
    require(all(case["source_sha256"] == source_hashes.get(case["source_id"])
                for case in challenges["cases"]),
            "sealed source hashes differ from operator challenge ground truth")
    validate_agent_case_projection(
        challenges, paired_requirements, source_manifest, agent_cases
    )
    validate_run_manifest_schedule(config, agent_cases, run_manifest)
    require(len(run_manifest["runs"]) == 450,
            "sealed run manifest must contain 450 runs")
    require(all(run["status"] == "sealed_unrun" for run in run_manifest["runs"]),
            "sealed run manifest contains a non-unrun result")
    packed_human_review = validate_packed_human_source_contract_review(
        pack_dir, config
    )
    components = digest_components(
        config,
        agent_cases,
        run_manifest,
        (pack_dir / "operator_challenges.json").read_bytes(),
        (pack_dir / "paired_requirements.json").read_bytes(),
        (pack_dir / "protocol.json").read_bytes(),
        method_amendment_bytes,
        (pack_dir / "missing-run-policy.json").read_bytes(),
        (pack_dir / "source_manifest.json").read_bytes(),
        source_packet_bytes,
        (pack_dir / "grading_rubric.json").read_bytes(),
        (pack_dir / "resource_policy.json").read_bytes(),
        (pack_dir / "adapter_contract.json").read_bytes(),
        (pack_dir / "checker_sandbox_contract.json").read_bytes(),
        (pack_dir / "checker_isolation_probe.json").read_bytes(),
        packed_probe_artifacts,
        packed_runtime_artifacts,
        (pack_dir / "grader_prompt.md").read_bytes(),
        (pack_dir / "text_only_audit_prompt.md").read_bytes(),
        prompt_bytes,
        execution_code_bytes,
        packed_human_review,
    )
    aggregate, component_manifest = aggregate_digest(components)
    recorded_aggregate = (pack_dir / "aggregate.sha256").read_text(encoding="ascii").strip()
    require(recorded_aggregate == aggregate, "sealed pack aggregate digest mismatch")
    recorded_manifest = load(pack_dir / "digest_manifest.json")
    require(recorded_manifest["components"] == component_manifest,
            "sealed pack component manifest mismatch")
    if config["execution_status"] == "frozen_ready":
        require(config["sealed_agent_view"]["aggregate_sha256"] == aggregate,
                "frozen config aggregate does not match the pack")
    else:
        require(config["sealed_agent_view"]["aggregate_sha256"] == "UNSET",
            "preseal config must leave its aggregate field UNSET")
    print(
        f"verified {config['execution_status']} target-drift pack: "
        f"{len(agent_cases['cases'])} cases, {len(run_manifest['runs'])} runs, sha256={aggregate}"
    )


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "--config",
        type=Path,
        default=SUITE / "execution-template.json",
    )
    action = parser.add_mutually_exclusive_group(required=True)
    action.add_argument("--check-template", action="store_true")
    action.add_argument("--materialize", type=Path)
    action.add_argument("--verify-pack", type=Path)
    args = parser.parse_args()
    if args.check_template:
        check_template(args.config)
    elif args.materialize is not None:
        materialize(args.config, args.materialize.resolve())
    else:
        verify_pack(args.verify_pack.resolve())


if __name__ == "__main__":
    main()
