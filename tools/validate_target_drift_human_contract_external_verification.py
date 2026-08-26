#!/usr/bin/env python3
"""Validate externally signed identity/qualification attestations for target drift.

OpenSSH signatures prove possession of registered keys and integrity of signed
canonical bytes. Human identity, expertise, independence, and COI status remain
claims attested by the external verifier; they are not cryptographic facts.
"""

from __future__ import annotations

import argparse
import base64
from datetime import datetime, timedelta, timezone
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys
from typing import Any

TOOLS = Path(__file__).resolve().parent
ROOT = TOOLS.parent
sys.path.insert(0, str(TOOLS))

import prepare_target_drift_human_contract_review as review_prepare
import validate_target_drift_human_contract_review as review_validate


DEFAULT_PROTOCOL = (
    ROOT
    / "evaluation/target-drift-v2/"
    "human-source-contract-external-verification-protocol.json"
)
UNSET = "UNSET"
COMPLETED_STATUS = "externally_signed_identity_qualification_attestation_complete"
REGISTRY_STATUS = "allowed_signers_and_roles_preregistered_review_not_started"
RECEIPT_STATUS = "external_attestation_prepared_unsigned"
IDENTIFIER = re.compile(r"[A-Za-z0-9][A-Za-z0-9._@+-]{2,63}")
SHA256_HEX = re.compile(r"[0-9a-f]{64}")
ATTESTATION_STATEMENT = (
    "The external verifier attests that the escrowed evidence was checked for "
    "identity, role-appropriate qualification, independence, and conflicts of "
    "interest before benchmark outcomes were observed."
)
FROZEN_PROTOCOL_CANONICAL_SHA256 = (
    "c3abb7a029b04c3472d4eba7beb9ca07303b64d6713b4567413a9558889412cd"
)


class ExternalVerificationError(RuntimeError):
    pass


def require(condition: bool, message: str) -> None:
    if not condition:
        raise ExternalVerificationError(message)


def reject_duplicate_keys(pairs: list[tuple[str, Any]]) -> dict[str, Any]:
    value: dict[str, Any] = {}
    for key, item in pairs:
        require(key not in value, f"duplicate JSON key: {key}")
        value[key] = item
    return value


def load(path: Path) -> dict[str, Any]:
    require(path.is_file() and not path.is_symlink(), f"missing or linked JSON: {path}")
    value = json.loads(
        path.read_text(encoding="utf-8"), object_pairs_hook=reject_duplicate_keys
    )
    require(isinstance(value, dict), f"{path} must contain one JSON object")
    return value


def canonical_bytes(value: Any) -> bytes:
    return review_prepare.canonical_bytes(value)


def sha256_bytes(value: bytes) -> str:
    return hashlib.sha256(value).hexdigest()


def sha256_file(path: Path) -> str:
    return sha256_bytes(path.read_bytes())


def nonempty(value: Any) -> bool:
    return (
        isinstance(value, str)
        and value == value.strip()
        and bool(value)
        and value != UNSET
    )


def require_identifier(value: Any, label: str) -> str:
    require(nonempty(value) and IDENTIFIER.fullmatch(value) is not None,
            f"{label} must be a 3--64 character ASCII identifier")
    return value.casefold()


def parse_utc(value: Any, label: str) -> datetime:
    require(isinstance(value, str) and re.fullmatch(
        r"\d{4}-\d{2}-\d{2}T\d{2}:\d{2}:\d{2}Z", value
    ) is not None, f"{label} must be UTC RFC3339 seconds ending in Z")
    try:
        parsed = datetime.strptime(value, "%Y-%m-%dT%H:%M:%SZ").replace(
            tzinfo=timezone.utc
        )
    except ValueError as error:
        raise ExternalVerificationError(f"{label} is not a valid UTC timestamp") from error
    return parsed


def public_key_fingerprint(public_key: str) -> str:
    parts = public_key.split(" ")
    require(len(parts) == 2 and parts[0] == "ssh-ed25519",
            "registry public keys must be comment-free ssh-ed25519 keys")
    try:
        blob = base64.b64decode(parts[1], validate=True)
    except (ValueError, TypeError) as error:
        raise ExternalVerificationError("registry public key base64 is invalid") from error
    require(base64.b64encode(blob).decode("ascii") == parts[1],
            "registry public key must use canonical base64 without padding aliases")
    encoded = base64.b64encode(hashlib.sha256(blob).digest()).decode("ascii").rstrip("=")
    return f"SHA256:{encoded}"


def allowed_signers_bytes(
    signers: list[dict[str, Any]], namespace: str
) -> bytes:
    lines = [
        f'{item["principal"]} namespaces="{namespace}" {item["public_key"]}'
        for item in signers
    ]
    return ("\n".join(lines) + "\n").encode("ascii")


def validate_protocol(protocol: dict[str, Any]) -> None:
    require(
        protocol.get("schema_version") == 1
        and protocol.get("protocol_id")
        == "ABRL-TARGET-DRIFT-V2-EXTERNAL-IDENTITY-QUALIFICATION-ATTESTATION"
        and protocol.get("status") == "protocol_frozen_no_real_signers_keys_or_receipts"
        and protocol.get("claim_boundary", {}).get("permitted_completed_status")
        == COMPLETED_STATUS
        and protocol.get("claim_boundary", {}).get("cryptographically_proven_human")
        is False
        and protocol.get("claim_boundary", {}).get("production_execution_eligible")
        is False
        and protocol.get("claim_boundary", {}).get(
            "this_layer_alone_makes_production_execution_eligible"
        ) is False,
        "external-verification protocol identity or claim boundary differs",
    )
    require(
        sha256_bytes(canonical_bytes(protocol)) == FROZEN_PROTOCOL_CANONICAL_SHA256,
        "external-verification protocol differs from the canonical frozen schema",
    )


def validate_registry(
    registry: dict[str, Any], protocol: dict[str, Any], allowed_signers: Path
) -> dict[str, dict[str, Any]]:
    template = protocol["role_registry_template"]
    require(set(registry) == set(template), "role registry top-level schema differs")
    require(
        registry["schema_version"] == 1
        and registry["protocol_id"] == protocol["protocol_id"]
        and registry["status"] == REGISTRY_STATUS
        and registry["evaluation_outcomes_observed"] is False
        and registry["benchmark_execution_complete"] is False,
        "role registry identity, preregistration, or result-free boundary differs",
    )
    parse_utc(registry["registered_at_utc"], "registry.registered_at_utc")
    expected_slots = protocol["required_signer_slots"]
    signers = registry["signers"]
    require(isinstance(signers, list) and len(signers) == 4,
            "role registry must contain exactly four signers")
    require([item.get("slot") for item in signers] == expected_slots,
            "role registry signer slots/order differs")
    expected_roles = protocol["required_registry_roles"]
    by_slot: dict[str, dict[str, Any]] = {}
    principals: set[str] = set()
    pseudonyms: set[str] = set()
    public_keys: set[str] = set()
    fingerprints: set[str] = set()
    for actual, expected in zip(signers, template["signers"]):
        require(set(actual) == set(expected), "role registry signer schema differs")
        slot = actual["slot"]
        principal = require_identifier(actual["principal"], f"registry.{slot}.principal")
        pseudonym = require_identifier(
            actual["pseudonymous_id"], f"registry.{slot}.pseudonymous_id"
        )
        require(actual["registry_role"] == expected_roles[slot],
                f"registry role differs for {slot}")
        require(nonempty(actual["qualification_scope"]),
                f"registry qualification scope is missing for {slot}")
        fingerprint = public_key_fingerprint(actual["public_key"])
        require(actual["public_key_fingerprint"] == fingerprint,
                f"registry public-key fingerprint differs for {slot}")
        require(principal not in principals, "signer principals must be distinct")
        require(pseudonym not in pseudonyms, "signer pseudonymous identities must be distinct")
        require(actual["public_key"] not in public_keys, "signer public keys must be distinct")
        require(fingerprint not in fingerprints,
                "signer public-key fingerprints must be distinct")
        principals.add(principal)
        pseudonyms.add(pseudonym)
        public_keys.add(actual["public_key"])
        fingerprints.add(fingerprint)
        by_slot[slot] = actual
    require(allowed_signers.is_file() and not allowed_signers.is_symlink(),
            "allowed-signers file is missing or linked")
    actual_allowed = allowed_signers.read_bytes()
    require(actual_allowed == allowed_signers_bytes(signers, protocol["signature_namespace"]),
            "allowed-signers bytes differ from the role registry")
    require(registry["allowed_signers_sha256"] == sha256_bytes(actual_allowed),
            "allowed-signers hash differs from the role registry")
    return by_slot


def ssh_keygen_path() -> str:
    executable = shutil.which("ssh-keygen")
    require(executable is not None,
            "OpenSSH ssh-keygen is required for production signature validation")
    return executable


def verify_ssh_signature(
    payload: bytes, signature: Path, allowed_signers: Path,
    principal: str, namespace: str, label: str,
) -> None:
    require(signature.is_file() and not signature.is_symlink(),
            f"{label} detached signature is missing or linked")
    process = subprocess.run(
        [
            ssh_keygen_path(), "-Y", "verify", "-f", str(allowed_signers),
            "-I", principal, "-n", namespace, "-s", str(signature),
        ],
        input=payload,
        stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT,
        check=False,
    )
    require(process.returncode == 0,
            f"{label} OpenSSH signature verification failed")


def validate_receipt_schema(
    receipt: dict[str, Any], protocol: dict[str, Any],
    protocol_path: Path,
    registry: dict[str, Any], by_slot: dict[str, dict[str, Any]],
    allowed_signers: Path, completion: dict[str, Any],
    payloads: dict[str, dict[str, Any]], signatures: dict[str, Path],
) -> None:
    template = protocol["external_receipt_template"]
    require(set(receipt) == set(template), "external receipt top-level schema differs")
    require(
        receipt["schema_version"] == 1
        and receipt["protocol_id"] == protocol["protocol_id"]
        and receipt["status"] == RECEIPT_STATUS
        and receipt["evaluation_outcomes_observed"] is False
        and receipt["benchmark_execution_complete"] is False
        and receipt["cryptographically_proven_human"] is False,
        "external receipt identity, outcome boundary, or crypto claim differs",
    )
    require(nonempty(receipt["receipt_id"]), "external receipt id is missing")
    registered_at = parse_utc(registry["registered_at_utc"], "registry.registered_at_utc")
    verified_at = parse_utc(receipt["verified_at_utc"], "receipt.verified_at_utc")
    require(registered_at < verified_at,
            "role registry must predate external verification")
    require(verified_at <= datetime.now(timezone.utc) + timedelta(minutes=5),
            "external verification timestamp is implausibly in the future")
    require(receipt["protocol_sha256"] == sha256_file(protocol_path),
            "receipt protocol hash differs")
    require(receipt["role_registry_canonical_sha256"]
            == sha256_bytes(canonical_bytes(registry)),
            "receipt role-registry hash differs")
    require(receipt["allowed_signers_sha256"] == sha256_file(allowed_signers),
            "receipt allowed-signers hash differs")
    require(receipt["review_completion_canonical_sha256"]
            == sha256_bytes(canonical_bytes(completion)),
            "receipt review-completion hash differs")
    require(receipt["review_completion_status"] == review_validate.SELF_ATTESTED_STATUS,
            "receipt review-completion status differs")

    signed = receipt["signed_payloads"]
    require(isinstance(signed, dict)
            and set(signed) == {"reviewer_a", "reviewer_b", "adjudicator"},
            "receipt signed-payload slots differ")
    for slot in ("reviewer_a", "reviewer_b", "adjudicator"):
        binding = signed[slot]
        template_binding = template["signed_payloads"][slot]
        signer = by_slot[slot]
        require(set(binding) == set(template_binding),
                f"receipt signed-payload schema differs for {slot}")
        require(
            binding["principal"] == signer["principal"]
            and binding["pseudonymous_id"] == signer["pseudonymous_id"]
            and binding["registry_role"] == signer["registry_role"]
            and binding["canonical_payload_sha256"]
            == sha256_bytes(canonical_bytes(payloads[slot]))
            and binding["detached_signature_sha256"] == sha256_file(signatures[slot]),
            f"receipt signed-payload binding differs for {slot}",
        )

    attestations = receipt["attestations"]
    require(isinstance(attestations, dict)
            and set(attestations) == {"reviewer_a", "reviewer_b", "adjudicator"},
            "receipt attestation slots differ")
    for slot, attestation in attestations.items():
        expected = template["attestations"][slot]
        signer = by_slot[slot]
        require(set(attestation) == set(expected),
                f"receipt attestation schema differs for {slot}")
        require(
            attestation["pseudonymous_id"] == signer["pseudonymous_id"]
            and attestation["registry_role"] == signer["registry_role"]
            and all(
                attestation[field] is True
                for field in (
                    "identity_evidence_checked", "qualification_evidence_checked",
                    "independence_checked", "conflict_of_interest_checked",
                    "private_evidence_escrowed",
                )
            ),
            f"receipt identity/qualification/independence/COI attestation incomplete for {slot}",
        )

    verifier = receipt["external_verifier"]
    expected_verifier = by_slot["external_verifier"]
    require(set(verifier) == set(template["external_verifier"]),
            "external-verifier receipt schema differs")
    require(
        verifier["principal"] == expected_verifier["principal"]
        and verifier["pseudonymous_id"] == expected_verifier["pseudonymous_id"]
        and verifier["registry_role"] == expected_verifier["registry_role"],
        "external-verifier receipt binding differs",
    )
    require(
        isinstance(receipt["public_escrow_reference"], str)
        and receipt["public_escrow_reference"].startswith("https://")
        and len(receipt["public_escrow_reference"]) >= 16,
        "public escrow reference must be a substantive HTTPS reference",
    )
    require(
        isinstance(receipt["public_escrow_receipt_sha256"], str)
        and SHA256_HEX.fullmatch(receipt["public_escrow_receipt_sha256"]) is not None,
        "public escrow receipt must have a lowercase SHA-256",
    )
    require(
        isinstance(receipt["private_escrow_reference"], str)
        and receipt["private_escrow_reference"].startswith("private-escrow:")
        and len(receipt["private_escrow_reference"]) >= 24,
        "private escrow reference must be an opaque private-escrow reference",
    )
    require(receipt["attestation_statement"] == ATTESTATION_STATEMENT,
            "external attestation statement differs")


def validate(
    protocol_path: Path, packet: Path,
    reviewer_a_path: Path, reviewer_a_signature: Path,
    reviewer_b_path: Path, reviewer_b_signature: Path,
    adjudication_path: Path, adjudication_signature: Path,
    completion_path: Path, registry_path: Path, allowed_signers: Path,
    receipt_path: Path, verifier_signature: Path,
    *, review_protocol_path: Path | None = None,
    challenge_path: Path | None = None, paired_path: Path | None = None,
) -> dict[str, Any]:
    protocol = load(protocol_path)
    validate_protocol(protocol)
    registry = load(registry_path)
    by_slot = validate_registry(registry, protocol, allowed_signers)

    reviewer_a = load(reviewer_a_path)
    reviewer_b = load(reviewer_b_path)
    adjudication = load(adjudication_path)
    completion = load(completion_path)
    rebuilt = review_validate.validate(
        packet, reviewer_a_path, reviewer_b_path, adjudication_path,
        protocol_path=review_protocol_path, challenge_path=challenge_path,
        paired_path=paired_path,
    )
    require(completion == rebuilt, "review completion differs from rebuilt review evidence")
    require(
        completion.get("status") == review_validate.SELF_ATTESTED_STATUS
        and completion.get("benchmark_amendment_required") is False
        and completion.get("benchmark_contract_ready_after_external_verification") is True
        and completion.get("external_identity_qualification_verification_required") is True
        and completion.get("independent_human_expert_validation_complete") is False
        and completion.get("production_execution_eligible") is False
        and completion.get("evaluation_outcomes_observed") is False
        and completion.get("benchmark_execution_complete") is False,
        "review completion is amended, overstated, post-outcome, or otherwise ineligible",
    )
    require(
        reviewer_a["reviewer_id"] == by_slot["reviewer_a"]["pseudonymous_id"]
        and reviewer_b["reviewer_id"] == by_slot["reviewer_b"]["pseudonymous_id"]
        and adjudication["adjudicator_id"] == by_slot["adjudicator"]["pseudonymous_id"],
        "review payload identities differ from the preregistered role registry",
    )

    payloads = {
        "reviewer_a": reviewer_a,
        "reviewer_b": reviewer_b,
        "adjudicator": adjudication,
    }
    signatures = {
        "reviewer_a": reviewer_a_signature,
        "reviewer_b": reviewer_b_signature,
        "adjudicator": adjudication_signature,
    }
    namespace = protocol["signature_namespace"]
    for slot in ("reviewer_a", "reviewer_b", "adjudicator"):
        verify_ssh_signature(
            canonical_bytes(payloads[slot]), signatures[slot], allowed_signers,
            by_slot[slot]["principal"], namespace, slot,
        )

    receipt = load(receipt_path)
    validate_receipt_schema(
        receipt, protocol, protocol_path, registry, by_slot, allowed_signers, completion,
        payloads, signatures,
    )
    verify_ssh_signature(
        canonical_bytes(receipt), verifier_signature, allowed_signers,
        by_slot["external_verifier"]["principal"], namespace, "external verifier",
    )
    return {
        "schema_version": 1,
        "protocol_id": protocol["protocol_id"],
        "status": COMPLETED_STATUS,
        "review_completion_canonical_sha256": sha256_bytes(canonical_bytes(completion)),
        "role_registry_canonical_sha256": sha256_bytes(canonical_bytes(registry)),
        "allowed_signers_sha256": sha256_file(allowed_signers),
        "external_receipt_canonical_sha256": sha256_bytes(canonical_bytes(receipt)),
        "external_verifier_signature_sha256": sha256_file(verifier_signature),
        "signed_key_possession_and_payload_integrity_complete": True,
        "external_identity_qualification_independence_coi_attestation_complete": True,
        "cryptographically_proven_human": False,
        "identity_qualification_basis": "external_verifier_signed_attestation",
        "pre_outcome_timing_cryptographically_proven": False,
        "pre_outcome_timing_basis": "external_verifier_signed_attestation_not_trusted_timestamp",
        "production_execution_eligible": False,
        "production_execution_eligible_from_this_layer_alone": False,
        "production_trust_anchor_verified": False,
        "evaluation_outcomes_observed": False,
        "benchmark_execution_complete": False,
        "claim_boundary": (
            "OpenSSH signatures prove registered-key possession and signed-byte integrity. "
            "Human identity, qualification, independence, and COI status rely on the "
            "external verifier's signed attestation and escrowed evidence; they are not "
            "cryptographically proven. This receipt does not establish workflow effectiveness."
        ),
    }


def write_new(path: Path, value: dict[str, Any]) -> None:
    require(not path.exists(), "external-verification output already exists")
    descriptor = os.open(path, os.O_WRONLY | os.O_CREAT | os.O_EXCL, 0o644)
    with os.fdopen(descriptor, "w", encoding="utf-8", newline="\n") as stream:
        json.dump(value, stream, indent=2, sort_keys=True, ensure_ascii=False)
        stream.write("\n")


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--protocol", type=Path, default=DEFAULT_PROTOCOL)
    parser.add_argument("--packet", type=Path, required=True)
    parser.add_argument("--reviewer-a", type=Path, required=True)
    parser.add_argument("--reviewer-a-signature", type=Path, required=True)
    parser.add_argument("--reviewer-b", type=Path, required=True)
    parser.add_argument("--reviewer-b-signature", type=Path, required=True)
    parser.add_argument("--adjudication", type=Path, required=True)
    parser.add_argument("--adjudication-signature", type=Path, required=True)
    parser.add_argument("--review-completion", type=Path, required=True)
    parser.add_argument("--role-registry", type=Path, required=True)
    parser.add_argument("--allowed-signers", type=Path, required=True)
    parser.add_argument("--external-receipt", type=Path, required=True)
    parser.add_argument("--external-verifier-signature", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    result = validate(
        args.protocol.resolve(), args.packet.resolve(),
        args.reviewer_a.resolve(), args.reviewer_a_signature.resolve(),
        args.reviewer_b.resolve(), args.reviewer_b_signature.resolve(),
        args.adjudication.resolve(), args.adjudication_signature.resolve(),
        args.review_completion.resolve(), args.role_registry.resolve(),
        args.allowed_signers.resolve(), args.external_receipt.resolve(),
        args.external_verifier_signature.resolve(),
    )
    write_new(args.output.resolve(), result)
    print(COMPLETED_STATUS)


if __name__ == "__main__":
    main()
