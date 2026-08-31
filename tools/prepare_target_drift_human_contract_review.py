#!/usr/bin/env python3
"""Create a result-free, hash-bound human source-contract review packet."""

from __future__ import annotations

import argparse
import hashlib
import json
import os
from pathlib import Path
from typing import Any


ROOT = Path(__file__).resolve().parents[1]
PROTOCOL = ROOT / "evaluation/target-drift-v2/human-source-contract-review-protocol.json"
UNSET = "UNSET"
CANONICAL_TARGET_CARD_FIELDS = (
    "source_result_label",
    "source_id",
    "source_sha256",
    "source_locator_exact",
    "source_faithful_contract",
    "injected_drift_contract",
    "expected_affected_fields",
    "paired_changed_field",
    "paired_source_faithful_value",
    "paired_injected_drift_value",
)


class ReviewPacketError(RuntimeError):
    pass


def require(condition: bool, message: str) -> None:
    if not condition:
        raise ReviewPacketError(message)


def reject_duplicate_keys(pairs: list[tuple[str, Any]]) -> dict[str, Any]:
    value: dict[str, Any] = {}
    for key, item in pairs:
        require(key not in value, f"duplicate JSON key: {key}")
        value[key] = item
    return value


def load(path: Path) -> dict[str, Any]:
    value = json.loads(
        path.read_text(encoding="utf-8"), object_pairs_hook=reject_duplicate_keys
    )
    require(isinstance(value, dict), f"{path} must contain one JSON object")
    return value


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def canonical_bytes(value: Any) -> bytes:
    return (json.dumps(
        value, sort_keys=True, separators=(",", ":"), ensure_ascii=False
    ) + "\n").encode("utf-8")


def write_new(path: Path, value: Any) -> None:
    payload = canonical_bytes(value)
    descriptor = os.open(path, os.O_WRONLY | os.O_CREAT | os.O_EXCL, 0o644)
    with os.fdopen(descriptor, "wb") as stream:
        stream.write(payload)


def validate_inputs(
    root: Path = ROOT, *, protocol_path: Path | None = None,
    challenge_path: Path | None = None, paired_path: Path | None = None,
) -> tuple[dict[str, Any], list[dict[str, Any]], dict[str, Any]]:
    protocol_path = (
        root / PROTOCOL.relative_to(ROOT) if protocol_path is None else protocol_path
    )
    protocol = load(protocol_path)
    require(
        protocol.get("schema_version") == 1
        and protocol.get("audit_id")
        == "ABRL-TARGET-DRIFT-V2-HUMAN-SOURCE-CONTRACT-REVIEW"
        and protocol.get("status") == "protocol_frozen_review_not_started"
        and protocol.get("evaluation_outcomes_observed") is False,
        "human-review protocol identity or result-free boundary differs",
    )
    scope = protocol["scope"]
    require(
        protocol.get("common_target_card_fields")
        == list(CANONICAL_TARGET_CARD_FIELDS),
        "human-review protocol canonical target-card fields differ",
    )
    completion_gate = protocol.get("completion_gate", {})
    require(
        completion_gate.get("machine_validated_status")
        == (
            "self_attested_review_bundle_complete_"
            "external_identity_qualification_verification_required"
        )
        and completion_gate.get(
            "external_identity_and_qualification_verification_required"
        ) is True
        and completion_gate.get(
            "production_execution_eligible_before_external_verification"
        ) is False,
        "human-review protocol external-verification boundary differs",
    )
    challenge_path = (
        root / scope["challenge_manifest"]
        if challenge_path is None else challenge_path
    )
    paired_path = (
        root / scope["paired_requirements"]
        if paired_path is None else paired_path
    )
    require(sha256(challenge_path) == scope["challenge_manifest_sha256"],
            "challenge manifest differs from the review protocol")
    require(sha256(paired_path) == scope["paired_requirements_sha256"],
            "paired requirements differ from the review protocol")
    challenges = load(challenge_path)["cases"]
    paired = load(paired_path)
    pairs = paired["cases"]
    require(len(challenges) == len(pairs) == scope["case_count"] == 30,
            "review packet must cover exactly thirty cases")
    require([case["id"] for case in challenges] == [case["case_id"] for case in pairs],
            "challenge and paired-requirement order differs")
    require(len({case["source_id"] for case in challenges}) == scope["source_count"] == 4,
            "review packet source count differs")
    require(len({case["id"] for case in challenges}) == 30,
            "review packet case identifiers must be unique")
    require(
        sum(case.get("stratum") == "paper_derived" for case in challenges)
        == scope["paper_derived_case_count"] == 18,
        "paper-derived review count differs",
    )
    require(
        sum(case.get("stratum") != "paper_derived" for case in challenges)
        == scope["textbook_or_evidence_control_case_count"] == 12,
        "textbook/control review count differs",
    )
    return protocol, challenges, paired


def canonical_target_card(
    challenge: dict[str, Any], pair: dict[str, Any]
) -> dict[str, Any]:
    """Return the complete card derivable without inventing source semantics."""
    return {
        "source_result_label": challenge["id"],
        "source_id": challenge["source_id"],
        "source_sha256": challenge["source_sha256"],
        "source_locator_exact": challenge["source_locator"],
        "source_faithful_contract": challenge["faithful_contract"],
        "injected_drift_contract": challenge["injected_drift"],
        "expected_affected_fields": list(challenge["expected_affected_fields"]),
        "paired_changed_field": pair["field"],
        "paired_source_faithful_value": pair["source_faithful_value"],
        "paired_injected_drift_value": pair["injected_drift_value"],
    }


def case_packet(
    challenge: dict[str, Any], pair: dict[str, Any], card_fields: list[str]
) -> dict[str, Any]:
    return {
        "case_id": challenge["id"],
        "source_id": challenge["source_id"],
        "source_sha256": challenge["source_sha256"],
        "current_source_locator": challenge["source_locator"],
        "current_faithful_contract": challenge["faithful_contract"],
        "current_injected_drift": challenge["injected_drift"],
        "expected_affected_fields": challenge["expected_affected_fields"],
        "paired_changed_field": pair["field"],
        "paired_source_faithful_value": pair["source_faithful_value"],
        "paired_injected_drift_value": pair["injected_drift_value"],
        "canonical_frozen_benchmark_card": canonical_target_card(challenge, pair),
        "review": {
            "faithful_contract": UNSET,
            "injected_drift": UNSET,
            "source_locator": UNSET,
            "source_hash_verified": UNSET,
            "complete_common_target_card": {field: UNSET for field in card_fields},
            "confidence_1_to_3": UNSET,
            "rationale": UNSET,
        },
    }


def build_packet(
    root: Path = ROOT, *, protocol_path: Path | None = None,
    challenge_path: Path | None = None, paired_path: Path | None = None,
) -> tuple[dict[str, Any], dict[str, Any], dict[str, Any]]:
    protocol_path = (
        root / PROTOCOL.relative_to(ROOT) if protocol_path is None else protocol_path
    )
    protocol, challenges, paired = validate_inputs(
        root, protocol_path=protocol_path, challenge_path=challenge_path,
        paired_path=paired_path,
    )
    card_fields = protocol["common_target_card_fields"]
    cases = [
        case_packet(challenge, pair, card_fields)
        for challenge, pair in zip(challenges, paired["cases"])
    ]
    reviewer = {
        "schema_version": 1,
        "audit_id": protocol["audit_id"],
        "reviewer_id": UNSET,
        "self_attested_human": UNSET,
        "self_attested_independent_bandit_or_formalization_expert": UNSET,
        "viewed_other_review_before_submission": UNSET,
        "evaluation_outcomes_observed": UNSET,
        "external_identity_qualification_verification_status": "required_not_performed",
        "protocol_sha256": sha256(protocol_path),
        "cases": cases,
    }
    adjudication_cases = []
    for challenge, pair in zip(challenges, paired["cases"]):
        adjudication_cases.append({
            "case_id": challenge["id"],
            "source_id": challenge["source_id"],
            "source_sha256": challenge["source_sha256"],
            "final_changed_field": pair["field"],
            "final_source_faithful_value": pair["source_faithful_value"],
            "final_injected_drift_value": pair["injected_drift_value"],
            "canonical_frozen_benchmark_card": canonical_target_card(challenge, pair),
            "final_decisions": {
                "faithful_contract": UNSET,
                "injected_drift": UNSET,
                "source_locator": UNSET,
            },
            "final_common_target_card": {field: UNSET for field in card_fields},
            "source_contract_valid": UNSET,
            "reviewer_disagreement_present": UNSET,
            "reviewer_disagreement_dimensions": UNSET,
            "reviewer_disagreement_resolved": UNSET,
            "adjudication_rationale": UNSET,
        })
    adjudication = {
        "schema_version": 1,
        "audit_id": protocol["audit_id"],
        "adjudicator_id": UNSET,
        "self_attested_human": UNSET,
        "self_attested_independent_bandit_or_formalization_expert": UNSET,
        "evaluation_outcomes_observed": UNSET,
        "external_identity_qualification_verification_status": "required_not_performed",
        "protocol_sha256": reviewer["protocol_sha256"],
        "reviewer_a_sha256": UNSET,
        "reviewer_b_sha256": UNSET,
        "cases": adjudication_cases,
    }
    manifest = {
        "schema_version": 1,
        "audit_id": protocol["audit_id"],
        "status": "review_packet_prepared_results_absent",
        "evaluation_outcomes_observed": False,
        "protocol_sha256": reviewer["protocol_sha256"],
        "challenge_manifest_sha256": protocol["scope"]["challenge_manifest_sha256"],
        "paired_requirements_sha256": protocol["scope"]["paired_requirements_sha256"],
        "case_count": 30,
        "reviewer_template_canonical_sha256": hashlib.sha256(
            canonical_bytes(reviewer)
        ).hexdigest(),
        "adjudication_template_canonical_sha256": hashlib.sha256(
            canonical_bytes(adjudication)
        ).hexdigest(),
        "claim_boundary": "This packet contains no completed review, externally verified human identity or qualification, benchmark run, grade, or workflow outcome.",
    }
    return manifest, reviewer, adjudication


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    output = args.output.resolve()
    require(not output.exists(), "review output directory already exists")
    require(output.parent.is_dir(), "review output parent is missing")
    manifest, reviewer, adjudication = build_packet()
    output.mkdir(mode=0o700)
    write_new(output / "packet-manifest.json", manifest)
    write_new(output / "reviewer-template.json", reviewer)
    write_new(output / "adjudication-template.json", adjudication)
    print(f"prepared result-free human source-contract review packet: {output}")


if __name__ == "__main__":
    main()
