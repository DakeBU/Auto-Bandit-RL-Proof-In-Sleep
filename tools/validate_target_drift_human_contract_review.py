#!/usr/bin/env python3
"""Fail-closed validation for a self-attested target-drift review bundle.

This module can validate frozen inputs, review consistency, disagreement, and
content hashes. It deliberately cannot certify that an identity is human,
independent, or appropriately qualified; that remains an external gate.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import sys
from typing import Any
import unicodedata

TOOLS = Path(__file__).resolve().parent
sys.path.insert(0, str(TOOLS))

import prepare_target_drift_human_contract_review as prepare


UNSET = "UNSET"
PRODUCTION_DECISIONS = {
    "faithful_contract": "match",
    "injected_drift": "source_critical_change",
    "source_locator": "exact",
}
SELF_ATTESTED_STATUS = (
    "self_attested_review_bundle_complete_"
    "external_identity_qualification_verification_required"
)
IDENTITY_PATTERN = re.compile(r"[A-Za-z0-9][A-Za-z0-9._-]{2,63}")


class HumanReviewError(RuntimeError):
    pass


def require(condition: bool, message: str) -> None:
    if not condition:
        raise HumanReviewError(message)


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


def canonical_sha256(value: Any) -> str:
    return hashlib.sha256(prepare.canonical_bytes(value)).hexdigest()


def nonempty(value: Any) -> bool:
    return (
        isinstance(value, str)
        and value == value.strip()
        and bool(value)
        and value != UNSET
    )


def normalized_identity(value: Any, label: str) -> str:
    require(nonempty(value), f"{label} is missing or untrimmed")
    require(IDENTITY_PATTERN.fullmatch(value) is not None,
            f"{label} must be a 3--64 character ASCII pseudonymous identifier")
    return unicodedata.normalize("NFKC", value).casefold()


def validate_card(card: Any, protocol: dict[str, Any], label: str) -> None:
    fields = protocol["common_target_card_fields"]
    require(isinstance(card, dict) and set(card) == set(fields),
            f"{label} target-card schema differs")
    for field in fields:
        item = card[field]
        if field == "expected_affected_fields":
            require(
                isinstance(item, list)
                and item
                and len(set(item)) == len(item)
                and all(nonempty(value) for value in item),
                f"{label}.{field} must be a nonempty unique string list",
            )
        else:
            require(nonempty(item), f"{label}.{field} is missing or untrimmed")


def validate_reviewer(
    value: dict[str, Any], template: dict[str, Any], protocol: dict[str, Any], label: str
) -> None:
    require(set(value) == set(template), f"{label} top-level schema differs")
    normalized_identity(value["reviewer_id"], f"{label}.reviewer_id")
    require(
        value["self_attested_human"] is True
        and value["self_attested_independent_bandit_or_formalization_expert"] is True
        and value["viewed_other_review_before_submission"] is False
        and value["evaluation_outcomes_observed"] is False
        and value["external_identity_qualification_verification_status"]
        == "required_not_performed"
        and value["protocol_sha256"] == template["protocol_sha256"],
        f"{label} self-attestation, review blindness, or result-free boundary differs",
    )
    decisions = protocol["review_decisions"]
    require(len(value["cases"]) == len(template["cases"]) == 30,
            f"{label} must cover thirty cases")
    for actual, expected in zip(value["cases"], template["cases"]):
        require(set(actual) == set(expected), f"{label} case schema differs")
        for field in set(expected) - {"review"}:
            require(actual[field] == expected[field],
                    f"{label} changed frozen case input {expected['case_id']}.{field}")
        review = actual["review"]
        require(set(review) == set(expected["review"]),
                f"{label} review schema differs for {actual['case_id']}")
        require(review["faithful_contract"] in decisions["faithful_contract"],
                f"{label} faithful decision is invalid")
        require(review["injected_drift"] in decisions["injected_drift"],
                f"{label} drift decision is invalid")
        require(review["source_locator"] in decisions["source_locator"],
                f"{label} locator decision is invalid")
        require(review["source_hash_verified"] is True,
                f"{label} did not self-attest source-hash verification")
        require(isinstance(review["confidence_1_to_3"], int)
                and not isinstance(review["confidence_1_to_3"], bool)
                and 1 <= review["confidence_1_to_3"] <= 3,
                f"{label} confidence is invalid")
        require(nonempty(review["rationale"]), f"{label} rationale is missing")
        validate_card(
            review["complete_common_target_card"], protocol,
            f"{label}.{actual['case_id']}.complete_common_target_card",
        )


def disagreement_dimensions(
    left: dict[str, Any], right: dict[str, Any], protocol: dict[str, Any]
) -> list[str]:
    dimensions = [
        f"decision.{field}"
        for field in PRODUCTION_DECISIONS
        if left["review"][field] != right["review"][field]
    ]
    dimensions.extend(
        f"card.{field}"
        for field in protocol["common_target_card_fields"]
        if left["review"]["complete_common_target_card"][field]
        != right["review"]["complete_common_target_card"][field]
    )
    return sorted(dimensions)


def decision_amendment_reasons(
    reviewer_a: dict[str, Any], reviewer_b: dict[str, Any], final: dict[str, Any]
) -> list[str]:
    reasons: list[str] = []
    for label, review in (
        ("reviewer_a", reviewer_a["review"]),
        ("reviewer_b", reviewer_b["review"]),
        ("adjudicated", final["final_decisions"]),
    ):
        for field, required in PRODUCTION_DECISIONS.items():
            if review[field] != required:
                reasons.append(f"{label}.{field}={review[field]}")
    return reasons


def validate_adjudication(
    value: dict[str, Any], template: dict[str, Any], protocol: dict[str, Any],
    reviewer_a_path: Path, reviewer_b_path: Path,
    reviewer_a: dict[str, Any], reviewer_b: dict[str, Any],
) -> dict[str, Any]:
    require(set(value) == set(template), "adjudication top-level schema differs")
    normalized_identity(value["adjudicator_id"], "adjudication.adjudicator_id")
    require(
        value["self_attested_human"] is True
        and value["self_attested_independent_bandit_or_formalization_expert"] is True
        and value["evaluation_outcomes_observed"] is False
        and value["external_identity_qualification_verification_status"]
        == "required_not_performed"
        and value["protocol_sha256"] == template["protocol_sha256"]
        and value["reviewer_a_sha256"] == sha256(reviewer_a_path)
        and value["reviewer_b_sha256"] == sha256(reviewer_b_path),
        "adjudication self-attestation, review binding, or result-free boundary differs",
    )
    require(len(value["cases"]) == len(template["cases"]) == 30,
            "adjudication must cover thirty cases")
    decisions = protocol["review_decisions"]
    amendment_cases: list[dict[str, Any]] = []
    case_summaries: list[dict[str, Any]] = []
    for actual, expected, left, right in zip(
        value["cases"], template["cases"], reviewer_a["cases"], reviewer_b["cases"]
    ):
        case_id = expected["case_id"]
        require(set(actual) == set(expected), "adjudication case schema differs")
        for field in {
            "case_id", "source_id", "source_sha256", "final_changed_field",
            "final_source_faithful_value", "final_injected_drift_value",
            "canonical_frozen_benchmark_card",
        }:
            require(actual[field] == expected[field],
                    f"adjudication changed frozen benchmark input {case_id}.{field}")
        final_decisions = actual["final_decisions"]
        require(isinstance(final_decisions, dict)
                and set(final_decisions) == set(PRODUCTION_DECISIONS),
                f"adjudication decision schema differs for {case_id}")
        for field in PRODUCTION_DECISIONS:
            require(final_decisions[field] in decisions[field],
                    f"adjudication decision is invalid for {case_id}.{field}")
        validate_card(
            actual["final_common_target_card"], protocol,
            f"adjudication.{case_id}.final_common_target_card",
        )

        computed_dimensions = disagreement_dimensions(left, right, protocol)
        require(actual["reviewer_disagreement_present"] is bool(computed_dimensions),
                f"adjudication disagreement flag differs from reviewer evidence for {case_id}")
        require(actual["reviewer_disagreement_dimensions"] == computed_dimensions,
                f"adjudication disagreement dimensions differ for {case_id}")
        require(actual["reviewer_disagreement_resolved"] is bool(computed_dimensions),
                f"adjudication disagreement resolution differs for {case_id}")
        require(nonempty(actual["adjudication_rationale"]),
                f"adjudication rationale is missing for {case_id}")

        reasons = decision_amendment_reasons(left, right, actual)
        card_matches = (
            actual["final_common_target_card"]
            == expected["canonical_frozen_benchmark_card"]
        )
        if not card_matches:
            reasons.append("final_common_target_card_differs_from_frozen_benchmark")
        computed_valid = not reasons
        require(actual["source_contract_valid"] is computed_valid,
                f"source_contract_valid differs from machine-derived status for {case_id}")
        if reasons:
            amendment_cases.append({"case_id": case_id, "reasons": reasons})
        case_summaries.append({
            "case_id": case_id,
            "reviewer_disagreement_dimensions": computed_dimensions,
            "reviewer_disagreement_resolved": bool(computed_dimensions),
            "frozen_benchmark_card_match": card_matches,
            "machine_derived_source_contract_valid": computed_valid,
        })
    return {
        "amendment_cases": amendment_cases,
        "case_summaries": case_summaries,
    }


def validate(
    packet: Path, reviewer_a: Path, reviewer_b: Path, adjudication: Path,
    *, root: Path = prepare.ROOT, protocol_path: Path | None = None,
    challenge_path: Path | None = None, paired_path: Path | None = None,
) -> dict[str, Any]:
    protocol, _, _ = prepare.validate_inputs(
        root, protocol_path=protocol_path, challenge_path=challenge_path,
        paired_path=paired_path,
    )
    expected_manifest, reviewer_template, adjudication_template = prepare.build_packet(
        root, protocol_path=protocol_path, challenge_path=challenge_path,
        paired_path=paired_path,
    )
    manifest = load(packet / "packet-manifest.json")
    template_on_disk = load(packet / "reviewer-template.json")
    adjudication_template_on_disk = load(packet / "adjudication-template.json")
    require(manifest == expected_manifest, "review packet manifest differs")
    require(template_on_disk == reviewer_template, "reviewer template differs")
    require(adjudication_template_on_disk == adjudication_template,
            "adjudication template differs")
    require(
        manifest["reviewer_template_canonical_sha256"]
        == canonical_sha256(template_on_disk),
        "reviewer template canonical hash differs",
    )
    require(
        manifest["adjudication_template_canonical_sha256"]
        == canonical_sha256(adjudication_template_on_disk),
        "adjudication template canonical hash differs",
    )
    left = load(reviewer_a)
    right = load(reviewer_b)
    validate_reviewer(left, reviewer_template, protocol, "reviewer A")
    validate_reviewer(right, reviewer_template, protocol, "reviewer B")
    left_identity = normalized_identity(left["reviewer_id"], "reviewer A identity")
    right_identity = normalized_identity(right["reviewer_id"], "reviewer B identity")
    require(left_identity != right_identity,
            "self-attested reviewer identities must be distinct after normalization")
    final = load(adjudication)
    adjudication_summary = validate_adjudication(
        final, adjudication_template, protocol, reviewer_a, reviewer_b, left, right
    )
    adjudicator_identity = normalized_identity(
        final["adjudicator_id"], "adjudicator identity"
    )
    require(adjudicator_identity not in {left_identity, right_identity},
            "self-attested adjudicator identity must differ from both reviewers")

    amendment_cases = adjudication_summary["amendment_cases"]
    amendment_required = bool(amendment_cases)
    status = "benchmark_amendment_required" if amendment_required else SELF_ATTESTED_STATUS
    final_cards = {
        item["case_id"]: {
            "source_id": item["source_id"],
            "source_sha256": item["source_sha256"],
            "common_target_card": item["final_common_target_card"],
            "changed_field": item["final_changed_field"],
            "source_faithful_value": item["final_source_faithful_value"],
            "injected_drift_value": item["final_injected_drift_value"],
        }
        for item in final["cases"]
    }
    return {
        "schema_version": 2,
        "audit_id": protocol["audit_id"],
        "status": status,
        "self_attested_review_bundle_complete": True,
        "independent_human_expert_validation_complete": False,
        "external_identity_qualification_verification_required": True,
        "external_identity_qualification_verification_status": "required_not_performed",
        "production_execution_eligible": False,
        "benchmark_contract_ready_after_external_verification": not amendment_required,
        "benchmark_amendment_required": amendment_required,
        "benchmark_amendment_cases": amendment_cases,
        "evaluation_outcomes_observed": False,
        "benchmark_execution_complete": False,
        "workflow_effectiveness_supported": False,
        "reviewer_ids": [left["reviewer_id"], right["reviewer_id"]],
        "adjudicator_id": final["adjudicator_id"],
        "protocol_sha256": reviewer_template["protocol_sha256"],
        "packet_manifest_sha256": sha256(packet / "packet-manifest.json"),
        "reviewer_a_sha256": sha256(reviewer_a),
        "reviewer_b_sha256": sha256(reviewer_b),
        "adjudication_sha256": sha256(adjudication),
        "case_count": 30,
        "machine_checked_all_case_contracts_match_frozen_benchmark": not amendment_required,
        "all_disagreements_machine_computed_and_resolved": True,
        "case_review_summary": adjudication_summary["case_summaries"],
        "final_target_cards": final_cards,
        "claim_boundary": (
            "Repository checks establish only a self-attested, hash-bound review bundle. "
            "External identity, independence, and qualification verification is required "
            "before production execution; this is not evidence of workflow effectiveness "
            "or validation of the full library."
        ),
    }


def write_new(path: Path, value: Any) -> None:
    require(not path.exists(), "validation output already exists")
    descriptor = os.open(path, os.O_WRONLY | os.O_CREAT | os.O_EXCL, 0o644)
    with os.fdopen(descriptor, "w", encoding="utf-8", newline="\n") as stream:
        json.dump(value, stream, indent=2, sort_keys=True, ensure_ascii=False)
        stream.write("\n")


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--packet", type=Path, required=True)
    parser.add_argument("--reviewer-a", type=Path, required=True)
    parser.add_argument("--reviewer-b", type=Path, required=True)
    parser.add_argument("--adjudication", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    result = validate(
        args.packet.resolve(), args.reviewer_a.resolve(), args.reviewer_b.resolve(),
        args.adjudication.resolve(),
    )
    write_new(args.output.resolve(), result)
    print(result["status"])


if __name__ == "__main__":
    main()
