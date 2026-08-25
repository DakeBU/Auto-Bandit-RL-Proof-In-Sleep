#!/usr/bin/env python3
"""Fail-closed validation for the paper-source contract pre-audit."""

from __future__ import annotations

from collections import Counter
import hashlib
import json
import math
from pathlib import Path
import subprocess
from typing import Any


ROOT = Path(__file__).resolve().parents[1]
AUDIT_REL = Path("evaluation/source-contract-audit-v1")
CHALLENGES_REL = Path("evaluation/target-drift-v1/challenges.json")
PAIRED_REL = Path("evaluation/target-drift-v2/paired-requirements.json")
AUDIT_ID = "ABRL-PAPER-SOURCE-CONTRACT-PREAUDIT-V1"
AMENDMENT_ID = (
    "ABRL-TARGET-DRIFT-PREEXEC-SOURCE-CONTRACT-AMENDMENT-2026-08-26"
)
EXPECTED_REVIEWER_IDS = ("ai-reviewer-a", "ai-reviewer-b")
EXPECTED_BASE_COMMIT = "705dfe1ab1b8e0d318097981a7322336686dd5c8"
EXPECTED_BASE_SNAPSHOTS = {
    "challenge_manifest": {
        "repository_path": "evaluation/target-drift-v1/challenges.json",
        "snapshot_path": (
            "evaluation/source-contract-audit-v1/pre-amendment/"
            "target-drift-v1-challenges.json"
        ),
        "git_blob_sha1": "0537c8e69233b46c27233323815d782962fef392",
        "sha256": (
            "ce9b7b00941e5ffdc70ada3c6104d20c"
            "ef446e70c1bfa162bb1b79e37d830fc6"
        ),
    },
    "paired_requirements": {
        "repository_path": "evaluation/target-drift-v2/paired-requirements.json",
        "snapshot_path": (
            "evaluation/source-contract-audit-v1/pre-amendment/"
            "target-drift-v2-paired-requirements.json"
        ),
        "git_blob_sha1": "18181fcdebff02bf840485004a8289cf12e140f9",
        "sha256": (
            "be11f20759eed85492a20c1a16b20f731"
            "7210494ed141b4d151ba7ee323e2bcd"
        ),
    },
}
DIMENSIONS = {
    "faithful_contract": (("match", "mismatch", "unclear"), "match"),
    "injected_drift": (
        ("source_critical_change", "not_critical", "unclear"),
        "source_critical_change",
    ),
    "source_locator": (("correct", "imprecise", "wrong"), "correct"),
}


class AuditError(RuntimeError):
    """Raised when a tracked audit invariant fails."""


def require(condition: bool, message: str) -> None:
    if not condition:
        raise AuditError(message)


def require_exact_keys(
    payload: dict[str, Any], expected: set[str], label: str
) -> None:
    actual = set(payload)
    require(
        actual == expected,
        f"{label}: key schema differs; missing={sorted(expected - actual)}, "
        f"extra={sorted(actual - expected)}",
    )


def load_json(path: Path) -> dict[str, Any]:
    value = json.loads(path.read_text(encoding="utf-8"))
    require(isinstance(value, dict), f"{path} must contain one JSON object")
    return value


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def git_blob_sha1(path: Path) -> str:
    payload = path.read_bytes()
    header = f"blob {len(payload)}\0".encode("ascii")
    return hashlib.sha1(header + payload).hexdigest()


def assert_close(actual: float, expected: float, label: str) -> None:
    require(
        math.isclose(actual, expected, rel_tol=0.0, abs_tol=1e-12),
        f"{label}: expected {expected}, got {actual}",
    )


def categorical_counts(records: list[dict[str, Any]], field: str) -> Counter[str]:
    return Counter(str(record[field]) for record in records)


def agreement_metrics(
    left: list[dict[str, Any]],
    right: list[dict[str, Any]],
    field: str,
    categories: tuple[str, str, str],
    positive: str,
) -> dict[str, float | int | None]:
    require(len(left) == len(right) and left, f"{field}: paired records required")
    n = len(left)
    left_values = [str(item[field]) for item in left]
    right_values = [str(item[field]) for item in right]
    require(
        all(value in categories for value in left_values + right_values),
        f"{field}: unknown category",
    )
    agreement_count = sum(a == b for a, b in zip(left_values, right_values))
    raw = agreement_count / n
    pooled = Counter(left_values + right_values)
    proportions = {category: pooled[category] / (2 * n) for category in categories}
    chance_ac1 = sum(
        proportion * (1.0 - proportion) for proportion in proportions.values()
    ) / (len(categories) - 1)
    gwet_ac1 = (raw - chance_ac1) / (1.0 - chance_ac1)

    left_positive = sum(value == positive for value in left_values)
    right_positive = sum(value == positive for value in right_values)
    both_positive = sum(
        a == positive and b == positive for a, b in zip(left_values, right_values)
    )
    positive_agreement = (2.0 * both_positive) / (left_positive + right_positive)
    left_negative = n - left_positive
    right_negative = n - right_positive
    both_negative = sum(
        a != positive and b != positive for a, b in zip(left_values, right_values)
    )
    negative_denominator = left_negative + right_negative
    negative_agreement = (
        (2.0 * both_negative) / negative_denominator
        if negative_denominator
        else None
    )

    left_counts = Counter(left_values)
    right_counts = Counter(right_values)
    expected_kappa = sum(
        (left_counts[category] / n) * (right_counts[category] / n)
        for category in categories
    )
    kappa = (
        (raw - expected_kappa) / (1.0 - expected_kappa)
        if len(left_counts) > 1 and len(right_counts) > 1 and expected_kappa < 1.0
        else None
    )
    return {
        "agreement_count": agreement_count,
        "raw_agreement": raw,
        "gwet_ac1": gwet_ac1,
        "cohen_kappa": kappa,
        "positive_agreement": positive_agreement,
        "negative_agreement": negative_agreement,
    }


def compare_count_block(
    actual: Counter[str],
    expected: dict[str, Any],
    label: str,
    categories: tuple[str, ...],
) -> None:
    require(set(actual) <= set(categories), f"{label}: unexpected category")
    require(set(expected) == set(categories), f"{label}: category schema differs")
    for category in categories:
        count = expected[category]
        require(actual[category] == count, f"{label}.{category}: count differs")


def indexed_cases(payload: dict[str, Any], id_field: str, label: str) -> dict[str, dict[str, Any]]:
    records = payload.get("cases")
    require(isinstance(records, list), f"{label}: cases must be a list")
    ids = [str(record[id_field]) for record in records]
    require(len(ids) == len(set(ids)), f"{label}: duplicate case ID")
    return {case_id: record for case_id, record in zip(ids, records)}


def verify_base_commit_when_available(
    root: Path, commit: str, repository_path: str, expected_sha256: str
) -> None:
    if not (root / ".git").exists():
        return
    try:
        payload = subprocess.check_output(
            ["git", "-C", str(root), "show", f"{commit}:{repository_path}"],
            stderr=subprocess.STDOUT,
        )
    except (OSError, subprocess.CalledProcessError) as error:
        raise AuditError(
            f"pre-amendment base: cannot read {repository_path} at {commit}"
        ) from error
    require(
        hashlib.sha256(payload).hexdigest() == expected_sha256,
        f"pre-amendment base: {repository_path} differs from commit {commit}",
    )


def validate(root: Path = ROOT) -> None:
    audit_dir = root / AUDIT_REL
    protocol = load_json(audit_dir / "protocol.json")
    reviewer_a = load_json(audit_dir / "reviewer-a.json")
    reviewer_b = load_json(audit_dir / "reviewer-b.json")
    adjudication = load_json(audit_dir / "adjudication.json")
    summary = load_json(audit_dir / "summary.json")
    amendment = load_json(audit_dir / "amendment.json")
    challenges = load_json(root / CHALLENGES_REL)
    paired = load_json(root / PAIRED_REL)

    require_exact_keys(
        protocol,
        {
            "schema_version",
            "audit_id",
            "conducted_on",
            "status",
            "protocol_timing",
            "scope",
            "sources",
            "review_design",
            "adjudication_design",
            "claim_boundary",
            "required_human_followup",
        },
        "protocol",
    )
    reviewer_top_keys = {
        "schema_version",
        "audit_id",
        "reviewer_id",
        "reviewer_type",
        "human",
        "independent_human_expert",
        "viewed_other_review_before_submission",
        "source_hashes_verified",
        "evaluated_outcomes_observed",
        "cases",
    }
    require_exact_keys(reviewer_a, reviewer_top_keys, "reviewer-a")
    require_exact_keys(reviewer_b, reviewer_top_keys, "reviewer-b")
    require_exact_keys(
        adjudication,
        {
            "schema_version",
            "audit_id",
            "adjudicator_id",
            "human",
            "independent_human_expert",
            "source_pdf_reinspection",
            "evaluated_outcomes_observed",
            "cases",
        },
        "adjudication",
    )
    require_exact_keys(
        summary,
        {
            "schema_version",
            "audit_id",
            "status",
            "case_count",
            "source_count",
            "reviewer_counts",
            "agreement",
            "adjudicated_original_contracts",
            "per_source_adjudicated_original",
            "pre_execution_amendment",
            "claim_boundary",
        },
        "summary",
    )
    require_exact_keys(
        amendment,
        {
            "schema_version",
            "amendment_id",
            "amended_on",
            "reason",
            "timing_and_claim_boundary",
            "pre_amendment_base",
            "primary_inputs",
            "metadata_changes",
            "case_changes",
            "derived_bindings_after",
        },
        "amendment",
    )

    for label, payload in (
        ("protocol", protocol),
        ("reviewer-a", reviewer_a),
        ("reviewer-b", reviewer_b),
        ("adjudication", adjudication),
        ("summary", summary),
    ):
        require(payload.get("schema_version") == 1, f"{label}: schema differs")
        require(payload.get("audit_id") == AUDIT_ID, f"{label}: audit ID differs")
    require(amendment.get("schema_version") == 1, "amendment: schema differs")
    require(
        amendment.get("amendment_id") == AMENDMENT_ID,
        "amendment: amendment ID differs",
    )

    require(
        protocol.get("status")
        == "ai_assisted_pre_audit_complete_human_expert_validation_pending",
        "protocol: status overstates evidence",
    )
    require(
        summary.get("status")
        == "ai_assisted_pre_audit_complete_human_expert_validation_pending",
        "summary: status overstates evidence",
    )
    claim = protocol.get("claim_boundary", {})
    require(isinstance(claim, dict), "protocol: claim boundary must be an object")
    require_exact_keys(
        claim,
        {
            "independent_human_expert_validation_complete",
            "evaluation_outcomes_present",
            "may_be_described_as",
            "must_not_be_described_as",
        },
        "protocol.claim_boundary",
    )
    require(
        claim.get("independent_human_expert_validation_complete") is False,
        "protocol: human validation must remain pending",
    )
    require(
        claim.get("evaluation_outcomes_present") is False,
        "protocol: evaluation outcomes must remain absent",
    )
    require(
        claim.get("may_be_described_as")
        == "dual-instance AI-assisted paper-source pre-audit",
        "protocol: permitted description differs",
    )
    forbidden_claims = claim.get("must_not_be_described_as")
    require(
        isinstance(forbidden_claims, list)
        and {
            "independent expert validation",
            "human validation",
            "target-drift benchmark result",
            "workflow effectiveness evidence",
        }.issubset(set(forbidden_claims)),
        "protocol: forbidden descriptions are incomplete",
    )

    review_design = protocol.get("review_design", {})
    require(
        isinstance(review_design, dict),
        "protocol: review design must be an object",
    )
    require_exact_keys(
        review_design,
        {
            "reviewer_count",
            "reviewer_ids",
            "reviewer_type",
            "same_system_class",
            "reviewers_blind_to_each_other",
            "external_provider_called",
            "human_expert_reviewer_count",
            "dimensions",
            "confidence_scale",
        },
        "protocol.review_design",
    )
    require(
        review_design.get("reviewer_count") == len(EXPECTED_REVIEWER_IDS) == 2,
        "protocol: reviewer count differs",
    )
    require(
        review_design.get("reviewer_ids") == list(EXPECTED_REVIEWER_IDS),
        "protocol: reviewer IDs differ",
    )
    require(
        review_design.get("reviewer_type") == "isolated_ai_reviewer_instances"
        and review_design.get("same_system_class") is True
        and review_design.get("reviewers_blind_to_each_other") is True,
        "protocol: reviewer isolation or blinding differs",
    )
    require(
        review_design.get("external_provider_called") is False
        and review_design.get("human_expert_reviewer_count") == 0,
        "protocol: provider or human-review boundary differs",
    )
    require(
        review_design.get("dimensions") == list(DIMENSIONS),
        "protocol: review dimensions differ",
    )
    confidence_scale = review_design.get("confidence_scale")
    require(
        isinstance(confidence_scale, dict),
        "protocol: confidence scale must be an object",
    )
    require_exact_keys(
        confidence_scale,
        {"1", "2", "3"},
        "protocol.review_design.confidence_scale",
    )
    adjudication_design = protocol.get("adjudication_design", {})
    require(
        isinstance(adjudication_design, dict),
        "protocol: adjudication design must be an object",
    )
    require_exact_keys(
        adjudication_design,
        {
            "adjudicator_type",
            "source_pdf_reinspection",
            "voting_rule",
            "outcomes_observed_before_adjudication",
        },
        "protocol.adjudication_design",
    )
    require(
        adjudication_design.get("adjudicator_type")
        == "primary_ai_assisted_agent"
        and adjudication_design.get("source_pdf_reinspection") is True
        and adjudication_design.get("outcomes_observed_before_adjudication")
        is False,
        "protocol: adjudication boundary differs",
    )

    require(
        protocol.get("protocol_timing")
        == "post_hoc_record_of_the_completed_pre_audit_not_a_preregistration",
        "protocol: timing label differs",
    )
    base_ref = amendment.get("pre_amendment_base", {})
    require(
        isinstance(base_ref, dict),
        "amendment: pre-amendment base must be an object",
    )
    require_exact_keys(
        base_ref,
        {"manifest_path", "manifest_sha256", "base_git_commit"},
        "amendment.pre_amendment_base",
    )
    require(
        base_ref.get("manifest_path")
        == "evaluation/source-contract-audit-v1/pre-amendment/base.json",
        "amendment: pre-amendment manifest path differs",
    )
    base_manifest_path = root / Path(base_ref["manifest_path"])
    require(base_manifest_path.is_file(), "amendment: pre-amendment manifest missing")
    require(
        sha256(base_manifest_path) == base_ref.get("manifest_sha256"),
        "amendment: pre-amendment manifest hash differs",
    )
    base = load_json(base_manifest_path)
    require_exact_keys(
        base,
        {"schema_version", "amendment_id", "base_git_commit", "snapshots"},
        "pre-amendment base",
    )
    require(base.get("schema_version") == 1, "pre-amendment base: schema differs")
    require(
        base.get("amendment_id") == AMENDMENT_ID,
        "pre-amendment base: amendment ID differs",
    )
    require(
        base.get("base_git_commit")
        == base_ref.get("base_git_commit")
        == EXPECTED_BASE_COMMIT,
        "pre-amendment base: Git commit differs",
    )
    primary = amendment.get("primary_inputs")
    require(
        isinstance(primary, dict)
        and set(primary) == {"challenge_manifest", "paired_requirements"},
        "amendment: primary input schema differs",
    )
    for name, entry in primary.items():
        require(
            isinstance(entry, dict),
            f"amendment.primary_inputs.{name}: must be an object",
        )
        require_exact_keys(
            entry,
            {"path", "before_sha256", "after_sha256"},
            f"amendment.primary_inputs.{name}",
        )
    base_snapshots = base.get("snapshots")
    require(
        isinstance(base_snapshots, dict)
        and set(base_snapshots) == set(primary),
        "pre-amendment base: snapshot set differs",
    )
    snapshot_payloads: dict[str, dict[str, Any]] = {}
    for name, expected_snapshot in EXPECTED_BASE_SNAPSHOTS.items():
        snapshot = base_snapshots[name]
        require(
            isinstance(snapshot, dict),
            f"pre-amendment base: {name} must be an object",
        )
        require_exact_keys(
            snapshot,
            {"repository_path", "snapshot_path", "git_blob_sha1", "sha256"},
            f"pre-amendment base.{name}",
        )
        require(
            snapshot == expected_snapshot,
            f"pre-amendment base: {name} manifest entry differs",
        )
        repository_path = expected_snapshot["repository_path"]
        snapshot_rel = expected_snapshot["snapshot_path"]
        snapshot_path = root / Path(snapshot_rel)
        require(snapshot_path.is_file(), f"pre-amendment base: {name} missing")
        require(
            sha256(snapshot_path) == snapshot.get("sha256"),
            f"pre-amendment base: {name} SHA-256 differs",
        )
        require(
            git_blob_sha1(snapshot_path) == snapshot.get("git_blob_sha1"),
            f"pre-amendment base: {name} Git blob differs",
        )
        primary_entry = primary[name]
        require(
            primary_entry.get("path") == repository_path
            and primary_entry.get("before_sha256") == snapshot.get("sha256"),
            f"amendment: {name} before-state binding differs",
        )
        current_path = root / Path(repository_path)
        require(current_path.is_file(), f"amendment: missing {repository_path}")
        require(
            sha256(current_path) == primary_entry.get("after_sha256"),
            f"amendment: {repository_path} after hash differs",
        )
        require(
            primary_entry.get("before_sha256") != primary_entry.get("after_sha256"),
            f"amendment: {name} does not record a change",
        )
        verify_base_commit_when_available(
            root,
            EXPECTED_BASE_COMMIT,
            repository_path,
            str(snapshot.get("sha256")),
        )
        snapshot_payloads[name] = load_json(snapshot_path)

    paper_cases = [
        case for case in challenges.get("cases", [])
        if case.get("stratum") == "paper_derived"
    ]
    require(len(paper_cases) == 18, "challenge manifest: expected 18 paper cases")
    case_ids = [str(case["id"]) for case in paper_cases]
    require(len(set(case_ids)) == 18, "challenge manifest: paper IDs not unique")
    scope = protocol.get("scope", {})
    require(isinstance(scope, dict), "protocol: scope must be an object")
    require_exact_keys(
        scope,
        {
            "challenge_manifest_path",
            "challenge_manifest_before_sha256",
            "stratum",
            "case_count",
            "source_count",
        },
        "protocol.scope",
    )
    require(
        scope.get("challenge_manifest_path") == CHALLENGES_REL.as_posix()
        and scope.get("challenge_manifest_before_sha256")
        == primary["challenge_manifest"]["before_sha256"]
        and scope.get("stratum") == "paper_derived"
        and scope.get("case_count") == len(case_ids) == 18
        and scope.get("source_count") == 3,
        "protocol: scope differs from bound inputs",
    )
    require(
        summary.get("case_count") == len(case_ids)
        and summary.get("source_count") == scope.get("source_count"),
        "summary: case or source count differs",
    )
    require(
        [entry.get("case_id") for entry in paired.get("cases", [])[:18]] == case_ids,
        "paired requirements: first 18 IDs differ from paper-case order",
    )
    pre_challenges = snapshot_payloads["challenge_manifest"]
    pre_paired = snapshot_payloads["paired_requirements"]
    pre_challenge_index = indexed_cases(
        pre_challenges, "id", "pre-amendment challenge manifest"
    )
    current_challenge_index = indexed_cases(
        challenges, "id", "current challenge manifest"
    )
    pre_paired_index = indexed_cases(
        pre_paired, "case_id", "pre-amendment paired requirements"
    )
    current_paired_index = indexed_cases(
        paired, "case_id", "current paired requirements"
    )
    require(
        all(case_id in pre_challenge_index for case_id in case_ids)
        and all(case_id in pre_paired_index for case_id in case_ids),
        "pre-amendment base: paper-case membership differs",
    )
    for case_id in case_ids:
        require(
            pre_challenge_index[case_id].get("source_id")
            == current_challenge_index[case_id].get("source_id")
            and pre_challenge_index[case_id].get("source_sha256")
            == current_challenge_index[case_id].get("source_sha256"),
            f"{case_id}: source identity changed during amendment",
        )

    protocol_sources = protocol.get("sources")
    require(isinstance(protocol_sources, list), "protocol: sources must be a list")
    for index, entry in enumerate(protocol_sources):
        require(
            isinstance(entry, dict),
            f"protocol.sources[{index}]: must be an object",
        )
        require_exact_keys(
            entry,
            {"source_id", "sha256", "case_count"},
            f"protocol.sources[{index}]",
        )
    source_specs = {entry["source_id"]: entry for entry in protocol_sources}
    require(len(source_specs) == 3, "protocol: expected three paper sources")
    require(
        len(protocol_sources) == len(source_specs),
        "protocol: duplicate paper source",
    )
    source_case_counts = Counter(str(case["source_id"]) for case in paper_cases)
    for case in paper_cases:
        spec = source_specs.get(str(case["source_id"]))
        require(spec is not None, f"{case['id']}: source absent from protocol")
        require(
            case.get("source_sha256") == spec.get("sha256"),
            f"{case['id']}: source hash differs",
        )
    for source_id, spec in source_specs.items():
        require(
            source_case_counts[source_id] == spec.get("case_count") == 6,
            f"{source_id}: expected six cases",
        )
        source_hashes = {
            str(case["source_sha256"])
            for case in paper_cases
            if case["source_id"] == source_id
        }
        require(
            source_hashes == {spec.get("sha256")},
            f"{source_id}: source SHA-256 is not uniquely bound",
        )

    reviewers: dict[str, list[dict[str, Any]]] = {}
    for label, expected_id, payload in (
        ("reviewer_a", EXPECTED_REVIEWER_IDS[0], reviewer_a),
        ("reviewer_b", EXPECTED_REVIEWER_IDS[1], reviewer_b),
    ):
        require(
            payload.get("reviewer_id") == expected_id
            and payload.get("reviewer_type") == "isolated_ai_assisted_instance",
            f"{label}: reviewer identity or type differs",
        )
        require(payload.get("human") is False, f"{label}: must be labeled nonhuman")
        require(
            payload.get("independent_human_expert") is False,
            f"{label}: must not claim expert independence",
        )
        require(
            payload.get("viewed_other_review_before_submission") is False,
            f"{label}: blinding flag differs",
        )
        require(
            payload.get("source_hashes_verified") is True,
            f"{label}: source hashes were not verified",
        )
        require(
            payload.get("evaluated_outcomes_observed") is False,
            f"{label}: evaluated-outcome boundary differs",
        )
        records = payload.get("cases")
        require(isinstance(records, list), f"{label}: cases must be a list")
        for index, record in enumerate(records):
            require(
                isinstance(record, dict),
                f"{label}.cases[{index}]: must be an object",
            )
            require_exact_keys(
                record,
                {
                    "case_id",
                    "faithful_contract",
                    "injected_drift",
                    "source_locator",
                    "confidence",
                    "source_anchor",
                    "suggested_correction",
                },
                f"{label}.cases[{index}]",
            )
        require(
            [record.get("case_id") for record in records] == case_ids,
            f"{label}: case order differs",
        )
        require(
            len(records) == len(case_ids) == 18,
            f"{label}: reviewer case count differs",
        )
        require(
            all(record.get("confidence") in (1, 2, 3) for record in records),
            f"{label}: confidence outside scale",
        )
        reviewers[label] = records

    reviewer_count_summary = summary.get("reviewer_counts")
    require(
        isinstance(reviewer_count_summary, dict),
        "summary: reviewer counts must be an object",
    )
    require_exact_keys(
        reviewer_count_summary,
        {"reviewer_a", "reviewer_b"},
        "summary.reviewer_counts",
    )
    for label, records in reviewers.items():
        expected = reviewer_count_summary[label]
        require(
            isinstance(expected, dict),
            f"summary.reviewer_counts.{label}: must be an object",
        )
        require_exact_keys(
            expected,
            set(DIMENSIONS),
            f"summary.reviewer_counts.{label}",
        )
        compare_count_block(
            categorical_counts(records, "faithful_contract"),
            expected["faithful_contract"],
            f"{label}.faithful_contract",
            DIMENSIONS["faithful_contract"][0],
        )
        compare_count_block(
            categorical_counts(records, "injected_drift"),
            expected["injected_drift"],
            f"{label}.injected_drift",
            DIMENSIONS["injected_drift"][0],
        )
        compare_count_block(
            categorical_counts(records, "source_locator"),
            expected["source_locator"],
            f"{label}.source_locator",
            DIMENSIONS["source_locator"][0],
        )

    agreement_summary = summary.get("agreement")
    require(
        isinstance(agreement_summary, dict),
        "summary: agreement must be an object",
    )
    require_exact_keys(
        agreement_summary,
        set(DIMENSIONS)
        | {
            "case_level_any_dimension_disagreement_count",
            "case_level_any_dimension_disagreement_rate",
            "disagreement_case_ids",
        },
        "summary.agreement",
    )
    metric_key_schemas = {
        "faithful_contract": {
            "agreement_count",
            "raw_agreement",
            "cohen_kappa",
            "cohen_kappa_reason",
            "gwet_ac1",
            "positive_agreement_match",
            "negative_agreement_nonmatch",
        },
        "injected_drift": {
            "agreement_count",
            "raw_agreement",
            "cohen_kappa",
            "cohen_kappa_reason",
            "gwet_ac1",
            "positive_agreement_source_critical_change",
            "negative_agreement_other",
        },
        "source_locator": {
            "agreement_count",
            "raw_agreement",
            "cohen_kappa",
            "gwet_ac1",
            "positive_agreement_correct",
            "negative_agreement_noncorrect",
        },
    }
    for field, (categories, positive) in DIMENSIONS.items():
        metrics = agreement_metrics(
            reviewers["reviewer_a"],
            reviewers["reviewer_b"],
            field,
            categories,
            positive,
        )
        reported = agreement_summary[field]
        require(
            isinstance(reported, dict),
            f"summary.agreement.{field}: must be an object",
        )
        require_exact_keys(
            reported,
            metric_key_schemas[field],
            f"summary.agreement.{field}",
        )
        require(
            metrics["agreement_count"] == reported["agreement_count"],
            f"{field}: agreement count differs",
        )
        for key in ("raw_agreement", "gwet_ac1"):
            assert_close(float(metrics[key]), float(reported[key]), f"{field}.{key}")
        if field == "faithful_contract":
            assert_close(
                float(metrics["positive_agreement"]),
                float(reported["positive_agreement_match"]),
                f"{field}.positive_agreement",
            )
            assert_close(
                float(metrics["negative_agreement"]),
                float(reported["negative_agreement_nonmatch"]),
                f"{field}.negative_agreement",
            )
        elif field == "injected_drift":
            assert_close(
                float(metrics["positive_agreement"]),
                float(reported["positive_agreement_source_critical_change"]),
                f"{field}.positive_agreement",
            )
            require(
                metrics["negative_agreement"] is reported["negative_agreement_other"],
                f"{field}.negative_agreement differs",
            )
        else:
            assert_close(
                float(metrics["positive_agreement"]),
                float(reported["positive_agreement_correct"]),
                f"{field}.positive_agreement",
            )
            assert_close(
                float(metrics["negative_agreement"]),
                float(reported["negative_agreement_noncorrect"]),
                f"{field}.negative_agreement",
            )
        reported_kappa = reported["cohen_kappa"]
        if metrics["cohen_kappa"] is None:
            require(reported_kappa is None, f"{field}: kappa must be null")
        else:
            assert_close(
                float(metrics["cohen_kappa"]),
                float(reported_kappa),
                f"{field}.cohen_kappa",
            )

    disagreement_ids = [
        case_id
        for case_id, left, right in zip(
            case_ids, reviewers["reviewer_a"], reviewers["reviewer_b"]
        )
        if any(left[field] != right[field] for field in DIMENSIONS)
    ]
    require(
        agreement_summary.get("disagreement_case_ids") == disagreement_ids,
        "summary: disagreement case IDs differ",
    )
    require(
        agreement_summary.get("case_level_any_dimension_disagreement_count")
        == len(disagreement_ids),
        "summary: disagreement count differs",
    )
    assert_close(
        float(agreement_summary["case_level_any_dimension_disagreement_rate"]),
        len(disagreement_ids) / len(case_ids),
        "summary: disagreement rate",
    )

    require(
        adjudication.get("adjudicator_id") == "primary-ai-assisted-adjudicator"
        and adjudication.get("human") is False
        and adjudication.get("independent_human_expert") is False
        and adjudication.get("source_pdf_reinspection") is True
        and adjudication.get("evaluated_outcomes_observed") is False,
        "adjudication: identity or evidence boundary differs",
    )
    adjudicated = adjudication.get("cases")
    require(isinstance(adjudicated, list), "adjudication: cases must be a list")
    for index, record in enumerate(adjudicated):
        require(
            isinstance(record, dict),
            f"adjudication.cases[{index}]: must be an object",
        )
        require_exact_keys(
            record,
            {
                "case_id",
                "faithful_contract_original",
                "injected_drift",
                "source_locator_original",
                "source_anchor",
                "rationale",
                "amendment_actions",
            },
            f"adjudication.cases[{index}]",
        )
    require(
        [record.get("case_id") for record in adjudicated] == case_ids,
        "adjudication: case order differs",
    )
    adjudicated_summary = summary.get("adjudicated_original_contracts")
    require(
        isinstance(adjudicated_summary, dict),
        "summary: adjudicated contracts must be an object",
    )
    require_exact_keys(
        adjudicated_summary,
        set(DIMENSIONS),
        "summary.adjudicated_original_contracts",
    )
    compare_count_block(
        categorical_counts(adjudicated, "faithful_contract_original"),
        adjudicated_summary["faithful_contract"],
        "adjudication.faithful_contract",
        DIMENSIONS["faithful_contract"][0],
    )
    compare_count_block(
        categorical_counts(adjudicated, "injected_drift"),
        adjudicated_summary["injected_drift"],
        "adjudication.injected_drift",
        DIMENSIONS["injected_drift"][0],
    )
    compare_count_block(
        categorical_counts(adjudicated, "source_locator_original"),
        adjudicated_summary["source_locator"],
        "adjudication.source_locator",
        DIMENSIONS["source_locator"][0],
    )
    adjudicated_index = {
        str(record["case_id"]): record for record in adjudicated
    }
    per_source_derived: list[dict[str, Any]] = []
    for spec in protocol_sources:
        source_id = str(spec["source_id"])
        source_case_ids = [
            str(case["id"]) for case in paper_cases
            if case["source_id"] == source_id
        ]
        source_records = [adjudicated_index[case_id] for case_id in source_case_ids]
        prefixes = {case_id.split("-", 1)[0] for case_id in source_case_ids}
        require(len(prefixes) == 1, f"{source_id}: case prefix is not unique")
        faithful = categorical_counts(source_records, "faithful_contract_original")
        drift = categorical_counts(source_records, "injected_drift")
        locator = categorical_counts(source_records, "source_locator_original")
        per_source_derived.append(
            {
                "source_prefix": next(iter(prefixes)),
                "source_id": source_id,
                "case_count": len(source_records),
                "faithful_match": faithful["match"],
                "faithful_mismatch": faithful["mismatch"],
                "faithful_unclear": faithful["unclear"],
                "injected_source_critical_change": drift[
                    "source_critical_change"
                ],
                "injected_not_critical": drift["not_critical"],
                "injected_unclear": drift["unclear"],
                "locator_correct": locator["correct"],
                "locator_imprecise": locator["imprecise"],
                "locator_wrong": locator["wrong"],
            }
        )
    per_source_reported = summary.get("per_source_adjudicated_original")
    require(
        isinstance(per_source_reported, list),
        "summary: per-source counts must be a list",
    )
    per_source_keys = {
        "source_prefix",
        "source_id",
        "case_count",
        "faithful_match",
        "faithful_mismatch",
        "faithful_unclear",
        "injected_source_critical_change",
        "injected_not_critical",
        "injected_unclear",
        "locator_correct",
        "locator_imprecise",
        "locator_wrong",
    }
    for index, entry in enumerate(per_source_reported):
        require(
            isinstance(entry, dict),
            f"summary.per_source_adjudicated_original[{index}]: "
            "must be an object",
        )
        require_exact_keys(
            entry,
            per_source_keys,
            f"summary.per_source_adjudicated_original[{index}]",
        )
    require(
        per_source_reported == per_source_derived,
        "summary: per-source adjudicated counts differ",
    )

    amended_ids = [
        str(record["case_id"]) for record in adjudicated
        if record.get("amendment_actions")
    ]
    pre_execution = summary.get("pre_execution_amendment", {})
    require(
        isinstance(pre_execution, dict),
        "summary: pre-execution amendment must be an object",
    )
    require_exact_keys(
        pre_execution,
        {
            "amended_case_count",
            "amended_case_rate",
            "case_ids",
            "outcomes_observed_before_amendment",
        },
        "summary.pre_execution_amendment",
    )
    require(
        amended_ids == pre_execution.get("case_ids"),
        "summary: amended case IDs differ",
    )
    require(
        pre_execution.get("amended_case_count") == len(amended_ids),
        "summary: amended case count differs",
    )
    assert_close(
        float(pre_execution["amended_case_rate"]),
        len(amended_ids) / len(case_ids),
        "summary: amended case rate",
    )
    require(
        pre_execution.get("outcomes_observed_before_amendment") is False,
        "summary: pre-amendment outcome boundary differs",
    )
    require(
        "post_amendment_ai_self_check" not in pre_execution,
        "summary: unsupported aggregate post-amendment self-check present",
    )
    case_changes = amendment.get("case_changes")
    require(isinstance(case_changes, list), "amendment: case changes must be a list")
    for index, entry in enumerate(case_changes):
        require(
            isinstance(entry, dict),
            f"amendment.case_changes[{index}]: must be an object",
        )
        require_exact_keys(
            entry,
            {"case_id", "fields", "change_summary"},
            f"amendment.case_changes[{index}]",
        )
    require(
        amended_ids == [entry["case_id"] for entry in case_changes],
        "amendment: case IDs differ from adjudication",
    )

    require(
        {
            key
            for key in pre_challenges
            if key != "cases" and pre_challenges.get(key) != challenges.get(key)
        }
        == set(),
        "amendment: undeclared challenge-manifest metadata changed",
    )
    paired_metadata_changes = [
        {
            "field": f"paired_requirements.{key}",
            "before": pre_paired.get(key),
            "after": paired.get(key),
        }
        for key in pre_paired
        if key != "cases" and pre_paired.get(key) != paired.get(key)
    ]
    metadata_changes = amendment.get("metadata_changes")
    require(
        isinstance(metadata_changes, list),
        "amendment: metadata changes must be a list",
    )
    for index, entry in enumerate(metadata_changes):
        require(
            isinstance(entry, dict),
            f"amendment.metadata_changes[{index}]: must be an object",
        )
        require_exact_keys(
            entry,
            {"field", "before", "after"},
            f"amendment.metadata_changes[{index}]",
        )
    require(
        metadata_changes == paired_metadata_changes,
        "amendment: metadata changes differ from bound files",
    )

    derived_fields_by_case: dict[str, set[str]] = {}
    for case_id in case_ids:
        challenge_fields = {
            f"challenges.{key}"
            for key in pre_challenge_index[case_id]
            if pre_challenge_index[case_id].get(key)
            != current_challenge_index[case_id].get(key)
        }
        paired_fields = {
            f"paired_requirements.{key}"
            for key in pre_paired_index[case_id]
            if pre_paired_index[case_id].get(key)
            != current_paired_index[case_id].get(key)
        }
        derived_fields_by_case[case_id] = challenge_fields | paired_fields
    require(
        [
            case_id for case_id in case_ids
            if derived_fields_by_case[case_id]
        ]
        == amended_ids,
        "amendment: changed case IDs differ from adjudication",
    )
    action_to_field = {
        "faithful_contract": "challenges.faithful_contract",
        "injected_drift": "challenges.injected_drift",
        "source_locator": "challenges.source_locator",
        "paired_requirement_source_faithful_value":
            "paired_requirements.source_faithful_value",
        "paired_requirement_injected_drift_value":
            "paired_requirements.injected_drift_value",
    }
    change_index = {str(entry["case_id"]): entry for entry in case_changes}
    require(
        len(change_index) == len(case_changes),
        "amendment: duplicate case change",
    )
    for record in adjudicated:
        case_id = str(record["case_id"])
        actions = record.get("amendment_actions")
        require(isinstance(actions, list), f"{case_id}: amendment actions differ")
        require(
            all(action in action_to_field for action in actions),
            f"{case_id}: unknown amendment action",
        )
        expected_fields = {action_to_field[action] for action in actions}
        require(
            expected_fields == derived_fields_by_case[case_id],
            f"{case_id}: adjudication actions differ from bound file changes",
        )
        if actions:
            change = change_index[case_id]
            fields = change.get("fields")
            require(
                isinstance(fields, list)
                and len(fields) == len(set(fields))
                and set(fields) == expected_fields,
                f"{case_id}: amendment fields differ from bound file changes",
            )
            require(
                isinstance(change.get("change_summary"), str)
                and bool(change["change_summary"].strip()),
                f"{case_id}: amendment summary missing",
            )

    timing = amendment.get("timing_and_claim_boundary", {})
    require(
        isinstance(timing, dict),
        "amendment: timing boundary must be an object",
    )
    require_exact_keys(
        timing,
        {
            "primary_model_outcomes_observed",
            "external_comparator_outcomes_observed",
            "provider_calls_for_evaluation_observed",
            "human_expert_validation_complete",
            "amendment_is_evaluation_result",
        },
        "amendment.timing_and_claim_boundary",
    )
    require(
        timing.get("primary_model_outcomes_observed") is False
        and timing.get("external_comparator_outcomes_observed") is False
        and timing.get("provider_calls_for_evaluation_observed") is False
        and timing.get("human_expert_validation_complete") is False
        and timing.get("amendment_is_evaluation_result") is False,
        "amendment: timing or claim boundary differs",
    )

    derived = amendment.get("derived_bindings_after", {})
    require(
        isinstance(derived, dict),
        "amendment: derived bindings must be an object",
    )
    require_exact_keys(
        derived,
        {
            "target_drift_v1_protocol",
            "target_drift_v2_protocol",
            "external_comparator_plan",
            "external_comparator_plan_seal",
            "leanflow_schedule",
            "leanflow_adapter_contract",
            "leanflow_fixture_request",
            "leanflow_completion_ledger_contract",
            "leanflow_plumbing_seal",
            "wording_negative_control_record",
        },
        "amendment.derived_bindings_after",
    )
    for name, entry in derived.items():
        require(
            isinstance(entry, dict),
            f"amendment.derived_bindings_after.{name}: must be an object",
        )
        if name == "leanflow_schedule":
            expected_keys = {"path", "before_sha256", "after_sha256"}
        elif name == "wording_negative_control_record":
            expected_keys = {
                "path",
                "sha256",
                "deterministic_accuracy_before",
                "deterministic_accuracy_after",
                "result_eligible",
            }
        else:
            expected_keys = {"path", "sha256"}
        require_exact_keys(
            entry,
            expected_keys,
            f"amendment.derived_bindings_after.{name}",
        )
        path = root / Path(entry["path"])
        require(path.is_file(), f"amendment: missing {entry['path']}")
        expected_hash = entry.get("after_sha256", entry.get("sha256"))
        require(expected_hash is not None, f"{entry['path']}: no current hash")
        require(sha256(path) == expected_hash, f"{entry['path']}: hash differs")

    wording_record = load_json(
        root / "evaluation/target-drift-v2/wording-negative-control-record.json"
    )
    require(
        wording_record.get("result_eligible") is False,
        "wording diagnostic must remain result-ineligible",
    )
    require(
        wording_record["input"]["sha256"] == sha256(root / PAIRED_REL),
        "wording diagnostic input hash differs",
    )
    assert_close(
        float(wording_record["audit"]["deterministic_leave_one_pair_out_bernoulli_nb_accuracy"]),
        0.5333333333333333,
        "wording diagnostic accuracy",
    )

    summary_boundary = summary.get("claim_boundary", {})
    require(
        isinstance(summary_boundary, dict),
        "summary: claim boundary must be an object",
    )
    require_exact_keys(
        summary_boundary,
        {
            "human_expert_validation_complete",
            "benchmark_execution_complete",
            "workflow_effectiveness_supported",
        },
        "summary.claim_boundary",
    )
    require(
        summary_boundary.get("human_expert_validation_complete") is False
        and summary_boundary.get("benchmark_execution_complete") is False
        and summary_boundary.get("workflow_effectiveness_supported") is False,
        "summary: claim boundary differs",
    )


def main() -> None:
    try:
        validate()
    except (AuditError, KeyError, TypeError, ValueError, json.JSONDecodeError) as error:
        raise SystemExit(f"source-contract audit validation failed: {error}") from error
    print(
        "source-contract pre-audit valid: 18 paper cases, two isolated AI reviews, "
        "human expert validation pending"
    )


if __name__ == "__main__":
    main()
