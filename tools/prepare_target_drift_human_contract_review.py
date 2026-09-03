#!/usr/bin/env python3
"""Create a result-free, hash-bound human source-contract review packet."""

from __future__ import annotations

import argparse
import hashlib
import json
import os
from pathlib import Path
from typing import Any
from urllib.parse import urlsplit


ROOT = Path(__file__).resolve().parents[1]
PROTOCOL = ROOT / "evaluation/target-drift-v2/human-source-contract-review-protocol.json"
EXTERNAL_PROTOCOL = (
    ROOT
    / "evaluation/target-drift-v2/"
    "human-source-contract-external-verification-protocol.json"
)
TRUST_ANCHOR_CONTRACT = (
    ROOT
    / "evaluation/target-drift-v2/"
    "human-source-contract-external-trust-anchor-contract.json"
)
SOURCE_TEMPLATE = ROOT / "evaluation/target-drift-v2/source-files.template.json"
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


def pretty_bytes(value: Any) -> bytes:
    return (
        json.dumps(value, indent=2, sort_keys=True, ensure_ascii=False) + "\n"
    ).encode("utf-8")


def sha256_bytes(value: bytes) -> str:
    return hashlib.sha256(value).hexdigest()


def write_new(path: Path, value: Any) -> None:
    write_new_bytes(path, canonical_bytes(value))


def write_new_bytes(path: Path, payload: bytes) -> None:
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


def build_source_index(
    reviewer_template: dict[str, Any], root: Path = ROOT
) -> dict[str, Any]:
    """Build the public-source index distributed to each reviewer.

    The source PDFs are intentionally not copied into the packet.  Reviewers
    acquire the named public bytes independently and verify their frozen hash.
    """
    source_template_path = root / SOURCE_TEMPLATE.relative_to(ROOT)
    source_template = load(source_template_path)
    require(
        source_template.get("schema_version") == 2
        and source_template.get("suite_id") == "ABRL-TARGET-DRIFT-V2",
        "source-file template identity differs",
    )
    cases_by_source: dict[str, list[dict[str, str]]] = {}
    expected_hashes: dict[str, str] = {}
    for case in reviewer_template["cases"]:
        source_id = case["source_id"]
        expected_hash = expected_hashes.setdefault(source_id, case["source_sha256"])
        require(
            expected_hash == case["source_sha256"],
            f"inconsistent frozen source hash for {source_id}",
        )
        cases_by_source.setdefault(source_id, []).append({
            "case_id": case["case_id"],
            "source_locator": case["current_source_locator"],
        })

    indexed_sources: list[dict[str, Any]] = []
    seen: set[str] = set()
    for source in source_template.get("sources", []):
        source_id = source.get("source_id")
        require(
            isinstance(source_id, str) and source_id in cases_by_source,
            f"unexpected source-file template entry: {source_id}",
        )
        require(source_id not in seen, f"duplicate source entry: {source_id}")
        seen.add(source_id)
        public_url = source.get("public_url")
        parsed = urlsplit(public_url if isinstance(public_url, str) else "")
        require(
            parsed.scheme == "https"
            and bool(parsed.netloc)
            and parsed.username is None
            and parsed.password is None,
            f"source URL must be credential-free HTTPS for {source_id}",
        )
        require(
            source.get("sha256") == expected_hashes[source_id],
            f"source-file template hash differs for {source_id}",
        )
        require(
            source.get("local_path") == UNSET,
            f"review source index must not expose an operator-local path for {source_id}",
        )
        indexed_sources.append({
            "source_id": source_id,
            "public_url": public_url,
            "sha256": source["sha256"],
            "edition_note": source["edition_note"],
            "cases": cases_by_source[source_id],
        })
    require(
        seen == set(cases_by_source) and len(seen) == 4,
        "review source index must cover exactly the four frozen sources",
    )
    return {
        "schema_version": 1,
        "audit_id": reviewer_template["audit_id"],
        "status": "result_free_public_source_index",
        "source_count": 4,
        "case_count": 30,
        "sources": indexed_sources,
        "source_template_sha256": sha256(source_template_path),
        "claim_boundary": (
            "URLs are acquisition pointers, not trusted content. Reviewers must verify "
            "the SHA-256 of independently acquired bytes before reviewing any case. "
            "No source PDF, benchmark execution, model output, grade, or result is included."
        ),
    }


def reviewer_guide(slot: str) -> str:
    label = "A" if slot == "reviewer-a" else "B"
    return f"""# Independent source-contract review — Reviewer {label}

This directory is the complete packet for reviewer {label}. It contains no other
reviewer's response, adjudication, model run, grade, condition assignment, or
workflow outcome. The proposed contracts and target cards are inputs under
review, not an answer key and not evidence that the benchmark is correct.

## Before reviewing

1. Work independently. Do not view or discuss the other review before submitting
   your final response to the operator.
2. Open `source-index.json`, acquire each source from its credential-free HTTPS
   URL, and verify the exact SHA-256. Do not substitute another edition.
3. Read `review-protocol.json`. Stop and report the case as `not_auditable` if
   the frozen bytes or exact locator cannot be checked.
4. Choose a 3–64 character ASCII pseudonymous `reviewer_id`. Identity,
   qualification, independence, and conflict-of-interest evidence is handled by
   the separate external verifier; do not put private identity evidence here.

## Complete `reviewer-response.json`

Replace every `UNSET` value. Keep every frozen field outside each `review` object
byte-for-byte semantically unchanged. For all 30 cases:

- decide whether the proposed faithful contract matches the source;
- decide whether the injected variant changes a source-critical field;
- decide whether the source locator is exact;
- reconstruct every field in `complete_common_target_card` from the source;
- record source-hash verification, confidence 1–3, and a case-specific rationale.

Use `needs_correction` or `not_auditable` when warranted. A negative review is a
valid scientific outcome and must not be softened to make the benchmark pass.

Submit only the completed JSON response through the operator's agreed private
channel. The operator freezes both reviewer files before either is disclosed to
the adjudicator or the other reviewer. Do not claim that completing this form
validates the full Lean library or any harness effectiveness result.
"""


def adjudicator_guide() -> str:
    return """# Source-contract adjudication

Begin only after the operator has frozen both independent reviewer responses and
their hashes. Receive those two completed JSON files separately; this starter
packet intentionally contains neither response.

For each of the 30 cases, recompute every decision and target-card field against
the hash-verified source. Record all reviewer disagreement dimensions exactly,
resolve every disagreement, and provide a case-specific rationale. If either
review or the adjudicated card requires a correction, set the corresponding
source contract invalid and trigger a benchmark amendment; never edit the frozen
benchmark in place after observing an outcome.

Fill every `UNSET` in `adjudication-response.json`, including the exact SHA-256 of
the two frozen reviewer files. The machine validator recomputes disagreement and
rejects inconsistent validity flags. External identity, qualification,
independence, and conflict-of-interest verification remains a separate gate.
"""


def operator_guide() -> str:
    return """# Operator runbook — two-expert source-contract prerequisite

This is a result-free dispatch kit. It prepares the work; it does not claim that
any human review, external verification, benchmark execution, or harness result
has occurred.

## Required order

1. Before review starts, recruit two independent subject/formalization experts,
   one distinct adjudicator, and one distinct external verifier. Resolve conflicts
   of interest outside the repository.
2. Generate separate Ed25519 keys, complete `role-registry-template.json`, create
   OpenSSH `allowed_signers`, and publicly preregister the real signer registry and
   trust anchor before anyone observes evaluation outcomes. Never commit private
   keys or private identity evidence.
3. Send only `reviewer-a/` to reviewer A and only `reviewer-b/` to reviewer B.
   Freeze and hash each returned response before cross-disclosure.
4. Give the adjudicator both frozen responses plus `adjudicator/`. Freeze and sign
   the completed adjudication.
5. Run the self-attested validator, then have the external verifier inspect the
   escrowed identity, qualification, independence, and conflict-of-interest
   evidence and sign the external receipt. Finally run the external validator and
   public trust-anchor verification defined by the frozen protocols.

## Core machine validation

```text
python tools/validate_target_drift_human_contract_review.py \\
  --packet CORE_PACKET --reviewer-a REVIEWER_A.json \\
  --reviewer-b REVIEWER_B.json --adjudication ADJUDICATION.json \\
  --output SELF_ATTESTED_COMPLETION.json
```

The exact external-verification CLI is documented by
`external-verification-protocol.json` and
`tools/validate_target_drift_human_contract_external_verification.py --help`.
Its successful status still does not cryptographically prove that a signer is
human, and it does not by itself make a production run eligible. The prior public
Git trust anchor and the full execution preseal remain mandatory.

Before distribution, verify the dispatch tree:

```text
python tools/prepare_target_drift_human_contract_review.py \
  --verify-dispatch THIS_DIRECTORY
```

The verifier rejects any changed, missing, added, or role-misrouted file.
"""


def build_dispatch_files(root: Path = ROOT) -> dict[str, bytes]:
    """Return the exact role-separated, result-free dispatch tree."""
    manifest, reviewer, adjudication = build_packet(root)
    review_protocol_path = root / PROTOCOL.relative_to(ROOT)
    external_protocol_path = root / EXTERNAL_PROTOCOL.relative_to(ROOT)
    trust_contract_path = root / TRUST_ANCHOR_CONTRACT.relative_to(ROOT)
    review_protocol = load(review_protocol_path)
    external_protocol = load(external_protocol_path)
    trust_contract = load(trust_contract_path)
    require(
        external_protocol.get("status")
        == "protocol_frozen_no_real_signers_keys_or_receipts",
        "external verification protocol is no longer result-free",
    )
    require(
        trust_contract.get("status")
        == "contract_frozen_real_anchor_unset_production_ineligible"
        and trust_contract.get("claim_boundary", {}).get(
            "real_anchor_present_in_this_contract"
        ) is False,
        "external trust-anchor contract is no longer result-free",
    )
    source_index = build_source_index(reviewer, root)
    files: dict[str, bytes] = {}

    for slot in ("reviewer-a", "reviewer-b"):
        files[f"{slot}/README.md"] = reviewer_guide(slot).encode("utf-8")
        files[f"{slot}/reviewer-response.json"] = pretty_bytes(reviewer)
        files[f"{slot}/review-protocol.json"] = pretty_bytes(review_protocol)
        files[f"{slot}/source-index.json"] = pretty_bytes(source_index)

    files["adjudicator/README.md"] = adjudicator_guide().encode("utf-8")
    files["adjudicator/adjudication-response.json"] = pretty_bytes(adjudication)
    files["adjudicator/review-protocol.json"] = pretty_bytes(review_protocol)
    files["adjudicator/source-index.json"] = pretty_bytes(source_index)

    files["operator/README.md"] = operator_guide().encode("utf-8")
    files["operator/core-packet/packet-manifest.json"] = canonical_bytes(manifest)
    files["operator/core-packet/reviewer-template.json"] = canonical_bytes(reviewer)
    files["operator/core-packet/adjudication-template.json"] = canonical_bytes(
        adjudication
    )
    files["operator/review-protocol.json"] = pretty_bytes(review_protocol)
    files["operator/external-verification-protocol.json"] = pretty_bytes(
        external_protocol
    )
    files["operator/trust-anchor-contract.json"] = pretty_bytes(trust_contract)
    files["operator/role-registry-template.json"] = pretty_bytes(
        external_protocol["role_registry_template"]
    )
    files["operator/external-receipt-template.json"] = pretty_bytes(
        external_protocol["external_receipt_template"]
    )
    files["operator/trust-anchor-template.json"] = pretty_bytes(
        trust_contract["anchor_template"]
    )
    files["operator/source-index.json"] = pretty_bytes(source_index)
    return files


def dispatch_manifest(files: dict[str, bytes]) -> dict[str, Any]:
    role_allowlists = {
        role: sorted(
            path for path in files if path.startswith(f"{role}/")
        )
        for role in ("reviewer-a", "reviewer-b", "adjudicator", "operator")
    }
    return {
        "schema_version": 1,
        "kit_id": "ABRL-TARGET-DRIFT-V2-HUMAN-SOURCE-CONTRACT-DISPATCH",
        "status": "result_free_role_separated_dispatch_ready",
        "evaluation_outcomes_observed": False,
        "files": [
            {
                "path": path,
                "size_bytes": len(files[path]),
                "sha256": sha256_bytes(files[path]),
            }
            for path in sorted(files)
        ],
        "role_allowlists": role_allowlists,
        "distribution_rule": (
            "Distribute only the named reviewer directory to each reviewer. "
            "Hold the adjudicator directory until both reviewer responses are frozen. "
            "Never distribute the operator directory as a reviewer packet."
        ),
        "reviewer_packet_boundary": (
            "Each reviewer sees the frozen proposed source contracts under audit, "
            "but no other review, adjudication, model run, condition assignment, "
            "grade, execution metric, or workflow outcome."
        ),
        "claim_boundary": (
            "This deterministic kit contains templates and public source pointers only. "
            "It is not a completed human review, identity/qualification attestation, "
            "public signer trust anchor, benchmark execution, or effectiveness result."
        ),
    }


def expected_dispatch_tree(root: Path = ROOT) -> dict[str, bytes]:
    files = build_dispatch_files(root)
    return {"manifest.json": pretty_bytes(dispatch_manifest(files)), **files}


def materialize_dispatch(output: Path, root: Path = ROOT) -> dict[str, Any]:
    output = output.resolve()
    require(not output.exists(), "dispatch output directory already exists")
    require(output.parent.is_dir(), "dispatch output parent is missing")
    tree = expected_dispatch_tree(root)
    output.mkdir(mode=0o700)
    for relative, payload in tree.items():
        destination = output / Path(relative)
        destination.parent.mkdir(parents=True, exist_ok=True)
        write_new_bytes(destination, payload)
    return json.loads(tree["manifest.json"], object_pairs_hook=reject_duplicate_keys)


def verify_dispatch(output: Path, root: Path = ROOT) -> dict[str, Any]:
    output = output.resolve()
    require(output.is_dir() and not output.is_symlink(),
            "dispatch output must be one regular directory")
    expected = expected_dispatch_tree(root)
    actual: dict[str, Path] = {}
    for path in output.rglob("*"):
        require(not path.is_symlink(), f"dispatch path must not be a link: {path}")
        if path.is_file():
            relative = path.relative_to(output).as_posix()
            actual[relative] = path
        else:
            require(path.is_dir(), f"dispatch path must be a file or directory: {path}")
    require(set(actual) == set(expected),
            "dispatch file allowlist differs (missing, added, or misrouted file)")
    for relative, payload in expected.items():
        require(actual[relative].read_bytes() == payload,
                f"dispatch file bytes differ: {relative}")
    return load(output / "manifest.json")


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--output", type=Path)
    parser.add_argument("--dispatch-output", type=Path)
    parser.add_argument("--verify-dispatch", type=Path)
    args = parser.parse_args()
    require(
        (args.verify_dispatch is None) != (args.output is None),
        "provide either --output (optionally with --dispatch-output) or --verify-dispatch",
    )
    require(
        args.output is not None or args.dispatch_output is None,
        "--dispatch-output requires --output",
    )
    if args.verify_dispatch is not None:
        verified = verify_dispatch(args.verify_dispatch)
        print(
            "verified result-free human source-contract dispatch kit: "
            f"{verified['kit_id']} ({len(verified['files'])} files)"
        )
        return
    output = args.output.resolve()
    require(not output.exists(), "review output directory already exists")
    require(output.parent.is_dir(), "review output parent is missing")
    manifest, reviewer, adjudication = build_packet()
    output.mkdir(mode=0o700)
    write_new(output / "packet-manifest.json", manifest)
    write_new(output / "reviewer-template.json", reviewer)
    write_new(output / "adjudication-template.json", adjudication)
    print(f"prepared result-free human source-contract review packet: {output}")
    if args.dispatch_output is not None:
        dispatch = materialize_dispatch(args.dispatch_output)
        print(
            "prepared role-separated human source-contract dispatch kit: "
            f"{args.dispatch_output.resolve()} ({len(dispatch['files'])} files)"
        )


if __name__ == "__main__":
    main()
