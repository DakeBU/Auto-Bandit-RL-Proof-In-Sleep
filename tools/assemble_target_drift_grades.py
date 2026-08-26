#!/usr/bin/env python3
"""Validate two blind grade files, adjudicate disagreements, and emit analysis records."""

from __future__ import annotations

import argparse
import hashlib
import json
import sys
from pathlib import Path
from statistics import mean
from typing import Any


CONDITIONS = ("compile_only", "source_aware_blueprint", "abrl")
BINARY_LABELS = (
    "primary_pass",
    "faithful_formal_completion",
    "drift_detected",
    "false_rejection",
    "unsupported_evidence_claim",
    "source_amendment_required",
)

TOOLS = Path(__file__).resolve().parent
sys.path.insert(0, str(TOOLS))

import prepare_target_drift_execution as prepare  # noqa: E402
import prepare_target_drift_grading as grading  # noqa: E402
import build_target_drift_completion_ledger as completion  # noqa: E402


def load(path: Path) -> dict[str, Any]:
    return json.loads(path.read_text(encoding="utf-8"))


def dump(path: Path, value: Any) -> None:
    path.write_text(
        json.dumps(value, indent=2, sort_keys=True, ensure_ascii=False) + "\n",
        encoding="utf-8",
    )


def require(condition: bool, message: str) -> None:
    if not condition:
        raise SystemExit(f"target-drift grade assembly failed: {message}")


def validate_variant_fields(final: dict[str, Any], requirement_variant: str,
                            canonical_fields: set[str]) -> None:
    if requirement_variant == "source_faithful":
        require(final["drift_detected"] is False,
                "drift_detected must be false for a source-faithful requirement")
        require(final["source_critical_fields"] == [],
                "source-faithful requirement must have an empty affected-field list")
    else:
        require(final["false_rejection"] is False,
                "false_rejection must be false for an injected-drift requirement")
        require(bool(final["source_critical_fields"])
                and set(final["source_critical_fields"]) <= canonical_fields,
                "injected-drift affected fields must be nonempty canonical challenge fields")


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


def operator_execution_metrics(mapping_item: dict[str, Any]) -> dict[str, Any]:
    """Return resource metrics from the operator-only mapping, never a grader packet."""
    metrics = mapping_item.get("execution_metrics")
    require(isinstance(metrics, dict) and bool(metrics),
            f"operator mapping omits execution metrics for {mapping_item.get('grade_id')}")
    return metrics


def operator_workflow_compliance(mapping_item: dict[str, Any]) -> bool:
    """Return the manipulation check retained behind the primary-grader boundary."""
    value = mapping_item.get("workflow_compliance_pass")
    require(isinstance(value, bool),
            f"operator mapping omits workflow compliance for {mapping_item.get('grade_id')}")
    return value


def validate_grade(item: dict[str, Any], require_condition_guess: bool = True) -> None:
    require(isinstance(item.get("grade_id"), str) and item["grade_id"],
            "grade_id must be a nonempty string")
    require(all(isinstance(item.get(label), bool) for label in BINARY_LABELS),
            f"all binary labels must be booleans for {item.get('grade_id')}")
    require(isinstance(item.get("rationale"), str) and item["rationale"].strip(),
            f"rationale must be nonempty for {item.get('grade_id')}")
    fields = item.get("source_critical_fields")
    require(isinstance(fields, list) and all(isinstance(field, str) and field for field in fields)
            and fields == sorted(set(fields)),
            f"source_critical_fields must be a sorted unique string list for {item.get('grade_id')}")
    if require_condition_guess:
        require(item.get("condition_guess") in CONDITIONS,
                f"unknown condition guess for {item.get('grade_id')}")
        confidence = item.get("condition_guess_confidence")
        require(isinstance(confidence, (int, float)) and not isinstance(confidence, bool)
                and 0 <= confidence <= 1,
                f"condition-guess confidence outside [0,1] for {item.get('grade_id')}")


def by_grade_id(
    response: dict[str, Any], expected: set[str], grading_pack_sha256: str,
    grader_prompt_sha256: str,
) -> dict[str, dict[str, Any]]:
    require(response.get("schema_version") == 1, "grader response schema_version must be 1")
    require(response.get("grading_pack_sha256") == grading_pack_sha256,
            "grader response names a different grading-pack digest")
    require(response.get("grader_prompt_sha256") == grader_prompt_sha256,
            "grader response names a different frozen grader prompt")
    grades = response.get("grades")
    require(isinstance(grades, list), "grader response grades must be a list")
    for grade in grades:
        validate_grade(grade)
    indexed = {grade["grade_id"]: grade for grade in grades}
    require(len(indexed) == len(grades), "grader response contains duplicate grade IDs")
    require(set(indexed) == expected, "grader response does not exactly cover packet IDs")
    return indexed


def cohen_kappa(left: list[bool], right: list[bool]) -> float | None:
    require(len(left) == len(right) and bool(left), "kappa inputs must be nonempty and paired")
    observed = mean(a == b for a, b in zip(left, right))
    left_true = mean(left)
    right_true = mean(right)
    expected = left_true * right_true + (1 - left_true) * (1 - right_true)
    if expected == 1:
        return None
    return (observed - expected) / (1 - expected)


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--pack", type=Path, required=True)
    parser.add_argument("--grading-pack", type=Path, required=True)
    parser.add_argument("--grader-response", type=Path, action="append", required=True)
    parser.add_argument("--adjudication", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    require(len(args.grader_response) == 2, "exactly two grader responses are required")
    require(not args.output.exists(), "analysis-record output already exists")

    pack = args.pack.resolve()
    grading_pack = args.grading_pack.resolve()
    prepare.verify_pack(pack)
    config = load(pack / "execution_config.json")
    require(config["suite_id"] == "ABRL-TARGET-DRIFT-V2", "assembler requires v2 pack")
    current = Path(__file__).resolve()
    expected_script_hash = config["analysis"]["grade_assembler_sha256"]
    require(hashlib.sha256(current.read_bytes()).hexdigest() == expected_script_hash,
            "invoked grade assembler differs from frozen hash")
    require(hashlib.sha256((pack / "execution_code" / current.name).read_bytes()).hexdigest()
            == expected_script_hash,
            "sealed grade assembler differs from frozen hash")
    prepare_path = Path(prepare.__file__).resolve()
    prepare_hash = config["sealed_agent_view"]["materializer_sha256"]
    require(hashlib.sha256(prepare_path.read_bytes()).hexdigest() == prepare_hash,
            "imported pack verifier differs from frozen hash")
    require(hashlib.sha256((pack / "execution_code" / prepare_path.name).read_bytes()).hexdigest()
            == prepare_hash, "sealed pack verifier differs from frozen hash")
    grading_path = Path(grading.__file__).resolve()
    grading_hash = config["grading"]["packet_materializer_sha256"]
    require(hashlib.sha256(grading_path.read_bytes()).hexdigest() == grading_hash,
            "imported grading materializer differs from frozen hash")
    require(hashlib.sha256((pack / "execution_code" / grading_path.name).read_bytes()).hexdigest()
            == grading_hash, "sealed grading materializer differs from frozen hash")
    require(
        config["grading"]["grader_conflict_policy"]
        == "adjudicate every disagreement on a primary or secondary binary label or the structured source-critical field list",
        "unsupported frozen grader conflict policy",
    )
    configured_graders = config["grading"]["primary_grader_ids"]
    require(isinstance(configured_graders, list) and len(configured_graders) == 2
            and len(set(configured_graders)) == 2,
            "frozen primary_grader_ids must contain two unique identifiers")

    packet_manifest = load(grading_pack / "packet-manifest.json")
    require(packet_manifest["suite_id"] == config["suite_id"],
            "grading pack suite differs from sealed execution pack")
    sealed_pack_sha256 = (pack / "aggregate.sha256").read_text(encoding="ascii").strip()
    require(packet_manifest["sealed_pack_sha256"] == sealed_pack_sha256,
            "grading pack names a different sealed execution pack")
    require(packet_manifest["grader_prompt_sha256"] == config["grading"]["grader_prompt_sha256"],
            "grading pack names a different frozen grader prompt")
    runtime_sha256 = prepare.checker_runtime_config_sha256(config)
    require(config["posthoc_checker"]["mode"] == "production"
            and packet_manifest.get("result_eligible") is True
            and packet_manifest.get("checker_mode") == "production",
            "grade assembly requires production-result-eligible checker records")
    require(packet_manifest.get("checker_runtime_config_sha256") == runtime_sha256
            == config["posthoc_checker"]["runtime_config_sha256"]
            and packet_manifest.get("isolation_probe_report_sha256")
            == config["posthoc_checker"]["isolation_probe_report_sha256"],
            "grading pack checker runtime/probe binding differs from frozen config")
    require(packet_manifest["grading_seed"] == config["grading"]["packet_order_seed"],
            "grading packet seed differs from frozen config")
    mapping_path = grading_pack / "operator-mapping.json"
    mapping_payload = mapping_path.read_bytes()
    completion_path = grading_pack / "completion-ledger.json"
    require(completion_path.is_file(), "grading pack completion ledger is missing")
    completion_payload = completion_path.read_bytes()
    require(hashlib.sha256(completion_payload).hexdigest()
            == packet_manifest.get("completion_ledger_sha256"),
            "grading completion-ledger hash differs from manifest")
    completion_ledger = json.loads(completion_payload.decode("utf-8"))
    completion.self_verify(pack, config)
    completion.validate_ledger(pack, completion_ledger, require_complete=True)
    require(packet_manifest.get("missing_run_policy_id")
            == completion_ledger["missing_run_policy_id"]
            and packet_manifest.get("missing_run_policy_sha256")
            == completion_ledger["missing_run_policy_sha256"],
            "grading pack missing-run policy binding mismatch")
    mapping = json.loads(mapping_payload.decode("utf-8"))["mapping"]
    packet_payloads = {
        f"packets/{path.name}": path.read_bytes()
        for path in sorted((grading_pack / "packets").glob("*.json"))
    }
    require(len(packet_payloads) == packet_manifest["packet_count"],
            "grading packet directory count differs from manifest")
    packet_grade_ids = {
        json.loads(payload.decode("utf-8"))["grade_id"]
        for payload in packet_payloads.values()
    }
    packet_by_grade_id = {
        json.loads(payload.decode("utf-8"))["grade_id"]: json.loads(payload.decode("utf-8"))
        for payload in packet_payloads.values()
    }
    for grade_id, packet in packet_by_grade_id.items():
        grading.require_primary_metadata_blind(packet, f"primary packet {grade_id}")
    require(
        set(packet_payloads)
        == {f"packets/{grade_id}.json" for grade_id in packet_grade_ids},
        "grading packet filename and embedded grade ID differ",
    )
    require(
        packet_manifest["packet_sha256"]
        == {name: hashlib.sha256(payload).hexdigest()
            for name, payload in sorted(packet_payloads.items())},
        "grading packet file hashes differ from manifest",
    )
    require(packet_manifest["packet_aggregate_sha256"] == digest_payloads(packet_payloads),
            "grading packet aggregate differs from manifest")
    require(packet_manifest["operator_mapping_sha256"] == hashlib.sha256(mapping_payload).hexdigest(),
            "operator mapping hash differs from manifest")
    require(packet_manifest.get("primary_packets_exclude_condition_and_variant_labels") is True,
            "grading manifest does not attest condition/variant-label exclusion")
    require(packet_manifest.get("primary_packets_exclude_execution_metrics") is True,
            "grading manifest does not attest execution-metric exclusion")
    require(packet_manifest.get("primary_packets_exclude_workflow_compliance") is True,
            "grading manifest does not attest workflow-compliance exclusion")
    require(
        packet_manifest["aggregate_sha256"]
        == digest_payloads({
            **packet_payloads,
            "operator-mapping.json": mapping_payload,
            "completion-ledger.json": completion_payload,
        }),
        "combined grading-pack aggregate differs from manifest",
    )
    packet_ids = {item["grade_id"] for item in mapping}
    require(len(packet_ids) == packet_manifest["packet_count"] == 450,
            "grading pack must contain exactly 450 unique packets")

    responses = [load(path.resolve()) for path in args.grader_response]
    response_ids = [response.get("grader_id") for response in responses]
    require(response_ids == configured_graders,
            "grader response order/identities differ from frozen config")
    indexed = [
        by_grade_id(
            response,
            packet_ids,
            packet_manifest["aggregate_sha256"],
            config["grading"]["grader_prompt_sha256"],
        )
        for response in responses
    ]

    conflicts = {
        grade_id for grade_id in packet_ids
        if any(indexed[0][grade_id][label] != indexed[1][grade_id][label]
               for label in BINARY_LABELS)
        or indexed[0][grade_id]["source_critical_fields"]
        != indexed[1][grade_id]["source_critical_fields"]
    }
    adjudication = load(args.adjudication.resolve())
    require(adjudication.get("schema_version") == 1,
            "adjudication schema_version must be 1")
    require(adjudication.get("grading_pack_sha256") == packet_manifest["aggregate_sha256"],
            "adjudication names a different grading-pack digest")
    require(adjudication.get("grader_prompt_sha256")
            == config["grading"]["grader_prompt_sha256"],
            "adjudication names a different frozen grader prompt")
    require(adjudication.get("adjudicator_id") == config["grading"]["adjudicator_id"],
            "adjudicator identity differs from frozen config")
    adjudicated_list = adjudication.get("grades")
    require(isinstance(adjudicated_list, list), "adjudication grades must be a list")
    for item in adjudicated_list:
        validate_grade(item, require_condition_guess=False)
    adjudicated = {item["grade_id"]: item for item in adjudicated_list}
    require(len(adjudicated) == len(adjudicated_list), "duplicate adjudication grade IDs")
    require(set(adjudicated) == conflicts,
            "adjudication must cover exactly the binary-label disagreements")

    run_manifest = load(pack / "run_manifest.json")
    run_by_id = {run["run_id"]: run for run in run_manifest["runs"]}
    challenges = load(pack / "operator_challenges.json")["cases"]
    challenge_by_id = {case["id"]: case for case in challenges}
    records = []
    primary_left: list[bool] = []
    primary_right: list[bool] = []
    for mapping_item in mapping:
        grade_id = mapping_item["grade_id"]
        left = indexed[0][grade_id]
        right = indexed[1][grade_id]
        final = adjudicated.get(grade_id, left)
        packet = packet_by_grade_id[grade_id]
        semantic_run_id = mapping_item["semantic_run_id"]
        run = run_by_id[semantic_run_id]
        challenge = challenge_by_id[run["case_id"]]
        canonical_fields = set(challenge["expected_affected_fields"])
        validate_variant_fields(final, run["requirement_variant"], canonical_fields)
        checker = packet["neutral_checker"]
        require(not final["faithful_formal_completion"] or (
            checker["checker_pass"]
            and checker["artifact_replay_success"]
            and bool(packet["public_declarations"])
        ), "faithful_formal_completion conflicts with neutral checker evidence")
        primary_left.append(left["primary_pass"])
        primary_right.append(right["primary_pass"])
        record = {
            "semantic_run_id": semantic_run_id,
            "case_id": run["case_id"],
            "source_id": challenge["source_id"],
            "stratum": challenge["stratum"],
            "condition": run["condition"],
            "replicate": run["replicate"],
            "requirement_variant": run["requirement_variant"],
            **{label: final[label] for label in BINARY_LABELS},
            "final_rationale": final["rationale"],
            "source_critical_fields": final["source_critical_fields"],
            "adjudicated": grade_id in adjudicated,
            "artifact_replay_success": checker["artifact_replay_success"],
            "checker_pass": checker["checker_pass"],
            "execution_metrics": operator_execution_metrics(mapping_item),
            "workflow_compliance_pass": operator_workflow_compliance(mapping_item),
            "grader_condition_guesses": {
                response_ids[0]: left["condition_guess"],
                response_ids[1]: right["condition_guess"],
            },
            "grader_condition_guess_confidences": {
                response_ids[0]: left["condition_guess_confidence"],
                response_ids[1]: right["condition_guess_confidence"],
            },
        }
        records.append(record)

    require(len(records) == 450, "assembled record count must be 450")
    raw_agreement = mean(a == b for a, b in zip(primary_left, primary_right))
    dump(args.output.resolve(), {
        "schema_version": 1,
        "suite_id": config["suite_id"],
        "sealed_pack_sha256": sealed_pack_sha256,
        "grading_pack_sha256": packet_manifest["aggregate_sha256"],
        "completion_ledger_sha256": packet_manifest["completion_ledger_sha256"],
        "missing_run_policy_id": packet_manifest["missing_run_policy_id"],
        "missing_run_policy_sha256": packet_manifest["missing_run_policy_sha256"],
        "result_eligible": True,
        "checker_mode": "production",
        "checker_runtime_config_sha256": runtime_sha256,
        "isolation_probe_report_sha256": config["posthoc_checker"][
            "isolation_probe_report_sha256"
        ],
        "grading_summary": {
            "primary_grader_ids": response_ids,
            "adjudicator_id": adjudication["adjudicator_id"],
            "binary_label_disagreement_count": len(conflicts),
            "primary_raw_agreement": raw_agreement,
            "primary_cohen_kappa": cohen_kappa(primary_left, primary_right),
        },
        "records": records,
    })
    print(
        f"assembled 450 target-drift grades: disagreements={len(conflicts)}, "
        f"primary_raw_agreement={raw_agreement:.6f}"
    )


if __name__ == "__main__":
    main()
