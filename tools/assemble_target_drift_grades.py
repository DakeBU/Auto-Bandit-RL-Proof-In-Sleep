#!/usr/bin/env python3
"""Validate two blind grade files, adjudicate disagreements, and emit analysis records."""

from __future__ import annotations

import argparse
import json
import os
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
    grader_export_sha256: str, grader_prompt_sha256: str,
) -> dict[str, dict[str, Any]]:
    require(response.get("schema_version") == grading.GRADER_RESPONSE_SCHEMA_VERSION,
            f"grader response schema_version must be "
            f"{grading.GRADER_RESPONSE_SCHEMA_VERSION}")
    require(response.get("grading_pack_sha256") == grading_pack_sha256,
            "grader response names a different grading-pack digest")
    require(response.get("grader_export_sha256") == grader_export_sha256,
            "grader response names a different grader-only export digest")
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
    parser.add_argument("--runs-root", type=Path, required=True)
    parser.add_argument("--grading-pack", type=Path, required=True)
    parser.add_argument("--grader-export", type=Path, required=True)
    parser.add_argument("--grader-response", type=Path, action="append", required=True)
    parser.add_argument("--adjudication", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    require(len(args.grader_response) == 2, "exactly two grader responses are required")
    output = grading.canonical_new_output(args.output, "grade-ledger output")
    pack = grading.canonical_existing_path(
        args.pack, directory=True, label="sealed pack"
    )
    runs_root = grading.canonical_existing_path(
        args.runs_root, directory=True, label="runs root"
    )
    grading_pack = grading.canonical_existing_path(
        args.grading_pack, directory=True, label="internal grading-pack"
    )
    grader_export = grading.canonical_existing_path(
        args.grader_export, directory=True, label="grader-only export"
    )
    for source_root, source_label in (
        (pack, "sealed pack"),
        (runs_root, "runs root"),
        (grading_pack, "internal grading-pack"),
        (grader_export, "grader-only export"),
    ):
        grading.require_separate_trees(
            output,
            source_root,
            left_label="grade-ledger output",
            right_label=source_label,
        )
    prepare.verify_pack(pack)
    config = load(pack / "execution_config.json")
    require(config["suite_id"] == "ABRL-TARGET-DRIFT-V2", "assembler requires v2 pack")
    current = Path(__file__).resolve()
    expected_script_hash = config["analysis"]["grade_assembler_sha256"]
    require(grading.sha256_bytes(grading.read_plain_file(
        current, "current grade assembler"
    )) == expected_script_hash,
            "invoked grade assembler differs from frozen hash")
    require(grading.sha256_bytes(grading.read_plain_file(
        pack / "execution_code" / current.name, "sealed grade assembler"
    )) == expected_script_hash,
            "sealed grade assembler differs from frozen hash")
    prepare_path = Path(prepare.__file__).resolve()
    prepare_hash = config["sealed_agent_view"]["materializer_sha256"]
    require(grading.sha256_bytes(grading.read_plain_file(
        prepare_path, "current pack verifier"
    )) == prepare_hash,
            "imported pack verifier differs from frozen hash")
    require(grading.sha256_bytes(grading.read_plain_file(
        pack / "execution_code" / prepare_path.name, "sealed pack verifier"
    )) == prepare_hash, "sealed pack verifier differs from frozen hash")
    grading_path = Path(grading.__file__).resolve()
    grading_hash = config["grading"]["packet_materializer_sha256"]
    require(grading.sha256_bytes(grading.read_plain_file(
        grading_path, "current grading materializer"
    )) == grading_hash,
            "imported grading materializer differs from frozen hash")
    require(grading.sha256_bytes(grading.read_plain_file(
        pack / "execution_code" / grading_path.name, "sealed grading materializer"
    )) == grading_hash, "sealed grading materializer differs from frozen hash")
    require(
        config["grading"]["grader_conflict_policy"]
        == "adjudicate every disagreement on a primary or secondary binary label or the structured source-critical field list",
        "unsupported frozen grader conflict policy",
    )
    configured_graders = config["grading"]["primary_grader_ids"]
    require(isinstance(configured_graders, list) and len(configured_graders) == 2
            and len(set(configured_graders)) == 2,
            "frozen primary_grader_ids must contain two unique identifiers")

    internal = grading.validate_internal_grading_pack_against_runs(
        pack, runs_root, grading_pack, config,
        expected_count=grading.PRODUCTION_PACKET_COUNT,
    )
    packet_manifest = internal["manifest"]
    mapping = internal["mapping"]
    packet_by_grade_id = internal["packets"]
    packet_ids = internal["packet_ids"]
    grader_export_manifest = grading.validate_grader_export(
        pack, runs_root, grading_pack, grader_export, config,
        expected_count=grading.PRODUCTION_PACKET_COUNT,
    )
    grader_export_sha256 = grader_export_manifest["grader_export_sha256"]
    sealed_pack_sha256 = (pack / "aggregate.sha256").read_text(encoding="ascii").strip()
    runtime_sha256 = prepare.checker_runtime_config_sha256(config)
    require(len(packet_ids) == packet_manifest["packet_count"] == 450,
            "grading pack must contain exactly 450 unique packets")

    response_payloads = [
        grading.read_plain_file(
            Path(os.path.abspath(path)), f"grader response {index + 1}"
        )
        for index, path in enumerate(args.grader_response)
    ]
    responses = [
        grading.json_from_bytes(payload, f"grader response {index + 1}")
        for index, payload in enumerate(response_payloads)
    ]
    response_ids = [response.get("grader_id") for response in responses]
    require(response_ids == configured_graders,
            "grader response order/identities differ from frozen config")
    indexed = [
        by_grade_id(
            response,
            packet_ids,
            packet_manifest["aggregate_sha256"],
            grader_export_sha256,
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
    adjudication_payload = grading.read_plain_file(
        Path(os.path.abspath(args.adjudication)), "adjudication"
    )
    adjudication = grading.json_from_bytes(adjudication_payload, "adjudication")
    require(adjudication.get("schema_version") == grading.GRADER_RESPONSE_SCHEMA_VERSION,
            f"adjudication schema_version must be "
            f"{grading.GRADER_RESPONSE_SCHEMA_VERSION}")
    require(adjudication.get("grading_pack_sha256") == packet_manifest["aggregate_sha256"],
            "adjudication names a different grading-pack digest")
    require(adjudication.get("grader_export_sha256") == grader_export_sha256,
            "adjudication names a different grader-only export digest")
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
    grade_ledger = {
        "schema_version": 2,
        "suite_id": config["suite_id"],
        "sealed_pack_sha256": sealed_pack_sha256,
        "grading_pack_sha256": packet_manifest["aggregate_sha256"],
        "grader_export_sha256": grader_export_sha256,
        "grade_assembler_sha256": expected_script_hash,
        "grader_response_sha256": {
            grader_id: grading.sha256_bytes(payload)
            for grader_id, payload in zip(response_ids, response_payloads)
        },
        "adjudication_sha256": grading.sha256_bytes(adjudication_payload),
        "assembly_input_sha256": grading.digest_payloads({
            "grader-response-1.json": response_payloads[0],
            "grader-response-2.json": response_payloads[1],
            "adjudication.json": adjudication_payload,
            "internal-grading-pack.sha256": (
                packet_manifest["aggregate_sha256"] + "\n"
            ).encode("ascii"),
            "grader-input.sha256": (grader_export_sha256 + "\n").encode("ascii"),
        }),
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
    }
    grading.write_atomic_file(
        output, grading.canonical_json_bytes(grade_ledger), "grade-ledger output"
    )
    print(
        f"assembled 450 target-drift grades: disagreements={len(conflicts)}, "
        f"primary_raw_agreement={raw_agreement:.6f}"
    )


if __name__ == "__main__":
    main()
