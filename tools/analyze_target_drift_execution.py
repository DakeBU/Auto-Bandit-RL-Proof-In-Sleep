#!/usr/bin/env python3
"""Frozen target-level analysis for completed ABRL target-drift v2 grades."""

from __future__ import annotations

import argparse
import hashlib
import json
import math
import random
import sys
from collections import defaultdict
from pathlib import Path
from statistics import mean
from typing import Any


CONDITIONS = ("compile_only", "source_aware_blueprint", "abrl")
PRIMARY_CONDITIONS = ("source_aware_blueprint", "abrl")
REQUIREMENT_VARIANTS = ("source_faithful", "injected_drift")
BINARY_FIELDS = (
    "primary_pass",
    "faithful_formal_completion",
    "drift_detected",
    "false_rejection",
    "unsupported_evidence_claim",
    "source_amendment_required",
    "artifact_replay_success",
)
INTEGER_EXECUTION_METRICS = (
    "input_tokens",
    "cached_input_tokens",
    "cache_write_input_tokens",
    "output_tokens",
    "reasoning_output_tokens",
    "tool_calls",
    "build_attempts",
    "recovery_tool_calls",
    "infrastructure_retries",
)
NUMBER_EXECUTION_METRICS = (
    "wall_seconds",
    "orchestrator_wall_seconds",
    "cost_usd",
)

TOOLS = Path(__file__).resolve().parent
sys.path.insert(0, str(TOOLS))

import prepare_target_drift_execution as prepare  # noqa: E402
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
        raise SystemExit(f"target-drift analysis failed: {message}")


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


def verify_grading_pack(grading_pack: Path, sealed_pack_sha256: str,
                        grader_prompt_sha256: str,
                        completion_ledger_sha256: str) -> dict[str, Any]:
    manifest_path = grading_pack / "packet-manifest.json"
    mapping_path = grading_pack / "operator-mapping.json"
    require(manifest_path.is_file() and mapping_path.is_file(),
            "grading pack manifest or operator mapping is missing")
    manifest = load(manifest_path)
    require(manifest.get("sealed_pack_sha256") == sealed_pack_sha256,
            "grading pack names a different sealed pack")
    require(manifest.get("grader_prompt_sha256") == grader_prompt_sha256,
            "grading pack names a different grader prompt")
    mapping_payload = mapping_path.read_bytes()
    completion_path = grading_pack / "completion-ledger.json"
    require(completion_path.is_file(), "grading-pack completion ledger is missing")
    completion_payload = completion_path.read_bytes()
    require(hashlib.sha256(completion_payload).hexdigest() == completion_ledger_sha256
            == manifest.get("completion_ledger_sha256"),
            "grading-pack completion ledger hash mismatch")
    require(hashlib.sha256(mapping_payload).hexdigest()
            == manifest.get("operator_mapping_sha256"),
            "grading-pack operator mapping hash mismatch")
    packet_hashes = manifest.get("packet_sha256")
    require(isinstance(packet_hashes, dict) and len(packet_hashes) == manifest.get("packet_count"),
            "grading-pack packet hash ledger is incomplete")
    payloads: dict[str, bytes] = {}
    for name, expected in packet_hashes.items():
        path = grading_pack / name
        require(path.is_file(), f"grading packet is missing: {name}")
        payload = path.read_bytes()
        require(hashlib.sha256(payload).hexdigest() == expected,
                f"grading packet hash mismatch: {name}")
        payloads[name] = payload
    require(digest_payloads(payloads) == manifest.get("packet_aggregate_sha256"),
            "grading packet aggregate mismatch")
    require(digest_payloads({
        **payloads,
        "operator-mapping.json": mapping_payload,
        "completion-ledger.json": completion_payload,
    })
            == manifest.get("aggregate_sha256"),
            "grading-pack aggregate mismatch")
    return manifest


def incomplete_analysis(ledger: dict[str, Any]) -> dict[str, Any]:
    """Return a non-inferential report; deliberately omit every numeric effect field."""
    return {
        "schema_version": 1,
        "suite_id": "ABRL-TARGET-DRIFT-V2",
        "analysis_status": "not_estimable_incomplete_preregistered_run_universe",
        "result_eligible": False,
        "primary_analysis_permitted": False,
        "planned_run_count": ledger["planned_run_count"],
        "result_eligible_run_count": ledger["summary"]["result_eligible_count"],
        "missing_run_count": ledger["summary"]["missing_count"],
        "missingness": {
            key: value for key, value in ledger["summary"].items()
            if key not in {"result_eligible_count", "missing_count"}
        },
        "replacement_runs_permitted": False,
        "outcome_imputation_permitted": False,
        "primary": {
            "status": "not_reported",
            "reason": "the frozen policy requires 450/450 production-result-eligible graded records",
        },
        "secondary_endpoints": {
            "status": "not_reported",
            "reason": "incomplete execution cannot enter the preregistered inferential family",
        },
        "reporting_boundary": "No point estimate, interval, p-value, q-value, or success claim is produced from an incomplete run universe.",
    }


def percentile(values: list[float], probability: float) -> float:
    ordered = sorted(values)
    index = probability * (len(ordered) - 1)
    lower = int(index)
    upper = min(lower + 1, len(ordered) - 1)
    fraction = index - lower
    return ordered[lower] * (1 - fraction) + ordered[upper] * fraction


def validate_execution_metrics(metrics: Any, run_id: str) -> None:
    require(isinstance(metrics, dict),
            f"execution_metrics must be an object for {run_id}")
    for field in INTEGER_EXECUTION_METRICS:
        value = metrics.get(field)
        require(type(value) is int and value >= 0,
                f"execution metric {field} must be a nonnegative integer for {run_id}")
    for field in NUMBER_EXECUTION_METRICS:
        value = metrics.get(field)
        require(isinstance(value, (int, float)) and not isinstance(value, bool)
                and math.isfinite(float(value)) and value >= 0,
                f"execution metric {field} must be a nonnegative number for {run_id}")
    require(metrics["cached_input_tokens"] + metrics["cache_write_input_tokens"]
            <= metrics["input_tokens"],
            f"cached input categories exceed input tokens for {run_id}")
    require(metrics["reasoning_output_tokens"] <= metrics["output_tokens"],
            f"reasoning output exceeds output tokens for {run_id}")


def validate_record_fields(records: list[dict[str, Any]]) -> None:
    for record in records:
        run_id = str(record.get("semantic_run_id", "<missing-run-id>"))
        require(isinstance(record.get("semantic_run_id"), str)
                and record["semantic_run_id"],
                "semantic_run_id must be nonempty")
        require(all(type(record.get(field)) is bool for field in BINARY_FIELDS),
                f"binary endpoint field is missing or non-boolean for {run_id}")
        require(record.get("condition") in CONDITIONS, f"unknown condition for {run_id}")
        require(record.get("requirement_variant") in REQUIREMENT_VARIANTS,
                f"unknown requirement variant for {run_id}")
        require(isinstance(record.get("case_id"), str) and record["case_id"],
                f"case_id must be nonempty for {run_id}")
        require(isinstance(record.get("source_id"), str) and record["source_id"],
                f"source_id must be nonempty for {run_id}")
        require(record.get("stratum") in {"paper_derived", "textbook_control"},
                f"unknown stratum for {run_id}")
        guesses = record.get("grader_condition_guesses")
        require(isinstance(guesses, dict) and len(guesses) == 2
                and all(isinstance(grader, str) and grader for grader in guesses)
                and all(guess in CONDITIONS for guess in guesses.values()),
                f"grader condition guesses are malformed for {run_id}")
        validate_execution_metrics(record.get("execution_metrics"), run_id)


def validate_fixed_run_universe(records: list[dict[str, Any]]) -> None:
    """Verify five fresh invocations and the fixed 2/3 variant allocation per cell."""
    grouped: dict[tuple[str, str], list[dict[str, Any]]] = defaultdict(list)
    for record in records:
        grouped[(record["case_id"], record["condition"])].append(record)
    require(len(grouped) == 30 * len(CONDITIONS),
            "fixed benchmark must contain all thirty target-condition cells")
    for (case_id, condition), cell in grouped.items():
        require(len(cell) == 5,
                f"target-condition cell must contain five fresh invocations: {case_id}/{condition}")
        require(all(type(record.get("replicate")) is int for record in cell)
                and {record["replicate"] for record in cell} == set(range(5)),
                f"target-condition invocation labels must be integers 0..4: {case_id}/{condition}")
        counts = {
            variant: sum(record["requirement_variant"] == variant for record in cell)
            for variant in REQUIREMENT_VARIANTS
        }
        require(sorted(counts.values()) == [2, 3],
                f"target-condition variant allocation must be 2/3: {case_id}/{condition}")
    for case_id in {record["case_id"] for record in records}:
        reference = None
        for condition in CONDITIONS:
            cell = grouped[(case_id, condition)]
            counts = tuple(
                sum(record["requirement_variant"] == variant for record in cell)
                for variant in REQUIREMENT_VARIANTS
            )
            require(reference is None or counts == reference,
                    f"conditions disagree on fixed variant counts for {case_id}")
            reference = counts


def validate_fixed_target_metadata(metadata: dict[str, dict[str, str]]) -> None:
    paper_sources: dict[str, int] = defaultdict(int)
    textbook_targets = 0
    for entry in metadata.values():
        if entry["stratum"] == "paper_derived":
            paper_sources[entry["source_id"]] += 1
        else:
            textbook_targets += 1
    require(len(paper_sources) == 3
            and sorted(paper_sources.values()) == [6, 6, 6]
            and textbook_targets == 12,
            "fixed benchmark must contain three six-target paper clusters and "
            "twelve textbook targets")


def target_scores(records: list[dict[str, Any]]) -> dict[tuple[str, str], float]:
    grouped: dict[tuple[str, str], list[float]] = defaultdict(list)
    for record in records:
        grouped[(record["case_id"], record["condition"])].append(
            1.0 if record["primary_pass"] else 0.0
        )
    require(all(len(values) == 5 for values in grouped.values()),
            "every target-condition must contain five graded replicates")
    return {key: mean(values) for key, values in grouped.items()}


def target_metric_scores(
    records: list[dict[str, Any]], value, predicate=lambda _record: True
) -> dict[tuple[str, str], float]:
    grouped: dict[tuple[str, str], list[float]] = defaultdict(list)
    for record in records:
        if predicate(record):
            grouped[(record["case_id"], record["condition"])].append(float(value(record)))
    expected = {(record["case_id"], condition) for record in records for condition in CONDITIONS}
    require(set(grouped) == expected, "secondary metric is missing a target-condition cell")
    return {key: mean(values) for key, values in grouped.items()}


def benjamini_hochberg(pvalues: dict[str, float]) -> dict[str, float]:
    ordered = sorted(pvalues.items(), key=lambda item: item[1])
    adjusted: dict[str, float] = {}
    running = 1.0
    count = len(ordered)
    for reverse_index in range(count - 1, -1, -1):
        name, value = ordered[reverse_index]
        rank = reverse_index + 1
        running = min(running, value * count / rank)
        adjusted[name] = min(1.0, running)
    return adjusted


def fixed_benchmark_invocation_bootstrap(
    records: list[dict[str, Any]], seed: int, replicates: int,
) -> list[float]:
    """Bootstrap fresh invocations while keeping all 30 targets and variants fixed.

    The five replicate labels are not provider seeds and do not pair model
    randomness across conditions.  Resampling is therefore independent within
    each target/condition/variant cell.  The deterministic 2/3 requirement-
    variant allocation is retained in every draw.
    """
    grouped: dict[tuple[str, str, str], list[float]] = defaultdict(list)
    case_ids = sorted({record["case_id"] for record in records})
    for record in records:
        grouped[(
            record["case_id"], record["condition"], record["requirement_variant"]
        )].append(1.0 if record["primary_pass"] else 0.0)
    rng = random.Random(seed)
    draws = []
    for _ in range(replicates):
        differences = []
        for case_id in case_ids:
            condition_means: dict[str, float] = {}
            for condition in PRIMARY_CONDITIONS:
                sampled = []
                for variant in REQUIREMENT_VARIANTS:
                    values = grouped[(case_id, condition, variant)]
                    require(len(values) in {2, 3},
                            "fixed invocation bootstrap encountered a non-2/3 cell")
                    sampled.extend(rng.choice(values) for _ in values)
                condition_means[condition] = mean(sampled)
            differences.append(
                condition_means["abrl"] - condition_means["source_aware_blueprint"]
            )
        draws.append(mean(differences))
    return draws


def source_aware_exact_sign_flip_pvalue(
    differences: dict[str, float], metadata: dict[str, dict[str, str]]
) -> tuple[float, int]:
    """Exact sign flip over three paper clusters and twelve textbook targets."""
    paper_units: dict[str, list[str]] = defaultdict(list)
    textbook_units: list[str] = []
    for case_id in differences:
        if metadata[case_id]["stratum"] == "paper_derived":
            paper_units[metadata[case_id]["source_id"]].append(case_id)
        else:
            textbook_units.append(case_id)
    units = [sorted(values) for _, values in sorted(paper_units.items())]
    units.extend([[case_id] for case_id in sorted(textbook_units)])
    require(len(units) == 15, "expected three paper clusters and twelve textbook units")
    observed = abs(mean(differences.values()))
    assignments = 1 << len(units)
    exceed = 0
    for mask in range(assignments):
        signed: list[float] = []
        for unit_index, cases in enumerate(units):
            sign = 1.0 if (mask >> unit_index) & 1 else -1.0
            signed.extend(sign * differences[case_id] for case_id in cases)
        if abs(mean(signed)) >= observed - 1e-15:
            exceed += 1
    return exceed / assignments, assignments


def sign_flip_sensitivity_record(pvalue: float, assignments: int) -> dict[str, Any]:
    return {
        "status": "preregistered_sensitivity_analysis",
        "two_sided_pvalue": pvalue,
        "enumerated_assignments": assignments,
        "dependence_units": 15,
        "unit_definition": (
            "Three paper-source clusters plus twelve individual frozen textbook targets."
        ),
        "assumption": (
            "The 15 bundled ABRL-minus-source-aware differences are jointly sign-"
            "exchangeable at the stated dependence-unit boundary."
        ),
        "inference_boundary": (
            "Enumeration is exact conditional on that sign-exchangeability assumption. "
            "It is a fixed-benchmark sensitivity analysis, not evidence that 450 runs "
            "are independent and not an estimate for a population of papers or targets."
        ),
    }


def target_weighted_variant_rates(records: list[dict[str, Any]]) -> dict[str, Any]:
    """Give every frozen target equal weight after within-target aggregation."""
    specifications = {
        "injected_drift_primary_pass_rate": (
            lambda record: record["primary_pass"], "injected_drift",
        ),
        "source_faithful_primary_pass_rate": (
            lambda record: record["primary_pass"], "source_faithful",
        ),
        "injected_drift_detection_sensitivity": (
            lambda record: record["drift_detected"], "injected_drift",
        ),
        "faithful_request_specificity": (
            lambda record: not record["false_rejection"], "source_faithful",
        ),
        "false_rejection_rate": (
            lambda record: record["false_rejection"], "source_faithful",
        ),
    }
    rates = {condition: {} for condition in CONDITIONS}
    for name, (value, variant) in specifications.items():
        scores = target_metric_scores(
            records, value,
            lambda record, selected=variant: record["requirement_variant"] == selected,
        )
        for condition in CONDITIONS:
            rates[condition][name] = mean(
                score for (case_id, candidate), score in scores.items()
                if candidate == condition
            )
    return {
        "analysis_role": "target_weighted_fixed_benchmark_inferential_reporting",
        "weighting": (
            "Each of the 30 frozen targets has equal weight after averaging the "
            "two or three applicable fresh invocations within target and condition."
        ),
        "inference_boundary": (
            "These rates describe the fixed benchmark and do not estimate a paper, "
            "theorem, or target population."
        ),
        "conditions": rates,
    }


def raw_run_weighted_variant_rates(records: list[dict[str, Any]]) -> dict[str, Any]:
    """Retain transparent raw counts without treating 450 runs as independent targets."""
    conditions: dict[str, Any] = {}
    for condition in CONDITIONS:
        selected = [record for record in records if record["condition"] == condition]
        faithful = [
            record for record in selected
            if record["requirement_variant"] == "source_faithful"
        ]
        drifted = [
            record for record in selected
            if record["requirement_variant"] == "injected_drift"
        ]
        require(len(selected) == 150 and len(faithful) == len(drifted) == 75,
                f"condition {condition} must contain 150 runs split 75/75")

        def count_rate(group: list[dict[str, Any]], value) -> dict[str, Any]:
            count = sum(bool(value(record)) for record in group)
            return {"count": count, "denominator": len(group), "rate": count / len(group)}

        conditions[condition] = {
            "run_count": len(selected),
            "injected_drift": {
                "run_count": len(drifted),
                "primary_pass": count_rate(drifted, lambda record: record["primary_pass"]),
                "drift_detected": count_rate(drifted, lambda record: record["drift_detected"]),
            },
            "source_faithful": {
                "run_count": len(faithful),
                "primary_pass": count_rate(faithful, lambda record: record["primary_pass"]),
                "specificity": count_rate(faithful, lambda record: not record["false_rejection"]),
                "false_rejection": count_rate(
                    faithful, lambda record: record["false_rejection"]
                ),
            },
        }
    return {
        "status": "descriptive_only",
        "weighting": (
            "Every invocation has equal weight, so targets with three rather than two "
            "applicable variant invocations receive more weight."
        ),
        "inference_boundary": (
            "Raw run-weighted rates and counts are audit summaries only; they are not "
            "used as the fixed-target primary estimand or as 450 independent samples."
        ),
        "conditions": conditions,
    }


def blinding_audit(records: list[dict[str, Any]]) -> dict[str, float]:
    grader_ids = sorted(records[0]["grader_condition_guesses"])
    require(len(grader_ids) == 2, "expected two condition guesses per record")
    require(all(sorted(record["grader_condition_guesses"]) == grader_ids
                for record in records),
            "grader condition-guess identities differ across records")
    return {
        grader_id: mean(
            record["grader_condition_guesses"][grader_id] == record["condition"]
            for record in records
        )
        for grader_id in grader_ids
    }


def source_stratified_condition_means(
    scores: dict[tuple[str, str], float], metadata: dict[str, dict[str, str]]
) -> dict[str, Any]:
    source_ids = sorted({entry["source_id"] for entry in metadata.values()})
    strata = sorted({entry["stratum"] for entry in metadata.values()})

    def means(case_ids: list[str]) -> dict[str, float]:
        return {
            condition: mean(scores[(case_id, condition)] for case_id in case_ids)
            for condition in CONDITIONS
        }

    return {
        "by_source": {
            source_id: means([
                case_id for case_id, entry in metadata.items()
                if entry["source_id"] == source_id
            ])
            for source_id in source_ids
        },
        "by_stratum": {
            stratum: means([
                case_id for case_id, entry in metadata.items()
                if entry["stratum"] == stratum
            ])
            for stratum in strata
        },
    }


def secondary_analyses(
    records: list[dict[str, Any]], metadata: dict[str, dict[str, str]]
) -> dict[str, Any]:
    specifications = {
        "faithful_formal_completion": (
            lambda record: record["faithful_formal_completion"],
            lambda record: True,
            "higher_is_better",
        ),
        "drift_detection_sensitivity": (
            lambda record: record["drift_detected"],
            lambda record: record["requirement_variant"] == "injected_drift",
            "higher_is_better",
        ),
        "faithful_request_specificity": (
            lambda record: not record["false_rejection"],
            lambda record: record["requirement_variant"] == "source_faithful",
            "higher_is_better",
        ),
        "unsupported_evidence_claim_rate": (
            lambda record: record["unsupported_evidence_claim"],
            lambda record: True,
            "lower_is_better",
        ),
        "recovery_cost": (
            lambda record: record["execution_metrics"]["recovery_tool_calls"],
            lambda record: True,
            "lower_is_better",
        ),
        "wall_time": (
            lambda record: record["execution_metrics"]["orchestrator_wall_seconds"],
            lambda record: True,
            "lower_is_better",
        ),
        "model_tokens": (
            lambda record: record["execution_metrics"]["input_tokens"]
            + record["execution_metrics"]["output_tokens"],
            lambda record: True,
            "lower_is_better",
        ),
        "uncached_input_tokens": (
            lambda record: record["execution_metrics"]["input_tokens"]
            - record["execution_metrics"]["cached_input_tokens"]
            - record["execution_metrics"]["cache_write_input_tokens"],
            lambda record: True,
            "lower_is_better",
        ),
        "cache_write_input_tokens": (
            lambda record: record["execution_metrics"]["cache_write_input_tokens"],
            lambda record: True,
            "lower_is_better",
        ),
        "reasoning_output_tokens": (
            lambda record: record["execution_metrics"]["reasoning_output_tokens"],
            lambda record: True,
            "lower_is_better",
        ),
        "tool_calls": (
            lambda record: record["execution_metrics"]["tool_calls"],
            lambda record: True,
            "lower_is_better",
        ),
        "build_attempts": (
            lambda record: record["execution_metrics"]["build_attempts"],
            lambda record: True,
            "lower_is_better",
        ),
        "model_cost_usd": (
            lambda record: record["execution_metrics"]["cost_usd"],
            lambda record: True,
            "lower_is_better",
        ),
        "artifact_replay_success": (
            lambda record: record["artifact_replay_success"],
            lambda record: True,
            "higher_is_better",
        ),
    }
    results: dict[str, Any] = {}
    pvalues: dict[str, float] = {}
    for name, (value, predicate, direction) in specifications.items():
        scores = target_metric_scores(records, value, predicate)
        raw_differences = {
            case_id: scores[(case_id, "abrl")] - scores[(case_id, "source_aware_blueprint")]
            for case_id in metadata
        }
        sign = 1.0 if direction == "higher_is_better" else -1.0
        oriented = {case_id: sign * difference for case_id, difference in raw_differences.items()}
        pvalue, assignments = source_aware_exact_sign_flip_pvalue(oriented, metadata)
        pvalues[name] = pvalue
        results[name] = {
            "direction": direction,
            "abrl_minus_source_aware_point_estimate": mean(raw_differences.values()),
            "oriented_benefit_point_estimate": mean(oriented.values()),
            "exact_sign_flip_15_unit_sensitivity": sign_flip_sensitivity_record(
                pvalue, assignments
            ),
            "condition_means": {
                condition: mean(
                    score for (case_id, candidate), score in scores.items()
                    if candidate == condition
                )
                for condition in CONDITIONS
            },
            "source_stratified_condition_means": source_stratified_condition_means(
                scores, metadata
            ),
        }
    adjusted = benjamini_hochberg(pvalues)
    for name, qvalue in adjusted.items():
        results[name]["benjamini_hochberg_qvalue"] = qvalue
        results[name]["bh_reject_at_q_0_05"] = qvalue <= 0.05
    specificity = results["faithful_request_specificity"]
    results["false_rejection_rate"] = {
        "inferential_status": "descriptive exact complement of faithful_request_specificity; excluded from the BH family",
        "condition_means": {
            condition: 1.0 - value
            for condition, value in specificity["condition_means"].items()
        },
        "source_stratified_condition_means": {
            level: {
                key: {condition: 1.0 - value for condition, value in means.items()}
                for key, means in groups.items()
            }
            for level, groups in specificity["source_stratified_condition_means"].items()
        },
    }
    return results


def primary_success_record(
    interval: list[float],
    leave_one_paper_out: dict[str, float],
    target_weighted_rates: dict[str, Any],
) -> dict[str, Any]:
    lower = interval[0]
    sensitivity = {
        condition: values["injected_drift_detection_sensitivity"]
        for condition, values in target_weighted_rates["conditions"].items()
    }
    specificity = {
        condition: values["faithful_request_specificity"]
        for condition, values in target_weighted_rates["conditions"].items()
    }
    interval_gate = {
        "rule": "fixed-benchmark invocation-bootstrap lower endpoint > 0",
        "observed_lower_endpoint": lower,
        "threshold": 0.0,
        "passed": lower > 0.0,
    }
    loo_gate = {
        "rule": "all three leave-one-paper-out fixed-benchmark point estimates >= 0",
        "required_source_count": 3,
        "observed_source_count": len(leave_one_paper_out),
        "observed": leave_one_paper_out,
        "passed": len(leave_one_paper_out) == 3
        and all(value >= 0.0 for value in leave_one_paper_out.values()),
    }
    sensitivity_gate = {
        "rule": "target-weighted injected-drift sensitivity reported for every condition",
        "observed": sensitivity,
        "passed": set(sensitivity) == set(CONDITIONS)
        and all(isinstance(value, (int, float)) and not isinstance(value, bool)
                and 0.0 <= value <= 1.0 for value in sensitivity.values()),
    }
    specificity_gate = {
        "rule": "target-weighted faithful-request specificity reported for every condition",
        "observed": specificity,
        "passed": set(specificity) == set(CONDITIONS)
        and all(isinstance(value, (int, float)) and not isinstance(value, bool)
                and 0.0 <= value <= 1.0 for value in specificity.values()),
    }
    gates = {
        "interval_lower_above_zero": interval_gate,
        "leave_one_paper_out_nonnegative": loo_gate,
        "injected_drift_sensitivity_reported": sensitivity_gate,
        "faithful_request_specificity_reported": specificity_gate,
    }
    passed = all(gate["passed"] for gate in gates.values())
    return {
        "status": "passed" if passed else "failed",
        "all_required_gates_passed": passed,
        "gates": gates,
        "claim_boundary": (
            "Passing is a prespecified success decision for the 30 frozen targets under "
            "the bundled-workflow ITT estimand. It is not paper-population generalization, "
            "mechanism attribution, or an acceptance claim."
        ),
    }


def analyze(
    data: dict[str, Any], seed: int, bootstrap_replicates: int,
    permutation_replicates: int,
) -> dict[str, Any]:
    records = data["records"]
    require(len(records) == 450, "analysis requires exactly 450 graded runs")
    require(type(seed) is int, "bootstrap seed must be an integer")
    require(type(bootstrap_replicates) is int and bootstrap_replicates > 0,
            "bootstrap replicate count must be a positive integer")
    validate_record_fields(records)
    require(len({record["semantic_run_id"] for record in records}) == 450,
            "semantic run identifiers must be unique")
    run_keys = {
        (record["case_id"], record["condition"], record["replicate"])
        for record in records
    }
    require(len(run_keys) == 450,
            "target-condition-replicate keys must be unique")
    validate_fixed_run_universe(records)
    paired_variants: dict[tuple[str, Any], str] = {}
    for record in records:
        key = (record["case_id"], record["replicate"])
        require(key not in paired_variants or paired_variants[key] == record["requirement_variant"],
                "conditions disagree on the hidden requirement variant within a paired replicate")
        paired_variants[key] = record["requirement_variant"]
    require(len(paired_variants) == 150,
            "expected 150 target-replicate variant assignments")

    metadata: dict[str, dict[str, str]] = {}
    for record in records:
        candidate = {"source_id": record["source_id"], "stratum": record["stratum"]}
        require(record["case_id"] not in metadata or metadata[record["case_id"]] == candidate,
                "target metadata is inconsistent")
        metadata[record["case_id"]] = candidate
    require(len(metadata) == 30, "expected thirty targets")
    validate_fixed_target_metadata(metadata)

    scores = target_scores(records)
    differences = {
        case_id: scores[(case_id, "abrl")] - scores[(case_id, "source_aware_blueprint")]
        for case_id in metadata
    }
    point = mean(differences.values())
    bootstrap = fixed_benchmark_invocation_bootstrap(
        records, seed, bootstrap_replicates
    )
    interval = [percentile(bootstrap, 0.025), percentile(bootstrap, 0.975)]
    pvalue, exact_assignments = source_aware_exact_sign_flip_pvalue(differences, metadata)
    require(permutation_replicates == exact_assignments,
            f"frozen permutation_replicates must equal exact assignment count {exact_assignments}")
    leave_one_paper_out = {}
    paper_sources = sorted({
        value["source_id"] for value in metadata.values()
        if value["stratum"] == "paper_derived"
    })
    for source in paper_sources:
        kept = [
            value for case_id, value in differences.items()
            if metadata[case_id]["source_id"] != source
        ]
        leave_one_paper_out[source] = mean(kept)

    target_weighted_rates = target_weighted_variant_rates(records)
    raw_run_weighted_rates = raw_run_weighted_variant_rates(records)
    success = primary_success_record(interval, leave_one_paper_out, target_weighted_rates)

    return {
        "schema_version": 1,
        "suite_id": "ABRL-TARGET-DRIFT-V2",
        "run_count": len(records),
        "target_count": len(metadata),
        "primary": {
            "estimand": (
                "Equal-target-weighted mean bundled-workflow intention-to-treat effect "
                "on the 30 frozen targets: ABRL minus source-aware blueprint primary-pass "
                "rate after averaging five fresh invocations within each target-condition."
            ),
            "estimand_population": "the fixed set of 30 frozen targets only",
            "treatment_boundary": (
                "Each condition is a bundled prompt/resource/workflow assignment. The "
                "contrast does not identify any single ABRL mechanism."
            ),
            "replicate_semantics": (
                "Five fresh, separately initiated provider invocations per target-"
                "condition are the planned repeated-sampling units. Independence is "
                "an analysis assumption; replicate integers are labels, not provider "
                "seeds, and do not pair model randomness across conditions."
            ),
            "point_estimate": point,
            "fixed_benchmark_invocation_bootstrap_95_interval": interval,
            "interval_boundary": (
                "The bootstrap resamples invocations independently within each fixed "
                "target/condition/requirement-variant cell. It quantifies fresh-invocation "
                "variation conditional on this benchmark and is not a paper- or target-"
                "population interval."
            ),
            "exact_sign_flip_15_unit_sensitivity": sign_flip_sensitivity_record(
                pvalue, exact_assignments
            ),
            "bootstrap_seed": seed,
            "bootstrap_replicates": bootstrap_replicates,
            "leave_one_paper_out_fixed_benchmark_point_estimates": leave_one_paper_out,
            "success_rule": success,
        },
        "target_weighted_variant_rates": target_weighted_rates,
        "raw_run_weighted_variant_counts_and_rates": raw_run_weighted_rates,
        "primary_source_stratified_condition_means": source_stratified_condition_means(
            scores, metadata
        ),
        "secondary_endpoints_bh_q_0_05": secondary_analyses(records, metadata),
        "secondary_analysis_boundary": (
            "Benjamini-Hochberg adjusts the preregistered family of 15-unit exact-"
            "sign-flip sensitivity p-values. These remain fixed-benchmark sensitivity "
            "analyses and do not support paper- or target-population inference."
        ),
        "grader_condition_guess_accuracy": blinding_audit(records),
        "grading_summary": data.get("grading_summary"),
        "inference_boundary": (
            "The confirmatory estimand is restricted to the 30 frozen targets. Three "
            "external paper sources cannot support paper-population generalization; the "
            "15-unit sign flip is a dependence-aware sensitivity analysis, and raw run "
            "counts never turn 450 invocations into 450 independent targets."
        ),
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--pack", type=Path, required=True)
    parser.add_argument("--runs-root", type=Path, required=True)
    parser.add_argument("--completion-ledger", type=Path, required=True)
    parser.add_argument("--grading-pack", type=Path)
    parser.add_argument("--grades", type=Path)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    require(not args.output.exists(), "analysis output already exists")
    pack = args.pack.resolve()
    prepare.verify_pack(pack)
    config = load(pack / "execution_config.json")
    require(config["suite_id"] == "ABRL-TARGET-DRIFT-V2", "analysis requires v2 pack")
    current = Path(__file__).resolve()
    expected_script_hash = config["analysis"]["script_sha256"]
    require(hashlib.sha256(current.read_bytes()).hexdigest() == expected_script_hash,
            "invoked analysis script differs from frozen hash")
    require(hashlib.sha256((pack / "execution_code" / current.name).read_bytes()).hexdigest()
            == expected_script_hash,
            "sealed analysis script differs from frozen hash")
    prepare_path = Path(prepare.__file__).resolve()
    prepare_hash = config["sealed_agent_view"]["materializer_sha256"]
    require(hashlib.sha256(prepare_path.read_bytes()).hexdigest() == prepare_hash,
            "imported pack verifier differs from frozen hash")
    require(hashlib.sha256((pack / "execution_code" / prepare_path.name).read_bytes()).hexdigest()
            == prepare_hash, "sealed pack verifier differs from frozen hash")
    analysis_config = config["analysis"]
    sealed_pack_sha256 = (pack / "aggregate.sha256").read_text(encoding="ascii").strip()
    completion.self_verify(pack, config)
    completion_path = args.completion_ledger.resolve()
    completion_ledger = load(completion_path)
    completion.validate_ledger_against_runs(
        pack, args.runs_root.resolve(), completion_ledger, require_complete=False,
    )
    completion_ledger_sha256 = prepare.sha256_file(completion_path)
    if not completion_ledger["primary_analysis_permitted"]:
        require(args.grading_pack is None and args.grades is None,
                "incomplete analysis must not receive grades or a grading pack")
        result = incomplete_analysis(completion_ledger)
        result["sealed_pack_sha256"] = sealed_pack_sha256
        result["completion_ledger_sha256"] = completion_ledger_sha256
        result["missing_run_policy_id"] = completion_ledger["missing_run_policy_id"]
        result["missing_run_policy_sha256"] = completion_ledger["missing_run_policy_sha256"]
        dump(args.output, result)
        print(
            "target-drift inferential analysis refused: "
            f"eligible={result['result_eligible_run_count']}/450, "
            f"missing={result['missing_run_count']}"
        )
        raise SystemExit(2)
    require(args.grading_pack is not None and args.grades is not None,
            "complete analysis requires --grading-pack and --grades")
    grading_pack_manifest = verify_grading_pack(
        args.grading_pack.resolve(), sealed_pack_sha256,
        config["grading"]["grader_prompt_sha256"],
        completion_ledger_sha256,
    )
    grades = load(args.grades)
    runtime_sha256 = prepare.checker_runtime_config_sha256(config)
    require(config["posthoc_checker"]["mode"] == "production"
            and grading_pack_manifest.get("result_eligible") is True
            and grading_pack_manifest.get("checker_mode") == "production"
            and grades.get("result_eligible") is True
            and grades.get("checker_mode") == "production",
            "analysis rejects nonproduction or fixture-derived results")
    require(grading_pack_manifest.get("checker_runtime_config_sha256")
            == grades.get("checker_runtime_config_sha256")
            == config["posthoc_checker"]["runtime_config_sha256"]
            == runtime_sha256,
            "analysis checker runtime binding mismatch")
    require(grading_pack_manifest.get("isolation_probe_report_sha256")
            == grades.get("isolation_probe_report_sha256")
            == config["posthoc_checker"]["isolation_probe_report_sha256"],
            "analysis checker isolation-probe binding mismatch")
    require(grades.get("sealed_pack_sha256")
            == sealed_pack_sha256,
            "grade ledger names a different sealed pack")
    require(grades.get("grading_pack_sha256")
            == grading_pack_manifest["aggregate_sha256"],
            "grade ledger names a different grading pack")
    require(grades.get("completion_ledger_sha256") == completion_ledger_sha256
            == grading_pack_manifest.get("completion_ledger_sha256"),
            "analysis completion-ledger binding mismatch")
    require(grades.get("missing_run_policy_id")
            == grading_pack_manifest.get("missing_run_policy_id")
            == completion_ledger["missing_run_policy_id"]
            and grades.get("missing_run_policy_sha256")
            == grading_pack_manifest.get("missing_run_policy_sha256")
            == completion_ledger["missing_run_policy_sha256"],
            "analysis missing-run policy binding mismatch")
    result = analyze(
        grades,
        analysis_config["bootstrap_seed"],
        analysis_config["bootstrap_replicates"],
        analysis_config["permutation_replicates"],
    )
    result["sealed_pack_sha256"] = sealed_pack_sha256
    result["grading_pack_sha256"] = grading_pack_manifest["aggregate_sha256"]
    result["grade_ledger_sha256"] = prepare.sha256_file(args.grades.resolve())
    result["completion_ledger_sha256"] = completion_ledger_sha256
    result["missing_run_policy_id"] = completion_ledger["missing_run_policy_id"]
    result["missing_run_policy_sha256"] = completion_ledger["missing_run_policy_sha256"]
    result["result_eligible"] = True
    result["checker_mode"] = "production"
    result["checker_runtime_config_sha256"] = runtime_sha256
    result["isolation_probe_report_sha256"] = config["posthoc_checker"][
        "isolation_probe_report_sha256"
    ]
    dump(args.output, result)
    print(
        "target-drift analysis complete: "
        f"point={result['primary']['point_estimate']:.6f}, "
        "fixed-benchmark interval="
        f"{result['primary']['fixed_benchmark_invocation_bootstrap_95_interval']}, "
        f"success={result['primary']['success_rule']['status']}"
    )


if __name__ == "__main__":
    main()
