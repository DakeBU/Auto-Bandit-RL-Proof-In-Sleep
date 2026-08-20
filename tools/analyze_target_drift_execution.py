#!/usr/bin/env python3
"""Frozen target-level analysis for completed ABRL target-drift v2 grades."""

from __future__ import annotations

import argparse
import hashlib
import json
import random
import sys
from collections import defaultdict
from pathlib import Path
from statistics import mean
from typing import Any


CONDITIONS = ("compile_only", "source_aware_blueprint", "abrl")

TOOLS = Path(__file__).resolve().parent
sys.path.insert(0, str(TOOLS))

import prepare_target_drift_execution as prepare  # noqa: E402


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
                        grader_prompt_sha256: str) -> dict[str, Any]:
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
    require(digest_payloads({**payloads, "operator-mapping.json": mapping_payload})
            == manifest.get("aggregate_sha256"),
            "grading-pack aggregate mismatch")
    return manifest


def percentile(values: list[float], probability: float) -> float:
    ordered = sorted(values)
    index = probability * (len(ordered) - 1)
    lower = int(index)
    upper = min(lower + 1, len(ordered) - 1)
    fraction = index - lower
    return ordered[lower] * (1 - fraction) + ordered[upper] * fraction


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


def hierarchical_bootstrap(
    differences: dict[str, float],
    metadata: dict[str, dict[str, str]],
    seed: int,
    replicates: int,
) -> list[float]:
    rng = random.Random(seed)
    paper_sources: dict[str, list[str]] = defaultdict(list)
    textbook: list[str] = []
    for case_id in differences:
        if metadata[case_id]["stratum"] == "paper_derived":
            paper_sources[metadata[case_id]["source_id"]].append(case_id)
        else:
            textbook.append(case_id)
    require(len(paper_sources) == 3 and all(len(values) == 6 for values in paper_sources.values()),
            "expected three six-target paper clusters")
    require(len(textbook) == 12, "expected twelve textbook targets")
    source_names = sorted(paper_sources)
    draws = []
    for _ in range(replicates):
        paper_values = []
        for sampled_source in (rng.choice(source_names) for _ in source_names):
            targets = paper_sources[sampled_source]
            paper_values.extend(differences[rng.choice(targets)] for _ in targets)
        textbook_values = [differences[rng.choice(textbook)] for _ in textbook]
        draws.append((18 * mean(paper_values) + 12 * mean(textbook_values)) / 30)
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


def variant_rates(records: list[dict[str, Any]]) -> dict[str, dict[str, float]]:
    rates: dict[str, dict[str, float]] = {}
    for condition in CONDITIONS:
        condition_records = [record for record in records if record["condition"] == condition]
        drifted = [record for record in condition_records if record["requirement_variant"] == "injected_drift"]
        faithful = [record for record in condition_records if record["requirement_variant"] == "source_faithful"]
        require(len(drifted) == len(faithful) == 75,
                f"condition {condition} must contain 75 records per requirement variant")
        rates[condition] = {
            "injected_drift_primary_pass_rate": mean(record["primary_pass"] for record in drifted),
            "source_faithful_primary_pass_rate": mean(record["primary_pass"] for record in faithful),
            "false_rejection_rate": mean(record["false_rejection"] for record in faithful),
        }
    return rates


def blinding_audit(records: list[dict[str, Any]]) -> dict[str, float]:
    grader_ids = sorted(records[0]["grader_condition_guesses"])
    require(len(grader_ids) == 2, "expected two condition guesses per record")
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
            "source_aware_exact_sign_flip_pvalue": pvalue,
            "permutation_assignments": assignments,
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


def analyze(data: dict[str, Any], seed: int, bootstrap_replicates: int, permutation_replicates: int) -> dict[str, Any]:
    records = data["records"]
    require(len(records) == 450, "analysis requires exactly 450 graded runs")
    require(all(record["condition"] in CONDITIONS for record in records), "unknown condition")
    require(all(isinstance(record["primary_pass"], bool) for record in records),
            "primary_pass must be boolean for every run")
    require(all(isinstance(record["false_rejection"], bool) for record in records),
            "false_rejection must be boolean for every run")
    for record in records:
        require(isinstance(record.get("artifact_replay_success"), bool),
                "artifact_replay_success must be boolean for every run")
        require(isinstance(record.get("execution_metrics"), dict),
                "execution_metrics must be present for every run")
    require(len({record["semantic_run_id"] for record in records}) == 450,
            "semantic run identifiers must be unique")
    run_keys = {
        (record["case_id"], record["condition"], record["replicate"])
        for record in records
    }
    require(len(run_keys) == 450,
            "target-condition-replicate keys must be unique")
    paired_variants: dict[tuple[str, Any], str] = {}
    for record in records:
        require(record["requirement_variant"] in {"source_faithful", "injected_drift"},
                "unknown requirement variant")
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

    scores = target_scores(records)
    differences = {
        case_id: scores[(case_id, "abrl")] - scores[(case_id, "source_aware_blueprint")]
        for case_id in metadata
    }
    point = mean(differences.values())
    bootstrap = hierarchical_bootstrap(
        differences, metadata, seed, bootstrap_replicates
    )
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

    return {
        "schema_version": 1,
        "suite_id": "ABRL-TARGET-DRIFT-V2",
        "run_count": len(records),
        "target_count": len(metadata),
        "primary": {
            "estimand": "target-level mean(abrl minus source_aware_blueprint primary pass rate after within-target replicate aggregation)",
            "point_estimate": point,
            "hierarchical_bootstrap_95_interval": [
                percentile(bootstrap, 0.025), percentile(bootstrap, 0.975)
            ],
            "source_aware_exact_sign_flip_pvalue": pvalue,
            "bootstrap_seed": seed,
            "bootstrap_replicates": bootstrap_replicates,
            "permutation_assignments": exact_assignments,
            "leave_one_paper_out": leave_one_paper_out,
        },
        "requirement_variant_rates": variant_rates(records),
        "primary_source_stratified_condition_means": source_stratified_condition_means(
            scores, metadata
        ),
        "secondary_endpoints_bh_q_0_05": secondary_analyses(records, metadata),
        "grader_condition_guess_accuracy": blinding_audit(records),
        "grading_summary": data.get("grading_summary"),
        "limitation": "Three external source papers do not support paper-population generalization; same-paper probes and within-target replicates are not treated as independent papers or targets."
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--pack", type=Path, required=True)
    parser.add_argument("--grading-pack", type=Path, required=True)
    parser.add_argument("--grades", type=Path, required=True)
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
    grading_pack_manifest = verify_grading_pack(
        args.grading_pack.resolve(), sealed_pack_sha256,
        config["grading"]["grader_prompt_sha256"],
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
    result = analyze(
        grades,
        analysis_config["bootstrap_seed"],
        analysis_config["bootstrap_replicates"],
        analysis_config["permutation_replicates"],
    )
    result["sealed_pack_sha256"] = sealed_pack_sha256
    result["grading_pack_sha256"] = grading_pack_manifest["aggregate_sha256"]
    result["grade_ledger_sha256"] = prepare.sha256_file(args.grades.resolve())
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
        f"interval={result['primary']['hierarchical_bootstrap_95_interval']}"
    )


if __name__ == "__main__":
    main()
