#!/usr/bin/env python3
"""Materialize condition-blind primary-grading packets for target-drift runs."""

from __future__ import annotations

import argparse
import hashlib
import json
import random
import sys
from pathlib import Path
from typing import Any


TOOLS = Path(__file__).resolve().parent
sys.path.insert(0, str(TOOLS))

import prepare_target_drift_execution as prepare  # noqa: E402


FORBIDDEN_PRIMARY_TEXT = (
    "compile-only condition",
    "source-aware blueprint condition",
    "full abrl condition",
    "promotion gate",
    "proof-blueprint",
    "condition=compile_only",
    "condition=source_aware_blueprint",
    "condition=abrl",
    "abrl",
    "target contract",
    "target-contract",
    "proof blueprint",
    "proof-blueprint",
    "source-aware blueprint",
    "evidence-typed",
    "promotion gate",
    "failure ledger",
    "bounded proof transaction",
)


def load(path: Path) -> dict[str, Any]:
    return json.loads(path.read_text(encoding="utf-8"))


def dump(path: Path, value: Any) -> None:
    path.write_text(
        json.dumps(value, indent=2, sort_keys=True, ensure_ascii=False) + "\n",
        encoding="utf-8",
    )


def require(condition: bool, message: str) -> None:
    if not condition:
        raise SystemExit(f"target-drift grading preparation failed: {message}")


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


def agent_manifest(root: Path) -> list[dict[str, Any]]:
    manifest = []
    for path in sorted(item for item in root.rglob("*") if item.is_file()):
        payload = path.read_bytes()
        manifest.append({
            "path": path.relative_to(root).as_posix(),
            "bytes": len(payload),
            "sha256": hashlib.sha256(payload).hexdigest(),
        })
    return manifest


def manifest_sha256(manifest: list[dict[str, Any]]) -> str:
    return hashlib.sha256(prepare.canonical_json_bytes(manifest)).hexdigest()


def flattened_strings(value: Any) -> list[str]:
    if isinstance(value, str):
        return [value]
    if isinstance(value, dict):
        return [text for child in value.values() for text in flattened_strings(child)]
    if isinstance(value, list):
        return [text for child in value for text in flattened_strings(child)]
    return []


def require_blind_text(value: Any, label: str) -> None:
    text = "\n".join(flattened_strings(value)).lower()
    require(not any(token in text for token in FORBIDDEN_PRIMARY_TEXT),
            f"condition-identifying text in primary {label}")


def agent_generated_blind_fields(packet: dict[str, Any]) -> dict[str, Any]:
    """Return only agent-authored fields; public source locators are not provenance leaks."""
    return {
        "agent_final_status": packet["agent_final_status"],
        "public_declarations": packet["public_declarations"],
        "primary_grader_rationale": packet["primary_grader_rationale"],
        "source_amendment": packet["source_amendment"],
        "lean_artifacts": packet["lean_artifacts"],
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--pack", type=Path, required=True)
    parser.add_argument("--runs-root", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--expected-count", type=int, default=450)
    args = parser.parse_args()
    pack = args.pack.resolve()
    runs_root = args.runs_root.resolve()
    output = args.output.resolve()
    require(not output.exists(), "grading output directory already exists")

    prepare.verify_pack(pack)
    config = load(pack / "execution_config.json")
    require(config["suite_id"] == "ABRL-TARGET-DRIFT-V2", "grading requires v2 pack")
    require(config["execution_status"] == "frozen_ready", "grading requires frozen_ready pack")
    current = Path(__file__).resolve()
    expected_hash = config["grading"]["packet_materializer_sha256"]
    require(hashlib.sha256(current.read_bytes()).hexdigest() == expected_hash,
            "invoked grading materializer differs from frozen hash")
    require(hashlib.sha256((pack / "execution_code" / current.name).read_bytes()).hexdigest()
            == expected_hash,
            "sealed grading materializer differs from frozen hash")
    prepare_path = Path(prepare.__file__).resolve()
    prepare_hash = config["sealed_agent_view"]["materializer_sha256"]
    require(hashlib.sha256(prepare_path.read_bytes()).hexdigest() == prepare_hash,
            "imported pack verifier differs from frozen hash")
    require(hashlib.sha256((pack / "execution_code" / prepare_path.name).read_bytes()).hexdigest()
            == prepare_hash, "sealed pack verifier differs from frozen hash")
    grading_seed = config["grading"]["packet_order_seed"]
    require(isinstance(grading_seed, int), "frozen packet_order_seed must be an integer")
    run_manifest = load(pack / "run_manifest.json")
    challenges = load(pack / "operator_challenges.json")["cases"]
    challenge_by_id = {case["id"]: case for case in challenges}
    sealed_by_id = {run["run_id"]: run for run in run_manifest["runs"]}

    collected = []
    for run_dir in sorted(path for path in runs_root.iterdir() if path.is_dir()):
        job_path = run_dir / "operator" / "job.json"
        checker_path = run_dir / "operator" / "checker" / "checker-result.json"
        result_path = run_dir / "agent" / "output" / "result.json"
        state_path = run_dir / "operator" / "run_state.json"
        receipt_path = run_dir / "operator" / "execution-receipt.json"
        if not all(path.is_file() for path in (
            job_path, checker_path, result_path, state_path, receipt_path
        )):
            continue
        job = load(job_path)
        checker = load(checker_path)
        result = load(result_path)
        state = load(state_path)
        receipt = load(receipt_path)
        require(state["status"] == "checked", f"run is not checked: {run_dir.name}")
        require(state["checker_result_sha256"] == prepare.sha256_file(checker_path),
                f"checker-result hash mismatch for {run_dir.name}")
        require(state["execution_receipt_sha256"] == prepare.sha256_file(receipt_path),
                f"execution-receipt hash mismatch for {run_dir.name}")
        require(checker["sealed_pack_sha256"] == receipt["sealed_pack_sha256"]
                == (pack / "aggregate.sha256").read_text(encoding="ascii").strip(),
                f"run sealed-pack binding mismatch for {run_dir.name}")
        current_manifest_sha256 = manifest_sha256(agent_manifest(run_dir / "agent"))
        require(current_manifest_sha256 == receipt["completed_agent_manifest_sha256"]
                == checker["completed_agent_manifest_sha256"],
                f"agent view changed after neutral checking for {run_dir.name}")
        require(checker["execution_receipt_sha256"] == prepare.sha256_file(receipt_path),
                f"checker names a different execution receipt for {run_dir.name}")
        sealed = sealed_by_id[job["semantic_run_id"]]
        challenge = challenge_by_id[sealed["case_id"]]
        amendment_path = run_dir / "agent" / "output" / "source-amendment.md"
        source_amendment = (
            amendment_path.read_text(encoding="utf-8") if amendment_path.is_file() else None
        )
        rationale = result["primary_grader_rationale"].strip()
        lowered = rationale.lower()
        require(not any(case_id.lower() in lowered for case_id in challenge_by_id),
                f"semantic case identifier in primary rationale for {job['opaque_run_id']}")

        changed_lean = []
        workspace = run_dir / "agent" / "workspace"
        for index, relative in enumerate(
            path for path in checker["changed_files"] if path.endswith(".lean")
        ):
            path = workspace / relative
            if path.is_file():
                changed_lean.append({
                    "artifact_name": f"lean_artifact_{index + 1}.lean",
                    "content": path.read_text(encoding="utf-8", errors="replace"),
                })

        packet = {
                "schema_version": 1,
                "source_locator": challenge["source_locator"],
                "frozen_contract": challenge["faithful_contract"],
                "proposed_requirement": sealed["proposed_requirement"],
                "expected_affected_fields": challenge["expected_affected_fields"],
                "agent_final_status": result["final_status"],
                "public_declarations": result["public_declarations"],
                "primary_grader_rationale": rationale,
                "source_amendment": source_amendment,
                "lean_artifacts": changed_lean,
                "execution_metrics": checker["execution_usage"],
                "neutral_checker": {
                    "checker_pass": checker["checker_pass"],
                    "forbidden_lean_hits": checker["forbidden_lean_hits"],
                    "unexpected_axioms": checker["unexpected_axioms"],
                    "artifact_replay_success": checker["artifact_replay_success"],
                    "workflow_compliance_pass": checker["workflow_compliance_pass"],
                    "neutral_build": checker["neutral_build"],
                    "neutral_canary": checker["neutral_canary"],
                    "claim_consistent_with_checker": checker["claim_consistent_with_checker"],
                },
                "grader_response_schema": {
                    "primary_pass": "boolean",
                    "faithful_formal_completion": "boolean",
                    "drift_detected": "boolean",
                    "false_rejection": "boolean",
                    "unsupported_evidence_claim": "boolean",
                    "source_amendment_required": "boolean",
                    "source_critical_fields": "sorted list of affected source-field names",
                    "rationale": "source-field and artifact-line grounded string",
                    "condition_guess": ["compile_only", "source_aware_blueprint", "abrl"],
                    "condition_guess_confidence": "number in [0,1]"
                }
            }
        require_blind_text(
            agent_generated_blind_fields(packet),
            f"agent-generated packet fields for {job['opaque_run_id']}",
        )
        collected.append({
            "semantic_run_id": job["semantic_run_id"],
            "condition": sealed["condition"],
            "requirement_variant": sealed["requirement_variant"],
            "packet": packet,
        })

    require(len(collected) == args.expected_count,
            f"expected {args.expected_count} completed checked runs, found {len(collected)}")
    require(len({item["semantic_run_id"] for item in collected}) == len(collected),
            "completed checked run identifiers are duplicated")
    collected.sort(key=lambda item: item["semantic_run_id"])
    rng = random.Random(grading_seed)
    rng.shuffle(collected)
    output.mkdir(parents=True)
    packets_dir = output / "packets"
    packets_dir.mkdir()
    mapping = []
    payloads: dict[str, bytes] = {}
    for order, item in enumerate(collected):
        grade_id = f"GRADE-{hashlib.sha256(f'{grading_seed}:{order}'.encode()).hexdigest()[:20]}"
        packet = {"grade_id": grade_id, **item["packet"]}
        payload = (json.dumps(packet, indent=2, sort_keys=True, ensure_ascii=False) + "\n").encode("utf-8")
        name = f"packets/{grade_id}.json"
        (output / name).write_bytes(payload)
        payloads[name] = payload
        mapping.append({
            "grade_id": grade_id,
            "semantic_run_id": item["semantic_run_id"],
            "condition": item["condition"],
            "requirement_variant": item["requirement_variant"],
        })

    mapping_payload = (
        json.dumps({
            "schema_version": 1,
            "visibility": "operator only; never provide to a primary grader",
            "mapping": mapping,
        }, indent=2, sort_keys=True, ensure_ascii=False) + "\n"
    ).encode("utf-8")
    packet_aggregate = digest_payloads(payloads)
    combined_payloads = {**payloads, "operator-mapping.json": mapping_payload}
    manifest = {
        "schema_version": 1,
        "suite_id": config["suite_id"],
        "packet_count": len(collected),
        "grading_seed": grading_seed,
        "sealed_pack_sha256": (pack / "aggregate.sha256").read_text(encoding="ascii").strip(),
        "grader_prompt_sha256": config["grading"]["grader_prompt_sha256"],
        "primary_packets_exclude_condition_and_variant_labels": True,
        "packet_aggregate_sha256": packet_aggregate,
        "operator_mapping_sha256": hashlib.sha256(mapping_payload).hexdigest(),
        "aggregate_sha256": digest_payloads(combined_payloads),
        "packet_sha256": {
            name: hashlib.sha256(payload).hexdigest() for name, payload in sorted(payloads.items())
        },
    }
    dump(output / "packet-manifest.json", manifest)
    (output / "operator-mapping.json").write_bytes(mapping_payload)
    print(
        f"materialized {len(collected)} blind grading packets, sha256={manifest['aggregate_sha256']}"
    )


if __name__ == "__main__":
    main()
