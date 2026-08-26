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
import run_target_drift_execution as runner  # noqa: E402
import build_target_drift_completion_ledger as completion  # noqa: E402


FORBIDDEN_PRIMARY_TEXT = prepare.PRIMARY_GRADING_PROVENANCE_MARKERS

# Resource-use metadata, semantic run identifiers, and direct condition fields
# can make a nominally blind packet condition-predictive.  Keep them in the
# operator-only mapping for later analysis, never in material sent to a primary
# grader.
FORBIDDEN_PRIMARY_METADATA_KEYS = frozenset({
    "condition",
    "condition_label",
    "execution_purpose",
    "execution_metrics",
    "execution_usage",
    "input_tokens",
    "cached_input_tokens",
    "cache_write_input_tokens",
    "output_tokens",
    "reasoning_output_tokens",
    "tool_calls",
    "recovery_tool_calls",
    "build_attempts",
    "infrastructure_retries",
    "wall_seconds",
    "orchestrator_wall_seconds",
    "adapter_process_wall_seconds",
    "model_cost_usd",
    "cost_usd",
    "duration_seconds",
    "elapsed_seconds",
    "opaque_run_id",
    "presentation_order",
    "prompt_path",
    "prompt_template_path",
    "requirement_variant",
    "run_id",
    "semantic_run_id",
    "workflow_condition",
    "workflow_compliance_pass",
})


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
        relative = path.relative_to(root)
        if ".lake" in relative.parts:
            continue
        payload = path.read_bytes()
        manifest.append({
            "path": relative.as_posix(),
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


def strip_primary_metadata(value: Any) -> Any:
    """Remove condition-predictive resource metadata from grader-visible evidence."""
    if isinstance(value, dict):
        return {
            key: strip_primary_metadata(child)
            for key, child in value.items()
            if key not in FORBIDDEN_PRIMARY_METADATA_KEYS
        }
    if isinstance(value, list):
        return [strip_primary_metadata(child) for child in value]
    return value


def require_primary_metadata_blind(value: Any, label: str) -> None:
    """Fail closed if a forbidden label, run ID, or resource key reaches a packet."""
    if isinstance(value, dict):
        leaked = sorted(set(value) & FORBIDDEN_PRIMARY_METADATA_KEYS)
        require(not leaked, f"condition-predictive metadata in {label}: {leaked}")
        for child in value.values():
            require_primary_metadata_blind(child, label)
    elif isinstance(value, list):
        for child in value:
            require_primary_metadata_blind(child, label)


def agent_generated_blind_fields(packet: dict[str, Any]) -> dict[str, Any]:
    """Return only agent-authored fields; public source locators are not provenance leaks."""
    return {
        "agent_final_status": packet["agent_final_status"],
        "public_declarations": packet["public_declarations"],
        "primary_grader_rationale": packet["primary_grader_rationale"],
        "source_amendment": packet["source_amendment"],
    }


def require_blind_lean_artifacts(artifacts: list[dict[str, str]], label: str) -> None:
    """Reject only explicit condition labels in Lean; ordinary ABRL source text is common."""
    text = "\n".join(item["content"] for item in artifacts).lower()
    require(not any(token in text for token in prepare.LEAN_PROVENANCE_MARKERS),
            f"condition-identifying text in primary {label}")


def require_production_checker(config: dict[str, Any], probe: dict[str, Any]) -> str:
    checker = config["posthoc_checker"]
    require(checker["mode"] == "production",
            "formal grading rejects excluded checker fixtures")
    runtime_sha256 = prepare.checker_runtime_config_sha256(config)
    require(checker["runtime_config_sha256"] == runtime_sha256,
            "grading checker runtime digest differs from frozen config")
    require(probe.get("status") == "passed"
            and probe.get("checker_runtime_config_sha256") == runtime_sha256
            and probe.get("probe_runner_sha256")
            == checker["isolation_probe_runner_sha256"],
            "formal grading requires the runtime-bound passed isolation probe")
    return runtime_sha256


def require_primary_job(job: dict[str, Any], label: str) -> None:
    require(job.get("execution_purpose") == runner.PRIMARY_EXECUTION_PURPOSE
            and job.get("primary_result_eligible") is True,
            f"grading rejects non-primary or smoke run: {label}")


def require_real_provider_completion(
    config: dict[str, Any], receipt: dict[str, Any],
    adapter_response: dict[str, Any], adapter_response_path: Path, label: str,
) -> None:
    """Re-derive real-provider eligibility at the final grading boundary."""
    require(config["execution_adapter"]["provider_runtime"]["kind"] == "codex_cli",
            "formal grading requires a real codex_cli provider runtime")
    require(receipt.get("termination") == adapter_response.get("termination") == "completed",
            f"grading rejects non-completed provider execution: {label}")
    require(receipt.get("adapter_artifact_sha256", {}).get("response.json")
            == prepare.sha256_file(adapter_response_path),
            f"grading adapter response is not bound by execution receipt: {label}")
    invocations = adapter_response.get("model_invocations")
    require(isinstance(invocations, list) and bool(invocations)
            and all(invocation.get("transport") == "codex_cli"
                    and invocation.get("usage_observed") is True
                    for invocation in invocations),
            f"grading lacks a real codex_cli invocation with observed usage: {label}")


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--pack", type=Path, required=True)
    parser.add_argument("--runs-root", type=Path, required=True)
    parser.add_argument("--completion-ledger", type=Path, required=True)
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
    completion.self_verify(pack, config)
    completion_ledger_path = args.completion_ledger.resolve()
    completion_ledger = load(completion_ledger_path)
    completion.validate_ledger_against_runs(
        pack, runs_root, completion_ledger, require_complete=True,
    )
    completion_ledger_bytes = completion_ledger_path.read_bytes()
    completion_ledger_sha256 = hashlib.sha256(completion_ledger_bytes).hexdigest()
    checker_config = config["posthoc_checker"]
    probe = load(pack / "checker_isolation_probe.json")
    runtime_sha256 = require_production_checker(config, probe)
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
    runner_path = Path(runner.__file__).resolve()
    runner_hash = config["sealed_agent_view"]["run_preparer_sha256"]
    require(hashlib.sha256(runner_path.read_bytes()).hexdigest() == runner_hash,
            "imported run helper differs from frozen hash")
    require(hashlib.sha256((pack / "execution_code" / runner_path.name).read_bytes()).hexdigest()
            == runner_hash, "sealed run helper differs from frozen hash")
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
        adapter_response_path = run_dir / "operator" / "adapter" / "response.json"
        checker_receipt_path = (
            run_dir / "operator" / "checker" / "checker-execution-receipt.json"
        )
        checker_response_path = run_dir / "operator" / "checker" / "sandbox-response.json"
        if not all(path.is_file() for path in (
            job_path, checker_path, result_path, state_path, receipt_path,
            adapter_response_path, checker_receipt_path, checker_response_path,
        )):
            continue
        job = load(job_path)
        checker = load(checker_path)
        result = load(result_path)
        state = load(state_path)
        receipt = load(receipt_path)
        adapter_response = load(adapter_response_path)
        checker_receipt = load(checker_receipt_path)
        checker_response = load(checker_response_path)
        require(job.get("semantic_run_id") in sealed_by_id,
                f"run is absent from the sealed manifest: {run_dir.name}")
        sealed = sealed_by_id[job["semantic_run_id"]]
        aggregate = (pack / "aggregate.sha256").read_text(
            encoding="ascii"
        ).strip()
        completion.validate_checked_run_evidence(
            pack, run_dir, sealed, aggregate, config
        )
        require_primary_job(job, run_dir.name)
        require_real_provider_completion(
            config, receipt, adapter_response, adapter_response_path, run_dir.name
        )
        require(state["prepared_job_sha256"] == receipt["prepared_job_sha256"]
                == prepare.sha256_file(job_path),
                f"prepared-job hash mismatch for {run_dir.name}")
        workspace_manifest_path = run_dir / "operator" / "workspace_manifest.json"
        require(state["workspace_manifest_sha256"] == receipt["workspace_manifest_sha256"]
                == prepare.sha256_file(workspace_manifest_path),
                f"workspace-manifest hash mismatch for {run_dir.name}")
        require(state["status"] == "checked", f"run is not checked: {run_dir.name}")
        require(state.get("result_eligible") is True
                and state.get("checker_mode") == "production",
                f"run is not production-result-eligible: {run_dir.name}")
        require(state.get("checker_runtime_config_sha256") == runtime_sha256
                and state.get("isolation_probe_report_sha256")
                == checker_config["isolation_probe_report_sha256"],
                f"run checker runtime/probe binding mismatch: {run_dir.name}")
        require(state["checker_result_sha256"] == prepare.sha256_file(checker_path),
                f"checker-result hash mismatch for {run_dir.name}")
        require(state["checker_execution_receipt_sha256"]
                == prepare.sha256_file(checker_receipt_path),
                f"checker-execution-receipt hash mismatch for {run_dir.name}")
        require(state["sandbox_response_sha256"]
                == prepare.sha256_file(checker_response_path),
                f"checker sandbox-response hash mismatch for {run_dir.name}")
        checker_request_path = (
            run_dir / "operator" / "checker-attempts"
            / state["checker_attempt_id"] / "request.json"
        )
        require(checker_request_path.is_file()
                and state["checker_request_sha256"]
                == checker_receipt["checker_request_sha256"]
                == checker_response["request_sha256"]
                == prepare.sha256_file(checker_request_path),
                f"checker sanitized-request hash mismatch for {run_dir.name}")
        require(checker_receipt["sandbox_response_sha256"]
                == state["sandbox_response_sha256"],
                f"checker response/receipt chain mismatch for {run_dir.name}")
        require(checker_receipt["checker_result_sha256"]
                == state["checker_result_sha256"]
                == checker_response["checker_result_sha256"],
                f"checker result/receipt chain mismatch for {run_dir.name}")
        require(checker_receipt["checker_artifact_aggregate_sha256"]
                == state["checker_artifact_aggregate_sha256"]
                == checker_response["artifact_aggregate_sha256"],
                f"checker artifact aggregate mismatch for {run_dir.name}")
        require(checker_response["container_image_digest"]
                == checker_config["container_image_digest"],
                f"checker image differs from frozen config for {run_dir.name}")
        expected_checker_response = {
            "checker_attempt_label": state["checker_attempt_id"],
            "checker_id": checker_config["checker_id"],
            "checker_version": checker_config["checker_version"],
            "inner_checker_sha256": checker_config["inner_checker_sha256"],
            "checker_contract_sha256": checker_config["contract_sha256"],
            "checker_runtime_config_sha256": runtime_sha256,
            "filesystem_network_process_attestation": checker_config[
                "filesystem_network_process_attestation"
            ],
            "controller_worker_separation_attestation": checker_config[
                "controller_worker_separation_attestation"
            ],
        }
        for key, value in expected_checker_response.items():
            require(checker_response.get(key) == value,
                    f"checker response differs from frozen {key}: {run_dir.name}")
        require(checker_receipt.get("checker_mode") == "production"
                and checker_receipt.get("result_eligible") is True
                and checker_receipt.get("checker_runtime_config_sha256") == runtime_sha256
                and checker_receipt.get("isolation_probe_report_sha256")
                == checker_config["isolation_probe_report_sha256"],
                f"checker receipt is not production eligible: {run_dir.name}")
        require(checker.get("checker_runtime_config_sha256") == runtime_sha256,
                f"checker result names a different runtime: {run_dir.name}")
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
        require(job["opaque_run_id"] == state["opaque_run_id"]
                == receipt["opaque_run_id"] == checker["opaque_run_id"]
                == runner.opaque_id("run", aggregate, job["semantic_run_id"]),
                f"opaque run binding mismatch for {run_dir.name}")
        require(job["condition"] == sealed["condition"]
                and job["replicate"] == sealed["replicate"],
                f"job condition/replicate differs from sealed run for {run_dir.name}")
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
                "neutral_checker": {
                    "checker_pass": checker["checker_pass"],
                    "forbidden_lean_hits": checker["forbidden_lean_hits"],
                    "unexpected_axioms": checker["unexpected_axioms"],
                    "artifact_replay_success": checker["artifact_replay_success"],
                    "neutral_build": strip_primary_metadata(checker["neutral_build"]),
                    "neutral_canary": strip_primary_metadata(checker["neutral_canary"]),
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
        require_blind_lean_artifacts(
            packet["lean_artifacts"], f"Lean artifacts for {job['opaque_run_id']}"
        )
        require_primary_metadata_blind(
            packet, f"primary packet for {job['opaque_run_id']}"
        )
        collected.append({
            "semantic_run_id": job["semantic_run_id"],
            "condition": sealed["condition"],
            "requirement_variant": sealed["requirement_variant"],
            "execution_metrics": checker["execution_usage"],
            "workflow_compliance_pass": checker["workflow_compliance_pass"],
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
            "execution_metrics": item["execution_metrics"],
            "workflow_compliance_pass": item["workflow_compliance_pass"],
        })

    mapping_payload = (
        json.dumps({
            "schema_version": 1,
            "visibility": "operator only; never provide to a primary grader",
            "mapping": mapping,
        }, indent=2, sort_keys=True, ensure_ascii=False) + "\n"
    ).encode("utf-8")
    packet_aggregate = digest_payloads(payloads)
    combined_payloads = {
        **payloads,
        "operator-mapping.json": mapping_payload,
        "completion-ledger.json": completion_ledger_bytes,
    }
    manifest = {
        "schema_version": 1,
        "suite_id": config["suite_id"],
        "packet_count": len(collected),
        "grading_seed": grading_seed,
        "sealed_pack_sha256": (pack / "aggregate.sha256").read_text(encoding="ascii").strip(),
        "completion_ledger_sha256": completion_ledger_sha256,
        "missing_run_policy_id": completion_ledger["missing_run_policy_id"],
        "missing_run_policy_sha256": completion_ledger["missing_run_policy_sha256"],
        "grader_prompt_sha256": config["grading"]["grader_prompt_sha256"],
        "primary_packets_exclude_condition_and_variant_labels": True,
        "primary_packets_exclude_execution_metrics": True,
        "primary_packets_exclude_workflow_compliance": True,
        "result_eligible": True,
        "checker_mode": "production",
        "checker_runtime_config_sha256": runtime_sha256,
        "isolation_probe_report_sha256": checker_config[
            "isolation_probe_report_sha256"
        ],
        "packet_aggregate_sha256": packet_aggregate,
        "operator_mapping_sha256": hashlib.sha256(mapping_payload).hexdigest(),
        "aggregate_sha256": digest_payloads(combined_payloads),
        "packet_sha256": {
            name: hashlib.sha256(payload).hexdigest() for name, payload in sorted(payloads.items())
        },
    }
    dump(output / "packet-manifest.json", manifest)
    (output / "operator-mapping.json").write_bytes(mapping_payload)
    (output / "completion-ledger.json").write_bytes(completion_ledger_bytes)
    print(
        f"materialized {len(collected)} blind grading packets, sha256={manifest['aggregate_sha256']}"
    )


if __name__ == "__main__":
    main()
