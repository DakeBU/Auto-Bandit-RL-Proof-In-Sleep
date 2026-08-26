#!/usr/bin/env python3

from __future__ import annotations

import hashlib
import contextlib
import io
import json
import sys
import tempfile
import unittest
from pathlib import Path
from unittest import mock


TOOLS = Path(__file__).resolve().parent
sys.path.insert(0, str(TOOLS))

import analyze_target_drift_execution as analysis  # noqa: E402
import build_target_drift_completion_ledger as completion  # noqa: E402
import run_target_drift_schedule as schedule  # noqa: E402


ROOT = TOOLS.parent
POLICY_SOURCE = ROOT / "evaluation" / "target-drift-v2" / "missing-run-policy.json"


def dump(path: Path, value: dict) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(value, indent=2, sort_keys=True) + "\n", encoding="utf-8")


class TargetDriftCompletionLedgerTest(unittest.TestCase):
    def synthetic_pack(self, root: Path) -> Path:
        pack = root / "pack"
        pack.mkdir()
        policy_bytes = POLICY_SOURCE.read_bytes()
        (pack / "missing-run-policy.json").write_bytes(policy_bytes)
        policy_sha256 = hashlib.sha256(policy_bytes).hexdigest()
        adapter_contract_source = (
            ROOT / "evaluation" / "target-drift-v2" / "adapter-contract.json"
        )
        checker_contract_source = (
            ROOT / "evaluation" / "target-drift-v2" / "checker-sandbox-contract.json"
        )
        (pack / "adapter_contract.json").write_bytes(adapter_contract_source.read_bytes())
        (pack / "checker_sandbox_contract.json").write_bytes(
            checker_contract_source.read_bytes()
        )
        execution_code = pack / "execution_code"
        execution_code.mkdir()
        for relative in (
            "tools/prepare_target_drift_execution.py",
            "tools/run_target_drift_execution.py",
            "tools/check_target_drift_run.py",
            "tools/check_target_drift_inner.py",
        ):
            source = ROOT / relative
            (execution_code / source.name).write_bytes(source.read_bytes())
        checker_paths = {
            "driver_path": "tools/check_target_drift_run.py",
            "inner_checker_path": "tools/check_target_drift_inner.py",
            "isolation_probe_runner_path": (
                "tools/record_target_drift_checker_isolation_probe.py"
            ),
            "host_launcher_path": "tools/launch_target_drift_checker_container.py",
            "checker_image_recipe": (
                "evaluation/target-drift-v2/checker-image.Containerfile"
            ),
            "checker_image_sbom": (
                "evaluation/target-drift-v2/checker-image-candidate-32419343467.json"
            ),
            "checker_image_build_input_manifest": (
                "evaluation/target-drift-v2/checker-image-candidate-32419343467.json"
            ),
            "checker_cache_manifest_artifact": (
                "evaluation/target-drift-v2/checker-image-candidate-32419343467.json"
            ),
            "checker_image_build_log": (
                "evaluation/target-drift-v2/checker-image-candidate-32419343467.json"
            ),
            "controller_entrypoint_source": (
                "tools/check_target_drift_container_controller.py"
            ),
        }
        path_hash = lambda relative: completion.prepare.sha256_file(ROOT / relative)
        zero_sha256 = "0" * 64
        checker_config = {
            "contract": "evaluation/target-drift-v2/checker-sandbox-contract.json",
            "contract_sha256": path_hash(
                "evaluation/target-drift-v2/checker-sandbox-contract.json"
            ),
            **checker_paths,
            "driver_sha256": path_hash(checker_paths["driver_path"]),
            "inner_checker_sha256": path_hash(checker_paths["inner_checker_path"]),
            "isolation_probe_runner_sha256": path_hash(
                checker_paths["isolation_probe_runner_path"]
            ),
            "host_launcher_sha256": path_hash(checker_paths["host_launcher_path"]),
            "host_python_executable": "C:/synthetic/python.exe",
            "host_python_executable_sha256": "1" * 64,
            "container_runtime_kind": "docker",
            "container_runtime_executable": "C:/synthetic/docker.exe",
            "container_runtime_executable_sha256": "2" * 64,
            "runtime_version_output_sha256": "3" * 64,
            "runtime_signature_output_sha256": "4" * 64,
            "daemon_identity_output_sha256": "5" * 64,
            "checker_image_recipe_sha256": path_hash(
                checker_paths["checker_image_recipe"]
            ),
            "checker_image_sbom_sha256": path_hash(checker_paths["checker_image_sbom"]),
            "checker_image_build_input_manifest_sha256": path_hash(
                checker_paths["checker_image_build_input_manifest"]
            ),
            "checker_cache_manifest_sha256": path_hash(
                checker_paths["checker_cache_manifest_artifact"]
            ),
            "checker_image_build_log_sha256": path_hash(
                checker_paths["checker_image_build_log"]
            ),
            "controller_entrypoint_source_sha256": path_hash(
                checker_paths["controller_entrypoint_source"]
            ),
            "controller_entrypoint_sha256": "6" * 64,
            "controller_entrypoint": "/usr/local/bin/abrl-checker-controller",
            "controller_uid": "0:0",
            "worker_uid": "10002:10002",
            "checker_id": "synthetic-production-checker",
            "checker_version": "1",
            "mode": "production",
            "runtime_id": "synthetic-docker",
            "runtime_version": "1",
            "inspect_absent_exit_code": 1,
            "container_image_digest": f"sha256:{'7' * 64}",
            "filesystem_network_process_attestation": "synthetic-isolated",
            "controller_worker_separation_attestation": "synthetic-separated",
            "checker_cache_root": "/opt/abrl-checker-cache/.lake",
            "checker_cache_manifest_path": (
                "/opt/abrl-checker-cache/cache-manifest.json"
            ),
            "budgets": {
                "wall_clock_seconds": 60,
                "memory_mb": 1024,
                "pids_limit": 64,
                "cpus": 1,
                "maximum_output_bytes": 1000000,
                "maximum_response_bytes": 1000000,
            },
            "worker_command_prefix": ["worker"],
            "cache_prelude_argv": [],
            "isolation_probe_report_sha256": zero_sha256,
        }
        launcher = (ROOT / checker_paths["host_launcher_path"]).resolve()
        checker_config.update(
            completion.prepare.checker_launcher.command_templates(
                checker_config, launcher
            )
        )
        config = {
            "suite_id": "ABRL-TARGET-DRIFT-V2",
            "execution_status": "frozen_ready",
            "workspace_base_commit": "8" * 40,
            "model": {
                "provider": "synthetic",
                "model_id": "synthetic-model",
                "immutable_version": "synthetic-model-v1",
            },
            "pricing": {
                "currency": "USD",
                "unit": "per_million_tokens",
                "input_tokens": 0,
                "cached_input_tokens": 0,
                "cache_write_input_tokens": 0,
                "output_tokens": 0,
                "source_url": "synthetic",
                "effective_date": "2026-08-26",
                "output_includes_reasoning_tokens": True,
            },
            "budgets_per_run": {
                "maximum_input_tokens": 1000,
                "maximum_output_tokens": 1000,
                "maximum_tool_calls": 10,
                "maximum_build_attempts": 10,
                "wall_clock_seconds": 60,
                "maximum_model_retries": 0,
                "maximum_cost_usd": 1,
            },
            "execution_adapter": {
                "contract_sha256": path_hash(
                    "evaluation/target-drift-v2/adapter-contract.json"
                ),
                "adapter_id": "synthetic-codex-adapter",
                "adapter_version": "1",
                "container_or_sandbox_image_digest": f"sha256:{'9' * 64}",
                "budget_enforcement_attestation": "synthetic-budgeted",
                "filesystem_network_process_attestation": "synthetic-isolated",
                "provider_runtime": {
                    "kind": "codex_cli",
                    "executable": "C:/synthetic/codex.exe",
                    "executable_sha256": "a" * 64,
                    "version": "synthetic",
                    "version_output_sha256": "b" * 64,
                    "auth_source_path": "C:/synthetic/auth",
                    "fresh_codex_home_attestation": "synthetic-fresh-home",
                    "process_environment": {},
                    "shell_environment": {},
                },
            },
            "posthoc_checker": checker_config,
            "retry_policy": {
                "semantic_failure_retries": 0,
                "infrastructure_failure_definition": "synthetic",
                "infrastructure_retry_limit": 0,
                "missing_run_policy": completion.POLICY_ID,
            },
            "missing_run_policy": {
                "policy_id": completion.POLICY_ID,
                "policy_sha256": policy_sha256,
            },
            "sealed_agent_view": {
                "materializer": "tools/prepare_target_drift_execution.py",
                "materializer_sha256": path_hash(
                    "tools/prepare_target_drift_execution.py"
                ),
                "run_preparer": "tools/run_target_drift_execution.py",
                "run_preparer_sha256": path_hash(
                    "tools/run_target_drift_execution.py"
                ),
            },
        }
        runtime_sha256 = completion.prepare.checker_runtime_config_sha256(config)
        checker_config["runtime_config_sha256"] = runtime_sha256
        probe_artifact_root = pack / "checker_isolation_probe_artifacts"
        probe_artifact_root.mkdir()
        probe_nonce = "c" * 48
        derived_probes = {
            "network_denied": True,
            "host_sentinel_protected": True,
            "operator_ground_truth_absent": True,
            "checker_outputs_not_worker_writable": True,
            "patched_source_and_controller_input_read_only": True,
            "mounted_inputs_and_cidfile_protected": True,
            "background_process_reaped": True,
        }
        dump(probe_artifact_root / "host-observations.json", {
            "probe_nonce": probe_nonce,
            "checker_attempt_label": f"ABRL-PROBE-{probe_nonce}",
            "checker_runtime_config_sha256": runtime_sha256,
            "container_image_digest": checker_config["container_image_digest"],
            "derived_probes": derived_probes,
        })
        probe_payloads = completion.prepare.probe_artifact_bytes(probe_artifact_root)
        probe = {
            "schema_version": 1,
            "suite_id": config["suite_id"],
            "status": "passed",
            "checker_id": checker_config["checker_id"],
            "checker_version": checker_config["checker_version"],
            "container_image_digest": checker_config["container_image_digest"],
            "controller_entrypoint_sha256": checker_config[
                "controller_entrypoint_sha256"
            ],
            "checker_runtime_config_sha256": runtime_sha256,
            "runtime_command_template_sha256": completion.prepare.sha256_bytes(
                completion.prepare.canonical_json_bytes(
                    checker_config["sandbox_command_argv"]
                )
            ),
            "probe_runner_sha256": checker_config["isolation_probe_runner_sha256"],
            "probe_nonce": probe_nonce,
            "checker_attempt_label": f"ABRL-PROBE-{probe_nonce}",
            "probes": derived_probes,
            "artifact_manifest": completion.prepare.probe_artifact_manifest(
                probe_payloads
            ),
        }
        probe_path = pack / "checker_isolation_probe.json"
        dump(probe_path, probe)
        checker_config["isolation_probe_report_sha256"] = (
            completion.prepare.sha256_file(probe_path)
        )
        dump(pack / "execution_config.json", config)
        (pack / "aggregate.sha256").write_text("a" * 64 + "\n", encoding="ascii")
        runs = []
        order = 0
        for case_index in range(30):
            for replicate in range(5):
                variant = "source_faithful" if (case_index + replicate) % 2 == 0 else "injected_drift"
                for condition in ("compile_only", "source_aware_blueprint", "abrl"):
                    runs.append({
                        "run_id": f"case-{case_index}--{condition}--replicate-{replicate}",
                        "case_id": f"case-{case_index}",
                        "condition": condition,
                        "replicate": replicate,
                        "requirement_variant": variant,
                        "presentation_order": order,
                    })
                    order += 1
        dump(pack / "run_manifest.json", {"runs": runs})
        return pack

    def materialize_checked_runs(
        self, pack: Path, runs_root: Path, limit: int | None = None,
    ) -> None:
        aggregate = (pack / "aggregate.sha256").read_text(encoding="ascii").strip()
        config = json.loads(
            (pack / "execution_config.json").read_text(encoding="utf-8")
        )
        planned_runs = json.loads(
            (pack / "run_manifest.json").read_text(encoding="utf-8")
        )["runs"]
        if limit is not None:
            planned_runs = planned_runs[:limit]
        for planned in planned_runs:
            opaque = completion.runner.opaque_id("run", aggregate, planned["run_id"])
            operator = runs_root / opaque / "operator"
            agent = runs_root / opaque / "agent"
            workspace = agent / "workspace"
            source = agent / "source"
            workspace.mkdir(parents=True)
            source.mkdir()
            (agent / "prompt.md").write_text("Synthetic prompt.\n", encoding="utf-8")
            (source / "source.pdf").write_bytes(b"synthetic source packet")
            (workspace / "Synthetic.lean").write_text(
                "theorem synthetic : True := by trivial\n", encoding="utf-8"
            )
            prepared_agent_manifest = completion.runner.file_manifest(agent)
            baseline_manifest = completion.runner.file_manifest(workspace)
            job_path = operator / "job.json"
            workspace_manifest_path = operator / "workspace_manifest.json"
            dump(workspace_manifest_path, {
                "schema_version": 1,
                "opaque_run_id": opaque,
                "workspace_base_commit": config["workspace_base_commit"],
                "condition_view": planned["condition"],
                "selected_repository_paths": ["Synthetic.lean"],
                "files": baseline_manifest,
            })
            result_contract = {
                "agent_output_directory": str((agent / "output").resolve()),
                "required_files": [
                    "result.json", "lean-diff.patch", "build.log",
                    "explanation.md", "workflow-compliance.json",
                ],
                "optional_files": ["source-amendment.md"],
                "workflow_id": planned["condition"],
                "workflow_evidence_files": completion.runner.WORKFLOW_EVIDENCE[
                    planned["condition"]
                ],
                "result_required_fields": [
                    "schema_version", "opaque_run_id", "final_status",
                    "public_declarations", "primary_grader_rationale",
                ],
                "blind_grading_text_rule": completion.runner.BLIND_GRADING_TEXT_RULE,
            }
            job = {
                "schema_version": 1,
                "suite_id": config["suite_id"],
                "semantic_run_id": planned["run_id"],
                "opaque_run_id": opaque,
                "source_primary_run_id": planned["run_id"],
                "execution_purpose": completion.runner.PRIMARY_EXECUTION_PURPOSE,
                "primary_result_eligible": True,
                "smoke_plan_sha256": None,
                "condition": planned["condition"],
                "replicate": planned["replicate"],
                "agent_mount": str(agent.resolve()),
                "prompt_path": str((agent / "prompt.md").resolve()),
                "prompt_sha256": completion.prepare.sha256_file(agent / "prompt.md"),
                "source_sha256": completion.prepare.sha256_file(
                    source / "source.pdf"
                ),
                "workspace_base_commit": config["workspace_base_commit"],
                "model": config["model"],
                "pricing": config["pricing"],
                "budgets": config["budgets_per_run"],
                "retry_policy": config["retry_policy"],
                "adapter_contract_sha256": config["execution_adapter"][
                    "contract_sha256"
                ],
                "provider_runtime": config["execution_adapter"]["provider_runtime"],
                "required_adapter_attestations": [
                    "fresh model context and process",
                    (
                        "only agent_mount plus pinned read-only toolchain/dependency "
                        "cache visible"
                    ),
                    "general network disabled inside evaluated tools",
                    "token/tool/build/time/cost budgets enforced",
                    (
                        "complete request/response/tool/process accounting retained "
                        "under operator output"
                    ),
                ],
                "result_contract": result_contract,
                "status": "prepared_unrun",
            }
            dump(job_path, job)

            output = agent / "output"
            output.mkdir()
            dump(output / "result.json", {
                "schema_version": 1,
                "opaque_run_id": opaque,
                "final_status": "partial",
                "public_declarations": [],
                "primary_grader_rationale": "Synthetic incomplete proof route.",
            })
            (output / "lean-diff.patch").write_bytes(b"")
            (output / "build.log").write_text("synthetic build\n", encoding="utf-8")
            (output / "explanation.md").write_text(
                "Synthetic explanation.\n", encoding="utf-8"
            )
            evidence = []
            for name in result_contract["workflow_evidence_files"]:
                path = output / name
                path.write_text(f"synthetic {name}\n", encoding="utf-8")
                evidence.append({
                    "path": name,
                    "sha256": completion.prepare.sha256_file(path),
                })
            dump(output / "workflow-compliance.json", {
                "schema_version": 1,
                "opaque_run_id": opaque,
                "workflow_id": planned["condition"],
                "evidence_files": evidence,
            })
            completed_agent_manifest = completion.runner.file_manifest(agent)
            completed_agent_manifest_sha256 = completion.runner.manifest_sha256(
                completed_agent_manifest
            )

            adapter_dir = operator / "adapter"
            adapter_dir.mkdir(parents=True)
            dump(adapter_dir / "request.json", completion.runner.adapter_request(job, agent))
            usage = {
                "input_tokens": 0,
                "cached_input_tokens": 0,
                "cache_write_input_tokens": 0,
                "output_tokens": 0,
                "reasoning_output_tokens": 0,
                "tool_calls": 0,
                "build_attempts": 0,
                "recovery_tool_calls": 0,
                "infrastructure_retries": 0,
                "wall_seconds": 0.1,
                "cost_usd": 0,
            }
            adapter_response_path = operator / "adapter" / "response.json"
            dump(adapter_response_path, {
                "schema_version": 1,
                "opaque_run_id": opaque,
                "adapter_id": config["execution_adapter"]["adapter_id"],
                "adapter_version": config["execution_adapter"]["adapter_version"],
                "model_id": config["model"]["model_id"],
                "immutable_model_version": config["model"]["immutable_version"],
                "replicate": planned["replicate"],
                "container_or_sandbox_image_digest": config["execution_adapter"][
                    "container_or_sandbox_image_digest"
                ],
                "budget_enforcement_attestation": config["execution_adapter"][
                    "budget_enforcement_attestation"
                ],
                "filesystem_network_process_attestation": config[
                    "execution_adapter"
                ]["filesystem_network_process_attestation"],
                "termination": "completed",
                "model_invocations": [{
                    "attempt": 1,
                    "transport": "codex_cli",
                    "observable_id_kind": "codex_thread",
                    "observable_id": f"thread-{opaque}",
                    "process_exit_code": 0,
                    "wall_seconds": 0.1,
                    "usage_observed": True,
                }],
                "usage": usage,
            })
            (adapter_dir / "trace.jsonl").write_text(json.dumps({
                "sequence": 0,
                "kind": "usage_summary",
                "usage": usage,
            }) + "\n", encoding="utf-8")
            (adapter_dir / "process.stdout.log").write_text("", encoding="utf-8")
            (adapter_dir / "process.stderr.log").write_text("", encoding="utf-8")
            (adapter_dir / "provider-attempt-001.stdout.jsonl").write_text(
                "{}\n", encoding="utf-8"
            )
            (adapter_dir / "provider-attempt-001.stderr.log").write_text(
                "", encoding="utf-8"
            )
            (adapter_dir / "provider-events.jsonl").write_text(
                "{}\n", encoding="utf-8"
            )
            adapter_hashes = {
                entry["path"]: entry["sha256"]
                for entry in completion.runner.file_manifest(adapter_dir)
            }
            execution_receipt_path = operator / "execution-receipt.json"
            dump(execution_receipt_path, {
                "schema_version": 1,
                "opaque_run_id": opaque,
                "execution_purpose": completion.runner.PRIMARY_EXECUTION_PURPOSE,
                "primary_result_eligible": True,
                "smoke_plan_sha256": None,
                "sealed_pack_sha256": aggregate,
                "prepared_agent_manifest_sha256": completion.runner.manifest_sha256(
                    prepared_agent_manifest
                ),
                "prepared_job_sha256": completion.prepare.sha256_file(job_path),
                "workspace_manifest_sha256": completion.prepare.sha256_file(
                    workspace_manifest_path
                ),
                "completed_agent_manifest_sha256": completed_agent_manifest_sha256,
                "completed_agent_manifest": completed_agent_manifest,
                "protected_input_hashes": {
                    "prompt.md": completion.prepare.sha256_file(agent / "prompt.md"),
                    "source/source.pdf": completion.prepare.sha256_file(
                        source / "source.pdf"
                    ),
                },
                "adapter_artifact_sha256": adapter_hashes,
                "adapter_process_exit_code": 0,
                "adapter_process_wall_seconds": 0.1,
                "usage": {**usage, "orchestrator_wall_seconds": 0.1},
                "termination": "completed",
                "status": "executed_unchecked",
            })
            execution_receipt_sha256 = completion.prepare.sha256_file(
                execution_receipt_path
            )
            checker_config = config["posthoc_checker"]
            checker_attempt_id = completion.checker.checker_attempt_id(
                aggregate, opaque, execution_receipt_sha256,
                checker_config["driver_sha256"],
                checker_config["inner_checker_sha256"],
                checker_config["runtime_config_sha256"], 1,
            )
            checker_request_path = (
                operator / "checker-attempts" / checker_attempt_id / "request.json"
            )
            checker_request = {
                "schema_version": 1,
                "suite_id": config["suite_id"],
                "opaque_run_id": opaque,
                "checker_attempt_id": checker_attempt_id,
                "checker_attempt_label": checker_attempt_id,
                "sealed_pack_sha256": aggregate,
                "execution_receipt_sha256": execution_receipt_sha256,
                "completed_agent_manifest_sha256": completed_agent_manifest_sha256,
                "baseline_manifest": baseline_manifest,
                "baseline_manifest_sha256": completion.runner.manifest_sha256(
                    baseline_manifest
                ),
                "expected_completed_workspace_manifest": baseline_manifest,
                "expected_completed_workspace_manifest_sha256": (
                    completion.runner.manifest_sha256(baseline_manifest)
                ),
                "patch_sha256": completion.prepare.sha256_file(
                    output / "lean-diff.patch"
                ),
                "result_sha256": completion.prepare.sha256_file(
                    output / "result.json"
                ),
                "public_declarations": [],
                "final_status": "partial",
                "allowed_axioms": sorted(completion.checker.inner.ALLOWED_AXIOMS),
                "checker_id": checker_config["checker_id"],
                "checker_version": checker_config["checker_version"],
                "inner_checker_sha256": checker_config["inner_checker_sha256"],
                "controller_entrypoint_sha256": checker_config[
                    "controller_entrypoint_sha256"
                ],
                "checker_contract_sha256": checker_config["contract_sha256"],
                "checker_runtime_config_sha256": checker_config[
                    "runtime_config_sha256"
                ],
                "container_image_digest": checker_config["container_image_digest"],
                "filesystem_network_process_attestation": checker_config[
                    "filesystem_network_process_attestation"
                ],
                "controller_worker_separation_attestation": checker_config[
                    "controller_worker_separation_attestation"
                ],
                "checker_cache_manifest_sha256": checker_config[
                    "checker_cache_manifest_sha256"
                ],
                "resource_limits": checker_config["budgets"],
                "worker_command_prefix": checker_config["worker_command_prefix"],
                "cache_prelude_argv": checker_config["cache_prelude_argv"],
                "sandbox_mode": "production",
                "workflow_compliance_pass": True,
                "execution_usage": {**usage, "orchestrator_wall_seconds": 0.1},
            }
            dump(checker_request_path, checker_request)
            checker_result_path = operator / "checker" / "checker-result.json"
            worker_success = {
                "command": ["git", "apply", "--check", "lean-diff.patch"],
                "exit_code": 0,
                "timed_out": False,
                "wall_seconds": 0.1,
            }
            checker_result = {
                "schema_version": 1,
                "opaque_run_id": opaque,
                "checker_attempt_id": checker_attempt_id,
                "checker_pass": True,
                "changed_files": [],
                "deleted_files": [],
                "forbidden_lean_hits": [],
                "replay_forbidden_lean_hits": [],
                "replay_changed_files": [],
                "replay_deleted_files": [],
                "patch_check": worker_success,
                "patch_apply": {
                    **worker_success,
                    "command": ["git", "apply", "lean-diff.patch"],
                },
                "replayed_content_matches_completed_workspace": True,
                "post_worker_content_unchanged": True,
                "public_declarations_absent_from_frozen_base": True,
                "cache_prelude": None,
                "neutral_build": {
                    **worker_success,
                    "command": [*checker_config["worker_command_prefix"], "lake", "build"],
                },
                "neutral_canary": None,
                "public_declarations": [],
                "axiom_dependencies": [],
                "unexpected_axioms": [],
                "artifact_replay_success": True,
                "workflow_compliance_pass": True,
                "execution_usage": checker_request["execution_usage"],
                "sealed_pack_sha256": aggregate,
                "execution_receipt_sha256": execution_receipt_sha256,
                "completed_agent_manifest_sha256": completed_agent_manifest_sha256,
                "agent_claimed_status": "partial",
                "claim_consistent_with_checker": True,
                "inner_checker_sha256": checker_config["inner_checker_sha256"],
                "checker_contract_sha256": checker_config["contract_sha256"],
                "container_image_digest": checker_config["container_image_digest"],
                "checker_runtime_config_sha256": checker_config[
                    "runtime_config_sha256"
                ],
            }
            dump(checker_result_path, checker_result)
            checker_artifact_manifest = completion.runner.file_manifest(
                operator / "checker"
            )
            checker_artifact_aggregate = completion.checker.artifact_aggregate(
                checker_artifact_manifest
            )
            sandbox_response_path = operator / "checker" / "sandbox-response.json"
            dump(sandbox_response_path, {
                "schema_version": 1,
                "opaque_run_id": opaque,
                "checker_attempt_id": checker_attempt_id,
                "checker_attempt_label": checker_attempt_id,
                "request_sha256": completion.prepare.sha256_file(checker_request_path),
                "checker_id": checker_config["checker_id"],
                "checker_version": checker_config["checker_version"],
                "inner_checker_sha256": checker_config["inner_checker_sha256"],
                "controller_entrypoint_sha256": checker_config[
                    "controller_entrypoint_sha256"
                ],
                "checker_contract_sha256": checker_config["contract_sha256"],
                "checker_runtime_config_sha256": checker_config[
                    "runtime_config_sha256"
                ],
                "container_image_digest": checker_config["container_image_digest"],
                "filesystem_network_process_attestation": checker_config[
                    "filesystem_network_process_attestation"
                ],
                "controller_worker_separation_attestation": checker_config[
                    "controller_worker_separation_attestation"
                ],
                "termination": "completed",
                "checker_result_sha256": completion.prepare.sha256_file(
                    checker_result_path
                ),
                "artifact_manifest": checker_artifact_manifest,
                "artifact_aggregate_sha256": checker_artifact_aggregate,
                "process_exit_code": 0,
                "measured_wall_seconds": 0.1,
            })
            checker_receipt_path = (
                operator / "checker" / "checker-execution-receipt.json"
            )
            dump(checker_receipt_path, {
                "schema_version": 1,
                "opaque_run_id": opaque,
                "checker_attempt_id": checker_attempt_id,
                "checker_request_sha256": completion.prepare.sha256_file(
                    checker_request_path
                ),
                "sandbox_response_sha256": completion.prepare.sha256_file(
                    sandbox_response_path
                ),
                "checker_result_sha256": completion.prepare.sha256_file(
                    checker_result_path
                ),
                "checker_artifact_aggregate_sha256": checker_artifact_aggregate,
                "checker_runtime_config_sha256": checker_config[
                    "runtime_config_sha256"
                ],
                "isolation_probe_report_sha256": checker_config[
                    "isolation_probe_report_sha256"
                ],
                "checker_mode": "production",
                "execution_purpose": completion.runner.PRIMARY_EXECUTION_PURPOSE,
                "result_eligible": True,
                "process": {
                    "exit_code": 0,
                    "timed_out": False,
                    "output_limit_exceeded": False,
                    "wall_seconds": 0.1,
                    "cidfile_container_id": "synthetic-container",
                    "lifecycle": {},
                    "lifecycle_verified_absent": True,
                },
            })
            dump(operator / "run_state.json", {
                "schema_version": 1,
                "status": "checked",
                "opaque_run_id": opaque,
                "execution_purpose": completion.runner.PRIMARY_EXECUTION_PURPOSE,
                "primary_result_eligible": True,
                "smoke_plan_sha256": None,
                "sealed_pack_sha256": aggregate,
                "agent_view_file_count": len(prepared_agent_manifest),
                "prepared_agent_manifest_sha256": completion.runner.manifest_sha256(
                    prepared_agent_manifest
                ),
                "result_eligible": True,
                "checker_mode": "production",
                "completed_agent_manifest_sha256": completed_agent_manifest_sha256,
                "prepared_job_sha256": completion.prepare.sha256_file(job_path),
                "workspace_manifest_sha256": completion.prepare.sha256_file(
                    workspace_manifest_path
                ),
                "execution_receipt_sha256": completion.prepare.sha256_file(
                    execution_receipt_path
                ),
                "checker_attempt_id": checker_attempt_id,
                "checker_runtime_config_sha256": checker_config[
                    "runtime_config_sha256"
                ],
                "isolation_probe_report_sha256": checker_config[
                    "isolation_probe_report_sha256"
                ],
                "checker_request_sha256": completion.prepare.sha256_file(
                    checker_request_path
                ),
                "checker_result_sha256": completion.prepare.sha256_file(
                    checker_result_path
                ),
                "checker_execution_receipt_sha256": completion.prepare.sha256_file(
                    checker_receipt_path
                ),
                "sandbox_response_sha256": completion.prepare.sha256_file(
                    sandbox_response_path
                ),
                "checker_artifact_aggregate_sha256": checker_artifact_aggregate,
            })

    def test_empty_run_root_emits_missingness_only_and_refuses_inference(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            pack = self.synthetic_pack(root)
            runs = root / "runs"
            runs.mkdir()
            ledger = completion.build_ledger(pack, runs)
            counts = completion.validate_ledger_against_runs(
                pack, runs, ledger, require_complete=False,
            )
            self.assertEqual(counts["missing_count"], 450)
            self.assertEqual(counts["missing_reason_counts"], {"run_not_materialized": 450})
            self.assertFalse(ledger["primary_analysis_permitted"])
            report = analysis.incomplete_analysis(ledger)
            self.assertEqual(report["analysis_status"],
                             "not_estimable_incomplete_preregistered_run_universe")
            self.assertEqual(report["primary"]["status"], "not_reported")
            self.assertNotIn("point_estimate", json.dumps(report))
            self.assertNotIn("pvalue", json.dumps(report))
            with self.assertRaises(SystemExit):
                completion.validate_ledger(pack, ledger, require_complete=True)

    def test_complete_ledger_is_exactly_450_and_has_no_missing_outcome_slots(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            pack = self.synthetic_pack(root)
            runs = root / "runs"
            runs.mkdir()
            self.materialize_checked_runs(pack, runs)
            ledger = completion.build_ledger(pack, runs)
            counts = completion.validate_ledger_against_runs(
                pack, runs, ledger, require_complete=True,
            )
            self.assertEqual(counts["result_eligible_count"], 450)
            self.assertEqual(counts["missing_count"], 0)

            ledger["records"][0]["state_status"] = "integrity_failure"
            ledger["records"][0]["result_eligible"] = False
            ledger["records"][0]["missing_reason"] = "run_evidence_unreadable_or_invalid"
            ledger["summary"] = completion.summary(ledger["records"])
            ledger["completion_status"] = "incomplete_primary_analysis_forbidden"
            ledger["primary_analysis_permitted"] = False
            with self.assertRaises(SystemExit):
                completion.validate_ledger_against_runs(
                    pack, runs, ledger, require_complete=False,
                )

    def test_checked_state_without_observed_real_invocation_is_missing(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            pack = self.synthetic_pack(root)
            runs = root / "runs"
            runs.mkdir()
            self.materialize_checked_runs(pack, runs, limit=1)
            planned = json.loads(
                (pack / "run_manifest.json").read_text(encoding="utf-8")
            )["runs"][0]
            opaque = completion.runner.opaque_id("run", "a" * 64, planned["run_id"])
            response_path = runs / opaque / "operator" / "adapter" / "response.json"
            response = json.loads(response_path.read_text(encoding="utf-8"))
            response["model_invocations"] = []
            dump(response_path, response)
            receipt_path = runs / opaque / "operator" / "execution-receipt.json"
            receipt = json.loads(receipt_path.read_text(encoding="utf-8"))
            receipt["adapter_artifact_sha256"]["response.json"] = (
                completion.prepare.sha256_file(response_path)
            )
            dump(receipt_path, receipt)
            state_path = runs / opaque / "operator" / "run_state.json"
            state = json.loads(state_path.read_text(encoding="utf-8"))
            state["execution_receipt_sha256"] = completion.prepare.sha256_file(
                receipt_path
            )
            dump(state_path, state)
            ledger = completion.build_ledger(pack, runs)
            record = next(
                item for item in ledger["records"]
                if item["semantic_run_id"] == planned["run_id"]
            )
            self.assertEqual(record["state_status"], "integrity_failure")
            self.assertFalse(record["result_eligible"])
            self.assertEqual(ledger["summary"]["missing_count"], 450)

    def test_checked_state_missing_expected_hash_binding_is_missing(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            pack = self.synthetic_pack(root)
            runs = root / "runs"
            runs.mkdir()
            self.materialize_checked_runs(pack, runs, limit=1)
            planned = json.loads(
                (pack / "run_manifest.json").read_text(encoding="utf-8")
            )["runs"][0]
            opaque = completion.runner.opaque_id("run", "a" * 64, planned["run_id"])
            run_dir = runs / opaque
            state_path = run_dir / "operator" / "run_state.json"
            original_state = json.loads(state_path.read_text(encoding="utf-8"))
            config = json.loads(
                (pack / "execution_config.json").read_text(encoding="utf-8")
            )
            for field in completion.REQUIRED_CHECKED_STATE_HASH_FIELDS:
                with self.subTest(field=field):
                    state = dict(original_state)
                    del state[field]
                    dump(state_path, state)
                    with self.assertRaises(SystemExit):
                        completion.inspect_run(
                            run_dir, planned, "a" * 64, config, pack
                        )

            state = dict(original_state)
            del state["execution_receipt_sha256"]
            dump(state_path, state)

            ledger = completion.build_ledger(pack, runs)
            record = next(
                item for item in ledger["records"]
                if item["semantic_run_id"] == planned["run_id"]
            )
            self.assertEqual(record["state_status"], "integrity_failure")
            self.assertFalse(record["result_eligible"])
            self.assertEqual(record["missing_reason"], "run_evidence_unreadable_or_invalid")
            self.assertEqual(ledger["summary"]["missing_count"], 450)

    def test_empty_checker_result_shell_stays_missing_after_rehashing_chain(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            pack = self.synthetic_pack(root)
            runs = root / "runs"
            runs.mkdir()
            self.materialize_checked_runs(pack, runs, limit=1)
            planned = json.loads(
                (pack / "run_manifest.json").read_text(encoding="utf-8")
            )["runs"][0]
            opaque = completion.runner.opaque_id("run", "a" * 64, planned["run_id"])
            operator = runs / opaque / "operator"
            checker_dir = operator / "checker"
            checker_result_path = checker_dir / "checker-result.json"
            dump(checker_result_path, {})
            checker_result_sha256 = completion.prepare.sha256_file(checker_result_path)

            sandbox_response_path = checker_dir / "sandbox-response.json"
            sandbox_response = json.loads(
                sandbox_response_path.read_text(encoding="utf-8")
            )
            artifact_manifest = completion.runner.file_manifest(checker_dir)
            artifact_manifest = [
                entry for entry in artifact_manifest
                if entry["path"] not in {
                    "sandbox-response.json", "checker-execution-receipt.json"
                }
            ]
            artifact_aggregate = completion.checker.artifact_aggregate(
                artifact_manifest
            )
            sandbox_response["checker_result_sha256"] = checker_result_sha256
            sandbox_response["artifact_manifest"] = artifact_manifest
            sandbox_response["artifact_aggregate_sha256"] = artifact_aggregate
            dump(sandbox_response_path, sandbox_response)

            checker_receipt_path = checker_dir / "checker-execution-receipt.json"
            checker_receipt = json.loads(
                checker_receipt_path.read_text(encoding="utf-8")
            )
            checker_receipt["sandbox_response_sha256"] = (
                completion.prepare.sha256_file(sandbox_response_path)
            )
            checker_receipt["checker_result_sha256"] = checker_result_sha256
            checker_receipt["checker_artifact_aggregate_sha256"] = artifact_aggregate
            dump(checker_receipt_path, checker_receipt)

            state_path = operator / "run_state.json"
            state = json.loads(state_path.read_text(encoding="utf-8"))
            state["sandbox_response_sha256"] = completion.prepare.sha256_file(
                sandbox_response_path
            )
            state["checker_result_sha256"] = checker_result_sha256
            state["checker_artifact_aggregate_sha256"] = artifact_aggregate
            state["checker_execution_receipt_sha256"] = completion.prepare.sha256_file(
                checker_receipt_path
            )
            dump(state_path, state)

            ledger = completion.build_ledger(pack, runs)
            record = next(
                item for item in ledger["records"]
                if item["semantic_run_id"] == planned["run_id"]
            )
            self.assertEqual(record["state_status"], "integrity_failure")
            self.assertFalse(record["result_eligible"])
            self.assertEqual(ledger["summary"]["result_eligible_count"], 0)
            self.assertFalse(ledger["primary_analysis_permitted"])

    def test_checked_run_rejects_tampered_sealed_checker_code(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            pack = self.synthetic_pack(root)
            runs = root / "runs"
            runs.mkdir()
            self.materialize_checked_runs(pack, runs, limit=1)
            sealed_checker = pack / "execution_code" / "check_target_drift_run.py"
            sealed_checker.write_bytes(sealed_checker.read_bytes() + b"\n# tampered\n")
            ledger = completion.build_ledger(pack, runs)
            planned = json.loads(
                (pack / "run_manifest.json").read_text(encoding="utf-8")
            )["runs"][0]
            record = next(
                item for item in ledger["records"]
                if item["semantic_run_id"] == planned["run_id"]
            )
            self.assertEqual(record["state_status"], "integrity_failure")
            self.assertFalse(record["result_eligible"])
            self.assertEqual(ledger["summary"]["result_eligible_count"], 0)
            self.assertFalse(ledger["primary_analysis_permitted"])

    def test_checked_run_rejects_tampered_sealed_runner_code(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            pack = self.synthetic_pack(root)
            runs = root / "runs"
            runs.mkdir()
            self.materialize_checked_runs(pack, runs, limit=1)
            sealed_runner = pack / "execution_code" / "run_target_drift_execution.py"
            sealed_runner.write_bytes(sealed_runner.read_bytes() + b"\n# tampered\n")
            ledger = completion.build_ledger(pack, runs)
            planned = json.loads(
                (pack / "run_manifest.json").read_text(encoding="utf-8")
            )["runs"][0]
            record = next(
                item for item in ledger["records"]
                if item["semantic_run_id"] == planned["run_id"]
            )
            self.assertEqual(record["state_status"], "integrity_failure")
            self.assertFalse(record["result_eligible"])
            self.assertEqual(ledger["summary"]["result_eligible_count"], 0)
            self.assertFalse(ledger["primary_analysis_permitted"])

    def test_tampered_policy_or_summary_fails_closed(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            pack = self.synthetic_pack(root)
            runs = root / "runs"
            runs.mkdir()
            ledger = completion.build_ledger(pack, runs)
            ledger["summary"]["missing_count"] = 449
            with self.assertRaises(SystemExit):
                completion.validate_ledger(pack, ledger, require_complete=False)

    def test_malformed_deterministic_run_directory_becomes_missing_evidence(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            pack = self.synthetic_pack(root)
            runs = root / "runs"
            runs.mkdir()
            planned = json.loads((pack / "run_manifest.json").read_text(encoding="utf-8"))["runs"][0]
            opaque = completion.runner.opaque_id("run", "a" * 64, planned["run_id"])
            (runs / opaque).mkdir()
            ledger = completion.build_ledger(pack, runs)
            first = next(record for record in ledger["records"]
                         if record["semantic_run_id"] == planned["run_id"])
            self.assertEqual(first["state_status"], "integrity_failure")
            self.assertEqual(first["missing_reason"], "run_evidence_unreadable_or_invalid")
            self.assertEqual(ledger["summary"]["missing_count"], 450)

    def test_schedule_continues_after_one_run_level_failure(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            pack = self.synthetic_pack(root)
            runs = root / "runs"
            successful = {
                "semantic_run_id": "synthetic",
                "opaque_run_id": "opaque",
                "status_before": "prepared_unrun",
                "status_after": "checked",
                "terminal": True,
                "error": None,
            }
            side_effects = [SystemExit("one run failed before materialization")] + [
                successful for _ in range(449)
            ]
            with mock.patch.object(schedule, "advance_run", side_effect=side_effects) as advance:
                with contextlib.redirect_stdout(io.StringIO()):
                    events = schedule.run_schedule(pack, runs)
            self.assertEqual(advance.call_count, 450)
            self.assertEqual(len(events), 450)
            self.assertIn("one run failed", events[0]["error"])
            self.assertEqual(events[-1]["status_after"], "checked")


if __name__ == "__main__":
    unittest.main()
