#!/usr/bin/env python3
"""Tests for the permanently result-ineligible three-condition smoke lane."""

from __future__ import annotations

import json
import os
import sys
import tempfile
import unittest
from pathlib import Path
from unittest import mock


TOOLS = Path(__file__).resolve().parent
sys.path.insert(0, str(TOOLS))

import check_target_drift_run as checker  # noqa: E402
import prepare_target_drift_execution as prepare  # noqa: E402
import prepare_target_drift_grading as grading  # noqa: E402
import prepare_target_drift_smoke as smoke  # noqa: E402
import run_target_drift_execution as runner  # noqa: E402
import run_target_drift_schedule as schedule  # noqa: E402
import run_target_drift_smoke as smoke_runner  # noqa: E402


def manifest() -> dict:
    runs = []
    for condition in runner.CONDITIONS:
        runs.append({
            "run_id": f"CASE--{condition}--replicate-17",
            "case_id": "CASE",
            "condition": condition,
            "replicate": 17,
            "requirement_variant": "source_faithful",
            "proposed_requirement": "same frozen requirement",
            "status": "sealed_unrun",
        })
    runs.append({
        "run_id": "OTHER--compile_only--replicate-17",
        "case_id": "OTHER",
        "condition": "compile_only",
        "replicate": 17,
        "requirement_variant": "injected_drift",
        "proposed_requirement": "other requirement",
        "status": "sealed_unrun",
    })
    return {
        "schema_version": 1,
        "suite_id": "ABRL-TARGET-DRIFT-V2",
        "runs": runs,
    }


class TargetDriftSmokeTest(unittest.TestCase):
    def _write_json(self, path: Path, value: dict) -> None:
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(
            json.dumps(value, indent=2, sort_keys=True) + "\n", encoding="utf-8"
        )

    def _successful_inspect_fixture(self, root: Path) -> tuple:
        aggregate = "a" * 64
        plan_sha256 = "e" * 64
        plan = smoke.build_plan(
            aggregate, manifest(), "CASE--compile_only--replicate-17",
            "b" * 64, "c" * 64,
        )
        planned = plan["runs"][0]
        runs_root = root / plan["neutral_runs_root_name"]
        opaque = runner.opaque_id("run", aggregate, planned["smoke_run_id"])
        run_dir = runs_root / opaque
        operator = run_dir / "operator"
        agent = run_dir / "agent"
        checker_root = operator / "checker"
        attempt_id = "CHK-" + "1" * 24 + "-01"
        agent.mkdir(parents=True)
        checker_root.mkdir(parents=True)

        checker_config = {
            "mode": "production",
            "checker_id": "neutral-checker",
            "checker_version": "1",
            "runtime_config_sha256": "r" * 64,
            "isolation_probe_report_sha256": "p" * 64,
            "container_image_digest": "sha256:" + "i" * 64,
            "inner_checker_sha256": "n" * 64,
            "controller_entrypoint_sha256": "o" * 64,
            "contract_sha256": "k" * 64,
            "filesystem_network_process_attestation": "restricted",
            "controller_worker_separation_attestation": "separated",
            "budgets": {"wall_clock_seconds": 60},
        }
        pack = root / "pack"
        self._write_json(pack / "execution_config.json", {
            "execution_adapter": {
                "provider_runtime": {"kind": "codex_cli"},
            },
            "posthoc_checker": checker_config,
        })
        (pack / "aggregate.sha256").write_text(aggregate + "\n", encoding="ascii")

        workspace = operator / "workspace_manifest.json"
        self._write_json(workspace, {"files": []})
        completed_manifest_sha = runner.manifest_sha256(runner.file_manifest(agent))
        job = {
            "semantic_run_id": planned["smoke_run_id"],
            "source_primary_run_id": planned["source_primary_run_id"],
            "opaque_run_id": opaque,
            "execution_purpose": runner.SMOKE_EXECUTION_PURPOSE,
            "primary_result_eligible": False,
            "smoke_plan_sha256": plan_sha256,
            "condition": planned["condition"],
            "replicate": planned["replicate"],
        }
        job_path = operator / "job.json"
        self._write_json(job_path, job)
        adapter_response_path = operator / "adapter" / "response.json"
        self._write_json(adapter_response_path, {
            "termination": "completed",
            "model_invocations": [{
                "transport": "codex_cli",
                "usage_observed": True,
            }],
        })
        receipt = {
            "opaque_run_id": opaque,
            "execution_purpose": runner.SMOKE_EXECUTION_PURPOSE,
            "primary_result_eligible": False,
            "smoke_plan_sha256": plan_sha256,
            "sealed_pack_sha256": aggregate,
            "prepared_job_sha256": prepare.sha256_file(job_path),
            "workspace_manifest_sha256": prepare.sha256_file(workspace),
            "completed_agent_manifest_sha256": completed_manifest_sha,
            "termination": "completed",
            "adapter_artifact_sha256": {
                "response.json": prepare.sha256_file(adapter_response_path),
            },
        }
        receipt_path = operator / "execution-receipt.json"
        self._write_json(receipt_path, receipt)
        receipt_sha = prepare.sha256_file(receipt_path)

        request = {
            "sealed_pack_sha256": aggregate,
            "execution_receipt_sha256": receipt_sha,
            "completed_agent_manifest_sha256": completed_manifest_sha,
            "container_image_digest": checker_config["container_image_digest"],
            "inner_checker_sha256": checker_config["inner_checker_sha256"],
            "checker_contract_sha256": checker_config["contract_sha256"],
            "checker_runtime_config_sha256": checker_config["runtime_config_sha256"],
        }
        request_path = operator / "checker-attempts" / attempt_id / "request.json"
        self._write_json(request_path, request)
        request_sha = prepare.sha256_file(request_path)
        result = {
            "opaque_run_id": opaque,
            "sealed_pack_sha256": aggregate,
            "execution_receipt_sha256": receipt_sha,
        }
        result_path = checker_root / "checker-result.json"
        self._write_json(result_path, result)
        result_sha = prepare.sha256_file(result_path)
        artifacts = [{
            "path": "checker-result.json",
            "bytes": result_path.stat().st_size,
            "sha256": result_sha,
        }]
        artifact_aggregate = checker.artifact_aggregate(artifacts)
        response = {
            "schema_version": 1,
            "opaque_run_id": opaque,
            "checker_attempt_id": attempt_id,
            "checker_attempt_label": attempt_id,
            "request_sha256": request_sha,
            "checker_result_sha256": result_sha,
            "artifact_manifest": artifacts,
            "artifact_aggregate_sha256": artifact_aggregate,
            "termination": "completed",
            "process_exit_code": 0,
            "measured_wall_seconds": 1.0,
            "checker_id": checker_config["checker_id"],
            "checker_version": checker_config["checker_version"],
            "inner_checker_sha256": checker_config["inner_checker_sha256"],
            "controller_entrypoint_sha256": checker_config[
                "controller_entrypoint_sha256"
            ],
            "checker_contract_sha256": checker_config["contract_sha256"],
            "checker_runtime_config_sha256": checker_config["runtime_config_sha256"],
            "container_image_digest": checker_config["container_image_digest"],
            "filesystem_network_process_attestation": checker_config[
                "filesystem_network_process_attestation"
            ],
            "controller_worker_separation_attestation": checker_config[
                "controller_worker_separation_attestation"
            ],
        }
        response_path = checker_root / "sandbox-response.json"
        self._write_json(response_path, response)
        checker_receipt = {
            "opaque_run_id": opaque,
            "checker_attempt_id": attempt_id,
            "checker_request_sha256": request_sha,
            "sandbox_response_sha256": prepare.sha256_file(response_path),
            "checker_result_sha256": result_sha,
            "checker_artifact_aggregate_sha256": artifact_aggregate,
            "checker_runtime_config_sha256": checker_config["runtime_config_sha256"],
            "isolation_probe_report_sha256": checker_config[
                "isolation_probe_report_sha256"
            ],
            "checker_mode": "production",
            "execution_purpose": runner.SMOKE_EXECUTION_PURPOSE,
            "result_eligible": False,
        }
        checker_receipt_path = checker_root / "checker-execution-receipt.json"
        self._write_json(checker_receipt_path, checker_receipt)
        state = {
            "status": "checked_smoke_nonexperimental",
            "result_eligible": False,
            "checker_mode": "production",
            "opaque_run_id": opaque,
            "execution_purpose": runner.SMOKE_EXECUTION_PURPOSE,
            "smoke_plan_sha256": plan_sha256,
            "sealed_pack_sha256": aggregate,
            "prepared_job_sha256": prepare.sha256_file(job_path),
            "workspace_manifest_sha256": prepare.sha256_file(workspace),
            "execution_receipt_sha256": receipt_sha,
            "checker_execution_receipt_sha256": prepare.sha256_file(
                checker_receipt_path
            ),
            "checker_result_sha256": result_sha,
            "sandbox_response_sha256": prepare.sha256_file(response_path),
            "completed_agent_manifest_sha256": completed_manifest_sha,
            "checker_runtime_config_sha256": checker_config["runtime_config_sha256"],
            "isolation_probe_report_sha256": checker_config[
                "isolation_probe_report_sha256"
            ],
            "checker_attempt_id": attempt_id,
            "checker_request_sha256": request_sha,
            "checker_artifact_aggregate_sha256": artifact_aggregate,
        }
        state_path = operator / "run_state.json"
        self._write_json(state_path, state)
        return pack, plan, plan_sha256, planned, runs_root, checker_receipt_path, state_path

    def test_plan_selects_one_matched_triplet_and_never_marks_it_eligible(self) -> None:
        plan = smoke.build_plan(
            "a" * 64, manifest(), "CASE--compile_only--replicate-17",
            "b" * 64, "c" * 64,
        )
        self.assertEqual(plan["run_count"], 3)
        self.assertEqual(
            {run["condition"] for run in plan["runs"]}, set(runner.CONDITIONS)
        )
        self.assertTrue(all(run["primary_result_eligible"] is False
                            for run in plan["runs"]))
        self.assertEqual(len({run["smoke_run_id"] for run in plan["runs"]}), 3)
        self.assertTrue(plan["result_boundary"]["grading_forbidden"])

    def test_plan_rejects_incomplete_condition_block(self) -> None:
        incomplete = manifest()
        incomplete["runs"] = incomplete["runs"][:2]
        with self.assertRaises(SystemExit):
            smoke.build_plan(
                "a" * 64, incomplete, "CASE--compile_only--replicate-17",
                "b" * 64, "c" * 64,
            )

    def test_smoke_plan_validation_binds_pack_tools_and_false_eligibility(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            pack = root / "pack"
            pack.mkdir()
            (pack / "aggregate.sha256").write_text("a" * 64 + "\n", encoding="ascii")
            (pack / "run_manifest.json").write_text(
                json.dumps(manifest()) + "\n", encoding="utf-8"
            )
            plan = smoke.build_plan(
                "a" * 64, manifest(), "CASE--compile_only--replicate-17",
                prepare.sha256_file(Path(smoke.__file__).resolve()),
                prepare.sha256_file(Path(smoke_runner.__file__).resolve()),
            )
            plan_path = root / "smoke-plan.json"
            plan_path.write_text(json.dumps(plan) + "\n", encoding="utf-8")
            with mock.patch.object(prepare, "verify_pack", return_value=None):
                self.assertEqual(
                    smoke_runner.validate_plan(pack, plan_path)[0]["run_count"], 3
                )
                plan["primary_result_eligible"] = True
                plan_path.write_text(json.dumps(plan) + "\n", encoding="utf-8")
                with self.assertRaises(SystemExit):
                    smoke_runner.validate_plan(pack, plan_path)

    def test_production_checker_keeps_smoke_permanently_ineligible(self) -> None:
        status, eligible = checker.checked_state_for({
            "execution_purpose": runner.SMOKE_EXECUTION_PURPOSE,
            "primary_result_eligible": False,
        }, "production", "codex_cli", "completed")
        self.assertEqual(status, "checked_smoke_nonexperimental")
        self.assertFalse(eligible)
        self.assertEqual(
            checker.checked_state_for({
                "execution_purpose": runner.PRIMARY_EXECUTION_PURPOSE,
                "primary_result_eligible": True,
            }, "production", "codex_cli", "completed"),
            ("checked", True),
        )
        with self.assertRaises(checker.CheckerFailure):
            checker.checked_state_for({
                "execution_purpose": runner.PRIMARY_EXECUTION_PURPOSE,
                "primary_result_eligible": True,
            }, "production", "excluded_fixture", "completed")
        with self.assertRaises(checker.CheckerFailure):
            checker.checked_state_for({
                "execution_purpose": runner.PRIMARY_EXECUTION_PURPOSE,
                "primary_result_eligible": True,
            }, "production", "codex_cli", "infrastructure_failure")

    def test_schedule_smoke_gate_rebuilds_exact_passed_records(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            pack = root / "pack"
            self._write_json(pack / "execution_config.json", {
                "execution_adapter": {
                    "provider_runtime": {"kind": "codex_cli"},
                },
                "posthoc_checker": {"mode": "production"},
            })
            plan_path = root / "smoke-plan.json"
            ledger_path = root / "smoke-ledger.json"
            self._write_json(plan_path, {"placeholder": True})
            self._write_json(ledger_path, {"placeholder": True})
            planned = [{"smoke_run_id": f"smoke-{index}"} for index in range(3)]
            plan = {"runs": planned}
            records = [{"smoke_run_id": item["smoke_run_id"]} for item in planned]
            ledger = {
                "status": "passed_result_ineligible_smoke",
                "all_three_infrastructure_paths_passed": True,
                "records": records,
            }
            with mock.patch.object(
                smoke_runner, "validate_plan", return_value=(plan, "p" * 64)
            ), mock.patch.object(
                smoke_runner, "load_bound", return_value=(ledger, "l" * 64)
            ), mock.patch.object(
                smoke_runner, "validate_ledger", return_value=None
            ), mock.patch.object(
                smoke_runner, "canonical_runs_root", return_value=root / "runs"
            ), mock.patch.object(
                smoke_runner, "inspect_smoke_run", side_effect=records
            ):
                gate = schedule.validate_smoke_gate(pack, plan_path, ledger_path)
            self.assertEqual(gate["status"], "passed_result_ineligible_smoke")
            self.assertFalse(gate["primary_result_eligible"])

    def test_schedule_smoke_gate_rejects_failed_or_rebound_evidence(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            pack = root / "pack"
            self._write_json(pack / "execution_config.json", {
                "execution_adapter": {
                    "provider_runtime": {"kind": "codex_cli"},
                },
                "posthoc_checker": {"mode": "production"},
            })
            plan_path = root / "smoke-plan.json"
            ledger_path = root / "smoke-ledger.json"
            self._write_json(plan_path, {"placeholder": True})
            self._write_json(ledger_path, {"placeholder": True})
            plan = {"runs": [{"smoke_run_id": f"smoke-{index}"} for index in range(3)]}
            failed = {
                "status": "failed_result_ineligible_smoke",
                "all_three_infrastructure_paths_passed": False,
                "records": [],
            }
            with mock.patch.object(
                smoke_runner, "validate_plan", return_value=(plan, "p" * 64)
            ), mock.patch.object(
                smoke_runner, "load_bound", return_value=(failed, "l" * 64)
            ), mock.patch.object(smoke_runner, "validate_ledger", return_value=None):
                with self.assertRaises(SystemExit):
                    schedule.validate_smoke_gate(pack, plan_path, ledger_path)

            records = [{"smoke_run_id": item["smoke_run_id"]} for item in plan["runs"]]
            passed = {
                "status": "passed_result_ineligible_smoke",
                "all_three_infrastructure_paths_passed": True,
                "records": records,
            }
            rebound = [{"smoke_run_id": "different"}] * 3
            with mock.patch.object(
                smoke_runner, "validate_plan", return_value=(plan, "p" * 64)
            ), mock.patch.object(
                smoke_runner, "load_bound", return_value=(passed, "l" * 64)
            ), mock.patch.object(
                smoke_runner, "validate_ledger", return_value=None
            ), mock.patch.object(
                smoke_runner, "canonical_runs_root", return_value=root / "runs"
            ), mock.patch.object(
                smoke_runner, "inspect_smoke_run", side_effect=rebound
            ):
                with self.assertRaises(SystemExit):
                    schedule.validate_smoke_gate(pack, plan_path, ledger_path)

    def test_agent_request_cannot_distinguish_primary_from_smoke(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            agent = Path(directory)
            common = {
                "opaque_run_id": "RUN-opaque",
                "replicate": 17,
                "model": {}, "pricing": {}, "budgets": {}, "retry_policy": {},
                "result_contract": {}, "provider_runtime": {},
            }
            smoke_job = {
                **common,
                "execution_purpose": runner.SMOKE_EXECUTION_PURPOSE,
                "primary_result_eligible": False,
                "smoke_plan_sha256": "a" * 64,
            }
            primary_job = {
                **common,
                "execution_purpose": runner.PRIMARY_EXECUTION_PURPOSE,
                "primary_result_eligible": True,
                "smoke_plan_sha256": None,
            }
            self.assertEqual(
                runner.adapter_request(smoke_job, agent),
                runner.adapter_request(primary_job, agent),
            )
            request = runner.adapter_request(smoke_job, agent)
            self.assertNotIn("execution_purpose", request)
            self.assertNotIn("primary_result_eligible", request)
            self.assertNotIn("smoke_plan_sha256", request)

    def test_neutral_root_and_relative_prompt_hide_smoke_path_semantics(self) -> None:
        plan = smoke.build_plan(
            "a" * 64, manifest(), "CASE--compile_only--replicate-17",
            "b" * 64, "c" * 64,
        )
        with tempfile.TemporaryDirectory() as directory:
            neutral_root = smoke_runner.canonical_runs_root(plan, Path(directory))
            rendered = runner.render_prompt(
                "{{CASE_ID}} {{SOURCE_ID}} {{SOURCE_LOCATOR}} "
                "{{SOURCE_PACKET_PATH}} {{PROPOSED_REQUIREMENT}} {{WORKSPACE_PATH}}",
                "CASE-opaque", "SOURCE-opaque", "public locator",
                "source/source.pdf", "same requirement", "workspace",
            )
            lowered = rendered.lower()
            self.assertNotIn("smoke", lowered)
            self.assertNotIn(str(neutral_root).lower(), lowered)
            self.assertEqual(neutral_root.name, plan["neutral_runs_root_name"])
            if os.name == "nt":
                with self.assertRaises(SystemExit):
                    smoke_runner.canonical_runs_root(plan)

    def test_validator_rejects_mixed_case_triplet_and_tampered_ids(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            pack = root / "pack"
            pack.mkdir()
            source_manifest = manifest()
            extra = []
            for condition in runner.CONDITIONS:
                extra.append({
                    "run_id": f"SECOND--{condition}--replicate-17",
                    "case_id": "SECOND", "condition": condition, "replicate": 17,
                    "requirement_variant": "source_faithful",
                    "proposed_requirement": "same frozen requirement",
                    "status": "sealed_unrun",
                })
            source_manifest["runs"].extend(extra)
            (pack / "aggregate.sha256").write_text("a" * 64 + "\n", encoding="ascii")
            (pack / "run_manifest.json").write_text(
                json.dumps(source_manifest) + "\n", encoding="utf-8"
            )
            plan = smoke.build_plan(
                "a" * 64, source_manifest, "CASE--compile_only--replicate-17",
                prepare.sha256_file(Path(smoke.__file__).resolve()),
                prepare.sha256_file(Path(smoke_runner.__file__).resolve()),
            )
            plan["runs"][1]["source_primary_run_id"] = (
                "SECOND--source_aware_blueprint--replicate-17"
            )
            plan["runs"][1]["smoke_run_id"] = smoke.smoke_run_id(
                "a" * 64, plan["runs"][1]["source_primary_run_id"]
            )
            plan_path = root / "plan.json"
            plan_path.write_text(json.dumps(plan) + "\n", encoding="utf-8")
            with mock.patch.object(prepare, "verify_pack", return_value=None), \
                    self.assertRaises(SystemExit):
                smoke_runner.validate_plan(pack, plan_path)

    def test_attempt_binding_is_resumable_only_at_the_same_paths(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            plan_path = root / "plan.json"
            plan_path.write_text("{}\n", encoding="utf-8")
            plan_sha256 = prepare.sha256_file(plan_path)
            runs = root / ("RUNS-" + "a" * 20)
            ledger = root / "ledger.json"
            attempt = smoke_runner.bind_single_attempt(
                plan_path, plan_sha256, runs.resolve(), ledger.resolve()
            )
            self.assertEqual(
                smoke_runner.bind_single_attempt(
                    plan_path, plan_sha256, runs.resolve(), ledger.resolve()
                ), attempt,
            )
            with self.assertRaises(SystemExit):
                smoke_runner.bind_single_attempt(
                    plan_path, plan_sha256, runs.resolve(),
                    (root / "different-ledger.json").resolve(),
                )

    def test_attempt_lock_rejects_a_concurrent_second_owner(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            plan_one = root / "plan-one.json"
            plan_two = root / "plan-two.json"
            plan_one.write_text("{}\n", encoding="utf-8")
            plan_two.write_text("{  }\n", encoding="utf-8")
            digest = prepare.sha256_file(plan_one)
            runs = root / ("RUNS-" + "a" * 20)
            _, _, lock_one = smoke_runner.attempt_registry_paths(digest, runs)
            _, _, lock_two = smoke_runner.attempt_registry_paths(
                prepare.sha256_file(plan_two), runs
            )
            self.assertEqual(lock_one, lock_two)
            with smoke_runner.exclusive_attempt_lock(lock_one):
                with self.assertRaises(SystemExit):
                    with smoke_runner.exclusive_attempt_lock(lock_two):
                        self.fail("concurrent lock unexpectedly acquired")

    def test_successful_inspector_rejects_rebound_checker_receipt(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            fixture = self._successful_inspect_fixture(Path(directory))
            pack, plan, plan_sha, planned, runs_root, receipt_path, state_path = fixture
            with mock.patch.object(
                checker, "require_adapter_artifacts_unchanged", return_value=None
            ), mock.patch.object(checker, "validate_checker_result", return_value=None):
                record = smoke_runner.inspect_smoke_run(
                    pack, plan, plan_sha, planned, runs_root
                )
                self.assertEqual(record["status"], "checked_smoke_nonexperimental")

                checker_receipt = json.loads(receipt_path.read_text(encoding="utf-8"))
                checker_receipt["checker_result_sha256"] = "f" * 64
                self._write_json(receipt_path, checker_receipt)
                state = json.loads(state_path.read_text(encoding="utf-8"))
                state["checker_execution_receipt_sha256"] = prepare.sha256_file(
                    receipt_path
                )
                self._write_json(state_path, state)
                with self.assertRaises(SystemExit):
                    smoke_runner.inspect_smoke_run(
                        pack, plan, plan_sha, planned, runs_root
                    )

    def test_preseeded_state_strings_cannot_forge_a_pass(self) -> None:
        plan = smoke.build_plan(
            "a" * 64, manifest(), "CASE--compile_only--replicate-17",
            "b" * 64, "c" * 64,
        )
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory) / plan["neutral_runs_root_name"]
            for planned in plan["runs"]:
                opaque = runner.opaque_id("run", "a" * 64, planned["smoke_run_id"])
                operator = root / opaque / "operator"
                operator.mkdir(parents=True)
                (operator / "run_state.json").write_text(json.dumps({
                    "status": "checked_smoke_nonexperimental",
                    "checker_mode": "production",
                    "result_eligible": False,
                }) + "\n", encoding="utf-8")
            with mock.patch.object(
                smoke_runner, "canonical_runs_root", return_value=root.resolve()
            ), mock.patch.object(
                runner, "prepare_run", side_effect=AssertionError("must not execute")
            ), mock.patch.object(
                runner, "execute_or_record_failure", side_effect=AssertionError("must not execute")
            ), mock.patch.object(
                checker, "execute", side_effect=AssertionError("must not execute")
            ):
                ledger = smoke_runner.run_smoke(
                    Path(directory), plan, "e" * 64, root.resolve()
                )
            self.assertFalse(ledger["all_three_infrastructure_paths_passed"])
            self.assertEqual(ledger["status"], "failed_result_ineligible_smoke")
            self.assertTrue(all(record["error"] for record in ledger["records"]))

    def test_ledger_validator_rejects_any_result_eligible_smoke_record(self) -> None:
        plan = smoke.build_plan(
            "a" * 64, manifest(), "CASE--compile_only--replicate-17",
            "b" * 64, "c" * 64,
        )
        records = [{
            "smoke_run_id": run["smoke_run_id"],
            "opaque_run_id": "RUN-opaque-" + str(index),
            "condition": run["condition"],
            "status": "checked_smoke_nonexperimental",
            "checker_mode": "production",
            "result_eligible": False,
            "run_state_sha256": "d" * 64,
            "error": None,
        } for index, run in enumerate(plan["runs"])]
        ledger = {
            "schema_version": 1,
            "suite_id": "ABRL-TARGET-DRIFT-V2",
            "execution_purpose": runner.SMOKE_EXECUTION_PURPOSE,
            "primary_result_eligible": False,
            "sealed_pack_sha256": "a" * 64,
            "smoke_plan_sha256": "e" * 64,
            "run_count": 3,
            "all_three_infrastructure_paths_passed": True,
            "model_or_formalization_outcome_reported": False,
            "records": records,
            "status": "passed_result_ineligible_smoke",
        }
        smoke_runner.validate_ledger(plan, "e" * 64, ledger)
        ledger["records"][0]["result_eligible"] = True
        with self.assertRaises(SystemExit):
            smoke_runner.validate_ledger(plan, "e" * 64, ledger)

    def test_grading_rejects_smoke_even_with_production_checker(self) -> None:
        with self.assertRaises(SystemExit):
            grading.require_primary_job({
                "execution_purpose": runner.SMOKE_EXECUTION_PURPOSE,
                "primary_result_eligible": False,
                "checker_mode": "production",
            }, "smoke")
        grading.require_primary_job({
            "execution_purpose": runner.PRIMARY_EXECUTION_PURPOSE,
            "primary_result_eligible": True,
        }, "primary")


if __name__ == "__main__":
    unittest.main()
