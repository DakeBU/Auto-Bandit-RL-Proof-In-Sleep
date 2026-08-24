#!/usr/bin/env python3
"""Tests for result-free, provider-disabled LeanFlow comparator plumbing."""

from __future__ import annotations

import contextlib
import hashlib
import io
import json
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path
from unittest import mock


TOOLS = Path(__file__).resolve().parent
ROOT = TOOLS.parent
V2 = ROOT / "evaluation" / "target-drift-v2"
sys.path.insert(0, str(TOOLS))

import build_leanflow_target_drift_completion_ledger as ledger_builder  # noqa: E402
import build_leanflow_target_drift_schedule as schedule_builder  # noqa: E402
import fake_leanflow_target_drift_adapter as fake_adapter  # noqa: E402
import validate_target_drift_external_comparator as validator  # noqa: E402
import build_anonymous_iclr_supplement as anonymous_builder  # noqa: E402


def load(path: Path) -> dict:
    return json.loads(path.read_text(encoding="utf-8"))


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


class LeanFlowExternalComparatorTests(unittest.TestCase):
    def setUp(self) -> None:
        self.contract_path = V2 / "leanflow-adapter-contract.json"
        self.schedule_path = V2 / "leanflow-external-schedule.json"
        self.request_path = V2 / "leanflow-excluded-fixture-request.json"
        self.ledger_contract_path = (
            V2 / "leanflow-external-completion-ledger-contract.json"
        )
        self.contract = load(self.contract_path)
        self.schedule = load(self.schedule_path)
        self.request = load(self.request_path)
        self.ledger_contract = load(self.ledger_contract_path)

    def test_schedule_is_exact_deterministic_30_id_universe(self) -> None:
        self.assertEqual(self.schedule, schedule_builder.build_schedule())
        runs = self.schedule["runs"]
        self.assertEqual(len(runs), 30)
        self.assertEqual(len({run["run_id"] for run in runs}), 30)
        self.assertEqual(
            [run["presentation_order"] for run in runs], list(range(30))
        )
        self.assertEqual(
            sum(run["requirement_variant"] == "source_faithful" for run in runs),
            15,
        )
        self.assertEqual(
            sum(run["requirement_variant"] == "injected_drift" for run in runs),
            15,
        )
        self.assertTrue(all(
            run["run_id"]
            == f"{run['case_id']}--leanflow_external--replicate-0"
            and run["condition"] == "leanflow_external"
            and run["replicate_index"] == 0
            and run["status"] == "sealed_unrun"
            for run in runs
        ))

    def test_fixture_request_is_bound_to_first_scheduled_id(self) -> None:
        first = self.schedule["runs"][0]
        expected_opaque = hashlib.sha256((
            f"leanflow-excluded-fixture:{sha256(self.schedule_path)}:"
            f"{first['run_id']}"
        ).encode("utf-8")).hexdigest()
        self.assertEqual(self.request["semantic_run_id"], first["run_id"])
        self.assertEqual(self.request["requirement_variant"], first["requirement_variant"])
        self.assertEqual(self.request["opaque_run_id"], expected_opaque)
        self.assertEqual(self.request["schedule_sha256"], sha256(self.schedule_path))
        self.assertEqual(
            self.request["adapter_contract_sha256"], sha256(self.contract_path)
        )

    def test_adapter_fails_closed_on_provider_or_credential_surface(self) -> None:
        provider_enabled = dict(self.request)
        provider_enabled["provider_mode"] = "enabled"
        with self.assertRaises(SystemExit):
            fake_adapter.build_fixture_response(
                provider_enabled, self.contract, "a" * 64, sha256(self.contract_path),
                self.schedule, sha256(self.schedule_path)
            )

        positive_budget = dict(self.request)
        positive_budget["model_invocations_allowed"] = 1
        with self.assertRaises(SystemExit):
            fake_adapter.build_fixture_response(
                positive_budget, self.contract, "a" * 64, sha256(self.contract_path),
                self.schedule, sha256(self.schedule_path)
            )

        credential_field = dict(self.request)
        credential_field["api_key"] = "fixture-must-not-accept-credentials"
        with self.assertRaises(SystemExit):
            fake_adapter.build_fixture_response(
                credential_field, self.contract, "a" * 64, sha256(self.contract_path),
                self.schedule, sha256(self.schedule_path)
            )

    def test_adapter_rejects_a_request_outside_the_sealed_schedule(self) -> None:
        outside = dict(self.request)
        outside["case_id"] = "NOT-IN-SCHEDULE"
        outside["semantic_run_id"] = (
            "NOT-IN-SCHEDULE--leanflow_external--replicate-0"
        )
        outside["opaque_run_id"] = hashlib.sha256((
            f"leanflow-excluded-fixture:{sha256(self.schedule_path)}:"
            f"{outside['semantic_run_id']}"
        ).encode("utf-8")).hexdigest()
        with self.assertRaises(SystemExit):
            fake_adapter.build_fixture_response(
                outside, self.contract, "a" * 64, sha256(self.contract_path),
                self.schedule, sha256(self.schedule_path)
            )

    def test_fixture_cli_emits_only_zero_usage_excluded_evidence(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            contract_path = root / "contract.json"
            schedule_path = root / "schedule.json"
            request_path = root / "request.json"
            response_path = root / "fixture-response.json"
            trace_path = root / "fixture-trace.jsonl"
            contract_path.write_bytes(self.contract_path.read_bytes())
            schedule_path.write_bytes(self.schedule_path.read_bytes())
            request = dict(self.request)
            request["adapter_contract_sha256"] = sha256(contract_path)
            request_path.write_text(
                json.dumps(request, indent=2, sort_keys=True) + "\n", encoding="utf-8"
            )
            argv = [
                "fake_leanflow_target_drift_adapter.py",
                "--mode", "excluded-fixture-smoke",
                "--contract", str(contract_path),
                "--schedule", str(schedule_path),
                "--request", str(request_path),
                "--response", str(response_path),
                "--trace", str(trace_path),
            ]
            with mock.patch.object(sys, "argv", argv), contextlib.redirect_stdout(io.StringIO()):
                fake_adapter.main()
            response = load(response_path)
            events = [json.loads(line) for line in trace_path.read_text(
                encoding="utf-8"
            ).splitlines()]
            self.assertEqual(response["status"], "excluded_fixture_completed")
            self.assertFalse(response["result_eligible"])
            self.assertFalse(response["provider_called"])
            self.assertFalse(response["credentials_read"])
            self.assertFalse(response["network_used"])
            self.assertFalse(response["leanflow_repository_executed"])
            self.assertFalse(response["formalization_outcome_reported"])
            self.assertEqual(response["model_invocations"], 0)
            self.assertTrue(all(value == 0 for value in response["usage"].values()))
            self.assertEqual(
                [event["kind"] for event in events],
                self.contract["trace_schema"]["event_kinds_in_order"],
            )

    def test_fixture_refuses_production_results_filename(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            contract_path = root / "contract.json"
            schedule_path = root / "schedule.json"
            request_path = root / "request.json"
            contract_path.write_bytes(self.contract_path.read_bytes())
            schedule_path.write_bytes(self.schedule_path.read_bytes())
            request = dict(self.request)
            request["adapter_contract_sha256"] = sha256(contract_path)
            request_path.write_text(json.dumps(request) + "\n", encoding="utf-8")
            forbidden = root / "external-comparator-results.json"
            argv = [
                "fake_leanflow_target_drift_adapter.py",
                "--mode", "excluded-fixture-smoke",
                "--contract", str(contract_path),
                "--schedule", str(schedule_path),
                "--request", str(request_path),
                "--response", str(forbidden),
                "--trace", str(root / "trace.jsonl"),
            ]
            with mock.patch.object(sys, "argv", argv), self.assertRaises(SystemExit):
                fake_adapter.main()
            self.assertFalse(forbidden.exists())

    def test_fixture_preflights_both_outputs_before_writing(self) -> None:
        for preexisting in ("response", "trace"):
            with self.subTest(preexisting=preexisting), tempfile.TemporaryDirectory() as directory:
                root = Path(directory)
                contract_path = root / "contract.json"
                schedule_path = root / "schedule.json"
                request_path = root / "request.json"
                response_path = root / "fixture-response.json"
                trace_path = root / "fixture-trace.jsonl"
                contract_path.write_bytes(self.contract_path.read_bytes())
                schedule_path.write_bytes(self.schedule_path.read_bytes())
                request = dict(self.request)
                request["adapter_contract_sha256"] = sha256(contract_path)
                request_path.write_text(
                    json.dumps(request, indent=2, sort_keys=True) + "\n",
                    encoding="utf-8",
                )
                occupied = response_path if preexisting == "response" else trace_path
                occupied.write_text("sentinel\n", encoding="utf-8")
                argv = [
                    "fake_leanflow_target_drift_adapter.py",
                    "--mode", "excluded-fixture-smoke",
                    "--contract", str(contract_path),
                    "--schedule", str(schedule_path),
                    "--request", str(request_path),
                    "--response", str(response_path),
                    "--trace", str(trace_path),
                ]
                with mock.patch.object(sys, "argv", argv), self.assertRaises(SystemExit):
                    fake_adapter.main()
                self.assertEqual(occupied.read_text(encoding="utf-8"), "sentinel\n")
                other = trace_path if preexisting == "response" else response_path
                self.assertFalse(other.exists())

    def test_completion_ledger_builder_is_result_free_and_exact(self) -> None:
        ledger = ledger_builder.build_result_free_ledger(
            self.schedule, self.ledger_contract, sha256(self.schedule_path)
        )
        ledger_builder.validate_result_free_ledger(
            ledger, self.schedule, self.ledger_contract
        )
        self.assertEqual(len(ledger["records"]), 30)
        self.assertEqual(ledger["result_eligible_count"], 0)
        self.assertEqual(ledger["missing_count"], 30)
        self.assertFalse(ledger["outcomes_observed"])
        self.assertFalse(ledger["complete_analysis_gate_passed"])
        self.assertFalse(ledger["effect_estimates_permitted"])
        summary = ledger["missingness_summary"]
        self.assertEqual(summary["missing_by_condition"], {"leanflow_external": 30})
        self.assertEqual(sum(summary["missing_by_paper_cluster"].values()), 18)
        self.assertEqual(sum(summary["missing_by_textbook_target"].values()), 12)
        self.assertTrue(all(
            record["state_status"] == "not_materialized"
            and record["result_eligible"] is False
            and record["evidence_sha256"] == {}
            and record["source_id"]
            and record["stratum"] in {"paper_derived", "textbook_control"}
            for record in ledger["records"]
        ))

    def test_result_and_production_ledger_files_remain_absent(self) -> None:
        self.assertFalse((V2 / "external-comparator-results.json").exists())
        self.assertFalse((V2 / "leanflow-external-completion-ledger.json").exists())

    def test_repository_validator_accepts_only_sealed_result_free_plumbing(self) -> None:
        output = io.StringIO()
        with contextlib.redirect_stdout(output):
            validator.main()
        rendered = output.getvalue()
        self.assertIn("external comparator plan valid and unrun", rendered)
        self.assertIn("provider-disabled excluded fixture valid", rendered)
        self.assertIn("result and completion ledger absent", rendered)

    def test_anonymous_payload_rebinds_the_complete_result_free_hash_chain(self) -> None:
        evaluation_paths = (
            anonymous_builder.TARGET_DRIFT_V2_PROTOCOL,
            anonymous_builder.EXTERNAL_COMPARATOR_PLAN,
            anonymous_builder.EXTERNAL_COMPARATOR_SEAL,
            anonymous_builder.LEANFLOW_ADAPTER_CONTRACT,
            anonymous_builder.LEANFLOW_EXTERNAL_SCHEDULE,
            anonymous_builder.LEANFLOW_FIXTURE_REQUEST,
            anonymous_builder.LEANFLOW_LEDGER_CONTRACT,
            anonymous_builder.LEANFLOW_PLUMBING_SEAL,
            "evaluation/target-drift-v1/challenges.json",
            "evaluation/target-drift-v2/paired-requirements.json",
        )
        tool_paths = (
            "tools/validate_target_drift_external_comparator.py",
            anonymous_builder.LEANFLOW_FAKE_ADAPTER,
            anonymous_builder.LEANFLOW_SCHEDULE_BUILDER,
            anonymous_builder.LEANFLOW_LEDGER_BUILDER,
        )
        payload: dict[str, bytes] = {}
        anonymous_reference = "0" * 40
        for rel in evaluation_paths:
            data = anonymous_builder.anonymize_evaluation_bytes(
                rel, anonymous_builder.read_regular(rel), anonymous_reference
            )
            anonymous_builder.add_payload(payload, rel, data)
        for rel in tool_paths:
            data = anonymous_builder.anonymize_evaluation_bytes(
                rel, anonymous_builder.read_regular(rel), anonymous_reference
            )
            anonymous_builder.add_payload(payload, rel, data)
        anonymous_builder.rebind_anonymous_external_comparator(payload)

        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            for rel, data in payload.items():
                destination = root / rel
                destination.parent.mkdir(parents=True, exist_ok=True)
                destination.write_bytes(data)
            completed = subprocess.run(
                [sys.executable, "tools/validate_target_drift_external_comparator.py"],
                cwd=root,
                text=True,
                stdout=subprocess.PIPE,
                stderr=subprocess.PIPE,
                check=False,
            )
            self.assertEqual(
                completed.returncode, 0, msg=completed.stdout + completed.stderr
            )
            self.assertIn("provider-disabled excluded fixture valid", completed.stdout)
            self.assertFalse((
                root / "evaluation/target-drift-v2/external-comparator-results.json"
            ).exists())


if __name__ == "__main__":
    unittest.main()
