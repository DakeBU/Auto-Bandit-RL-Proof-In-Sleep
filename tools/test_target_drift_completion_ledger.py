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
        dump(pack / "execution_config.json", {
            "suite_id": "ABRL-TARGET-DRIFT-V2",
            "execution_adapter": {
                "provider_runtime": {"kind": "codex_cli"},
            },
            "posthoc_checker": {"mode": "production"},
            "retry_policy": {
                "missing_run_policy": completion.POLICY_ID,
            },
            "missing_run_policy": {
                "policy_id": completion.POLICY_ID,
                "policy_sha256": policy_sha256,
            },
        })
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

    def materialize_checked_runs(self, pack: Path, runs_root: Path) -> None:
        aggregate = (pack / "aggregate.sha256").read_text(encoding="ascii").strip()
        planned_runs = json.loads(
            (pack / "run_manifest.json").read_text(encoding="utf-8")
        )["runs"]
        for planned in planned_runs:
            opaque = completion.runner.opaque_id("run", aggregate, planned["run_id"])
            operator = runs_root / opaque / "operator"
            job_path = operator / "job.json"
            dump(job_path, {
                "semantic_run_id": planned["run_id"],
                "opaque_run_id": opaque,
                "execution_purpose": completion.runner.PRIMARY_EXECUTION_PURPOSE,
                "primary_result_eligible": True,
            })
            workspace_manifest_path = operator / "workspace_manifest.json"
            dump(workspace_manifest_path, {})
            adapter_response_path = operator / "adapter" / "response.json"
            dump(adapter_response_path, {
                "termination": "completed",
                "model_invocations": [{
                    "transport": "codex_cli",
                    "usage_observed": True,
                }],
            })
            dump(operator / "execution-receipt.json", {
                "termination": "completed",
                "adapter_artifact_sha256": {
                    "response.json": completion.prepare.sha256_file(adapter_response_path),
                },
            })
            execution_receipt_path = operator / "execution-receipt.json"
            checker_result_path = operator / "checker" / "checker-result.json"
            dump(checker_result_path, {})
            checker_receipt_path = (
                operator / "checker" / "checker-execution-receipt.json"
            )
            dump(checker_receipt_path, {
                "checker_mode": "production",
                "execution_purpose": completion.runner.PRIMARY_EXECUTION_PURPOSE,
                "result_eligible": True,
            })
            sandbox_response_path = operator / "checker" / "sandbox-response.json"
            dump(sandbox_response_path, {})
            checker_attempt_id = "checker-attempt-1"
            checker_request_path = (
                operator / "checker-attempts" / checker_attempt_id / "request.json"
            )
            dump(checker_request_path, {})
            dump(operator / "run_state.json", {
                "schema_version": 1,
                "status": "checked",
                "opaque_run_id": opaque,
                "sealed_pack_sha256": aggregate,
                "result_eligible": True,
                "checker_mode": "production",
                "prepared_job_sha256": completion.prepare.sha256_file(job_path),
                "workspace_manifest_sha256": completion.prepare.sha256_file(
                    workspace_manifest_path
                ),
                "execution_receipt_sha256": completion.prepare.sha256_file(
                    execution_receipt_path
                ),
                "checker_attempt_id": checker_attempt_id,
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
            self.materialize_checked_runs(pack, runs)
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
            self.assertEqual(ledger["summary"]["missing_count"], 1)

    def test_checked_state_missing_expected_hash_binding_is_missing(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            pack = self.synthetic_pack(root)
            runs = root / "runs"
            runs.mkdir()
            self.materialize_checked_runs(pack, runs)
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
                            run_dir, planned, "a" * 64, config
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
            self.assertEqual(ledger["summary"]["missing_count"], 1)

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
