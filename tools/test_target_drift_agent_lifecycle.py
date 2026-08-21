from __future__ import annotations

import json
import os
import tempfile
import unittest
from pathlib import Path

import record_target_drift_agent_lifecycle_probe as probe
import target_drift_agent_pid1 as controller


ROOT = Path(__file__).resolve().parents[1]


class TargetDriftAgentLifecycleTest(unittest.TestCase):
    def test_contract_requires_pid1_and_records_nonclaims(self) -> None:
        contract = json.loads((
            ROOT / "evaluation/target-drift-v2/agent-sandbox-contract.json"
        ).read_text(encoding="utf-8"))
        self.assertEqual(contract["suite_id"], "ABRL-TARGET-DRIFT-V2")
        self.assertIn("PID 1", contract["controller"]["pid_namespace_requirement"])
        self.assertIn("--init is forbidden", contract["controller"][
            "pid_namespace_requirement"
        ])
        self.assertEqual(contract["required_probe"]["id"],
                         "host_control_loss_reaps_pid_namespace_v1")
        self.assertTrue(any("model run" in text.lower()
                            for text in contract["production_nonclaims"]))

    def test_controller_fails_closed_outside_pid_namespace(self) -> None:
        if os.getpid() == 1:
            self.skipTest("test host unexpectedly runs the test process as PID 1")
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            with self.assertRaisesRegex(SystemExit, "requires Linux|must be PID 1"):
                controller.run_controller(
                    ["ignored"], root / "ready.json", root / "exit.json"
                )

    def test_atomic_json_is_lf_and_parseable(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "ledger.json"
            probe.dump_atomic(path, {"schema_version": 1, "status": "passed"})
            payload = path.read_bytes()
            self.assertNotIn(b"\r\n", payload)
            self.assertEqual(json.loads(payload)["status"], "passed")

    def test_containerfile_keeps_controller_as_pid1(self) -> None:
        recipe = (
            ROOT / "evaluation/target-drift-v2/agent-lifecycle.Containerfile"
        ).read_text(encoding="utf-8")
        self.assertIn('ENTRYPOINT ["python3", "/usr/local/bin/abrl-agent-pid1"]', recipe)
        self.assertNotIn("--init", recipe)
        self.assertIn("USER 65532:65532", recipe)

    def test_workflow_runs_the_crash_probe_without_secrets(self) -> None:
        workflow = (
            ROOT / ".github/workflows/target-drift-agent-lifecycle.yml"
        ).read_text(encoding="utf-8")
        self.assertIn("record_target_drift_agent_lifecycle_probe.py", workflow)
        self.assertIn("agent-lifecycle-probe.json", workflow)
        self.assertIn("python:3.11-slim-bookworm", workflow)
        self.assertNotIn("secrets.", workflow)
        self.assertIn("if: always()", workflow)


if __name__ == "__main__":
    unittest.main()
