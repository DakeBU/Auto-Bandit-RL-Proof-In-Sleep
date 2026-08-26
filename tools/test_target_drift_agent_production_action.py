#!/usr/bin/env python3
"""Result-free tests for the closed production-action interface candidate."""

from __future__ import annotations

import ast
import hashlib
import json
import os
import sys
import tempfile
import unittest
from pathlib import Path
from unittest import mock

import codex_target_drift_adapter as codex_adapter
import launch_target_drift_agent_container as launcher
import target_drift_agent_action_driver as driver
import target_drift_agent_fake_codex as fake_codex
import target_drift_agent_outer_controller as controller


class TargetDriftAgentProductionActionTest(unittest.TestCase):
    def contract(self) -> dict:
        return launcher.load_action_contract()

    def final_seal(self) -> dict:
        return {
            "schema_version": 1,
            "suite_id": launcher.SUITE_ID,
            "status": "sealed_final_production_agent_action",
            "production_execution_enabled": True,
            "primary_result_eligible": True,
            "orchestrator_commit": "a" * 40,
            "image": {
                "digest": "sha256:" + "b" * 64,
                "sbom_sha256": "c" * 64,
                "sbom_status": "sealed_final_production_agent_image",
            },
            "runtime": {
                "kind": "docker",
                "executable_sha256": "d" * 64,
                "identity_sha256": "e" * 64,
            },
            "config": {
                "status": "sealed_final_execution_config",
                "sha256": "f" * 64,
            },
            "provider": {
                "kind": "codex_cli",
                "fixture_provider": False,
                "single_file_credential_boundary": True,
                "model_shell_network_access": False,
                "egress_policy": "provider_only_allowlist_enforced",
            },
            "probes": {
                "image_probe_status": "passed_final_agent_image_probe",
                "image_probe_sha256": "1" * 64,
                "lifecycle_probe_status": "passed_final_pid1_lifecycle_probe",
                "lifecycle_probe_sha256": "2" * 64,
                "credential_visibility_probe_status": (
                    "passed_real_credential_visibility_no_secret_digest"
                ),
                "credential_visibility_probe_sha256": "3" * 64,
                "provider_egress_probe_status": "passed_provider_only_egress_probe",
                "provider_egress_probe_sha256": "4" * 64,
                "real_smoke_status": (
                    "passed_result_ineligible_real_three_condition_smoke"
                ),
                "real_smoke_ledger_sha256": "5" * 64,
            },
            "request": {
                "status": "sealed_production_run_input",
                "manifest_sha256": "6" * 64,
            },
        }

    def test_contract_binds_real_adapter_fixed_driver_and_fake_provider(self) -> None:
        contract = self.contract()
        self.assertFalse(contract["production_execution_enabled"])
        self.assertEqual(contract["production_gate"]["decision"], "closed")
        fixture = contract["fixture"]
        bindings = {
            "driver": launcher.TOOLS / "target_drift_agent_action_driver.py",
            "adapter": launcher.TOOLS / "codex_target_drift_adapter.py",
            "fake_provider": launcher.TOOLS / "target_drift_agent_fake_codex.py",
        }
        for name, path in bindings.items():
            self.assertEqual(fixture[name]["sha256"], launcher.sha256(path))
        self.assertEqual(
            fixture["request_sha256"],
            launcher.sha256(launcher.CANONICAL_ACTION_FIXTURE / "request.json"),
        )
        self.assertIn(
            "/usr/local/lib/abrl/codex_target_drift_adapter.py",
            (launcher.TOOLS / "target_drift_agent_action_driver.py").read_text(
                encoding="utf-8"
            ),
        )

    def test_fixture_input_is_exact_and_tamper_fails_before_docker(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory).resolve()
            agent = root / "agent"
            control = root / "control"
            agent.mkdir()
            control.mkdir()
            for source in launcher.CANONICAL_ACTION_FIXTURE.rglob("*"):
                relative = source.relative_to(launcher.CANONICAL_ACTION_FIXTURE)
                target = agent / relative
                if source.is_dir():
                    target.mkdir(parents=True, exist_ok=True)
                else:
                    target.parent.mkdir(parents=True, exist_ok=True)
                    target.write_bytes(source.read_bytes())
            auth = root / "auth.json"
            auth.write_bytes(launcher.EXPECTED_AUTH)
            launcher.validate_inputs(
                agent, auth, control, launcher.PRODUCTION_FIXTURE_MODE
            )
            (agent / "prompt.md").write_text("tampered\n", encoding="utf-8")
            with self.assertRaises(SystemExit):
                launcher.validate_inputs(
                    agent, auth, control, launcher.PRODUCTION_FIXTURE_MODE
                )
            (agent / "prompt.md").write_bytes(
                (launcher.CANONICAL_ACTION_FIXTURE / "prompt.md").read_bytes()
            )
            (agent / "unsealed-empty-directory").mkdir()
            with self.assertRaises(SystemExit):
                launcher.validate_inputs(
                    agent, auth, control, launcher.PRODUCTION_FIXTURE_MODE
                )

    def test_fixture_docker_command_keeps_pid1_network_none_and_copyback(self) -> None:
        digest = "sha256:" + "7" * 64
        command = launcher.docker_command(
            Path("/usr/bin/docker"), digest, Path("/host/input"),
            Path("/host/auth.json"), Path("/host/control"), "fixture-test",
            launcher.PRODUCTION_FIXTURE_MODE, Path("/host/artifacts"),
        )
        self.assertEqual(command[command.index("--network") + 1], "none")
        self.assertNotIn("--init", command)
        self.assertIn(launcher.PID1, command)
        self.assertIn(launcher.OUTER_CONTROLLER, command)
        self.assertNotIn(launcher.ACTION_DRIVER, command)
        self.assertNotIn(launcher.FAKE_CODEX, command)
        self.assertIn(
            "ABRL_OUTER_COMPONENT_MODE=result_free_production_action_fixture_v1",
            command,
        )
        self.assertIn(
            f"type=bind,src={Path('/host/artifacts')},dst=/artifacts", command
        )

    def test_final_seal_schema_rejects_candidate_fake_and_unsealed_values(self) -> None:
        contract = self.contract()
        seal = self.final_seal()
        self.assertIs(
            launcher.validate_production_seal_structure(seal, contract), seal
        )
        for value in (
            "candidate_agent_image", "fixed_fake_provider", "UNSET",
            "unsealed_runtime", "result-free-only",
        ):
            changed = json.loads(json.dumps(seal))
            changed["config"]["status"] = value
            with self.assertRaises(SystemExit):
                launcher.validate_production_seal_structure(changed, contract)
        changed = json.loads(json.dumps(seal))
        changed["image"]["digest"] = "latest"
        with self.assertRaises(SystemExit):
            launcher.validate_production_seal_structure(changed, contract)

    def test_valid_final_seal_still_cannot_open_checked_in_gate(self) -> None:
        contract = self.contract()
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory).resolve() / "seal.json"
            path.write_text(json.dumps(self.final_seal()) + "\n", encoding="utf-8")
            with self.assertRaisesRegex(SystemExit, "production action gate is closed"):
                launcher.reject_closed_production_execution(path, contract)

    def test_production_main_stops_before_auth_or_docker_even_if_data_gate_opens(
        self,
    ) -> None:
        contract = self.contract()
        contract["production_execution_enabled"] = True
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory).resolve()
            seal = root / "seal.json"
            seal.write_text(json.dumps(self.final_seal()) + "\n", encoding="utf-8")
            arguments = [
                "launch_target_drift_agent_container.py",
                "--component-mode", launcher.PRODUCTION_EXECUTE_MODE,
                "--production-seal", str(seal),
                "--image-sbom", str(root / "not-read-sbom.json"),
                "--agent-input", str(root / "not-read-input"),
                "--auth-sentinel", str(root / "not-read-auth.json"),
                "--control-output", str(root / "not-read-control"),
                "--apparmor-source", str(root / "not-read.apparmor"),
                "--report", str(root / "not-written-report.json"),
                "--probe-commit", "a" * 40,
            ]
            with mock.patch.object(
                launcher, "load_action_contract", return_value=contract
            ):
                with mock.patch.object(sys, "argv", arguments):
                    with mock.patch.object(
                        launcher.checker_launcher,
                        "canonical_docker_executable",
                    ) as docker_lookup:
                        with self.assertRaisesRegex(
                            SystemExit,
                            "production controller implementation is intentionally absent",
                        ):
                            launcher.main()
            docker_lookup.assert_not_called()
            self.assertFalse((root / "not-read-auth.json").exists())
            self.assertFalse((root / "not-written-report.json").exists())

    def test_driver_consumes_one_read_only_fake_auth_file_and_removes_marker(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory).resolve()
            source = root / "auth.json"
            source.write_bytes(driver.EXPECTED_AUTH)
            descriptor = os.open(source, os.O_RDONLY)
            target = root / "provider-auth"
            with mock.patch.dict(
                os.environ, {driver.AUTH_FD_ENV: str(descriptor)}, clear=False
            ):
                handoff = driver.consume_fake_auth(target)
                self.assertNotIn(driver.AUTH_FD_ENV, os.environ)
            self.assertTrue(handoff["descriptor_closed_before_adapter_launch"])
            self.assertEqual(
                handoff["sha256"], hashlib.sha256(driver.EXPECTED_AUTH).hexdigest()
            )
            self.assertEqual((target / "auth.json").read_bytes(), driver.EXPECTED_AUTH)
            driver.remove_auth_tree(target)
            self.assertFalse(target.exists())

    def test_fake_provider_has_no_network_or_subprocess_import(self) -> None:
        path = launcher.TOOLS / "target_drift_agent_fake_codex.py"
        tree = ast.parse(path.read_text(encoding="utf-8"))
        imported = set()
        for node in ast.walk(tree):
            if isinstance(node, ast.Import):
                imported.update(alias.name.split(".")[0] for alias in node.names)
            elif isinstance(node, ast.ImportFrom) and node.module:
                imported.add(node.module.split(".")[0])
        self.assertTrue({
            "ftplib", "http", "requests", "socket", "ssl", "subprocess",
            "telnetlib", "urllib", "webbrowser",
        }.isdisjoint(imported))
        arguments = fake_codex.expected_arguments()
        self.assertIn("sandbox_workspace_write.network_access=false", arguments)
        request = json.loads(
            (launcher.CANONICAL_ACTION_FIXTURE / "request.json").read_text(
                encoding="utf-8"
            )
        )
        request["provider_runtime"]["executable"] = str(path.resolve())
        request["provider_runtime"]["executable_sha256"] = launcher.sha256(path)
        adapter_arguments = codex_adapter.codex_command(
            request, Path("/agent/run")
        )[1:]
        adapter_arguments[adapter_arguments.index("--cd") + 1] = "/agent/run"
        self.assertEqual(adapter_arguments, arguments)
        unexpected_arguments = fake_codex.expected_arguments()
        unexpected_arguments.insert(-1, "--unexpected")
        with mock.patch.object(
            sys, "argv", [str(path), *unexpected_arguments]
        ):
            with self.assertRaisesRegex(SystemExit, "Codex argv differs"):
                fake_codex.main()

    def test_controller_copies_only_the_sealed_fixture_tree(self) -> None:
        contract = controller.load_action_contract(
            launcher.CANONICAL_ACTION_CONTRACT,
            launcher.TOOLS / "target_drift_agent_action_driver.py",
            launcher.TOOLS / "codex_target_drift_adapter.py",
            launcher.TOOLS / "target_drift_agent_fake_codex.py",
        )
        with tempfile.TemporaryDirectory() as directory:
            target = Path(directory).resolve() / "run"
            records = controller.copy_action_fixture(
                launcher.CANONICAL_ACTION_FIXTURE, target, contract
            )
            self.assertEqual(records, contract["fixture"]["input_manifest"])
            self.assertEqual(
                (target / "request.json").read_bytes(),
                (launcher.CANONICAL_ACTION_FIXTURE / "request.json").read_bytes(),
            )

    def test_host_copyback_validator_hashes_receipt_and_every_artifact(self) -> None:
        contract = self.contract()
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory).resolve()
            records = []
            for group, names in (
                ("adapter", contract["fixture"]["required_adapter_files"]),
                ("output", contract["fixture"]["required_output_files"]),
            ):
                target = root / group
                target.mkdir()
                for name in sorted(names):
                    path = target / name
                    payload = f"fixture:{group}/{name}\n".encode("utf-8")
                    path.write_bytes(payload)
                    path.chmod(0o444)
                    records.append({
                        "path": f"{group}/{name}",
                        "bytes": len(payload),
                        "sha256": hashlib.sha256(payload).hexdigest(),
                    })
            receipt = {
                "schema_version": 1,
                "suite_id": launcher.SUITE_ID,
                "status": "copied_result_free_production_action_fixture",
                "primary_result_eligible": False,
                "provider_execution_enabled": False,
                "provider_request_or_model_invocation_occurred": False,
                "source_request_sha256": contract["fixture"]["request_sha256"],
                "copied_files": records,
            }
            receipt_path = root / "copyback-receipt.json"
            receipt_path.write_text(json.dumps(receipt) + "\n", encoding="utf-8")
            receipt_path.chmod(0o444)
            report = {"copyback_evidence": {
                "copyback_manifest": records,
                "copyback_receipt_status": receipt["status"],
                "copyback_receipt_sha256": launcher.sha256(receipt_path),
            }}
            info = receipt_path.stat()
            launcher.validate_action_copyback(
                root, report, contract,
                expected_uid=info.st_uid, expected_gid=info.st_gid,
            )
            tampered = root / "output/result.json"
            tampered.chmod(0o644)
            tampered.write_text("tampered\n", encoding="utf-8")
            tampered.chmod(0o444)
            with self.assertRaises(SystemExit):
                launcher.validate_action_copyback(
                    root, report, contract,
                    expected_uid=info.st_uid, expected_gid=info.st_gid,
                )


if __name__ == "__main__":
    unittest.main()
