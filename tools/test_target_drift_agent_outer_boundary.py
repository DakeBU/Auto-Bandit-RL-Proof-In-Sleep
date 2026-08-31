#!/usr/bin/env python3
"""Component tests for the result-free agent outer boundary."""

from __future__ import annotations

import contextlib
import ast
import hashlib
import io
import json
import errno
import os
import sys
import tempfile
import unittest
from pathlib import Path
from unittest import mock


import launch_target_drift_agent_container as launcher
import prepare_target_drift_agent_image as image_builder
import target_drift_agent_outer_controller as controller
import target_drift_agent_model_probe as model_probe
import target_drift_agent_outer_probe as worker_probe
import target_drift_agent_excluded_adapter as excluded_adapter


class AgentOuterBoundaryTest(unittest.TestCase):
    def test_workflow_supplies_canonical_fake_auth_basename(self) -> None:
        workflow = (
            launcher.ROOT / ".github" / "workflows" /
            "target-drift-agent-image.yml"
        ).read_text(encoding="utf-8")
        canonical = '${RUNNER_TEMP}/abrl-agent-outer-auth/auth.json'
        self.assertEqual(workflow.count(canonical), 3)
        self.assertNotIn(
            '${RUNNER_TEMP}/abrl-agent-outer-auth.json', workflow
        )

    def test_workflow_exercises_excluded_execute_without_provider_secret(self) -> None:
        workflow = (
            launcher.ROOT / ".github" / "workflows" /
            "target-drift-agent-image.yml"
        ).read_text(encoding="utf-8")
        self.assertEqual(workflow.count("--component-mode excluded-execute"), 1)
        self.assertIn(
            "evaluation/target-drift-v2/agent-excluded-execution-request.json",
            workflow,
        )
        self.assertIn("RESULT_FREE_SENTINEL_DO_NOT_USE", workflow)
        self.assertNotIn("secrets.", workflow)

    def test_canonical_command_has_fixed_root_and_worker_boundary(self) -> None:
        command = launcher.docker_command(
            Path("/usr/bin/docker"), "sha256:" + "a" * 64,
            Path("/host/input"), Path("/host/auth.json"),
            Path("/host/control"), "result-free-test",
        )
        self.assertEqual(command[:4], [
            str(Path("/usr/bin/docker")), "run", "--rm", "--pull",
        ])
        self.assertIn("--read-only", command)
        self.assertIn("--interactive", command)
        self.assertNotIn("--init", command)
        self.assertEqual(command.count("--cap-drop"), 1)
        self.assertIn("ALL", command)
        caps = {
            command[index + 1] for index, item in enumerate(command)
            if item == "--cap-add"
        }
        self.assertEqual(caps, {
            "SETUID", "SETGID", "CHOWN", "DAC_OVERRIDE", "FOWNER",
        })
        self.assertIn("apparmor=abrl-target-drift-codex", command)
        self.assertIn("no-new-privileges=true", command)
        self.assertIn("0:0", command)
        self.assertIn("ABRL_OUTER_COMPONENT_MODE=result_free_probe_v1", command)
        self.assertIn(
            f"type=bind,src={Path('/host/input')},dst=/input/agent,readonly",
            command,
        )
        self.assertIn(
            f"type=bind,src={Path('/host/auth.json')},"
            "dst=/run/secrets/provider-auth,readonly",
            command,
        )
        self.assertIn(
            f"type=bind,src={Path('/host/control')},dst=/control", command
        )
        self.assertIn(launcher.PID1, command)
        self.assertIn(launcher.OUTER_CONTROLLER, command)

    def test_excluded_execute_command_is_networkless_and_fixed(self) -> None:
        digest = "sha256:" + "b" * 64
        command = launcher.docker_command(
            Path("/usr/bin/docker"), digest, Path("/host/input"),
            Path("/host/auth.json"), Path("/host/control"),
            "result-free-execute-test", launcher.EXCLUDED_EXECUTE_MODE,
        )
        network = command.index("--network")
        self.assertEqual(command[network + 1], "none")
        self.assertIn(
            "ABRL_OUTER_COMPONENT_MODE=result_free_excluded_execute_v1", command
        )
        self.assertIn(f"ABRL_OUTER_COMPONENT_IMAGE_DIGEST={digest}", command)
        self.assertNotIn(launcher.EXCLUDED_ADAPTER, command)
        self.assertIn(launcher.PID1, command)
        self.assertIn(launcher.OUTER_CONTROLLER, command)

    def test_pid1_lifecycle_cross_binding_fails_closed(self) -> None:
        ready = {
            "controller_pid": 1,
            "child_pid": 17,
            "pid_namespace_requirement": "controller_is_pid_1",
        }
        exit_ledger = {"reason": "child_exited", "child_return_code": 0}
        report = {"controller_pid": 17, "controller_parent_pid": 1}
        launcher.validate_process_lifecycle(ready, exit_ledger, report)
        changed = dict(report, controller_pid=18)
        with self.assertRaises(SystemExit):
            launcher.validate_process_lifecycle(ready, exit_ledger, changed)
        changed_exit = dict(exit_ledger, child_return_code=125)
        with self.assertRaises(SystemExit):
            launcher.validate_process_lifecycle(ready, changed_exit, report)

    def test_launcher_accepts_only_fixed_fake_inputs(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory).resolve()
            agent = root / "agent"
            control = root / "control"
            agent.mkdir()
            control.mkdir()
            (agent / "input.txt").write_bytes(launcher.EXPECTED_INPUT)
            auth = root / "auth.json"
            auth.write_bytes(launcher.EXPECTED_AUTH)
            launcher.validate_inputs(agent, auth, control)
            auth.write_text("real-or-other-secret\n", encoding="utf-8")
            with self.assertRaises(SystemExit):
                launcher.validate_inputs(agent, auth, control)

    def test_launcher_accepts_only_the_tracked_excluded_request(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory).resolve()
            agent = root / "agent"
            control = root / "control"
            agent.mkdir()
            control.mkdir()
            request = agent / "request.json"
            request.write_bytes(launcher.CANONICAL_EXCLUDED_REQUEST.read_bytes())
            auth = root / "auth.json"
            auth.write_bytes(launcher.EXPECTED_AUTH)
            launcher.validate_inputs(
                agent, auth, control, launcher.EXCLUDED_EXECUTE_MODE
            )
            payload = json.loads(request.read_text(encoding="utf-8"))
            payload["provider_runtime"]["provider_execution_enabled"] = True
            request.write_text(json.dumps(payload) + "\n", encoding="utf-8")
            with self.assertRaises(SystemExit):
                launcher.validate_inputs(
                    agent, auth, control, launcher.EXCLUDED_EXECUTE_MODE
                )

    def test_controller_copies_only_single_regular_frozen_input(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            source = root / "source"
            target = root / "target"
            source.mkdir()
            payload = b"RESULT_FREE_AGENT_INPUT\n"
            (source / "input.txt").write_bytes(payload)
            records = controller.copy_agent_input(source, target)
            self.assertEqual(records, [{
                "path": "input.txt", "bytes": len(payload),
                "sha256": hashlib.sha256(payload).hexdigest(),
            }])
            self.assertEqual((target / "input.txt").read_bytes(), payload)

    def test_worker_failure_diagnostic_is_bounded_and_redacted(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            control = Path(directory)
            output = (
                b"prefix RESULT_FREE_SENTINEL_DO_NOT_USE "
                b"RESULT_FREE_AGENT_INPUT\n"
            )
            with contextlib.redirect_stderr(io.StringIO()):
                controller.persist_worker_failure(control, 17, output)
            payload = json.loads((
                control / "worker-probe-failure.json"
            ).read_text(encoding="utf-8"))
            self.assertEqual(payload["return_code"], 17)
            self.assertEqual(payload["stdout_bytes"], len(output))
            self.assertEqual(
                payload["stdout_sha256"], hashlib.sha256(output).hexdigest()
            )
            self.assertNotIn(
                "RESULT_FREE_SENTINEL_DO_NOT_USE",
                payload["diagnostic_tail"],
            )
            self.assertNotIn(
                "RESULT_FREE_AGENT_INPUT", payload["diagnostic_tail"]
            )

    def test_worker_consumes_and_closes_read_only_fake_auth_fd(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            auth = Path(directory) / "auth.json"
            auth.write_bytes(worker_probe.EXPECTED_AUTH)
            descriptor = os.open(auth, os.O_RDONLY)
            with mock.patch.dict(
                os.environ,
                {worker_probe.AUTH_FD_ENV: str(descriptor)},
                clear=False,
            ):
                handoff = worker_probe.consume_brokered_fake_auth()
                self.assertNotIn(worker_probe.AUTH_FD_ENV, os.environ)
            self.assertTrue(handoff["read_only_descriptor"])
            self.assertTrue(handoff["descriptor_closed_before_sandbox"])
            self.assertEqual(
                handoff["sha256"],
                hashlib.sha256(worker_probe.EXPECTED_AUTH).hexdigest(),
            )
            with self.assertRaises(OSError) as closed:
                os.fstat(descriptor)
            self.assertEqual(closed.exception.errno, errno.EBADF)

    def test_root_parent_closes_auth_fd_immediately_after_spawn(self) -> None:
        process = mock.Mock()
        process.returncode = 0
        close_observed: list[int] = []

        def communicate(*, timeout: int):
            self.assertEqual(timeout, 45)
            self.assertEqual(close_observed, [9])
            return b"worker-output", None

        process.communicate.side_effect = communicate
        with mock.patch.object(
            controller.subprocess, "Popen", return_value=process
        ) as popen, mock.patch.object(
            controller.os, "close", side_effect=close_observed.append
        ):
            outcome = controller.run_worker_with_brokered_auth(
                9, {controller.AUTH_FD_ENV: "9"}
            )
        self.assertEqual(outcome.returncode, 0)
        self.assertEqual(outcome.stdout, b"worker-output")
        self.assertEqual(popen.call_args.kwargs["pass_fds"], (9,))

    def test_sbom_must_bind_checked_out_outer_sources(self) -> None:
        payload = {
            "schema_version": 1,
            "suite_id": launcher.SUITE_ID,
            "status": "provider_client_image_built_probe_pending_results_absent",
            "container_image_digest": "sha256:" + "a" * 64,
            "controller_sha256": launcher.sha256(
                launcher.TOOLS / "target_drift_agent_pid1.py"
            ),
            "adapter_sha256": launcher.sha256(
                launcher.TOOLS / "codex_target_drift_adapter.py"
            ),
            "outer_controller_sha256": launcher.sha256(
                launcher.TOOLS / "target_drift_agent_outer_controller.py"
            ),
            "outer_probe_sha256": launcher.sha256(
                launcher.TOOLS / "target_drift_agent_outer_probe.py"
            ),
            "model_probe_sha256": launcher.sha256(
                launcher.TOOLS / "target_drift_agent_model_probe.py"
            ),
            "excluded_adapter_sha256": launcher.sha256(
                launcher.TOOLS / "target_drift_agent_excluded_adapter.py"
            ),
            "excluded_execution_contract_sha256": launcher.sha256(
                launcher.CANONICAL_EXCLUDED_CONTRACT
            ),
            "excluded_execution_request_sha256": launcher.sha256(
                launcher.CANONICAL_EXCLUDED_REQUEST
            ),
            "production_action_driver_sha256": launcher.sha256(
                launcher.TOOLS / "target_drift_agent_action_driver.py"
            ),
            "production_action_fake_provider_sha256": launcher.sha256(
                launcher.TOOLS / "target_drift_agent_fake_codex.py"
            ),
            "production_action_contract_sha256": launcher.sha256(
                launcher.CANONICAL_ACTION_CONTRACT
            ),
            "production_action_fixture_request_sha256": launcher.sha256(
                launcher.CANONICAL_ACTION_FIXTURE / "request.json"
            ),
        }
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory).resolve() / "sbom.json"
            path.write_text(json.dumps(payload) + "\n", encoding="utf-8")
            self.assertEqual(
                launcher.validate_sbom(path)["container_image_digest"],
                payload["container_image_digest"],
            )
            payload["outer_probe_sha256"] = "0" * 64
            path.write_text(json.dumps(payload) + "\n", encoding="utf-8")
            with self.assertRaises(SystemExit):
                launcher.validate_sbom(path)

    def test_controller_rejects_linked_input(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            source = root / "source"
            source.mkdir()
            external = root / "external"
            external.write_bytes(b"RESULT_FREE_AGENT_INPUT\n")
            link = source / "input.txt"
            try:
                link.symlink_to(external)
            except OSError:
                self.skipTest("symlinks unavailable")
            with self.assertRaises(SystemExit):
                controller.copy_agent_input(source, root / "target")

    def test_root_control_read_requires_permission_denial_not_absence(self) -> None:
        denied = mock.Mock()
        denied.read_bytes.side_effect = PermissionError(errno.EACCES, "denied")
        absent = mock.Mock()
        absent.read_bytes.side_effect = FileNotFoundError(errno.ENOENT, "absent")
        readable = mock.Mock()
        readable.read_bytes.return_value = b"visible"
        self.assertEqual(model_probe.read_denial_errno(denied), errno.EACCES)
        self.assertEqual(model_probe.read_denial_errno(absent), errno.ENOENT)
        self.assertIsNone(model_probe.read_denial_errno(readable))
        accepted = {errno.EACCES, errno.EPERM}
        self.assertIn(model_probe.read_denial_errno(denied), accepted)
        self.assertNotIn(model_probe.read_denial_errno(absent), accepted)

    def test_launcher_requires_the_exact_root_control_evidence_set(self) -> None:
        if os.name == "nt":
            self.skipTest("POSIX ownership and exact modes are unavailable")
        with tempfile.TemporaryDirectory() as directory:
            control = Path(directory).resolve()
            for name in launcher.CONTROL_EVIDENCE_NAMES:
                path = control / name
                path.write_text("evidence\n", encoding="utf-8")
                path.chmod(0o400 if name == "root-only-sentinel" else 0o644)
            evidence = launcher.validate_control_evidence(
                control, expected_uid=os.getuid(), expected_gid=os.getgid()
            )
            self.assertEqual(set(evidence), launcher.CONTROL_EVIDENCE_NAMES)
            undeclared = control / "undeclared.log"
            undeclared.write_text("must fail closed\n", encoding="utf-8")
            with self.assertRaises(SystemExit):
                launcher.validate_control_evidence(
                    control, expected_uid=os.getuid(), expected_gid=os.getgid()
                )

    def test_nested_capability_parser_requires_an_observed_hex_field(self) -> None:
        self.assertEqual(model_probe.parse_effective_capabilities(
            "Name:\tpython3\nCapEff:\t0000000000000000\n"
        ), "0000000000000000")
        with self.assertRaises(SystemExit):
            model_probe.parse_effective_capabilities("Name:\tpython3\n")
        with self.assertRaises(ValueError):
            model_probe.parse_effective_capabilities("CapEff:\tnot-hex\n")

    def test_worker_transition_clears_groups_before_uid(self) -> None:
        calls: list[tuple[str, object]] = []
        with mock.patch.object(controller.os, "setgroups", create=True,
                               side_effect=lambda value: calls.append(("groups", value))), \
             mock.patch.object(controller.os, "setgid", create=True,
                               side_effect=lambda value: calls.append(("gid", value))), \
             mock.patch.object(controller.os, "setuid", create=True,
                               side_effect=lambda value: calls.append(("uid", value))), \
             mock.patch.object(controller.os, "umask",
                               side_effect=lambda value: calls.append(("umask", value))):
            controller.drop_worker()
        self.assertEqual(calls, [
            ("groups", []), ("gid", 10002), ("uid", 10002), ("umask", 0o077),
        ])

    def test_image_context_and_sbom_bind_all_outer_components(self) -> None:
        self.assertEqual(
            image_builder.CONTEXT_INPUTS["target_drift_agent_outer_controller.py"],
            image_builder.TOOLS / "target_drift_agent_outer_controller.py",
        )
        self.assertEqual(
            image_builder.CONTEXT_INPUTS["target_drift_agent_outer_probe.py"],
            image_builder.TOOLS / "target_drift_agent_outer_probe.py",
        )
        self.assertEqual(
            image_builder.CONTEXT_INPUTS["target_drift_agent_model_probe.py"],
            image_builder.TOOLS / "target_drift_agent_model_probe.py",
        )
        self.assertEqual(
            image_builder.CONTEXT_INPUTS[
                "target_drift_agent_excluded_adapter.py"
            ],
            image_builder.TOOLS / "target_drift_agent_excluded_adapter.py",
        )
        self.assertEqual(
            image_builder.CONTEXT_INPUTS["target_drift_agent_action_driver.py"],
            image_builder.TOOLS / "target_drift_agent_action_driver.py",
        )
        self.assertEqual(
            image_builder.CONTEXT_INPUTS["target_drift_agent_fake_codex.py"],
            image_builder.TOOLS / "target_drift_agent_fake_codex.py",
        )
        self.assertEqual(
            image_builder.CONTEXT_INPUTS["agent-production-action-contract.json"],
            image_builder.ROOT
            / "evaluation/target-drift-v2/agent-production-action-contract.json",
        )

    def test_excluded_adapter_has_no_provider_network_or_process_escape(self) -> None:
        source = (launcher.TOOLS / "target_drift_agent_excluded_adapter.py").read_text(
            encoding="utf-8"
        )
        tree = ast.parse(source)
        imported = set()
        for node in ast.walk(tree):
            if isinstance(node, ast.Import):
                imported.update(alias.name.split(".")[0] for alias in node.names)
            elif isinstance(node, ast.ImportFrom) and node.module:
                imported.add(node.module.split(".")[0])
        blocked_import_roots = {
            "ftplib", "http", "requests", "socket", "ssl", "subprocess",
            "telnetlib", "urllib", "webbrowser",
        }
        self.assertTrue(blocked_import_roots.isdisjoint(imported))
        blocked_os_calls = []
        for node in ast.walk(tree):
            if not isinstance(node, ast.Call):
                continue
            function = node.func
            if (
                isinstance(function, ast.Attribute)
                and isinstance(function.value, ast.Name)
                and function.value.id == "os"
                and (
                    function.attr in {"popen", "system"}
                    or function.attr.startswith("exec")
                    or function.attr.startswith("spawn")
                )
            ):
                blocked_os_calls.append(function.attr)
        self.assertEqual(blocked_os_calls, [])

    def test_excluded_contract_hashes_and_primary_status_fail_closed(self) -> None:
        contract = controller.load_excluded_contract(
            launcher.CANONICAL_EXCLUDED_CONTRACT,
            launcher.TOOLS / "target_drift_agent_excluded_adapter.py",
        )
        self.assertEqual(
            contract["execution_status_boundary"],
            "primary_execution_not_started",
        )
        self.assertFalse(contract["primary_result_eligible"])
        protocol = json.loads((
            launcher.ROOT / "evaluation/target-drift-v2/protocol.json"
        ).read_text(encoding="utf-8"))
        self.assertTrue(protocol["execution_status"].endswith("execution_not_started"))
        with tempfile.TemporaryDirectory() as directory:
            changed_adapter = Path(directory) / "adapter.py"
            changed_adapter.write_bytes(
                (launcher.TOOLS / "target_drift_agent_excluded_adapter.py").read_bytes()
                + b"\n# drift\n"
            )
            with self.assertRaises(SystemExit):
                controller.load_excluded_contract(
                    launcher.CANONICAL_EXCLUDED_CONTRACT, changed_adapter
                )

    def test_excluded_adapter_round_trip_is_zero_usage_and_result_ineligible(self) -> None:
        contract = json.loads(
            launcher.CANONICAL_EXCLUDED_CONTRACT.read_text(encoding="utf-8")
        )
        request_payload = launcher.CANONICAL_EXCLUDED_REQUEST.read_bytes()
        request = json.loads(request_payload.decode("utf-8"))
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory).resolve()
            agent = root / "agent"
            agent.mkdir()
            request_path = agent / "request.json"
            request_path.write_bytes(request_payload)
            auth = root / "auth.json"
            auth.write_bytes(excluded_adapter.EXPECTED_AUTH)
            descriptor = os.open(auth, os.O_RDONLY)
            response = agent / "adapter/response.json"
            trace = agent / "adapter/trace.jsonl"
            argv = [
                "target_drift_agent_excluded_adapter.py",
                "--request", str(request_path),
                "--response", str(response),
                "--trace", str(trace),
                "--agent-mount", str(agent),
                "--adapter-id", "abrl-agent-excluded-component",
                "--adapter-version", "1",
                "--model-id", "excluded-provider-no-model",
                "--immutable-model-version", "excluded-provider-no-model",
                "--image-digest", "sha256:" + "c" * 64,
                "--budget-attestation", "zero-provider-zero-model-zero-cost",
                "--isolation-attestation",
                "network-none-fixed-fake-auth-result-ineligible",
                "--request-sha256", hashlib.sha256(request_payload).hexdigest(),
            ]
            stdout = io.StringIO()
            try:
                with mock.patch.object(sys, "argv", argv), mock.patch.object(
                         excluded_adapter, "read_denial_errno",
                         return_value=errno.EACCES
                     ), mock.patch.dict(os.environ, {
                         excluded_adapter.AUTH_FD_ENV: str(descriptor),
                         "ABRL_OUTER_COMPONENT_MODE": excluded_adapter.EXPECTED_MODE,
                     }, clear=False), contextlib.redirect_stdout(stdout):
                    excluded_adapter.main()
            finally:
                try:
                    os.close(descriptor)
                except OSError:
                    pass
            evidence = controller.validate_excluded_execution_artifacts(
                agent, contract, request, stdout.getvalue().encode("utf-8")
            )
            self.assertFalse(evidence["primary_result_eligible"])
            self.assertFalse(evidence["provider_execution_enabled"])
            self.assertEqual(
                evidence["adapter_response"]["usage"]["cost_usd"], 0.0
            )
            trace.write_text("{}\n", encoding="utf-8")
            with self.assertRaises(SystemExit):
                controller.validate_excluded_execution_artifacts(
                    agent, contract, request, stdout.getvalue().encode("utf-8")
                )


if __name__ == "__main__":
    unittest.main()
