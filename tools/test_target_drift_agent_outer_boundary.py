#!/usr/bin/env python3
"""Component tests for the result-free agent outer boundary."""

from __future__ import annotations

import hashlib
import json
import errno
import os
import tempfile
import unittest
from pathlib import Path
from unittest import mock


import launch_target_drift_agent_container as launcher
import prepare_target_drift_agent_image as image_builder
import target_drift_agent_outer_controller as controller
import target_drift_agent_model_probe as model_probe


class AgentOuterBoundaryTest(unittest.TestCase):
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

    def test_sbom_must_bind_checked_out_outer_sources(self) -> None:
        payload = {
            "schema_version": 1,
            "suite_id": launcher.SUITE_ID,
            "status": "provider_client_image_built_probe_pending_results_absent",
            "container_image_digest": "sha256:" + "a" * 64,
            "controller_sha256": launcher.sha256(
                launcher.TOOLS / "target_drift_agent_pid1.py"
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


if __name__ == "__main__":
    unittest.main()
