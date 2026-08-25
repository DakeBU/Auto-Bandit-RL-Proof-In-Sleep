#!/usr/bin/env python3
"""Tests for the result-free LeanFlow real-adapter preflight."""

from __future__ import annotations

import ast
import copy
import hashlib
import json
import subprocess
import sys
import tempfile
import unittest
from contextlib import redirect_stderr
from io import StringIO
from pathlib import Path
from types import SimpleNamespace
from unittest import mock


ROOT = Path(__file__).resolve().parents[1]
TOOLS = ROOT / "tools"
CONTRACT = ROOT / "evaluation" / "target-drift-v2" / "leanflow-real-adapter-contract.json"
sys.path.insert(0, str(TOOLS))

import leanflow_target_drift_adapter as adapter  # noqa: E402


def sha256(value: bytes) -> str:
    return hashlib.sha256(value).hexdigest()


class LeanFlowResultFreePreflightTests(unittest.TestCase):
    def load_contract(self) -> dict:
        return json.loads(CONTRACT.read_text(encoding="utf-8"))

    def materialize_synthetic_source(self, root: Path) -> tuple[dict, Path]:
        contract = copy.deepcopy(self.load_contract())
        source_root = root / "leanflow-source"
        source_root.mkdir()
        contents = {
            "pyproject.toml": (
                b"[project]\n"
                b'name = "leanflow-agent"\n'
                b'version = "0.3.0"\n'
                b'requires-python = ">=3.11"\n\n'
                b"[project.scripts]\n"
                b'leanflow = "leanflow_cli.main:main"\n'
                b'leanflow-agent = "leanflow_agent:main"\n'
            ),
            "uv.lock": b"synthetic-lock\n",
            "README.md": b"synthetic readme\n",
            "core/toolsets.py": b"# synthetic pinned toolset evidence\n",
            "leanflow_cli/workflow.py": b"# synthetic pinned workflow evidence\n",
            "tests/leanflow/test_workflow_swarm.py": b"# synthetic pinned policy test\n",
            "LICENSE": b"Apache License 2.0 synthetic fixture\n",
        }
        pinned = []
        for relative, value in contents.items():
            path = source_root.joinpath(*relative.split("/"))
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_bytes(value)
            pinned.append({"path": relative, "bytes": len(value), "sha256": sha256(value)})
        (source_root / ".git").mkdir()
        source = contract["source_identity"]
        source["repository_commit"] = "1" * 40
        source["repository_tree_sha1"] = "2" * 40
        source["pinned_files"] = pinned
        source["lock_sha256"] = next(
            item["sha256"] for item in pinned if item["path"] == "uv.lock"
        )
        contract_path = root / "contract.json"
        contract_path.write_text(
            json.dumps(contract, indent=2, sort_keys=True) + "\n", encoding="utf-8",
        )
        return contract, source_root

    @staticmethod
    def fake_identity(contract: dict) -> dict:
        source = contract["source_identity"]
        return {
            "repository_commit": source["repository_commit"],
            "repository_tree_sha1": source["repository_tree_sha1"],
            "git_executable_sha256": "3" * 64,
            "local_git_probe_count": 2,
        }

    def test_repository_contract_pins_source_and_keeps_production_closed(self) -> None:
        contract = self.load_contract()
        adapter.validate_contract(contract)
        source = contract["source_identity"]
        self.assertEqual(
            source["repository_commit"],
            "72a58a5ffe3d26710e8e0a5d0f4e9bcaab3fed4d",
        )
        self.assertEqual(source["repository_tree_sha1"], "5db00ff277884f8df1f0379b4f1418abcd32f31c")
        self.assertEqual(source["project_version"], "0.3.0")
        self.assertEqual(
            source["lock_sha256"],
            "1239513509ee29a580c3f3f293e86dd16f77c298dbe9a99cba6aaaf93a1b0dd5",
        )
        clean_room = contract["clean_room_audit"]
        self.assertFalse(clean_room["no_web_overlay_frozen"])
        self.assertFalse(clean_room["provider_only_network_containment_frozen"])
        self.assertFalse(clean_room["production_requirement_satisfied"])
        self.assertFalse(contract["preflight_capability"]["execution_enabled"])
        self.assertFalse(contract["preflight_capability"]["result_eligible"])
        self.assertFalse(contract["preflight_capability"]["local_git_executable_pre_frozen"])
        self.assertFalse(contract["preflight_capability"]["os_network_isolation_attested"])

    def test_preflight_validates_synthetic_pins_but_emits_no_result(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            contract, source_root = self.materialize_synthetic_source(root)
            response_path = root / "response.json"
            trace_path = root / "trace.jsonl"
            response = adapter.run_preflight(
                root / "contract.json",
                source_root,
                response_path,
                trace_path,
                git_identity_probe=lambda unused: self.fake_identity(contract),
            )
            self.assertEqual(response["status"], "result_free_preflight_completed")
            for field in (
                "result_eligible", "production_eligible", "adapter_provider_client_called",
                "adapter_started_leanflow", "adapter_credential_read_path_present",
                "adapter_network_client_path_present", "local_git_executable_pre_frozen",
                "os_network_isolation_attested",
                "formalization_outcome_reported", "production_gate_passed",
            ):
                self.assertFalse(response[field], field)
            self.assertEqual(response["local_preflight"]["model_invocations"], 0)
            self.assertFalse(response["local_preflight"]["git_executable_pre_frozen"])
            self.assertFalse(response["local_preflight"]["git_os_level_behavior_attested"])
            self.assertFalse(response["gates"]["no_web_overlay_frozen"])
            self.assertFalse(response["gates"]["os_network_isolation_attested"])
            self.assertFalse(response["gates"]["production_execution_enabled"])
            on_disk = json.loads(response_path.read_text(encoding="utf-8"))
            self.assertEqual(on_disk, response)
            events = [json.loads(line) for line in trace_path.read_text(
                encoding="utf-8",
            ).splitlines()]
            self.assertEqual([event["kind"] for event in events], adapter.EXPECTED_TRACE_KINDS)
            self.assertFalse(events[-1]["result_eligible"])
            self.assertFalse(events[-1]["formalization_outcome_reported"])
            self.assertNotIn("credentials_read", response)
            self.assertNotIn("network_used", response)
            self.assertNotIn("credentials_read", events[-1])
            self.assertNotIn("network_used", events[-1])

    def test_execute_mode_fails_before_contract_source_or_output_access(self) -> None:
        stderr = StringIO()
        with mock.patch.object(adapter, "load_regular_object") as load_contract, \
                mock.patch.object(adapter, "local_git_identity") as git_identity, \
                mock.patch.object(adapter.subprocess, "run") as process_run, \
                redirect_stderr(stderr):
            code = adapter.main(["--mode", "execute"])
        self.assertEqual(code, 2)
        self.assertIn("execute is disabled", stderr.getvalue())
        load_contract.assert_not_called()
        git_identity.assert_not_called()
        process_run.assert_not_called()

    def test_source_hash_drift_fails_without_outputs(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            contract, source_root = self.materialize_synthetic_source(root)
            (source_root / "uv.lock").write_bytes(b"drifted\n")
            response = root / "response.json"
            trace = root / "trace.jsonl"
            with self.assertRaisesRegex(adapter.PreflightError, "byte length differs"):
                adapter.run_preflight(
                    root / "contract.json", source_root, response, trace,
                    git_identity_probe=lambda unused: self.fake_identity(contract),
                )
            self.assertFalse(response.exists())
            self.assertFalse(trace.exists())

    def test_safety_flags_and_unknown_contract_fields_fail_closed(self) -> None:
        contract = self.load_contract()
        for path, value in (
            (("preflight_capability", "execution_enabled"), True),
            (("clean_room_audit", "production_requirement_satisfied"), True),
            (("response_schema", "result_eligible"), True),
        ):
            mutated = copy.deepcopy(contract)
            mutated[path[0]][path[1]] = value
            with self.subTest(path=path):
                with self.assertRaises(adapter.PreflightError):
                    adapter.validate_contract(mutated)
        mutated = copy.deepcopy(contract)
        mutated["unexpected"] = "field"
        with self.assertRaisesRegex(adapter.PreflightError, "contract fields differ"):
            adapter.validate_contract(mutated)

    def test_audit_text_and_nested_schema_fail_closed(self) -> None:
        contract = self.load_contract()
        mutations = (
            ("purpose", None, "weakened-purpose"),
            ("clean_room_audit", "facts", ["weakened fact"] * 4),
            ("unmet_production_gates", None, ["weakened blocker"] * 6),
            ("nonclaims", None, ["claim"] * 6),
        )
        for field, nested, value in mutations:
            mutated = copy.deepcopy(contract)
            if nested is None:
                mutated[field] = value
            else:
                mutated[field][nested] = value
            with self.subTest(field=field, nested=nested):
                with self.assertRaises(adapter.PreflightError):
                    adapter.validate_contract(mutated)

        mutated = copy.deepcopy(contract)
        mutated["clean_room_audit"]["result"] = "invented"
        with self.assertRaises(adapter.PreflightError):
            adapter.validate_contract(mutated)

    def test_production_output_name_is_rejected_before_git_probe(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            unused_contract, source_root = self.materialize_synthetic_source(root)
            probe = mock.Mock()
            with self.assertRaisesRegex(adapter.PreflightError, "production output basename"):
                adapter.run_preflight(
                    root / "contract.json",
                    source_root,
                    root / "external-comparator-results.json",
                    root / "trace.jsonl",
                    git_identity_probe=probe,
                )
            probe.assert_not_called()

    def test_preexisting_output_is_not_overwritten(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            contract, source_root = self.materialize_synthetic_source(root)
            response = root / "response.json"
            response.write_text("sentinel", encoding="utf-8")
            with self.assertRaisesRegex(adapter.PreflightError, "refusing to overwrite"):
                adapter.run_preflight(
                    root / "contract.json", source_root, response, root / "trace.jsonl",
                    git_identity_probe=lambda unused: self.fake_identity(contract),
                )
            self.assertEqual(response.read_text(encoding="utf-8"), "sentinel")

    def test_local_git_identity_uses_only_two_local_rev_parse_probes(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            (root / ".git").mkdir()
            git = root / ("git.exe" if sys.platform == "win32" else "git")
            git.write_bytes(b"synthetic-git-binary")
            returns = [
                SimpleNamespace(returncode=0, stdout="1" * 40 + "\n", stderr=""),
                SimpleNamespace(returncode=0, stdout="2" * 40 + "\n", stderr=""),
            ]
            with mock.patch.object(adapter.shutil, "which", return_value=str(git)), \
                    mock.patch.object(adapter.subprocess, "run", side_effect=returns) as run:
                identity = adapter.local_git_identity(root)
            self.assertEqual(identity["repository_commit"], "1" * 40)
            self.assertEqual(identity["repository_tree_sha1"], "2" * 40)
            self.assertEqual(identity["local_git_probe_count"], 2)
            self.assertEqual(run.call_count, 2)
            for index, call in enumerate(run.call_args_list):
                argv = call.args[0]
                self.assertEqual(tuple(argv[-3:]), adapter.EXPECTED_GIT_PROBES[index])
                self.assertNotIn("clone", argv)
                self.assertNotIn("fetch", argv)
                env = call.kwargs["env"]
                self.assertEqual(env["GIT_TERMINAL_PROMPT"], "0")
                self.assertEqual(env["GIT_NO_LAZY_FETCH"], "1")
                self.assertFalse(any(
                    key.endswith("_API_KEY") or key.endswith("_TOKEN")
                    for key in env
                ))

    def test_nonallowlisted_git_probe_is_rejected_without_subprocess(self) -> None:
        with tempfile.TemporaryDirectory() as tmp, \
                mock.patch.object(adapter.subprocess, "run") as run:
            root = Path(tmp)
            git = root / "git.exe"
            git.write_bytes(b"git")
            with self.assertRaisesRegex(adapter.PreflightError, "non-allowlisted"):
                adapter._run_git_probe(git, root, ("fetch", "origin"))
            run.assert_not_called()

    def test_adapter_has_no_provider_or_network_client_import(self) -> None:
        source = (TOOLS / "leanflow_target_drift_adapter.py").read_text(encoding="utf-8")
        tree = ast.parse(source)
        imports = set()
        for node in ast.walk(tree):
            if isinstance(node, ast.Import):
                imports.update(alias.name.split(".", 1)[0] for alias in node.names)
            elif isinstance(node, ast.ImportFrom) and node.module:
                imports.add(node.module.split(".", 1)[0])
        self.assertFalse(imports & {
            "anthropic", "httpx", "openai", "requests", "socket", "urllib",
        })
        self.assertEqual(source.count("subprocess.run("), 1)


if __name__ == "__main__":
    unittest.main()
