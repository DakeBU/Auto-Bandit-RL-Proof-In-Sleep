#!/usr/bin/env python3
"""Deterministic tests for the result-free Codex CLI adapter candidate."""

from __future__ import annotations

import hashlib
import json
import os
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path


TOOLS = Path(__file__).resolve().parent
sys.path.insert(0, str(TOOLS))

import codex_target_drift_adapter as adapter  # noqa: E402


def jsonl(events: list[dict]) -> str:
    return "".join(json.dumps(event) + "\n" for event in events)


class CodexTargetDriftAdapterTest(unittest.TestCase):
    def test_observable_thread_and_usage_are_not_called_provider_requests(self) -> None:
        parsed = adapter.parse_codex_jsonl(jsonl([
            {"type": "thread.started", "thread_id": "thread-visible"},
            {"type": "turn.started"},
            {"type": "item.completed", "item": {
                "id": "item-0", "type": "agent_message", "text": "done",
            }},
            {"type": "turn.completed", "usage": {
                "input_tokens": 100, "cached_input_tokens": 25,
                "cache_write_input_tokens": 10,
                "output_tokens": 20, "reasoning_output_tokens": 5,
            }},
        ]), attempt=1)
        self.assertEqual(parsed["thread_id"], "thread-visible")
        self.assertTrue(parsed["turn_completed"])
        self.assertEqual(parsed["usage"]["cached_input_tokens"], 25)
        self.assertEqual(parsed["events"], [])
        invocation = adapter.model_invocation(1, parsed["thread_id"], 0, 1.25, True)
        self.assertEqual(invocation["observable_id_kind"], "codex_thread")
        self.assertNotIn("provider_request", json.dumps(invocation))

    def test_failed_build_starts_recovery_and_preserves_observable_output(self) -> None:
        parsed = adapter.parse_codex_jsonl(jsonl([
            {"type": "thread.started", "thread_id": "thread-build"},
            {"type": "turn.started"},
            {"type": "item.completed", "item": {
                "id": "item-0", "type": "command_execution",
                "command": ["lake", "build"], "aggregated_output": "failed\n",
                "exit_code": 1, "status": "failed",
            }},
            {"type": "item.completed", "item": {
                "id": "item-1", "type": "command_execution",
                "command": "rg theorem", "aggregated_output": "found\n",
                "exit_code": 0, "status": "completed",
            }},
            {"type": "turn.completed", "usage": {
                "input_tokens": 10, "cached_input_tokens": 0,
                "cache_write_input_tokens": 0,
                "output_tokens": 5, "reasoning_output_tokens": 1,
            }},
        ]), attempt=1)
        self.assertEqual(
            [event["kind"] for event in parsed["events"]],
            ["tool_call", "build_attempt", "tool_call"],
        )
        self.assertFalse(parsed["events"][0]["recovery_phase"])
        self.assertFalse(parsed["events"][1]["success"])
        self.assertTrue(parsed["events"][2]["recovery_phase"])
        self.assertIn("failed", parsed["build_log"])

    def test_unknown_observable_event_fails_closed(self) -> None:
        with self.assertRaises(SystemExit):
            adapter.parse_codex_jsonl(
                jsonl([{"type": "provider.magic", "secret": "not observable"}]),
                attempt=1,
            )

    def test_terminal_usage_requires_cache_write_field(self) -> None:
        with self.assertRaises(SystemExit):
            adapter.parse_codex_jsonl(jsonl([{
                "type": "turn.completed", "usage": {
                    "input_tokens": 1, "cached_input_tokens": 0,
                    "output_tokens": 1, "reasoning_output_tokens": 0,
                },
            }]), attempt=1)

    def test_updates_and_forbidden_or_error_items_are_parsed_fail_closed(self) -> None:
        parsed = adapter.parse_codex_jsonl(jsonl([
            {"type": "thread.started", "thread_id": "thread-policy"},
            {"type": "item.updated", "item": {
                "id": "todo", "type": "todo_list", "items": [],
            }},
            {"type": "item.completed", "item": {
                "id": "collab", "type": "collab_tool_call", "status": "completed",
            }},
            {"type": "item.completed", "item": {
                "id": "error", "type": "error", "message": "observable failure",
            }},
        ]), attempt=1)
        self.assertEqual(parsed["policy_violations"], ["collab_tool_call"])
        self.assertTrue(parsed["runtime_failure"])
        self.assertEqual(
            [event["kind"] for event in parsed["events"]],
            ["forbidden_tool_call", "runtime_error"],
        )

    def test_forbidden_or_error_updates_fail_closed_before_completion(self) -> None:
        parsed = adapter.parse_codex_jsonl(jsonl([
            {"type": "thread.started", "thread_id": "thread-policy-update"},
            {"type": "item.updated", "item": {
                "id": "collab", "type": "collab_tool_call", "status": "in_progress",
            }},
            {"type": "item.updated", "item": {
                "id": "error", "type": "error", "message": "observable failure",
            }},
            {"type": "turn.completed", "usage": {
                "input_tokens": 1, "cached_input_tokens": 0,
                "cache_write_input_tokens": 0, "output_tokens": 1,
                "reasoning_output_tokens": 0,
            }},
        ]), attempt=1)
        self.assertEqual(parsed["policy_violations"], ["collab_tool_call"])
        self.assertTrue(parsed["runtime_failure"])

    def test_two_build_commands_in_one_item_fail_closed_as_ambiguous(self) -> None:
        parsed = adapter.parse_codex_jsonl(jsonl([{
            "type": "item.completed", "item": {
                "id": "builds", "type": "command_execution",
                "command": "lake build A; lake env lean B.lean",
                "aggregated_output": "", "exit_code": 0, "status": "completed",
            },
        }]), attempt=1)
        self.assertEqual(parsed["policy_violations"], ["ambiguous_multi_build_command"])
        self.assertEqual(
            [event["kind"] for event in parsed["events"]],
            ["tool_call", "ambiguous_build_accounting"],
        )
        self.assertIn(
            "ambiguous_build_accounting",
            adapter.CODEX_INFRASTRUCTURE_FAILURE_DEFINITION,
        )

    def test_mentioned_build_text_is_not_counted_as_an_observed_build(self) -> None:
        parsed = adapter.parse_codex_jsonl(jsonl([{
            "type": "item.completed", "item": {
                "id": "mention", "type": "command_execution",
                "command": "echo lake build BanditRLProof",
                "aggregated_output": "lake build BanditRLProof\n",
                "exit_code": 0, "status": "completed",
            },
        }]), attempt=1)
        self.assertEqual(
            [event["kind"] for event in parsed["events"]],
            ["tool_call"],
        )
        self.assertEqual(parsed["build_log"], "")

    def test_turn_completed_is_unique_and_terminal(self) -> None:
        terminal = {"type": "turn.completed", "usage": {
            "input_tokens": 1, "cached_input_tokens": 0,
            "cache_write_input_tokens": 0, "output_tokens": 1,
            "reasoning_output_tokens": 0,
        }}
        with self.assertRaises(SystemExit):
            adapter.parse_codex_jsonl(jsonl([terminal, terminal]), attempt=1)
        with self.assertRaises(SystemExit):
            adapter.parse_codex_jsonl(jsonl([
                terminal,
                {"type": "item.completed", "item": {
                    "id": "late", "type": "agent_message", "text": "late",
                }},
            ]), attempt=1)

    def test_cost_uses_frozen_uncached_cached_and_output_rates(self) -> None:
        usage = {
            "input_tokens": 100, "cached_input_tokens": 40,
            "cache_write_input_tokens": 10,
            "output_tokens": 20, "reasoning_output_tokens": 5,
        }
        pricing = {
            "input_tokens": 10.0, "cached_input_tokens": 2.5,
            "cache_write_input_tokens": 12.5,
            "output_tokens": 30.0,
        }
        self.assertEqual(adapter.calculate_cost(usage, pricing), 0.001325)

    def test_lean_patch_is_exact_for_modified_new_and_deleted_files(self) -> None:
        patch = adapter.lean_patch(
            {"A.lean": "old\n", "Deleted.lean": "gone\n"},
            {"A.lean": "new\n", "New.lean": "fresh\n"},
        )
        self.assertIn("--- a/A.lean", patch)
        self.assertIn("+++ b/A.lean", patch)
        self.assertIn("--- a/Deleted.lean", patch)
        self.assertIn("+++ /dev/null", patch)
        self.assertIn("--- /dev/null", patch)
        self.assertIn("+++ b/New.lean", patch)

    def test_codex_command_binds_runtime_model_reasoning_tier_and_agent_root(self) -> None:
        executable = Path(sys.executable).resolve()
        request = {
            "provider_runtime": {
                "kind": "codex_cli", "executable": str(executable),
                "executable_sha256": hashlib.sha256(executable.read_bytes()).hexdigest(),
                "shell_environment": {"PATH": "frozen-path"},
            },
            "model": {
                "model_id": "frozen-model", "reasoning_effort": "high",
                "service_tier": "fast",
            },
        }
        agent = Path.cwd().resolve()
        command = adapter.codex_command(request, agent)
        self.assertEqual(command[0], str(executable))
        self.assertIn("--ignore-user-config", command)
        self.assertIn("--ignore-rules", command)
        self.assertIn("--ephemeral", command)
        self.assertIn("workspace-write", command)
        self.assertIn('model_reasoning_effort="high"', command)
        self.assertIn('service_tier="fast"', command)
        self.assertIn('web_search="disabled"', command)
        self.assertIn("allow_login_shell=false", command)
        self.assertIn("shell_snapshot", command)
        for feature in adapter.DISABLED_CODEX_FEATURES:
            self.assertIn(feature, command)
        self.assertNotIn("--search", command)
        self.assertIn("shell_environment_policy.inherit=\"none\"", command)
        self.assertEqual(command[-1], "-")

    def test_adapter_owned_write_rejects_a_hardlink_before_protected_input_damage(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            prompt = root / "prompt.md"
            prompt.write_text("protected\n", encoding="utf-8")
            target = root / "lean-diff.patch"
            os.link(prompt, target)
            with self.assertRaises(SystemExit):
                adapter.write_new_text(target, "malicious overwrite\n", "lean-diff.patch")
            self.assertEqual(prompt.read_text(encoding="utf-8"), "protected\n")

    def test_main_records_provider_process_failure_with_matching_terminal_result(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            agent = root / "agent"
            workspace = agent / "workspace"
            output = agent / "output"
            adapter_dir = root / "adapter"
            codex_home = root / "codex-home"
            workspace.mkdir(parents=True)
            output.mkdir()
            adapter_dir.mkdir()
            codex_home.mkdir()
            (workspace / "A.lean").write_text("def a := 1\n", encoding="utf-8")
            (agent / "prompt.md").write_text("Implement the target.\n", encoding="utf-8")
            (codex_home / "auth.json").write_text("{}\n", encoding="utf-8")
            runtime = Path(sys.executable).resolve()
            request = {
                "opaque_run_id": "RUN-INTEGRATION", "replicate": 0,
                "agent_mount": str(agent.resolve()),
                "prompt_path": str((agent / "prompt.md").resolve()),
                "model": {"model_id": "frozen", "reasoning_effort": "high",
                          "service_tier": "fast"},
                "pricing": {"input_tokens": 1.0, "cached_input_tokens": 0.5,
                            "cache_write_input_tokens": 1.25,
                            "output_tokens": 2.0},
                "budgets": {"maximum_model_retries": 0},
                "retry_policy": {"semantic_failure_retries": 0,
                                 "infrastructure_retry_limit": 0,
                                 "infrastructure_failure_definition": (
                                     adapter.CODEX_INFRASTRUCTURE_FAILURE_DEFINITION
                                 )},
                "result_contract": {
                    "agent_output_directory": "output",
                    "required_files": ["result.json", "explanation.md", "lean-diff.patch",
                                       "build.log", "workflow-compliance.json"],
                    "optional_files": [], "result_required_fields": ["final_status"],
                    "workflow_evidence_files": [], "workflow_id": "neutral",
                    "blind_grading_text_rule": "Use neutral mathematical language.",
                },
                "provider_runtime": {
                    "kind": "codex_cli", "executable": str(runtime),
                    "executable_sha256": hashlib.sha256(runtime.read_bytes()).hexdigest(),
                    "auth_source_path": str(codex_home.resolve()),
                    "process_environment": {},
                    "shell_environment": {"PATH": os.environ.get("PATH", ".")},
                },
            }
            request_path = root / "request.json"
            request_path.write_text(json.dumps(request), encoding="utf-8")
            response_path = adapter_dir / "response.json"
            trace_path = adapter_dir / "trace.jsonl"
            process = subprocess.run([
                sys.executable, str(TOOLS / "codex_target_drift_adapter.py"),
                "--request", str(request_path), "--response", str(response_path),
                "--trace", str(trace_path), "--agent-mount", str(agent),
                "--adapter-id", "candidate", "--adapter-version", "test",
                "--model-id", "frozen", "--immutable-model-version", "operator-attested",
                "--image-digest", "sha256:" + "a" * 64,
                "--budget-attestation", "test budget",
                "--isolation-attestation", "test isolation",
            ], stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True, check=False)
            self.assertEqual(process.returncode, 0, process.stderr)
            response = json.loads(response_path.read_text(encoding="utf-8"))
            result = json.loads((output / "result.json").read_text(encoding="utf-8"))
            self.assertEqual(response["termination"], "infrastructure_failure")
            self.assertEqual(result["final_status"], "infrastructure_failure")
            self.assertFalse(response["model_invocations"][0]["usage_observed"])
            self.assertNotEqual(response["model_invocations"][0]["process_exit_code"], 0)
            self.assertTrue(
                (adapter_dir / "provider-attempt-001.stdout.jsonl").is_file()
            )
            self.assertTrue(
                (adapter_dir / "provider-attempt-001.stderr.log").is_file()
            )


if __name__ == "__main__":
    unittest.main()
