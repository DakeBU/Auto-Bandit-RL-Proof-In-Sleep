#!/usr/bin/env python3
"""Fixed offline Codex-JSONL fixture for the agent production-action candidate.

This executable is deliberately not a provider client.  It accepts only the
exact command shape emitted by ``codex_target_drift_adapter.py``, writes one
blocked, result-ineligible fixture result, and emits a deterministic zero-usage
Codex event stream.  It imports no network or subprocess client and must never
be used in a smoke, primary run, grade, or analysis ledger.
"""

from __future__ import annotations

import json
import sys
from pathlib import Path


EXPECTED_AGENT_TEXT = "/agent/run"
EXPECTED_AGENT = Path(EXPECTED_AGENT_TEXT)
EXPECTED_MODEL = "abrl-fixed-offline-provider-fixture"
DISABLED_FEATURES = (
    "apps", "artifact", "auth_elicitation", "browser_use", "browser_use_external",
    "builtin_mcp", "computer_use", "default_mode_request_user_input",
    "enable_fanout", "enable_mcp_apps", "goals", "image_generation",
    "hooks", "in_app_browser", "memories", "multi_agent", "multi_agent_v2",
    "plugin_hooks", "plugins", "request_permissions_tool",
    "remote_plugin", "skill_mcp_dependency_install", "tool_call_mcp_elicitation",
    "shell_snapshot", "tool_search", "tool_search_always_defer_mcp_tools",
    "tool_suggest", "workspace_dependencies",
)


def require(condition: bool, message: str) -> None:
    if not condition:
        raise SystemExit(f"target-drift fixed fake Codex failed: {message}")


def expected_arguments() -> list[str]:
    arguments = [
        "exec", "--ignore-user-config", "--ignore-rules", "--ephemeral",
        "--json", "--color", "never", "--sandbox", "workspace-write",
        "--skip-git-repo-check", "--cd", EXPECTED_AGENT_TEXT,
        "--model", EXPECTED_MODEL,
        "--config", 'model_reasoning_effort="low"',
        "--config", 'service_tier="priority"',
        "--config", 'web_search="disabled"',
        "--config", "sandbox_workspace_write.network_access=false",
        "--config", 'shell_environment_policy.inherit="none"',
        "--config", "shell_environment_policy.ignore_default_excludes=false",
        "--config", "allow_login_shell=false",
        "--config", "skills.include_instructions=false",
        "--config", 'shell_environment_policy.set.LANG="C.UTF-8"',
        "--config", (
            'shell_environment_policy.set.PATH="/usr/local/bin:/usr/bin:/bin"'
        ),
    ]
    for feature in DISABLED_FEATURES:
        arguments.extend(["--disable", feature])
    arguments.append("-")
    return arguments


def write_new_json(path: Path, value: object) -> None:
    require(path.parent.is_dir() and not path.parent.is_symlink(),
            "output parent is not a plain directory")
    with path.open("x", encoding="utf-8", newline="\n") as stream:
        json.dump(value, stream, indent=2, sort_keys=True)
        stream.write("\n")


def main() -> None:
    arguments = sys.argv[1:]
    require(arguments == expected_arguments(),
            "Codex argv differs from the fixed fixture")
    prompt = sys.stdin.read()
    require("ABRL_FIXED_PRODUCTION_ACTION_FIXTURE" in prompt,
            "fixture prompt marker is absent")

    output = EXPECTED_AGENT / "output"
    output.mkdir(mode=0o700)
    write_new_json(output / "result.json", {
        "schema_version": 1,
        "opaque_run_id": "result-free-production-action-fixture",
        "final_status": "blocked",
        "public_declarations": [],
        "primary_grader_rationale": (
            "Fixed offline provider fixture only; no model, provider, or Lean "
            "formalization outcome was attempted."
        ),
    })
    with (output / "explanation.md").open(
        "x", encoding="utf-8", newline="\n"
    ) as stream:
        stream.write(
            "Permanent result-ineligible production-action fixture; no model result.\n"
        )

    events = [
        {"type": "thread.started", "thread_id": "offline-fixture-thread"},
        {"type": "turn.started"},
        {
            "type": "item.completed",
            "item": {
                "type": "agent_message",
                "text": "Fixed offline production-action fixture completed.",
            },
        },
        {
            "type": "turn.completed",
            "usage": {
                "input_tokens": 0,
                "cached_input_tokens": 0,
                "cache_write_input_tokens": 0,
                "output_tokens": 0,
                "reasoning_output_tokens": 0,
            },
        },
    ]
    for event in events:
        print(json.dumps(event, sort_keys=True, separators=(",", ":")), flush=True)


if __name__ == "__main__":
    main()
