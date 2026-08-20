#!/usr/bin/env python3
"""Result-free Codex CLI adapter candidate for target-drift runs.

This adapter translates observable ``codex exec --json`` events into the
frozen target-drift trace.  It is not a production-isolation claim: eligibility
still requires the separately frozen agent image, filesystem/network/process
probe, cache, and real-infrastructure smoke specified by the protocol.
"""

from __future__ import annotations

import argparse
import difflib
import hashlib
import json
import os
import re
import shutil
import stat
import subprocess
import tempfile
import time
from pathlib import Path
from typing import Any


BUILD_COMMAND = re.compile(
    r"(?:^\s*|(?:&&|\|\||;|[\r\n])\s*)"
    r"lake(?:\.exe)?\s+(?:build|env\s+lean)(?:\s|$)",
    re.I,
)
PERMITTED_TOOL_ITEM_TYPES = {"command_execution", "file_change"}
FORBIDDEN_TOOL_ITEM_TYPES = {"mcp_tool_call", "collab_tool_call", "web_search"}
NON_TOOL_ITEM_TYPES = {"agent_message", "reasoning", "todo_list", "error"}
KNOWN_ITEM_TYPES = PERMITTED_TOOL_ITEM_TYPES | FORBIDDEN_TOOL_ITEM_TYPES | NON_TOOL_ITEM_TYPES
DISABLED_CODEX_FEATURES = (
    "apps", "artifact", "auth_elicitation", "browser_use", "browser_use_external",
    "builtin_mcp", "computer_use", "default_mode_request_user_input",
    "enable_fanout", "enable_mcp_apps", "goals", "image_generation",
    "hooks", "in_app_browser", "memories", "multi_agent", "multi_agent_v2",
    "plugin_hooks", "plugins", "request_permissions_tool",
    "remote_plugin", "skill_mcp_dependency_install", "tool_call_mcp_elicitation",
    "shell_snapshot",
    "tool_search", "tool_search_always_defer_mcp_tools", "tool_suggest",
    "workspace_dependencies",
)
SAFE_ENVIRONMENT_NAMES = {
    "LANG", "LC_ALL", "PATH", "SYSTEMROOT", "SystemRoot", "TEMP", "TMP",
}
CODEX_INFRASTRUCTURE_FAILURE_DEFINITION = (
    "codex_cli_nonzero_exit_or_missing_thread_or_missing_terminal_usage_or_"
    "runtime_error_or_forbidden_tool_or_ambiguous_build_accounting"
)


def require(condition: bool, message: str) -> None:
    if not condition:
        raise SystemExit(f"codex target-drift adapter failed: {message}")


def load(path: Path) -> dict[str, Any]:
    return json.loads(path.read_text(encoding="utf-8"))


def path_lexists(path: Path) -> bool:
    return os.path.lexists(str(path))


def write_new_text(path: Path, text: str, label: str) -> None:
    require_plain_directory(path.parent, f"{label} parent directory")
    require(not path_lexists(path), f"{label} already exists")
    with path.open("x", encoding="utf-8", newline="\n") as stream:
        stream.write(text)


def write_new_bytes(path: Path, payload: bytes, label: str) -> None:
    require_plain_directory(path.parent, f"{label} parent directory")
    require(not path_lexists(path), f"{label} already exists")
    with path.open("xb") as stream:
        stream.write(payload)


def dump_new(path: Path, value: Any, label: str) -> None:
    write_new_text(
        path,
        json.dumps(value, indent=2, sort_keys=True, ensure_ascii=False) + "\n",
        label,
    )


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def is_reparse(path: Path) -> bool:
    attributes = getattr(path.lstat(), "st_file_attributes", 0)
    return bool(attributes & getattr(stat, "FILE_ATTRIBUTE_REPARSE_POINT", 0x400))


def require_plain_directory(path: Path, label: str) -> None:
    require(path.is_dir() and not path.is_symlink() and not is_reparse(path),
            f"{label} is not a plain directory")


def require_plain_file(path: Path, label: str) -> None:
    metadata = path.lstat()
    require(stat.S_ISREG(metadata.st_mode) and not path.is_symlink()
            and not is_reparse(path) and metadata.st_nlink == 1,
            f"{label} is not a single-linked regular file")


def model_invocation(
    attempt: int, thread_id: str | None, process_exit_code: int,
    wall_seconds: float, usage_observed: bool,
) -> dict[str, Any]:
    return {
        "attempt": attempt,
        "transport": "codex_cli",
        "observable_id_kind": "codex_thread" if thread_id else "none",
        "observable_id": thread_id,
        "process_exit_code": process_exit_code,
        "wall_seconds": round(wall_seconds, 6),
        "usage_observed": usage_observed,
    }


def calculate_cost(usage: dict[str, int | float], pricing: dict[str, Any]) -> float:
    require(int(usage["cached_input_tokens"]) + int(usage["cache_write_input_tokens"])
            <= int(usage["input_tokens"]),
            "cache-read plus cache-write tokens exceed total input tokens")
    return round((
        (int(usage["input_tokens"]) - int(usage["cached_input_tokens"])
         - int(usage["cache_write_input_tokens"]))
        * float(pricing["input_tokens"])
        + int(usage["cached_input_tokens"]) * float(pricing["cached_input_tokens"])
        + int(usage["cache_write_input_tokens"])
        * float(pricing["cache_write_input_tokens"])
        + int(usage["output_tokens"]) * float(pricing["output_tokens"])
    ) / 1_000_000, 12)


def validated_environment(value: Any, label: str) -> dict[str, str]:
    require(isinstance(value, dict), f"{label} must be an object")
    result: dict[str, str] = {}
    seen: set[str] = set()
    for name, content in value.items():
        require(isinstance(name, str) and name in SAFE_ENVIRONMENT_NAMES,
                f"{label} contains a non-allowlisted variable")
        require(name.lower() not in seen, f"{label} repeats a variable by case")
        require(isinstance(content, str) and bool(content),
                f"{label}.{name} must be a nonempty string")
        seen.add(name.lower())
        result[name] = content
    return result


def require_auth_only_codex_home(path: Path) -> Path:
    require(path.is_absolute(), "provider auth source is not absolute")
    require(path.resolve() == path, "provider auth source path is not canonical")
    require_plain_directory(path, "provider auth source")
    entries = list(path.iterdir())
    require({entry.name for entry in entries} == {"auth.json"},
            "provider auth source must contain only auth.json")
    require_plain_file(path / "auth.json", "provider auth source auth.json")
    return path


def materialize_fresh_codex_home(request: dict[str, Any], codex_home: Path) -> Path:
    provider = request["provider_runtime"]
    source = require_auth_only_codex_home(Path(provider["auth_source_path"]))
    require_plain_directory(codex_home, "fresh provider CODEX_HOME")
    shutil.copyfile(source / "auth.json", codex_home / "auth.json")
    require_plain_file(codex_home / "auth.json", "fresh provider auth.json")
    return codex_home


def codex_process_environment(
    request: dict[str, Any], codex_home: Path
) -> dict[str, str]:
    provider = request["provider_runtime"]
    environment = validated_environment(
        provider["process_environment"], "provider process_environment"
    )
    environment["CODEX_HOME"] = str(codex_home)
    return environment


def codex_command(request: dict[str, Any], agent: Path) -> list[str]:
    provider = request["provider_runtime"]
    model = request["model"]
    require(provider["kind"] == "codex_cli", "provider runtime kind is not codex_cli")
    executable = Path(provider["executable"])
    require(executable.is_absolute() and executable.is_file() and not executable.is_symlink(),
            "provider runtime is not an absolute regular executable")
    require(sha256(executable) == provider["executable_sha256"],
            "provider runtime bytes differ from the frozen hash")
    command = [
        str(executable), "exec", "--ignore-user-config", "--ignore-rules",
        "--ephemeral", "--json", "--color", "never", "--sandbox",
        "workspace-write", "--skip-git-repo-check", "--cd", str(agent),
        "--model", model["model_id"],
        "--config", f"model_reasoning_effort={json.dumps(model['reasoning_effort'])}",
        "--config", f"service_tier={json.dumps(model['service_tier'])}",
        "--config", 'web_search="disabled"',
        "--config", "sandbox_workspace_write.network_access=false",
        "--config", 'shell_environment_policy.inherit="none"',
        "--config", "shell_environment_policy.ignore_default_excludes=false",
        "--config", "allow_login_shell=false",
        "--config", "skills.include_instructions=false",
    ]
    shell_environment = validated_environment(
        provider["shell_environment"], "provider shell_environment"
    )
    require("path" in {name.lower() for name in shell_environment},
            "provider shell_environment must freeze PATH")
    for name, value in sorted(shell_environment.items()):
        command.extend([
            "--config", f"shell_environment_policy.set.{name}={json.dumps(value)}",
        ])
    for feature in DISABLED_CODEX_FEATURES:
        command.extend(["--disable", feature])
    command.append("-")
    return command


def result_contract_text(contract: dict[str, Any]) -> str:
    return (
        "\n\nMachine-readable completion contract (applies equally in every condition):\n"
        f"- Write outputs only under: {contract['agent_output_directory']}\n"
        f"- Required files: {', '.join(contract['required_files'])}\n"
        f"- Optional files: {', '.join(contract['optional_files']) or '(none)'}\n"
        "- result.json must contain exactly the requested semantic fields, including "
        f"{', '.join(contract['result_required_fields'])}.\n"
        f"- Condition-specific evidence files: "
        f"{', '.join(contract['workflow_evidence_files']) or '(none)'}.\n"
        f"- Blind grading rule: {contract['blind_grading_text_rule']}\n"
        "- The adapter, not the model, creates lean-diff.patch, build.log, and "
        "workflow-compliance.json. Do not create or link those three files.\n"
        "Do not invent a declaration, successful build, evidence file, provider request, "
        "token count, or source amendment. Missing work must be reported as partial.\n"
    )


def lean_snapshot(workspace: Path) -> dict[str, str]:
    snapshot: dict[str, str] = {}
    require_plain_directory(workspace, "workspace root")
    for current_text, directories, files in os.walk(workspace, followlinks=False):
        current = Path(current_text)
        require_plain_directory(current, "workspace directory")
        if ".lake" in current.relative_to(workspace).parts:
            directories[:] = []
            continue
        for directory in list(directories):
            require_plain_directory(current / directory, "workspace child directory")
        for name in files:
            if not name.endswith(".lean"):
                continue
            path = current / name
            require_plain_file(path, "Lean source")
            snapshot[path.relative_to(workspace).as_posix()] = path.read_text(
                encoding="utf-8"
            )
    return snapshot


def lean_patch(before: dict[str, str], after: dict[str, str]) -> str:
    chunks: list[str] = []
    for relative in sorted(set(before) | set(after)):
        old = before.get(relative)
        new = after.get(relative)
        if old == new:
            continue
        chunks.extend(difflib.unified_diff(
            [] if old is None else old.splitlines(keepends=True),
            [] if new is None else new.splitlines(keepends=True),
            fromfile="/dev/null" if old is None else f"a/{relative}",
            tofile="/dev/null" if new is None else f"b/{relative}",
        ))
    return "".join(chunks)


def parse_codex_jsonl(
    text: str, attempt: int, recovery_initial: bool = False
) -> dict[str, Any]:
    raw: list[dict[str, Any]] = []
    normalized: list[dict[str, Any]] = []
    build_records: list[str] = []
    thread_id: str | None = None
    recovery = recovery_initial
    usage = {
        "input_tokens": 0, "cached_input_tokens": 0, "cache_write_input_tokens": 0,
        "output_tokens": 0, "reasoning_output_tokens": 0,
    }
    turn_completed = False
    runtime_failure = False
    policy_violations: list[str] = []
    for line_number, line in enumerate(text.splitlines(), 1):
        require(not turn_completed,
                "Codex emitted an event after terminal turn.completed")
        require(line.strip(), f"blank Codex JSONL line {line_number}")
        try:
            event = json.loads(line)
        except json.JSONDecodeError as error:
            raise SystemExit(
                f"codex target-drift adapter failed: invalid Codex JSONL line "
                f"{line_number}: {error}"
            ) from error
        require(isinstance(event, dict) and isinstance(event.get("type"), str),
                f"Codex event {line_number} has no type")
        raw.append(event)
        event_type = event["type"]
        if event_type == "thread.started":
            candidate = event.get("thread_id")
            require(isinstance(candidate, str) and candidate,
                    "thread.started lacks a thread_id")
            require(thread_id is None, "one Codex invocation exposed multiple thread IDs")
            thread_id = candidate
        elif event_type == "turn.completed":
            observed = event.get("usage")
            require(isinstance(observed, dict), "turn.completed lacks usage")
            for field in usage:
                require(field in observed,
                        f"turn.completed usage omits required field {field}")
                value = observed[field]
                require(isinstance(value, int) and not isinstance(value, bool) and value >= 0,
                        f"Codex usage {field} is not a nonnegative integer")
                usage[field] += value
            turn_completed = True
        elif event_type in {"item.started", "item.updated", "item.completed"}:
            item = event.get("item")
            require(isinstance(item, dict) and isinstance(item.get("type"), str),
                    f"{event_type} lacks a typed item")
            item_type = item["type"]
            require(item_type in KNOWN_ITEM_TYPES,
                    f"unsupported observable Codex item type: {item_type}")
            if item_type in FORBIDDEN_TOOL_ITEM_TYPES:
                policy_violations.append(item_type)
            elif item_type == "error":
                runtime_failure = True
            if event_type != "item.completed":
                continue
            if item_type in PERMITTED_TOOL_ITEM_TYPES:
                command_value = item.get("command", "") if item_type == "command_execution" else ""
                command = (
                    " ".join(str(part) for part in command_value)
                    if isinstance(command_value, list) else str(command_value)
                )
                status = item.get("status")
                exit_code = item.get("exit_code")
                success = (
                    exit_code == 0 if isinstance(exit_code, int)
                    else status in {"completed", "success"}
                )
                normalized.append({
                    "kind": "tool_call", "recovery_phase": recovery,
                    "tool_type": item_type, "success": bool(success),
                })
                build_matches = (
                    list(BUILD_COMMAND.finditer(str(command)))
                    if item_type == "command_execution" else []
                )
                if len(build_matches) > 1:
                    policy_violations.append("ambiguous_multi_build_command")
                    normalized.append({
                        "kind": "ambiguous_build_accounting", "success": False,
                        "command_sha256": hashlib.sha256(command.encode("utf-8")).hexdigest(),
                    })
                elif build_matches:
                    normalized.append({
                        "kind": "build_attempt", "success": bool(success),
                        "command_sha256": hashlib.sha256(command.encode("utf-8")).hexdigest(),
                    })
                if build_matches:
                    build_records.append(
                        f"$ {command}\n{item.get('aggregated_output', '')}\n"
                        f"[exit_code={exit_code!r}; status={status!r}]\n"
                    )
                    if not success:
                        recovery = True
            elif item_type in FORBIDDEN_TOOL_ITEM_TYPES:
                normalized.append({
                    "kind": "forbidden_tool_call", "tool_type": item_type,
                    "success": False,
                })
            elif item_type == "error":
                normalized.append({"kind": "runtime_error"})
        elif event_type in {"error", "turn.failed"}:
            runtime_failure = True
            normalized.append({"kind": "runtime_error"})
        elif event_type != "turn.started":
            require(False, f"unsupported observable Codex event type: {event_type}")
    return {
        "attempt": attempt,
        "raw": raw,
        "events": normalized,
        "thread_id": thread_id,
        "usage": usage,
        "build_log": "".join(build_records),
        "turn_completed": turn_completed,
        "recovery": recovery,
        "runtime_failure": runtime_failure,
        "policy_violations": sorted(set(policy_violations)),
    }


def restore_agent(agent: Path, baseline: Path) -> None:
    shutil.rmtree(agent)
    shutil.copytree(baseline, agent, symlinks=True)


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--request", type=Path, required=True)
    parser.add_argument("--response", type=Path, required=True)
    parser.add_argument("--trace", type=Path, required=True)
    parser.add_argument("--agent-mount", type=Path, required=True)
    parser.add_argument("--adapter-id", required=True)
    parser.add_argument("--adapter-version", required=True)
    parser.add_argument("--model-id", required=True)
    parser.add_argument("--immutable-model-version", required=True)
    parser.add_argument("--image-digest", required=True)
    parser.add_argument("--budget-attestation", required=True)
    parser.add_argument("--isolation-attestation", required=True)
    args = parser.parse_args()

    request = load(args.request)
    agent = args.agent_mount.resolve()
    require(Path(request["agent_mount"]).resolve() == agent,
            "request agent mount differs from argv")
    require(request["model"]["model_id"] == args.model_id,
            "request model differs from argv")
    prompt = Path(request["prompt_path"]).read_text(encoding="utf-8")
    prompt += result_contract_text(request["result_contract"])
    require(request["retry_policy"]["semantic_failure_retries"] == 0,
            "Codex CLI candidate does not perform semantic retries")
    require(request["retry_policy"]["infrastructure_retry_limit"] == 0,
            "Codex CLI candidate does not perform automatic infrastructure retries")
    require(request["budgets"]["maximum_model_retries"] == 0,
            "Codex CLI candidate requires a zero model-retry budget")
    require(request["retry_policy"]["infrastructure_failure_definition"]
            == CODEX_INFRASTRUCTURE_FAILURE_DEFINITION,
            "Codex CLI infrastructure-failure definition differs from the adapter")
    workspace = agent / "workspace"
    before = lean_snapshot(workspace)
    output = agent / "output"
    started = time.monotonic()
    all_events: list[dict[str, Any]] = []
    raw_records: list[dict[str, Any]] = []
    invocations: list[dict[str, Any]] = []
    build_logs: list[str] = []
    aggregate = {
        "input_tokens": 0, "cached_input_tokens": 0, "cache_write_input_tokens": 0,
        "output_tokens": 0, "reasoning_output_tokens": 0,
    }
    recovery = False
    termination = "infrastructure_failure"
    with tempfile.TemporaryDirectory(prefix="abrl-codex-baseline-") as directory:
        baseline = Path(directory) / "agent"
        shutil.copytree(agent, baseline, symlinks=True)
        for attempt in range(1, 2):
            invocation_started = time.monotonic()
            with tempfile.TemporaryDirectory(prefix="abrl-codex-home-") as home_text:
                fresh_home = materialize_fresh_codex_home(request, Path(home_text))
                process = subprocess.run(
                    codex_command(request, agent), input=prompt.encode("utf-8"), cwd=agent,
                    stdout=subprocess.PIPE, stderr=subprocess.PIPE, check=False,
                    env=codex_process_environment(request, fresh_home),
                )
            stdout_bytes = bytes(process.stdout)
            stderr_bytes = bytes(process.stderr)
            write_new_bytes(
                args.response.parent / f"provider-attempt-{attempt:03d}.stdout.jsonl",
                stdout_bytes,
                f"provider attempt {attempt} stdout",
            )
            write_new_bytes(
                args.response.parent / f"provider-attempt-{attempt:03d}.stderr.log",
                stderr_bytes,
                f"provider attempt {attempt} stderr",
            )
            try:
                stdout_text = stdout_bytes.decode("utf-8", errors="strict")
                stderr_text = stderr_bytes.decode("utf-8", errors="strict")
            except UnicodeDecodeError as error:
                raise SystemExit(
                    "codex target-drift adapter failed: provider output is not UTF-8"
                ) from error
            parsed = parse_codex_jsonl(stdout_text, attempt, recovery)
            invocations.append(model_invocation(
                attempt, parsed["thread_id"], process.returncode,
                time.monotonic() - invocation_started, parsed["turn_completed"],
            ))
            raw_records.extend(
                {"attempt": attempt, "event": event} for event in parsed["raw"]
            )
            all_events.extend(parsed["events"])
            build_logs.append(
                f"[codex invocation {attempt} stderr]\n{stderr_text}\n"
                + parsed["build_log"]
            )
            for field in aggregate:
                aggregate[field] += parsed["usage"][field]
            recovery = parsed["recovery"]
            if (process.returncode == 0 and parsed["thread_id"]
                    and parsed["turn_completed"] and not parsed["runtime_failure"]
                    and not parsed["policy_violations"]):
                termination = "completed"
                break
        if termination == "infrastructure_failure":
            restore_agent(agent, baseline)
    output = agent / "output"
    if output.exists():
        require_plain_directory(output, "agent output directory")
    else:
        output.mkdir()
    after = lean_snapshot(workspace)
    write_new_text(output / "lean-diff.patch", lean_patch(before, after), "lean-diff.patch")
    write_new_text(output / "build.log",
        "".join(build_logs) or "No observable Lean build command was executed.\n",
        "build.log",
    )
    contract = request["result_contract"]
    evidence = []
    for name in contract["workflow_evidence_files"]:
        path = output / name
        if path.exists():
            require_plain_file(path, f"workflow evidence {name}")
            evidence.append({"path": name, "sha256": sha256(path)})
    dump_new(output / "workflow-compliance.json", {
        "schema_version": 1,
        "opaque_run_id": request["opaque_run_id"],
        "workflow_id": contract["workflow_id"],
        "evidence_files": evidence,
    }, "workflow-compliance.json")
    result_path = output / "result.json"
    if result_path.exists():
        require_plain_file(result_path, "result.json")
    else:
        dump_new(output / "result.json", {
            "schema_version": 1,
            "opaque_run_id": request["opaque_run_id"],
            "final_status": (
                "infrastructure_failure"
                if termination == "infrastructure_failure" else "partial"
            ),
            "public_declarations": [],
            "primary_grader_rationale": (
                "The model invocation did not produce a complete machine-readable result."
            ),
        }, "result.json")
    explanation_path = output / "explanation.md"
    if explanation_path.exists():
        require_plain_file(explanation_path, "explanation.md")
    else:
        write_new_text(output / "explanation.md",
            "The model invocation did not produce a complete explanation.\n",
            "explanation.md",
        )

    usage: dict[str, int | float] = {
        **aggregate,
        "tool_calls": sum(event["kind"] == "tool_call" for event in all_events),
        "build_attempts": sum(event["kind"] == "build_attempt" for event in all_events),
        "recovery_tool_calls": sum(
            event["kind"] == "tool_call" and event.get("recovery_phase") is True
            for event in all_events
        ),
        "infrastructure_retries": sum(
            event["kind"] == "model_invocation_retry"
            and event.get("reason") == "infrastructure"
            for event in all_events
        ),
        "wall_seconds": round(time.monotonic() - started, 6),
        "cost_usd": 0.0,
    }
    usage["cost_usd"] = calculate_cost(usage, request["pricing"])
    sequenced = [{"sequence": index, **event} for index, event in enumerate(all_events)]
    sequenced.append({"sequence": len(sequenced), "kind": "usage_summary", "usage": usage})
    write_new_text(args.trace,
        "".join(json.dumps(event, sort_keys=True) + "\n" for event in sequenced),
        "adapter trace",
    )
    provider_events = args.response.parent / "provider-events.jsonl"
    write_new_text(provider_events,
        "".join(json.dumps(record, sort_keys=True) + "\n" for record in raw_records),
        "provider event log",
    )
    dump_new(args.response, {
        "schema_version": 1,
        "opaque_run_id": request["opaque_run_id"],
        "adapter_id": args.adapter_id,
        "adapter_version": args.adapter_version,
        "model_id": args.model_id,
        "immutable_model_version": args.immutable_model_version,
        "replicate": request["replicate"],
        "container_or_sandbox_image_digest": args.image_digest,
        "budget_enforcement_attestation": args.budget_attestation,
        "filesystem_network_process_attestation": args.isolation_attestation,
        "termination": termination,
        "model_invocations": invocations,
        "usage": usage,
    }, "adapter response")


if __name__ == "__main__":
    main()
