#!/usr/bin/env python3
"""Prepare and execute one opaque target-drift run through a frozen adapter."""

from __future__ import annotations

import argparse
import hashlib
import json
import os
import shutil
import signal
import subprocess
import sys
import tarfile
from pathlib import Path, PurePosixPath
from typing import Any


TOOLS = Path(__file__).resolve().parent
ROOT = TOOLS.parent
sys.path.insert(0, str(TOOLS))

import prepare_target_drift_execution as prepare  # noqa: E402


CONDITIONS = ("compile_only", "source_aware_blueprint", "abrl")
WORKFLOW_EVIDENCE = {
    "compile_only": [],
    "source_aware_blueprint": ["blueprint.md"],
    "abrl": [
        "target-contract.json", "blueprint.md", "failure-ledger.json",
        "promotion-gate.log",
    ],
}
USAGE_FIELDS = (
    "input_tokens", "output_tokens", "tool_calls", "build_attempts",
    "recovery_tool_calls", "infrastructure_retries", "wall_seconds", "cost_usd",
)
BLIND_GRADING_TEXT_RULE = (
    "Write primary_grader_rationale and any source-amendment.md using "
    "condition-neutral mathematical language. Do not name the assigned workflow, "
    "its condition label, promotion gate, proof-blueprint, target-contract, failure "
    "ledger, evidence typing, or bounded proof transaction. These operator-only "
    "details remain available through the separate workflow-artifact record."
)


def load(path: Path) -> dict[str, Any]:
    return json.loads(path.read_text(encoding="utf-8"))


def dump(path: Path, value: Any) -> None:
    path.write_text(
        json.dumps(value, indent=2, sort_keys=True, ensure_ascii=False) + "\n",
        encoding="utf-8",
    )


def require(condition: bool, message: str) -> None:
    if not condition:
        raise SystemExit(f"target-drift run preparation failed: {message}")


def opaque_id(kind: str, aggregate: str, semantic_id: str) -> str:
    digest = hashlib.sha256(
        f"{kind}\0{aggregate}\0{semantic_id}".encode("utf-8")
    ).hexdigest()[:20]
    return f"{kind.upper()}-{digest}"


def git_top_level(commit: str) -> list[str]:
    output = subprocess.check_output(
        ["git", "ls-tree", "--name-only", commit], cwd=ROOT, text=True
    )
    return [line for line in output.splitlines() if line]


def selected_paths(commit: str, policy: dict[str, Any], condition: str) -> list[str]:
    entry = policy["conditions"][condition]
    if entry["path_mode"] == "allowlist":
        paths = entry["repository_paths"]
    else:
        excluded = set(entry["excluded_repository_paths"])
        paths = [path for path in git_top_level(commit) if path not in excluded]
    require(paths, f"empty repository view for {condition}")
    for path in paths:
        require(path not in {".git", "evaluation"}, f"forbidden repository path {path}")
        require(not Path(path).is_absolute() and ".." not in PurePosixPath(path).parts,
                f"unsafe repository path {path}")
    return paths


def extract_git_archive(commit: str, paths: list[str], output: Path) -> None:
    output.mkdir(parents=True)
    process = subprocess.Popen(
        ["git", "archive", "--format=tar", commit, "--", *paths],
        cwd=ROOT,
        stdout=subprocess.PIPE,
    )
    assert process.stdout is not None
    with tarfile.open(fileobj=process.stdout, mode="r|") as archive:
        for member in archive:
            name = PurePosixPath(member.name)
            require(not name.is_absolute() and ".." not in name.parts,
                    f"unsafe archive member {member.name}")
            archive.extract(member, output)
    return_code = process.wait()
    require(return_code == 0, f"git archive exited with {return_code}")


def file_manifest(root: Path) -> list[dict[str, Any]]:
    manifest = []
    for path in sorted(item for item in root.rglob("*") if item.is_file()):
        relative = path.relative_to(root)
        if ".lake" in relative.parts:
            continue
        payload = path.read_bytes()
        manifest.append({
            "path": relative.as_posix(),
            "bytes": len(payload),
            "sha256": hashlib.sha256(payload).hexdigest(),
        })
    return manifest


def manifest_sha256(manifest: list[dict[str, Any]]) -> str:
    return hashlib.sha256(prepare.canonical_json_bytes(manifest)).hexdigest()


def terminate_tree(process: subprocess.Popen[str]) -> None:
    if os.name == "nt":
        subprocess.run(
            ["taskkill", "/PID", str(process.pid), "/T", "/F"],
            stdout=subprocess.DEVNULL,
            stderr=subprocess.DEVNULL,
            check=False,
        )
    else:
        try:
            os.killpg(process.pid, signal.SIGKILL)
        except ProcessLookupError:
            pass


def self_verify(pack_dir: Path, config: dict[str, Any]) -> None:
    checks = {
        Path(__file__).resolve(): config["sealed_agent_view"]["run_preparer_sha256"],
        Path(prepare.__file__).resolve(): config["sealed_agent_view"]["materializer_sha256"],
    }
    for current, expected in checks.items():
        sealed = pack_dir / "execution_code" / current.name
        require(sealed.is_file(), f"sealed execution-code copy is missing: {current.name}")
        require(hashlib.sha256(current.read_bytes()).hexdigest() == expected,
                f"invoked execution code differs from frozen hash: {current.name}")
        require(hashlib.sha256(sealed.read_bytes()).hexdigest() == expected,
                f"sealed execution code differs from frozen hash: {current.name}")
    adapter = config["execution_adapter"]
    sealed_entrypoint = pack_dir / "execution_code" / "execution_adapter_entrypoint"
    require(sealed_entrypoint.is_file() and not sealed_entrypoint.is_symlink(),
            "sealed execution-adapter entrypoint is missing or linked")
    require(hashlib.sha256(sealed_entrypoint.read_bytes()).hexdigest()
            == adapter["entrypoint_sha256"],
            "sealed execution-adapter entrypoint differs from frozen hash")
    runtime_text = adapter["runtime_executable"]
    require(isinstance(runtime_text, str) and Path(runtime_text).is_absolute(),
            "frozen execution-adapter runtime is not absolute")
    runtime = prepare.regular_unlinked_file(
        Path(runtime_text).resolve(), "execution adapter runtime"
    )
    require(Path(runtime_text) == runtime,
            "execution-adapter runtime path is not canonical")
    require(hashlib.sha256(runtime.read_bytes()).hexdigest()
            == adapter["runtime_executable_sha256"],
            "execution-adapter runtime differs from frozen hash")
    require(adapter["command_argv"][0] == runtime_text,
            "execution-adapter command does not begin with the frozen runtime")


def scan_forbidden(root: Path, forbidden: list[str]) -> list[dict[str, str]]:
    hits: list[dict[str, str]] = []
    needles = [(value, value.encode("utf-8")) for value in forbidden if value]
    for path in sorted(item for item in root.rglob("*") if item.is_file()):
        try:
            payload = path.read_bytes()
        except OSError:
            continue
        for text, encoded in needles:
            if encoded in payload:
                hits.append({"path": path.relative_to(root).as_posix(), "value": text})
    return hits


def render_prompt(
    template: str,
    opaque_case: str,
    opaque_source: str,
    source_locator: str,
    source_path: Path,
    requirement: str,
    workspace_path: Path,
) -> str:
    replacements = {
        "{{CASE_ID}}": opaque_case,
        "{{SOURCE_ID}}": opaque_source,
        "{{SOURCE_LOCATOR}}": source_locator,
        "{{SOURCE_PACKET_PATH}}": str(source_path),
        "{{PROPOSED_REQUIREMENT}}": requirement,
        "{{WORKSPACE_PATH}}": str(workspace_path),
    }
    rendered = template
    for placeholder, value in replacements.items():
        rendered = rendered.replace(placeholder, value)
    require(not any(placeholder in rendered for placeholder in prepare.PLACEHOLDERS),
            "rendered prompt still contains a placeholder")
    return rendered.rstrip() + "\n\nBlind-grading requirement: " + BLIND_GRADING_TEXT_RULE + "\n"


def prepare_run(pack_dir: Path, semantic_run_id: str, output_dir: Path) -> None:
    prepare.verify_pack(pack_dir)
    config = load(pack_dir / "execution_config.json")
    require(config["suite_id"] == "ABRL-TARGET-DRIFT-V2", "runner requires v2 pack")
    require(config["execution_status"] == "frozen_ready", "runner requires frozen_ready pack")
    self_verify(pack_dir, config)
    require(not output_dir.exists(), "run output directory already exists")

    run_manifest = load(pack_dir / "run_manifest.json")
    matching = [run for run in run_manifest["runs"] if run["run_id"] == semantic_run_id]
    require(len(matching) == 1, "semantic run id not found or duplicated")
    run = matching[0]
    require(run["status"] == "sealed_unrun", "run is not sealed_unrun")
    condition = run["condition"]
    require(condition in CONDITIONS, "unknown run condition")

    case_bank = load(pack_dir / "agent_cases.json")
    cases = [case for case in case_bank["cases"] if case["case_id"] == run["case_id"]]
    require(len(cases) == 1, "run case missing or duplicated")
    case = cases[0]
    aggregate = (pack_dir / "aggregate.sha256").read_text(encoding="ascii").strip()
    opaque_run = opaque_id("run", aggregate, semantic_run_id)
    opaque_case = opaque_id("case", aggregate, run["case_id"])
    opaque_source = opaque_id("source", aggregate, case["source_id"])

    operator_dir = output_dir / "operator"
    agent_dir = output_dir / "agent"
    workspace_dir = agent_dir / "workspace"
    source_dir = agent_dir / "source"
    operator_dir.mkdir(parents=True)
    source_dir.mkdir(parents=True)

    policy = load(pack_dir / "resource_policy.json")
    commit = config["workspace_base_commit"]
    paths = selected_paths(commit, policy, condition)
    extract_git_archive(commit, paths, workspace_dir)
    require(not (workspace_dir / ".git").exists(), "workspace unexpectedly contains .git")
    require(not (workspace_dir / "evaluation").exists(), "workspace leaks evaluation directory")

    source_origin = pack_dir / "source_packets" / case["source_packet_name"]
    require(source_origin.is_file(), "source packet is missing")
    require(prepare.sha256_file(source_origin) == case["source_sha256"],
            "source packet hash differs from sealed case bank")
    source_copy = source_dir / "source.pdf"
    shutil.copyfile(source_origin, source_copy)
    source_copy.chmod(0o444)

    template = (pack_dir / "prompt_templates" / f"{condition}.md").read_text(
        encoding="utf-8"
    )
    rendered = render_prompt(
        template,
        opaque_case,
        opaque_source,
        case["source_locator"],
        source_copy,
        run["proposed_requirement"],
        workspace_dir,
    )
    prompt_path = agent_dir / "prompt.md"
    prompt_path.write_text(rendered, encoding="utf-8")

    forbidden_values = [
        semantic_run_id,
        run["case_id"],
        *[entry["case_id"] for entry in case_bank["cases"]],
    ]
    leakage = scan_forbidden(agent_dir, forbidden_values)
    require(not leakage, "semantic case/run identifier leaked into agent view")

    manifest = file_manifest(workspace_dir)
    dump(operator_dir / "workspace_manifest.json", {
        "schema_version": 1,
        "opaque_run_id": opaque_run,
        "workspace_base_commit": commit,
        "condition_view": condition,
        "selected_repository_paths": paths,
        "files": manifest,
    })
    job = {
        "schema_version": 1,
        "suite_id": config["suite_id"],
        "opaque_run_id": opaque_run,
        "semantic_run_id": semantic_run_id,
        "condition": condition,
        "replicate": run["replicate"],
        "agent_mount": str(agent_dir.resolve()),
        "prompt_path": str(prompt_path.resolve()),
        "prompt_sha256": prepare.sha256_file(prompt_path),
        "source_sha256": case["source_sha256"],
        "workspace_base_commit": commit,
        "model": config["model"],
        "budgets": config["budgets_per_run"],
        "retry_policy": config["retry_policy"],
        "adapter_contract_sha256": config["execution_adapter"]["contract_sha256"],
        "required_adapter_attestations": [
            "fresh model context and process",
            "only agent_mount plus pinned read-only toolchain/dependency cache visible",
            "general network disabled inside evaluated tools",
            "token/tool/build/time/cost budgets enforced",
            "complete request/response/tool/process accounting retained under operator output",
        ],
        "result_contract": {
            "agent_output_directory": str((agent_dir / "output").resolve()),
            "required_files": [
                "result.json",
                "lean-diff.patch",
                "build.log",
                "explanation.md",
                "workflow-compliance.json"
            ],
            "optional_files": ["source-amendment.md"],
            "workflow_id": condition,
            "workflow_evidence_files": WORKFLOW_EVIDENCE[condition],
            "result_required_fields": [
                "schema_version", "opaque_run_id", "final_status",
                "public_declarations", "primary_grader_rationale"
            ],
            "blind_grading_text_rule": BLIND_GRADING_TEXT_RULE,
        },
        "status": "prepared_unrun"
    }
    dump(operator_dir / "job.json", job)
    initial_manifest = file_manifest(agent_dir)
    dump(operator_dir / "run_state.json", {
        "schema_version": 1,
        "opaque_run_id": opaque_run,
        "status": "prepared_unrun",
        "sealed_pack_sha256": aggregate,
        "agent_view_file_count": len(initial_manifest),
        "prepared_agent_manifest_sha256": manifest_sha256(initial_manifest),
        "prepared_job_sha256": prepare.sha256_file(operator_dir / "job.json"),
        "workspace_manifest_sha256": prepare.sha256_file(
            operator_dir / "workspace_manifest.json"
        ),
    })
    print(
        f"prepared opaque target-drift run {opaque_run}: condition={condition}, "
        f"workspace_files={len(manifest)}, status=prepared_unrun"
    )


def parse_trace(path: Path) -> list[dict[str, Any]]:
    require(path.is_file(), "adapter did not produce the required JSONL trace")
    events = []
    for line_number, line in enumerate(path.read_text(encoding="utf-8").splitlines(), 1):
        require(line.strip(), f"blank adapter-trace line {line_number}")
        try:
            event = json.loads(line)
        except json.JSONDecodeError as error:
            raise SystemExit(
                f"target-drift run execution failed: invalid trace JSON line {line_number}: {error}"
            ) from error
        require(event.get("sequence") == len(events),
                f"adapter trace sequence mismatch at line {line_number}")
        require(isinstance(event.get("kind"), str) and event["kind"],
                f"adapter trace kind missing at line {line_number}")
        events.append(event)
    require(events and events[-1]["kind"] == "usage_summary",
            "adapter trace must end in a usage_summary event")
    return events


def validate_usage(
    response: dict[str, Any], events: list[dict[str, Any]], job: dict[str, Any]
) -> dict[str, int | float]:
    usage = response.get("usage")
    require(isinstance(usage, dict), "adapter response usage must be an object")
    require(set(usage) == set(USAGE_FIELDS), "adapter usage field set differs from contract")
    integer_fields = USAGE_FIELDS[:-2]
    for field in integer_fields:
        require(isinstance(usage[field], int) and not isinstance(usage[field], bool)
                and usage[field] >= 0, f"adapter usage {field} must be a nonnegative integer")
    for field in ("wall_seconds", "cost_usd"):
        require(isinstance(usage[field], (int, float)) and not isinstance(usage[field], bool)
                and usage[field] >= 0, f"adapter usage {field} must be nonnegative")
    retry_events = [event for event in events if event["kind"] == "provider_retry"]
    for event in retry_events:
        require(event.get("reason") in {"infrastructure", "semantic"},
                "each provider_retry must record infrastructure or semantic reason")
    request_ids = response.get("provider_request_ids")
    require(isinstance(request_ids, list), "provider_request_ids must be a list")
    require(len(request_ids) == len(set(request_ids)),
            "provider_request_ids must not contain duplicates")
    require(len(retry_events) == max(0, len(request_ids) - 1),
            "provider retry events differ from provider_request_ids")
    derived = {
        "tool_calls": sum(event["kind"] == "tool_call" for event in events),
        "build_attempts": sum(event["kind"] == "build_attempt" for event in events),
        "recovery_tool_calls": sum(
            event["kind"] == "tool_call" and event.get("recovery_phase") is True
            for event in events
        ),
        "infrastructure_retries": sum(
            event["kind"] == "provider_retry" and event.get("reason") == "infrastructure"
            for event in events
        ),
    }
    failure_seen = False
    for event in events[:-1]:
        if event["kind"] == "build_attempt":
            require(isinstance(event.get("success"), bool),
                    "each build_attempt trace event must record boolean success")
            failure_seen = failure_seen or not event["success"]
        elif event["kind"] == "proof_route_failure":
            failure_seen = True
        if event["kind"] == "tool_call" and event.get("recovery_phase") is True:
            require(failure_seen,
                    "recovery_phase tool call occurred before any recorded failure")
    require(all(usage[field] == value for field, value in derived.items()),
            "adapter usage counters differ from complete trace events")
    summary = events[-1].get("usage")
    require(summary == usage, "final trace usage summary differs from adapter response")
    budgets = job["budgets"]
    limits = {
        "input_tokens": "maximum_input_tokens",
        "output_tokens": "maximum_output_tokens",
        "tool_calls": "maximum_tool_calls",
        "build_attempts": "maximum_build_attempts",
        "wall_seconds": "wall_clock_seconds",
        "cost_usd": "maximum_cost_usd",
        "infrastructure_retries": None,
    }
    for field, budget_field in limits.items():
        limit = (
            job["retry_policy"]["infrastructure_retry_limit"]
            if budget_field is None else budgets[budget_field]
        )
        require(usage[field] <= limit, f"adapter exceeded frozen {field} budget")
    require(
        len(retry_events) <= job["budgets"]["maximum_model_retries"],
        "adapter exceeded frozen maximum_model_retries",
    )
    require(
        sum(event.get("reason") == "semantic" for event in retry_events)
        <= job["retry_policy"]["semantic_failure_retries"],
        "adapter exceeded frozen semantic_failure_retries",
    )
    return usage


def render_adapter_command(command: list[str], replacements: dict[str, str]) -> list[str]:
    rendered = []
    joined = "\0".join(command)
    for placeholder in replacements:
        require(placeholder in joined, f"adapter command omits {placeholder}")
    for item in command:
        value = item
        for placeholder, replacement in replacements.items():
            value = value.replace(placeholder, replacement)
        require("{{" not in value and "}}" not in value,
                "adapter command contains an unresolved placeholder")
        rendered.append(value)
    return rendered


def execute_run(pack_dir: Path, run_dir: Path) -> None:
    prepare.verify_pack(pack_dir)
    config = load(pack_dir / "execution_config.json")
    require(config["suite_id"] == "ABRL-TARGET-DRIFT-V2", "executor requires v2 pack")
    require(config["execution_status"] == "frozen_ready", "executor requires frozen pack")
    self_verify(pack_dir, config)
    operator = run_dir / "operator"
    agent = run_dir / "agent"
    require(operator.is_dir() and agent.is_dir(), "prepared run directory is incomplete")
    state_path = operator / "run_state.json"
    state = load(state_path)
    require(state["status"] == "prepared_unrun", "run is not prepared_unrun")
    require(state["sealed_pack_sha256"] == (pack_dir / "aggregate.sha256").read_text(
        encoding="ascii"
    ).strip(), "run state names a different sealed pack")
    job = load(operator / "job.json")
    require(job["opaque_run_id"] == state["opaque_run_id"], "job/run-state ID mismatch")
    require(state["prepared_job_sha256"] == prepare.sha256_file(operator / "job.json"),
            "prepared job changed before execution")
    require(state["workspace_manifest_sha256"]
            == prepare.sha256_file(operator / "workspace_manifest.json"),
            "workspace manifest changed before execution")
    require(job["model"] == config["model"], "prepared job model differs from frozen config")
    require(job["budgets"] == config["budgets_per_run"],
            "prepared job budgets differ from frozen config")
    require(job["retry_policy"] == config["retry_policy"],
            "prepared job retry policy differs from frozen config")
    current_manifest = file_manifest(agent)
    require(manifest_sha256(current_manifest) == state["prepared_agent_manifest_sha256"],
            "agent view changed after preparation and before execution")

    adapter_dir = operator / "adapter"
    adapter_dir.mkdir()
    request_path = adapter_dir / "request.json"
    response_path = adapter_dir / "response.json"
    trace_path = adapter_dir / "trace.jsonl"
    request = {
        "schema_version": 1,
        "opaque_run_id": job["opaque_run_id"],
        "agent_mount": str(agent.resolve()),
        "prompt_path": str((agent / "prompt.md").resolve()),
        "replicate": job["replicate"],
        "model": job["model"],
        "budgets": job["budgets"],
        "retry_policy": job["retry_policy"],
        "result_contract": job["result_contract"],
    }
    dump(request_path, request)
    command = render_adapter_command(
        config["execution_adapter"]["command_argv"],
        {
            "{{REQUEST_PATH}}": str(request_path.resolve()),
            "{{RESPONSE_PATH}}": str(response_path.resolve()),
            "{{TRACE_PATH}}": str(trace_path.resolve()),
            "{{AGENT_MOUNT}}": str(agent.resolve()),
            "{{ADAPTER_ENTRYPOINT_PATH}}": str(
                (pack_dir / "execution_code" / "execution_adapter_entrypoint").resolve()
            ),
        },
    )
    process_kwargs: dict[str, Any] = {}
    if os.name != "nt":
        process_kwargs["start_new_session"] = True
    started = __import__("time").monotonic()
    process = subprocess.Popen(
        command,
        cwd=run_dir,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        text=True,
        encoding="utf-8",
        errors="replace",
        **process_kwargs,
    )
    timeout = int(job["budgets"]["wall_clock_seconds"])
    try:
        stdout, stderr = process.communicate(timeout=timeout)
        timed_out = False
    except subprocess.TimeoutExpired:
        terminate_tree(process)
        stdout, stderr = process.communicate()
        timed_out = True
    orchestrator_wall = __import__("time").monotonic() - started
    (adapter_dir / "process.stdout.log").write_text(stdout, encoding="utf-8")
    (adapter_dir / "process.stderr.log").write_text(stderr, encoding="utf-8")
    require(not timed_out, "adapter exceeded orchestrator wall-clock timeout")
    require(process.returncode == 0, f"adapter exited with code {process.returncode}")
    require(response_path.is_file(), "adapter response is missing")
    response = load(response_path)
    require(response.get("schema_version") == 1, "adapter response schema_version must be 1")
    require(response.get("opaque_run_id") == job["opaque_run_id"], "adapter response run ID mismatch")
    adapter_config = config["execution_adapter"]
    require(response.get("adapter_id") == adapter_config["adapter_id"],
            "adapter response ID differs from frozen config")
    require(response.get("adapter_version") == adapter_config["adapter_version"],
            "adapter response version differs from frozen config")
    require(response.get("model_id") == config["model"]["model_id"],
            "adapter response model ID differs from frozen config")
    require(response.get("immutable_model_version") == config["model"]["immutable_version"],
            "adapter response model version differs from frozen config")
    require(response.get("replicate") == job["replicate"],
            "adapter response does not bind the paired replicate value")
    require(response.get("container_or_sandbox_image_digest")
            == adapter_config["container_or_sandbox_image_digest"],
            "adapter response image digest differs from frozen config")
    require(response.get("budget_enforcement_attestation")
            == adapter_config["budget_enforcement_attestation"],
            "adapter response budget attestation differs from frozen config")
    require(response.get("filesystem_network_process_attestation")
            == adapter_config["filesystem_network_process_attestation"],
            "adapter response isolation attestation differs from frozen config")
    require(response.get("termination") in {
        "completed", "budget_exhausted", "infrastructure_failure"
    }, "unknown adapter termination")
    request_ids = response.get("provider_request_ids")
    require(isinstance(request_ids, list) and all(isinstance(item, str) and item for item in request_ids),
            "provider_request_ids must be a string list")
    require(response["termination"] == "infrastructure_failure" or bool(request_ids),
            "completed/budget-exhausted adapter response needs a provider request ID")
    events = parse_trace(trace_path)
    usage = validate_usage(response, events, job)
    require(orchestrator_wall <= timeout + 1.0,
            "orchestrator wall time exceeds frozen timeout tolerance")

    required_outputs = job["result_contract"]["required_files"]
    output_dir = agent / "output"
    require(output_dir.is_dir(), "adapter did not create the output directory")
    require(all((output_dir / name).is_file() for name in required_outputs),
            "adapter omitted one or more required output files")
    after_manifest = file_manifest(agent)
    receipt_payloads = {
        "request.json": request_path.read_bytes(),
        "response.json": response_path.read_bytes(),
        "trace.jsonl": trace_path.read_bytes(),
        "process.stdout.log": (adapter_dir / "process.stdout.log").read_bytes(),
        "process.stderr.log": (adapter_dir / "process.stderr.log").read_bytes(),
    }
    receipt = {
        "schema_version": 1,
        "opaque_run_id": job["opaque_run_id"],
        "sealed_pack_sha256": state["sealed_pack_sha256"],
        "prepared_agent_manifest_sha256": state["prepared_agent_manifest_sha256"],
        "prepared_job_sha256": state["prepared_job_sha256"],
        "workspace_manifest_sha256": state["workspace_manifest_sha256"],
        "completed_agent_manifest_sha256": manifest_sha256(after_manifest),
        "completed_agent_manifest": after_manifest,
        "protected_input_hashes": {
            "prompt.md": prepare.sha256_file(agent / "prompt.md"),
            "source/source.pdf": prepare.sha256_file(agent / "source" / "source.pdf"),
        },
        "adapter_artifact_sha256": {
            name: hashlib.sha256(payload).hexdigest()
            for name, payload in sorted(receipt_payloads.items())
        },
        "adapter_process_exit_code": process.returncode,
        "adapter_process_wall_seconds": round(orchestrator_wall, 6),
        "usage": {
            **usage,
            "orchestrator_wall_seconds": round(orchestrator_wall, 6),
        },
        "termination": response["termination"],
        "status": "executed_unchecked",
    }
    dump(operator / "execution-receipt.json", receipt)
    state.update({
        "status": "executed_unchecked",
        "completed_agent_manifest_sha256": receipt["completed_agent_manifest_sha256"],
        "execution_receipt_sha256": prepare.sha256_file(operator / "execution-receipt.json"),
    })
    dump(state_path, state)
    print(
        f"executed opaque target-drift run {job['opaque_run_id']}: "
        f"termination={response['termination']}, tools={usage['tool_calls']}, "
        f"wall={usage['wall_seconds']}"
    )


def record_operator_failure(run_dir: Path, message: str) -> None:
    """Persist fail-closed evidence for adapter/time/budget failures before re-raising."""
    operator = run_dir / "operator"
    agent = run_dir / "agent"
    state_path = operator / "run_state.json"
    if not state_path.is_file() or (operator / "execution-receipt.json").exists():
        return
    state = load(state_path)
    if state.get("status") != "prepared_unrun":
        return
    adapter = operator / "adapter"
    artifacts = {
        path.relative_to(adapter).as_posix(): hashlib.sha256(path.read_bytes()).hexdigest()
        for path in sorted(adapter.rglob("*"))
        if adapter.is_dir() and path.is_file()
    }
    receipt = {
        "schema_version": 1,
        "opaque_run_id": state["opaque_run_id"],
        "sealed_pack_sha256": state["sealed_pack_sha256"],
        "prepared_job_sha256": state["prepared_job_sha256"],
        "workspace_manifest_sha256": state["workspace_manifest_sha256"],
        "status": "terminal_operator_failure",
        "failure_message": message,
        "adapter_artifact_sha256": artifacts,
        "agent_manifest_at_failure_sha256": (
            manifest_sha256(file_manifest(agent)) if agent.is_dir() else None
        ),
        "retry_disposition": (
            "fail closed; a separately prepared retry may be scheduled only under the "
            "frozen infrastructure retry policy and must not replace this record"
        ),
    }
    failure_path = operator / "operator-failure-receipt.json"
    dump(failure_path, receipt)
    state.update({
        "status": "terminal_operator_failure",
        "operator_failure_receipt_sha256": prepare.sha256_file(failure_path),
    })
    dump(state_path, state)


def execute_or_record_failure(pack_dir: Path, run_dir: Path) -> None:
    """Execute one run and preserve a terminal receipt for expected or unexpected failures."""
    try:
        execute_run(pack_dir, run_dir)
    except SystemExit as error:
        record_operator_failure(run_dir, str(error))
        raise
    except Exception as error:
        record_operator_failure(run_dir, f"{type(error).__name__}: {error}")
        raise


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--pack", type=Path, required=True)
    action = parser.add_mutually_exclusive_group(required=True)
    action.add_argument("--run-id")
    action.add_argument("--execute", type=Path)
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    if args.run_id is not None:
        require(args.output is not None, "--output is required with --run-id")
        prepare_run(args.pack.resolve(), args.run_id, args.output.resolve())
    else:
        require(args.output is None, "--output is not used with --execute")
        execute_or_record_failure(args.pack.resolve(), args.execute.resolve())


if __name__ == "__main__":
    main()
