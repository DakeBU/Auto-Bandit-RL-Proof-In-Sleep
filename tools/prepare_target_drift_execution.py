#!/usr/bin/env python3
"""Validate or materialize the result-free ABRL target-drift execution pack."""

from __future__ import annotations

import argparse
import hashlib
import json
import os
import random
import re
import stat
import subprocess
import sys
import tempfile
from pathlib import Path
from typing import Any

import launch_target_drift_checker_container as checker_launcher
import prepare_target_drift_checker_image as checker_image_builder
import target_drift_checker_cache_manifest as checker_cache_manifest


ROOT = Path(__file__).resolve().parents[1]
SUITE = ROOT / "evaluation" / "target-drift-v1"
CONDITIONS = ("compile_only", "source_aware_blueprint", "abrl")
PLACEHOLDERS = (
    "{{CASE_ID}}",
    "{{SOURCE_ID}}",
    "{{SOURCE_LOCATOR}}",
    "{{SOURCE_PACKET_PATH}}",
    "{{PROPOSED_REQUIREMENT}}",
    "{{WORKSPACE_PATH}}",
)
PRIMARY_GRADING_PROVENANCE_MARKERS = (
    "compile-only condition",
    "source-aware blueprint condition",
    "full abrl condition",
    "condition=compile_only",
    "condition=source_aware_blueprint",
    "condition=abrl",
    "promotion gate",
    "proof-blueprint",
    "target-contract",
    "failure ledger",
    "evidence-typed",
    "bounded proof transaction",
)
LEAN_PROVENANCE_MARKERS = PRIMARY_GRADING_PROVENANCE_MARKERS[:6]


def load(path: Path) -> dict[str, Any]:
    return json.loads(path.read_text(encoding="utf-8"))


def dump(path: Path, value: Any) -> None:
    path.write_text(
        json.dumps(value, indent=2, sort_keys=True, ensure_ascii=False) + "\n",
        encoding="utf-8",
    )


def require(condition: bool, message: str) -> None:
    if not condition:
        raise SystemExit(f"target-drift preparation failed: {message}")


def sha256_bytes(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def sha256_file(path: Path) -> str:
    return sha256_bytes(path.read_bytes())


def canonical_json_bytes(value: Any) -> bytes:
    return (
        json.dumps(value, indent=2, sort_keys=True, ensure_ascii=False) + "\n"
    ).encode("utf-8")


def normalized_config_for_digest(config: dict[str, Any]) -> dict[str, Any]:
    normalized = json.loads(json.dumps(config))
    normalized["execution_status"] = "frozen_ready"
    normalized["sealed_agent_view"]["aggregate_sha256"] = "UNSET"
    normalized["source_files_manifest"] = "SEALED/source_manifest.json"
    normalized["unresolved_fields"] = []
    return normalized


def aggregate_digest(components: dict[str, bytes]) -> tuple[str, list[dict[str, Any]]]:
    digest = hashlib.sha256()
    manifest: list[dict[str, Any]] = []
    for name in sorted(components):
        payload = components[name]
        encoded_name = name.encode("utf-8")
        digest.update(len(encoded_name).to_bytes(8, "big"))
        digest.update(encoded_name)
        digest.update(len(payload).to_bytes(8, "big"))
        digest.update(payload)
        manifest.append({
            "name": name,
            "bytes": len(payload),
            "sha256": sha256_bytes(payload),
        })
    return digest.hexdigest(), manifest


def unset_paths(value: Any, prefix: str = "") -> list[str]:
    paths: list[str] = []
    if value == "UNSET":
        return [prefix or "<root>"]
    if isinstance(value, dict):
        for key, child in value.items():
            if key == "unresolved_fields":
                continue
            child_prefix = f"{prefix}.{key}" if prefix else key
            paths.extend(unset_paths(child, child_prefix))
    elif isinstance(value, list):
        for index, child in enumerate(value):
            paths.extend(unset_paths(child, f"{prefix}[{index}]"))
    return paths


def resolve_repo_path(path_text: str) -> Path:
    path = Path(path_text)
    return path if path.is_absolute() else ROOT / path


def adapter_entrypoint_path(config: dict[str, Any]) -> Path:
    text = config["execution_adapter"]["entrypoint_path"]
    require(isinstance(text, str) and text and text != "UNSET",
            "execution adapter entrypoint path is unresolved")
    relative = Path(text)
    require(not relative.is_absolute(),
            "execution adapter entrypoint must be a repository-relative path")
    root = ROOT.resolve()
    require(relative.parts and all(part not in {"", ".", ".."} for part in relative.parts),
            "execution adapter entrypoint contains a traversal component")
    current = root
    for index, part in enumerate(relative.parts):
        current = current / part
        require(current.exists() and not current.is_symlink(),
                "execution adapter entrypoint path is missing or linked")
        info = current.lstat()
        reparse = bool(getattr(info, "st_file_attributes", 0) & 0x400)
        require(not reparse, "execution adapter entrypoint crosses a reparse point")
        if index < len(relative.parts) - 1:
            require(stat.S_ISDIR(info.st_mode),
                    "execution adapter entrypoint parent is not a directory")
        else:
            require(stat.S_ISREG(info.st_mode) and info.st_nlink == 1,
                    "execution adapter entrypoint must be one unlinked regular file")
    resolved = current.resolve()
    try:
        resolved.relative_to(root)
    except ValueError:
        require(False, "execution adapter entrypoint escapes the repository")
    return resolved


def regular_unlinked_file(
    path: Path, label: str, *, require_executable: bool = True,
) -> Path:
    require(path.is_absolute() and path.exists() and not path.is_symlink(),
            f"{label} must be an existing absolute nonlink path")
    info = path.lstat()
    reparse = bool(getattr(info, "st_file_attributes", 0) & 0x400)
    require(stat.S_ISREG(info.st_mode) and not reparse and info.st_nlink == 1,
            f"{label} must be one unlinked regular file")
    if require_executable and os.name != "nt":
        require(os.access(path, os.X_OK), f"{label} is not executable")
    return path


def checker_runtime_config_payload(config: dict[str, Any]) -> dict[str, Any]:
    """Return the complete, non-self-referential checker runtime boundary.

    The isolation report binds this payload rather than a hand-written subset.
    Derived hashes are read from the current files so the payload can be
    computed before preseal fills the corresponding config fields.
    """
    entry = config["posthoc_checker"]
    if entry.get("mode") == "excluded_fixture":
        return {
            "schema_version": 1,
            "suite_id": config["suite_id"],
            "checker_id": entry["checker_id"],
            "checker_version": entry["checker_version"],
            "mode": "excluded_fixture",
            "runtime_id": entry["runtime_id"],
            "runtime_version": entry["runtime_version"],
            "sandbox_command_argv": entry["sandbox_command_argv"],
            "sandbox_cleanup_argv": entry["sandbox_cleanup_argv"],
            "sandbox_inspect_argv": entry["sandbox_inspect_argv"],
            "sandbox_cleanup_by_label_argv": entry["sandbox_cleanup_by_label_argv"],
            "sandbox_inspect_by_label_argv": entry["sandbox_inspect_by_label_argv"],
            "inspect_absent_exit_code": entry["inspect_absent_exit_code"],
            "container_image_digest": entry["container_image_digest"],
            "budgets": entry["budgets"],
            "worker_command_prefix": entry["worker_command_prefix"],
            "cache_prelude_argv": entry["cache_prelude_argv"],
            "driver_sha256": sha256_file(resolve_repo_path(entry["driver_path"])),
            "inner_checker_sha256": sha256_file(
                resolve_repo_path(entry["inner_checker_path"])
            ),
            "contract_sha256": sha256_file(resolve_repo_path(entry["contract"])),
        }
    launcher_path = resolve_repo_path(entry["host_launcher_path"])
    commands = checker_launcher.command_templates(entry, launcher_path)
    code = {
        "driver_sha256": sha256_file(resolve_repo_path(entry["driver_path"])),
        "inner_checker_sha256": sha256_file(
            resolve_repo_path(entry["inner_checker_path"])
        ),
        "isolation_probe_runner_sha256": sha256_file(
            resolve_repo_path(entry["isolation_probe_runner_path"])
        ),
        "contract_sha256": sha256_file(resolve_repo_path(entry["contract"])),
        "host_launcher_sha256": sha256_file(launcher_path),
        "checker_image_recipe_sha256": sha256_file(
            resolve_repo_path(entry["checker_image_recipe"])
        ),
        "checker_image_sbom_sha256": sha256_file(
            resolve_repo_path(entry["checker_image_sbom"])
        ),
        "checker_image_build_input_manifest_sha256": sha256_file(
            resolve_repo_path(entry["checker_image_build_input_manifest"])
        ),
        "checker_cache_manifest_sha256": sha256_file(
            resolve_repo_path(entry["checker_cache_manifest_artifact"])
        ),
        "checker_image_build_log_sha256": sha256_file(
            resolve_repo_path(entry["checker_image_build_log"])
        ),
        "controller_entrypoint_source_sha256": sha256_file(
            resolve_repo_path(entry["controller_entrypoint_source"])
        ),
        "controller_entrypoint_sha256": entry["controller_entrypoint_sha256"],
        "materializer_sha256": sha256_file(resolve_repo_path(
            config["sealed_agent_view"]["materializer"]
        )),
        "run_preparer_sha256": sha256_file(resolve_repo_path(
            config["sealed_agent_view"]["run_preparer"]
        )),
    }
    return {
        "schema_version": 1,
        "suite_id": config["suite_id"],
        "checker_id": entry["checker_id"],
        "checker_version": entry["checker_version"],
        "mode": entry["mode"],
        "runtime_id": entry["runtime_id"],
        "runtime_version": entry["runtime_version"],
        **commands,
        "host_python_executable": entry["host_python_executable"],
        "host_python_executable_sha256": entry["host_python_executable_sha256"],
        "container_runtime_kind": entry["container_runtime_kind"],
        "container_runtime_executable": entry["container_runtime_executable"],
        "container_runtime_executable_sha256": entry[
            "container_runtime_executable_sha256"
        ],
        "runtime_version_output_sha256": entry["runtime_version_output_sha256"],
        "runtime_signature_output_sha256": entry[
            "runtime_signature_output_sha256"
        ],
        "daemon_identity_output_sha256": entry["daemon_identity_output_sha256"],
        "controller_entrypoint": entry["controller_entrypoint"],
        "controller_uid": entry["controller_uid"],
        "worker_uid": entry["worker_uid"],
        "inspect_absent_exit_code": entry["inspect_absent_exit_code"],
        "container_image_digest": entry["container_image_digest"],
        "filesystem_network_process_attestation": entry[
            "filesystem_network_process_attestation"
        ],
        "controller_worker_separation_attestation": entry[
            "controller_worker_separation_attestation"
        ],
        "checker_cache_root": entry["checker_cache_root"],
        "checker_cache_manifest_path": entry["checker_cache_manifest_path"],
        "checker_cache_manifest_sha256": entry["checker_cache_manifest_sha256"],
        "budgets": entry["budgets"],
        "worker_command_prefix": entry["worker_command_prefix"],
        "cache_prelude_argv": entry["cache_prelude_argv"],
        **code,
    }


def checker_runtime_config_sha256(config: dict[str, Any]) -> str:
    return sha256_bytes(canonical_json_bytes(checker_runtime_config_payload(config)))


def rendered_argv_matches_template(template: list[str], rendered: list[str]) -> bool:
    if len(template) != len(rendered):
        return False
    for source, actual in zip(template, rendered):
        pattern = re.escape(source)
        pattern = re.sub(r"\\\{\\\{[A-Z0-9_]+\\\}\\\}", r".+", pattern)
        if re.fullmatch(pattern, actual) is None:
            return False
    return True


def probe_artifact_bytes(root: Path) -> dict[str, bytes]:
    require(root.is_dir(), "checker isolation-probe artifact directory is missing")
    payloads: dict[str, bytes] = {}
    for path in sorted(root.rglob("*")):
        relative = path.relative_to(root).as_posix()
        info = path.lstat()
        reparse = bool(getattr(info, "st_file_attributes", 0) & 0x400)
        require(not path.is_symlink() and not reparse,
                f"checker isolation-probe artifact is linked: {relative}")
        require(path.is_dir() or path.is_file(),
                f"checker isolation-probe artifact is special: {relative}")
        if path.is_file():
            require(info.st_nlink == 1,
                    f"checker isolation-probe artifact is multiply linked: {relative}")
            payloads[relative] = path.read_bytes()
    require(payloads, "checker isolation-probe artifact directory is empty")
    return payloads


def probe_artifact_manifest(payloads: dict[str, bytes]) -> list[dict[str, Any]]:
    return [
        {"path": name, "bytes": len(payload), "sha256": sha256_bytes(payload)}
        for name, payload in sorted(payloads.items())
    ]


def validate_prompt_templates(config: dict[str, Any], require_hashes: bool) -> None:
    require(set(config["conditions"]) == set(CONDITIONS),
            "condition set must remain compile_only, source_aware_blueprint, abrl")
    for condition in CONDITIONS:
        entry = config["conditions"][condition]
        template_path = resolve_repo_path(entry["prompt_template"])
        require(template_path.is_file(), f"missing prompt template for {condition}")
        text = template_path.read_text(encoding="utf-8")
        for placeholder in PLACEHOLDERS:
            require(placeholder in text,
                    f"{condition} prompt is missing placeholder {placeholder}")
        if require_hashes:
            require(entry["prompt_sha256"] == sha256_file(template_path),
                    f"{condition} prompt hash does not match")


def validate_resource_policy(config: dict[str, Any], require_hash: bool) -> dict[str, Any]:
    policy_path = resolve_repo_path(config["resource_policy"])
    require(policy_path.is_file(), "missing resource policy")
    policy = load(policy_path)
    require(policy["suite_id"] == config["suite_id"], "resource policy suite mismatch")
    require(policy["status"] == "policy_frozen_results_absent",
            "resource policy must remain result-free")
    require(set(policy["conditions"]) == set(CONDITIONS),
            "resource policy condition set differs from execution conditions")
    require(policy["common_isolation"]["attestation_required"] is True,
            "resource policy must require an isolation attestation")
    require(policy["conditions"]["compile_only"]["path_mode"] == "allowlist",
            "compile-only repository view must be an allowlist")
    require(policy["conditions"]["source_aware_blueprint"]["path_mode"] == "allowlist",
            "source-aware repository view must be an allowlist")
    for condition in ("compile_only", "source_aware_blueprint"):
        require(policy["conditions"][condition]["repository_paths"]
                == list(checker_image_builder.SOURCE_PATHS),
                f"{condition} base paths differ from the checker-image baseline")
    require(policy["conditions"]["abrl"]["path_mode"] == "denylist",
            "ABRL repository view must be a denylist")
    require("evaluation" in policy["conditions"]["abrl"]["excluded_repository_paths"],
            "ABRL view must exclude the adjudication/evaluation directory")
    if "workspace_base_commit" in config:
        require(policy["workspace_base_commit"] == config["workspace_base_commit"],
                "resource policy workspace base differs from execution config")
    if require_hash:
        require(config["resource_policy_sha256"] == sha256_file(policy_path),
                "resource policy hash does not match")
    return policy


def validate_paired_requirements(
    config: dict[str, Any], challenges: list[dict[str, Any]] | None = None
) -> dict[str, Any]:
    path = resolve_repo_path(config["paired_requirements"])
    require(path.is_file(), "missing paired-requirement bank")
    payload = load(path)
    require(payload["suite_id"] == config["suite_id"],
            "paired-requirement suite mismatch")
    require(payload["status"] == "paired_wording_frozen_results_absent",
            "paired-requirement bank must remain result-free")
    template = payload.get("common_template")
    require(isinstance(template, str) and len(template.split()) >= 12,
            "paired requirements need one substantive common template")
    require(template.count("{{FIELD}}") == 1 and template.count("{{VALUE}}") == 1,
            "paired requirement template must contain one FIELD and one VALUE placeholder")
    entries = payload.get("cases")
    require(isinstance(entries, list) and len(entries) == 30,
            "paired-requirement bank must contain thirty cases")
    require(len({entry.get("case_id") for entry in entries}) == 30,
            "paired-requirement case identifiers must be unique")
    forbidden_markers = (
        "source_faithful", "injected_drift", "faithful variant", "drift variant",
        "implement a lean target that preserves this frozen source contract",
    )
    for entry in entries:
        field = entry.get("field")
        require(isinstance(field, str) and field.strip() == field and field,
                f"empty or untrimmed field for {entry.get('case_id')}")
        for variant in ("source_faithful", "injected_drift"):
            value = entry.get(f"{variant}_value")
            require(isinstance(value, str) and value.strip() and value == value.strip(),
                    f"empty or untrimmed {variant} value for {entry.get('case_id')}")
            rendered = render_paired_requirement(template, field, value)
            require(not any(marker in rendered.lower() for marker in forbidden_markers),
                    f"variant-label/style marker leaked for {entry.get('case_id')}")
    if challenges is not None:
        require(
            [entry["case_id"] for entry in entries] == [case["id"] for case in challenges],
            "paired-requirement order/identity differs from frozen challenges",
        )
    return payload


def render_paired_requirement(template: str, field: str, value: str) -> str:
    rendered = template.replace("{{FIELD}}", field).replace("{{VALUE}}", value)
    require("{{" not in rendered and "}}" not in rendered,
            "paired requirement still contains a template placeholder")
    return rendered


def validate_adapter_contract(config: dict[str, Any], require_hash: bool) -> dict[str, Any]:
    entry = config["execution_adapter"]
    path = resolve_repo_path(entry["contract"])
    require(path.is_file(), "missing execution-adapter contract")
    contract = load(path)
    require(contract.get("schema_version") == 3,
            "adapter contract schema must be version 3")
    require(contract["suite_id"] == config["suite_id"], "adapter-contract suite mismatch")
    require(contract["status"] == "interface_frozen_results_absent",
            "adapter contract must remain result-free")
    require(set(contract["request_schema"]["required"]) == {
        "opaque_run_id", "replicate", "agent_mount", "prompt_path", "model",
        "pricing", "budgets", "retry_policy", "result_contract", "provider_runtime",
    }, "adapter request schema differs from the runner request")
    require(set(contract["response_schema"]["usage_fields"]) == {
        "input_tokens", "cached_input_tokens", "cache_write_input_tokens", "output_tokens",
        "reasoning_output_tokens", "tool_calls", "build_attempts",
        "recovery_tool_calls", "infrastructure_retries", "wall_seconds", "cost_usd",
    }, "adapter usage schema differs from the runner accounting")
    require(set(contract["response_schema"]["model_invocation_fields"]) == {
        "attempt", "transport", "observable_id_kind", "observable_id",
        "process_exit_code", "wall_seconds", "usage_observed",
    }, "adapter model-invocation schema differs from the runner accounting")
    command = entry["command_argv"]
    require(isinstance(command, list) and command and all(isinstance(item, str) for item in command),
            "execution adapter command_argv must be a nonempty string list")
    if require_hash:
        require(entry["contract_sha256"] == sha256_file(path),
                "adapter-contract hash does not match")
        entrypoint = adapter_entrypoint_path(config)
        require(entrypoint.is_file() and not entrypoint.is_symlink(),
                "execution adapter entrypoint is missing or linked")
        require(entry["entrypoint_sha256"] == sha256_file(entrypoint),
                "execution adapter entrypoint hash does not match")
        runtime_text = entry["runtime_executable"]
        require(isinstance(runtime_text, str) and Path(runtime_text).is_absolute(),
                "execution adapter runtime must be an absolute path")
        runtime = regular_unlinked_file(Path(runtime_text).resolve(),
                                        "execution adapter runtime")
        require(Path(runtime_text) == runtime,
                "execution adapter runtime path must already be canonical")
        require(entry["runtime_executable_sha256"] == sha256_file(runtime),
                "execution adapter runtime hash does not match")
        validate_provider_runtime(entry["provider_runtime"], require_hash=True)
        require(command[0] == runtime_text,
                "execution adapter command must begin with the frozen runtime")
        joined = "\0".join(command)
        for placeholder in contract["invocation"]["required_placeholders"]:
            require(placeholder in joined,
                    f"adapter command omits required placeholder {placeholder}")
        require(entry["container_or_sandbox_image_digest"] in joined,
                "adapter command must literally bind the frozen sandbox image digest")
    return contract


def provider_runtime_version_output(executable: Path) -> bytes:
    process = subprocess.run(
        [str(executable), "--version"], stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT, check=False,
    )
    require(process.returncode == 0,
            "provider runtime --version command failed")
    require(bool(process.stdout.strip()),
            "provider runtime --version output is empty")
    return process.stdout


def validate_provider_runtime(
    provider: dict[str, Any], require_hash: bool
) -> Path | None:
    require(isinstance(provider, dict),
            "execution_adapter.provider_runtime must be an object")
    require(provider.get("kind") in {"codex_cli", "excluded_fixture"},
            "provider runtime kind must be codex_cli or excluded_fixture")
    executable_text = provider.get("executable")
    if not require_hash and executable_text == "UNSET":
        return None
    require(isinstance(executable_text, str) and Path(executable_text).is_absolute(),
            "provider runtime executable must be an absolute path")
    executable = regular_unlinked_file(
        Path(executable_text).resolve(), "provider runtime executable"
    )
    require(Path(executable_text) == executable,
            "provider runtime executable path must already be canonical")
    if require_hash:
        require(provider.get("executable_sha256") == sha256_file(executable),
                "provider runtime executable hash does not match")
        output = provider_runtime_version_output(executable)
        require(provider.get("version_output_sha256") == sha256_bytes(output),
                "provider runtime version output hash does not match")
        observed = output.decode("utf-8", errors="strict").strip()
        require(provider.get("version") == observed,
                "provider runtime version text does not match")
        if provider["kind"] == "codex_cli":
            auth_source_text = provider.get("auth_source_path")
            require(isinstance(auth_source_text, str)
                    and Path(auth_source_text).is_absolute(),
                    "Codex provider auth source must be an absolute path")
            auth_source = Path(auth_source_text)
            require(auth_source.resolve() == auth_source,
                    "Codex provider auth source path must already be canonical")
            home_info = auth_source.lstat() if auth_source.exists() else None
            require(auth_source.is_dir() and not auth_source.is_symlink()
                    and home_info is not None
                    and not bool(getattr(home_info, "st_file_attributes", 0) & 0x400),
                    "Codex provider auth source must be a plain directory")
            children = list(auth_source.iterdir())
            require({child.name for child in children} == {"auth.json"},
                    "Codex provider auth source must contain only auth.json")
            regular_unlinked_file(auth_source / "auth.json", "Codex provider auth.json")
            attestation = provider.get("fresh_codex_home_attestation")
            require(isinstance(attestation, str) and len(attestation.strip()) >= 20,
                    "Codex provider fresh auth-only CODEX_HOME needs an attestation")
            safe_names = {
                "LANG", "LC_ALL", "PATH", "SYSTEMROOT", "SystemRoot", "TEMP", "TMP",
            }
            for field in ("process_environment", "shell_environment"):
                environment = provider.get(field)
                require(isinstance(environment, dict),
                        f"Codex provider {field} must be an object")
                lowered = set()
                for name, value in environment.items():
                    require(isinstance(name, str) and name in safe_names,
                            f"Codex provider {field} has a non-allowlisted name")
                    require(name.lower() not in lowered,
                            f"Codex provider {field} repeats a name by case")
                    require(isinstance(value, str) and bool(value),
                            f"Codex provider {field}.{name} must be nonempty")
                    lowered.add(name.lower())
            require("path" in {
                name.lower() for name in provider["shell_environment"]
            }, "Codex provider shell_environment must freeze PATH")
    return executable


def validate_codex_cli_configuration(
    provider: dict[str, Any], model: dict[str, Any]
) -> None:
    """Require the frozen CLI to parse the selected reasoning/tier configuration."""
    executable = Path(provider["executable"])
    environment = dict(provider["process_environment"])
    with tempfile.TemporaryDirectory(prefix="abrl-codex-config-probe-") as directory:
        environment["CODEX_HOME"] = directory
        process = subprocess.run([
            str(executable),
            "--config", f"model_reasoning_effort={json.dumps(model['reasoning_effort'])}",
            "--config", f"service_tier={json.dumps(model['service_tier'])}",
            "features", "list",
        ], cwd=ROOT, env=environment, stdout=subprocess.PIPE,
            stderr=subprocess.STDOUT, check=False, timeout=30)
    require(process.returncode == 0,
            "frozen Codex CLI rejects the selected reasoning effort or service tier")


def validate_checker_runtime_preflight(config: dict[str, Any]) -> dict[str, Any]:
    """Validate the executable checker boundary before any probe is launched."""
    entry = config["posthoc_checker"]
    contract_path = resolve_repo_path(entry["contract"])
    require(contract_path.is_file(), "missing checker-sandbox contract")
    contract = load(contract_path)
    require(contract.get("suite_id") == config["suite_id"]
            and contract.get("status") == "interface_frozen_results_absent",
            "checker-sandbox contract identity/status mismatch")
    if entry.get("mode") == "excluded_fixture":
        for field in (
            "sandbox_command_argv", "sandbox_cleanup_argv", "sandbox_inspect_argv",
            "sandbox_cleanup_by_label_argv", "sandbox_inspect_by_label_argv",
        ):
            require(isinstance(entry[field], list) and entry[field]
                    and all(isinstance(item, str) and item for item in entry[field]),
                    f"excluded fixture {field} must be a nonempty argv")
        return contract
    require(entry.get("mode") == "production",
            "checker mode must be production or excluded_fixture")
    launcher_path = resolve_repo_path(entry["host_launcher_path"])
    require(launcher_path.is_file()
            and entry["host_launcher_sha256"] == sha256_file(launcher_path),
            "checker host launcher is missing or differs from the seal")
    generated_commands = checker_launcher.command_templates(entry, launcher_path)
    command_fields = (
        "sandbox_command_argv", "sandbox_cleanup_argv", "sandbox_inspect_argv",
        "sandbox_cleanup_by_label_argv", "sandbox_inspect_by_label_argv",
    )
    for field in command_fields:
        argv = entry[field]
        require(isinstance(argv, list) and argv
                and all(isinstance(item, str) and item for item in argv),
                f"posthoc_checker.{field} must be a nonempty argv")
        require(argv == generated_commands[field],
                f"posthoc_checker.{field} is not the sealed launcher template")
    joined = "\0".join(entry["sandbox_command_argv"])
    for placeholder in contract["invocation"]["required_placeholders"]:
        require(placeholder in joined,
                f"checker sandbox command omits required placeholder {placeholder}")
    route_placeholders = (
        ("sandbox_cleanup_argv", "cleanup_required_placeholder"),
        ("sandbox_inspect_argv", "inspect_required_placeholder"),
        ("sandbox_cleanup_by_label_argv", "label_cleanup_required_placeholder"),
        ("sandbox_inspect_by_label_argv", "label_inspect_required_placeholder"),
    )
    for field, contract_field in route_placeholders:
        require(contract["invocation"][contract_field] in "\0".join(entry[field]),
                f"checker lifecycle route omits {contract['invocation'][contract_field]}")
    require(not any(
        token == "-d" or token == "--detach" or token.startswith("--detach=")
        for token in entry["sandbox_command_argv"]
    ), "checker sandbox command contains detached mode")
    require(entry["mode"] in {"production", "excluded_fixture"},
            "checker mode must be production or excluded_fixture")
    require(re.fullmatch(r"sha256:[0-9a-f]{64}", entry["container_image_digest"])
            is not None, "checker image digest is not immutable")
    require(isinstance(entry["inspect_absent_exit_code"], int)
            and not isinstance(entry["inspect_absent_exit_code"], bool)
            and 0 <= entry["inspect_absent_exit_code"] <= 255,
            "checker absent exit code is invalid")
    require(entry["inspect_absent_exit_code"] == checker_launcher.ABSENT_EXIT_CODE,
            "checker absent exit code differs from the sealed launcher")
    for field in (
        "wall_clock_seconds", "memory_mb", "pids_limit", "maximum_output_bytes",
        "maximum_response_bytes",
    ):
        require(isinstance(entry["budgets"][field], int)
                and not isinstance(entry["budgets"][field], bool)
                and entry["budgets"][field] > 0,
                f"posthoc_checker.budgets.{field} must be positive")
    require(isinstance(entry["budgets"]["cpus"], (int, float))
            and not isinstance(entry["budgets"]["cpus"], bool)
            and entry["budgets"]["cpus"] > 0,
            "posthoc_checker.budgets.cpus must be positive")
    require(all(resolve_repo_path(entry[field]).is_file() for field in (
        "driver_path", "inner_checker_path", "isolation_probe_runner_path",
        "host_launcher_path", "checker_image_recipe", "checker_image_sbom",
        "checker_image_build_input_manifest", "checker_cache_manifest_artifact",
        "checker_image_build_log", "controller_entrypoint_source",
    )), "checker controller/inner/probe-runner file is missing")
    host_python = Path(entry["host_python_executable"])
    require(host_python.resolve() == Path(sys.executable).resolve(),
            "checker host Python differs from the invoking interpreter")
    checker_launcher.regular_executable(
        host_python.resolve(), entry["host_python_executable_sha256"], "host Python"
    )
    runtime = checker_launcher.regular_executable(
        Path(entry["container_runtime_executable"]),
        entry["container_runtime_executable_sha256"], "Docker runtime",
    )
    require(entry["container_runtime_kind"] == "docker",
            "production checker supports only the sealed Docker launcher")
    require(runtime.resolve() == checker_launcher.canonical_docker_executable(),
            "Docker runtime differs from the canonical audited executable")
    identity = checker_launcher.runtime_identity(runtime)
    require(entry["runtime_id"] == identity["runtime_id"]
            and entry["runtime_version"] == identity["runtime_version"]
            and entry["runtime_signature_output_sha256"]
            == identity["runtime_signature_output_sha256"]
            and identity["runtime_version_output_sha256"]
            == entry["runtime_version_output_sha256"]
            and identity["daemon_identity_output_sha256"]
            == entry["daemon_identity_output_sha256"],
            "Docker client/server version or daemon identity changed")
    recipe_path = resolve_repo_path(entry["checker_image_recipe"])
    sbom_path = resolve_repo_path(entry["checker_image_sbom"])
    build_input_path = resolve_repo_path(entry["checker_image_build_input_manifest"])
    cache_manifest_path = resolve_repo_path(entry["checker_cache_manifest_artifact"])
    build_log_path = resolve_repo_path(entry["checker_image_build_log"])
    controller_path = resolve_repo_path(entry["controller_entrypoint_source"])
    require(entry["checker_image_recipe_sha256"] == sha256_file(recipe_path)
            and entry["checker_image_sbom_sha256"] == sha256_file(sbom_path)
            and entry["checker_image_build_input_manifest_sha256"]
            == sha256_file(build_input_path)
            and entry["checker_cache_manifest_sha256"] == sha256_file(cache_manifest_path)
            and entry["checker_image_build_log_sha256"] == sha256_file(build_log_path)
            and entry["controller_entrypoint_source_sha256"]
            == sha256_file(controller_path),
            "checker image provenance artifact/controller hash differs from the seal")
    sbom = load(sbom_path)
    build_input = load(build_input_path)
    current_orchestrator = subprocess.check_output(
        ["git", "rev-parse", "HEAD"], cwd=ROOT, text=True
    ).strip()
    checker_image_builder.validate_build_input_payload(
        build_input,
        expected_workspace_commit=config.get("workspace_base_commit"),
        expected_orchestrator_commit=current_orchestrator,
    )
    cache_payload = checker_cache_manifest.load_manifest(cache_manifest_path)
    lean_toolchain_sha256 = next(
        item["sha256"] for item in build_input["source_files"]
        if item["path"] == "lean-toolchain"
    )
    expected_cache_provenance = {
        "workspace_base_commit": build_input["workspace_base_commit"],
        "source_files_aggregate_sha256": build_input[
            "source_files_aggregate_sha256"
        ],
        "build_input_manifest_sha256": sha256_file(build_input_path),
        "checker_image_recipe_sha256": sha256_file(recipe_path),
        "base_image_digest": build_input["lean_base_image_digest"].split(":", 1)[1],
        "lean_toolchain_sha256": lean_toolchain_sha256,
    }
    require(cache_payload["provenance"] == expected_cache_provenance,
            "checker cache manifest is not bound to the frozen Git baseline")
    validate_checker_image_sbom(
        entry, sbom, sha256_file(resolve_repo_path(entry["inner_checker_path"])),
        config.get("workspace_base_commit"), build_input, cache_payload,
        sha256_file(build_input_path), sha256_file(build_log_path), identity,
        checker_image_builder.lean_toolchain_release(
            build_input["workspace_base_commit"]
        ),
    )
    require(entry["controller_uid"] == "0:0"
            and re.fullmatch(r"[1-9][0-9]*:[1-9][0-9]*", entry["worker_uid"]),
            "checker requires the sealed root controller and a positive worker UID:GID")
    require(entry["controller_entrypoint"] == checker_launcher.CONTROLLER_PATH,
            "checker controller entrypoint differs from the sealed image path")
    if entry["mode"] == "production":
        require(entry["cache_prelude_argv"] == [],
                "production checker cache prelude must be empty")
        require(entry["worker_command_prefix"]
                == checker_launcher.worker_command_prefix(entry),
                "production worker prefix is not the sealed UID/GID transition")
    if entry.get("contract_sha256") != "UNSET":
        require(entry["contract_sha256"] == sha256_file(contract_path),
                "checker contract hash is stale")
    return contract


def validate_checker_image_sbom(
    entry: dict[str, Any], sbom: dict[str, Any], inner_checker_sha256: str,
    workspace_base_commit: str | None = None,
    build_input: dict[str, Any] | None = None,
    cache_manifest: dict[str, Any] | None = None,
    build_input_sha256: str | None = None,
    build_log_sha256: str | None = None,
    current_runtime_identity: dict[str, str] | None = None,
    expected_toolchain_release: str | None = None,
) -> None:
    expected_sbom_fields = {
        "schema_version", "suite_id", "status", "container_image_digest",
        "checker_image_recipe_sha256", "controller_entrypoint_sha256",
        "inner_checker_sha256", "cache_manifest_tool_sha256",
        "image_context_builder_sha256", "build_input_manifest_sha256",
        "source_snapshot_manifest_sha256", "workspace_base_commit",
        "controller_uid", "worker_uid", "base_image_digest", "base_image_reference",
        "toolchain_release", "offline_toolchain_probe",
        "toolchain_probe_source_sha256", "lean_version", "lake_version",
        "python_version",
        "lake_cache_manifest_sha256", "checker_cache_root",
        "checker_cache_manifest_path", "docker_executable_sha256",
        "docker_runtime_identity", "image_build_log_sha256", "nonclaim",
    }
    required_toolchain = (
        "lean_version", "lake_version", "python_version",
    )
    toolchain_complete = all(
        isinstance(sbom.get(name), str)
        and bool(sbom[name].strip())
        and "UNSET" not in sbom[name]
        for name in required_toolchain
    )
    cache_manifest_sha256 = sbom.get("lake_cache_manifest_sha256")
    digest_fields = (
        "cache_manifest_tool_sha256", "image_context_builder_sha256",
        "build_input_manifest_sha256", "source_snapshot_manifest_sha256",
        "image_build_log_sha256", "docker_executable_sha256",
    )
    provenance_complete = all(
        isinstance(sbom.get(name), str)
        and re.fullmatch(r"[0-9a-f]{64}", sbom[name]) is not None
        for name in digest_fields
    )
    base_reference = sbom.get("base_image_reference", "")
    base_commit = sbom.get("workspace_base_commit", "")
    build_runtime = sbom.get("docker_runtime_identity")
    runtime_identity_complete = (
        isinstance(build_runtime, dict)
        and set(build_runtime) == {
            "runtime_id", "runtime_version", "runtime_signature_output_sha256",
            "runtime_version_output_sha256", "daemon_identity_output_sha256",
        }
        and build_runtime.get("runtime_id") == "docker"
        and isinstance(build_runtime.get("runtime_version"), str)
        and bool(build_runtime["runtime_version"].strip())
        and all(
            isinstance(build_runtime.get(name), str)
            and re.fullmatch(r"[0-9a-f]{64}", build_runtime[name]) is not None
            for name in (
                "runtime_signature_output_sha256", "runtime_version_output_sha256",
                "daemon_identity_output_sha256",
            )
        )
    )
    require(set(sbom) == expected_sbom_fields
            and sbom.get("schema_version") == 1
            and sbom.get("suite_id") == "ABRL-TARGET-DRIFT-V2"
            and isinstance(sbom.get("nonclaim"), str)
            and len(sbom["nonclaim"].strip()) >= 40
            and sbom.get("status") == "built_manifest_verified_probe_pending"
            and sbom.get("container_image_digest") == entry["container_image_digest"]
            and sbom.get("checker_image_recipe_sha256")
            == entry["checker_image_recipe_sha256"]
            and sbom.get("controller_entrypoint_sha256")
            == entry["controller_entrypoint_sha256"]
            and sbom.get("inner_checker_sha256")
            == inner_checker_sha256
            and sbom.get("controller_uid") == entry["controller_uid"]
            and sbom.get("worker_uid") == entry["worker_uid"]
            and re.fullmatch(r"sha256:[0-9a-f]{64}", sbom.get("base_image_digest", ""))
            and isinstance(base_reference, str)
            and re.fullmatch(r"[^\s@]+@sha256:[0-9a-f]{64}", base_reference)
            and base_reference.rsplit("@", 1)[1] == sbom.get("base_image_digest")
            and re.fullmatch(r"[0-9a-f]{40}", base_commit) is not None
            and (workspace_base_commit is None or base_commit == workspace_base_commit)
            and provenance_complete
            and runtime_identity_complete
            and sbom.get("cache_manifest_tool_sha256")
            == sha256_file(ROOT / "tools" / "target_drift_checker_cache_manifest.py")
            and sbom.get("image_context_builder_sha256")
            == sha256_file(ROOT / "tools" / "prepare_target_drift_checker_image.py")
            and (build_input is None
                 or sbom.get("build_input_manifest_sha256") == build_input_sha256)
            and (build_input is None
                 or sbom.get("source_snapshot_manifest_sha256")
                 == build_input.get("source_files_aggregate_sha256"))
            and (build_input is None
                 or sbom.get("base_image_reference") == build_input.get("lean_base_image"))
            and (cache_manifest is None
                 or cache_manifest.get("provenance", {}).get(
                     "build_input_manifest_sha256"
                 ) == build_input_sha256)
            and (cache_manifest is None
                 or sbom.get("lake_cache_manifest_sha256")
                 == entry.get("checker_cache_manifest_sha256"))
            and (build_log_sha256 is None
                 or sbom.get("image_build_log_sha256") == build_log_sha256)
            and sbom.get("docker_executable_sha256")
            == entry.get("container_runtime_executable_sha256")
            and (current_runtime_identity is None
                 or build_runtime == current_runtime_identity)
            and (expected_toolchain_release is None
                 or sbom.get("toolchain_release") == expected_toolchain_release)
            and sbom.get("offline_toolchain_probe")
            == "passed_network_none_as_worker"
            and sbom.get("toolchain_probe_source_sha256")
            == sha256_bytes(checker_image_builder.TOOLCHAIN_PROBE_SOURCE)
            and isinstance(sbom.get("toolchain_release"), str)
            and checker_image_builder.parse_lean_version_output(
                sbom.get("lean_version", "")
            ) == sbom["toolchain_release"]
            and checker_image_builder.parse_lake_lean_version_output(
                sbom.get("lake_version", "")
            ) == sbom["toolchain_release"]
            and toolchain_complete
            and isinstance(cache_manifest_sha256, str)
            and re.fullmatch(r"[0-9a-f]{64}", cache_manifest_sha256)
            and sbom.get("checker_cache_root") == entry["checker_cache_root"]
            == checker_launcher.CHECKER_CACHE_ROOT
            and sbom.get("checker_cache_manifest_path")
            == entry["checker_cache_manifest_path"]
            == checker_launcher.CHECKER_CACHE_MANIFEST_PATH
            and cache_manifest_sha256 == entry["checker_cache_manifest_sha256"],
            "checker image SBOM does not bind the image recipe/controller/inner checker")


def validate_checker_contract(config: dict[str, Any], require_hashes: bool) -> dict[str, Any]:
    entry = config["posthoc_checker"]
    if require_hashes:
        validate_checker_runtime_preflight(config)
    contract_path = resolve_repo_path(entry["contract"])
    require(contract_path.is_file(), "missing checker-sandbox contract")
    contract = load(contract_path)
    require(contract["suite_id"] == config["suite_id"],
            "checker-sandbox contract suite mismatch")
    require(contract["status"] == "interface_frozen_results_absent",
            "checker-sandbox contract must remain result-free")
    command = entry["sandbox_command_argv"]
    cleanup = entry["sandbox_cleanup_argv"]
    inspect = entry["sandbox_inspect_argv"]
    cleanup_by_label = entry["sandbox_cleanup_by_label_argv"]
    inspect_by_label = entry["sandbox_inspect_by_label_argv"]
    require(isinstance(command, list) and command
            and all(isinstance(item, str) and item for item in command),
            "checker sandbox_command_argv must be a nonempty string list")
    require(isinstance(cleanup, list) and cleanup
            and all(isinstance(item, str) and item for item in cleanup),
            "checker sandbox_cleanup_argv must be a nonempty string list")
    require(isinstance(inspect, list) and inspect
            and all(isinstance(item, str) and item for item in inspect),
            "checker sandbox_inspect_argv must be a nonempty string list")
    require(isinstance(cleanup_by_label, list) and cleanup_by_label
            and all(isinstance(item, str) and item for item in cleanup_by_label),
            "checker sandbox_cleanup_by_label_argv must be a nonempty string list")
    require(isinstance(inspect_by_label, list) and inspect_by_label
            and all(isinstance(item, str) and item for item in inspect_by_label),
            "checker sandbox_inspect_by_label_argv must be a nonempty string list")
    if not require_hashes:
        return contract
    require(entry["contract_sha256"] == sha256_file(contract_path),
            "checker-sandbox contract hash does not match")
    joined = "\0".join(command)
    for placeholder in contract["invocation"]["required_placeholders"]:
        require(placeholder in joined,
                f"checker sandbox command omits required placeholder {placeholder}")
    require(contract["invocation"]["cleanup_required_placeholder"]
            in "\0".join(cleanup), "checker cleanup command must bind the cidfile")
    require(contract["invocation"]["inspect_required_placeholder"]
            in "\0".join(inspect), "checker inspect command must bind the cidfile")
    require(contract["invocation"]["label_cleanup_required_placeholder"]
            in "\0".join(cleanup_by_label),
            "checker label cleanup command must bind the attempt label")
    require(contract["invocation"]["label_inspect_required_placeholder"]
            in "\0".join(inspect_by_label),
            "checker label inspect command must bind the attempt label")
    forbidden_detach = any(
        token == "-d" or token == "--detach" or token.startswith("--detach=")
        for token in command
    )
    require(not forbidden_detach,
            "checker sandbox command contains a forbidden detached-mode token")
    runtime_sha256 = checker_runtime_config_sha256(config)
    require(entry["runtime_config_sha256"] == runtime_sha256,
            "checker runtime-config digest does not match the complete runtime boundary")
    probe_path = resolve_repo_path(entry["isolation_probe_report"])
    require(probe_path.is_file(), "checker isolation-probe report is missing")
    require(entry["isolation_probe_report_sha256"] == sha256_file(probe_path),
            "checker isolation-probe report hash does not match")
    probe = load(probe_path)
    require(probe.get("suite_id") == config["suite_id"],
            "checker isolation-probe suite mismatch")
    require(probe.get("container_image_digest") == entry["container_image_digest"],
            "checker isolation-probe image differs from frozen config")
    require(probe.get("checker_runtime_config_sha256") == runtime_sha256,
            "checker isolation-probe does not bind the frozen runtime config")
    command_template_sha256 = sha256_bytes(canonical_json_bytes(command))
    require(probe.get("runtime_command_template_sha256") == command_template_sha256,
            "checker isolation-probe does not bind the sandbox command template")
    require(probe.get("probe_runner_sha256")
            == entry["isolation_probe_runner_sha256"],
            "checker isolation-probe does not bind the sealed probe runner")
    probe_artifacts = probe.get("artifact_manifest")
    require(isinstance(probe_artifacts, list) and probe_artifacts,
            "checker isolation-probe artifact manifest is empty")
    require(all(
        isinstance(item, dict)
        and set(item) == {"path", "bytes", "sha256"}
        and isinstance(item["path"], str)
        and isinstance(item["bytes"], int)
        and re.fullmatch(r"[0-9a-f]{64}", item["sha256"]) is not None
        for item in probe_artifacts
    ), "checker isolation-probe artifact manifest is malformed")
    artifact_root = resolve_repo_path(entry["isolation_probe_artifacts_dir"])
    artifact_payloads = probe_artifact_bytes(artifact_root)
    require(probe_artifact_manifest(artifact_payloads) == probe_artifacts,
            "checker isolation-probe artifact bytes differ from the report manifest")
    require(probe.get("checker_id") == entry["checker_id"]
            and probe.get("checker_version") == entry["checker_version"],
            "checker isolation-probe identity differs from frozen config")
    if entry["mode"] == "production":
        require(probe.get("status") == "passed",
                "production checker requires a passed isolation-probe report")
        require(probe.get("controller_entrypoint_sha256")
                == entry["controller_entrypoint_sha256"],
                "production probe does not bind the in-image controller bytes")
        required_probes = {
            "network_denied", "host_sentinel_protected", "operator_ground_truth_absent",
            "checker_outputs_not_worker_writable",
            "patched_source_and_controller_input_read_only",
            "mounted_inputs_and_cidfile_protected", "background_process_reaped",
        }
        results = probe.get("probes", {})
        require(required_probes == set(results)
                and all(results[name] is True for name in required_probes),
                "production checker isolation probes are incomplete or failed")
        nonce = probe.get("probe_nonce")
        attempt_label = probe.get("checker_attempt_label")
        require(isinstance(nonce, str) and re.fullmatch(r"[0-9a-f]{48}", nonce)
                and attempt_label == f"ABRL-PROBE-{nonce}",
                "production checker isolation probe nonce/label is malformed")
        require("host-observations.json" in artifact_payloads,
                "production checker probe omits host observations")
        host_observations = json.loads(artifact_payloads["host-observations.json"])
        require(host_observations.get("probe_nonce") == nonce
                and host_observations.get("checker_attempt_label") == attempt_label
                and host_observations.get("checker_runtime_config_sha256") == runtime_sha256
                and host_observations.get("container_image_digest")
                == entry["container_image_digest"]
                and host_observations.get("derived_probes") == results,
                "probe report differs from sealed host observations")
        require(rendered_argv_matches_template(
            command, host_observations.get("rendered_sandbox_argv", [])
        ), "probe host ledger did not execute the frozen sandbox argv template")
    else:
        require(entry["mode"] == "excluded_fixture",
                "checker mode must be production or excluded_fixture")
        require(probe.get("status") == "excluded_fixture_nonexperimental",
                "fixture checker requires a nonexperimental probe record")
    return contract


def validate_auxiliary_prompts(config: dict[str, Any], require_hashes: bool) -> None:
    entries = (
        (config["grading"]["grader_prompt"], config["grading"]["grader_prompt_sha256"],
         "grader prompt"),
        (config["wording_audit"]["text_only_prompt"],
         config["wording_audit"]["text_only_prompt_sha256"], "text-only audit prompt"),
    )
    for path_text, expected, label in entries:
        path = resolve_repo_path(path_text)
        require(path.is_file(), f"missing {label}")
        if require_hashes:
            require(expected == sha256_file(path), f"{label} hash does not match")


def execution_code_paths(config: dict[str, Any]) -> dict[str, Path]:
    paths = {
        "prepare_target_drift_execution.py": resolve_repo_path(
            config["sealed_agent_view"]["materializer"]
        ),
        "run_target_drift_execution.py": resolve_repo_path(
            config["sealed_agent_view"]["run_preparer"]
        ),
        "check_target_drift_run.py": resolve_repo_path(
            config["posthoc_checker"]["driver_path"]
        ),
        "check_target_drift_inner.py": resolve_repo_path(
            config["posthoc_checker"]["inner_checker_path"]
        ),
        "record_target_drift_checker_isolation_probe.py": resolve_repo_path(
            config["posthoc_checker"]["isolation_probe_runner_path"]
        ),
        "launch_target_drift_checker_container.py": resolve_repo_path(
            config["posthoc_checker"]["host_launcher_path"]
        ),
        "check_target_drift_container_controller.py": resolve_repo_path(
            config["posthoc_checker"]["controller_entrypoint_source"]
        ),
        "prepare_target_drift_grading.py": resolve_repo_path(
            config["grading"]["packet_materializer"]
        ),
        "assemble_target_drift_grades.py": resolve_repo_path(
            config["analysis"]["grade_assembler"]
        ),
        "analyze_target_drift_execution.py": resolve_repo_path(
            config["analysis"]["script"]
        ),
        "audit_target_drift_wording.py": resolve_repo_path(
            config["wording_audit"]["script"]
        ),
    }
    if config["execution_adapter"].get("entrypoint_path") != "UNSET":
        paths["execution_adapter_entrypoint"] = adapter_entrypoint_path(config)
    return paths


def validate_execution_code_hashes(config: dict[str, Any], require_hashes: bool) -> None:
    paths = execution_code_paths(config)
    require(all(path.is_file() for path in paths.values()),
            "one or more sealed execution-code files are missing")
    if not require_hashes:
        return
    expected = {
        "prepare_target_drift_execution.py": config["sealed_agent_view"]["materializer_sha256"],
        "run_target_drift_execution.py": config["sealed_agent_view"]["run_preparer_sha256"],
        "check_target_drift_run.py": config["posthoc_checker"]["driver_sha256"],
        "check_target_drift_inner.py": config["posthoc_checker"]["inner_checker_sha256"],
        "record_target_drift_checker_isolation_probe.py": config["posthoc_checker"][
            "isolation_probe_runner_sha256"
        ],
        "launch_target_drift_checker_container.py": config["posthoc_checker"][
            "host_launcher_sha256"
        ],
        "check_target_drift_container_controller.py": config["posthoc_checker"][
            "controller_entrypoint_source_sha256"
        ],
        "prepare_target_drift_grading.py": config["grading"]["packet_materializer_sha256"],
        "assemble_target_drift_grades.py": config["analysis"]["grade_assembler_sha256"],
        "analyze_target_drift_execution.py": config["analysis"]["script_sha256"],
        "audit_target_drift_wording.py": config["wording_audit"]["script_sha256"],
    }
    if "execution_adapter_entrypoint" in paths:
        expected["execution_adapter_entrypoint"] = config["execution_adapter"][
            "entrypoint_sha256"
        ]
    for name, path in paths.items():
        require(expected[name] == sha256_file(path), f"execution-code hash mismatch for {name}")


def checker_runtime_artifact_paths(config: dict[str, Any]) -> dict[str, Path]:
    checker = config["posthoc_checker"]
    if checker.get("mode") != "production":
        return {}
    return {
        "checker-image.Containerfile": resolve_repo_path(checker["checker_image_recipe"]),
        "checker-image-sbom.json": resolve_repo_path(checker["checker_image_sbom"]),
        "checker-image-build-input.json": resolve_repo_path(
            checker["checker_image_build_input_manifest"]
        ),
        "checker-cache-manifest.json": resolve_repo_path(
            checker["checker_cache_manifest_artifact"]
        ),
        "checker-image-build.log": resolve_repo_path(checker["checker_image_build_log"]),
    }


def validate_checker_runtime_artifacts(config: dict[str, Any]) -> None:
    paths = checker_runtime_artifact_paths(config)
    if not paths:
        return
    checker = config["posthoc_checker"]
    require(all(path.is_file() for path in paths.values()),
            "checker image provenance artifact is missing")
    require(sha256_file(paths["checker-image.Containerfile"])
            == checker["checker_image_recipe_sha256"],
            "checker image recipe artifact hash differs from config")
    require(sha256_file(paths["checker-image-sbom.json"])
            == checker["checker_image_sbom_sha256"],
            "checker image SBOM artifact hash differs from config")
    require(sha256_file(paths["checker-image-build-input.json"])
            == checker["checker_image_build_input_manifest_sha256"],
            "checker image build-input artifact hash differs from config")
    require(sha256_file(paths["checker-cache-manifest.json"])
            == checker["checker_cache_manifest_sha256"],
            "checker cache-manifest artifact hash differs from config")
    require(sha256_file(paths["checker-image-build.log"])
            == checker["checker_image_build_log_sha256"],
            "checker image build-log artifact hash differs from config")


def validate_frozen_choices(config: dict[str, Any]) -> None:
    def nonempty(value: Any, label: str, minimum: int = 1) -> None:
        require(isinstance(value, str) and len(value.strip()) >= minimum,
                f"{label} must be a substantive nonempty string")

    commit = config["orchestrator_commit"]
    require(isinstance(commit, str) and re.fullmatch(r"[0-9a-f]{40}", commit) is not None,
            "orchestrator_commit must be a lowercase full Git commit")
    model = config["model"]
    for field in (
        "provider", "model_id", "immutable_version", "api_or_runtime",
        "seed_semantics", "reasoning_effort", "service_tier",
        "sampling_control_semantics",
    ):
        nonempty(model[field], f"model.{field}")
    pricing = config["pricing"]
    require(pricing.get("currency") == "USD"
            and pricing.get("unit") == "per_million_tokens",
            "pricing must use USD per million tokens")
    for field in (
        "input_tokens", "cached_input_tokens", "cache_write_input_tokens",
        "output_tokens",
    ):
        require(isinstance(pricing[field], (int, float))
                and not isinstance(pricing[field], bool) and pricing[field] >= 0,
                f"pricing.{field} must be a nonnegative number")
    nonempty(pricing["source_url"], "pricing.source_url")
    nonempty(pricing["effective_date"], "pricing.effective_date")
    require(pricing["output_includes_reasoning_tokens"] is True,
            "pricing must explicitly count reasoning tokens inside output tokens")

    budgets = config["budgets_per_run"]
    for field in (
        "maximum_input_tokens", "maximum_output_tokens", "maximum_tool_calls",
        "maximum_build_attempts", "wall_clock_seconds",
    ):
        require(isinstance(budgets[field], int) and not isinstance(budgets[field], bool)
                and budgets[field] > 0, f"budgets_per_run.{field} must be a positive integer")
    require(isinstance(budgets["maximum_model_retries"], int)
            and not isinstance(budgets["maximum_model_retries"], bool)
            and budgets["maximum_model_retries"] >= 0,
            "budgets_per_run.maximum_model_retries must be a nonnegative integer")
    require(isinstance(budgets["maximum_cost_usd"], (int, float))
            and not isinstance(budgets["maximum_cost_usd"], bool)
            and budgets["maximum_cost_usd"] >= 0,
            "budgets_per_run.maximum_cost_usd must be nonnegative")

    retry = config["retry_policy"]
    require(retry["semantic_failure_retries"] == 0,
            "semantic failures must never be retried")
    require(isinstance(retry["infrastructure_retry_limit"], int)
            and not isinstance(retry["infrastructure_retry_limit"], bool)
            and retry["infrastructure_retry_limit"] >= 0,
            "infrastructure_retry_limit must be a nonnegative integer")
    require(retry["infrastructure_retry_limit"] <= budgets["maximum_model_retries"],
            "infrastructure retry limit exceeds the model-retry budget")
    nonempty(retry["infrastructure_failure_definition"],
             "retry_policy.infrastructure_failure_definition", 20)
    nonempty(retry["missing_run_policy"], "retry_policy.missing_run_policy", 20)

    randomization = config["randomization"]
    replicates = randomization["paired_replicates"]
    require(isinstance(replicates, list) and len(replicates) == 5
            and len(set(replicates)) == 5
            and all(isinstance(item, int) and not isinstance(item, bool) for item in replicates),
            "randomization.paired_replicates must contain five unique integers")
    require(isinstance(randomization["presentation_order_seed"], int)
            and not isinstance(randomization["presentation_order_seed"], bool),
            "presentation_order_seed must be an integer")

    wording = config["wording_audit"]
    nonempty(wording["text_only_model_id"], "wording_audit.text_only_model_id")
    require(isinstance(wording["text_only_accuracy"], (int, float))
            and not isinstance(wording["text_only_accuracy"], bool)
            and 0 <= wording["text_only_accuracy"] <= 1,
            "wording_audit.text_only_accuracy must lie in [0,1]")
    nonempty(wording["independent_blind_reviewer_id"],
             "wording_audit.independent_blind_reviewer_id")
    nonempty(wording["independent_blind_review_attestation"],
             "wording_audit.independent_blind_review_attestation", 20)

    adapter = config["execution_adapter"]
    for field in ("adapter_id", "adapter_version"):
        nonempty(adapter[field], f"execution_adapter.{field}")
    require(re.fullmatch(r"sha256:[0-9a-f]{64}",
                         adapter["container_or_sandbox_image_digest"]) is not None,
            "sandbox image digest must be sha256:<64 lowercase hex characters>")
    nonempty(adapter["budget_enforcement_attestation"],
             "execution_adapter.budget_enforcement_attestation", 20)
    nonempty(adapter["filesystem_network_process_attestation"],
             "execution_adapter.filesystem_network_process_attestation", 20)
    validate_provider_runtime(adapter["provider_runtime"], require_hash=True)
    adapter_identity = (adapter["adapter_id"] + " " + adapter["adapter_version"]).lower()
    if adapter["provider_runtime"]["kind"] == "excluded_fixture":
        require(any(marker in adapter_identity for marker in ("fixture", "excluded")),
                "excluded provider runtime requires an explicit fixture adapter identity")
    else:
        require(not any(marker in adapter_identity for marker in ("fixture", "excluded")),
                "codex_cli provider runtime cannot use a fixture adapter identity")
        require(retry["infrastructure_retry_limit"] == 0
                and budgets["maximum_model_retries"] == 0,
                "Codex CLI candidate requires zero adapter-level automatic CLI retries")
        require(retry["infrastructure_failure_definition"] == (
            "codex_cli_nonzero_exit_or_missing_thread_or_missing_terminal_usage_or_"
            "runtime_error_or_forbidden_tool_or_ambiguous_build_accounting"
        ), "Codex CLI infrastructure-failure definition must match the adapter enum")
        validate_codex_cli_configuration(adapter["provider_runtime"], model)

    checker = config["posthoc_checker"]
    for field in ("checker_id", "checker_version", "runtime_id", "runtime_version"):
        nonempty(checker[field], f"posthoc_checker.{field}")
    require(checker["mode"] in {"production", "excluded_fixture"},
            "posthoc_checker.mode must be production or excluded_fixture")
    require(re.fullmatch(r"sha256:[0-9a-f]{64}", checker["container_image_digest"])
            is not None, "checker image digest must be sha256:<64 lowercase hex>")
    require(re.fullmatch(r"[0-9a-f]{64}", checker["runtime_config_sha256"])
            is not None, "checker runtime_config_sha256 must be a lowercase SHA-256")
    require(isinstance(checker["inspect_absent_exit_code"], int)
            and not isinstance(checker["inspect_absent_exit_code"], bool)
            and 0 <= checker["inspect_absent_exit_code"] <= 255,
            "posthoc_checker.inspect_absent_exit_code must be an exit-code integer")
    nonempty(checker["filesystem_network_process_attestation"],
             "posthoc_checker.filesystem_network_process_attestation", 20)
    nonempty(checker["controller_worker_separation_attestation"],
             "posthoc_checker.controller_worker_separation_attestation", 20)
    checker_budgets = checker["budgets"]
    for field in (
        "wall_clock_seconds", "memory_mb", "pids_limit", "maximum_output_bytes",
        "maximum_response_bytes",
    ):
        require(isinstance(checker_budgets[field], int)
                and not isinstance(checker_budgets[field], bool)
                and checker_budgets[field] > 0,
                f"posthoc_checker.budgets.{field} must be a positive integer")
    require(isinstance(checker_budgets["cpus"], (int, float))
            and not isinstance(checker_budgets["cpus"], bool)
            and checker_budgets["cpus"] > 0,
            "posthoc_checker.budgets.cpus must be positive")
    worker_prefix = checker["worker_command_prefix"]
    require(isinstance(worker_prefix, list)
            and all(isinstance(item, str) and item.strip() for item in worker_prefix),
            "posthoc_checker.worker_command_prefix must be a string list")
    cache_prelude = checker["cache_prelude_argv"]
    require(isinstance(cache_prelude, list)
            and all(isinstance(item, str) and item.strip() for item in cache_prelude),
            "posthoc_checker.cache_prelude_argv must be an argv string list (possibly empty)")
    require(not any("{{" in item or "}}" in item for item in cache_prelude),
            "checker cache prelude must not contain unresolved placeholders")
    if checker["mode"] == "production":
        require(not cache_prelude,
                "production checker cache must come from the immutable image")
        require(bool(worker_prefix),
                "production checker requires a controller/worker command prefix")
        joined_identity = (checker["checker_id"] + " " + checker["checker_version"]).lower()
        require(not any(marker in joined_identity for marker in ("fake", "fixture", "excluded")),
                "production checker identity must not name a fixture")
    else:
        require("fixture" in checker["checker_id"].lower()
                or "excluded" in checker["checker_id"].lower(),
                "excluded checker mode requires an explicit fixture identity")

    grading = config["grading"]
    require(isinstance(grading["packet_order_seed"], int)
            and not isinstance(grading["packet_order_seed"], bool),
            "grading.packet_order_seed must be an integer")
    graders = grading["primary_grader_ids"]
    require(isinstance(graders, list) and len(graders) == 2
            and len(set(graders)) == 2
            and all(isinstance(item, str) and item.strip() for item in graders),
            "grading.primary_grader_ids must contain two unique nonempty strings")
    nonempty(grading["adjudicator_id"], "grading.adjudicator_id")
    require(grading["adjudicator_id"] not in graders,
            "adjudicator must be independent of both primary graders")
    nonempty(grading["grader_blinding_attestation"],
             "grading.grader_blinding_attestation", 20)

    analysis = config["analysis"]
    require(isinstance(analysis["bootstrap_seed"], int)
            and not isinstance(analysis["bootstrap_seed"], bool),
            "analysis.bootstrap_seed must be an integer")
    require(isinstance(analysis["bootstrap_replicates"], int)
            and analysis["bootstrap_replicates"] >= 1000,
            "analysis.bootstrap_replicates must be at least 1000")
    require(analysis["permutation_replicates"] == 32768,
            "analysis.permutation_replicates must enumerate all 15-unit sign flips")


def digest_components(
    config: dict[str, Any],
    agent_cases: dict[str, Any],
    run_manifest: dict[str, Any],
    challenges_bytes: bytes,
    paired_requirements_bytes: bytes,
    protocol_bytes: bytes,
    source_manifest_bytes: bytes,
    source_packet_bytes: dict[str, bytes],
    rubric_bytes: bytes,
    resource_policy_bytes: bytes,
    adapter_contract_bytes: bytes,
    checker_contract_bytes: bytes,
    checker_probe_bytes: bytes,
    checker_probe_artifact_bytes: dict[str, bytes],
    checker_runtime_artifact_bytes: dict[str, bytes],
    grader_prompt_bytes: bytes,
    text_only_prompt_bytes: bytes,
    prompt_bytes: dict[str, bytes],
    execution_code_bytes: dict[str, bytes],
) -> dict[str, bytes]:
    components = {
        "agent_cases.json": canonical_json_bytes(agent_cases),
        "run_manifest.json": canonical_json_bytes(run_manifest),
        "execution_config.normalized.json": canonical_json_bytes(
            normalized_config_for_digest(config)
        ),
        "operator_challenges.json": challenges_bytes,
        "paired_requirements.json": paired_requirements_bytes,
        "protocol.json": protocol_bytes,
        "source_manifest.json": source_manifest_bytes,
        "grading_rubric.json": rubric_bytes,
        "resource_policy.json": resource_policy_bytes,
        "adapter_contract.json": adapter_contract_bytes,
        "checker_sandbox_contract.json": checker_contract_bytes,
        "checker_isolation_probe.json": checker_probe_bytes,
        "grader_prompt.md": grader_prompt_bytes,
        "text_only_audit_prompt.md": text_only_prompt_bytes,
    }
    components.update({
        f"checker_isolation_probe_artifacts/{name}": payload
        for name, payload in checker_probe_artifact_bytes.items()
    })
    components.update({
        f"checker_runtime_artifacts/{name}": payload
        for name, payload in checker_runtime_artifact_bytes.items()
    })
    components.update({
        f"source_packets/{name}": payload
        for name, payload in source_packet_bytes.items()
    })
    components.update({
        f"prompt_templates/{condition}.md": prompt_bytes[condition]
        for condition in CONDITIONS
    })
    components.update({
        f"execution_code/{name}": payload
        for name, payload in execution_code_bytes.items()
    })
    return components


def check_template(config_path: Path) -> None:
    config = load(config_path)
    require(config["suite_id"] in {"ABRL-TARGET-DRIFT-V1", "ABRL-TARGET-DRIFT-V2"},
            "wrong suite id")
    require(config["execution_status"] == "template_unfrozen",
            "checked template must remain template_unfrozen")
    require(bool(config["unresolved_fields"]), "template must enumerate unresolved fields")
    missing = unset_paths(config)
    require(bool(missing), "template unexpectedly contains no UNSET fields")
    validate_prompt_templates(config, require_hashes=False)
    if "resource_policy" in config:
        validate_resource_policy(config, require_hash=False)
        validate_paired_requirements(config)
        validate_adapter_contract(config, require_hash=False)
        validate_checker_contract(config, require_hashes=False)
        validate_auxiliary_prompts(config, require_hashes=False)
        validate_execution_code_hashes(config, require_hashes=False)
    else:
        require(config["suite_id"] == "ABRL-TARGET-DRIFT-V1",
                "v2 template must define a resource policy")
    sources = load(resolve_repo_path(config["source_files_manifest"]))
    require(sources["status"] == "template_unfrozen",
            "source manifest must remain template_unfrozen")
    require(len(sources["sources"]) == 4, "expected four frozen-source entries")
    require(
        all(
            isinstance(source["sha256"], str)
            and len(source["sha256"]) == 64
            and all(character in "0123456789abcdef" for character in source["sha256"])
            for source in sources["sources"]
        ),
        "every source template entry must carry a lowercase SHA-256",
    )
    rubric = load(resolve_repo_path(config["grading"]["rubric"]))
    require(rubric["no_results"] is True, "grading rubric must remain result-free")
    print(
        "target-drift execution template valid but not ready: "
        f"{len(missing)} machine fields plus named human/provenance choices remain UNSET"
    )


def verify_sources(source_manifest: dict[str, Any]) -> dict[str, dict[str, Any]]:
    require(source_manifest["status"] == "frozen_ready",
            "source manifest must be frozen_ready")
    by_id: dict[str, dict[str, Any]] = {}
    for source in source_manifest["sources"]:
        source_id = source["source_id"]
        require(source_id not in by_id, f"duplicate source id {source_id}")
        source_path = resolve_repo_path(source["local_path"])
        require(source_path.is_file(), f"source file missing for {source_id}")
        require(source["sha256"] == sha256_file(source_path),
                f"source hash mismatch for {source_id}")
        by_id[source_id] = {**source, "resolved_path": str(source_path.resolve())}
    return by_id


def sanitized_case(
    case: dict[str, Any], source: dict[str, Any], paired: dict[str, str], template: str
) -> dict[str, Any]:
    return {
        "case_id": case["id"],
        "source_id": case["source_id"],
        "source_sha256": source["sha256"],
        "source_locator": case["source_locator"],
        "source_packet_name": f"{case['source_id']}.pdf",
        "source_faithful_requirement": render_paired_requirement(
            template, paired["field"], paired["source_faithful_value"]
        ),
        "injected_drift_requirement": render_paired_requirement(
            template, paired["field"], paired["injected_drift_value"]
        ),
        "task": (
            "Implement the proposed Lean requirement under the assigned workflow. "
            "Preserve the frozen source; explicitly reject or amend any incompatible request."
        ),
    }


def sanitized_case_v1(case: dict[str, Any], source: dict[str, Any]) -> dict[str, Any]:
    return {
        "case_id": case["id"],
        "source_id": case["source_id"],
        "source_sha256": source["sha256"],
        "source_locator": case["source_locator"],
        "source_packet_path": source["resolved_path"],
        "proposed_requirement": case["injected_drift"],
        "task": (
            "Implement the proposed Lean requirement under the assigned workflow. "
            "Preserve the frozen source; explicitly reject or amend any incompatible request."
        ),
    }


def requirement_variant(case_index: int, seed_index: int) -> str:
    return "injected_drift" if (case_index + seed_index) % 2 == 0 else "source_faithful"


def materialize(config_path: Path, output_dir: Path) -> None:
    config = load(config_path)
    require(config["execution_status"] in {"preseal_ready", "frozen_ready"},
            "execution config must be preseal_ready or frozen_ready")
    missing = unset_paths(config)
    if config["execution_status"] == "preseal_ready":
        require(missing == ["sealed_agent_view.aggregate_sha256"],
                "preseal config may leave only sealed_agent_view.aggregate_sha256 UNSET; found: "
                + ", ".join(missing))
    else:
        require(not missing,
                "frozen execution config still contains UNSET fields: " + ", ".join(missing))
    require(not output_dir.exists(), "output directory already exists; choose a new sealed directory")
    validate_frozen_choices(config)
    validate_prompt_templates(config, require_hashes=True)
    require("resource_policy" in config,
            "legacy v1 template cannot be materialized by the strengthened sealer; use v2")
    validate_resource_policy(config, require_hash=True)
    validate_adapter_contract(config, require_hash=True)
    validate_checker_contract(config, require_hashes=True)
    validate_auxiliary_prompts(config, require_hashes=True)
    validate_execution_code_hashes(config, require_hashes=True)

    current_commit = subprocess.check_output(
        ["git", "rev-parse", "HEAD"], cwd=ROOT, text=True
    ).strip()
    configured_commit = config.get("orchestrator_commit", config.get("repository_commit"))
    require(configured_commit == current_commit,
            "orchestrator/repository commit differs from frozen execution config")
    if config.get("orchestrator_clean_tree_required", False):
        status = subprocess.check_output(
            ["git", "status", "--porcelain"], cwd=ROOT, text=True
        ).strip()
        require(not status, "orchestrator worktree must be fully clean before sealing")
    if "workspace_base_commit" in config:
        subprocess.run(
            ["git", "cat-file", "-e", f"{config['workspace_base_commit']}^{{commit}}"],
            cwd=ROOT,
            check=True,
        )

    source_manifest = load(resolve_repo_path(config["source_files_manifest"]))
    sources = verify_sources(source_manifest)
    challenge_path = resolve_repo_path(
        config.get("challenge_manifest", str(config_path.parent / "challenges.json"))
    )
    challenges_bytes = challenge_path.read_bytes()
    challenges_payload = json.loads(challenges_bytes.decode("utf-8"))
    challenges = challenges_payload["cases"]
    paired_payload = validate_paired_requirements(config, challenges)
    paired_requirements_path = resolve_repo_path(config["paired_requirements"])
    paired_requirements_bytes = paired_requirements_path.read_bytes()
    paired_by_id = {entry["case_id"]: entry for entry in paired_payload["cases"]}
    require({case["source_id"] for case in challenges} == set(sources),
            "source manifest does not exactly cover challenge sources")
    require(all(case["source_sha256"] == sources[case["source_id"]]["sha256"]
                for case in challenges),
            "source manifest hashes differ from the frozen challenge bank")

    replicate_key = (
        "paired_replicates" if "paired_replicates" in config["randomization"]
        else "paired_seeds"
    )
    seeds = config["randomization"][replicate_key]
    require(isinstance(seeds, list) and len(seeds) == 5,
            "paired_seeds must contain exactly five entries")
    require(len(set(seeds)) == 5, "paired seeds must be unique")
    require(all(isinstance(seed, int) for seed in seeds), "paired seeds must be integers")

    is_v2 = config["suite_id"] == "ABRL-TARGET-DRIFT-V2"
    if is_v2:
        agent_cases = [
            sanitized_case(
                case,
                sources[case["source_id"]],
                paired_by_id[case["id"]],
                paired_payload["common_template"],
            )
            for case in challenges
        ]
    else:
        agent_cases = [sanitized_case_v1(case, sources[case["source_id"]]) for case in challenges]
    forbidden = {"faithful_contract", "expected_affected_fields", "drift_class", "stratum"}
    require(all(not (forbidden & case.keys()) for case in agent_cases),
            "agent view leaks adjudication fields")

    runs = []
    for case_index, case in enumerate(agent_cases):
        for seed_index, seed in enumerate(seeds):
            variant = requirement_variant(case_index, seed_index) if is_v2 else "injected_drift"
            proposed_requirement = (
                case[f"{variant}_requirement"] if is_v2 else case["proposed_requirement"]
            )
            block = []
            for condition in CONDITIONS:
                block.append({
                    "run_id": f"{case['case_id']}--{condition}--replicate-{seed}",
                    "case_id": case["case_id"],
                    "condition": condition,
                    "replicate": seed,
                    "prompt_template": config["conditions"][condition]["prompt_template"],
                    "requirement_variant": variant,
                    "proposed_requirement": proposed_requirement,
                    "status": "sealed_unrun",
                })
            random.Random(config["randomization"]["presentation_order_seed"] + case_index * 31 + seed_index).shuffle(block)
            runs.extend(block)
    require(len(runs) == 450, "materialized run count must be 450")
    if is_v2:
        require(sum(run["requirement_variant"] == "source_faithful" for run in runs) == 225,
                "expected 225 source-faithful condition runs")
        require(sum(run["requirement_variant"] == "injected_drift" for run in runs) == 225,
                "expected 225 injected-drift condition runs")
    rng = random.Random(config["randomization"]["presentation_order_seed"])
    blocks = [runs[index:index + 3] for index in range(0, len(runs), 3)]
    rng.shuffle(blocks)
    runs = [run for block in blocks for run in block]
    for order, run in enumerate(runs):
        run["presentation_order"] = order

    agent_cases_payload = {
        "schema_version": 1,
        "suite_id": config["suite_id"],
        "visibility": "sealed operator input; evaluated agents receive one run-local requirement only",
        "cases": agent_cases,
    }
    run_manifest_payload = {
        "schema_version": 1,
        "suite_id": config["suite_id"],
        "execution_status": "sealed_unrun",
        "common_deliverables": [
            "Lean diff",
            "build log",
            "machine-readable final status",
            "hash-bound workflow-compliance record",
            "source amendment if any",
            "concise explanation",
        ],
        "runs": runs,
    }

    source_manifest_path = resolve_repo_path(config["source_files_manifest"])
    protocol_path = resolve_repo_path(config["protocol"])
    require(protocol_path.is_file(), "missing v2 protocol")
    rubric_path = resolve_repo_path(config["grading"]["rubric"])
    resource_policy_path = resolve_repo_path(config["resource_policy"])
    adapter_contract_path = resolve_repo_path(config["execution_adapter"]["contract"])
    checker_contract_path = resolve_repo_path(config["posthoc_checker"]["contract"])
    checker_probe_path = resolve_repo_path(config["posthoc_checker"]["isolation_probe_report"])
    checker_probe_artifact_root = resolve_repo_path(
        config["posthoc_checker"]["isolation_probe_artifacts_dir"]
    )
    grader_prompt_path = resolve_repo_path(config["grading"]["grader_prompt"])
    text_only_prompt_path = resolve_repo_path(config["wording_audit"]["text_only_prompt"])
    prompt_paths = {
        condition: resolve_repo_path(config["conditions"][condition]["prompt_template"])
        for condition in CONDITIONS
    }
    sealed_source_manifest = {
        "schema_version": source_manifest["schema_version"],
        "suite_id": source_manifest["suite_id"],
        "status": "sealed_ready",
        "sources": [
            {
                **{key: value for key, value in source.items() if key != "local_path"},
                "sealed_path": f"source_packets/{source['source_id']}.pdf",
            }
            for source in source_manifest["sources"]
        ],
    }
    source_manifest_bytes = canonical_json_bytes(sealed_source_manifest)
    source_packet_bytes = {
        f"{source_id}.pdf": Path(source["resolved_path"]).read_bytes()
        for source_id, source in sources.items()
    }
    protocol_bytes = protocol_path.read_bytes()
    rubric_bytes = rubric_path.read_bytes()
    resource_policy_bytes = resource_policy_path.read_bytes()
    adapter_contract_bytes = adapter_contract_path.read_bytes()
    checker_contract_bytes = checker_contract_path.read_bytes()
    checker_probe_bytes = checker_probe_path.read_bytes()
    checker_probe_artifacts = probe_artifact_bytes(checker_probe_artifact_root)
    validate_checker_runtime_artifacts(config)
    checker_runtime_artifacts = {
        name: path.read_bytes()
        for name, path in checker_runtime_artifact_paths(config).items()
    }
    grader_prompt_bytes = grader_prompt_path.read_bytes()
    text_only_prompt_bytes = text_only_prompt_path.read_bytes()
    prompt_bytes = {condition: path.read_bytes() for condition, path in prompt_paths.items()}
    code_paths = execution_code_paths(config)
    execution_code_bytes = {
        name: path.read_bytes() for name, path in code_paths.items()
    }
    components = digest_components(
        config,
        agent_cases_payload,
        run_manifest_payload,
        challenges_bytes,
        paired_requirements_bytes,
        protocol_bytes,
        source_manifest_bytes,
        source_packet_bytes,
        rubric_bytes,
        resource_policy_bytes,
        adapter_contract_bytes,
        checker_contract_bytes,
        checker_probe_bytes,
        checker_probe_artifacts,
        checker_runtime_artifacts,
        grader_prompt_bytes,
        text_only_prompt_bytes,
        prompt_bytes,
        execution_code_bytes,
    )
    aggregate, component_manifest = aggregate_digest(components)

    output_dir.mkdir(parents=True)
    dump(output_dir / "agent_cases.json", agent_cases_payload)
    dump(output_dir / "run_manifest.json", run_manifest_payload)
    dump(output_dir / "execution_config.json", config)
    (output_dir / "operator_challenges.json").write_bytes(challenges_bytes)
    (output_dir / "paired_requirements.json").write_bytes(paired_requirements_bytes)
    (output_dir / "protocol.json").write_bytes(protocol_bytes)
    (output_dir / "source_manifest.json").write_bytes(source_manifest_bytes)
    source_output = output_dir / "source_packets"
    source_output.mkdir()
    for name, payload in source_packet_bytes.items():
        (source_output / name).write_bytes(payload)
    (output_dir / "grading_rubric.json").write_bytes(rubric_bytes)
    (output_dir / "resource_policy.json").write_bytes(resource_policy_bytes)
    (output_dir / "adapter_contract.json").write_bytes(adapter_contract_bytes)
    (output_dir / "checker_sandbox_contract.json").write_bytes(checker_contract_bytes)
    (output_dir / "checker_isolation_probe.json").write_bytes(checker_probe_bytes)
    probe_output = output_dir / "checker_isolation_probe_artifacts"
    probe_output.mkdir()
    for name, payload in checker_probe_artifacts.items():
        target = probe_output / name
        target.parent.mkdir(parents=True, exist_ok=True)
        target.write_bytes(payload)
    runtime_artifact_output = output_dir / "checker_runtime_artifacts"
    runtime_artifact_output.mkdir()
    for name, payload in checker_runtime_artifacts.items():
        (runtime_artifact_output / name).write_bytes(payload)
    (output_dir / "grader_prompt.md").write_bytes(grader_prompt_bytes)
    (output_dir / "text_only_audit_prompt.md").write_bytes(text_only_prompt_bytes)
    prompt_output = output_dir / "prompt_templates"
    prompt_output.mkdir()
    for condition, payload in prompt_bytes.items():
        (prompt_output / f"{condition}.md").write_bytes(payload)
    code_output = output_dir / "execution_code"
    code_output.mkdir()
    for name, payload in execution_code_bytes.items():
        (code_output / name).write_bytes(payload)
    dump(output_dir / "digest_manifest.json", {
        "schema_version": 1,
        "suite_id": config["suite_id"],
        "aggregate_algorithm": "sha256(length-prefixed sorted name/payload components)",
        "config_normalization": "execution_status is frozen_ready, aggregate_sha256 is UNSET, source_files_manifest is SEALED/source_manifest.json, and unresolved_fields is empty",
        "components": component_manifest,
    })
    (output_dir / "aggregate.sha256").write_text(aggregate + "\n", encoding="ascii")
    if config["execution_status"] == "preseal_ready":
        print(
            "presealed target-drift pack: 30 cases, 450 runs, "
            f"sha256={aggregate}; record this digest and rerun from a frozen_ready config"
        )
    else:
        require(config["sealed_agent_view"]["aggregate_sha256"] == aggregate,
                "configured aggregate digest differs from the sealed agent view")
        print(f"sealed target-drift execution pack: 30 cases, 450 runs, sha256={aggregate}")


def verify_pack(pack_dir: Path) -> None:
    require(pack_dir.is_dir(), "sealed pack directory is missing")
    config = load(pack_dir / "execution_config.json")
    require(config["execution_status"] in {"preseal_ready", "frozen_ready"},
            "pack execution status must be preseal_ready or frozen_ready")
    agent_cases = load(pack_dir / "agent_cases.json")
    run_manifest = load(pack_dir / "run_manifest.json")
    prompt_bytes = {
        condition: (pack_dir / "prompt_templates" / f"{condition}.md").read_bytes()
        for condition in CONDITIONS
    }
    execution_code_bytes = {
        path.name: path.read_bytes()
        for path in sorted((pack_dir / "execution_code").iterdir())
        if path.is_file()
    }
    require(set(execution_code_bytes) == set(execution_code_paths(config)),
            "sealed pack execution-code file set differs from frozen config")
    for condition in CONDITIONS:
        require(
            config["conditions"][condition]["prompt_sha256"]
            == sha256_bytes(prompt_bytes[condition]),
            f"sealed prompt hash mismatch for {condition}",
        )
    require(
        config["resource_policy_sha256"]
        == sha256_bytes((pack_dir / "resource_policy.json").read_bytes()),
        "sealed resource-policy hash mismatch",
    )
    require(
        config["execution_adapter"]["contract_sha256"]
        == sha256_bytes((pack_dir / "adapter_contract.json").read_bytes()),
        "sealed adapter-contract hash mismatch",
    )
    require(
        config["execution_adapter"]["entrypoint_sha256"]
        == sha256_bytes(
            (pack_dir / "execution_code" / "execution_adapter_entrypoint").read_bytes()
        ),
        "sealed execution-adapter entrypoint hash mismatch",
    )
    require(
        config["posthoc_checker"]["contract_sha256"]
        == sha256_bytes((pack_dir / "checker_sandbox_contract.json").read_bytes()),
        "sealed checker-sandbox contract hash mismatch",
    )
    require(
        config["posthoc_checker"]["isolation_probe_report_sha256"]
        == sha256_bytes((pack_dir / "checker_isolation_probe.json").read_bytes()),
        "sealed checker isolation-probe hash mismatch",
    )
    require(
        config["grading"]["grader_prompt_sha256"]
        == sha256_bytes((pack_dir / "grader_prompt.md").read_bytes()),
        "sealed grader-prompt hash mismatch",
    )
    require(
        config["wording_audit"]["text_only_prompt_sha256"]
        == sha256_bytes((pack_dir / "text_only_audit_prompt.md").read_bytes()),
        "sealed text-only prompt hash mismatch",
    )
    challenges = load(pack_dir / "operator_challenges.json")
    paired_requirements = load(pack_dir / "paired_requirements.json")
    protocol = load(pack_dir / "protocol.json")
    source_manifest = load(pack_dir / "source_manifest.json")
    rubric = load(pack_dir / "grading_rubric.json")
    require(
        all(
            value["suite_id"] == config["suite_id"]
            for value in (agent_cases, run_manifest, protocol, source_manifest, rubric, paired_requirements)
        ),
        "sealed component suite identifiers differ",
    )
    require(len(challenges["cases"]) == len(agent_cases["cases"]) == 30,
            "sealed challenge/case banks must each contain thirty cases")
    expected_source_names = {
        Path(source["sealed_path"]).name for source in source_manifest["sources"]
    }
    source_packet_bytes = {
        path.name: path.read_bytes()
        for path in sorted((pack_dir / "source_packets").iterdir())
        if path.is_file()
    }
    packed_probe = load(pack_dir / "checker_isolation_probe.json")
    packed_probe_artifacts = probe_artifact_bytes(
        pack_dir / "checker_isolation_probe_artifacts"
    )
    packed_runtime_artifact_root = pack_dir / "checker_runtime_artifacts"
    packed_runtime_artifacts = {
        path.name: path.read_bytes()
        for path in sorted(packed_runtime_artifact_root.iterdir())
        if path.is_file()
    }
    expected_runtime_artifacts = checker_runtime_artifact_paths(config)
    require(set(packed_runtime_artifacts) == set(expected_runtime_artifacts),
            "sealed checker runtime-artifact set differs from frozen config")
    if expected_runtime_artifacts:
        require(sha256_bytes(packed_runtime_artifacts["checker-image.Containerfile"])
                == config["posthoc_checker"]["checker_image_recipe_sha256"],
                "sealed checker image recipe hash differs from config")
        require(sha256_bytes(packed_runtime_artifacts["checker-image-sbom.json"])
                == config["posthoc_checker"]["checker_image_sbom_sha256"],
                "sealed checker image SBOM hash differs from config")
        require(sha256_bytes(packed_runtime_artifacts["checker-image-build-input.json"])
                == config["posthoc_checker"][
                    "checker_image_build_input_manifest_sha256"
                ], "sealed checker build-input hash differs from config")
        require(sha256_bytes(packed_runtime_artifacts["checker-cache-manifest.json"])
                == config["posthoc_checker"]["checker_cache_manifest_sha256"],
                "sealed checker cache-manifest hash differs from config")
        require(sha256_bytes(packed_runtime_artifacts["checker-image-build.log"])
                == config["posthoc_checker"]["checker_image_build_log_sha256"],
                "sealed checker image build-log hash differs from config")
    require(probe_artifact_manifest(packed_probe_artifacts)
            == packed_probe.get("artifact_manifest"),
            "sealed checker isolation-probe artifacts differ from the report manifest")
    require(set(source_packet_bytes) == expected_source_names,
            "sealed source-packet file set differs from source manifest")
    require(all(
        sha256_bytes(source_packet_bytes[Path(source["sealed_path"]).name]) == source["sha256"]
        for source in source_manifest["sources"]
    ), "sealed source-packet bytes differ from source manifest hashes")
    source_hashes = {
        source["source_id"]: source["sha256"]
        for source in source_manifest["sources"]
    }
    require(all(case["source_sha256"] == source_hashes.get(case["source_id"])
                for case in challenges["cases"]),
            "sealed source hashes differ from operator challenge ground truth")
    require(len(run_manifest["runs"]) == 450,
            "sealed run manifest must contain 450 runs")
    require(all(run["status"] == "sealed_unrun" for run in run_manifest["runs"]),
            "sealed run manifest contains a non-unrun result")
    components = digest_components(
        config,
        agent_cases,
        run_manifest,
        (pack_dir / "operator_challenges.json").read_bytes(),
        (pack_dir / "paired_requirements.json").read_bytes(),
        (pack_dir / "protocol.json").read_bytes(),
        (pack_dir / "source_manifest.json").read_bytes(),
        source_packet_bytes,
        (pack_dir / "grading_rubric.json").read_bytes(),
        (pack_dir / "resource_policy.json").read_bytes(),
        (pack_dir / "adapter_contract.json").read_bytes(),
        (pack_dir / "checker_sandbox_contract.json").read_bytes(),
        (pack_dir / "checker_isolation_probe.json").read_bytes(),
        packed_probe_artifacts,
        packed_runtime_artifacts,
        (pack_dir / "grader_prompt.md").read_bytes(),
        (pack_dir / "text_only_audit_prompt.md").read_bytes(),
        prompt_bytes,
        execution_code_bytes,
    )
    aggregate, component_manifest = aggregate_digest(components)
    recorded_aggregate = (pack_dir / "aggregate.sha256").read_text(encoding="ascii").strip()
    require(recorded_aggregate == aggregate, "sealed pack aggregate digest mismatch")
    recorded_manifest = load(pack_dir / "digest_manifest.json")
    require(recorded_manifest["components"] == component_manifest,
            "sealed pack component manifest mismatch")
    if config["execution_status"] == "frozen_ready":
        require(config["sealed_agent_view"]["aggregate_sha256"] == aggregate,
                "frozen config aggregate does not match the pack")
    else:
        require(config["sealed_agent_view"]["aggregate_sha256"] == "UNSET",
            "preseal config must leave its aggregate field UNSET")
    expected_code_hashes = {
        "prepare_target_drift_execution.py": config["sealed_agent_view"]["materializer_sha256"],
        "run_target_drift_execution.py": config["sealed_agent_view"]["run_preparer_sha256"],
        "check_target_drift_run.py": config["posthoc_checker"]["driver_sha256"],
        "check_target_drift_inner.py": config["posthoc_checker"]["inner_checker_sha256"],
        "record_target_drift_checker_isolation_probe.py": config["posthoc_checker"][
            "isolation_probe_runner_sha256"
        ],
        "launch_target_drift_checker_container.py": config["posthoc_checker"][
            "host_launcher_sha256"
        ],
        "check_target_drift_container_controller.py": config["posthoc_checker"][
            "controller_entrypoint_sha256"
        ],
        "prepare_target_drift_grading.py": config["grading"]["packet_materializer_sha256"],
        "assemble_target_drift_grades.py": config["analysis"]["grade_assembler_sha256"],
        "analyze_target_drift_execution.py": config["analysis"]["script_sha256"],
        "audit_target_drift_wording.py": config["wording_audit"]["script_sha256"],
    }
    if config["execution_status"] == "frozen_ready":
        for name, expected in expected_code_hashes.items():
            require(name in execution_code_bytes, f"sealed pack omits execution code {name}")
            require(expected == sha256_bytes(execution_code_bytes[name]),
                    f"sealed pack execution-code hash mismatch for {name}")
    print(
        f"verified {config['execution_status']} target-drift pack: "
        f"{len(agent_cases['cases'])} cases, {len(run_manifest['runs'])} runs, sha256={aggregate}"
    )


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "--config",
        type=Path,
        default=SUITE / "execution-template.json",
    )
    action = parser.add_mutually_exclusive_group(required=True)
    action.add_argument("--check-template", action="store_true")
    action.add_argument("--materialize", type=Path)
    action.add_argument("--verify-pack", type=Path)
    args = parser.parse_args()
    if args.check_template:
        check_template(args.config)
    elif args.materialize is not None:
        materialize(args.config, args.materialize.resolve())
    else:
        verify_pack(args.verify_pack.resolve())


if __name__ == "__main__":
    main()
