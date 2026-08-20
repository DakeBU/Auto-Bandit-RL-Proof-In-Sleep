#!/usr/bin/env python3
"""Fill derived v2 hashes for preseal, then bind the verified preseal digest."""

from __future__ import annotations

import argparse
import json
import subprocess
import sys
from pathlib import Path
from typing import Any


TOOLS = Path(__file__).resolve().parent
ROOT = TOOLS.parent
sys.path.insert(0, str(TOOLS))

import prepare_target_drift_execution as prepare  # noqa: E402
import launch_target_drift_checker_container as checker_launcher  # noqa: E402


def load(path: Path) -> dict[str, Any]:
    return json.loads(path.read_text(encoding="utf-8"))


def dump_new(path: Path, value: Any) -> None:
    prepare.require(not path.exists(), f"refusing to overwrite {path}")
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(
        json.dumps(value, indent=2, sort_keys=True, ensure_ascii=False) + "\n",
        encoding="utf-8",
    )


def bind_runtime(draft_path: Path, runtime_executable: Path, output: Path) -> None:
    """Derive the exact production runtime boundary before the live probe."""
    config = load(draft_path)
    prepare.require(config["suite_id"] == "ABRL-TARGET-DRIFT-V2",
                    "runtime binding requires v2")
    prepare.require(config["execution_status"] == "template_unfrozen",
                    "runtime binding input must be template_unfrozen")
    checker = config["posthoc_checker"]
    prepare.require(checker.get("mode") == "production",
                    "runtime binding is only valid for the production checker")
    build_input_candidate = prepare.resolve_repo_path(
        checker["checker_image_build_input_manifest"]
    ).resolve()
    context_root = build_input_candidate.parent
    # The image and runtime seal use the canonical LF bytes from the prepared,
    # Git-validated context, never checkout-dependent CRLF presentations.
    checker["checker_image_recipe"] = str(context_root / "Containerfile")
    checker["inner_checker_path"] = str(
        context_root / "check_target_drift_inner.py"
    )
    checker["controller_entrypoint_source"] = str(
        context_root / "check_target_drift_container_controller.py"
    )

    launcher_path = prepare.resolve_repo_path(checker["host_launcher_path"]).resolve()
    checker["driver_sha256"] = prepare.sha256_file(
        prepare.resolve_repo_path(checker["driver_path"])
    )
    checker["inner_checker_sha256"] = prepare.sha256_file(
        prepare.resolve_repo_path(checker["inner_checker_path"])
    )
    checker["isolation_probe_runner_sha256"] = prepare.sha256_file(
        prepare.resolve_repo_path(checker["isolation_probe_runner_path"])
    )
    checker["contract_sha256"] = prepare.sha256_file(
        prepare.resolve_repo_path(checker["contract"])
    )
    host_python = Path(sys.executable).resolve()
    runtime = runtime_executable.resolve()
    prepare.require(runtime == checker_launcher.canonical_docker_executable(),
                    "runtime executable must equal the canonical Docker CLI on PATH")
    checker["host_launcher_sha256"] = prepare.sha256_file(launcher_path)
    checker["host_python_executable"] = str(host_python)
    checker["host_python_executable_sha256"] = prepare.sha256_file(host_python)
    checker["container_runtime_kind"] = "docker"
    checker["container_runtime_executable"] = str(runtime)
    checker["container_runtime_executable_sha256"] = prepare.sha256_file(runtime)
    identity = checker_launcher.runtime_identity(runtime)
    checker["runtime_id"] = identity["runtime_id"]
    checker["runtime_version"] = identity["runtime_version"]
    checker["runtime_version_output_sha256"] = identity[
        "runtime_version_output_sha256"
    ]
    checker["runtime_signature_output_sha256"] = identity[
        "runtime_signature_output_sha256"
    ]
    checker["daemon_identity_output_sha256"] = identity[
        "daemon_identity_output_sha256"
    ]
    recipe = prepare.resolve_repo_path(checker["checker_image_recipe"])
    sbom = prepare.resolve_repo_path(checker["checker_image_sbom"])
    build_input = build_input_candidate
    cache_manifest = prepare.resolve_repo_path(
        checker["checker_cache_manifest_artifact"]
    )
    build_log = prepare.resolve_repo_path(checker["checker_image_build_log"])
    controller = prepare.resolve_repo_path(checker["controller_entrypoint_source"])
    checker["checker_image_recipe_sha256"] = prepare.sha256_file(recipe)
    checker["checker_image_sbom_sha256"] = prepare.sha256_file(sbom)
    checker["checker_image_build_input_manifest_sha256"] = prepare.sha256_file(
        build_input
    )
    checker["checker_image_build_log_sha256"] = prepare.sha256_file(build_log)
    checker["controller_entrypoint_source_sha256"] = prepare.sha256_file(controller)
    sbom_payload = load(sbom)
    checker["controller_entrypoint_sha256"] = sbom_payload.get(
        "controller_entrypoint_sha256", "UNSET"
    )
    checker["checker_cache_root"] = sbom_payload.get("checker_cache_root", "UNSET")
    checker["checker_cache_manifest_path"] = sbom_payload.get(
        "checker_cache_manifest_path", "UNSET"
    )
    checker["checker_cache_manifest_sha256"] = sbom_payload.get(
        "lake_cache_manifest_sha256", "UNSET"
    )
    prepare.require(checker["checker_cache_manifest_sha256"]
                    == prepare.sha256_file(cache_manifest),
                    "checker cache-manifest artifact differs from the image SBOM")
    checker["inspect_absent_exit_code"] = checker_launcher.ABSENT_EXIT_CODE
    checker["worker_command_prefix"] = checker_launcher.worker_command_prefix(checker)
    checker.update(checker_launcher.command_templates(checker, launcher_path))
    checker["runtime_config_sha256"] = prepare.checker_runtime_config_sha256(config)
    config["execution_status"] = "runtime_bound_unfrozen"
    config["unresolved_fields"] = prepare.unset_paths(config)
    prepare.validate_checker_runtime_preflight(config)
    dump_new(output.resolve(), config)
    print(
        "wrote runtime_bound_unfrozen config; run the sealed isolation probe before preseal: "
        f"{output.resolve()}"
    )


def prepare_preseal(draft_path: Path, source_manifest_path: Path, output: Path) -> None:
    config = load(draft_path)
    prepare.require(config["suite_id"] == "ABRL-TARGET-DRIFT-V2", "preseal requires v2")
    if config["posthoc_checker"].get("mode") == "production":
        prepare.require(config["execution_status"] == "runtime_bound_unfrozen",
                        "production preseal requires a bound runtime and completed probe")
        prepare.validate_checker_runtime_preflight(config)
    else:
        prepare.require(config["execution_status"] == "template_unfrozen",
                        "excluded fixture preseal must begin at template_unfrozen")
    source_manifest_path = source_manifest_path.resolve()
    source_manifest = load(source_manifest_path)
    prepare.require(source_manifest["suite_id"] == config["suite_id"],
                    "source manifest suite mismatch")
    prepare.verify_sources(source_manifest)

    config["orchestrator_commit"] = subprocess.check_output(
        ["git", "rev-parse", "HEAD"], cwd=ROOT, text=True
    ).strip()
    config["source_files_manifest"] = str(source_manifest_path)
    for condition in prepare.CONDITIONS:
        prompt = prepare.resolve_repo_path(config["conditions"][condition]["prompt_template"])
        config["conditions"][condition]["prompt_sha256"] = prepare.sha256_file(prompt)
    policy = prepare.resolve_repo_path(config["resource_policy"])
    config["resource_policy_sha256"] = prepare.sha256_file(policy)
    adapter_contract = prepare.resolve_repo_path(config["execution_adapter"]["contract"])
    config["execution_adapter"]["contract_sha256"] = prepare.sha256_file(adapter_contract)
    checker_contract = prepare.resolve_repo_path(config["posthoc_checker"]["contract"])
    config["posthoc_checker"]["contract_sha256"] = prepare.sha256_file(checker_contract)
    grader_prompt = prepare.resolve_repo_path(config["grading"]["grader_prompt"])
    config["grading"]["grader_prompt_sha256"] = prepare.sha256_file(grader_prompt)
    wording_prompt = prepare.resolve_repo_path(config["wording_audit"]["text_only_prompt"])
    config["wording_audit"]["text_only_prompt_sha256"] = prepare.sha256_file(wording_prompt)
    code_hashes = {
        name: prepare.sha256_file(path)
        for name, path in prepare.execution_code_paths(config).items()
    }
    adapter = config["execution_adapter"]
    adapter["entrypoint_sha256"] = code_hashes["execution_adapter_entrypoint"]
    runtime_text = adapter["runtime_executable"]
    prepare.require(isinstance(runtime_text, str) and Path(runtime_text).is_absolute(),
                    "execution adapter runtime must be an absolute path")
    runtime = prepare.regular_unlinked_file(
        Path(runtime_text).resolve(), "execution adapter runtime"
    )
    prepare.require(Path(runtime_text) == runtime,
                    "execution adapter runtime path must already be canonical")
    adapter["runtime_executable_sha256"] = prepare.sha256_file(runtime)
    provider = adapter["provider_runtime"]
    provider_runtime = prepare.validate_provider_runtime(provider, require_hash=False)
    prepare.require(provider_runtime is not None,
                    "provider runtime must be selected before preseal")
    provider["executable_sha256"] = prepare.sha256_file(provider_runtime)
    provider_version_output = prepare.provider_runtime_version_output(provider_runtime)
    provider["version_output_sha256"] = prepare.sha256_bytes(provider_version_output)
    provider["version"] = provider_version_output.decode("utf-8", errors="strict").strip()
    config["sealed_agent_view"]["materializer_sha256"] = code_hashes[
        "prepare_target_drift_execution.py"
    ]
    config["sealed_agent_view"]["run_preparer_sha256"] = code_hashes[
        "run_target_drift_execution.py"
    ]
    config["posthoc_checker"]["driver_sha256"] = code_hashes[
        "check_target_drift_run.py"
    ]
    config["posthoc_checker"]["inner_checker_sha256"] = code_hashes[
        "check_target_drift_inner.py"
    ]
    config["posthoc_checker"]["isolation_probe_runner_sha256"] = code_hashes[
        "record_target_drift_checker_isolation_probe.py"
    ]
    config["posthoc_checker"]["host_launcher_sha256"] = code_hashes[
        "launch_target_drift_checker_container.py"
    ]
    config["posthoc_checker"]["controller_entrypoint_source_sha256"] = code_hashes[
        "check_target_drift_container_controller.py"
    ]
    config["grading"]["packet_materializer_sha256"] = code_hashes[
        "prepare_target_drift_grading.py"
    ]
    config["analysis"]["grade_assembler_sha256"] = code_hashes[
        "assemble_target_drift_grades.py"
    ]
    config["analysis"]["script_sha256"] = code_hashes[
        "analyze_target_drift_execution.py"
    ]
    config["wording_audit"]["script_sha256"] = code_hashes[
        "audit_target_drift_wording.py"
    ]
    config["posthoc_checker"]["runtime_config_sha256"] = (
        prepare.checker_runtime_config_sha256(config)
    )
    checker_probe = prepare.resolve_repo_path(
        config["posthoc_checker"]["isolation_probe_report"]
    )
    config["posthoc_checker"]["isolation_probe_report_sha256"] = prepare.sha256_file(
        checker_probe
    )
    config["execution_status"] = "preseal_ready"
    config["sealed_agent_view"]["aggregate_sha256"] = "UNSET"
    config["unresolved_fields"] = ["sealed_agent_view.aggregate_sha256"]
    missing = prepare.unset_paths(config)
    prepare.require(missing == ["sealed_agent_view.aggregate_sha256"],
                    "human draft still has unresolved execution choices: " + ", ".join(missing))
    prepare.validate_prompt_templates(config, require_hashes=True)
    prepare.validate_resource_policy(config, require_hash=True)
    prepare.validate_adapter_contract(config, require_hash=True)
    prepare.validate_checker_contract(config, require_hashes=True)
    prepare.validate_auxiliary_prompts(config, require_hashes=True)
    prepare.validate_execution_code_hashes(config, require_hashes=True)
    dump_new(output.resolve(), config)
    print(f"wrote preseal_ready execution config: {output.resolve()}")


def freeze_config(preseal_config_path: Path, preseal_pack: Path, output: Path) -> None:
    config = load(preseal_config_path)
    prepare.require(config["execution_status"] == "preseal_ready",
                    "freeze input must be preseal_ready")
    preseal_pack = preseal_pack.resolve()
    prepare.verify_pack(preseal_pack)
    packed_config = load(preseal_pack / "execution_config.json")
    prepare.require(
        prepare.normalized_config_for_digest(config)
        == prepare.normalized_config_for_digest(packed_config),
        "preseal config differs from the verified preseal pack",
    )
    aggregate = (preseal_pack / "aggregate.sha256").read_text(encoding="ascii").strip()
    prepare.require(len(aggregate) == 64 and all(char in "0123456789abcdef" for char in aggregate),
                    "preseal aggregate is not a lowercase SHA-256")
    config["execution_status"] = "frozen_ready"
    config["sealed_agent_view"]["aggregate_sha256"] = aggregate
    config["unresolved_fields"] = []
    prepare.require(not prepare.unset_paths(config), "frozen config still contains UNSET")
    dump_new(output.resolve(), config)
    print(f"wrote frozen_ready execution config: {output.resolve()}, sha256={aggregate}")


def main() -> None:
    parser = argparse.ArgumentParser()
    subcommands = parser.add_subparsers(dest="command", required=True)
    runtime = subcommands.add_parser("bind-runtime")
    runtime.add_argument("--draft", type=Path, required=True)
    runtime.add_argument("--runtime-executable", type=Path, required=True)
    runtime.add_argument("--output", type=Path, required=True)
    preseal = subcommands.add_parser("preseal")
    preseal.add_argument("--draft", type=Path, required=True)
    preseal.add_argument("--source-manifest", type=Path, required=True)
    preseal.add_argument("--output", type=Path, required=True)
    freeze = subcommands.add_parser("freeze")
    freeze.add_argument("--preseal-config", type=Path, required=True)
    freeze.add_argument("--preseal-pack", type=Path, required=True)
    freeze.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    if args.command == "bind-runtime":
        bind_runtime(args.draft.resolve(), args.runtime_executable.resolve(), args.output.resolve())
    elif args.command == "preseal":
        prepare_preseal(args.draft.resolve(), args.source_manifest.resolve(), args.output.resolve())
    else:
        freeze_config(args.preseal_config.resolve(), args.preseal_pack.resolve(), args.output.resolve())


if __name__ == "__main__":
    main()
