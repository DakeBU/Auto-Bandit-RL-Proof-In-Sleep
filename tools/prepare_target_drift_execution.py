#!/usr/bin/env python3
"""Validate or materialize the result-free ABRL target-drift execution pack."""

from __future__ import annotations

import argparse
import hashlib
import json
import random
import re
import subprocess
from pathlib import Path
from typing import Any


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


def validate_prompt_templates(config: dict[str, Any], require_hashes: bool) -> None:
    require(tuple(config["conditions"].keys()) == CONDITIONS,
            "condition order must remain compile_only, source_aware_blueprint, abrl")
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
    require(tuple(policy["conditions"].keys()) == CONDITIONS,
            "resource policy condition order differs from execution conditions")
    require(policy["common_isolation"]["attestation_required"] is True,
            "resource policy must require an isolation attestation")
    require(policy["conditions"]["compile_only"]["path_mode"] == "allowlist",
            "compile-only repository view must be an allowlist")
    require(policy["conditions"]["source_aware_blueprint"]["path_mode"] == "allowlist",
            "source-aware repository view must be an allowlist")
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
    require(contract["suite_id"] == config["suite_id"], "adapter-contract suite mismatch")
    require(contract["status"] == "interface_frozen_results_absent",
            "adapter contract must remain result-free")
    command = entry["command_argv"]
    require(isinstance(command, list) and command and all(isinstance(item, str) for item in command),
            "execution adapter command_argv must be a nonempty string list")
    if require_hash:
        require(entry["contract_sha256"] == sha256_file(path),
                "adapter-contract hash does not match")
        joined = "\0".join(command)
        for placeholder in contract["invocation"]["required_placeholders"]:
            require(placeholder in joined,
                    f"adapter command omits required placeholder {placeholder}")
        require(entry["container_or_sandbox_image_digest"] in joined,
                "adapter command must literally bind the frozen sandbox image digest")
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
    return {
        "prepare_target_drift_execution.py": resolve_repo_path(
            config["sealed_agent_view"]["materializer"]
        ),
        "run_target_drift_execution.py": resolve_repo_path(
            config["sealed_agent_view"]["run_preparer"]
        ),
        "check_target_drift_run.py": resolve_repo_path(config["posthoc_checker"]["path"]),
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


def validate_execution_code_hashes(config: dict[str, Any], require_hashes: bool) -> None:
    paths = execution_code_paths(config)
    require(all(path.is_file() for path in paths.values()),
            "one or more sealed execution-code files are missing")
    if not require_hashes:
        return
    expected = {
        "prepare_target_drift_execution.py": config["sealed_agent_view"]["materializer_sha256"],
        "run_target_drift_execution.py": config["sealed_agent_view"]["run_preparer_sha256"],
        "check_target_drift_run.py": config["posthoc_checker"]["sha256"],
        "prepare_target_drift_grading.py": config["grading"]["packet_materializer_sha256"],
        "assemble_target_drift_grades.py": config["analysis"]["grade_assembler_sha256"],
        "analyze_target_drift_execution.py": config["analysis"]["script_sha256"],
        "audit_target_drift_wording.py": config["wording_audit"]["script_sha256"],
    }
    for name, path in paths.items():
        require(expected[name] == sha256_file(path), f"execution-code hash mismatch for {name}")


def validate_frozen_choices(config: dict[str, Any]) -> None:
    def nonempty(value: Any, label: str, minimum: int = 1) -> None:
        require(isinstance(value, str) and len(value.strip()) >= minimum,
                f"{label} must be a substantive nonempty string")

    commit = config["orchestrator_commit"]
    require(isinstance(commit, str) and re.fullmatch(r"[0-9a-f]{40}", commit) is not None,
            "orchestrator_commit must be a lowercase full Git commit")
    model = config["model"]
    for field in ("provider", "model_id", "immutable_version", "api_or_runtime", "seed_semantics"):
        nonempty(model[field], f"model.{field}")
    require(isinstance(model["temperature"], (int, float))
            and not isinstance(model["temperature"], bool)
            and 0 <= model["temperature"] <= 2,
            "model.temperature must lie in [0,2]")
    require(isinstance(model["top_p"], (int, float)) and not isinstance(model["top_p"], bool)
            and 0 < model["top_p"] <= 1, "model.top_p must lie in (0,1]")

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
        "grader_prompt.md": grader_prompt_bytes,
        "text_only_audit_prompt.md": text_only_prompt_bytes,
    }
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
        "check_target_drift_run.py": config["posthoc_checker"]["sha256"],
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
