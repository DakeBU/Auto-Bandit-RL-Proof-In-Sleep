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


def load(path: Path) -> dict[str, Any]:
    return json.loads(path.read_text(encoding="utf-8"))


def dump_new(path: Path, value: Any) -> None:
    prepare.require(not path.exists(), f"refusing to overwrite {path}")
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(
        json.dumps(value, indent=2, sort_keys=True, ensure_ascii=False) + "\n",
        encoding="utf-8",
    )


def prepare_preseal(draft_path: Path, source_manifest_path: Path, output: Path) -> None:
    config = load(draft_path)
    prepare.require(config["suite_id"] == "ABRL-TARGET-DRIFT-V2", "preseal requires v2")
    prepare.require(config["execution_status"] == "template_unfrozen",
                    "human draft must begin at template_unfrozen")
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
    grader_prompt = prepare.resolve_repo_path(config["grading"]["grader_prompt"])
    config["grading"]["grader_prompt_sha256"] = prepare.sha256_file(grader_prompt)
    wording_prompt = prepare.resolve_repo_path(config["wording_audit"]["text_only_prompt"])
    config["wording_audit"]["text_only_prompt_sha256"] = prepare.sha256_file(wording_prompt)
    code_hashes = {
        name: prepare.sha256_file(path)
        for name, path in prepare.execution_code_paths(config).items()
    }
    config["sealed_agent_view"]["materializer_sha256"] = code_hashes[
        "prepare_target_drift_execution.py"
    ]
    config["sealed_agent_view"]["run_preparer_sha256"] = code_hashes[
        "run_target_drift_execution.py"
    ]
    config["posthoc_checker"]["sha256"] = code_hashes["check_target_drift_run.py"]
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
    config["execution_status"] = "preseal_ready"
    config["sealed_agent_view"]["aggregate_sha256"] = "UNSET"
    config["unresolved_fields"] = ["sealed_agent_view.aggregate_sha256"]
    missing = prepare.unset_paths(config)
    prepare.require(missing == ["sealed_agent_view.aggregate_sha256"],
                    "human draft still has unresolved execution choices: " + ", ".join(missing))
    prepare.validate_prompt_templates(config, require_hashes=True)
    prepare.validate_resource_policy(config, require_hash=True)
    prepare.validate_adapter_contract(config, require_hash=True)
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
    preseal = subcommands.add_parser("preseal")
    preseal.add_argument("--draft", type=Path, required=True)
    preseal.add_argument("--source-manifest", type=Path, required=True)
    preseal.add_argument("--output", type=Path, required=True)
    freeze = subcommands.add_parser("freeze")
    freeze.add_argument("--preseal-config", type=Path, required=True)
    freeze.add_argument("--preseal-pack", type=Path, required=True)
    freeze.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    if args.command == "preseal":
        prepare_preseal(args.draft.resolve(), args.source_manifest.resolve(), args.output.resolve())
    else:
        freeze_config(args.preseal_config.resolve(), args.preseal_pack.resolve(), args.output.resolve())


if __name__ == "__main__":
    main()
