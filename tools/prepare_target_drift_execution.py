#!/usr/bin/env python3
"""Validate or materialize the result-free ABRL target-drift execution pack."""

from __future__ import annotations

import argparse
import hashlib
import json
import random
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


def check_template(config_path: Path) -> None:
    config = load(config_path)
    require(config["suite_id"] == "ABRL-TARGET-DRIFT-V1", "wrong suite id")
    require(config["execution_status"] == "template_unfrozen",
            "checked template must remain template_unfrozen")
    require(bool(config["unresolved_fields"]), "template must enumerate unresolved fields")
    missing = unset_paths(config)
    require(bool(missing), "template unexpectedly contains no UNSET fields")
    validate_prompt_templates(config, require_hashes=False)
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


def sanitized_case(case: dict[str, Any], source: dict[str, Any]) -> dict[str, Any]:
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
    validate_prompt_templates(config, require_hashes=True)

    current_commit = subprocess.check_output(
        ["git", "rev-parse", "HEAD"], cwd=ROOT, text=True
    ).strip()
    require(config["repository_commit"] == current_commit,
            "repository commit differs from frozen execution config")

    source_manifest = load(resolve_repo_path(config["source_files_manifest"]))
    sources = verify_sources(source_manifest)
    challenges = load(SUITE / "challenges.json")["cases"]
    require({case["source_id"] for case in challenges} == set(sources),
            "source manifest does not exactly cover challenge sources")

    seeds = config["randomization"]["paired_seeds"]
    require(isinstance(seeds, list) and len(seeds) == 5,
            "paired_seeds must contain exactly five entries")
    require(len(set(seeds)) == 5, "paired seeds must be unique")
    require(all(isinstance(seed, int) for seed in seeds), "paired seeds must be integers")

    agent_cases = [sanitized_case(case, sources[case["source_id"]]) for case in challenges]
    forbidden = {"faithful_contract", "expected_affected_fields", "drift_class", "stratum"}
    require(all(not (forbidden & case.keys()) for case in agent_cases),
            "agent view leaks adjudication fields")

    runs = [
        {
            "run_id": f"{case['case_id']}--{condition}--seed-{seed}",
            "case_id": case["case_id"],
            "condition": condition,
            "seed": seed,
            "prompt_template": config["conditions"][condition]["prompt_template"],
            "status": "sealed_unrun",
        }
        for case in agent_cases
        for condition in CONDITIONS
        for seed in seeds
    ]
    require(len(runs) == 450, "materialized run count must be 450")
    rng = random.Random(config["randomization"]["presentation_order_seed"])
    rng.shuffle(runs)
    for order, run in enumerate(runs):
        run["presentation_order"] = order

    output_dir.mkdir(parents=True)
    dump(output_dir / "agent_cases.json", {
        "schema_version": 1,
        "suite_id": config["suite_id"],
        "cases": agent_cases,
    })
    dump(output_dir / "run_manifest.json", {
        "schema_version": 1,
        "suite_id": config["suite_id"],
        "execution_status": "sealed_unrun",
        "common_deliverables": [
            "Lean diff",
            "build log",
            "machine-readable final status",
            "source amendment if any",
            "concise explanation",
        ],
        "runs": runs,
    })
    dump(output_dir / "execution_config.json", config)
    digest_payload = b"".join(
        (output_dir / name).read_bytes()
        for name in ("agent_cases.json", "run_manifest.json")
    )
    aggregate = sha256_bytes(digest_payload)
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


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "--config",
        type=Path,
        default=SUITE / "execution-template.json",
    )
    parser.add_argument("--check-template", action="store_true")
    parser.add_argument("--materialize", type=Path)
    args = parser.parse_args()
    require(args.check_template != (args.materialize is not None),
            "choose exactly one of --check-template or --materialize OUTPUT_DIR")
    if args.check_template:
        check_template(args.config)
    else:
        materialize(args.config, args.materialize.resolve())


if __name__ == "__main__":
    main()
