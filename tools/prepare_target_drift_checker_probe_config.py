#!/usr/bin/env python3
"""Materialize the result-free checker candidate used by the live probe.

This tool fills only the checker-image/runtime inputs that are already fixed by
one completed candidate build.  Provider, model, pricing, grading, and primary
run fields deliberately remain ``UNSET``; the output is not a runnable or
presealed target-drift experiment configuration.
"""

from __future__ import annotations

import argparse
import json
import os
import re
import subprocess
import sys
from pathlib import Path
from typing import Any


TOOLS = Path(__file__).resolve().parent
ROOT = TOOLS.parent
sys.path.insert(0, str(TOOLS))

import prepare_target_drift_execution as prepare  # noqa: E402
import prepare_target_drift_checker_image as checker_image  # noqa: E402


SUITE_ID = "ABRL-TARGET-DRIFT-V2"
SBOM_STATUS = "built_manifest_verified_probe_pending"


def load_object(path: Path, label: str) -> dict[str, Any]:
    prepare.require(path.is_file(), f"missing {label}: {path}")
    value = json.loads(path.read_text(encoding="utf-8"))
    prepare.require(isinstance(value, dict), f"{label} must be a JSON object")
    return value


def write_new_json(path: Path, value: Any) -> None:
    prepare.require(not path.exists(), f"refusing to overwrite {path}")
    path.parent.mkdir(parents=True, exist_ok=True)
    descriptor = os.open(path, os.O_WRONLY | os.O_CREAT | os.O_EXCL, 0o644)
    try:
        with os.fdopen(descriptor, "w", encoding="utf-8", newline="\n") as handle:
            json.dump(value, handle, indent=2, sort_keys=True, ensure_ascii=False)
            handle.write("\n")
    except BaseException:
        path.unlink(missing_ok=True)
        raise


def current_commit() -> str:
    commit = subprocess.check_output(
        ["git", "rev-parse", "HEAD"], cwd=ROOT, text=True
    ).strip()
    prepare.require(re.fullmatch(r"[0-9a-f]{40}", commit) is not None,
                    "current Git commit is not a full lowercase SHA")
    return commit


def materialize(
    template_path: Path,
    context: Path,
    artifact_dir: Path,
    probe_report: Path,
    probe_artifacts_dir: Path,
    output: Path,
    budgets: dict[str, int | float],
) -> dict[str, Any]:
    template_path = template_path.resolve()
    context = context.resolve()
    artifact_dir = artifact_dir.resolve()
    probe_report = probe_report.resolve()
    probe_artifacts_dir = probe_artifacts_dir.resolve()
    output = output.resolve()

    config = load_object(template_path, "execution template")
    prepare.require(config.get("schema_version") == 2
                    and config.get("suite_id") == SUITE_ID,
                    "checker probe materializer requires the v2 template")
    prepare.require(config.get("execution_status") == "template_unfrozen",
                    "checker probe input must remain template_unfrozen")

    build_input = checker_image.validate_context(context)
    build_input_path = context / "checker-image-build-input.json"
    recipe_path = context / "Containerfile"
    controller_path = context / "check_target_drift_container_controller.py"
    inner_path = context / "check_target_drift_inner.py"
    sbom_path = artifact_dir / "checker-image-sbom.json"
    cache_manifest_path = artifact_dir / "checker-cache-manifest.json"
    build_log_path = artifact_dir / "checker-image-build.log"
    sbom = load_object(sbom_path, "checker-image SBOM")
    for path, label in (
        (build_input_path, "build-input manifest"),
        (recipe_path, "checker image recipe"),
        (controller_path, "in-image controller"),
        (inner_path, "inner checker"),
        (cache_manifest_path, "checker cache manifest"),
        (build_log_path, "checker image build log"),
    ):
        prepare.require(path.is_file(), f"missing {label}: {path}")

    prepare.require(sbom.get("schema_version") == 1
                    and sbom.get("suite_id") == SUITE_ID
                    and sbom.get("status") == SBOM_STATUS,
                    "checker-image SBOM identity/status mismatch")
    image_digest = sbom.get("container_image_digest")
    workspace_commit = sbom.get("workspace_base_commit")
    prepare.require(isinstance(image_digest, str)
                    and re.fullmatch(r"sha256:[0-9a-f]{64}", image_digest) is not None,
                    "checker-image SBOM does not contain an immutable digest")
    prepare.require(isinstance(workspace_commit, str)
                    and re.fullmatch(r"[0-9a-f]{40}", workspace_commit) is not None,
                    "checker-image SBOM does not contain a full base commit")
    expected_hashes = {
        "build_input_manifest_sha256": prepare.sha256_file(build_input_path),
        "checker_image_recipe_sha256": prepare.sha256_file(recipe_path),
        "controller_entrypoint_sha256": prepare.sha256_file(controller_path),
        "inner_checker_sha256": prepare.sha256_file(inner_path),
        "lake_cache_manifest_sha256": prepare.sha256_file(cache_manifest_path),
        "image_build_log_sha256": prepare.sha256_file(build_log_path),
    }
    prepare.require(all(sbom.get(field) == digest
                        for field, digest in expected_hashes.items()),
                    "checker-image build artifacts differ from the SBOM hash chain")
    prepare.require(build_input.get("workspace_base_commit") == workspace_commit,
                    "checker-image SBOM and build input disagree on the base commit")
    prepare.require(not probe_report.exists(),
                    "probe report already exists; refusing to relabel evidence")
    prepare.require(not probe_artifacts_dir.exists(),
                    "probe artifact directory already exists")

    checker = config["posthoc_checker"]
    checker.update({
        "checker_id": "abrl-target-drift-neutral-checker",
        "checker_version": f"candidate-{current_commit()}",
        "mode": "production",
        "container_image_digest": image_digest,
        "checker_image_sbom": str(sbom_path),
        "checker_image_build_input_manifest": str(build_input_path),
        "checker_cache_manifest_artifact": str(cache_manifest_path),
        "checker_image_build_log": str(build_log_path),
        "isolation_probe_report": str(probe_report),
        "isolation_probe_artifacts_dir": str(probe_artifacts_dir),
        "filesystem_network_process_attestation": (
            "Candidate probe only: the exact frozen Docker boundary will be tested; "
            "no isolation result is claimed until the sealed seven-probe report passes."
        ),
        "controller_worker_separation_attestation": (
            "Candidate probe only: controller/worker write separation will be measured "
            "by the sealed runner before this checker can enter any production seal."
        ),
        "budgets": budgets,
        "cache_prelude_argv": [],
    })
    config["workspace_base_commit"] = workspace_commit
    config["unresolved_fields"] = prepare.unset_paths(config)
    write_new_json(output, config)
    return config


def positive_int(value: str) -> int:
    parsed = int(value)
    if parsed <= 0:
        raise argparse.ArgumentTypeError("must be positive")
    return parsed


def positive_float(value: str) -> float:
    parsed = float(value)
    if parsed <= 0:
        raise argparse.ArgumentTypeError("must be positive")
    return parsed


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--template", type=Path, required=True)
    parser.add_argument("--context", type=Path, required=True)
    parser.add_argument("--artifact-dir", type=Path, required=True)
    parser.add_argument("--probe-report", type=Path, required=True)
    parser.add_argument("--probe-artifacts-dir", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--wall-clock-seconds", type=positive_int, default=900)
    parser.add_argument("--memory-mb", type=positive_int, default=8192)
    parser.add_argument("--pids-limit", type=positive_int, default=256)
    parser.add_argument("--cpus", type=positive_float, default=2.0)
    parser.add_argument("--maximum-output-bytes", type=positive_int,
                        default=16 * 1024 * 1024)
    parser.add_argument("--maximum-response-bytes", type=positive_int,
                        default=4 * 1024 * 1024)
    args = parser.parse_args()
    config = materialize(
        args.template, args.context, args.artifact_dir, args.probe_report,
        args.probe_artifacts_dir, args.output,
        {
            "wall_clock_seconds": args.wall_clock_seconds,
            "memory_mb": args.memory_mb,
            "pids_limit": args.pids_limit,
            "cpus": args.cpus,
            "maximum_output_bytes": args.maximum_output_bytes,
            "maximum_response_bytes": args.maximum_response_bytes,
        },
    )
    print(json.dumps({
        "status": config["execution_status"],
        "checker_mode": config["posthoc_checker"]["mode"],
        "container_image_digest": config["posthoc_checker"]["container_image_digest"],
        "unresolved_field_count": len(config["unresolved_fields"]),
        "nonclaim": "This checker-only draft is not a frozen experiment configuration.",
    }, sort_keys=True))


if __name__ == "__main__":
    main()
