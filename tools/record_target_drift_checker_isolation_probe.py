#!/usr/bin/env python3
"""Execute and seal the production checker-isolation probe.

This runner constructs a fresh nonce-bound request, invokes the exact frozen
checker runtime argv, derives pass/fail from host observations plus one strict
controller response, and seals every raw ledger byte.
"""

from __future__ import annotations

import argparse
import json
import os
import secrets
import shutil
import stat
import subprocess
import sys
from pathlib import Path
from typing import Any


TOOLS = Path(__file__).resolve().parent
sys.path.insert(0, str(TOOLS))

import check_target_drift_run as controller  # noqa: E402
import prepare_target_drift_execution as prepare  # noqa: E402


PROBES = (
    "network_denied",
    "host_sentinel_protected",
    "operator_ground_truth_absent",
    "checker_outputs_not_worker_writable",
    "patched_source_and_controller_input_read_only",
    "mounted_inputs_and_cidfile_protected",
    "background_process_reaped",
)
WORKER_WRITE_KEYS = (
    "request", "base_snapshot", "patch", "cidfile", "patched_source",
    "controller_input", "checker_output", "checker_response",
)


def load(path: Path) -> dict[str, Any]:
    value = json.loads(path.read_text(encoding="utf-8"))
    prepare.require(isinstance(value, dict), f"expected JSON object: {path}")
    return value


def dump(path: Path, value: Any) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(
        json.dumps(value, indent=2, sort_keys=True, ensure_ascii=False) + "\n",
        encoding="utf-8",
    )


def require_plain_tree(root: Path, label: str) -> None:
    prepare.require(root.is_dir(), f"{label} is missing")
    for path in root.rglob("*"):
        info = path.lstat()
        reparse = bool(getattr(info, "st_file_attributes", 0) & 0x400)
        prepare.require(not stat.S_ISLNK(info.st_mode) and not reparse,
                        f"{label} contains a link/reparse point: {path}")
        prepare.require(stat.S_ISDIR(info.st_mode) or stat.S_ISREG(info.st_mode),
                        f"{label} contains a special file: {path}")
        if stat.S_ISREG(info.st_mode):
            prepare.require(info.st_nlink == 1,
                            f"{label} contains a multiply linked file: {path}")


def tree_manifest(root: Path) -> list[dict[str, Any]]:
    require_plain_tree(root, "probe tree")
    return [
        {
            "path": path.relative_to(root).as_posix(),
            "bytes": path.stat().st_size,
            "sha256": prepare.sha256_file(path),
        }
        for path in sorted(root.rglob("*")) if path.is_file()
    ]


def copy_artifact(source: Path, root: Path, name: str) -> None:
    payload = controller.regular_file_bytes(source, 16 * 1024 * 1024, name)
    target = root / name
    target.parent.mkdir(parents=True, exist_ok=True)
    target.write_bytes(payload)


def strict_probe_response(
    response: dict[str, Any], nonce: str, attempt_label: str, runtime_sha256: str,
    image_digest: str, controller_sha256: str,
) -> dict[str, Any]:
    expected_fields = {
        "schema_version", "mode", "probe_nonce", "checker_attempt_label",
        "checker_runtime_config_sha256", "container_image_digest",
        "controller_entrypoint_sha256", "observations", "process_exit_code",
    }
    prepare.require(set(response) == expected_fields,
                    "isolation-probe response schema differs from the contract")
    prepare.require(response["schema_version"] == 1
                    and response["mode"] == "checker_isolation_probe"
                    and response["probe_nonce"] == nonce
                    and response["checker_attempt_label"] == attempt_label
                    and response["checker_runtime_config_sha256"] == runtime_sha256
                    and response["container_image_digest"] == image_digest
                    and response["controller_entrypoint_sha256"] == controller_sha256
                    and type(response["process_exit_code"]) is int
                    and response["process_exit_code"] == 0,
                    "isolation-probe response identity/runtime binding failed")
    observations = response["observations"]
    expected_observations = {
        "network_request_succeeded", "host_sentinel_visible",
        "operator_ground_truth_visible", "worker_write_succeeded",
        "background_probe_started",
    }
    prepare.require(isinstance(observations, dict)
                    and set(observations) == expected_observations,
                    "isolation-probe observations have the wrong schema")
    prepare.require(type(observations["network_request_succeeded"]) is bool
                    and type(observations["host_sentinel_visible"]) is bool
                    and type(observations["operator_ground_truth_visible"]) is bool
                    and type(observations["background_probe_started"]) is bool,
                    "isolation-probe flags must be literal booleans")
    writes = observations["worker_write_succeeded"]
    prepare.require(isinstance(writes, dict) and set(writes) == set(WORKER_WRITE_KEYS)
                    and all(type(writes[key]) is bool for key in WORKER_WRITE_KEYS),
                    "worker write-protection observations are incomplete")
    return observations


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--config", type=Path, required=True)
    parser.add_argument("--work-dir", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--probe-commit", required=True)
    parser.add_argument("--host-platform", required=True)
    args = parser.parse_args()
    current_commit = subprocess.check_output(
        ["git", "rev-parse", "HEAD"], cwd=prepare.ROOT, text=True
    ).strip()
    prepare.require(
        len(args.probe_commit) == 40
        and all(char in "0123456789abcdef" for char in args.probe_commit)
        and args.probe_commit == current_commit,
        "probe commit must be the current full lowercase Git commit",
    )
    config = load(args.config.resolve())
    checker = config["posthoc_checker"]
    prepare.validate_checker_runtime_preflight(config)
    prepare.require(checker["mode"] == "production",
                    "the checker isolation probe is production-only")
    prepare.require(not args.output.exists(), "refusing to overwrite probe report")
    prepare.require(args.output.resolve()
                    == prepare.resolve_repo_path(checker["isolation_probe_report"]).resolve(),
                    "probe output must equal the config-bound report path")
    artifact_root = prepare.resolve_repo_path(checker["isolation_probe_artifacts_dir"])
    prepare.require(not artifact_root.exists(), "probe artifact directory already exists")
    work = args.work_dir.resolve()
    prepare.require(not work.exists(), "probe work directory already exists")
    work.mkdir(parents=True)
    artifact_root.mkdir(parents=True)

    runtime_sha256 = prepare.checker_runtime_config_sha256(config)
    if checker.get("runtime_config_sha256") != "UNSET":
        prepare.require(checker["runtime_config_sha256"] == runtime_sha256,
                        "configured checker runtime digest is stale")
    nonce = secrets.token_hex(24)
    attempt_label = f"ABRL-PROBE-{nonce}"
    request_path = work / "request.json"
    base_snapshot = work / "base-snapshot"
    base_snapshot.mkdir()
    (base_snapshot / "ProbeSource.lean").write_text(
        "def checkerIsolationProbeSource : Nat := 1\n", encoding="utf-8"
    )
    patch_path = work / "probe.patch"
    patch_path.write_text(
        "diff --git a/ProbeSource.lean b/ProbeSource.lean\n"
        "index 1111111..2222222 100644\n"
        "--- a/ProbeSource.lean\n+++ b/ProbeSource.lean\n"
        "@@ -1 +1 @@\n-def checkerIsolationProbeSource : Nat := 1\n"
        "+def checkerIsolationProbeSource : Nat := 2\n",
        encoding="utf-8",
    )
    checker_output = work / "checker-output"
    checker_output.mkdir()
    response_root = work / "sandbox-response-output"
    response_root.mkdir()
    response_path = response_root / "sandbox-response.json"
    cidfile = work / "container.cid"
    host_sentinel = work / f"host-private-{nonce}.sentinel"
    operator_sentinel = work / f"operator-ground-truth-{nonce}.sentinel"
    host_sentinel.write_text(secrets.token_hex(32), encoding="ascii")
    operator_sentinel.write_text(secrets.token_hex(32), encoding="ascii")
    request = {
        "schema_version": 1,
        "mode": "checker_isolation_probe",
        "probe_nonce": nonce,
        "checker_attempt_label": attempt_label,
        "checker_runtime_config_sha256": runtime_sha256,
        "container_image_digest": checker["container_image_digest"],
        "controller_entrypoint_sha256": checker["controller_entrypoint_sha256"],
        "worker_command_prefix": checker["worker_command_prefix"],
        "probe_contract": {
            "forbidden_host_sentinel_filename": host_sentinel.name,
            "forbidden_operator_ground_truth_filename": operator_sentinel.name,
            "worker_write_targets": list(WORKER_WRITE_KEYS),
            "network_probe": "attempt DNS and HTTPS; both must fail",
            "background_probe": "start a worker child that requires runtime reaping",
        },
    }
    dump(request_path, request)
    protected_limit = max(
        int(checker["budgets"]["maximum_output_bytes"]),
        int(checker["budgets"]["maximum_response_bytes"]),
    )
    protected_before = {
        "request_sha256": controller.regular_file_sha256(
            request_path, protected_limit, "probe request before sandbox"
        ),
        "base_manifest": tree_manifest(base_snapshot),
        "patch_sha256": controller.regular_file_sha256(
            patch_path, protected_limit, "probe patch before sandbox"
        ),
        "host_sentinel_sha256": controller.regular_file_sha256(
            host_sentinel, protected_limit, "host sentinel before sandbox"
        ),
        "operator_sentinel_sha256": controller.regular_file_sha256(
            operator_sentinel, protected_limit, "operator sentinel before sandbox"
        ),
    }
    replacements = {
        "{{CHECKER_REQUEST_PATH}}": str(request_path.resolve()),
        "{{BASE_SNAPSHOT_PATH}}": str(base_snapshot.resolve()),
        "{{PATCH_PATH}}": str(patch_path.resolve()),
        "{{CHECKER_OUTPUT_DIR}}": str(checker_output.resolve()),
        "{{CHECKER_RESPONSE_PATH}}": str(response_path.resolve()),
        "{{CIDFILE}}": str(cidfile.resolve()),
        "{{CHECKER_ATTEMPT_LABEL}}": attempt_label,
        "{{CHECKER_IMAGE_DIGEST}}": checker["container_image_digest"],
    }
    command = controller.render_command(checker["sandbox_command_argv"], replacements)
    cleanup = controller.render_command(checker["sandbox_cleanup_argv"], replacements)
    inspect = controller.render_command(checker["sandbox_inspect_argv"], replacements)
    cleanup_label = controller.render_command(
        checker["sandbox_cleanup_by_label_argv"], replacements
    )
    inspect_label = controller.render_command(
        checker["sandbox_inspect_by_label_argv"], replacements
    )
    outcome = controller.run_sandbox(
        command, cleanup, inspect, cleanup_label, inspect_label, work,
        int(checker["budgets"]["wall_clock_seconds"]),
        int(checker["budgets"]["maximum_output_bytes"]), cidfile,
        int(checker["inspect_absent_exit_code"]),
    )
    prepare.require(outcome["exit_code"] == 0 and not outcome["timed_out"]
                    and not outcome["output_limit_exceeded"]
                    and outcome["lifecycle_verified_absent"] is True,
                    "checker isolation-probe runtime did not close cleanly")
    protected_after = {
        "request_sha256": controller.regular_file_sha256(
            request_path, protected_limit, "probe request after sandbox"
        ),
        "base_manifest": tree_manifest(base_snapshot),
        "patch_sha256": controller.regular_file_sha256(
            patch_path, protected_limit, "probe patch after sandbox"
        ),
        "host_sentinel_sha256": controller.regular_file_sha256(
            host_sentinel, protected_limit, "host sentinel after sandbox"
        ),
        "operator_sentinel_sha256": controller.regular_file_sha256(
            operator_sentinel, protected_limit, "operator sentinel after sandbox"
        ),
    }
    prepare.require(protected_after == protected_before,
                    "probe runtime mutated a protected host input")
    response = controller.load_bounded_regular_json(
        response_path, int(checker["budgets"]["maximum_response_bytes"]),
        "checker isolation-probe response",
    )
    observations = strict_probe_response(
        response, nonce, attempt_label, runtime_sha256, checker["container_image_digest"],
        checker["controller_entrypoint_sha256"],
    )
    writes = observations["worker_write_succeeded"]
    results = {
        "network_denied": observations["network_request_succeeded"] is False,
        "host_sentinel_protected": observations["host_sentinel_visible"] is False,
        "operator_ground_truth_absent": observations["operator_ground_truth_visible"] is False,
        "checker_outputs_not_worker_writable": (
            writes["checker_output"] is False and writes["checker_response"] is False
        ),
        "patched_source_and_controller_input_read_only": (
            writes["patched_source"] is False and writes["controller_input"] is False
        ),
        "mounted_inputs_and_cidfile_protected": all(
            writes[name] is False for name in ("request", "base_snapshot", "patch", "cidfile")
        ),
        "background_process_reaped": (
            observations["background_probe_started"] is True
            and outcome["lifecycle_verified_absent"] is True
        ),
    }
    prepare.require(set(results) == set(PROBES) and all(results.values()),
                    "one or more checker isolation probes failed")

    dump(artifact_root / "host-observations.json", {
        "schema_version": 1,
        "probe_nonce": nonce,
        "checker_attempt_label": attempt_label,
        "checker_runtime_config_sha256": runtime_sha256,
        "container_image_digest": checker["container_image_digest"],
        "rendered_sandbox_argv": command,
        "rendered_cleanup_argv": cleanup,
        "rendered_inspect_argv": inspect,
        "rendered_cleanup_by_label_argv": cleanup_label,
        "rendered_inspect_by_label_argv": inspect_label,
        "protected_before": protected_before,
        "protected_after": protected_after,
        "derived_probes": results,
        "lifecycle": outcome["lifecycle"],
    })
    (artifact_root / "sandbox-stdout.log").write_text(outcome["output"], encoding="utf-8")
    copy_artifact(request_path, artifact_root, "request.json")
    copy_artifact(response_path, artifact_root, "sandbox-response.json")
    copy_artifact(cidfile, artifact_root, "container.cid")
    for path in sorted(checker_output.rglob("*")):
        if path.is_file():
            copy_artifact(
                path, artifact_root,
                f"checker-output/{path.relative_to(checker_output).as_posix()}",
            )
    artifact_payloads = prepare.probe_artifact_bytes(artifact_root)
    manifest = prepare.probe_artifact_manifest(artifact_payloads)
    command_template_sha256 = prepare.sha256_bytes(
        prepare.canonical_json_bytes(checker["sandbox_command_argv"])
    )
    report = {
        "schema_version": 1,
        "suite_id": config["suite_id"],
        "status": "passed",
        "checker_id": checker["checker_id"],
        "checker_version": checker["checker_version"],
        "container_image_digest": checker["container_image_digest"],
        "controller_entrypoint_sha256": checker["controller_entrypoint_sha256"],
        "runtime_and_version": f"{checker['runtime_id']} {checker['runtime_version']}",
        "checker_runtime_config_sha256": runtime_sha256,
        "runtime_command_template_sha256": command_template_sha256,
        "probe_runner_sha256": prepare.sha256_file(Path(__file__).resolve()),
        "probe_nonce": nonce,
        "checker_attempt_label": attempt_label,
        "probe_commit": args.probe_commit,
        "host_platform": args.host_platform,
        "probes": results,
        "artifact_manifest": manifest,
        "attestation": (
            "The sealed runner executed the exact rendered production runtime command, "
            "derived every result from typed controller output and protected host bytes, "
            "and proved both cid- and label-indexed container absence."
        ),
    }
    temporary = args.output.with_name(args.output.name + ".tmp")
    dump(temporary, report)
    os.replace(temporary, args.output)
    shutil.rmtree(work)
    print(f"checker isolation probe passed: runtime={runtime_sha256}, nonce={nonce}")


if __name__ == "__main__":
    main()
