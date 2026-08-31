#!/usr/bin/env python3
"""Canonical Docker launcher for result-free agent-boundary components.

The probe mode preserves the existing offline sandbox check.  The excluded
execute mode follows the production-shaped PID-1/controller/adapter path but
accepts only one sealed result-ineligible request and one fixed fake auth file.
The production-action fixture additionally traverses the real Codex adapter
through a fixed offline executable.  The reserved production mode validates a
final seal and then fails because the checked-in production gate is closed.
No enabled mode can read a real credential, contact a provider, or invoke a model.
"""

from __future__ import annotations

import argparse
import errno
import hashlib
import json
import os
import re
import stat
import subprocess
import sys
import tempfile
import time
import uuid
from pathlib import Path
from typing import Any


TOOLS = Path(__file__).resolve().parent
ROOT = TOOLS.parent
sys.path.insert(0, str(TOOLS))

import launch_target_drift_checker_container as checker_launcher  # noqa: E402


SUITE_ID = "ABRL-TARGET-DRIFT-V2"
APPARMOR_PROFILE = "abrl-target-drift-codex"
PID1 = "/usr/local/bin/abrl-agent-pid1"
OUTER_CONTROLLER = "/usr/local/lib/abrl/target_drift_agent_outer_controller.py"
OUTER_PROBE = "/usr/local/lib/abrl/target_drift_agent_outer_probe.py"
MODEL_PROBE = "/usr/local/lib/abrl/target_drift_agent_model_probe.py"
EXCLUDED_ADAPTER = "/usr/local/lib/abrl/target_drift_agent_excluded_adapter.py"
EXCLUDED_CONTRACT = "/usr/local/share/abrl/agent-excluded-execution-contract.json"
ACTION_DRIVER = "/usr/local/lib/abrl/target_drift_agent_action_driver.py"
FAKE_CODEX = "/usr/local/lib/abrl/target_drift_agent_fake_codex.py"
ACTION_CONTRACT = "/usr/local/share/abrl/agent-production-action-contract.json"
CANONICAL_EXCLUDED_REQUEST = (
    ROOT / "evaluation/target-drift-v2/agent-excluded-execution-request.json"
)
CANONICAL_EXCLUDED_CONTRACT = (
    ROOT / "evaluation/target-drift-v2/agent-excluded-execution-contract.json"
)
CANONICAL_ACTION_CONTRACT = (
    ROOT / "evaluation/target-drift-v2/agent-production-action-contract.json"
)
CANONICAL_ACTION_FIXTURE = (
    ROOT / "evaluation/target-drift-v2/agent-production-action-fixture"
)
EXPECTED_AUTH = b"RESULT_FREE_SENTINEL_DO_NOT_USE\n"
EXPECTED_INPUT = b"RESULT_FREE_AGENT_INPUT\n"
PROBE_MODE = "probe"
EXCLUDED_EXECUTE_MODE = "excluded-execute"
PRODUCTION_FIXTURE_MODE = "production-fixture"
PRODUCTION_EXECUTE_MODE = "production-execute"
MAX_OUTPUT_BYTES = 4 * 1024 * 1024
CONTROL_EVIDENCE_NAMES = {
    "root-only-sentinel",
    "pid1-ready.json",
    "pid1-exit.json",
    "controller-report.json",
}


def require(condition: bool, message: str) -> None:
    if not condition:
        raise SystemExit(f"target-drift agent launcher failed: {message}")


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def nested_value(payload: dict[str, Any], dotted: str) -> Any:
    value: Any = payload
    for part in dotted.split("."):
        require(isinstance(value, dict) and part in value,
                f"production seal omits {dotted}")
        value = value[part]
    return value


def load_action_contract(
    path: Path = CANONICAL_ACTION_CONTRACT,
) -> dict[str, Any]:
    contract = json.loads(regular_file(path.resolve(), "production-action contract").read_text(
        encoding="utf-8"
    ))
    fixture = contract.get("fixture", {})
    manifest = fixture.get("input_manifest")
    require(
        contract.get("schema_version") == 1
        and contract.get("suite_id") == SUITE_ID
        and contract.get("status")
        == "production_action_interface_candidate_gate_closed"
        and contract.get("execution_status_boundary")
        == "primary_execution_not_started"
        and contract.get("production_execution_enabled") is False
        and contract.get("primary_result_eligible") is False
        and contract.get("production_gate", {}).get("decision") == "closed"
        and fixture.get("permanently_result_ineligible") is True
        and fixture.get("provider_execution_enabled") is False
        and fixture.get("provider_request_or_model_invocation_occurred") is False
        and fixture.get("input_directories") == ["workspace"]
        and isinstance(manifest, list) and len(manifest) == 3,
        "production-action contract identity or closed evidence boundary differs",
    )
    source_bindings = {
        "driver": TOOLS / "target_drift_agent_action_driver.py",
        "adapter": TOOLS / "codex_target_drift_adapter.py",
        "fake_provider": TOOLS / "target_drift_agent_fake_codex.py",
    }
    require(all(
        fixture.get(key, {}).get("sha256") == sha256(regular_file(source, key))
        for key, source in source_bindings.items()
    ), "production-action in-image source binding differs")
    observed_manifest = []
    observed_directories = []
    for source in sorted(CANONICAL_ACTION_FIXTURE.rglob("*"), key=lambda item: item.as_posix()):
        if source.is_dir():
            require(not source.is_symlink(), "production fixture contains a linked directory")
            observed_directories.append(
                source.relative_to(CANONICAL_ACTION_FIXTURE).as_posix()
            )
            continue
        regular_file(source, "production fixture input")
        observed_manifest.append({
            "path": source.relative_to(CANONICAL_ACTION_FIXTURE).as_posix(),
            "bytes": source.stat().st_size,
            "sha256": sha256(source),
        })
    require(fixture["input_directories"] == observed_directories
            and manifest == observed_manifest,
            "production-action fixture input differs from its contract")
    require(fixture.get("request_sha256") == sha256(
        CANONICAL_ACTION_FIXTURE / "request.json"
    ), "production-action fixture request hash differs")
    return contract


def validate_production_seal_structure(
    payload: Any, contract: dict[str, Any],
) -> dict[str, Any]:
    """Validate a would-be final seal without making it executable.

    The checked-in contract still disables production after this structural
    check.  This function exists so candidate/fake/unsealed artifacts cannot be
    mistaken for the external evidence still required to open the gate.
    """
    require(isinstance(payload, dict), "production seal must be one JSON object")
    schema = contract.get("production_seal_schema", {})
    required = schema.get("required_top_level_fields")
    require(isinstance(required, list) and set(payload) == set(required),
            "production seal top-level field set differs")
    require(
        payload.get("schema_version") == schema.get("schema_version") == 1
        and payload.get("suite_id") == SUITE_ID
        and payload.get("status")
        == contract["production_gate"]["required_final_seal_status"]
        and payload.get("production_execution_enabled") is True
        and payload.get("primary_result_eligible") is True
        and re.fullmatch(r"[0-9a-f]{40}", payload.get("orchestrator_commit", ""))
        is not None,
        "production seal identity, commit, or eligibility differs",
    )
    for field, nested_fields in schema.get("required_nested_fields", {}).items():
        value = payload.get(field)
        require(isinstance(value, dict) and set(value) == set(nested_fields),
                f"production seal {field} field set differs")
    string_values: list[str] = []
    pending: list[Any] = [payload]
    while pending:
        value = pending.pop()
        if isinstance(value, dict):
            pending.extend(value.values())
        elif isinstance(value, list):
            pending.extend(value)
        elif isinstance(value, str):
            string_values.append(value)
    serialized_values = "\n".join(string_values)
    for marker in contract["production_gate"]["rejected_markers"]:
        require(marker.lower() not in serialized_values.lower(),
                f"production seal contains rejected marker {marker}")
    for dotted in schema.get("sha256_fields", []):
        require(re.fullmatch(r"[0-9a-f]{64}", nested_value(payload, dotted)) is not None,
                f"production seal {dotted} is not SHA-256")
    for dotted in schema.get("digest_fields", []):
        require(re.fullmatch(r"sha256:[0-9a-f]{64}", nested_value(payload, dotted))
                is not None, f"production seal {dotted} is not an image digest")
    for dotted, expected in schema.get("required_exact_values", {}).items():
        require(nested_value(payload, dotted) == expected,
                f"production seal {dotted} differs")
    return payload


def reject_closed_production_execution(
    seal_path: Path | None, contract: dict[str, Any],
) -> None:
    require(seal_path is not None, "production mode requires --production-seal")
    seal = json.loads(regular_file(
        seal_path.resolve(), "production seal"
    ).read_text(encoding="utf-8"))
    validate_production_seal_structure(seal, contract)
    require(contract.get("production_execution_enabled") is True,
            "production action gate is closed; no credential was inspected and Docker was not launched")


def regular_file(path: Path, label: str) -> Path:
    require(path.is_absolute() and path.exists() and not path.is_symlink(),
            f"{label} must be an absolute existing nonlink")
    info = path.lstat()
    reparse = bool(getattr(info, "st_file_attributes", 0) & 0x400)
    require(stat.S_ISREG(info.st_mode) and not reparse and info.st_nlink == 1,
            f"{label} must be one regular file")
    return path


def plain_empty_directory(path: Path, label: str) -> Path:
    require(path.is_absolute() and path.is_dir() and not path.is_symlink(),
            f"{label} must be an absolute plain directory")
    require(not any(path.iterdir()), f"{label} must start empty")
    return path


def validate_inputs(
    agent_input: Path, auth: Path, control: Path,
    component_mode: str = PROBE_MODE,
) -> None:
    require(agent_input.is_absolute() and agent_input.is_dir()
            and not agent_input.is_symlink(), "agent input must be a plain directory")
    members = list(agent_input.iterdir())
    if component_mode == PROBE_MODE:
        require(len(members) == 1 and members[0].name == "input.txt",
                "component probe accepts exactly input.txt")
        require(regular_file(members[0], "agent input").read_bytes()
                == EXPECTED_INPUT, "agent input is not the frozen fake input")
    elif component_mode == EXCLUDED_EXECUTE_MODE:
        require(len(members) == 1 and members[0].name == "request.json",
                "excluded execute accepts exactly request.json")
        require(
            regular_file(members[0], "excluded request").read_bytes()
            == regular_file(
                CANONICAL_EXCLUDED_REQUEST.resolve(), "canonical excluded request"
            ).read_bytes(),
            "excluded request differs from the tracked result-ineligible fixture",
        )
    else:
        require(component_mode == PRODUCTION_FIXTURE_MODE,
                "unknown agent-boundary component mode")
        contract = load_action_contract()
        observed = []
        observed_directories = []
        for path in sorted(agent_input.rglob("*"), key=lambda item: item.as_posix()):
            if path.is_dir():
                require(not path.is_symlink(),
                        "production-action fixture contains a linked directory")
                observed_directories.append(path.relative_to(agent_input).as_posix())
                continue
            regular_file(path, "production-action fixture input")
            observed.append({
                "path": path.relative_to(agent_input).as_posix(),
                "bytes": path.stat().st_size,
                "sha256": sha256(path),
            })
        require(
                observed_directories == contract["fixture"]["input_directories"]
                and observed == contract["fixture"]["input_manifest"],
                "production-action input differs from the fixed fixture")
    require(regular_file(auth, "auth sentinel").name == "auth.json"
            and auth.read_bytes() == EXPECTED_AUTH,
            "component probe accepts only the frozen fake auth.json")
    plain_empty_directory(control, "root control output")


def validate_control_evidence(
    control: Path, *, expected_uid: int = 0, expected_gid: int = 0,
) -> dict[str, Path]:
    """Fail closed on the complete persistent root-control output surface."""
    require(control.is_dir() and not control.is_symlink(),
            "root control output ceased to be a plain directory")
    members = {path.name: path for path in control.iterdir()}
    require(set(members) == CONTROL_EVIDENCE_NAMES,
            "root control output contains an absent or undeclared evidence file")
    for name, path in members.items():
        info = path.lstat()
        require(stat.S_ISREG(info.st_mode) and not path.is_symlink()
                and info.st_nlink == 1 and info.st_uid == expected_uid
                and info.st_gid == expected_gid,
                f"root control evidence is not one root-owned regular file: {name}")
    sentinel_info = members["root-only-sentinel"].lstat()
    require(stat.S_IMODE(sentinel_info.st_mode) == 0o400,
            "root control sentinel is not mode 0400")
    for name in CONTROL_EVIDENCE_NAMES - {"root-only-sentinel"}:
        require(stat.S_IMODE(members[name].lstat().st_mode) == 0o644,
                f"root control JSON evidence is not mode 0644: {name}")
    return members


def validate_sbom(path: Path) -> dict[str, Any]:
    payload = json.loads(regular_file(path, "agent image SBOM").read_text(
        encoding="utf-8"
    ))
    require(payload.get("schema_version") == 1
            and payload.get("suite_id") == SUITE_ID
            and payload.get("status")
            == "provider_client_image_built_probe_pending_results_absent"
            and re.fullmatch(r"sha256:[0-9a-f]{64}",
                             payload.get("container_image_digest", "")),
            "agent image SBOM is not a result-free built candidate")
    required = {
        "controller_sha256", "adapter_sha256", "outer_controller_sha256",
        "outer_probe_sha256", "model_probe_sha256", "excluded_adapter_sha256",
        "excluded_execution_contract_sha256", "excluded_execution_request_sha256",
        "production_action_driver_sha256",
        "production_action_fake_provider_sha256",
        "production_action_contract_sha256",
        "production_action_fixture_request_sha256",
    }
    require(all(re.fullmatch(r"[0-9a-f]{64}", payload.get(key, ""))
                for key in required), "agent image SBOM omits outer-boundary bytes")
    source_bindings = {
        "controller_sha256": TOOLS / "target_drift_agent_pid1.py",
        "adapter_sha256": TOOLS / "codex_target_drift_adapter.py",
        "outer_controller_sha256": TOOLS / "target_drift_agent_outer_controller.py",
        "outer_probe_sha256": TOOLS / "target_drift_agent_outer_probe.py",
        "model_probe_sha256": TOOLS / "target_drift_agent_model_probe.py",
        "excluded_adapter_sha256": TOOLS / "target_drift_agent_excluded_adapter.py",
        "excluded_execution_contract_sha256": CANONICAL_EXCLUDED_CONTRACT,
        "excluded_execution_request_sha256": CANONICAL_EXCLUDED_REQUEST,
        "production_action_driver_sha256": (
            TOOLS / "target_drift_agent_action_driver.py"
        ),
        "production_action_fake_provider_sha256": (
            TOOLS / "target_drift_agent_fake_codex.py"
        ),
        "production_action_contract_sha256": CANONICAL_ACTION_CONTRACT,
        "production_action_fixture_request_sha256": (
            CANONICAL_ACTION_FIXTURE / "request.json"
        ),
    }
    require(all(
        payload[key] == sha256(regular_file(source, key))
        for key, source in source_bindings.items()
    ), "agent image SBOM differs from the checked-out controller/probe sources")
    return payload


def docker_output(command: list[str]) -> bytes:
    outcome = subprocess.run(
        command, stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
        check=False, timeout=120,
    )
    require(outcome.returncode == 0 and len(outcome.stdout) <= MAX_OUTPUT_BYTES,
            f"Docker command failed: {outcome.stdout[-1000:]!r}")
    return outcome.stdout


def verify_image(runtime: Path, sbom: dict[str, Any], label: str) -> None:
    digest = sbom["container_image_digest"]
    inspected = json.loads(docker_output([
        str(runtime), "image", "inspect", digest, "--format", "{{json .}}",
    ]).decode("utf-8"))
    require(inspected.get("Id") == digest
            and inspected.get("Config", {}).get("Entrypoint")
            == ["python3", PID1]
            and inspected.get("Config", {}).get("User") in {"", "0", "0:0"},
            "image digest, root identity, or PID-1 entrypoint differs")
    name = f"abrl-agent-image-audit-{uuid.uuid4().hex}"
    created = docker_output([
        str(runtime), "create", "--network", "none", "--name", name,
        "--label", f"abrl.agent_outer_probe={label}", "--entrypoint",
        "/bin/true", digest,
    ]).decode("ascii").strip()
    require(re.fullmatch(r"[A-Za-z0-9_.-]+", created) is not None,
            "image-audit container id is malformed")
    try:
        with tempfile.TemporaryDirectory(prefix="abrl-agent-outer-audit-") as directory:
            for source, key in (
                (PID1, "controller_sha256"),
                (OUTER_CONTROLLER, "outer_controller_sha256"),
                (OUTER_PROBE, "outer_probe_sha256"),
                (MODEL_PROBE, "model_probe_sha256"),
                (EXCLUDED_ADAPTER, "excluded_adapter_sha256"),
                (EXCLUDED_CONTRACT, "excluded_execution_contract_sha256"),
                (ACTION_DRIVER, "production_action_driver_sha256"),
                (FAKE_CODEX, "production_action_fake_provider_sha256"),
                (ACTION_CONTRACT, "production_action_contract_sha256"),
            ):
                target = Path(directory) / key
                docker_output([str(runtime), "cp", f"{created}:{source}", str(target)])
                require(sha256(regular_file(target.resolve(), source)) == sbom[key],
                        f"in-image {source} differs from the SBOM")
    finally:
        docker_output([str(runtime), "rm", "--force", created])


def docker_command(
    runtime: Path, digest: str, agent_input: Path, auth: Path,
    control: Path, label: str, component_mode: str = PROBE_MODE,
    artifact_output: Path | None = None,
) -> list[str]:
    """Return one of the three fixed provider-free component commands."""
    require(component_mode in {
        PROBE_MODE, EXCLUDED_EXECUTE_MODE, PRODUCTION_FIXTURE_MODE,
    },
            "unknown agent-boundary component mode")
    controller_mode = {
        PROBE_MODE: "result_free_probe_v1",
        EXCLUDED_EXECUTE_MODE: "result_free_excluded_execute_v1",
        PRODUCTION_FIXTURE_MODE: "result_free_production_action_fixture_v1",
    }[component_mode]
    network = "bridge" if component_mode == PROBE_MODE else "none"
    if component_mode == PRODUCTION_FIXTURE_MODE:
        require(artifact_output is not None,
                "production-action fixture requires a copyback directory")
    else:
        require(artifact_output is None,
                "copyback directory is accepted only by production-action fixture")
    command = [
        str(runtime), "run", "--rm", "--pull", "never", "--read-only",
        "--network", network, "--cap-drop", "ALL",
        "--cap-add", "SETUID", "--cap-add", "SETGID",
        "--cap-add", "CHOWN", "--cap-add", "DAC_OVERRIDE",
        "--cap-add", "FOWNER",
        "--security-opt", "no-new-privileges=true",
        "--security-opt", "seccomp=unconfined",
        "--security-opt", f"apparmor={APPARMOR_PROFILE}",
        "--user", "0:0", "--pids-limit", "96", "--memory", "1024m",
        "--cpus", "1", "--stop-timeout", "5", "--label",
        f"abrl.agent_outer_probe={label}", "--interactive",
        "--env", f"ABRL_OUTER_COMPONENT_MODE={controller_mode}",
        "--env", f"ABRL_OUTER_COMPONENT_IMAGE_DIGEST={digest}",
        "--env", "HOME=/tmp", "--env", "CODEX_HOME=/codex-home",
        "--env", "PYTHONDONTWRITEBYTECODE=1",
        "--mount", f"type=bind,src={agent_input},dst=/input/agent,readonly",
        "--mount", f"type=bind,src={auth},dst=/run/secrets/provider-auth,readonly",
        "--mount", f"type=bind,src={control},dst=/control",
    ]
    if artifact_output is not None:
        command.extend([
            "--mount", f"type=bind,src={artifact_output},dst=/artifacts",
        ])
    command.extend([
        "--tmpfs", "/agent:rw,nosuid,nodev,size=128m,mode=0700,uid=10002,gid=10002",
        "--tmpfs", "/codex-home:rw,nosuid,nodev,noexec,size=16m,mode=0700,uid=10002,gid=10002",
        "--tmpfs", "/tmp:rw,nosuid,nodev,size=64m,mode=1777",
        "--entrypoint", "python3", digest, PID1,
        "--ready-file", "/control/pid1-ready.json",
        "--exit-file", "/control/pid1-exit.json", "--", "python3",
        OUTER_CONTROLLER,
    ])
    return command


def run_with_control(command: list[str], output: Path) -> None:
    with output.open("xb") as log:
        process = subprocess.Popen(
            command, stdin=subprocess.PIPE, stdout=log,
            stderr=subprocess.STDOUT,
        )
        assert process.stdin is not None
        process.stdin.write(b"result-free-host-control\n")
        process.stdin.flush()
        deadline = time.monotonic() + 90
        while process.poll() is None and time.monotonic() < deadline:
            time.sleep(0.05)
        if process.poll() is None:
            process.stdin.close()
            process.wait(timeout=15)
            raise SystemExit("target-drift agent launcher failed: component probe timed out")
        try:
            process.stdin.close()
        except BrokenPipeError:
            pass
        require(process.returncode == 0, "outer-boundary container failed")
    require(output.stat().st_size <= MAX_OUTPUT_BYTES,
            "outer-boundary container log is oversized")


def validate_process_lifecycle(
    ready_ledger: dict[str, Any], exit_ledger: dict[str, Any],
    controller_report: dict[str, Any],
) -> None:
    """Bind the PID-1 ledger to its direct controller child and clean exit."""
    require(ready_ledger.get("controller_pid") == 1
            and isinstance(ready_ledger.get("child_pid"), int)
            and not isinstance(ready_ledger.get("child_pid"), bool)
            and ready_ledger["child_pid"] > 1
            and ready_ledger.get("pid_namespace_requirement")
            == "controller_is_pid_1"
            and controller_report.get("controller_pid")
            == ready_ledger["child_pid"]
            and controller_report.get("controller_parent_pid") == 1,
            "PID-1 ready ledger does not bind the direct controller child")
    require(exit_ledger.get("reason") == "child_exited"
            and exit_ledger.get("child_return_code") == 0,
            "PID-1 ledger does not record a clean controlled child exit")


def validate_action_copyback(
    artifacts: Path, controller_report: dict[str, Any],
    contract: dict[str, Any], *, expected_uid: int = 0, expected_gid: int = 0,
) -> dict[str, Any]:
    require(artifacts.is_dir() and not artifacts.is_symlink(),
            "production-action copyback ceased to be a plain directory")
    root_members = {path.name: path for path in artifacts.iterdir()}
    require(set(root_members) == {"adapter", "output", "copyback-receipt.json"},
            "production-action copyback root file set differs")
    records: list[dict[str, Any]] = []
    fixture = contract["fixture"]
    for group, expected_names in (
        ("adapter", set(fixture["required_adapter_files"])),
        ("output", set(fixture["required_output_files"])),
    ):
        directory = root_members[group]
        require(directory.is_dir() and not directory.is_symlink(),
                f"production-action copyback {group} is not a plain directory")
        members = {path.name: path for path in directory.iterdir()}
        require(set(members) == expected_names,
                f"production-action copyback {group} file set differs")
        for name, path in sorted(members.items()):
            regular_file(path, f"production-action copyback {group}/{name}")
            info = path.lstat()
            require(info.st_uid == expected_uid and info.st_gid == expected_gid
                    and stat.S_IMODE(info.st_mode) == 0o444,
                    f"production-action copyback ownership or mode differs: {group}/{name}")
            payload = path.read_bytes()
            records.append({
                "path": f"{group}/{name}",
                "bytes": len(payload),
                "sha256": hashlib.sha256(payload).hexdigest(),
            })
    receipt_path = regular_file(
        root_members["copyback-receipt.json"], "production-action copyback receipt"
    )
    receipt_info = receipt_path.lstat()
    require(receipt_info.st_uid == expected_uid and receipt_info.st_gid == expected_gid
            and stat.S_IMODE(receipt_info.st_mode) == 0o444,
            "production-action copyback receipt ownership or mode differs")
    receipt = json.loads(receipt_path.read_text(encoding="utf-8"))
    evidence = controller_report.get("copyback_evidence", {})
    require(
        receipt.get("schema_version") == 1
        and receipt.get("suite_id") == SUITE_ID
        and receipt.get("status")
        == "copied_result_free_production_action_fixture"
        and receipt.get("primary_result_eligible") is False
        and receipt.get("provider_execution_enabled") is False
        and receipt.get("provider_request_or_model_invocation_occurred") is False
        and receipt.get("source_request_sha256")
        == contract["fixture"]["request_sha256"]
        and receipt.get("copied_files") == records
        and evidence.get("copyback_manifest") == records
        and evidence.get("copyback_receipt_status") == receipt["status"]
        and evidence.get("copyback_receipt_sha256") == sha256(receipt_path),
        "production-action copyback receipt or hash binding differs",
    )
    return {
        "copyback_manifest": records,
        "copyback_receipt_sha256": sha256(receipt_path),
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "--component-mode", choices=(
            PROBE_MODE, EXCLUDED_EXECUTE_MODE, PRODUCTION_FIXTURE_MODE,
            PRODUCTION_EXECUTE_MODE,
        ),
        default=PROBE_MODE,
    )
    parser.add_argument("--production-seal", type=Path)
    parser.add_argument("--image-sbom", type=Path, required=True)
    parser.add_argument("--agent-input", type=Path, required=True)
    parser.add_argument("--auth-sentinel", type=Path, required=True)
    parser.add_argument("--control-output", type=Path, required=True)
    parser.add_argument("--artifact-output", type=Path)
    parser.add_argument("--apparmor-source", type=Path, required=True)
    parser.add_argument("--report", type=Path, required=True)
    parser.add_argument("--probe-commit", required=True)
    args = parser.parse_args()
    action_contract = load_action_contract()
    if args.component_mode == PRODUCTION_EXECUTE_MODE:
        reject_closed_production_execution(args.production_seal, action_contract)
        require(False, "production controller implementation is intentionally absent; a reviewed code change is required after the external gate opens")
    require(args.production_seal is None,
            "--production-seal is accepted only by the closed production mode")
    require(sys.platform.startswith("linux"), "component probe requires Linux")
    require(re.fullmatch(r"[0-9a-f]{40}", args.probe_commit) is not None,
            "probe commit must be a full Git commit")
    apparmor = regular_file(
        Path(os.path.abspath(args.apparmor_source)), "AppArmor source"
    )
    require(f"profile {APPARMOR_PROFILE} flags=(unconfined)" in apparmor.read_text(
        encoding="utf-8"
    ), "AppArmor source does not define the frozen profile")
    agent_input = Path(os.path.abspath(args.agent_input))
    auth = Path(os.path.abspath(args.auth_sentinel))
    control = Path(os.path.abspath(args.control_output))
    validate_inputs(agent_input, auth, control, args.component_mode)
    artifact_output = (
        Path(os.path.abspath(args.artifact_output))
        if args.artifact_output is not None else None
    )
    if args.component_mode == PRODUCTION_FIXTURE_MODE:
        require(artifact_output is not None,
                "production-action fixture requires --artifact-output")
        plain_empty_directory(artifact_output, "production-action copyback output")
    else:
        require(artifact_output is None,
                "--artifact-output is accepted only by production-action fixture")
    report_path = Path(os.path.abspath(args.report))
    require(report_path.parent.is_dir() and not report_path.parent.is_symlink(),
            "report parent must be a plain existing directory")
    require(not report_path.exists(), "report already exists")
    sbom_path = Path(os.path.abspath(args.image_sbom))
    sbom = validate_sbom(sbom_path)
    runtime = checker_launcher.canonical_docker_executable()
    before = checker_launcher.runtime_identity(runtime)
    label = "result-free-" + uuid.uuid4().hex
    verify_image(runtime, sbom, label)
    command = docker_command(
        runtime, sbom["container_image_digest"], agent_input, auth, control, label,
        args.component_mode, artifact_output,
    )
    log = report_path.with_name(report_path.stem + "-container.log")
    require(not log.exists(), "container log already exists")
    run_with_control(command, log)
    after = checker_launcher.runtime_identity(runtime)
    require(before == after, "Docker runtime identity changed during the probe")
    control_evidence = validate_control_evidence(control)
    controller_report_path = regular_file(
        control_evidence["controller-report.json"], "controller report"
    )
    controller_report = json.loads(controller_report_path.read_text(encoding="utf-8"))
    expected_status = {
        PROBE_MODE: "passed_result_free_outer_boundary_component",
        EXCLUDED_EXECUTE_MODE: "passed_result_free_excluded_execute_component",
        PRODUCTION_FIXTURE_MODE: (
            "passed_result_free_production_action_fixture_component"
        ),
    }[args.component_mode]
    require(controller_report.get("status") == expected_status,
            "root controller did not report the expected passing component")
    worker_observation = controller_report.get("worker_observation", {})
    copyback_validation: dict[str, Any] | None = None
    require(controller_report.get("controller_uid") == 0
            and controller_report.get("controller_gid") == 0
            and controller_report.get("worker_uid") == 10002
            and controller_report.get("worker_gid") == 10002
            and (
                args.component_mode in {
                    EXCLUDED_EXECUTE_MODE, PRODUCTION_FIXTURE_MODE,
                }
                or (
                    isinstance(worker_observation, dict)
                    and worker_observation.get("worker_uid") == 10002
                    and worker_observation.get("worker_gid") == 10002
                    and int(worker_observation.get(
                        "worker_effective_capabilities_hex", "1"
                    ), 16) == 0
                )
            ),
            "controller report does not bind the root-to-worker transition")
    if args.component_mode == PROBE_MODE:
        model_observation = worker_observation.get("model_shell", {})
        require(isinstance(model_observation, dict)
                and model_observation.get("trusted_auth_fd_env_absent") is True
                and model_observation.get("trusted_auth_fd_target_absent") is True
                and model_observation.get("outer_auth_mount_unreadable") is True
                and model_observation.get("outer_auth_mount_read_errno")
                in {errno.EACCES, errno.EPERM}
                and model_observation.get("root_control_output_unreadable") is True
                and model_observation.get("root_control_output_read_errno")
                in {errno.EACCES, errno.EPERM}
                and int(model_observation.get(
                    "effective_capabilities_hex", "1"
                ), 16) == 0,
                "nested command sandbox did not prove the auth/control boundary")
        handoff = worker_observation.get("trusted_client_fake_auth_handoff", {})
        require(isinstance(handoff, dict)
                and handoff.get("bytes") == len(EXPECTED_AUTH)
                and handoff.get("sha256")
                == hashlib.sha256(EXPECTED_AUTH).hexdigest()
                and handoff.get("read_only_descriptor") is True
                and handoff.get("descriptor_closed_before_sandbox") is True
                and handoff.get("environment_marker_removed_before_sandbox") is True,
                "trusted worker did not prove the one-time fake-auth handoff")
    elif args.component_mode == EXCLUDED_EXECUTE_MODE:
        execution = controller_report.get("execution_evidence", {})
        handoff = execution.get("fake_auth_handoff", {})
        usage = execution.get("adapter_response", {}).get("usage", {})
        require(
            controller_report.get("execution_status_boundary")
            == "primary_execution_not_started"
            and controller_report.get("container_image_digest")
            == sbom["container_image_digest"]
            and execution.get("primary_result_eligible") is False
            and execution.get("provider_execution_enabled") is False
            and execution.get("provider_request_or_model_invocation_occurred") is False
            and isinstance(usage, dict)
            and usage.get("cost_usd") == 0
            and usage.get("input_tokens") == 0
            and usage.get("output_tokens") == 0
            and isinstance(handoff, dict)
            and handoff.get("sha256") == hashlib.sha256(EXPECTED_AUTH).hexdigest()
            and handoff.get("descriptor_closed_before_adapter_work") is True,
            "excluded execution evidence weakens the no-provider/result boundary",
        )
    else:
        execution = controller_report.get("execution_evidence", {})
        handoff = execution.get("fake_auth_handoff", {})
        usage = execution.get("adapter_response", {}).get("usage", {})
        require(
            controller_report.get("execution_status_boundary")
            == "primary_execution_not_started"
            and controller_report.get("container_image_digest")
            == sbom["container_image_digest"]
            and execution.get("primary_result_eligible") is False
            and execution.get("provider_execution_enabled") is False
            and execution.get("provider_request_or_model_invocation_occurred") is False
            and execution.get("temporary_auth_removed") is True
            and execution.get("adapter_path")
            == "/usr/local/lib/abrl/codex_target_drift_adapter.py"
            and execution.get("adapter_sha256") == sbom["adapter_sha256"]
            and isinstance(usage, dict)
            and usage.get("cost_usd") == 0
            and usage.get("input_tokens") == 0
            and usage.get("output_tokens") == 0
            and isinstance(handoff, dict)
            and handoff.get("sha256") == hashlib.sha256(EXPECTED_AUTH).hexdigest()
            and handoff.get("descriptor_closed_before_adapter_launch") is True,
            "production-action fixture weakens the no-provider/result boundary",
        )
        require(artifact_output is not None,
                "production-action copyback output disappeared")
        copyback_validation = validate_action_copyback(
            artifact_output, controller_report, action_contract,
        )
    sentinel = controller_report.get("root_control_sentinel", {})
    require(isinstance(sentinel, dict)
            and sentinel.get("path") == "/control/root-only-sentinel"
            and sentinel.get("mode") == "0400"
            and sentinel.get("uid") == 0
            and sentinel.get("gid") == 0
            and sentinel.get("bytes")
            == len(b"RESULT_FREE_ROOT_CONTROL_SENTINEL\n")
            and sentinel.get("sha256") == hashlib.sha256(
                b"RESULT_FREE_ROOT_CONTROL_SENTINEL\n"
            ).hexdigest(), "root control sentinel binding is malformed")
    ready_path = regular_file(
        control_evidence["pid1-ready.json"], "PID-1 ready ledger"
    )
    exit_path = regular_file(
        control_evidence["pid1-exit.json"], "PID-1 exit ledger"
    )
    ready_ledger = json.loads(ready_path.read_text(encoding="utf-8"))
    exit_ledger = json.loads(exit_path.read_text(encoding="utf-8"))
    validate_process_lifecycle(ready_ledger, exit_ledger, controller_report)
    report_status = {
        PROBE_MODE: "passed_result_free_outer_launcher_component_candidate",
        EXCLUDED_EXECUTE_MODE: (
            "passed_result_free_excluded_execute_launcher_component_candidate"
        ),
        PRODUCTION_FIXTURE_MODE: (
            "passed_result_free_production_action_launcher_fixture_candidate"
        ),
    }[args.component_mode]
    report = {
        "schema_version": 1,
        "suite_id": SUITE_ID,
        "status": report_status,
        "component_mode": args.component_mode,
        "probe_commit": args.probe_commit,
        "container_image_digest": sbom["container_image_digest"],
        "image_sbom_sha256": sha256(sbom_path),
        "docker_runtime_identity": before,
        "docker_command_argv": command,
        "docker_command_sha256": hashlib.sha256(json.dumps(
            command, separators=(",", ":")
        ).encode("utf-8")).hexdigest(),
        "source_bindings": {
            "host_launcher_sha256": sha256(Path(__file__).resolve()),
            "apparmor_source_sha256": sha256(apparmor),
            "controller_report_sha256": sha256(controller_report_path),
            "pid1_ready_ledger_sha256": sha256(ready_path),
            "pid1_exit_ledger_sha256": sha256(exit_path),
            "production_action_contract_sha256": sha256(
                CANONICAL_ACTION_CONTRACT
            ),
        },
        "controller_report": controller_report,
        "copyback_validation": copyback_validation,
        "container_log_sha256": sha256(log),
        "nonclaims": [
            "The mounted auth.json was a fixed fake sentinel, not a provider credential.",
            "The one-time descriptor handoff is component evidence, not the real provider authentication path.",
            "No provider request or model invocation occurred.",
            "The image is local and unpublished; this is not a production seal or real smoke.",
            "The 450-run primary evaluation remains execution_not_started."
        ],
    }
    descriptor = os.open(report_path, os.O_WRONLY | os.O_CREAT | os.O_EXCL, 0o644)
    with os.fdopen(descriptor, "w", encoding="utf-8", newline="\n") as stream:
        json.dump(report, stream, indent=2, sort_keys=True)
        stream.write("\n")
    print(json.dumps({
        "status": report["status"], "report": str(report_path),
        "container_image_digest": report["container_image_digest"],
    }, sort_keys=True))


if __name__ == "__main__":
    main()
