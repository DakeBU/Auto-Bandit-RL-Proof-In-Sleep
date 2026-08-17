#!/usr/bin/env python3
"""Run the same neutral Lean checker on every prepared target-drift workspace."""

from __future__ import annotations

import argparse
import json
import os
import re
import shutil
import signal
import subprocess
import time
import sys
from pathlib import Path
from typing import Any


FORBIDDEN_LEAN = {
    "sorry": re.compile(r"\bsorry\b"),
    "admit": re.compile(r"\badmit\b"),
    "axiom": re.compile(r"(?m)^\s*axiom\b"),
    "constant": re.compile(r"(?m)^\s*constant\b"),
    "postulate": re.compile(r"(?m)^\s*postulate\b"),
}
ALLOWED_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}
DECLARATION_NAME = re.compile(
    r"^[A-Za-z_][A-Za-z0-9_']*(?:\.[A-Za-z_][A-Za-z0-9_']*)*$"
)

TOOLS = Path(__file__).resolve().parent
sys.path.insert(0, str(TOOLS))
import prepare_target_drift_execution as prepare  # noqa: E402
import run_target_drift_execution as runner  # noqa: E402


def load(path: Path) -> dict[str, Any]:
    return json.loads(path.read_text(encoding="utf-8"))


def dump(path: Path, value: Any) -> None:
    path.write_text(
        json.dumps(value, indent=2, sort_keys=True, ensure_ascii=False) + "\n",
        encoding="utf-8",
    )


def require(condition: bool, message: str) -> None:
    if not condition:
        raise SystemExit(f"target-drift checker failed: {message}")


def sha256(path: Path) -> str:
    import hashlib
    return hashlib.sha256(path.read_bytes()).hexdigest()


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


def run_checked(command: list[str], cwd: Path, timeout: int) -> dict[str, Any]:
    started = time.monotonic()
    kwargs: dict[str, Any] = {}
    if os.name != "nt":
        kwargs["start_new_session"] = True
    process = subprocess.Popen(
        command,
        cwd=cwd,
        stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT,
        text=True,
        encoding="utf-8",
        errors="replace",
        **kwargs,
    )
    try:
        output, _ = process.communicate(timeout=timeout)
        timed_out = False
    except subprocess.TimeoutExpired:
        terminate_tree(process)
        output, _ = process.communicate()
        timed_out = True
    return {
        "command": command,
        "exit_code": process.returncode,
        "timed_out": timed_out,
        "wall_seconds": round(time.monotonic() - started, 6),
        "output": output,
    }


def changed_files(workspace: Path, baseline: dict[str, str]) -> tuple[list[str], list[str]]:
    current = {
        path.relative_to(workspace).as_posix(): sha256(path)
        for path in workspace.rglob("*")
        if path.is_file() and not path.relative_to(workspace).as_posix().startswith(".lake/")
    }
    changed = sorted(
        path for path, digest in current.items()
        if baseline.get(path) != digest
    )
    deleted = sorted(path for path in baseline if path not in current)
    return changed, deleted


def scan_lean(workspace: Path, paths: list[str]) -> list[dict[str, Any]]:
    hits = []
    for relative in paths:
        if not relative.endswith(".lean"):
            continue
        path = workspace / relative
        if not path.is_file():
            continue
        text = path.read_text(encoding="utf-8", errors="replace")
        for kind, pattern in FORBIDDEN_LEAN.items():
            for match in pattern.finditer(text):
                hits.append({
                    "path": relative,
                    "kind": kind,
                    "line": text.count("\n", 0, match.start()) + 1,
                })
    return hits


def parsed_axioms(output: str) -> set[str]:
    axioms: set[str] = set()
    for body in re.findall(r"depends on axioms:\s*\[([^\]]*)\]", output):
        axioms.update(item.strip() for item in body.split(",") if item.strip())
    return axioms


def declarations_appear_in_changes(
    workspace: Path, changed: list[str], declarations: list[str]
) -> bool:
    introduced: set[str] = set()
    namespace_line = re.compile(r"^\s*namespace\s+([A-Za-z_][A-Za-z0-9_'.]*)\s*$")
    end_line = re.compile(r"^\s*end(?:\s+[A-Za-z_][A-Za-z0-9_'.]*)?\s*$")
    declaration_line = re.compile(
        r"^\s*(?:theorem|lemma|def|abbrev|structure|class|instance|inductive|opaque)\s+"
        r"([A-Za-z_][A-Za-z0-9_']*(?:\.[A-Za-z_][A-Za-z0-9_']*)*)\b"
    )
    for relative in changed:
        path = workspace / relative
        if not relative.endswith(".lean") or not path.is_file():
            continue
        namespace: list[str] = []
        for line in path.read_text(encoding="utf-8", errors="replace").splitlines():
            opened = namespace_line.match(line)
            if opened:
                namespace.append(opened.group(1))
                continue
            if end_line.match(line):
                if namespace:
                    namespace.pop()
                continue
            declaration = declaration_line.match(line)
            if not declaration:
                continue
            name = declaration.group(1)
            introduced.add(name if "." in name or not namespace else ".".join([*namespace, name]))
    return set(declarations) <= introduced


def self_verify(pack: Path, config: dict[str, Any]) -> None:
    checks = {
        Path(__file__).resolve(): config["posthoc_checker"]["sha256"],
        Path(prepare.__file__).resolve(): config["sealed_agent_view"]["materializer_sha256"],
        Path(runner.__file__).resolve(): config["sealed_agent_view"]["run_preparer_sha256"],
    }
    for current, expected in checks.items():
        sealed = pack / "execution_code" / current.name
        require(sealed.is_file(), f"sealed execution-code copy is missing: {current.name}")
        require(sha256(current) == expected,
                f"invoked execution code differs from frozen hash: {current.name}")
        require(sha256(sealed) == expected,
                f"sealed execution code differs from frozen hash: {current.name}")


def require_adapter_artifacts_unchanged(operator: Path, receipt: dict[str, Any]) -> None:
    adapter = operator / "adapter"
    for name, expected in receipt["adapter_artifact_sha256"].items():
        path = adapter / name
        require(path.is_file(), f"adapter artifact missing after execution: {name}")
        require(sha256(path) == expected, f"adapter artifact changed after execution: {name}")


def validate_workflow_compliance(output_dir: Path, job: dict[str, Any]) -> None:
    path = output_dir / "workflow-compliance.json"
    payload = load(path)
    require(payload.get("schema_version") == 1,
            "workflow-compliance schema_version must be 1")
    require(payload.get("opaque_run_id") == job["opaque_run_id"],
            "workflow-compliance run id mismatch")
    contract = job["result_contract"]
    require(payload.get("workflow_id") == contract["workflow_id"],
            "workflow-compliance id differs from the assigned workflow")
    evidence = payload.get("evidence_files")
    require(isinstance(evidence, list), "workflow-compliance evidence_files must be a list")
    require(all(isinstance(item, dict) and set(item) == {"path", "sha256"}
                for item in evidence),
            "workflow-compliance evidence entries must contain exactly path and sha256")
    expected_paths = contract["workflow_evidence_files"]
    require([item["path"] for item in evidence] == expected_paths,
            "workflow-compliance evidence paths differ from the frozen condition contract")
    for item in evidence:
        evidence_path = output_dir / item["path"]
        require(evidence_path.is_file(), f"workflow evidence file is missing: {item['path']}")
        require(sha256(evidence_path) == item["sha256"],
                f"workflow evidence hash mismatch: {item['path']}")


def declaration_absent_in_base(
    workspace: Path, checker_dir: Path, declaration: str, timeout: int
) -> bool:
    token = re.sub(r"[^A-Za-z0-9_]", "_", declaration)
    path = checker_dir / f"BaselineAbsence_{token}.lean"
    path.write_text(f"import BanditRLProof\n\n#check {declaration}\n", encoding="utf-8")
    outcome = run_checked(["lake", "env", "lean", str(path)], workspace, timeout)
    (checker_dir / f"BaselineAbsence_{token}.log").write_text(
        outcome["output"], encoding="utf-8"
    )
    lowered = outcome["output"].lower()
    return (
        outcome["exit_code"] != 0
        and not outcome["timed_out"]
        and ("unknown identifier" in lowered or "unknown constant" in lowered)
    )


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--pack", type=Path, required=True)
    parser.add_argument("--run-dir", type=Path, required=True)
    args = parser.parse_args()
    run_dir = args.run_dir.resolve()
    pack = args.pack.resolve()
    prepare.verify_pack(pack)
    config = load(pack / "execution_config.json")
    require(config["execution_status"] == "frozen_ready", "checker requires frozen pack")
    self_verify(pack, config)
    operator = run_dir / "operator"
    agent = run_dir / "agent"
    workspace = agent / "workspace"
    output_dir = agent / "output"
    require(workspace.is_dir(), "agent workspace is missing")
    require(output_dir.is_dir(), "agent output directory is missing")

    job = load(operator / "job.json")
    state_path = operator / "run_state.json"
    state = load(state_path)
    receipt_path = operator / "execution-receipt.json"
    require(state["status"] == "executed_unchecked", "run is not executed_unchecked")
    require(receipt_path.is_file(), "execution receipt is missing")
    require(state["execution_receipt_sha256"] == sha256(receipt_path),
            "run-state execution-receipt hash mismatch")
    receipt = load(receipt_path)
    aggregate = (pack / "aggregate.sha256").read_text(encoding="ascii").strip()
    require(state["sealed_pack_sha256"] == receipt["sealed_pack_sha256"] == aggregate,
            "run artifacts name different sealed packs")
    require(receipt["opaque_run_id"] == state["opaque_run_id"] == job["opaque_run_id"],
            "opaque run identifiers differ across execution artifacts")
    require(receipt["prepared_job_sha256"] == state["prepared_job_sha256"]
            == sha256(operator / "job.json"), "prepared job hash chain mismatch")
    require(receipt["workspace_manifest_sha256"] == state["workspace_manifest_sha256"]
            == sha256(operator / "workspace_manifest.json"),
            "workspace-manifest hash chain mismatch")
    require_adapter_artifacts_unchanged(operator, receipt)
    run_manifest = load(pack / "run_manifest.json")
    sealed_runs = [run for run in run_manifest["runs"] if run["run_id"] == job["semantic_run_id"]]
    require(len(sealed_runs) == 1, "job semantic run is absent or duplicated in sealed pack")
    sealed_run = sealed_runs[0]
    require(sealed_run["condition"] == job["condition"]
            and sealed_run["replicate"] == job["replicate"],
            "job condition/replicate differs from sealed run")
    current_agent_manifest = runner.file_manifest(agent)
    require(runner.manifest_sha256(current_agent_manifest)
            == receipt["completed_agent_manifest_sha256"]
            == state["completed_agent_manifest_sha256"],
            "agent view changed after adapter completion")
    require(receipt["protected_input_hashes"]["prompt.md"] == sha256(agent / "prompt.md")
            == job["prompt_sha256"], "prompt changed or differs from prepared job")
    require(receipt["protected_input_hashes"]["source/source.pdf"]
            == sha256(agent / "source" / "source.pdf") == job["source_sha256"],
            "source packet changed or differs from prepared job")
    for name in job["result_contract"]["required_files"]:
        require((output_dir / name).is_file(), f"required adapter output missing: {name}")
    result = load(output_dir / "result.json")
    adapter_response = load(operator / "adapter" / "response.json")
    require(result.get("schema_version") == 1, "result schema_version must be 1")
    require(result.get("opaque_run_id") == job["opaque_run_id"], "result run id mismatch")
    require(result.get("final_status") in {
        "compiled", "partial", "source_amended", "source_rejected",
        "library_blocked", "mathematically_blocked", "counterexample",
        "budget_exhausted", "infrastructure_failure"
    }, "unknown final status")
    termination_status = {
        "budget_exhausted": "budget_exhausted",
        "infrastructure_failure": "infrastructure_failure",
    }
    if adapter_response["termination"] in termination_status:
        require(result["final_status"] == termination_status[adapter_response["termination"]],
                "adapter termination conflicts with agent final status")
    else:
        require(result["final_status"] not in {"budget_exhausted", "infrastructure_failure"},
                "completed adapter response conflicts with agent final status")
    declarations = result.get("public_declarations", [])
    require(isinstance(declarations, list) and all(isinstance(item, str) for item in declarations),
            "public_declarations must be a string list")
    require(all(DECLARATION_NAME.fullmatch(item) for item in declarations),
            "public_declarations contains an unsafe or non-qualified Lean identifier")
    require(len(declarations) == len(set(declarations)),
            "public_declarations must not contain duplicates")
    require(result["final_status"] != "compiled" or bool(declarations),
            "compiled status requires at least one public declaration")
    require(isinstance(result.get("primary_grader_rationale"), str)
            and bool(result["primary_grader_rationale"].strip()),
            "result must include a nonempty primary_grader_rationale")
    require("source_amendment" not in result,
            "source amendment text must live only in source-amendment.md")
    amendment_path = output_dir / "source-amendment.md"
    require((result["final_status"] == "source_amended") == amendment_path.is_file(),
            "source_amended status and source-amendment.md presence must agree")
    if amendment_path.is_file():
        require(bool(amendment_path.read_text(encoding="utf-8").strip()),
                "source-amendment.md must be nonempty")
    validate_workflow_compliance(output_dir, job)

    baseline_manifest = load(operator / "workspace_manifest.json")
    baseline = {entry["path"]: entry["sha256"] for entry in baseline_manifest["files"]}
    changed, deleted = changed_files(workspace, baseline)
    forbidden_hits = scan_lean(workspace, changed)
    timeout = int(job["budgets"]["wall_clock_seconds"])
    checker_dir = operator / "checker"
    if checker_dir.exists() and not (checker_dir / "checker-result.json").exists():
        require(checker_dir.resolve().parent == operator.resolve(),
                "refusing to clean an unexpected checker path")
        shutil.rmtree(checker_dir)
    checker_dir.mkdir()
    policy = load(pack / "resource_policy.json")
    replay_workspace = checker_dir / "replay-workspace"
    paths = runner.selected_paths(config["workspace_base_commit"], policy, job["condition"])
    runner.extract_git_archive(config["workspace_base_commit"], paths, replay_workspace)
    baseline_absent = all(
        declaration_absent_in_base(replay_workspace, checker_dir, declaration, timeout)
        for declaration in declarations
    )
    require(result["final_status"] != "compiled" or baseline_absent,
            "compiled public declaration already exists in the frozen base")
    patch_path = output_dir / "lean-diff.patch"
    patch_check = run_checked(["git", "apply", "--check", str(patch_path)], replay_workspace, timeout)
    (checker_dir / "patch-check.log").write_text(patch_check["output"], encoding="utf-8")
    patch_apply = (
        run_checked(["git", "apply", str(patch_path)], replay_workspace, timeout)
        if patch_check["exit_code"] == 0 and not patch_check["timed_out"]
        else None
    )
    if patch_apply is not None:
        (checker_dir / "patch-apply.log").write_text(patch_apply["output"], encoding="utf-8")
    replay_changed, replay_deleted = changed_files(replay_workspace, baseline)
    content_reproduced = (
        patch_apply is not None
        and patch_apply["exit_code"] == 0
        and not patch_apply["timed_out"]
        and replay_changed == changed
        and replay_deleted == deleted
        and all(sha256(replay_workspace / relative) == sha256(workspace / relative)
                for relative in changed if (replay_workspace / relative).is_file())
    )
    replay_forbidden_hits = scan_lean(replay_workspace, replay_changed)
    require(result["final_status"] != "compiled" or declarations_appear_in_changes(
        replay_workspace, replay_changed, declarations
    ), "compiled declarations must be introduced by the replayed Lean patch")
    cache_prelude_argv = config["posthoc_checker"]["cache_prelude_argv"]
    cache_prelude = (
        run_checked(cache_prelude_argv, replay_workspace, timeout)
        if cache_prelude_argv else None
    )
    if cache_prelude is not None:
        (checker_dir / "cache-prelude.log").write_text(
            cache_prelude["output"], encoding="utf-8"
        )
    build = run_checked(["lake", "build"], replay_workspace, timeout)
    (checker_dir / "neutral-build.log").write_text(build["output"], encoding="utf-8")
    canary: dict[str, Any] | None = None
    if declarations:
        canary_path = checker_dir / "NeutralDeclarationCanary.lean"
        canary_path.write_text(
            "import BanditRLProof\n\n"
            + "\n".join(f"#check {name}\n#print axioms {name}" for name in declarations)
            + "\n",
            encoding="utf-8",
        )
        canary = run_checked(
            ["lake", "env", "lean", str(canary_path)], replay_workspace, timeout
        )
        (checker_dir / "neutral-canary.log").write_text(
            canary["output"], encoding="utf-8"
        )

    build_pass = build["exit_code"] == 0 and not build["timed_out"]
    axiom_dependencies = set() if canary is None else parsed_axioms(canary["output"])
    unexpected_axioms = sorted(axiom_dependencies - ALLOWED_AXIOMS)
    canary_pass = (
        canary is None
        or (
            canary["exit_code"] == 0
            and not canary["timed_out"]
            and not unexpected_axioms
        )
    )
    artifact_replay_success = (
        content_reproduced and build_pass and canary_pass
        and not replay_forbidden_hits and not replay_deleted
    )
    checker_pass = (
        artifact_replay_success and not forbidden_hits and not deleted and baseline_absent
    )
    checker_result = {
        "schema_version": 1,
        "opaque_run_id": job["opaque_run_id"],
        "checker_pass": checker_pass,
        "changed_files": changed,
        "deleted_files": deleted,
        "forbidden_lean_hits": forbidden_hits,
        "replay_forbidden_lean_hits": replay_forbidden_hits,
        "replay_changed_files": replay_changed,
        "replay_deleted_files": replay_deleted,
        "patch_check": {key: value for key, value in patch_check.items() if key != "output"},
        "patch_apply": (
            None if patch_apply is None
            else {key: value for key, value in patch_apply.items() if key != "output"}
        ),
        "replayed_content_matches_completed_workspace": content_reproduced,
        "public_declarations_absent_from_frozen_base": baseline_absent,
        "cache_prelude": (
            None if cache_prelude is None
            else {key: value for key, value in cache_prelude.items() if key != "output"}
        ),
        "neutral_build": {key: value for key, value in build.items() if key != "output"},
        "neutral_canary": (
            None if canary is None
            else {key: value for key, value in canary.items() if key != "output"}
        ),
        "public_declarations": declarations,
        "axiom_dependencies": sorted(axiom_dependencies),
        "unexpected_axioms": unexpected_axioms,
        "artifact_replay_success": artifact_replay_success,
        "workflow_compliance_pass": True,
        "execution_usage": receipt["usage"],
        "sealed_pack_sha256": aggregate,
        "execution_receipt_sha256": state["execution_receipt_sha256"],
        "completed_agent_manifest_sha256": receipt["completed_agent_manifest_sha256"],
        "agent_claimed_status": result["final_status"],
        "claim_consistent_with_checker": (
            result["final_status"] != "compiled" or checker_pass
        ),
    }
    dump(checker_dir / "checker-result.json", checker_result)
    state.update({
        "status": "checked",
        "checker_result_sha256": sha256(checker_dir / "checker-result.json"),
    })
    dump(state_path, state)
    print(
        f"neutral checker {'PASS' if checker_pass else 'FAIL'} for {job['opaque_run_id']}: "
        f"changed={len(changed)}, deleted={len(deleted)}, forbidden={len(forbidden_hits)}"
    )
    raise SystemExit(0 if checker_pass else 1)


if __name__ == "__main__":
    main()
