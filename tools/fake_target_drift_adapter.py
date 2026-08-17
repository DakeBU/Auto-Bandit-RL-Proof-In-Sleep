#!/usr/bin/env python3
"""Deterministic local fixture for excluded target-drift infrastructure smoke tests.

This is not a model provider or security sandbox.  It only exercises the sealed
request/response, artifact, replay, checker, and grading plumbing.
"""

from __future__ import annotations

import argparse
import difflib
import hashlib
import json
import subprocess
import time
from pathlib import Path
from typing import Any


def load(path: Path) -> dict[str, Any]:
    return json.loads(path.read_text(encoding="utf-8"))


def dump(path: Path, value: Any) -> None:
    path.write_text(
        json.dumps(value, indent=2, sort_keys=True, ensure_ascii=False) + "\n",
        encoding="utf-8",
    )


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def unified_patch(relative: str, before: str | None, after: str) -> str:
    return "".join(difflib.unified_diff(
        [] if before is None else before.splitlines(keepends=True),
        after.splitlines(keepends=True),
        fromfile="/dev/null" if before is None else f"a/{relative}",
        tofile=f"b/{relative}",
    ))


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--request", type=Path, required=True)
    parser.add_argument("--response", type=Path, required=True)
    parser.add_argument("--trace", type=Path, required=True)
    parser.add_argument("--agent-mount", type=Path, required=True)
    parser.add_argument("--adapter-id", required=True)
    parser.add_argument("--adapter-version", required=True)
    parser.add_argument("--model-id", required=True)
    parser.add_argument("--immutable-model-version", required=True)
    parser.add_argument("--image-digest", required=True)
    parser.add_argument("--budget-attestation", required=True)
    parser.add_argument("--isolation-attestation", required=True)
    args = parser.parse_args()

    request = load(args.request)
    agent = args.agent_mount.resolve()
    workspace = agent / "workspace"
    output = agent / "output"
    output.mkdir()
    root_path = workspace / "BanditRLProof.lean"
    before_root = root_path.read_text(encoding="utf-8")
    import_line = "import BanditRLProof.TargetDriftSmoke\n"
    after_root = before_root if import_line in before_root else before_root + import_line
    root_path.write_text(after_root, encoding="utf-8")
    smoke_relative = "BanditRLProof/TargetDriftSmoke.lean"
    smoke_text = (
        "namespace BanditRLProof\n\n"
        "theorem targetDriftSmokeWitness : True := by\n"
        "  trivial\n\n"
        "end BanditRLProof\n"
    )
    (workspace / smoke_relative).write_text(smoke_text, encoding="utf-8")
    patch = unified_patch("BanditRLProof.lean", before_root, after_root)
    patch += unified_patch(smoke_relative, None, smoke_text)
    (output / "lean-diff.patch").write_text(patch, encoding="utf-8")

    started = time.monotonic()
    cache = subprocess.run(
        ["lake", "exe", "cache", "get"], cwd=workspace,
        stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True,
        encoding="utf-8", errors="replace",
        timeout=int(request["budgets"]["wall_clock_seconds"]), check=False,
    )
    build = subprocess.run(
        ["lake", "build"], cwd=workspace, stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT, text=True, encoding="utf-8", errors="replace",
        timeout=max(1, int(request["budgets"]["wall_clock_seconds"])
                    - int(time.monotonic() - started)), check=False,
    )
    wall = time.monotonic() - started
    (output / "build.log").write_text(
        "[cache prelude]\n" + cache.stdout + "\n[build]\n" + build.stdout,
        encoding="utf-8",
    )

    contract = request["result_contract"]
    for name in contract["workflow_evidence_files"]:
        path = output / name
        if path.suffix == ".json":
            dump(path, {"schema_version": 1, "fixture": True, "artifact": name})
        else:
            path.write_text(
                f"Excluded infrastructure-smoke fixture artifact: {name}\n",
                encoding="utf-8",
            )
    evidence = [
        {"path": name, "sha256": sha256(output / name)}
        for name in contract["workflow_evidence_files"]
    ]
    dump(output / "workflow-compliance.json", {
        "schema_version": 1,
        "opaque_run_id": request["opaque_run_id"],
        "workflow_id": contract["workflow_id"],
        "evidence_files": evidence,
    })
    dump(output / "result.json", {
        "schema_version": 1,
        "opaque_run_id": request["opaque_run_id"],
        "final_status": "compiled" if build.returncode == 0 else "partial",
        "public_declarations": (
            ["BanditRLProof.targetDriftSmokeWitness"] if build.returncode == 0 else []
        ),
        "primary_grader_rationale": (
            "A fresh witness declaration compiled; this excluded infrastructure smoke "
            "test makes no source-adequacy claim."
        ),
    })
    (output / "explanation.md").write_text(
        "Excluded deterministic infrastructure smoke test; no model result.\n",
        encoding="utf-8",
    )

    usage = {
        "input_tokens": 32,
        "output_tokens": 32,
        "tool_calls": 1,
        "build_attempts": 1,
        "recovery_tool_calls": 0,
        "infrastructure_retries": 0,
        "wall_seconds": round(wall, 6),
        "cost_usd": 0.0,
    }
    trace = [
        {"sequence": 0, "kind": "tool_call", "recovery_phase": False},
        {"sequence": 1, "kind": "build_attempt", "success": build.returncode == 0},
        {"sequence": 2, "kind": "usage_summary", "usage": usage},
    ]
    args.trace.write_text(
        "".join(json.dumps(event, sort_keys=True) + "\n" for event in trace),
        encoding="utf-8",
    )
    dump(args.response, {
        "schema_version": 1,
        "opaque_run_id": request["opaque_run_id"],
        "adapter_id": args.adapter_id,
        "adapter_version": args.adapter_version,
        "model_id": args.model_id,
        "immutable_model_version": args.immutable_model_version,
        "replicate": request["replicate"],
        "container_or_sandbox_image_digest": args.image_digest,
        "budget_enforcement_attestation": args.budget_attestation,
        "filesystem_network_process_attestation": args.isolation_attestation,
        "termination": "completed",
        "provider_request_ids": ["excluded-local-smoke-fixture"],
        "usage": usage,
    })


if __name__ == "__main__":
    main()
