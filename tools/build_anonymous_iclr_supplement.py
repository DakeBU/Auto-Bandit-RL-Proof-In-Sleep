#!/usr/bin/env python3
"""Build a deterministic, positive-allowlist anonymous Lean/code supplement."""

import argparse
import hashlib
import json
import re
import subprocess
import sys
import zipfile
from pathlib import Path


REPO_ROOT = Path(__file__).resolve().parents[1]
ARCHIVE_ROOT = "abrl-anonymous-artifact"
ARCHIVE_NAME = "ABRL-ICLR-2027-anonymous-lean-code.zip"
FIXED_ZIP_TIME = (2026, 1, 1, 0, 0, 0)
TEXT_PAYLOAD_SUFFIXES = {
    ".Containerfile", ".apparmor", ".json", ".lean", ".md", ".py", ".sh", ".toml",
    ".txt", ".yaml", ".yml",
}
TEXT_PAYLOAD_NAMES = {"LICENSE", "lean-toolchain"}

BLOCKED_BYTES = (
    b"dakebu",
    b"dake bu",
    b"ji cheng",
    b"bo xue",
    b"atsushi nitanda",
    b"hau-san wong",
    b"qingfu zhang",
    b"city university of hong kong",
    b"auto-bandit-rl-proof-in-sleep",
    b"git.overleaf.com",
    b"6a3f743d1f1f53f96990c557",
    b"d43bfeee56fb0c1c35cf5af9fc1a7fdc3e0c37b9",
    b"cb5d50be148c691cc595ed9fd2f535c42506fada",
)
WINDOWS_PATH = re.compile(
    br"(?i)(?<![a-z])[a-z]:[\\/](?:users[\\/][^\\/\s]+|home[\\/][^\\/\s]+|wt[\\/]|code[\\/])"
)
HOST_HOME = re.compile(br"(?i)/(?:home|users)/[^/\s]+/")
EMAIL = re.compile(br"(?i)\b[a-z0-9._%+-]+@[a-z0-9.-]+\.[a-z]{2,}\b")
PUBLIC_WORKSPACE_BASE_COMMIT = "d43bfeee56fb0c1c35cf5af9fc1a7fdc3e0c37b9"
PUBLIC_CANDIDATE_RUN_ID = "32137509103"
PUBLIC_CANDIDATE_RUN_URL = (
    "https://github.com/DakeBU/Auto-Bandit-RL-Proof-In-Sleep/"
    "actions/runs/32137509103"
)
PUBLIC_ISOLATION_CANDIDATE_RUN_ID = "32419343467"
PUBLIC_ISOLATION_CANDIDATE_RUN_URL = (
    "https://github.com/DakeBU/Auto-Bandit-RL-Proof-In-Sleep/"
    "actions/runs/32419343467"
)
PUBLIC_AGENT_LIFECYCLE_RUN_ID = "32436339541"
PUBLIC_AGENT_LIFECYCLE_RUN_URL = (
    "https://github.com/DakeBU/Auto-Bandit-RL-Proof-In-Sleep/"
    "actions/runs/32436339541"
)
PUBLIC_AGENT_IMAGE_RUN_ID = "32464814750"
PUBLIC_AGENT_IMAGE_RUN_URL = (
    "https://github.com/DakeBU/Auto-Bandit-RL-Proof-In-Sleep/"
    "actions/runs/32464814750"
)
PUBLIC_CANDIDATE_RECORD = (
    "evaluation/target-drift-v2/checker-image-candidate-32137509103.json"
)
PUBLIC_ISOLATION_CANDIDATE_RECORD = (
    "evaluation/target-drift-v2/checker-image-candidate-32419343467.json"
)
PUBLIC_AGENT_LIFECYCLE_RECORD = (
    "evaluation/target-drift-v2/agent-lifecycle-candidate-32436339541.json"
)
PUBLIC_AGENT_IMAGE_RECORD = (
    "evaluation/target-drift-v2/agent-image-candidate-32464814750.json"
)
ANONYMOUS_CANDIDATE_RECORD = (
    "evaluation/target-drift-v2/checker-image-candidate-record.json"
)
ANONYMOUS_ISOLATION_CANDIDATE_RECORD = (
    "evaluation/target-drift-v2/checker-image-isolation-candidate-record.json"
)
ANONYMOUS_AGENT_LIFECYCLE_RECORD = (
    "evaluation/target-drift-v2/agent-lifecycle-candidate-record.json"
)
ANONYMOUS_AGENT_IMAGE_RECORD = (
    "evaluation/target-drift-v2/agent-image-candidate-record.json"
)

DELAYED_IMPLEMENTATION_IDS = (
    "DELAYED-FEEDBACK-SOURCE-ACCOUNTING",
    "DELAYED-FEEDBACK-CAUSAL-PROCESSING",
    "DELAYED-SAPO-ACTIVE-ALLOCATION",
    "DELAYED-SAPO-ELIMINATION-ACTION-LAW",
    "DELAYED-SAPO-GOOD-EVENT-D9-PROJECTION",
    "DELAYED-SAPO-D8-D9-ASSEMBLY",
)
DELAYED_DIAGNOSTIC_ID = "DELAYED-SAPO-D10-D12-GAP-ORDERING-AUDIT"
SUCCINCT_AUDIT_ID = "NEURIPS-2025-SUCCINCT-LOWER-BOUND-GEOMETRY-AUDIT"
SGB_AUDIT_ID = "NEURIPS-2025-STOCHASTIC-GRADIENT-BANDIT-MECHANISM-AUDIT"
SGB_FINITE_ALGEBRA_FILE = "BanditRLProof/Algorithms/StochasticGradientBanditAudit.lean"
SGB_GENERATED_HISTORY_FILE = (
    "BanditRLProof/Algorithms/StochasticGradientBanditTrajectoryAudit.lean"
)
SGB_FINITE_ALGEBRA_DECLARATION_COUNT = 26
SGB_GENERATED_HISTORY_DECLARATION_COUNT = 18
SGB_GENERATED_TRAJECTORY_DECLARATIONS = frozenset({
    "BanditRLProof.StochasticGradientBandit.trajectoryKernel",
    "BanditRLProof.StochasticGradientBandit.trajectoryMeasure_condDistrib_action_zero_given_environment",
    "BanditRLProof.StochasticGradientBandit.trajectoryMeasure_condDistrib_action",
    "BanditRLProof.StochasticGradientBandit.trajectoryMeasure_condDistrib_nextPair_given_environment_prefix",
})
SGB_CONDITIONAL_LAW_BRIDGE_DECLARATIONS = frozenset({
    "BanditRLProof.StochasticGradientBandit.integral_measurableEnvironmentInitialPairKernel_sourceIncrement_eq_expectedSourceIncrement",
    "BanditRLProof.StochasticGradientBandit.integral_historyStepKernel_sourceIncrement_eq_expectedSourceIncrement",
    "BanditRLProof.StochasticGradientBandit.integral_measurableEnvironmentHistoryStepKernel_sourceIncrement_eq_expectedSourceIncrement",
    "BanditRLProof.StochasticGradientBandit.integral_measurableEnvironmentHistoryStepKernel_sourceIncrement_eq_gapCoordinate",
})
EXPECTED_INDEX_EXCEPTIONS = (
    "BanditRLProof.DelayedFeedback.ActionTimeView.ext",
    "BanditRLProof.LowerBounds.IsConsistentRegret.add",
    "BanditRLProof.LowerBounds.IsConsistentRegret.eventually_add_le_rpow",
    "BanditRLProof.LowerBounds.IsConsistentRegret.eventually_log_add_div_log_le",
)
SOURCE_RESULT_IDS = (
    "RL-UNBOUNDED-HITTINGAFTER-EXPECTED-UPPER-BOUND",
    "ETC-CANONICAL-SUBGAUSSIAN-REGRET",
    "TEXTBOOK-PART-IV-CH13-BASIC-IDEAS-LEAN-SPINE",
    "TEXTBOOK-PART-IV-THEOREM-13-1-GAUSSIAN-MINIMAX",
    "TEXTBOOK-PART-IV-CH14-INFORMATION-THEORY-LEAN-SPINE",
    "TEXTBOOK-PART-IV-CH15-GAUSSIAN-KL-DEPENDENCY-SLICE",
    "TEXTBOOK-PART-IV-CH15-SAME-POLICY-HISTORY-KL-DECOMPOSITION",
    "TEXTBOOK-PART-IV-CH15-GAUSSIAN-MINIMAX-LOWER-BOUND",
    "TEXTBOOK-PART-IV-CH16-CONSISTENCY-DINF-DEPENDENCY-SLICE",
    "TEXTBOOK-PART-IV-CH16-SOURCE-TERMINALS",
    "TEXTBOOK-PART-IV-CH17-FIRST-MOMENT-AND-TAIL-DEPENDENCY-SLICE",
    "TEXTBOOK-PART-IV-CH17-SOURCE-TERMINALS",
) + DELAYED_IMPLEMENTATION_IDS + (
    DELAYED_DIAGNOSTIC_ID,
    "NEURIPS-2025-DELAYED-BOBW-CENTRAL-ENDPOINTS",
    SUCCINCT_AUDIT_ID,
    SGB_AUDIT_ID,
    "TARGET-DRIFT-V2-CONTROLLED-EVALUATION",
)

TARGET_DRIFT_TOOLS = (
    "tools/analyze_target_drift_execution.py",
    "tools/assemble_target_drift_grades.py",
    "tools/audit_target_drift_wording.py",
    "tools/build_target_drift_completion_ledger.py",
    "tools/check_target_drift_container_controller.py",
    "tools/check_target_drift_inner.py",
    "tools/check_target_drift_run.py",
    "tools/codex_target_drift_adapter.py",
    "tools/fake_target_drift_adapter.py",
    "tools/fake_target_drift_cache_prelude.py",
    "tools/fake_target_drift_checker_sandbox.py",
    "tools/finalize_target_drift_config.py",
    "tools/launch_target_drift_checker_container.py",
    "tools/prepare_target_drift_agent_image.py",
    "tools/prepare_target_drift_checker_image.py",
    "tools/prepare_target_drift_checker_probe_config.py",
    "tools/prepare_target_drift_execution.py",
    "tools/prepare_target_drift_grading.py",
    "tools/prepare_target_drift_smoke.py",
    "tools/record_target_drift_agent_image_probe.py",
    "tools/record_target_drift_agent_lifecycle_probe.py",
    "tools/record_target_drift_checker_isolation_probe.py",
    "tools/run_target_drift_execution.py",
    "tools/run_target_drift_schedule.py",
    "tools/run_target_drift_smoke.py",
    "tools/target_drift_checker_cache_manifest.py",
    "tools/target_drift_agent_pid1.py",
    "tools/test_target_drift_agent_image.py",
    "tools/test_target_drift_analysis.py",
    "tools/test_target_drift_agent_lifecycle.py",
    "tools/test_target_drift_completion_ledger.py",
    "tools/test_codex_target_drift_adapter.py",
    "tools/test_target_drift_execution.py",
    "tools/test_target_drift_runtime.py",
    "tools/test_target_drift_smoke.py",
    "tools/validate_target_drift_suite.py",
    "tools/validate_target_drift_suite_v2.py",
)

# The evaluation layer is result-free by construction.  New tracked files must
# be reviewed and added explicitly so that run records, grades, or analyses can
# never enter the anonymous artifact through a recursive directory copy.
TARGET_DRIFT_PROTOCOL_FILES = (
    "evaluation/target-drift-v1/README.md",
    "evaluation/target-drift-v1/challenges.json",
    "evaluation/target-drift-v1/execution-template.json",
    "evaluation/target-drift-v1/grading-rubric.json",
    "evaluation/target-drift-v1/prompts/abrl.md",
    "evaluation/target-drift-v1/prompts/compile-only.md",
    "evaluation/target-drift-v1/prompts/source-aware-blueprint.md",
    "evaluation/target-drift-v1/protocol.json",
    "evaluation/target-drift-v1/source-files.template.json",
    "evaluation/target-drift-v2/README.md",
    "evaluation/target-drift-v2/adapter-contract.json",
    "evaluation/target-drift-v2/agent-image-sources.json",
    "evaluation/target-drift-v2/agent-image.Containerfile",
    "evaluation/target-drift-v2/agent-codex-native.apparmor",
    "evaluation/target-drift-v2/agent-lifecycle.Containerfile",
    "evaluation/target-drift-v2/agent-sandbox-contract.json",
    PUBLIC_CANDIDATE_RECORD,
    PUBLIC_ISOLATION_CANDIDATE_RECORD,
    PUBLIC_AGENT_LIFECYCLE_RECORD,
    PUBLIC_AGENT_IMAGE_RECORD,
    "evaluation/target-drift-v2/checker-image-sbom.template.json",
    "evaluation/target-drift-v2/checker-image.Containerfile",
    "evaluation/target-drift-v2/checker-isolation-probe.excluded-fixture.json",
    "evaluation/target-drift-v2/checker-isolation-probe.template.json",
    "evaluation/target-drift-v2/checker-sandbox-contract.json",
    "evaluation/target-drift-v2/execution-template.json",
    "evaluation/target-drift-v2/grader-prompt.md",
    "evaluation/target-drift-v2/grading-rubric.json",
    "evaluation/target-drift-v2/missing-run-policy.json",
    "evaluation/target-drift-v2/paired-requirements.json",
    "evaluation/target-drift-v2/protocol.json",
    "evaluation/target-drift-v2/resource-policy.json",
    "evaluation/target-drift-v2/source-files.template.json",
    "evaluation/target-drift-v2/text-only-audit-prompt.md",
)

TARGET_DRIFT_WORKFLOW_FILES = (
    ".github/workflows/target-drift-agent-image.yml",
    ".github/workflows/target-drift-agent-lifecycle.yml",
)

EXPLICIT_COPIES = {
    "lean-toolchain": "lean-toolchain",
    "lakefile.lean": "lakefile.lean",
    "lake-manifest.json": "lake-manifest.json",
    "BanditRLProof.lean": "BanditRLProof.lean",
    "Tests.lean": "Tests.lean",
    "tools/ProofGraphExport.lean": "tools/ProofGraphExport.lean",
    "tools/proof_graph_lab.py": "tools/proof_graph_lab.py",
    "tools/test_proof_graph_lab.py": "tools/test_proof_graph_lab.py",
    "artifact/anonymous-supplement/README.md": "README.md",
    "artifact/anonymous-supplement/LICENSE": "LICENSE",
    "artifact/anonymous-supplement/THIRD_PARTY_NOTICES.md": "THIRD_PARTY_NOTICES.md",
    "artifact/anonymous-supplement/verify_artifact.py": "artifact/verify_artifact.py",
    "research-wiki/retrieval-index/local_lean_declarations.json":
        "evidence/local_lean_declarations.json",
    "research-wiki/papers/neurips-2025-delayed-bobw-audit.md":
        "evidence/delayed-feedback-audit.md",
    "proof-obligations/PAPER-AUDIT-NEURIPS-2025-DELAYED-BOBW-FEASIBILITY.md":
        "evidence/delayed-feedback-proof-obligations.md",
}

EVIDENCE_JSON = {
    "research-wiki/papers/prospective-audit-2025-freeze.json":
        "evidence/source-freeze.json",
    "research-wiki/proof-graph/benchmark_measurements.json":
        "evidence/proof-graph/historical-local-measurements.json",
    "research-wiki/proof-graph/benchmark_roots.json":
        "evidence/proof-graph/benchmark_roots.json",
    "research-wiki/proof-graph/cng_candidate_evaluation.json":
        "evidence/proof-graph/cng_candidate_evaluation.json",
    "research-wiki/proof-graph/cng_candidate_roots.json":
        "evidence/proof-graph/cng_candidate_roots.json",
    "research-wiki/proof-graph/novelty_audit.json":
        "evidence/proof-graph/novelty_audit.json",
    "research-wiki/proof-graph/proof_cost.schema.json":
        "evidence/proof-graph/proof_cost.schema.json",
}

# These versioned files are duplicated at their authoring-tree paths because
# the shipped proof-graph unit tests deliberately check their cross-file
# contracts in place.  The reader-facing copies above remain the stable
# evidence entrypoints.
PROOF_GRAPH_TEST_EVIDENCE = (
    "research-wiki/proof-graph/benchmark_report.json",
    "research-wiki/proof-graph/benchmark_roots.json",
    "research-wiki/proof-graph/cng_candidate_evaluation.json",
    "research-wiki/proof-graph/cng_candidate_roots.json",
    "research-wiki/proof-graph/novelty_audit.json",
    "research-wiki/proof-graph/proof_cost.schema.json",
)


def canonical_json(value):
    return (json.dumps(value, ensure_ascii=False, indent=2, sort_keys=True) + "\n").encode("utf-8")


def is_text_payload_path(rel):
    path = Path(rel)
    return path.name in TEXT_PAYLOAD_NAMES or path.suffix in TEXT_PAYLOAD_SUFFIXES


def canonical_text_bytes(rel, data):
    if not is_text_payload_path(rel):
        return data
    text = data.decode("utf-8")
    return text.replace("\r\n", "\n").replace("\r", "\n").encode("utf-8")


def sha256_bytes(data):
    return hashlib.sha256(data).hexdigest()


def sha256_file(path):
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        for chunk in iter(lambda: handle.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


def load_json(path):
    return json.loads(path.read_text(encoding="utf-8"))


def require_safe_relative(path):
    pure = Path(path)
    if pure.is_absolute() or ".." in pure.parts or not pure.parts:
        raise ValueError("unsafe archive path: {!r}".format(path))
    return pure.as_posix()


def require_anonymous_bytes(rel, data):
    lowered = data.lower()
    for marker in BLOCKED_BYTES:
        if marker in lowered:
            raise ValueError("identity marker in {}: {}".format(rel, marker.decode("ascii")))
    if WINDOWS_PATH.search(data):
        raise ValueError("absolute Windows path in {}".format(rel))
    if HOST_HOME.search(data):
        raise ValueError("absolute host home path in {}".format(rel))
    if EMAIL.search(data):
        raise ValueError("email address in {}".format(rel))


def sanitize_json(value):
    if isinstance(value, dict):
        cleaned = {}
        for key, item in value.items():
            if key == "dependency_build_root":
                cleaned[key] = "<isolated-build-root>"
            elif key in ("frozen_git_commit", "git_commit"):
                cleaned["frozen_source_snapshot"] = "<anonymous-source-snapshot>"
            else:
                cleaned[key] = sanitize_json(item)
        return cleaned
    if isinstance(value, list):
        return [sanitize_json(item) for item in value]
    return value


def git_tracked_files():
    result = subprocess.run(
        ["git", "ls-files", "-z"],
        cwd=str(REPO_ROOT),
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        check=True,
    )
    return {item.decode("utf-8").replace("\\", "/")
            for item in result.stdout.split(b"\0") if item}


def source_tree_files(tracked):
    files = []
    for prefix in ("BanditRLProof", "Tests"):
        for path in sorted((REPO_ROOT / prefix).rglob("*.lean")):
            rel = path.relative_to(REPO_ROOT).as_posix()
            if rel not in tracked:
                raise ValueError("untracked Lean source under allowlisted tree: " + rel)
            files.append(rel)
    return files


def evaluation_files(tracked):
    allowed = set(TARGET_DRIFT_PROTOCOL_FILES)
    actual = {
        rel for rel in tracked
        if rel.startswith("evaluation/target-drift-v1/")
        or rel.startswith("evaluation/target-drift-v2/")
    }
    missing = sorted(allowed - actual)
    unexpected = sorted(actual - allowed)
    if missing:
        raise ValueError("missing allowlisted evaluation source: " + ", ".join(missing))
    if unexpected:
        raise ValueError(
            "unreviewed evaluation file would enter result-free artifact: "
            + ", ".join(unexpected)
        )
    return sorted(allowed)


def anonymous_base_manifest(payload):
    base_paths = [
        rel for rel in sorted(payload)
        if rel == "BanditRLProof.lean"
        or rel == "Tests.lean"
        or rel in ("lean-toolchain", "lakefile.lean", "lake-manifest.json")
        or rel.startswith("BanditRLProof/")
        or rel.startswith("Tests/")
    ]
    digest = hashlib.sha256()
    rows = []
    for rel in base_paths:
        data = payload[rel]
        item_digest = sha256_bytes(data)
        rows.append({"path": rel, "bytes": len(data), "sha256": item_digest})
        digest.update(rel.encode("utf-8") + b"\0")
        digest.update(item_digest.encode("ascii") + b"\n")
    tree_digest = digest.hexdigest()
    return {
        "schema_version": 1,
        "status": "anonymous-source-snapshot",
        "tree_sha256": tree_digest,
        "schema_compatibility_reference": tree_digest[:40],
        "git_object_database_included": False,
        "materializable_by_target_drift_runner": False,
        "interpretation": (
            "The full digest binds the packaged Lean/test base. The 40-hex reference is only "
            "a schema-compatible anonymous placeholder, not a Git commit object."
        ),
        "files": rows,
    }


def anonymous_agent_image_candidate(candidate, anonymous_reference):
    """Keep only self-contained qualitative evidence from the public CI run.

    Public-run timestamps, durations, image/source digests, and the downloaded
    artifact inventory are useful in the public repository but are unique
    linkage fingerprints in a double-blind archive.  The anonymous supplement
    therefore uses a positive allowlist and retains only claims that can be
    interpreted without locating the public workflow run.
    """
    def require_dict(parent, key):
        value = parent.get(key)
        if not isinstance(value, dict):
            raise ValueError("combined agent-image candidate is missing " + key)
        return value

    def pick(parent, keys, label):
        missing = [key for key in keys if key not in parent]
        if missing:
            raise ValueError(
                "combined agent-image candidate is missing {} fields: {}".format(
                    label, ", ".join(missing)
                )
            )
        return {key: parent[key] for key in keys}

    workflow = require_dict(candidate, "workflow_run")
    public_candidate = require_dict(candidate, "candidate")
    sandbox = require_dict(candidate, "sandbox_probe")
    lifecycle = require_dict(candidate, "lifecycle_probe")
    checks = require_dict(candidate, "hash_chain_checks")
    if not checks or any(type(value) is not bool for value in checks.values()):
        raise ValueError("combined agent-image hash checks must be literal booleans")
    nonclaims = candidate.get("nonclaims")
    if not isinstance(nonclaims, list) or not all(
        isinstance(value, str) for value in nonclaims
    ):
        raise ValueError("combined agent-image nonclaims must be a string list")

    anonymous_candidate = {
        **pick(candidate, ("schema_version", "suite_id", "evidence_type"), "top-level"),
        "recorded_at_utc": "<redacted-public-run-time>",
        "workflow_run": {
            "id": "<redacted-public-run-id>",
            "url": "<redacted-public-run-url>",
            "head_commit": "<anonymous-builder-snapshot>",
            **pick(
                workflow,
                ("conclusion", "artifact_retention_days"),
                "workflow",
            ),
            "job_duration": "<redacted-public-run-duration>",
        },
        "candidate": {
            **pick(
                public_candidate,
                (
                    "status",
                    "published",
                    "codex_version",
                    "toolchain_release",
                    "lean_version",
                    "lake_version",
                    "offline_toolchain_probe",
                    "runtime",
                    "apparmor_profile",
                ),
                "candidate",
            ),
            "workspace_base_commit": anonymous_reference,
        },
        "sandbox_probe": pick(
            sandbox,
            (
                "status",
                "workspace_write_succeeded",
                "persistent_outside_workspace_write_denied",
                "provider_auth_unreadable",
                "openai_api_key_absent",
                "outer_same_ipv4_endpoint_reachable",
                "inner_network_denied",
                "inner_network_denial_stage",
                "inner_network_errno",
                "inner_network_error_name",
                "fresh_pid_namespace",
                "observed_apparmor_profile",
                "observed_apparmor_mode",
                "apparmor_profile_attached",
            ),
            "sandbox probe",
        ),
        "lifecycle_probe": pick(
            lifecycle,
            (
                "status",
                "controller_pid",
                "pre_crash_heartbeat_observations",
                "post_cleanup_heartbeat_observation",
                "escaped_descendant_heartbeat_frozen",
                "container_absent_after_control_loss",
                "controller_exit_reason",
                "direct_child_return_code",
            ),
            "lifecycle probe",
        ),
        "hash_chain_checks": dict(checks),
        "nonclaims": list(nonclaims),
    }
    return anonymous_candidate


def anonymous_checker_image_candidate(candidate, anonymous_reference):
    """Remove public-run linkage fields from a checker-image candidate record."""
    workflow = candidate.get("workflow_run")
    public_candidate = candidate.get("candidate")
    checks = candidate.get("hash_chain_checks")
    nonclaims = candidate.get("nonclaims")
    if not isinstance(workflow, dict) or not isinstance(public_candidate, dict):
        raise ValueError("checker-image candidate structure changed")
    if not isinstance(checks, dict) or not checks or any(
        type(value) is not bool for value in checks.values()
    ):
        raise ValueError("checker-image hash checks must be literal booleans")
    if not isinstance(nonclaims, list) or not all(
        isinstance(value, str) for value in nonclaims
    ):
        raise ValueError("checker-image nonclaims must be a string list")

    def pick(parent, keys, label):
        missing = [key for key in keys if key not in parent]
        if missing:
            raise ValueError(
                "checker-image candidate is missing {} fields: {}".format(
                    label, ", ".join(missing)
                )
            )
        return {key: parent[key] for key in keys}

    candidate_fields = (
        "status",
        "published",
        "toolchain_release",
        "lean_version",
        "lake_version",
        "offline_toolchain_probe",
        "worker_uid",
    )
    result = {
        **pick(candidate, ("schema_version", "suite_id", "evidence_type"), "top-level"),
        "recorded_at_utc": "<redacted-public-run-time>",
        "workflow_run": {
            "id": "<redacted-public-run-id>",
            "url": "<redacted-public-run-url>",
            "head_commit": "<anonymous-builder-snapshot>",
            **pick(
                workflow,
                ("conclusion", "artifact_retention_days"),
                "workflow",
            ),
            "job_duration": "<redacted-public-run-duration>",
        },
        "candidate": {
            **pick(public_candidate, candidate_fields, "candidate"),
            "workspace_base_commit": anonymous_reference,
        },
        "hash_chain_checks": dict(checks),
        "nonclaims": list(nonclaims),
    }
    isolation = candidate.get("isolation_probes")
    if isolation is not None:
        if not isinstance(isolation, dict) or not isolation or any(
            type(value) is not bool for value in isolation.values()
        ):
            raise ValueError("checker isolation probes must be literal booleans")
        result["candidate"].update(pick(
            public_candidate,
            ("worker_effective_capabilities_hex", "runtime"),
            "isolation candidate",
        ))
        result["isolation_probes"] = dict(isolation)
    return result


def anonymous_agent_lifecycle_candidate(candidate):
    """Retain the lifecycle result without its public workflow fingerprint."""
    workflow = candidate.get("workflow_run")
    public_candidate = candidate.get("candidate")
    runtime = candidate.get("runtime")
    checks = candidate.get("hash_chain_checks")
    nonclaims = candidate.get("nonclaims")
    if not all(isinstance(value, dict) for value in (
        workflow, public_candidate, runtime, checks
    )):
        raise ValueError("agent lifecycle candidate structure changed")
    if not checks or any(type(value) is not bool for value in checks.values()):
        raise ValueError("agent lifecycle hash checks must be literal booleans")
    if not isinstance(nonclaims, list) or not all(
        isinstance(value, str) for value in nonclaims
    ):
        raise ValueError("agent lifecycle nonclaims must be a string list")

    def pick(parent, keys, label):
        missing = [key for key in keys if key not in parent]
        if missing:
            raise ValueError(
                "agent lifecycle candidate is missing {} fields: {}".format(
                    label, ", ".join(missing)
                )
            )
        return {key: parent[key] for key in keys}

    return {
        **pick(candidate, ("schema_version", "suite_id", "evidence_type"), "top-level"),
        "recorded_at_utc": "<redacted-public-run-time>",
        "workflow_run": {
            "id": "<redacted-public-run-id>",
            "url": "<redacted-public-run-url>",
            "head_commit": "<anonymous-builder-snapshot>",
            **pick(
                workflow,
                ("conclusion", "artifact_retention_days"),
                "workflow",
            ),
            "job_duration": "<redacted-public-run-duration>",
        },
        "candidate": pick(
            public_candidate,
            (
                "status",
                "published",
                "controller_pid",
                "control_loss_reason",
                "direct_child_return_code",
                "pre_crash_heartbeat_observations",
                "post_cleanup_heartbeat_observation",
                "escaped_descendant_heartbeat_frozen",
                "container_absent_after_control_loss",
            ),
            "candidate",
        ),
        "runtime": pick(
            runtime,
            (
                "client_version",
                "server_version",
                "server_os",
                "storage_driver",
                "security_options",
            ),
            "runtime",
        ),
        "hash_chain_checks": dict(checks),
        "nonclaims": list(nonclaims),
    }


def anonymize_evaluation_bytes(rel, data, anonymous_reference):
    if not rel.endswith((".json", ".md", ".py", ".yml", ".Containerfile")):
        return data
    # Normalize before matching the guarded redaction blocks.  add_payload
    # applies the same canonicalization to every allowlisted text artifact.
    text = canonical_text_bytes(rel, data).decode("utf-8")
    if rel == "evaluation/target-drift-v2/README.md":
        source_block = (
            "The protocol requires every future evaluated workspace to be built from commit\n"
            "`{}`, the public base immediately\n"
            "before the source-frozen paper audit and challenge artifacts.  This prevents\n"
            "the common Lean tree or the ABRL overlay from containing case-specific audit\n"
            "answers.  The compile-only and source-aware conditions use an explicit core\n"
            "allowlist; the ABRL condition uses the same base with `evaluation/` removed."
        ).format(PUBLIC_WORKSPACE_BASE_COMMIT)
        anonymous_block = (
            "The formal protocol requires a production Git base that predates the\n"
            "source-frozen audit and challenge artifacts.  That repository identifier is\n"
            "redacted here.  The 40-hex value in packaged machine fields is a non-Git\n"
            "placeholder derived from the anonymous source-tree digest; this archive has\n"
            "no Git object database and cannot materialize the preregistered workspaces.\n"
            "The three condition definitions are retained only for protocol inspection."
        )
        if source_block not in text:
            raise ValueError("target-drift README base-commit paragraph changed")
        text = text.replace(source_block, anonymous_block)
        text = text.replace(
            "GitHub Actions [run {}]({})".format(
                PUBLIC_CANDIDATE_RUN_ID, PUBLIC_CANDIDATE_RUN_URL
            ),
            "A public result-free CI candidate build (run metadata redacted)",
        )
        text = text.replace(
            "checker-image-candidate-32137509103.json",
            "checker-image-candidate-record.json",
        )
        text = text.replace(
            "GitHub Actions [run {}]({})".format(
                PUBLIC_ISOLATION_CANDIDATE_RUN_ID,
                PUBLIC_ISOLATION_CANDIDATE_RUN_URL,
            ),
            "A public result-free candidate build and isolation run "
            "(run metadata redacted)",
        )
        text = text.replace(
            "checker-image-candidate-32419343467.json",
            "checker-image-isolation-candidate-record.json",
        )
        text = text.replace(
            "GitHub Actions [run {}]({})".format(
                PUBLIC_AGENT_LIFECYCLE_RUN_ID,
                PUBLIC_AGENT_LIFECYCLE_RUN_URL,
            ),
            "A public result-free agent lifecycle candidate run "
            "(run metadata redacted)",
        )
        text = text.replace(
            "agent-lifecycle-candidate-32436339541.json",
            "agent-lifecycle-candidate-record.json",
        )
        text = text.replace(
            "[run {}]({})".format(
                PUBLIC_AGENT_IMAGE_RUN_ID, PUBLIC_AGENT_IMAGE_RUN_URL,
            ),
            "a public result-free combined agent-image run "
            "(run metadata redacted)",
        )
        text = text.replace(
            "agent-image-candidate-32464814750.json",
            "agent-image-candidate-record.json",
        )
    candidate_records = {
        PUBLIC_CANDIDATE_RECORD: (
            PUBLIC_CANDIDATE_RUN_ID, PUBLIC_CANDIDATE_RUN_URL,
        ),
        PUBLIC_ISOLATION_CANDIDATE_RECORD: (
            PUBLIC_ISOLATION_CANDIDATE_RUN_ID,
            PUBLIC_ISOLATION_CANDIDATE_RUN_URL,
        ),
        PUBLIC_AGENT_LIFECYCLE_RECORD: (
            PUBLIC_AGENT_LIFECYCLE_RUN_ID, PUBLIC_AGENT_LIFECYCLE_RUN_URL,
        ),
        PUBLIC_AGENT_IMAGE_RECORD: (
            PUBLIC_AGENT_IMAGE_RUN_ID, PUBLIC_AGENT_IMAGE_RUN_URL,
        ),
    }
    if rel in candidate_records:
        candidate = json.loads(text)
        workflow_run = candidate.get("workflow_run")
        if not isinstance(workflow_run, dict):
            raise ValueError("candidate build record is missing workflow metadata")
        expected_run_id, expected_run_url = candidate_records[rel]
        if str(workflow_run.get("id")) != expected_run_id:
            raise ValueError("candidate build run identifier changed")
        if workflow_run.get("url") != expected_run_url:
            raise ValueError("candidate build run URL changed")
        if rel in (PUBLIC_CANDIDATE_RECORD, PUBLIC_ISOLATION_CANDIDATE_RECORD):
            candidate = anonymous_checker_image_candidate(
                candidate, anonymous_reference
            )
        elif rel == PUBLIC_AGENT_LIFECYCLE_RECORD:
            candidate = anonymous_agent_lifecycle_candidate(candidate)
        elif rel == PUBLIC_AGENT_IMAGE_RECORD:
            candidate = anonymous_agent_image_candidate(
                candidate, anonymous_reference
            )
        text = canonical_json(candidate).decode("utf-8")
    text = text.replace(PUBLIC_WORKSPACE_BASE_COMMIT, anonymous_reference)
    return text.encode("utf-8")


def selected_source_records():
    raw = load_json(REPO_ROOT / "website" / "content" / "results.json")
    by_id = {row["id"]: row for row in raw["results"]}
    missing = sorted(set(SOURCE_RESULT_IDS) - set(by_id))
    if missing:
        raise ValueError("missing source result records: " + ", ".join(missing))
    records = {}
    for item in SOURCE_RESULT_IDS:
        source = by_id[item]
        records[item] = {
            "id": source["id"],
            "title": source["title"],
            "status": source["status"],
            "informal": source["informal"],
            "declarations": list(source.get("declarations", [])),
            "depends_on": list(source.get("depends_on", [])),
            "missing": list(source.get("missing", [])),
        }
    return records


def validate_delayed_counts(records):
    if any(records[item]["status"] != "compiled" for item in DELAYED_IMPLEMENTATION_IDS):
        raise ValueError("implementation-facing delayed records must remain compiled")
    implementation_count = sum(
        len(records[item]["declarations"]) for item in DELAYED_IMPLEMENTATION_IDS
    )
    diagnostic = records[DELAYED_DIAGNOSTIC_ID]
    if implementation_count != 88:
        raise ValueError("delayed implementation count drifted to {}".format(implementation_count))
    if diagnostic["status"] != "partial" or len(diagnostic["declarations"]) != 19:
        raise ValueError(
            "D.10--D.12 diagnostic/repair record must remain partial with 19 declarations"
        )


def validate_succinct_count(records):
    succinct = records[SUCCINCT_AUDIT_ID]
    if succinct["status"] != "partial" or len(succinct["declarations"]) != 54:
        raise ValueError(
            "succinct geometry audit must remain partial with 54 declarations"
        )


def validate_sgb_count(records, index):
    sgb = records[SGB_AUDIT_ID]
    declaration_list = sgb["declarations"]
    declarations = set(declaration_list)
    rows = {
        row["full_name"]: row for row in index["declarations"]
        if row["full_name"] in declarations
    }
    finite_count = sum(
        row["file"] == SGB_FINITE_ALGEBRA_FILE for row in rows.values()
    )
    generated_history_count = sum(
        row["file"] == SGB_GENERATED_HISTORY_FILE for row in rows.values()
    )
    if (
        sgb["status"] != "partial"
        or len(declaration_list) != len(declarations)
        or len(declarations) != 44
        or set(rows) != declarations
        or finite_count != SGB_FINITE_ALGEBRA_DECLARATION_COUNT
        or generated_history_count != SGB_GENERATED_HISTORY_DECLARATION_COUNT
        or finite_count + generated_history_count != len(declarations)
        or not SGB_GENERATED_TRAJECTORY_DECLARATIONS.issubset(declarations)
        or not SGB_CONDITIONAL_LAW_BRIDGE_DECLARATIONS.issubset(declarations)
    ):
        raise ValueError(
            "stochastic-gradient-bandit audit must remain partial with exactly "
            "26 finite-algebra and 18 generated-history declarations"
        )
    return {
        "generated_trajectory_compiled":
            SGB_GENERATED_TRAJECTORY_DECLARATIONS.issubset(declarations),
        "conditional_law_bridge_compiled":
            SGB_CONDITIONAL_LAW_BRIDGE_DECLARATIONS.issubset(declarations),
    }


def build_claim_ledger(proof_report):
    records = selected_source_records()
    index = load_json(REPO_ROOT / "research-wiki" / "retrieval-index" /
                      "local_lean_declarations.json")
    validate_delayed_counts(records)
    validate_succinct_count(records)
    sgb_evidence = validate_sgb_count(records, index)
    index_names = {row["full_name"] for row in index["declarations"]}
    referenced = {
        name for record in records.values() for name in record["declarations"]
    }
    missing = sorted(referenced - index_names)
    if missing != sorted(EXPECTED_INDEX_EXCEPTIONS):
        raise ValueError("unexpected result/index mismatch: " + ", ".join(missing[:8]))

    cng = load_json(REPO_ROOT / "research-wiki" / "proof-graph" /
                    "cng_candidate_evaluation.json")
    shared = proof_report["shared_library"]
    best_zdd = min(row["nonterminal_nodes"] for row in proof_report["zdd"]["orders"])
    target_id = "TARGET-DRIFT-V2-CONTROLLED-EVALUATION"
    if records[target_id]["status"] != "planned" or records[target_id]["declarations"]:
        raise ValueError("target-drift record must remain planned and result-free")
    return {
        "schema_version": 1,
        "status_vocabulary": ["compiled", "partial", "blocked", "prototype", "planned"],
        "index_counts": {
            "source_declarations": len(index["declarations"]),
            "generated_declaration_exceptions": list(EXPECTED_INDEX_EXCEPTIONS),
            "interpretation": "Counter-specific artifact size; not theorem coverage or an evaluation score.",
        },
        "table_rows": [
            {
                "artifact": "RL random-time route",
                "status": "compiled",
                "source_record_ids": ["RL-UNBOUNDED-HITTINGAFTER-EXPECTED-UPPER-BOUND"],
                "boundary": "Fixed-index and L1 consumers under recorded assumptions; not optional stopping or full UCB-VI.",
            },
            {
                "artifact": "ETC finite-history route",
                "status": "compiled",
                "source_record_ids": ["ETC-CANONICAL-SUBGAUSSIAN-REGRET"],
                "boundary": "Exact local endpoint; external theorem cards are retrieval evidence only.",
            },
            {
                "artifact": "Textbook Chapters 13--17",
                "status": "partial",
                "source_record_ids": [item for item in SOURCE_RESULT_IDS if item.startswith("TEXTBOOK-PART-IV-")],
                "boundary": "Chapter 15 Lemma 15.1 and the exact Theorem 15.2 expected-pseudo-regret/minimax terminals compile, with a Chapter 13 constant-1/54 consumer; whole-chapter Notes/Exercises and Chapter 16--17 terminals remain open.",
            },
            {
                "artifact": "Delayed best-of-both-worlds audit",
                "status": "partial",
                "source_record_ids": list(DELAYED_IMPLEMENTATION_IDS) + [
                    DELAYED_DIAGNOSTIC_ID,
                    "NEURIPS-2025-DELAYED-BOBW-CENTRAL-ENDPOINTS",
                ],
                "boundary": "88 implementation-facing plus 19 diagnostic/conditional/repair declarations, including an exact small-count scalar bound and only a conditional same-snapshot factor-20 skeleton; no source-paper regret theorem.",
            },
            {
                "artifact": "Succinct geometry audit",
                "status": "partial",
                "source_record_ids": [SUCCINCT_AUDIT_ID],
                "boundary": "54 declarations compile Definitions 3.1--3.3 and Lemmas 3.1--3.4, including finite-Bessel strict representation-size minimality and uniqueness for the same vector; a global R boundedness obligation is explicit; no Lemma 3.5--3.6, Theorem 3.8, or regret endpoint.",
            },
            {
                "artifact": "Stochastic-gradient-bandit mechanism audit",
                "status": "partial",
                "source_record_ids": [SGB_AUDIT_ID],
                "boundary": "44 declarations compile the 26-declaration finite-action algebra plus an 18-declaration generated-history layer: recursive measurable softmax state, canonical action/reward trajectory, initial/successor conditional laws, and Equation-(5) history-step-kernel integrals under explicit coordinate-update integrability and arm-reward integral equalities. Source-specific uniform reward regularity, including a producer of the required hypotheses, every learning-rate regime, and Theorems 1--4 remain open.",
            },
            {
                "artifact": "Proof graph / curvature--noise--gap",
                "status": "prototype",
                "source_record_ids": [],
                "boundary": "Deterministic structural measurements and eight finite leaves; no search-speed or theory-discovery claim.",
            },
            {
                "artifact": "Matched workflow study",
                "status": "planned",
                "source_record_ids": [target_id],
                "boundary": "Protocol and challenge allocation only; no model run, grade, causal result, or numerical outcome.",
            },
        ],
        "source_records": records,
        "delayed_feedback": {
            "implementation_facing_ids": list(DELAYED_IMPLEMENTATION_IDS),
            "implementation_facing_declaration_count": 88,
            "diagnostic_id": DELAYED_DIAGNOSTIC_ID,
            "diagnostic_conditional_repair_declaration_count": 19,
            "source_audit_declaration_count": 107,
            "paper_endpoint_verified": False,
        },
        "succinct_geometry": {
            "source_record_id": SUCCINCT_AUDIT_ID,
            "declaration_count": 54,
            "paper_endpoint_verified": False,
        },
        "stochastic_gradient_bandit": {
            "source_record_id": SGB_AUDIT_ID,
            "declaration_count": 44,
            "finite_algebra_declaration_count": SGB_FINITE_ALGEBRA_DECLARATION_COUNT,
            "generated_history_declaration_count": SGB_GENERATED_HISTORY_DECLARATION_COUNT,
            "generated_trajectory_compiled":
                sgb_evidence["generated_trajectory_compiled"],
            "conditional_law_bridge_compiled":
                sgb_evidence["conditional_law_bridge_compiled"],
            "uniform_reward_regularities_verified": False,
            "learning_rate_regime_verified": False,
            "paper_endpoint_verified": False,
        },
        "proof_graph": {
            "status": "prototype",
            "standalone_fixed_charge_sum": shared["standalone_fixed_charge_sum"],
            "union_fixed_charge": shared["union_fixed_charge"],
            "shared_declaration_count": shared["shared_declaration_count"],
            "best_zdd_nonterminal_nodes": best_zdd,
            "cng_root_count": cng["candidate_support"]["root_count"],
            "structural_discovery_established": cng["structural_discovery_established"],
            "search_speedup_established": False,
        },
        "matched_workflow_study": {
            "source_record_id": target_id,
            "numerical_results_present": False,
            "provider_runs_present": False,
            "grades_present": False,
            "analysis_results_present": False,
        },
    }


def add_payload(payload, rel, data):
    rel = require_safe_relative(rel)
    if rel in payload:
        raise ValueError("duplicate archive path: " + rel)
    data = canonical_text_bytes(rel, data)
    require_anonymous_bytes(rel, data)
    payload[rel] = data


def read_regular(rel):
    path = REPO_ROOT / rel
    if not path.is_file() or path.is_symlink():
        raise ValueError("missing or non-regular allowlisted file: " + rel)
    try:
        path.resolve().relative_to(REPO_ROOT.resolve())
    except ValueError:
        raise ValueError("allowlisted file resolves outside repository: " + rel)
    return path.read_bytes()


def proof_report_from_path(path):
    report = load_json(path)
    required = ("shared_library", "zdd", "hypergraph", "graph")
    if any(key not in report for key in required):
        raise ValueError("proof-graph report is missing structural fields")
    return sanitize_json(report)


def validate_graph_pair(graph_path, report):
    expected = report["graph"].get("sha256")
    raw_graph = graph_path.read_bytes()
    actual = sha256_bytes(raw_graph)
    if expected != actual:
        raise ValueError("proof graph/report SHA-256 mismatch")
    graph = json.loads(raw_graph.decode("utf-8"))
    counts = graph.get("counts")
    if counts != report["graph"].get("counts"):
        raise ValueError("proof graph/report count mismatch")
    # The submitted pair is authenticated in its original byte presentation.
    # The anonymous archive then stores canonical JSON and rebinds its report
    # to those exact packaged bytes, avoiding CRLF/LF hash drift.
    graph_data = canonical_json(graph)
    report["graph"]["sha256"] = sha256_bytes(graph_data)
    return graph_data, report


def build_payload(proof_graph=None, proof_report_path=None, allow_missing_graph=False):
    if (proof_graph is None) != (proof_report_path is None):
        raise ValueError("proof graph and report must be supplied together")
    if proof_graph is None and not allow_missing_graph:
        raise ValueError("submission build requires --proof-graph and --proof-graph-report")

    tracked = git_tracked_files()
    payload = {}
    for source, destination in sorted(EXPLICIT_COPIES.items()):
        add_payload(payload, destination, read_regular(source))
    for rel in source_tree_files(tracked):
        add_payload(payload, rel, read_regular(rel))
    # Build the anonymous base binding before adding the evaluation layer.  The
    # protocol's public Git commit is replaced by a schema-compatible opaque
    # reference; the archive intentionally contains no Git object database.
    base_manifest = anonymous_base_manifest(payload)
    anonymous_reference = base_manifest["schema_compatibility_reference"]
    add_payload(payload, "evidence/anonymous-base-manifest.json",
                canonical_json(base_manifest))
    for rel in evaluation_files(tracked):
        data = anonymize_evaluation_bytes(rel, read_regular(rel), anonymous_reference)
        destination = rel
        if rel == PUBLIC_CANDIDATE_RECORD:
            destination = ANONYMOUS_CANDIDATE_RECORD
        elif rel == PUBLIC_ISOLATION_CANDIDATE_RECORD:
            destination = ANONYMOUS_ISOLATION_CANDIDATE_RECORD
        elif rel == PUBLIC_AGENT_LIFECYCLE_RECORD:
            destination = ANONYMOUS_AGENT_LIFECYCLE_RECORD
        elif rel == PUBLIC_AGENT_IMAGE_RECORD:
            destination = ANONYMOUS_AGENT_IMAGE_RECORD
        add_payload(payload, destination, data)
    for rel in TARGET_DRIFT_WORKFLOW_FILES:
        if rel not in tracked:
            raise ValueError("untracked or missing target-drift workflow: " + rel)
        data = anonymize_evaluation_bytes(rel, read_regular(rel), anonymous_reference)
        add_payload(payload, rel, data)
    for rel in TARGET_DRIFT_TOOLS:
        if rel not in tracked:
            raise ValueError("untracked or missing target-drift tool: " + rel)
        data = anonymize_evaluation_bytes(rel, read_regular(rel), anonymous_reference)
        add_payload(payload, rel, data)
    for source, destination in sorted(EVIDENCE_JSON.items()):
        value = sanitize_json(load_json(REPO_ROOT / source))
        add_payload(payload, destination, canonical_json(value))
    for rel in PROOF_GRAPH_TEST_EVIDENCE:
        value = sanitize_json(load_json(REPO_ROOT / rel))
        add_payload(payload, rel, canonical_json(value))

    if proof_report_path is None:
        report = sanitize_json(load_json(
            REPO_ROOT / "research-wiki" / "proof-graph" / "benchmark_report.json"
        ))
    else:
        proof_graph = Path(proof_graph).resolve()
        proof_report_path = Path(proof_report_path).resolve()
        if not proof_graph.is_file() or proof_graph.is_symlink():
            raise ValueError("proof graph is missing or non-regular")
        if not proof_report_path.is_file() or proof_report_path.is_symlink():
            raise ValueError("proof graph report is missing or non-regular")
        report = proof_report_from_path(proof_report_path)
        graph_data, report = validate_graph_pair(proof_graph, report)
        add_payload(payload, "evidence/proof-graph/current-proof-graph.json", graph_data)
        add_payload(payload, "evidence/proof-graph/current-benchmark-report.json",
                    canonical_json(report))

    ledger = build_claim_ledger(report)
    add_payload(payload, "evidence/claim-ledger.json", canonical_json(ledger))
    return payload


def manifest_for(payload, graph_included):
    entries = []
    digest = hashlib.sha256()
    for rel in sorted(payload):
        data = payload[rel]
        item = {
            "path": rel,
            "bytes": len(data),
            "sha256": sha256_bytes(data),
        }
        entries.append(item)
        digest.update(rel.encode("utf-8") + b"\0")
        digest.update(item["sha256"].encode("ascii") + b"\0")
        digest.update(str(item["bytes"]).encode("ascii") + b"\n")
    anonymous_base = json.loads(payload["evidence/anonymous-base-manifest.json"].decode("utf-8"))
    return {
        "schema_version": 1,
        "artifact_title": "ABRL anonymous Lean/code artifact",
        "archive_root": ARCHIVE_ROOT,
        "source_tree_digest": digest.hexdigest(),
        "file_count": len(entries),
        "files": entries,
        "proof_graph": {
            "included": graph_included,
            "interpretation": "Environment-level direct-constant dependency export; not an elaborator trace.",
        },
        "anonymous_base": {
            "tree_sha256": anonymous_base["tree_sha256"],
            "git_object_database_included": False,
            "target_drift_materialization_ready": False,
        },
        "anonymity": {
            "positive_allowlist": True,
            "authoring_repository_metadata_included": False,
            "source_pdfs_included": False,
            "unrun_evaluation_outputs_included": False,
        },
    }


def write_zip(output_path, payload, manifest):
    output_path.parent.mkdir(parents=True, exist_ok=True)
    manifest_data = canonical_json(manifest)
    require_anonymous_bytes("ARTIFACT_MANIFEST.json", manifest_data)
    with zipfile.ZipFile(str(output_path), "w", compression=zipfile.ZIP_DEFLATED,
                         compresslevel=9) as archive:
        complete = dict(payload)
        complete["ARTIFACT_MANIFEST.json"] = manifest_data
        for rel in sorted(complete):
            info = zipfile.ZipInfo(ARCHIVE_ROOT + "/" + rel, FIXED_ZIP_TIME)
            info.create_system = 3
            info.external_attr = 0o100644 << 16
            info.compress_type = zipfile.ZIP_DEFLATED
            archive.writestr(info, complete[rel], compress_type=zipfile.ZIP_DEFLATED,
                             compresslevel=9)


def build_archive(output_path, proof_graph=None, proof_report_path=None,
                  allow_missing_graph=False):
    payload = build_payload(proof_graph, proof_report_path, allow_missing_graph)
    manifest = manifest_for(payload, proof_graph is not None)
    write_zip(Path(output_path), payload, manifest)
    return {
        "archive": Path(output_path).name,
        "bytes": Path(output_path).stat().st_size,
        "file_count": manifest["file_count"],
        "sha256": sha256_file(Path(output_path)),
        "source_tree_digest": manifest["source_tree_digest"],
        "proof_graph_included": manifest["proof_graph"]["included"],
    }


def build_parser():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output-dir", type=Path, required=True)
    parser.add_argument("--proof-graph", type=Path, required=True,
                        help="current compact JSON produced by proof_graph_export")
    parser.add_argument("--proof-graph-report", type=Path, required=True,
                        help="benchmark report whose graph digest matches --proof-graph")
    return parser


def main(argv=None):
    args = build_parser().parse_args(argv)
    result = build_archive(
        args.output_dir / ARCHIVE_NAME,
        proof_graph=args.proof_graph,
        proof_report_path=args.proof_graph_report,
    )
    print(json.dumps(result, sort_keys=True))
    return 0


if __name__ == "__main__":
    sys.exit(main())
