#!/usr/bin/env python3
"""Evidence-bounded comparison for ABRL harness executions.

The module deliberately separates deterministic measurements from GPT review.
Only matched experiments carrying an explicit harness mode, experiment id,
identical frozen route packet, and reviewer-owned progress verdict can support
a default-harness recommendation.
"""

from __future__ import annotations

import hashlib
import json
import re
from collections import defaultdict
from pathlib import Path
from typing import Any, Sequence


HARNESS_MODES = ("hierarchical", "master-worker")
PROGRESS_CLASSES = (
    "unreviewed",
    "no-progress",
    "diagnostic",
    "retrieval-reuse",
    "statement-repair",
    "compiled-leaf",
    "closed-frontier",
    "terminal",
)
PROGRESS_WEIGHTS = {
    "unreviewed": 0.0,
    "no-progress": 0.0,
    "diagnostic": 1.0,
    "retrieval-reuse": 1.5,
    "statement-repair": 2.0,
    "compiled-leaf": 3.0,
    "closed-frontier": 5.0,
    "terminal": 8.0,
}


def normalized_text_sha256(path: Path) -> str:
    """Hash text content independently of Git's platform line endings."""
    payload = path.read_bytes().replace(b"\r\n", b"\n").replace(b"\r", b"\n")
    return hashlib.sha256(payload).hexdigest()


VERIFIED_STATUSES = {"compiled", "accepted"}
REVIEWED_STATUSES = VERIFIED_STATUSES | {"blocked", "rejected"}
ATTEMPT_ROLES = {"lower", "worker"}


def _as_int(value: Any) -> int:
    try:
        return int(value or 0)
    except (TypeError, ValueError):
        return 0


def _as_float(value: Any) -> float:
    try:
        return float(value or 0.0)
    except (TypeError, ValueError):
        return 0.0


def _as_list(value: Any) -> list[Any]:
    if value is None or value == "":
        return []
    if isinstance(value, list):
        return value
    if isinstance(value, tuple):
        return list(value)
    return [value]


def _eligible_rows(
    rows: Sequence[dict[str, Any]],
    *,
    task: str = "",
    experiment: str = "",
) -> list[dict[str, Any]]:
    selected: list[dict[str, Any]] = []
    for row in rows:
        if row.get("harness") not in HARNESS_MODES:
            continue
        if not row.get("experiment_id"):
            continue
        if task and row.get("task") != task:
            continue
        if experiment and row.get("experiment_id") != experiment:
            continue
        selected.append(row)
    return selected


def _is_attempt(row: dict[str, Any]) -> bool:
    return row.get("role") in ATTEMPT_ROLES or (
        row.get("role") == "reviewer"
        and bool(row.get("attempt_id"))
        and row.get("reviewer_validated") is True
    )


def _is_reviewed(row: dict[str, Any]) -> bool:
    return (
        row.get("reviewer_role") == "reviewer"
        and row.get("reviewer_validated") is True
        and row.get("status") in REVIEWED_STATUSES
        and bool(_as_list(row.get("verifier_evidence")))
        and row.get("progress_class") in PROGRESS_WEIGHTS
        and row.get("progress_class") != "unreviewed"
    )


def _substantive_weight(row: dict[str, Any]) -> float:
    if not _is_reviewed(row):
        return 0.0
    return PROGRESS_WEIGHTS.get(str(row.get("progress_class", "unreviewed")), 0.0)


def _attempt_join_key(row: dict[str, Any]) -> tuple[str, str, str, str]:
    return (
        str(row.get("experiment_id") or ""),
        str(row.get("harness") or ""),
        str(row.get("run_id") or ""),
        str(row.get("attempt_id") or ""),
    )


def _merged_attempts(rows: Sequence[dict[str, Any]]) -> list[dict[str, Any]]:
    """Join worker execution measurements to a separate reviewer verdict.

    A worker cannot make its own result count as reviewed.  Review rows use the
    same attempt id and contribute classification/evidence fields, while the
    worker row remains the source of elapsed time and token measurements.
    """
    executions: dict[tuple[str, str, str, str], dict[str, Any]] = {}
    reviews: dict[tuple[str, str, str, str], dict[str, Any]] = {}
    anonymous = 0
    for row in rows:
        role = row.get("role")
        if role not in ATTEMPT_ROLES and role != "reviewer":
            continue
        attempt_id = str(row.get("attempt_id") or "")
        if not attempt_id:
            if role not in ATTEMPT_ROLES:
                continue
            anonymous += 1
            attempt_id = f"anonymous-{anonymous}"
            key = (*_attempt_join_key(row)[:3], attempt_id)
        else:
            key = _attempt_join_key(row)
        if role in ATTEMPT_ROLES:
            executions.setdefault(key, dict(row))
        elif row.get("reviewer_validated") is True:
            reviews[key] = dict(row)

    merged: list[dict[str, Any]] = []
    review_fields = (
        "status",
        "progress_class",
        "reviewer_validated",
        "verifier_evidence",
        "notes",
        "obligations_before",
        "obligations_after",
        "new_declarations",
        "reused_declarations",
        "dag_nodes",
        "dag_depth",
        "lean_check_seconds",
        "error_signature",
        "changed_files",
        "route_fingerprint",
        "route_packet_hash",
        "target_fingerprint",
    )
    for key, execution in executions.items():
        combined = dict(execution)
        review = reviews.get(key)
        if review is not None:
            if any(
                review.get(field) != execution.get(field)
                for field in ("target_fingerprint", "route_packet_hash")
            ):
                review = None
        if review is not None:
            for field in review_fields:
                value = review.get(field)
                if value not in (None, "", [], False):
                    combined[field] = value
            combined["reviewer_validated"] = True
            combined["reviewer_role"] = "reviewer"
            combined["review_time"] = review.get("time", "")
        merged.append(combined)
    return merged


def _critical_path_seconds(rows: Sequence[dict[str, Any]], harness: str) -> float:
    measurement_rows = [row for row in rows if not _is_attempt(row)]
    measurement_rows.extend(_merged_attempts(rows))
    by_run: dict[str, list[dict[str, Any]]] = defaultdict(list)
    for row in measurement_rows:
        by_run[str(row.get("run_id") or row.get("experiment_id") or "unknown")].append(row)
    total = 0.0
    for run_rows in by_run.values():
        if harness == "master-worker":
            worker_times = [
                _as_float(row.get("elapsed_seconds"))
                for row in run_rows
                if row.get("role") == "worker"
            ]
            serial = sum(
                _as_float(row.get("elapsed_seconds"))
                for row in run_rows
                if row.get("role") != "worker"
            )
            total += serial + (max(worker_times) if worker_times else 0.0)
        else:
            total += sum(_as_float(row.get("elapsed_seconds")) for row in run_rows)
    return total


def summarize_arm(rows: Sequence[dict[str, Any]], harness: str) -> dict[str, Any]:
    arm_rows = [row for row in rows if row.get("harness") == harness]
    attempts = _merged_attempts(arm_rows)
    reviewed = [row for row in attempts if _is_reviewed(row)]
    substantive = [row for row in reviewed if _substantive_weight(row) > 0]
    run_ids = {str(row.get("run_id")) for row in arm_rows if row.get("run_id")}
    experiment_ids = {
        str(row.get("experiment_id")) for row in arm_rows if row.get("experiment_id")
    }
    declarations = {
        str(name)
        for row in substantive
        for name in _as_list(row.get("new_declarations"))
        if str(name)
    }
    reused = {
        str(name)
        for row in substantive
        for name in _as_list(row.get("reused_declarations"))
        if str(name)
    }
    obligations_closed = sum(
        max(
            0,
            _as_int(row.get("obligations_before"))
            - _as_int(row.get("obligations_after")),
        )
        for row in substantive
    )
    score = sum(_substantive_weight(row) for row in substantive)
    critical_seconds = _critical_path_seconds(arm_rows, harness)
    prompt_chars = sum(_as_int(row.get("prompt_chars")) for row in arm_rows)
    input_tokens = sum(_as_int(row.get("input_tokens")) for row in arm_rows)
    output_tokens = sum(_as_int(row.get("output_tokens")) for row in arm_rows)
    failed = sum(1 for row in attempts if row.get("status") in {"failed", "rejected"})
    unreviewed = sum(1 for row in attempts if not _is_reviewed(row))
    return {
        "harness": harness,
        "experiments": len(experiment_ids),
        "runs": len(run_ids),
        "attempts": len(attempts),
        "reviewed_attempts": len(reviewed),
        "substantive_attempts": len(substantive),
        "failed_or_rejected_attempts": failed,
        "unreviewed_attempts": unreviewed,
        "substantive_score": round(score, 3),
        "obligations_closed": obligations_closed,
        "new_declarations": sorted(declarations),
        "reused_declarations": sorted(reused),
        "critical_path_seconds": round(critical_seconds, 3),
        "prompt_chars": prompt_chars,
        "input_tokens": input_tokens,
        "output_tokens": output_tokens,
        "substantive_yield": round(len(substantive) / len(attempts), 3) if attempts else 0.0,
        "score_per_critical_minute": (
            round(score / (critical_seconds / 60.0), 3) if critical_seconds > 0 else 0.0
        ),
    }


def _matched_experiment_rows(
    rows: Sequence[dict[str, Any]],
) -> tuple[list[dict[str, Any]], list[str], dict[str, str]]:
    by_experiment: dict[str, list[dict[str, Any]]] = defaultdict(list)
    for row in rows:
        by_experiment[str(row["experiment_id"])].append(row)
    matched_ids: list[str] = []
    exclusions: dict[str, str] = {}
    matched_rows: list[dict[str, Any]] = []
    for experiment_id, experiment_rows in sorted(by_experiment.items()):
        modes = {str(row.get("harness")) for row in experiment_rows}
        if modes != set(HARNESS_MODES):
            exclusions[experiment_id] = "both harness arms are not present"
            continue
        if any(not row.get("target_fingerprint") for row in experiment_rows):
            exclusions[experiment_id] = "one or more rows lack an explicit target fingerprint"
            continue
        target_keys = {str(row["target_fingerprint"]) for row in experiment_rows}
        if len(target_keys) != 1:
            exclusions[experiment_id] = "arms do not share one target fingerprint"
            continue
        execution_rows = [
            row for row in experiment_rows if row.get("role") in ATTEMPT_ROLES
        ]
        if not execution_rows:
            exclusions[experiment_id] = "no lower/worker execution attempts are present"
            continue
        route_packet_hashes = {
            str(row.get("route_packet_hash"))
            for row in execution_rows
            if row.get("route_packet_hash")
        }
        if len(route_packet_hashes) != 1 or any(
            not row.get("route_packet_hash") for row in execution_rows
        ):
            exclusions[experiment_id] = (
                "arms do not share one explicit frozen route-packet hash"
            )
            continue
        reviewed_modes = {
            str(row.get("harness"))
            for row in _merged_attempts(experiment_rows)
            if _is_reviewed(row)
        }
        if reviewed_modes != set(HARNESS_MODES):
            exclusions[experiment_id] = "both arms lack reviewer-classified attempts"
            continue
        matched_ids.append(experiment_id)
        matched_rows.extend(experiment_rows)
    return matched_rows, matched_ids, exclusions


def analyze_trials(
    rows: Sequence[dict[str, Any]],
    *,
    task: str = "",
    experiment: str = "",
    min_matched_experiments: int = 2,
) -> dict[str, Any]:
    eligible = _eligible_rows(rows, task=task, experiment=experiment)
    all_arms = {mode: summarize_arm(eligible, mode) for mode in HARNESS_MODES}
    matched_rows, matched_ids, exclusions = _matched_experiment_rows(eligible)
    matched_arms = {mode: summarize_arm(matched_rows, mode) for mode in HARNESS_MODES}

    if len(matched_ids) < min_matched_experiments:
        run_counts = {mode: all_arms[mode]["runs"] for mode in HARNESS_MODES}
        if run_counts["master-worker"] <= run_counts["hierarchical"]:
            next_harness = "master-worker"
        else:
            next_harness = "hierarchical"
        decision = {
            "status": "insufficient-evidence",
            "recommended_default": "retain-current-default",
            "next_experiment_harness": next_harness,
            "reason": (
                f"need at least {min_matched_experiments} matched experiments; "
                f"found {len(matched_ids)}"
            ),
        }
    else:
        hierarchical = matched_arms["hierarchical"]
        master_worker = matched_arms["master-worker"]
        h_score = hierarchical["substantive_score"]
        m_score = master_worker["substantive_score"]
        h_fail = hierarchical["failed_or_rejected_attempts"]
        m_fail = master_worker["failed_or_rejected_attempts"]
        if m_score > h_score and m_fail <= h_fail:
            recommendation = "master-worker"
        elif h_score > m_score and h_fail <= m_fail:
            recommendation = "hierarchical"
        else:
            recommendation = "retain-current-default"
        decision = {
            "status": "measured",
            "recommended_default": recommendation,
            "next_experiment_harness": (
                "hierarchical" if recommendation == "master-worker" else "master-worker"
            ),
            "reason": (
                "substantive reviewed progress dominates throughput; failures and target fidelity "
                "act as safety constraints"
            ),
        }

    return {
        "schema_version": 1,
        "task_filter": task,
        "experiment_filter": experiment,
        "eligible_rows": len(eligible),
        "matched_experiments": matched_ids,
        "excluded_experiments": exclusions,
        "minimum_matched_experiments": min_matched_experiments,
        "all_evidence": all_arms,
        "matched_evidence": matched_arms,
        "decision": decision,
        "metric_policy": {
            "primary": "reviewer-validated substantive progress on the same frozen target",
            "secondary": [
                "closed obligations",
                "new and reused declarations",
                "critical-path time",
                "prompt and token volume",
            ],
            "matching_contract": [
                "same experiment id",
                "same target fingerprint",
                "same frozen route-packet hash",
                "separate reviewer-owned verdict for each execution attempt",
            ],
            "excluded_as_primary": [
                "raw worker count",
                "raw node count",
                "command exit zero without Lean/reviewer evidence",
                "unmatched historical trials",
            ],
            "progress_weights": PROGRESS_WEIGHTS,
        },
    }


def _mermaid_id(value: str) -> str:
    clean = re.sub(r"[^A-Za-z0-9_]", "_", value)
    return clean or "node"


def render_mermaid(rows: Sequence[dict[str, Any]], analysis: dict[str, Any]) -> str:
    eligible = _eligible_rows(
        rows,
        task=str(analysis.get("task_filter", "")),
        experiment=str(analysis.get("experiment_filter", "")),
    )
    lines = [
        "flowchart TD",
        '  ROOT["Frozen theorem target"]',
        '  H["Hierarchical: upper → middle → lower → reviewer"]',
        '  M["Master–worker: master → parallel workers → synthesis → reviewer"]',
        "  ROOT --> H",
        "  ROOT --> M",
    ]
    for index, row in enumerate(_merged_attempts(eligible)):
        harness = str(row.get("harness"))
        parent = "H" if harness == "hierarchical" else "M"
        attempt = str(row.get("attempt_id") or row.get("run_id") or f"row-{index}")
        node_id = f"A{index}_{_mermaid_id(attempt)[:32]}"
        progress = str(row.get("progress_class") or "unreviewed")
        status = str(row.get("status") or "unknown")
        if _is_reviewed(row):
            evidence_label = f"reviewed {progress} · {status}"
        else:
            evidence_label = f"unreviewed · reported {progress}/{status}"
        label = f"{attempt}\\n{evidence_label}".replace('"', "'")
        lines.append(f'  {node_id}["{label}"]')
        lines.append(f"  {parent} --> {node_id}")
        if _substantive_weight(row) > 0:
            lines.append(f"  class {node_id} substantive")
        elif status in {"failed", "rejected"}:
            lines.append(f"  class {node_id} failed")
        else:
            lines.append(f"  class {node_id} unreviewed")
    lines.extend([
        "  classDef substantive fill:#dff5e7,stroke:#176b3a,color:#123b25",
        "  classDef failed fill:#fde7e7,stroke:#a33a3a,color:#5f1d1d",
        "  classDef unreviewed fill:#f4f1e8,stroke:#8c8268,color:#3f3a2f",
    ])
    return "\n".join(lines) + "\n"


def render_markdown(analysis: dict[str, Any]) -> str:
    rows = []
    for mode in HARNESS_MODES:
        arm = analysis["matched_evidence"][mode]
        rows.append(
            "| {mode} | {runs} | {attempts} | {reviewed} | {substantive} | {score} | "
            "{closed} | {seconds} | {chars} |".format(
                mode=mode,
                runs=arm["runs"],
                attempts=arm["attempts"],
                reviewed=arm["reviewed_attempts"],
                substantive=arm["substantive_attempts"],
                score=arm["substantive_score"],
                closed=arm["obligations_closed"],
                seconds=arm["critical_path_seconds"],
                chars=arm["prompt_chars"],
            )
        )
    matched = ", ".join(analysis["matched_experiments"]) or "none"
    excluded = "\n".join(
        f"- `{key}`: {value}" for key, value in analysis["excluded_experiments"].items()
    ) or "- none"
    decision = analysis["decision"]
    return f"""# ABRL Harness Comparison

## Evidence boundary

- Eligible structured rows: {analysis['eligible_rows']}
- Matched experiments: {matched}
- Minimum matched experiments for a recommendation: {analysis['minimum_matched_experiments']}
- Decision status: **{decision['status']}**
- Recommended default: **{decision['recommended_default']}**
- Next matched arm to collect: **{decision['next_experiment_harness']}**

Historical trials without an explicit harness mode, experiment id, frozen target
fingerprint, identical route-packet hash, reviewer-owned progress verdict, and
verifier evidence are excluded from the causal comparison.  A successful agent
command or worker self-report is not a compiled Lean result.

## Matched evidence

| Harness | Runs | Attempts | Reviewed | Substantive | Score | Obligations closed | Critical seconds | Prompt chars |
| --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
{chr(10).join(rows)}

The score weights reviewer-validated mathematical progress: diagnostics and
statement repairs count, compiled leaves count more, and a closed frontier or
terminal counts most.  Raw worker/node count is not a success metric.

## Excluded or unmatched experiments

{excluded}

## Deterministic conclusion

{decision['reason']}.  GPT review may explain the pattern and propose the next
matched experiment, but it cannot promote an unreviewed attempt or silently
change the frozen theorem target.
"""


def render_review_prompt(
    rows: Sequence[dict[str, Any]],
    analysis: dict[str, Any],
    *,
    max_rows: int = 80,
) -> str:
    eligible = _eligible_rows(
        rows,
        task=str(analysis.get("task_filter", "")),
        experiment=str(analysis.get("experiment_filter", "")),
    )[-max_rows:]
    compact_rows = [
        {
            key: row.get(key)
            for key in (
                "time",
                "task",
                "experiment_id",
                "harness",
                "route_packet_hash",
                "run_id",
                "attempt_id",
                "role",
                "route_fingerprint",
                "progress_class",
                "status",
                "reviewer_validated",
                "obligations_before",
                "obligations_after",
                "new_declarations",
                "reused_declarations",
                "elapsed_seconds",
                "prompt_chars",
                "input_tokens",
                "output_tokens",
                "error_signature",
                "notes",
                "verifier_evidence",
            )
            if row.get(key) not in (None, "", [], False)
        }
        for row in eligible
    ]
    return f"""# GPT Harness Review Packet

You are reviewing two ABRL proof harnesses on matched, frozen theorem targets
and identical route packets:

1. `hierarchical`: upper → middle → one or more lower roles → reviewer;
2. `master-worker`: a light master plans, ordinary workers explore disjoint
   routes concurrently, the master synthesizes, and a reviewer gates Lean and
   target fidelity.

Judge which harness is more useful for *substantive mathematical progress*, not
which launches more workers.  Give highest weight to reviewer-validated closed
obligations, compiled declarations, statement repairs, reusable retrieval, and
frontier/terminal closure.  Penalize target drift, duplicate routes, unreviewed
success claims, file conflicts, context duplication, and master bottlenecks.
Do not infer a winner when the deterministic report says evidence is
insufficient.  Do not edit Lean or change the target in this review.

Return:

1. a concise comparison of progress, context cost, critical path, duplication,
   and failure diagnosis;
2. the strongest internal harness pattern supported by the evidence;
3. one matched next experiment using the same target and route packet;
4. exactly one fenced `mermaid` block containing the proposed internal harness;
5. exactly one fenced `json` object with keys `recommended_default`, `confidence`,
   `evidence`, `risks`, `next_matched_experiment`, and `proposed_change`.

When the deterministic status is `insufficient-evidence`, set
`recommended_default` to `retain-current-default`; a proposed hybrid remains a
hypothesis for the next matched experiment, not an adopted scheduler.

## Deterministic analysis

```json
{json.dumps(analysis, indent=2, ensure_ascii=False)}
```

## Eligible recent log rows

```json
{json.dumps(compact_rows, indent=2, ensure_ascii=False)}
```
"""


def parse_gpt_review_response(text: str) -> dict[str, Any]:
    """Extract the bounded JSON verdict and Mermaid proposal from GPT output.

    The raw response remains the provenance artifact.  This parser deliberately
    accepts only the two fenced, machine-readable blocks requested by the
    prompt, so free-form prose cannot silently become a scheduler decision.
    """

    json_blocks = re.findall(r"```json\s*(\{.*?\})\s*```", text, flags=re.IGNORECASE | re.DOTALL)
    mermaid_blocks = re.findall(
        r"```mermaid\s*([^`]+?)\s*```", text, flags=re.IGNORECASE | re.DOTALL
    )
    if len(json_blocks) != 1:
        raise ValueError("GPT harness review must contain exactly one fenced JSON object")
    if len(mermaid_blocks) != 1:
        raise ValueError("GPT harness review must contain exactly one fenced Mermaid diagram")

    try:
        review = json.loads(json_blocks[0])
    except json.JSONDecodeError as error:
        raise ValueError(f"GPT harness review JSON is invalid: {error}") from error
    if not isinstance(review, dict):
        raise ValueError("GPT harness review JSON must be an object")

    required = {
        "recommended_default",
        "confidence",
        "evidence",
        "risks",
        "next_matched_experiment",
        "proposed_change",
    }
    missing = sorted(required - set(review))
    if missing:
        raise ValueError("GPT harness review JSON is missing: " + ", ".join(missing))
    if review["recommended_default"] not in {
        "hierarchical",
        "master-worker",
        "retain-current-default",
    }:
        raise ValueError("GPT harness review recommends an unknown harness")
    for key in ("evidence", "risks"):
        if not isinstance(review[key], list) or not all(
            isinstance(item, str) and item.strip() for item in review[key]
        ):
            raise ValueError(f"GPT harness review field {key!r} must be a non-empty string list")
    if not isinstance(review["proposed_change"], str) or not review["proposed_change"].strip():
        raise ValueError("GPT harness review proposed_change must be a non-empty string")
    next_experiment = review["next_matched_experiment"]
    if not (
        isinstance(next_experiment, str) and next_experiment.strip()
    ) and not (
        isinstance(next_experiment, dict) and bool(next_experiment)
    ):
        raise ValueError(
            "GPT harness review next_matched_experiment must be a non-empty string or object"
        )

    mermaid = mermaid_blocks[0].strip()
    if not re.match(r"^(?:flowchart|graph)\s", mermaid):
        raise ValueError("GPT harness Mermaid proposal must start with flowchart or graph")
    return {"review": review, "mermaid": mermaid + "\n"}
