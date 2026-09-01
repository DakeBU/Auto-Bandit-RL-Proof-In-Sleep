# GPT Harness Review Packet

You are reviewing two ABRL proof harnesses on matched, frozen theorem targets:

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
4. one Mermaid diagram of the proposed internal harness;
5. exactly one JSON object with keys `recommended_default`, `confidence`,
   `evidence`, `risks`, `next_matched_experiment`, and `proposed_change`.

## Deterministic analysis

```json
{
  "schema_version": 1,
  "task_filter": "PAPER-AUDIT-NEURIPS-2025-SGB-PHASE-TRANSITION-PROSPECTIVE",
  "experiment_filter": "",
  "eligible_rows": 0,
  "matched_experiments": [],
  "excluded_experiments": {},
  "minimum_matched_experiments": 2,
  "all_evidence": {
    "hierarchical": {
      "harness": "hierarchical",
      "experiments": 0,
      "runs": 0,
      "attempts": 0,
      "reviewed_attempts": 0,
      "substantive_attempts": 0,
      "failed_or_rejected_attempts": 0,
      "unreviewed_attempts": 0,
      "substantive_score": 0,
      "obligations_closed": 0,
      "new_declarations": [],
      "reused_declarations": [],
      "critical_path_seconds": 0.0,
      "prompt_chars": 0,
      "input_tokens": 0,
      "output_tokens": 0,
      "substantive_yield": 0.0,
      "score_per_critical_minute": 0.0
    },
    "master-worker": {
      "harness": "master-worker",
      "experiments": 0,
      "runs": 0,
      "attempts": 0,
      "reviewed_attempts": 0,
      "substantive_attempts": 0,
      "failed_or_rejected_attempts": 0,
      "unreviewed_attempts": 0,
      "substantive_score": 0,
      "obligations_closed": 0,
      "new_declarations": [],
      "reused_declarations": [],
      "critical_path_seconds": 0.0,
      "prompt_chars": 0,
      "input_tokens": 0,
      "output_tokens": 0,
      "substantive_yield": 0.0,
      "score_per_critical_minute": 0.0
    }
  },
  "matched_evidence": {
    "hierarchical": {
      "harness": "hierarchical",
      "experiments": 0,
      "runs": 0,
      "attempts": 0,
      "reviewed_attempts": 0,
      "substantive_attempts": 0,
      "failed_or_rejected_attempts": 0,
      "unreviewed_attempts": 0,
      "substantive_score": 0,
      "obligations_closed": 0,
      "new_declarations": [],
      "reused_declarations": [],
      "critical_path_seconds": 0.0,
      "prompt_chars": 0,
      "input_tokens": 0,
      "output_tokens": 0,
      "substantive_yield": 0.0,
      "score_per_critical_minute": 0.0
    },
    "master-worker": {
      "harness": "master-worker",
      "experiments": 0,
      "runs": 0,
      "attempts": 0,
      "reviewed_attempts": 0,
      "substantive_attempts": 0,
      "failed_or_rejected_attempts": 0,
      "unreviewed_attempts": 0,
      "substantive_score": 0,
      "obligations_closed": 0,
      "new_declarations": [],
      "reused_declarations": [],
      "critical_path_seconds": 0.0,
      "prompt_chars": 0,
      "input_tokens": 0,
      "output_tokens": 0,
      "substantive_yield": 0.0,
      "score_per_critical_minute": 0.0
    }
  },
  "decision": {
    "status": "insufficient-evidence",
    "recommended_default": "retain-current-default",
    "next_experiment_harness": "master-worker",
    "reason": "need at least 2 matched experiments; found 0"
  },
  "metric_policy": {
    "primary": "reviewer-validated substantive progress on the same frozen target",
    "secondary": [
      "closed obligations",
      "new and reused declarations",
      "critical-path time",
      "prompt and token volume"
    ],
    "excluded_as_primary": [
      "raw worker count",
      "raw node count",
      "command exit zero without Lean/reviewer evidence",
      "unmatched historical trials"
    ],
    "progress_weights": {
      "unreviewed": 0.0,
      "no-progress": 0.0,
      "diagnostic": 1.0,
      "retrieval-reuse": 1.5,
      "statement-repair": 2.0,
      "compiled-leaf": 3.0,
      "closed-frontier": 5.0,
      "terminal": 8.0
    }
  }
}
```

## Eligible recent log rows

```json
[]
```
