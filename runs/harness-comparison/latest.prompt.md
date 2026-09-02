# GPT Harness Review Packet

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
4. one Mermaid diagram of the proposed internal harness;
5. exactly one JSON object with keys `recommended_default`, `confidence`,
   `evidence`, `risks`, `next_matched_experiment`, and `proposed_change`.

## Deterministic analysis

```json
{
  "schema_version": 1,
  "task_filter": "PAPER-AUDIT-NEURIPS-2025-SGB-PHASE-TRANSITION-PROSPECTIVE",
  "experiment_filter": "",
  "eligible_rows": 1,
  "matched_experiments": [],
  "excluded_experiments": {
    "sgb-t2-round33-master-worker": "both harness arms are not present"
  },
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
      "experiments": 1,
      "runs": 1,
      "attempts": 1,
      "reviewed_attempts": 0,
      "substantive_attempts": 0,
      "failed_or_rejected_attempts": 0,
      "unreviewed_attempts": 1,
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
    "next_experiment_harness": "hierarchical",
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
    "matching_contract": [
      "same experiment id",
      "same target fingerprint",
      "same frozen route-packet hash",
      "separate reviewer-owned verdict for each execution attempt"
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
[
  {
    "time": "2026-09-02T06:26:53+00:00",
    "task": "PAPER-AUDIT-NEURIPS-2025-SGB-PHASE-TRANSITION-PROSPECTIVE",
    "experiment_id": "sgb-t2-round33-master-worker",
    "harness": "master-worker",
    "run_id": "sgb-theorem2-missing-pull-regret-consumer-round33-2026-09-02",
    "attempt_id": "sgb-t2-round33-worker-consumer",
    "role": "lower",
    "progress_class": "compiled-leaf",
    "status": "compiled",
    "obligations_before": 1,
    "new_declarations": [
      "BanditRLProof.StochasticGradientBandit.twoArmOptimalPullCountBelowEvent_charge_mul_probability_le_integral",
      "BanditRLProof.StochasticGradientBandit.twoArmFixedIIDLatentTrajectoryMeasure_map_visible_eq_generated",
      "BanditRLProof.StochasticGradientBandit.twoArmFixedIIDMissingPullLatentPhase_probability_le_countBelow",
      "BanditRLProof.StochasticGradientBandit.twoArmFixedIIDMissingPullLatentPhase_charge_mul_probability_le_integral"
    ],
    "reused_declarations": [
      "BanditRLProof.StochasticGradientBandit.twoArmAppendixCMissingPullLatentPhaseEvent_subset_terminalCountBelow",
      "BanditRLProof.StochasticGradientBandit.twoArmTerminalOptimalPullCountEvent_sampledPseudoRegret_eq",
      "BanditRLProof.Thompson.latentArmStreamVisibleTrajectoryMeasure_eq_native",
      "BanditRLProof.StochasticGradientBandit.twoArmFixedIIDTrajectoryMeasure_map_snd_eq_nativeStationary",
      "Measure.measure_mono"
    ],
    "notes": "Compiled the frozen finite-horizon missing-pull regret consumer. The latent missing-pull event is mapped through an exact latent-visible/generated-source marginal to the generated terminal-count-below event; its nonnegative-gap horizon-minus-block-size charge is bounded by expected sampled pseudo-regret. This proves neither positive missing-branch probability nor a source trigger, selected IID, future/no-return, ballot/asymptotic assembly, or Theorem 2.",
    "verifier_evidence": [
      "focused source build passed 3642 jobs; focused typed-canary build passed 3644 jobs; audited endpoints use only propext, Classical.choice, and Quot.sound",
      "SafeVerify passed with statement hash e0b6df5dcf07b860cdd4b02695c1621609030bb03ed06c502748691242ab7dc9 and all source-assumption tokens preserved",
      "full repository gate passed using C:\\Users\\admin\\anaconda3\\python.exe: 8852 library jobs, 8894 test jobs, 387 Python tests with 7 skipped; anonymous supplement tests passed"
    ]
  }
]
```
