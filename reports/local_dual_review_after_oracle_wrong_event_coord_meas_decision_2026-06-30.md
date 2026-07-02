# Local Dual-Agent Review Response: After Oracle Wrong-Event Coordinate Measurability

- Date: 2026-06-30
- Tool/model: Local dual-agent review
- Prompt file: `reports/local_dual_review_after_oracle_wrong_event_coord_meas_prompt_2026-06-30.md`
- Local gate before review: `python3 tools\bandit.py check`
- Boundary:
  `ETC-COMMIT-ORACLE-WRONG-EVENT-MEASURABILITY-OF-COORDINATES`

## Reviewer Decision

- Chosen next leaf: `ETC-COMMIT-ORACLE-CONCRETE-ARGMAX-ROUTE-CARD`
- Classification: theorem-card-only
- Status: local-dual-agent-approved route card

## Agent A Opinion

The tool/CLI reviewer recommended replacing the hard Extended Pro gate with a
generic local review gate while preserving historical Extended Pro artifacts.
They also warned that `review-status` should remain read-only and that local
agent spawning should stay in the main workflow or an explicit command, not in
status inspection.

## Agent B Opinion

The project-process reviewer recommended minimal documentation changes: keep
the proof status unchanged, add a superseding note to the Extended Pro pending
artifact, and record a new local review decision artifact. For the next route,
they selected Candidate A because the project already has abstract oracle
measurability and probability wrappers, while the concrete finite argmax-backed
oracle contract is the smallest missing bridge before tail or filtration work.

## Reconciled Decision

Select Candidate A:
`ETC-COMMIT-ORACLE-CONCRETE-ARGMAX-ROUTE-CARD`.

This batch should write the route card only. It should not implement the
concrete argmax oracle, prove pairwise concentration, introduce filtration,
or attempt a final ETC theorem.

Rejected candidates for this batch:

- `ETC-PAIRWISE-TAIL-IMPORT-ROUTE-CARD`: important but premature before the
  concrete oracle interface is pinned down.
- `FILTRATION-HISTORY-ROUTE-CARD`: broader than the immediate oracle gap and
  should wait until a precise tail theorem target requires it.

## Exact Lean-Facing Statement

```lean
-- Route-card only for this batch. A later implementation should specify
-- an argmax-backed oracle and a theorem connecting its maximality certificate
-- to the existing abstract argmax consumer.
```

## Imports And Local APIs

- `BanditRLProof.Algorithms.ETC`
- `BanditRLProof.Algorithms.ETCMeasurability`
- `BanditRLProof.Algorithms.ETCWrongCommit`
- local `ETC.CommitOracle K`
- local `ETC.commitOracle_argmax_consumer`

## Intended Proof Route

1. Write a route card defining the desired finite argmax-backed oracle
   interface.
2. Specify the nonempty-arm contract for `Fin K`, likely `0 < K`.
3. Specify deterministic tie-breaking, preferably by first maximal index under
   a stable finite enumeration.
4. State the selected-score maximality theorem needed by the existing abstract
   wrong-commit consumer.
5. State measurability obligations for oracle choice as already covered by the
   countable score-vector and coordinatewise empirical-mean wrappers.

## Regularity Contracts

- `0 < K` or an equivalent inhabitance/nonemptiness contract for `Fin K`.
- `[LinearOrder Rat]` from existing Rat order structure.
- Decidable comparisons on scores.
- Stable tie-breaking independent of probability space data.
- No probability, concentration, filtration, or final regret assumptions in
  this route-card batch.

## Retrieval Evidence

- Local declarations already compile for abstract oracle choice measurability,
  coordinate-to-choice measurability, and coordinate-to-wrong-event
  measurability.
- Local probability wrappers already consume abstract pairwise-tail hypotheses.
- The missing bridge is not a Mathlib concentration theorem; it is the
  project-local concrete oracle construction plan.

## Failure Policy

If the concrete argmax route requires additional finite-order helper lemmas,
stop at the route card and record those helpers as separate future leaves. Do
not import probability theory, start concentration, or implement final ETC
regret in the same batch.

## Combined Local Review

Two local agents reviewed the workflow change and the route choice. The
combined decision is to replace the required Extended Pro gate with local
dual-agent review artifacts and to select the concrete argmax oracle route
card as the next single theorem-card-only task.
