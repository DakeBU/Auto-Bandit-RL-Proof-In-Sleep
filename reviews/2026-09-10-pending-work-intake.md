# Pending-work intake: deterministic SGB adapters

Baseline: the accepted research main, including Books navigation. This intake
reviews old working copies; it does not finish the source paper's Theorem 2.

## Retrieval and scope fixed before proof work

Source card: `PPR-BAUDRY-JOHNSON-VARY-PIKEBURKE-REBESCHINI-2025-SGB`.
Scenario: `SCN-STOCHASTIC-FINITE`. Mathlib cards: `MLIB-ORDER-ALGEBRA`,
`MLIB-EXP-LOG-INEQUALITIES`, `MLIB-REAL-LOG-SQRT`.
No proof-weapon card is used as a theorem dependency and no new import is needed.

The three odds-threshold declarations from the old round-34 working copy and
the three deterministic adapters in the old phase-trigger commit are absent
from the accepted library under their original names. They have complementary
contracts, not six independent proofs of the phase trigger.

Existing APIs: `exp_two_mul_zero_mul_one_sub_softmaxProbability_zero`,
`historyParameter_exp_two_mul_zero_eq_odds`,
`historyParameter_zeroInitialization_sum`, `softmaxProbability_nonneg`,
`softmaxProbability_le_one`, `twoArmNthOptimalPullTime_spec`, and the existing
all-pulls-present phase event. Retrieval searches checked the local declaration
index and Mathlib cards before changing Lean files.

## Mathematical review

For the zero-sum two-arm parameter, write `r = exp(2 theta_0)` and
`p = softmax(theta)_0`. The existing exact identity is `r*(1-p)=p`.
It implies `p <= r`. For a natural horizon `T >= 1`, the sharper implication
`r <= 1/(2*T-1) -> p <= 1/(2*T)` uses the strictly positive denominator
`2*T-1`. These are different sufficient thresholds. The logarithmic adapter
uses `2 theta_0 <= -log(2*T)`; the exact-odds adapter does not silently replace
that premise with a statement derived from the reward phase.

The finite-pull specialization retains an explicit equality between the
`WithTop Nat` pull time and a finite chronological time. The occurrence adapter
requires a positive block size and membership in the all-pulls-present event;
it exposes the zero-based last index `n0+n1-1` and exact count/action/count
transition. It never identifies a missing pull with a finite time.

The intended proof route is the already-written ordered-field argument and
existing stopped-time specification. No new source assumption, selected-IID
assertion, stopped future law or concentration estimate is introduced.

## Acceptance gate

Focused validation: all six declarations and typed canaries compile; axiom
prints contain only `propext`, `Classical.choice` and `Quot.sound`. A new
horizon-one test initially needed an explicit natural-to-real normalization;
the test was repaired without changing any theorem contract. Check all six
headers, positive-horizon and missing-pull premises, typed canaries and axiom
prints, then the full library/harness and website checks. The full phase-to-
parameter recurrence, positive phase probability, no-return law, ballot bound
and source Theorem 2 stay unresolved. Maintainer review here is not described
as an independent blinded semantic review.

The full library, `Tests` and proof-graph exporter compiled on the pinned
4.29.1 toolchain. The final complete project gate passed 421 Python tests
(seven platform/environment skips); the focused intake suite passed 71 tests
(one skip), including the master/synthesis failure regression. Website
generation and link/declaration/formula/diagram checks also passed.

## Harness intake

The old lifecycle edits preserve multiline result-let statements, ignore
quoted identifiers during that scan, and reject empty, escaping or aliased
overlapping file ownership. The current harness already calls a successful
process `executed`, not `compiled`; retain that newer vocabulary. Port the
remaining first-failure preservation and head/tail context fixes onto both
current execution modes, with deterministic regression tests. Do not restore
the old sequential-only help text over the newer parallel-worker implementation.

The old LML toolchain audit is not merged: it changes Lean to 4.32.0-rc1,
changes Mathlib, adds LML and renames the test library. Its two direct wrappers
are upstream-symbol experiments, not additional 4.29.1 library theorems. The
current faithful local field-compatibility route and dependency boundary stay
unchanged; complete source and logs are preserved privately for a future
separately scoped migration.
