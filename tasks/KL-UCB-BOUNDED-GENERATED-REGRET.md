# Generated bounded-reward KL-UCB regret

Task id: `KL-UCB-BOUNDED-GENERATED-REGRET`  
Kind: `theoremFormalization`  
Status: `accepted`  
Harness: `hierarchical`

## Goal

Define a Bernoulli-KL confidence-supremum selector and run it as one measurable,
horizon-free policy on the canonical finite-arm generated action/reward
trajectory.  The terminal is a same-source finite-time expected pseudo-regret
theorem backed by all-time confidence and an all-horizon pull-count theorem; a
scalar KL inequality or an ordinary-UCB wrapper is not the terminal.

## Source and scope

- Route: `ROUTE-KL-UCB`
- Paper: `PPR-GARIVIER-CAPPE-2011-KLUCB`
- Textbook: `TXT-LATTIMORE-SZEPESVARI-2020`
- Scenario: `SCN-STOCHASTIC-FINITE`
- Weapons: `WEAPON-KL-CHANGE-OF-MEASURE`, `WEAPON-UCB-OPTIMISM`
  (proof inspiration only)
- Mathlib cards: `MLIB-EXP-LOG-INEQUALITIES`, `MLIB-MEASURE-INTEGRAL`,
  `MLIB-ORDER-ALGEBRA`, `MLIB-FINSET-SUMS`, `MLIB-REAL-LOG-SQRT`,
  `MLIB-ASYMPTOTICS`

The compiled theorem is a conservative finite-time generated-policy result.
It assumes means lie in `[margin, 1-margin]`, rewards are almost everywhere in
`[0,1]` on the canonical trajectory measure, and a centered sub-Gaussian
kernel law supplies the accepted telescoping empirical-mean confidence event.
It does **not** claim the Garivier--Cappé leading constant, a direct KL-Chernoff
tail, or asymptotic optimality.

## Lean targets

```lean
KLUCB.bernoulliKL
KLUCB.half_sq_sub_le_bernoulliKLCore
KLUCB.bernoulliKLCore_le_sq_div
KLUCB.confidenceSet
KLUCB.index
KLUCB.historyPolicy
KLUCB.generatedAction
KLUCB.pairHistory_eq_finitePairHistoryOfTrace
KLUCB.generatedIndexAt_le_selected_of_K_le
KLUCB.measure_generatedKLAllTimeBadEvent_le_trajMeasure
KLUCB.margin_mul_gap_div_eight_le_radius_of_selected_of_not_badEvent
KLUCB.allHorizonPullCount_of_not_badEvent
KLUCB.lintegral_ofReal_pseudoRegret_generatedKLUCBBounded_le_trajMeasure
```

Target files:

- `BanditRLProof/Algorithms/KLUCBBernoulli.lean`
- `BanditRLProof/Algorithms/KLUCBGeneratedRegret.lean`
- `Tests/KLUCBGeneratedRegretCanary.lean`

## Compiled contracts

- [x] Bernoulli KL has explicit outside-domain `top`, singular `q=0/1`,
  endpoint diagonal, nonnegativity, diagonal zero, continuity, and the finite
  interior comparison inequalities used by the route.
- [x] The KL confidence set and `sSup` index compile, lie in `[0,1]`, have
  index `1` at zero count, prove optimism from membership, and never assume an
  unattested supremum maximizer.
- [x] `historyPolicy`, `historyState`, index, argmax and generated action are
  measurable and contain no terminal horizon parameter.
- [x] Pair-history reconstruction aligns the score, empirical count, empirical
  mean, selected arm and actual reward-generated trace exactly.
- [x] The accepted telescoping producer is instantiated on this policy; the
  sampled/generated action equality is transported on the same trajectory
  measure rather than changing probability spaces.
- [x] Outside one all-time bad event, every positive-gap arm obeys the compiled
  single-round radius implication and all-horizon pull-count threshold.
- [x] The same canonical measure yields finite-time expected pseudo-regret with
  an explicit `T * delta` failure contribution.
- [x] Focused modules and the dedicated typed canary compile; representative
  axiom reports contain only `propext`, `Classical.choice`, and `Quot.sound`.
- [x] Full `python3 tools/bandit.py check` passes after synchronized artifacts.

## Evidence boundary

- `PPR-GARIVIER-CAPPE-2011-KLUCB` and the weapon cards select the route; they
  are not local proof evidence.
- The policy score really is the `sSup` of the Bernoulli-KL confidence set; no
  ordinary additive UCB score is relabelled as KL-UCB.
- The confidence-probability proof is conservative: a proved interior upper
  bound on Bernoulli KL turns the existing same-source absolute-deviation event
  into KL feasibility.  A sharp KL change-of-measure/Chernoff exponent remains
  a separate refinement.
- The expected bound retains `T * delta`; fixed-delta expected-average
  consistency and Garivier--Cappé asymptotic optimality are not claimed.
