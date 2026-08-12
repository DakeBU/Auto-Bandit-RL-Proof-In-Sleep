# Conversion Window: Generated bounded-reward KL-UCB regret

Task id: `KL-UCB-BOUNDED-GENERATED-REGRET`

Route: `ROUTE-KL-UCB`  
Source cards: `PPR-GARIVIER-CAPPE-2011-KLUCB`,
`TXT-LATTIMORE-SZEPESVARI-2020`  
Scenario card: `SCN-STOCHASTIC-FINITE`

## Natural-language statement

For a finite nonempty family of arms, define the Bernoulli KL index as the
supremum of `q in [0,1]` satisfying
`N * kl(empiricalMean,q) <= explorationBudget`.  Use that index in one
measurable reward-history policy with round-robin initialization.  On the
policy's own canonical action/reward trajectory measure, almost-everywhere
unit reward support and interior stationary means turn the accepted all-time
telescoping empirical-mean event into a KL confidence event.  KL optimism and
selected-index maximality imply an all-horizon positive-gap count bound; the
finite-arm decomposition then gives a finite-time expected pseudo-regret
bound with an explicit failure term.

## Lean mapping

| Source object | Lean declaration | Status |
| --- | --- | --- |
| Bernoulli relative entropy | `KLUCB.bernoulliKL` | compiled |
| interior Pinsker/upper comparison | `KLUCB.half_sq_sub_le_bernoulliKLCore`; `KLUCB.bernoulliKLCore_le_sq_div` | compiled |
| confidence set and index | `KLUCB.confidenceSet`; `KLUCB.index` | compiled |
| zero-count index | `KLUCB.index_zero_count` | compiled |
| generated KL-UCB policy/action | `KLUCB.historyPolicy`; `KLUCB.generatedAction` | compiled |
| history/trace alignment | `KLUCB.pairHistory_eq_finitePairHistoryOfTrace`; `KLUCB.historyIndex_finitePairHistoryOfTrace` | compiled |
| selected-index maximality | `KLUCB.generatedIndexAt_le_selected_of_K_le` | compiled |
| same-source KL confidence failure | `KLUCB.measure_generatedKLAllTimeBadEvent_le_trajMeasure` | compiled |
| one-round selected-arm threshold | `KLUCB.margin_mul_gap_div_eight_le_radius_of_selected_of_not_badEvent` | compiled |
| simultaneous all-horizon count | `KLUCB.allHorizonPullCount_of_not_badEvent` | compiled |
| canonical expected pseudo-regret | `KLUCB.lintegral_ofReal_pseudoRegret_generatedKLUCBBounded_le_trajMeasure` | compiled |

## Assumption ledger

| Assumption | Lean-facing contract |
| --- | --- |
| finite nonempty arms | `K : Nat`, `hK : 0 < K`, action type `Fin K` |
| probability source | probability initial pair law and canonical `Kernel.trajMeasure` |
| unit reward support | reward coordinate lies in `Set.Icc 0 1` almost everywhere on that measure |
| stationary exact means | reward-kernel mean equals `armMean arm` at every generated history |
| interior means | `0 < margin`, `margin <= 1/2`, and every mean is in `[margin,1-margin]` |
| concentration | positive `sigma2`, centered sub-Gaussian reward-kernel law, selected-history variance proxy bounded by `sigma2` |
| confidence budget | `0 < delta`; telescoping share is used at every positive prefix |
| endpoints | parameters outside `[0,1]` or singular right endpoint use `ENNReal.top`; diagonal endpoints are zero |
| zero count | confidence set is `[0,1]` and index is `1`; initialization establishes positive counts before score use |
| supremum | nonempty and bounded confidence set; only approximation below `sSup` is used, not unproved attainment |
| positive gap | required only for count inversion; best-arm dominance is explicit in regret assembly |
| expectation | measurable generated actions/counts and deterministic horizon cap; bad-event term is retained |

## Route actually compiled

1. Prove the explicit Bernoulli KL wrapper and finite interior comparison
   inequalities from Mathlib real-log/information-theory APIs.
2. Define the KL confidence set and `sSup` index, including exact zero-count
   behavior and optimism from membership.
3. Reconstruct the finite reward history used by the index and prove it equals
   the history extracted from the actual generated action/reward trace.
4. Instantiate the accepted telescoping empirical-mean theorem on this policy.
   A proved Bernoulli-KL upper comparison maps its absolute-deviation good event
   to the true-mean KL confidence condition.
5. Combine optimism, score maximality and Pinsker's lower comparison to obtain
   the selected-arm radius implication and invert the existing telescoping
   radius into an all-horizon pull-count threshold.
6. Integrate the count bound on the same canonical measure and use the finite
   arm gap decomposition for expected pseudo-regret.

## Deliberate nonclaims

- No measure-level KL identity is invoked, so no hidden absolute-continuity
  premise is needed by this compiled route.
- No sharp Bernoulli KL-Chernoff tail or Garivier--Cappé leading constant is
  claimed; the confidence producer is a conservative sub-Gaussian bridge.
- No asymptotic-optimality or limsup theorem is claimed.
- The explicit `T * delta` term is not silently discarded.
