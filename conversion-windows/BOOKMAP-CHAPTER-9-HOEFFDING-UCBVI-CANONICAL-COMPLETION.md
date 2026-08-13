# Conversion Window: Book Map Chapter 9 Hoeffding UCBVI canonical completion

Task id: `BOOKMAP-CHAPTER-9-HOEFFDING-UCBVI-CANONICAL-COMPLETION`

## Frozen statement boundary

The terminal is the generated known-reward UCBVI-CH probability theorem on one
`AdaptiveEpisodeBatchSource.trajectoryMeasure`.  With
`T = K * mdp.horizon` and the compiled safe logarithm identified with
`L = log (5*H*S*A*T/delta)`, the cumulative raw episode pseudo-regret failure
set above

```text
20 * H * sqrt(H) * L * sqrt(S*A*K)
  + 250 * H^2 * S^2 * A * L^2
```

has ENNReal mass at most `ENNReal.ofReal delta`.  The expected corollary keeps
the additional `K*H*delta` contribution.

## Symbol mapping

| Mathematical object | Lean surface or target | Status |
| --- | --- | --- |
| finite Bellman/occupancy foundations | `FiniteHorizonPolicy`, `FiniteHorizonTrajectory`, `FiniteHorizonOptimality`, `FiniteHorizonOccupancyRegret` | compiled |
| adaptive generated law | `AdaptiveEpisodeBatchSource.trajectoryMeasure` | compiled |
| cumulative paired state | `AdaptiveCumulativeEmpiricalModelState` and exact successor lemmas | compiled |
| aggregate denominator `N_k(x,a)` | `TransitionCountSummary.aggregateVisitCount`, `adaptiveCumulativeAggregateVisitCountAt_succ` | compiled |
| aggregate numerator `N_k(x,a,y)` | `adaptiveCumulativeAggregateTransitionCountAt`; exact sum/update APIs | compiled |
| aggregate empirical kernel | `TransitionCountSummary.aggregateEmpiricalTransitionKernel`; zero and positive-count equations | compiled |
| log/radius | `AdaptiveCumulativeHoeffdingUCBVI.logFactor`, `.scale`, `.countRadius` | compiled calibration |
| recurrent clipped planner | `clippedQRemaining`, `recurrentQTableOfSummaries`, `recurrentSource` | compiled |
| canonical recurrent source | `recurrentSource_policyAt_succ`; strict-prefix recurrent table | compiled |
| same-source confidence | joint singleton-Bernstein and normalized-optimal-tail probe event on `recurrentSource.trajectoryMeasure` | compiled |
| optimism | `AdaptiveEpisodeBatchSource.recurrentQTableOfTrajectory_dominatesOptimal` | compiled |
| cumulative pseudo-regret | `generatedEpisodePseudoRegret`, `cumulativeEpisodePseudoRegret` | compiled |
| bonus and martingale assembly | `totalGeneratedPairCharge_le_explicit`; tuned Bellman-innovation tail | compiled |
| high-probability terminal | `recurrentSource_trajectoryMeasure_cumulativeEpisodePseudoRegret_gt_canonicalRegretBound_le` | compiled |
| expected corollary | `integral_cumulativeEpisodePseudoRegret_recurrentSource_le_canonicalRegretBound_add_failure` | compiled |

## Assumption ledger

Finite nonempty decidable State/Action; measurable singletons and required
Standard Borel instances; probability initial law; positive horizon and
episode budget; `0 < delta <= 1`; deterministic known reward in `[0,1]`;
strictly prior generated prefix at episode `k`; aggregate actual counts;
optimistic zero-count value `H`; safe log/sqrt/division; measurable finite
argmax with a fixed tie break.

## Deliberate separation

The old stage-indexed empirical plan, offline iid batches, exploratory
reachability floors, cumulative coordinate cover supplied by a caller, and
normalized batch-average/stopping results are not the target algorithm or
terminal.  Hoeffding completion does not imply the Bernstein/minimax milestone.

The sharp optimal-tail transition-value probe is proved from the same raw
generated transition law and included in the same finite failure event as the
singleton Bernstein coordinates. It is not inferred from singleton bounds
alone: that implication would lose a factor `sqrt S`. Thus the confidence
event is same-source without claiming a false coordinate-only inversion.
