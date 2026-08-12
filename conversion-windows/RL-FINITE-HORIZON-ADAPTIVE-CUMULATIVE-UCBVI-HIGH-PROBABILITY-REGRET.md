# Conversion window: adaptive cumulative UCB-VI high-probability regret

Task id: `RL-FINITE-HORIZON-ADAPTIVE-CUMULATIVE-UCBVI-HIGH-PROBABILITY-REGRET`

Route: `ROUTE-RL-UCBVI`  
Source cards: `PPR-AZAR-OSBAND-MUNOS-2017-UCBVI`,
`TXT-SLIVKINS-2019-2024`  
Scenario card: `SCN-RL-MDP`

## Frozen natural-language statement

For finite nonempty state and action types, a positive finite horizon `H`, a
positive episode budget `K`, confidence `0 < delta <= 1`, and known
deterministic rewards in `[0,1]`, run a single adaptive UCBVI-CH source.  Before
episode `k`, form cumulative state-action and transition counts from exactly
the prior generated episodes; compute the empirical transition model; run the
backward recurrence

```text
Q[k,h](x,a) = min (Q[k-1,h](x,a)) H
  (reward(x,a) + empiricalTransition(V[k,h+1]) + 7*H*L/sqrt(N[k](x,a)))
```

with value `H` at zero count and a measurable finite argmax policy.  Let
`T=K*H` and `L=log(5*H*S*A*T/delta)`.  On that source's own trajectory measure,
one simultaneous confidence event must imply optimism and the generated
cumulative episode regret must be at most

```text
20 * H^(3/2) * L * sqrt(S*A*K) + 250 * H^2 * S^2 * A * L^2
```

with probability at least `1-delta`.

## Lean mapping

| Mathematical object | Lean declaration or target | Status |
| --- | --- | --- |
| cumulative count/reward state | `AdaptiveCumulativeEmpiricalModelState` | compiled |
| prefix and round measurability | `EpisodeBatchPrefix.measurable_cumulativeEmpiricalModelState`; `measurable_adaptiveCumulativeEmpiricalModelStateAt` | compiled |
| exact transition/reward update | `adaptiveCumulativeEmpiricalModelStateAt_transitionCount_succ`; `adaptiveCumulativeEmpiricalModelStateAt_rewardSum_succ` | compiled |
| exact derived visit count | `adaptiveCumulativeEmpiricalModelStateAt_visitCount` | compiled |
| zero-count empirical reward | `AdaptiveCumulativeEmpiricalModelState.empiricalReward_of_visitCount_eq_zero` | compiled |
| paper-shaped log/radius | `AdaptiveCumulativeHoeffdingUCBVI.logFactor_eq_paper`; `.countRadius_zero`; `.countRadius_of_pos` | compiled |
| one-episode generated source | `AdaptiveCumulativeHoeffdingUCBVI.source` | compiled foundation |
| same-prefix source/policy/model | `.source_policyAt_succ_eq_modelState_optimisticPolicy` | compiled foundation |
| aggregate cross-stage paper count | `TransitionCountSummary.aggregateVisitCount`; `adaptiveCumulativeAggregateVisitCountAt_succ` | compiled; planner integration pending |
| previous-Q clipped optimistic DP | new recurrent plan state and policy | planned |
| adaptive same-source confidence | new bad event, measurability and measure bound | planned |
| generated Bellman optimism | new per-episode certificate | planned |
| regret decomposition/noise | new same-trajectory pathwise bound | planned |
| bonus/count summation | new explicit `S,A,H,K,L` inequality | planned |
| UCBVI-CH terminal | new cumulative high-probability theorem | planned |
| expected regret | new failure-aware integral corollary | planned |
| Bernstein/minimax | variance-aware second milestone | planned |

## Assumption ledger

| Assumption | Lean-facing contract |
| --- | --- |
| finite model | finite nonempty measurable State/Action; decidable equality; measurable singletons |
| horizon/episodes | `0 < mdp.horizon`, `0 < K`, `T=K*H` |
| confidence | `0 < delta <= 1`; safe total log proved equal to paper log on this domain |
| rewards | frozen terminal uses known deterministic `mdp.reward` with `0 <= reward <= 1` |
| probability space | one `AdaptiveEpisodeBatchSource.trajectoryMeasure`; fixed probability initial-state law in the project variant |
| empirical state | prior generated coordinates only; exact successor updates; count derived from transition rows |
| paper count | aggregate state-action visits over all stages and prior episodes; current stage-indexed view is insufficient |
| zero count | optimistic action value `H`; no division by zero |
| clipping | explicit `min` with previous episode Q table and `H` |
| selection | measurable finite argmax; chosen policy is exactly the generated source's policy |
| confidence | reward/transition event on the same trajectory, self-normalized by actual cumulative counts |
| regret | policy and initial state read from the same episode coordinate; high-probability before expectation |

## Compiled route and exact gap

The compiled foundation genuinely constructs a paired cumulative state, the
cross-stage paper-count view with its exact successor update, and a
history-dependent one-episode source with exact policy/model alignment. It does
not yet instantiate the paper algorithm: the selected source still passes
stage-indexed counts to the existing one-model optimistic plan, which has no
previous-Q clipping.
The available count-martingale cover is not yet the required adaptive
self-normalized transition-value confidence, and the natural-causal terminals
sum normalized batch regrets rather than raw episode regret.  Those differences
are proof obligations, not documentation details.

## Deliberate nonclaims

- No high-probability UCBVI-CH regret theorem is compiled yet.
- No expected-regret corollary follows until the bad-event contribution is
  integrated explicitly.
- No stochastic-reward version inherits the known-reward paper constants
  without a new theorem and calibration.
- No Bernstein bonus, law-of-total-variance argument, minimax leading rate, or
  complete variance-aware UCB-VI is claimed.
