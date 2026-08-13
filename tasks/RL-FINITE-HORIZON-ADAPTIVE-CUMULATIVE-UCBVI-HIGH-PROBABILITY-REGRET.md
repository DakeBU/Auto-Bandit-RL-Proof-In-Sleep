# Adaptive cumulative finite-horizon UCB-VI high-probability regret

Task id: `RL-FINITE-HORIZON-ADAPTIVE-CUMULATIVE-UCBVI-HIGH-PROBABILITY-REGRET`  
Kind: `theoremFormalization`  
Status: `accepted`  
Harness: `hierarchical`

## Goal

Construct the Hoeffding UCB-VI algorithm on one adaptive generated episode
process and prove its cumulative high-probability regret theorem.  The policy,
cumulative empirical model, simultaneous confidence event, optimistic planner,
episode regret, and terminal probability statement must refer to the same
`AdaptiveEpisodeBatchSource.trajectoryMeasure`.  A planner certificate, an
offline batch theorem, or a cumulative average of independently normalized
batch regrets is not the terminal.

## Source and exact first-milestone target

- Route: `ROUTE-RL-UCBVI`
- Scenario: `SCN-RL-MDP`
- Sources: `PPR-AZAR-OSBAND-MUNOS-2017-UCBVI`,
  `TXT-SLIVKINS-2019-2024`
- Weapons: `WEAPON-UCB-OPTIMISM`, `WEAPON-TAIL-INEQUALITIES`
  (proof inspiration only)
- Mathlib cards: `MLIB-PROBABILITY-KERNEL`,
  `MLIB-CONDITIONAL-EXPECTATION`, `MLIB-MARTINGALE-STOCHASTIC`,
  `MLIB-PROBABILITY-SUBGAUSSIAN`, `MLIB-PROBABILITY-VARIANCE`,
  `MLIB-MEASURE-INTEGRAL`, `MLIB-FINSET-SUMS`, `MLIB-ASYMPTOTICS`

The frozen Hoeffding target follows UCBVI-CH.  Write
`S = Fintype.card State`, `A = Fintype.card Action`, `T = K * H`, and
`L = log (5 * H * S * A * T / delta)`.  Under the paper-facing known
deterministic reward contract `0 <= reward <= 1`, positive `H` and `K`, and
`0 < delta <= 1`, the compiled canonical terminal bounds the generated cumulative
episode pseudo-regret by

```text
20 * H^(3/2) * L * sqrt (S * A * K)
  + 250 * H^2 * S^2 * A * L^2
```

outside an event of trajectory-measure at most `delta`.  The Lean theorem must
spell this without informal powers or hidden casts.  If stochastic rewards are
added, their reward-confidence cost and changed constants require a separately
frozen theorem; the paper constant must not be reused silently.

## Existing code reused

- `RL.FiniteHorizonPolicy`, `FiniteHorizonTrajectory`,
  `FiniteHorizonOptimality`, and `FiniteHorizonOccupancyRegret` provide the
  policy/value/trajectory/occupancy semantics.
- `FiniteHorizonOptimisticCertificate`,
  `FiniteHorizonEstimatedModelCertificate`, and
  `FiniteHorizonCoordinateModelConfidence` provide one-model optimism and
  regret consumers.
- `FiniteHorizonEmpiricalModel`, `FiniteHorizonIIDTrajectoryBatch`,
  `FiniteHorizonAdaptiveEpisodeBatchLaw`, and
  `FiniteHorizonAdaptiveEmpiricalOptimisticSource` provide generated batches
  and adaptive history-dependent policy selection.
- The adaptive cumulative count, stochastic-reward, visit-factorization, and
  transition-factorization modules are dependencies, not replacements for the
  end-to-end theorem.

## Compiled foundation

Target file:
`BanditRLProof/RL/FiniteHorizonAdaptiveCumulativeHoeffdingUCBVI.lean`.

- [x] `RewardSumSummary` and `AdaptiveCumulativeEmpiricalModelState` pair
  transition counts with reward sums from exactly one generated prefix.
- [x] `EpisodeBatchPrefix.measurable_cumulativeEmpiricalModelState` and
  `measurable_adaptiveCumulativeEmpiricalModelStateAt` prove measurability.
- [x] `adaptiveCumulativeEmpiricalModelStateAt_transitionCount_succ`,
  `adaptiveCumulativeEmpiricalModelStateAt_rewardSum_succ`, and
  `adaptiveCumulativeEmpiricalModelStateAt_visitCount` prove exact updates and
  derived-count alignment.
- [x] `TransitionCountSummary.aggregateVisitCount`,
  `measurable_adaptiveCumulativeAggregateVisitCountAt`, and
  `adaptiveCumulativeAggregateVisitCountAt_succ` expose the paper's
  cross-stage `N_k(x,a)` view with exact generated-prefix alignment.
- [x] `AdaptiveCumulativeEmpiricalModelState.empiricalReward` is totalized at
  zero count, with an explicit zero theorem.
- [x] `AdaptiveCumulativeHoeffdingUCBVI.logFactor_eq_paper` identifies the safe
  total logarithm with `log (5 H S A T / delta)` on the task domain.
- [x] `AdaptiveCumulativeHoeffdingUCBVI.countRadius` has exact zero-count and
  positive-count equations for the clipped `7 H L / sqrt N` shape.
- [x] `AdaptiveCumulativeHoeffdingUCBVI.source` generates one episode at every
  coordinate and contains no terminal round index in its policy type.
- [x] `source_policyAt_succ_eq_modelState_optimisticPolicy` locks the selected
  successor policy to the cumulative state derived from the same trajectory
  prefix.
- [x] The dedicated typed canary compiles and the audited declarations use only
  the project baseline axioms `propext`, `Classical.choice`, and `Quot.sound`.

## Proof DAG and remaining obligations

| Node | Contract | Status |
| --- | --- | --- |
| `UCBVI-STATE` | cumulative transition counts, reward sums, derived visit counts, exact successor update, measurability | compiled |
| `UCBVI-CALIBRATION-SOURCE` | total log/radius definitions; one generated episode per coordinate; same-prefix policy/model alignment | compiled foundation |
| `UCBVI-PAPER-COUNT` | aggregate `N_k(x,a,y)` and `N_k(x,a)` across all stages, exact same-prefix row sum/update | compiled |
| `UCBVI-CLIPPED-PLAN` | recurrent `Q_{k,h} = min(Q_{k-1,h}, H, R + P_hat V + b)`; zero-count value `H`; measurable finite argmax | compiled |
| `UCBVI-SAME-SOURCE-CONFIDENCE` | simultaneous singleton Bernstein plus normalized optimal-tail probe event on the recurrent source law | compiled |
| `UCBVI-OPTIMISM` | good event implies Bellman optimism for every generated recurrent plan | compiled |
| `UCBVI-REGRET-DECOMPOSITION` | generated successor pseudo-regret obeys weighted charge plus generated Bellman innovation | compiled |
| `UCBVI-BONUS-SUM` | actual-count clipped charge sum with explicit `S,A,H,K,L` bound | compiled |
| `UCBVI-CH-TERMINAL` | same-process event mass at most `delta` and the frozen cumulative regret bound | compiled |
| `UCBVI-EXPECTED` | integrable expected-regret corollary with explicit `K*H*delta` failure contribution | compiled |
| `UCBVI-BERNSTEIN` | variance bonus, empirical variance confidence, total variance, minimax leading rate | second milestone; planned |

## Closed semantic mismatch ledger

- The new recurrent source consumes aggregate transition numerators and visit
  denominators from the same strict prefix and does not call the older
  stage-indexed `EstimatedModelPlan`.
- `clippedQRemaining` carries the previous Q table literally and totalizes a
  zero count to `H`.
- The confidence event is proved on the recurrent source's own generated law.
  It includes p-sensitive singleton coordinates and a normalized optimal-tail
  scalar probe from the same raw transition kernel; it does not use a caller
  confidence premise, an independent batch, or a reachability floor.
- The terminal uses raw `Fin episodes` policy-value pseudo-regret, including
  coordinate zero, and is distinct from natural-causal batch-average or
  realized sampled-return statements.
- The compiled reward-sum state is structural.  The current paper-shaped
  source still plans with the known deterministic `mdp.reward`; reward sums do
  not yet enter the selected plan.

## Regularity and totalization contract

- finite nonempty measurable `State` and `Action`, decidable equality and
  measurable singletons; Standard Borel instances where kernel regularity
  requires them;
- `0 < mdp.horizon`, `0 < K`, and `0 < delta <= 1`;
- probability initial-state law for the current project variant; any
  adversarial episode-initial-state generalization is separate;
- deterministic known reward in `[0,1]` for the frozen UCBVI-CH terminal;
- zero empirical count gives the explicit high optimistic value `H` and never
  divides by zero;
- every log, square root, cast, division, clipped value, and denominator has an
  explicit domain proof;
- the terminal cumulative regret uses the policy and start state read from the
  same generated episode coordinate.

## Gates and failure policy

- [x] Focused source build.
- [x] Dedicated exact-type canary and representative axiom audit.
- [x] Historical full repository gate for the compiled foundation: 3664 Lean
  build jobs; 43 Python tests passed with one expected skip.
- [x] Paper aggregate-count view/update node.
- [x] Clipped-plan/confidence/decomposition/bonus/high-probability/expected nodes.
- [x] Public root build and nondegenerate `Tests/BookMapChapterNineCanary.lean`.
- [x] Full terminal reviewer gate: independent read-only ACCEPT, no unresolved
  P0--P3 findings.
- [x] Refreshed full `python3 tools/bandit.py check`: 3699 Lean jobs; 42 Python
  tests passed with one expected skip; `check passed`.

The Hoeffding nodes, reviewer, refreshed full harness, GitHub Actions, merge,
and Pages gates are closed. Do not substitute a caller-supplied confidence
witness, an offline
iid batch, forced-exploration consistency, a batch-average stopping theorem,
or an expected-regret theorem for the required generated high-probability
cumulative regret theorem.  Do not label Bernstein/minimax UCB-VI complete
until the second milestone has its own compiled terminal.
