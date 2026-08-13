# Proof obligations: adaptive cumulative UCB-VI high-probability regret

Task id: `RL-FINITE-HORIZON-ADAPTIVE-CUMULATIVE-UCBVI-HIGH-PROBABILITY-REGRET`

Source: `PPR-AZAR-OSBAND-MUNOS-2017-UCBVI`; `TXT-SLIVKINS-2019-2024`  
Scenario: `SCN-RL-MDP`

| Node | Declaration or target | Contract | Gate | Status |
| --- | --- | --- | --- | --- |
| `STATE-MEASURABLE` | `EpisodeBatchPrefix.measurable_cumulativeEmpiricalModelState`; `measurable_adaptiveCumulativeEmpiricalModelStateAt` | paired counts/reward sums from one generated prefix | focused Lean | compiled |
| `STATE-UPDATE` | `adaptiveCumulativeEmpiricalModelStateAt_transitionCount_succ`; `adaptiveCumulativeEmpiricalModelStateAt_rewardSum_succ`; `adaptiveCumulativeEmpiricalModelStateAt_visitCount` | exact successor update; visit count derived from transition rows | typed canary | compiled |
| `ZERO-COUNT` | `AdaptiveCumulativeEmpiricalModelState.empiricalReward_of_visitCount_eq_zero`; `AdaptiveCumulativeHoeffdingUCBVI.countRadius_zero` | no hidden positive denominator | typed canary | compiled |
| `LOG-RADIUS` | `AdaptiveCumulativeHoeffdingUCBVI.logFactor_eq_paper`; `.countRadius_of_pos` | `T=KH`, `L=log(5HSAT/delta)`, `7HL/sqrt N`, task-domain proofs | focused Lean | compiled |
| `GENERATED-SOURCE` | `AdaptiveCumulativeHoeffdingUCBVI.source`; `.source_policyAt_succ_eq_modelState_optimisticPolicy` | one adaptive generated process; successor policy reads the same prefix | typed canary | compiled foundation |
| `AGGREGATE-COUNT` | `sum_adaptiveCumulativeAggregateTransitionCountAt_eq_visitCountAt`; `adaptiveCumulativeAggregateTransitionCountAt_succ` | paper count `N_k(x,a)` sums visits across stages and prior episodes; exact same-prefix numerator/denominator | typed canary | compiled |
| `CLIPPED-RECURRENT-PLAN` | `AdaptiveCumulativeHoeffdingUCBVI.recurrentQTableOfSummaries`; `.recurrentSource_policyAt_succ` | `min(Q_previous,H,backup)`, zero-count `H`, finite measurable argmax | focused Lean | compiled |
| `SAME-SOURCE-CONFIDENCE` | `.recurrentSource_trajectoryMeasure_simultaneousTransitionFailureEvent_le_fifth` | joint singleton Bernstein and normalized optimal-tail probes; actual adaptive counts; recurrent source law | typed canary | compiled |
| `BELLMAN-OPTIMISM` | `AdaptiveEpisodeBatchSource.recurrentQTableOfTrajectory_dominatesOptimal` | confidence implies optimism for each generated episode plan | focused Lean | compiled |
| `REGRET-DECOMPOSITION` | `.recurrentSource_generatedSuccessorPseudoRegret_le_charge_add_innovation` | optimism, weighted local charge and generated Bellman innovation on one process | focused Lean | compiled |
| `BONUS-SUM` | `.totalGeneratedPairCharge_le_explicit` | explicit `S,A,H,K,L`; actual counts and zero/low-count charge | focused Lean | compiled |
| `UCBVI-CH-TERMINAL` | `.recurrentSource_trajectoryMeasure_cumulativeEpisodePseudoRegret_gt_canonicalRegretBound_le` | `20 H^(3/2)L sqrt(SAK) + 250 H^2 S^2 A L^2`; known reward `[0,1]` | root/tests/reviewer | compiled; independent review accepted |
| `EXPECTED-COROLLARY` | `.integral_cumulativeEpisodePseudoRegret_recurrentSource_le_canonicalRegretBound_add_failure` | integrable and retains `K*H*delta` failure contribution | focused Lean | compiled |
| `BERNSTEIN-MINIMAX` | planned variance-aware route | empirical variance, total variance and paper-leading rate | separate milestone | planned |
| `ROOT-GATE` | root import, dedicated canary, no placeholders, baseline axioms, synchronized artifacts | no target weakening | full `python3 tools/bandit.py check` | accepted: 3699 jobs; 42 tests, one skipped; `check passed` |

## Retrieval evidence

- Local producers: adaptive episode batch law, cumulative transition summary,
  generated optimistic selector, coordinate confidence, count martingale,
  stochastic reward confidence, stage visit/transition factorization.
- Local consumers: Bellman optimism, occupancy regret, estimated-model
  confidence, one-episode expected regret, cumulative selected-radius algebra.
- Mathlib routes: kernels and trajectory measures; conditional expectation and
  martingales; finite sums/unions; sub-Gaussian/variance tails; ENNReal and
  Bochner integration.
- Paper and weapon cards determine the route but are not Lean proof evidence.

## Failure and claim policy

The existing stage-indexed planner and batch-average high-probability terminals
may be dependencies only.  Do not relabel them as the aggregate-count,
cross-episode-clipped UCBVI-CH algorithm.  Do not move confidence to an
independent probability space, hide zero counts or log/division conditions,
drop the martingale/noise term, infer expectation without a failure-event
bound, or claim Bernstein/minimax completion from the Hoeffding milestone.
