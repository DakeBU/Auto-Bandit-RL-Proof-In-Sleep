# Proof Obligations: Book Map Chapter 9 Hoeffding UCBVI canonical completion

Task id: `BOOKMAP-CHAPTER-9-HOEFFDING-UCBVI-CANONICAL-COMPLETION`

| Node | Target | Local APIs/imports | Gate | Status |
| --- | --- | --- | --- | --- |
| `CH9-BELLMAN` | policy evaluation, optimality, occupancy regret | compiled finite-horizon foundation modules | root declarations | compiled |
| `CH9-GENERATED-TRAJECTORY` | one adaptive generated batch trajectory and raw episode pseudo-regret semantics | `FiniteHorizonAdaptiveEpisodeBatchLaw`, trajectory/value APIs | typed application | compiled foundation |
| `CH9-CUMULATIVE-STATE` | aggregate `N_k(x,a,y)`, row sum `N_k(x,a)`, successor update, measurable empirical row, zero fallback | `FiniteHorizonAdaptiveCumulativeUCBVIAggregateTransition` | focused Lean | compiled |
| `CH9-CLIPPED-RECURRENT-PLAN` | `min(Q_previous,H,reward+P_hat V+bonus)`; initial Q=`H`; finite measurable argmax | `FiniteHorizonAdaptiveCumulativeUCBVIClippedPlanner` | focused Lean | compiled |
| `CH9-GENERATED-SOURCE` | source policy at episode `k` is exactly the recurrent plan from coordinates `< k` | `recurrentSource_policyAt_succ` | exact-let typed canary | compiled |
| `CH9-SAME-SOURCE-CONFIDENCE` | simultaneous transition confidence at actual aggregate counts on the source trajectory law | singleton Bernstein plus same-law optimal-tail probe and finite union | probability canary | compiled |
| `CH9-OPTIMISM` | good event implies recurrent-plan Bellman optimism at every episode/stage | `recurrentQTableOfTrajectory_dominatesOptimal` | focused Lean | compiled |
| `CH9-REGRET-DECOMPOSITION` | generated cumulative episode pseudo-regret bounded by bonuses and martingale noise | `recurrentSource_generatedSuccessorPseudoRegret_le_charge_add_innovation` | focused Lean | compiled |
| `CH9-BONUS-SUM` | actual-count clipped bonus sum with explicit `S,A,H,K,L` bound | `totalGeneratedPairCharge_le_explicit` | focused Lean | compiled |
| `CH9-MARTINGALE-SUM` | generated-filtration transition-value noise event and explicit tail | tuned recurrent Bellman-innovation theorem | probability canary | compiled |
| `CH9-HIGH-PROBABILITY` | generated-law event with frozen `20/250` UCBVI-CH threshold | `FiniteHorizonAdaptiveCumulativeUCBVITerminal` | root/Tests/reviewer | compiled |
| `CH9-EXPECTED` | integrability and expected regret at most frozen bound plus `K*H*delta` | `FiniteHorizonAdaptiveCumulativeUCBVIExpectedRegret` | focused Lean | compiled |
| `CH9-TYPED-CANARY` | fourteen full-conclusion groups and nondegenerate `Fin 2` recurrent terminal instance | `Tests/BookMapChapterNineCanary.lean` | dedicated/root Tests | compiled |
| `CH9-REVIEW-SYNC` | independent read-only review; task/window/obligation/blueprint/DAG/site/index agreement | harness and website scripts | no unresolved P0--P3 | accepted |
| `CH9-LOCAL-FULL-GATE` | focused modules, root, Tests, SafeVerify, site and final harness check | `python3 tools/bandit.py check` | deterministic full gate | accepted: 3699 jobs; 42 tests, one skipped; `check passed` |
| `CH9-REMOTE-DELIVERY` | PR, Actions, merge, Pages and live chapter verification | GitHub/Pages workflow | remote checks | planned |

## Reviewer statement fence

- The final policy is the recurrent generated policy, not the prior
  `countRadiusOptimisticPlan` and not a caller-supplied policy.
- Every plan at episode `k` uses only the prefix strictly before `k`; coordinate
  zero and `Fin K`/`range K` off-by-one conventions are explicit.
- Confidence and regret use the exact same recurrent source and exact same
  trajectory measure.
- Aggregate actual counts, not expected reachability or a deterministic floor,
  normalize the transition estimates and bonuses.
- The high-probability theorem contains the exact frozen conclusion and no
  confidence/optimism/decomposition/bonus target premise.
- The expectation proof retains the bad-event term; baseline axioms only.
- Bernstein/minimax and stochastic-reward UCBVI remain unclaimed.

## Failure classification

Record the first exact failure as recurrence/API, measurability, source/prefix
alignment, adaptive actual-count concentration, Bellman optimism, regret
decomposition, bonus summation, martingale tail, terminal constants,
integrability, typed-canary, review, local full gate, or remote delivery.  Do
not weaken the fenced statement.
