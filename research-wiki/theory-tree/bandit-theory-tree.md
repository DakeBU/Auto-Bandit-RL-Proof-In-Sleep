# ABRL Bandit Theory Tree

This is the working tree for reproducing bandit/RL theory in Lean.  It is
organized so lower agents can find the smallest usable leaf instead of
rebuilding a proof from scratch.

## Root Spine

```text
Bandit/RL theorem target
-> source card: textbook, paper, LML, or Mathlib
-> scenario card
-> definition layer
-> regularity contracts
-> concentration/posterior/optimization spine
-> algorithm wrapper
-> final regret/sample-complexity theorem
-> Markdown and LaTeX export
```

## Paper-Guided Build Order

The paper's two audited focal cases are source-shaped ETC expected regret and
uncapped finite-horizon stopped-value RL. They remain evidence anchors, while
new Lean work follows the shared dependency order: recurring
probability/filtration/stopping/concentration contracts; canonical stochastic
and adversarial textbook consumers; OFUL's self-normalized matrix layer; then
modular RL Bellman, occupancy, confidence, and policy-output interfaces.

The Book Map Chapters 7--8 canonical gate now compiles two independent routes.
Chapter 7 includes potential/Hedge algebra, generated importance-weighted
moments, horizon-tuned expected regret, a horizon-tuned fixed-window best-arm
tail, one fixed-process and fixed-comparator all-positive-prefix realized-
regret event, and a separately labelled sparse extension.  Chapter 8 includes
half-Tsallis minimizer regularity, the scheduled generated action law, score
alignment, all-rate expected stability, fixed-gap self-bounding, and a
finite-arm IID bounded reward-law logarithmic terminal.  The public canary
keeps every generated measure visible and instantiates the Tsallis terminal
with a concrete Dirac law.

The next nodes are extensions, not missing canonical prerequisites: aggregate
the finite supported comparator set on the same fixed EXP3 process, construct
a horizon-free tuned EXP3 policy, or strengthen Tsallis toward paper-sharp
best-of-both-worlds/high-probability guarantees.  Ville/Doob, mixtures,
optional stopping, general Freedman, EXP3.P, observed-reward restart detection,
and complete Tsallis-INF remain unclaimed.

## Definition Layer

| Branch | Leaf nodes | Current status |
| --- | --- | --- |
| Finite actions | `Fin K`, nonempty action set, finite policies, arm casts | dependency-light local core plus Mathlib card `MLIB-FINTYPE-FIN` |
| Time traces | action traces, reward traces, histories, filtrations | local finite traces plus measurable action-event and indicator canaries; filtrations are theorem-card/proof-obligation |
| Pull counts | recursive count, monotonicity, split by arm/time, finite-action partition, indicator sum bridge | compiled leaves in `BanditRLProof.LeafLemmas` plus `pullCount_eq_finset_filter_card` and `finset_sum_pullCount_eq_time` |
| Regret | pseudo-regret, gap decomposition, Bayesian regret, dynamic regret | compiled pseudo-regret and `REGRET-PULLCOUNT` core plus generated expected-regret routes and one explicit-envelope actual-mean dynamic Tsallis route; Bayesian regret remains theorem-card |
| Reward models | rational mean surface, sub-Gaussian rewards, Bernoulli rewards, kernels | local rational surface; probability layer staged |
| Resource models | budgets, consumption traces, stopping by budget | theorem-card via `SCN-RESOURCE-CONSTRAINED` and BwK paper card |
| Preference models | pairwise preference matrices, winner notions, ranking regret | theorem-card via `SCN-DUELING-PREFERENCE` |
| Federated models | client-indexed traces, aggregation rounds, heterogeneous means | theorem-card via `SCN-FEDERATED-DISTRIBUTED` |

## Reusable Mathematical Leaves

| Leaf family | Mathlib cards | Downstream branches |
| --- | --- | --- |
| Finite sums and reindexing | `MLIB-FINSET-SUMS`, `MLIB-FINTYPE-FIN` | regret decomposition, EXP3 weights, combinatorial actions |
| Order and positivity | `MLIB-ORDER-ALGEBRA`, `MLIB-REAL-LOG-SQRT` | UCB widths, KL-UCB, confidence radii, constraint budgets |
| Measurability and integrability | `MLIB-MEASURE-INTEGRAL`, `MLIB-PROBABILITY-KERNEL` | expected regret, Bayesian regret, contextual/RL kernels |
| Independence and conditioning | `MLIB-PROBABILITY-INDEPENDENCE`, `MLIB-CONDITIONAL-EXPECTATION` | Hoeffding routes, martingales, posterior identities |
| Martingale and stochastic-process APIs | `MLIB-MARTINGALE-STOCHASTIC`, `MLIB-CONDITIONAL-EXPECTATION` | self-normalized processes, delayed feedback, RL episode regret |
| Asymptotics | `MLIB-ASYMPTOTICS` | minimax rates, logarithmic regret exports |
| Linear/convex algebra | `MLIB-CONVEX-LINALG` | linear bandits, OFUL, convex action sets |
| Metric topology | `MLIB-METRIC-TOPOLOGY` | Lipschitz/continuum bandits, covering arguments, zooming-style routes |
| Tail inequalities | `MLIB-PROBABILITY-SUBGAUSSIAN`, `MLIB-PROBABILITY-MGF`, `MLIB-PROBABILITY-VARIANCE` | UCB/ETC tails, Chernoff routes, robust/heavy-tailed baselines |
| Tsallis/FTRL power algebra | `MLIB-REAL-RPOW-TSALLIS`, `MLIB-CONVEX-LINALG`, `MLIB-FINSET-SUMS` | Tsallis-INF, best-of-both-worlds, adaptive FTRL |

## Textbook Spine: Part IV Finite-Arm Lower Bounds

This source-faithful spine is separate from the ten-chapter teaching Book Map.
Its canonical source is Lattimore--Szepesvári (Cambridge University Press,
2020), Part IV, Chapters 13--17. A chapter advances only after source mapping,
Lean, evidence, site, review, and remote gates agree.

| Chapter | Current node | Evidence status | Boundary / next dependency |
| --- | --- | --- | --- |
| 13, Lower Bounds: Basic Ideas | explicit ENNReal minimax semantics; least-explored alternative averaging; quantitative two-environment algebra with an explicit pull-discrepancy error | local leaves compiled; chapter partial | Theorem 13.1 is only source-stated here and proved in Ch. 15; use the compiled Ch. 14 event-testing layer and the Ch. 15 history bridge when available |
| 14, Foundations of Information Theory | extended-real relative entropy, event-level binary data processing, endpoint-complete binary testing, unconditional Bretagnolle--Huber | scoped §14.2 leaves compiled; chapter partial | §14.1 coding and full Exercise 14.10 remain uncompiled; adaptive history KL belongs to Ch. 15 |
| 15, Minimax Lower Bounds | exact Lemma 15.1/Theorem 15.2 contracts; unit-Gaussian RN, exact arm KL, changed-arm cost, source gap and information-exponent tuning | Gaussian/numeric dependency leaves compiled; chapter partial and terminals blocked | prove the conditional composition-product KL integral and canonical stochastic-policy history law before Lemma 15.1 and the `1/27` terminal |
| 16, Instance-Dependent Lower Bounds | exact Definition 16.1 / Theorem 16.2 / Lemma 16.3 / Theorem 16.4 contracts; generic consistency, `d_inf`, Gaussian-candidate, eventual power, and eventual log-growth leaves | dependency slice compiled; chapter partial and terminals blocked | prove the Chapter 15 same-policy stochastic history KL bridge, exact Gaussian `d_inf`, and liminf extraction before the source terminals |
| 17, High-Probability Lower Bounds | source page map and navigation only | planned | freeze the exact event/probability quantifiers and horizon order before formalization |

The frozen source cards currently run through
`TXT-LS-2020-CH13-MINIMAL-SOURCE-CHANGE`, `TXT-LS-2020-THM-13-1`, the Chapter
14 relative-entropy/testing cards, and
`TXT-LS-2020-LEMMA-15-1-DIVERGENCE-DECOMPOSITION` /
`TXT-LS-2020-THM-15-2-GAUSSIAN-MINIMAX`, followed by the four Chapter 16
consistency/asymptotic/finite-time cards. The relevant Mathlib retrieval
surface includes finite sums, measure KL, Gaussian RN/first-moment APIs, and
filters, real powers/logarithms, complete-lattice infima, and the
composition-product chain rule. The missing conditional-KL integral is
recorded as a blocker; `WEAPON-KL-CHANGE-OF-MEASURE` remains inspiration-only.
No LML theorem card is treated as a local lower-bound proof.

## Compiled Local Leaves

The first dependency-light compiled leaf library is
`BanditRLProof.LeafLemmas`.  It currently exposes:

The canonical Chapter 9 terminal is now
`AdaptiveCumulativeHoeffdingUCBVI.recurrentSource_trajectoryMeasure_cumulativeEpisodePseudoRegret_gt_canonicalRegretBound_le`.
One strict-prefix recurrent source uses aggregate generated transition counts,
previous-Q clipping, same-law singleton Bernstein and optimal-tail confidence,
Bellman optimism, actual-count charge summation, and a generated-filtration
innovation tail to prove the frozen `20/250` UCBVI-CH bound. Its expectation
consumer retains `K*H*delta`. The natural-causal consistency and genuine
`hittingAfter` stopping routes remain separately compiled extensions rather
than aliases of this raw cumulative pseudo-regret theorem. Bernstein/minimax
and stochastic-reward UCBVI remain open milestones.

- `pullCount_one`;
- `pullCount_succ_of_eq`;
- `pullCount_succ_of_ne`;
- `pullCount_le_succ`;
- `pullCount_succ_le_succ`;
- `pullCount_mono`;
- `pullCount_le_time`;
- `pullCount_add_le`;
- `pullCount_le_add`;
- `pullCount_eq_zero_of_forall_ne`;
- `pullCount_eq_time_of_forall_eq`;
- `pullCount_pos_of_eq_before`;
- `pullCount_const_self`;
- `pullCount_const_of_ne`;
- `pullCount_add_eq_of_forall_ne_between`;
- `pullCount_add_eq_add_of_forall_eq_between`;
- `sumRewards_succ_of_eq`;
- `sumRewards_succ_of_ne`;
- `sumRewards_eq_zero_of_forall_ne`;
- `sumRewards_const_of_ne`;
- `sumRewards_add_eq_of_forall_ne_between`;
- `FiniteBanditModel.bestMean_eq_mean_bestArm`;
- `FiniteBanditModel.gap_bestArm`;
- `FiniteBanditModel.gap_of_ne_bestArm`;
- `pseudoRegret_one`;
- `pseudoRegret_succ_of_bestArm`;
- `pseudoRegret_succ_of_gap_zero`;
- `pseudoRegret_eq_zero_of_forall_bestArm`;
- `pseudoRegret_eq_zero_of_forall_gap_zero`;
- `pseudoRegret_const_bestArm`;
- `pseudoRegret_const_of_gap_zero`;
- `pseudoRegret_add_eq_of_forall_bestArm_between`;
- `pseudoRegret_add_eq_of_forall_gap_zero_between`.

The first compiled algorithm-wrapper leaves are:

- `ETC.exploreArm_eq_of_mod_eq`;
- `ETC.exploreArm_eq_iff_mod_eq_val`;
- `ETC.exploreArm_add_K`;
- `UCB.score_eq_empiricalMean`.

The first compiled ETC trace-boundary leaves are:

- `ETC.actionWithCommit`;
- `ETC.actionWithCommit_eq_exploreArm_of_lt`.
- `ETC.actionWithCommit_eq_commitArm_of_ge`.
- `ETC.actionWithCommit_eq_bestArm_of_commitArm_eq_bestArm_of_explorationPulls_mul_K_le`.
- `ETC.pullCount_actionWithCommit_eq_pullCount_exploreArm_of_le`.
- `ETC.pullCount_actionWithCommit_explorationPulls_mul_K_eq`.
- `ETC.pullCount_actionWithCommit_succ_eq_add_if_commitArm_of_ge`.
- `ETC.pullCount_actionWithCommit_explorationPulls_mul_K_add_eq`.
- `ETC.pullCount_actionWithCommit_explorationPulls_mul_K_add_eq_of_ne`.
- `ETC.pullCount_actionWithCommit_explorationPulls_mul_K_add_eq_commitArm`.
- `ETC.pseudoRegret_actionWithCommit_explorationPulls_mul_K_le_sum_gap_mul_explorationPulls`.
- `ETC.pseudoRegret_actionWithCommit_explorationPulls_mul_K_add_le_sum_gap_mul_suffix_count_budget`.
- `ETC.pseudoRegret_actionWithCommit_explorationPulls_mul_K_add_le_sum_gap_mul_explorationPulls_add_suffix`.
- `ETC.pseudoRegret_actionWithCommit_explorationPulls_mul_K_add_eq_add_suffix_gap`.
- `ETC.pseudoRegret_actionWithCommit_explorationPulls_mul_K_add_eq_of_commitArm_eq_bestArm`.
- `ETC.pseudoRegret_actionWithCommit_explorationPulls_mul_K_add_le_sum_gap_mul_explorationPulls_of_commitArm_eq_bestArm`.
- `ETC.pseudoRegret_actionWithCommit_explorationPulls_mul_K_add_le_sum_gap_mul_explorationPulls_add_suffix_gap`.

The first compiled Mathlib-backed finite wrappers are:

- `pullCount_eq_finset_filter_card`;
- `sumRewards_eq_finset_filter_sum`;
- `pseudoRegret_eq_finset_sum`.

The first compiled deterministic regret consumer is:

- `pseudoRegret_eq_finset_sum_gap_mul_pullCount`.
- `pseudoRegret_le_finset_sum_gap_mul_count_bound`.
- `pseudoRegret_le_finset_sum_gap_mul_nat_count_bound`.
- `pseudoRegret_le_sum_gap_mul_uniform_nat_count_bound`.

The first compiled deterministic finite-action count partition is:

- `finset_sum_pullCount_eq_time`.

The first compiled finite-bandit model invariant is:

- `FiniteBanditModel.gap_bestArm`.
- `FiniteBanditModel.mean_le_bestArm_mean`.
- `FiniteBanditModel.gap_nonneg`.

The first compiled scalar and probability-facing measurable/integral canaries
are:

- `ENNReal.ofReal_finset_sum_mul_natCast_of_nonneg`.
- `ENNReal.ofReal_pseudoRegret_eq_univ_sum_model_gap_ofReal_mul_natCast_pullCount_of_nonneg`.
- `measurableSet_actionTrace_eval_eq`.
- `measurable_actionTrace_eval_eq_indicator_const`.
- `measurable_actionTrace_eval_eq_indicator_reward`.
- `measurable_finset_sum_indicator_reward`.
- `measurable_sumRewards`.
- `measurable_pseudoRegret`.
- `measurable_pullCount`.
- `measurable_natCast_pullCount`.
- `lintegral_actionTrace_eval_eq_indicator_one`.
- `lintegral_finset_sum_actionTrace_eval_eq_indicator_one`.
- `lintegral_natCast_pullCount_eq_sum_measure_actionTrace_eval_eq`.
- `lintegral_finset_sum_gap_mul_natCast_pullCount_eq`.
- `lintegral_natCast_pullCount_le_time`.
- `lintegral_finset_sum_gap_mul_natCast_pullCount_le_sum_gap_mul_time`.
- `lintegral_univ_sum_gap_mul_natCast_pullCount_le_sum_gap_mul_time`.
- `lintegral_univ_sum_model_gap_ofReal_mul_natCast_pullCount_le_sum_model_gap_ofReal_mul_time`.
- `lintegral_ofReal_pseudoRegret_le_sum_model_gap_ofReal_mul_time_of_nonneg`.
- `lintegral_ofReal_pseudoRegret_le_sum_model_gap_ofReal_mul_time_of_rat_gap_nonneg`.
- `lintegral_ofReal_pseudoRegret_le_sum_model_gap_ofReal_mul_time`.

Future Mathlib-backed tasks should use these as local bridge lemmas, then
replace or generalize them with Mathlib APIs when the dependency layer is
selected.

## Algorithm Branches

The Book Map Chapter 5 canonical branch is now compiled through
`OFUL.finiteHistoryTelescopingScalarRidgeOptimisticAlgorithm`: Gram and
determinant geometry feed self-normalized ridge confidence, measurable
optimism, producer-backed all-time confidence, all-horizon regret, and bounded
plus square-integrable stopping consumers on the same horizon-free generated
policy.  The compiled expected-average consistency theorem belongs to a
separate horizon-indexed fixed-model family.  Contextual/dynamic or
infinite-dimensional OFUL and universal optional-stopping claims remain open.

The Chapter 6 canonical branch is compiled from posterior-kernel correctness
to actual recursive probability matching, clipped-score decomposition,
stationary latent-stream support, and the generated Bayesian-regret terminal.
`Thompson.IsOptimalMeanSelector` is now an explicit premise of that terminal;
the underlying decomposition alone remains comparator-relative.  Broader
posterior models, contextual/linear Thompson sampling, PSRL, sharp asymptotic
constants, and literal LML declaration identity remain separate.

| Branch | Immediate proof leaves | Source cards |
| --- | --- | --- |
| ETC | phase-splitting helper, deterministic ETC-only regret extension, commit argmax, wrong-commit probability, pull-count after commit | `TXT-LATTIMORE-SZEPESVARI-2020`, LML `Bandits.ETC.regret_le` |
| UCB | positive initial counts, index maximization, good-event pull bound, tail union, regret sum | `TXT-BUBECK-CESABIANCHI-2012`, `TXT-LATTIMORE-SZEPESVARI-2020`, `PPR-AUER-CBF-2002-UCB1`, LML `Bandits.UCB.regret_le` |
| KL-UCB | Bernoulli KL, confidence inversion, bounded stochastic reward contracts | `PPR-GARIVIER-CAPPE-2011-KLUCB`, `TXT-LATTIMORE-SZEPESVARI-2020` |
| Thompson sampling | compiled stationary posterior kernel, actual recursive probability matching, comparator decomposition plus explicit mean-optimality contract, clipped confidence, latent-stream support, generated Bayesian regret; broader model/toolchain ports remain open | `TXT-SLIVKINS-2019-2024`, `PPR-AGRAWAL-GOYAL-2011-TS`, LML cards `Bandits.TS.hasCondDistrib_action`, `Bandits.integral_regret_le` |
| EXP3/adversarial | canonical generated route compiled through potential/Hedge, importance-weighted conditional moments, measurable recursive sampling, exploration bias, tuned expected regret, per-horizon best-arm realized tails, a distinct fixed-process all-positive-prefix realized-regret terminal, and an explicit sparse-loss extension; horizon-free tuned EXP3, best-arm aggregation on that one fixed process, and EXP3.P remain extensions | `TXT-BUBECK-CESABIANCHI-2012`, `TXT-LATTIMORE-SZEPESVARI-2020`, `PPR-AUER-CFS-2002-EXP3` |
| Tsallis-INF/FTRL | canonical generated half-Tsallis route compiled through minimizer regularity, scheduled conditional action law, score alignment, expected stability/penalty, fixed-gap self-bounding, square-root schedule, and a finite-arm IID bounded reward-law logarithmic terminal; corruption, dynamic, and population-oracle restart results compile as labelled extensions, while the strict `Fin 2` refined-average obstruction and paper-sharp complete Tsallis-INF remain visible | `LOCAL-LEAF-TSALLIS-FINITE-BANDIT-MEAN-LOSS`, `LOCAL-LEAF-TSALLIS-SQRT-SCHEDULE-LOG-FIXED-GAP`, `LOCAL-LEAF-TSALLIS-SCHEDULED-FIXED-GAP-SELF-BOUNDING`, `LOCAL-LEAF-TSALLIS-SCHEDULED-EXPECTED-REGRET`, `LOCAL-LEAF-TSALLIS-SCHEDULED-ALL-RATE-EXPECTED-STABILITY`, `PPR-ZIMMERT-SELDIN-2018-TSALLIS-INF`, `PPR-MASOUDIAN-SELDIN-2021-TSALLIS-INF`, `PPR-ADAPTIVE-LR-FTRL-2024` |
| Linear/OFUL | compiled finite-action scalar route from Gram/determinant and confidence ellipsoid to a horizon-free all-time/all-horizon/stopping policy; horizon-indexed expectation/consistency is separate; contextual/dynamic/Hilbert extensions remain open | `TXT-LATTIMORE-SZEPESVARI-2020`, `PPR-ABBASI-YADKORI-2011-SELF-NORMALIZED`, `PPR-LI-CHU-LANGFORD-SCHAPIRE-2010-LINUCB` |
| Pure exploration | confidence event, stopping rule, sample complexity, lower-bound change-of-measure | `TXT-LATTIMORE-SZEPESVARI-2020`, `TXT-SLIVKINS-2019-2024` |
| BwK/resource constraints | budget stopping time, resource consumption, primal-dual comparison | `TXT-SLIVKINS-2019-2024`, `PPR-BADANIDIYURU-KLEINBERG-SLIVKINS-2013-BWK` |
| Dueling/preference | pairwise preference, Borda/Condorcet winner notions, comparison regret | `PPR-IJCAI-2018-DUELING-SURVEY` |
| Safe/fair/private | baseline feasibility, safe set, privacy composition, fairness invariant | `PPR-AAAI-2020-SAFE-LINEAR-STOCHASTIC`, `PPR-AAAI-2016-DP-MAB`, `PPR-FAT-2018-MERITOCRATIC-FAIRNESS` |
| Federated/neural | client traces, aggregation invariant, communication regret, neural confidence surrogate | `PPR-AAAI-2021-FEDERATED-MAB`, `PPR-FEDERATED-NEURAL-BANDITS-2022` |
| Finite-horizon RL/MDP | finite kernels, Bellman recursion, occupancy measures, episode regret, optimism | `TXT-SLIVKINS-2019-2024`, `PPR-AZAR-OSBAND-MUNOS-2017-UCBVI`, scenario card `SCN-RL-MDP` |

## Scenario Frontier

The active scenario atlas now includes finite stochastic, Bayesian posterior,
adversarial, best-of-both-worlds/adaptive, contextual, linear/GLM,
Lipschitz/metric, pure exploration, combinatorial, resource-constrained,
dueling/preference, nonstationary, heavy-tailed/robust, delayed/batched,
safe/fair/private, federated/distributed, finite-horizon RL/MDP, and
neural/LLM recommender bandits.

Watchlist scenarios may still be theorem-card-only.  They should not be used as
Lean proof targets until a source card, local API, and Mathlib retrieval route
are recorded.

The machine-readable route atlas is `lean-route-roadmap.json`.  It is the
handoff contract between upper planning agents and lower Lean agents: each
route records the compiled local core, missing Mathlib-grade leaves, intended
proof route, regularity contracts, reviewer gates, and export target.  Human
readers should use the PNG route diagrams in `docs/assets/` and the detailed
roadmap in `docs/full_lean_tree_roadmap.md`; agents should load the JSON.

## Expansion Policy

When adding a theorem:

1. attach it to a scenario card;
2. choose the textbook/paper/LML source card;
3. search Mathlib retrieval cards for each general leaf;
4. search local declarations with `list-lean-decls`;
5. make hidden regularity explicit;
6. write one proof-obligation row per lower-agent leaf;
7. keep failed attempts in memory with the mathematical diagnosis;
8. render or update the route diagram when the dependency shape changes;
9. export the compiled theorem to Markdown and LaTeX only after Lean closure.

The tree is intentionally larger than the current Lean package.  Branches
without compiled local declarations remain theorem-card, cited-result, or
open-problem memory until a task imports, ports, or proves the needed lemmas.

## 2026-07-22 Scheduled Tsallis Route Update

`LOCAL-LEAF-TSALLIS-SCHEDULED-RECURSIVE-TRAJECTORY` now compiles the
time-varying generated selector, recursive score, policy/trajectory kernels,
and successor conditional action laws. It consumes the canonical selector and
deterministic time-varying penalty layers. The next edge toward
`TSALLIS-REFINED-SUBOPTIMAL-STABILITY-PENALTY` now also compiles as
`LOCAL-LEAF-TSALLIS-SCHEDULED-SCORE-PENALTY-ALIGNMENT`: observed-IW scores
match `FTRL.cumulativeLoss`, and generated best-arm estimated regret is
decomposed pathwise into same-rate stability plus scheduled penalty. The next
edge now also compiles as
`LOCAL-LEAF-TSALLIS-SCHEDULED-SUCCESSOR-EXPECTED-STABILITY`: every actual
successor term is transported through the scheduled conditional action law and
summed against its local refined budget. The next edge now also compiles as
`LOCAL-LEAF-TSALLIS-SCHEDULED-INITIAL-EXPECTED-STABILITY`: the exact pathwise
time-zero term is transported through the canonical initial action law and
bounded by its initial refined budget. The next edge is their finite-sum
assembly, which now compiles as
`LOCAL-LEAF-TSALLIS-SCHEDULED-ALL-TIMES-EXPECTED-STABILITY`: the exact
`Finset.range (horizon + 1)` pathwise stability sum is integrable and bounded
by the initial plus successor refined budgets. Early-large-rate handling and
expected stability-plus-penalty integration remain independent next edges.

`LOCAL-LEAF-TSALLIS-SCHEDULED-ALL-RATE-EXPECTED-STABILITY` now closes the
early-large-rate edge. A deterministic ordinary-IW producer proves the coarse
constant-one budget for every positive local rate; generic finite-action
integrability and `condDistrib` transport feed generated initial and successor
wrappers, and the final exact all-times theorem selects refined versus coarse
at each actual time. The generated expected-regret edge now compiles, and
`LOCAL-LEAF-TSALLIS-SCHEDULED-SUBOPTIMAL-EXPECTED-BOUND` closes the next
small-rate edge: expected scheduled probabilities form a finite simplex,
concave Jensen transports square roots, the best-arm term is eliminated, and
the result feeds the abstract self-bounding completion-of-squares theorem.
`LOCAL-LEAF-TSALLIS-SCHEDULED-FIXED-GAP-SELF-BOUNDING` now supplies that
self-bound from an exact predictable fixed-gap law: pathwise regret equals
suboptimal gap mass, finite integral exchange yields
`sum_t sum_{a != best} gap(a) E[p_t(a)]`, and the final regret theorem is
automatic for nonnegative corruption. Reward-kernel/mean-law transport and
schedule tuning remain open; final Tsallis-INF regret is not yet proved.

## 2026-07-23 Finite-Arm IID Reward-Law Update

`LOCAL-LEAF-TSALLIS-FINITE-ARM-IID-REWARD-LAW-REGRET` now consumes the
scheduled IID mean-gap route. Mathlib's finite product measure packages one
bounded rational reward law per arm; clipping reconciles the abstract
pointwise loss bound with the natural a.e. reward-support contract; Pi-coordinate
integrals identify the resulting loss mean gaps with
`FiniteBanditModel.gap`. The generated square-root scheduled half-Tsallis
theorem therefore reaches its explicit logarithmic model-gap endpoint for an
IID independent reward-vector process. A generated corruption process and its
additive self-bounding allowance remain the next theorem-route edge.

## 2026-07-23 Stationary Corrupted IID Reward-Law Update

`LOCAL-LEAF-TSALLIS-FINITE-ARM-IID-STATIONARY-CORRUPTED-REWARD-LAW-REGRET`
now consumes the finite-arm IID reward-law endpoint. A fixed reward shift per
arm is projected back to the unit interval; Mathlib's projection contraction
bounds actual mean-gap drift, and the perturbed expected-gap consumer turns
that drift into an explicit finite-horizon self-bounding allowance. The final
scheduled half-Tsallis theorem is baseline-model-facing and has no free
corruption scalar. The deterministic time-indexed edge now compiles through a
time-varying expected-gap contract and an IID prefix-law producer. Its final
budget is the explicit sum over rounds and non-best arms of the two affected
shift magnitudes, and constant schedules recover the stationary theorem.
The past-measurable history-adaptive edge now compiles as described below. It
still does not prove current-action or latent-law corruption and therefore is
not the full adaptive corrupted-stochastic paper theorem.

## 2026-07-23 History-Adaptive Corruption Update

The next edge now compiles in three layers. The generic reference-gap bridge
compares two predictable losses on the same actual trajectory measure. The
IID history-adaptive prefix layer proves that pre-action-history dependence is
compatible with finite state-prefix factorization when only the current IID
state coordinate is read. The concrete finite-arm source combines these with
clipped additive shifts and a deterministic envelope, proving the baseline
scheduled half-Tsallis logarithmic bound plus the exact envelope budget.

This edge remains below the full paper-level corruption node. Current-action
corruption, latent reward-kernel changes, or envelope control available only
conditionally or in expectation require a new filtration-aware law producer.

## 2026-07-23 Improved Self-Bounding Interpolation Update

The Tsallis branch now contains the terminal lambda-interpolation edge from
Masoudian--Seldin's equation `upperfull`. The compiled edge combines the
generated scheduled square-root expected-probability upper bound with a
single horizon-`T` `(Delta,C,T)` self-bound and leaves a deterministic finite
optimization problem. It intentionally stops before the simplex-constrained
one-step maximization, threshold decomposition, and joint lambda choice that
produce the sharper corruption dependence.

## 2026-07-23 Constrained Quadratic Optimization Update

`LOCAL-LEAF-TSALLIS-CONSTRAINED-QUADRATIC-OPTIMIZATION` now closes the
one-step maximization edge. Positive quadratic coefficients give both the
coordinatewise vertex bound and the active common-mass bound. A Mathlib
Cauchy--Schwarz square-root-sum theorem transports finite-simplex mass to
`sum sqrt(p_a) <= sqrt(K-1)`, and the result is instantiated for generated
scheduled expected action probabilities with coefficients
`c_a=lambda*gap(a)`.

Strict positivity of `lambda` and every suboptimal gap, best-arm membership,
nonempty suboptimal arms for the active branch, and the exact threshold remain
explicit contracts. The next edge is the finite-time threshold split and
summation. Joint `lambda` optimization and the improved corruption endpoint
are still open.

## 2026-07-23 Square-Root Self-Bounding Optimization Update

`LOCAL-LEAF-TSALLIS-SQRT-SCHEDULE-SELF-BOUNDING-OPTIMIZATION` now closes the
finite-time split and summation edge. The refined generated stability/penalty
bound is split at the exact constrained-quadratic threshold, a scalar cutoff
makes the active times a prefix, and the concrete schedule reduces the two
branches to inverse-square-root and harmonic sums. Mathlib integral comparison
then yields an explicit `sqrt(cutoff)` active term and
`log((T+1)/cutoff)` tail.

Positive gaps, `lambda in (0,1]`, a nonempty suboptimal set, a positive cutoff
bounded by `T+1`, its threshold certificate, and the terminal self-bound are
all retained. The next edge is discrete cutoff construction followed by joint
`lambda` and corruption optimization. The final improved paper theorem remains
open.

## 2026-07-23 Floor Cutoff and General Corruption Update

`LOCAL-LEAF-TSALLIS-SQRT-SCHEDULE-SELF-BOUNDING-FLOOR-TUNING` closes the
discrete cutoff edge. The continuous quadratic threshold is replaced by its
natural floor using a compiled factor-two sandwich, so positivity, active
threshold, and horizon membership no longer remain caller-level cutoff
obligations. At `lambda=1`, the threshold is identified with
`25*S^2/(K-1)` and the generated theorem reaches an explicit
`C+S*log((T+1)(K-1)/S^2)`-shape bound with local constants.

The theorem tree forks at the scalar optimizer. The general corruption branch
is locally proved in the large-horizon regime, and a coefficient-aware refined
branch now also compiles without Lambert W. It uses an elementary log/sqrt
estimate instead of the Masoudian--Seldin negative Lambert branch.

The stochastic process-law branch now also contains
`TSALLIS-SCHEDULED-INDEPENDENT-NONIDENTICAL-MEAN-GAP`. It replaces the common
IID coordinate law by `law : Nat -> Measure LossState`, reuses the generated
trajectory's finite-prefix factorization, and proves the exact per-time
independence and marginal gap under `Measure.infinitePi law`. This closes
independent nonstationary latent states but not history-dependent or
conditional-kernel reward laws.

`LOCAL-LEAF-TSALLIS-SELF-BOUNDING-BETA-ROOT` retains the paper's ideal `-1`
equation as route evidence. The compiled
`LOCAL-LEAF-TSALLIS-SQRT-SCHEDULE-SELF-BOUNDING-REFINED-TUNING` audit instead
derives the locally valid `-2` equation and factor `25`, proves a quantitative
root-weight estimate, transports alpha/lambda and the exact threshold, and
closes the generated local `sqrt(C*S)` endpoint.

`LOCAL-LEAF-TSALLIS-FINITE-ARM-IID-HISTORY-ADAPTIVE-REFINED-CORRUPTED-REWARD-LAW-REGRET`
now supplies a concrete model-level consumer. It reconstructs the actual
history-adaptive trajectory, proves the uncorrupted reference model-gap law on
that measure, exposes the deterministic envelope-budget self-bound, and feeds
it to refined tuning. The branch no longer has a free corruption scalar or
caller-supplied law transport. A generic compact-window theorem and a
model-facing `_of_window` wrapper now derive budget positivity and all four
low-level scalar bounds from three natural window clauses and gaps in `(0,1]`.
`LOCAL-LEAF-TSALLIS-FINITE-ARM-IID-UNIFORM-SUBOPTIMAL-BOOST-REFINED-REGRET`
closes the first concrete envelope branch: exact budget
`(T+1)*k*epsilon`, compact-window transport from `epsilon*S<=1`, and the final
explicit refined model theorem. A named regime and total bound now select that
branch when valid and otherwise reuse the logarithmic `+C` theorem, closing
zero/small corruption for every nonnegative `epsilon` in this family.
`TSALLIS-FINITE-ARM-IID-ARM-DEPENDENT-SUBOPTIMAL-BOOST-ALL-REGIMES` generalizes
this to pointwise nonnegative stationary boosts, forces the best-arm shift to
zero, proves exact budget `(T+1) * sum_(a != best) boost(a)`, and exposes the
same refined/logarithmic total theorem.
`TSALLIS-FINITE-ARM-IID-TIME-VARYING-SUBOPTIMAL-BOOST-ALL-REGIMES` further
allows pointwise nonnegative deterministic `boost(t,a)` and proves the exact
double finite-sum budget `sum_(t<T+1) sum_(a!=best) boost(t,a)`.
`TSALLIS-FINITE-ARM-IID-PREVIOUS-ACTION-GATED-SUBOPTIMAL-BOOST-ALL-REGIMES`
then consumes that envelope with a source whose successor shift reads the
previous sampled action and activates only on a fixed trigger arm.
`TSALLIS-FINITE-ARM-IID-MEASURABLE-HISTORY-ARM-GATED-SUBOPTIMAL-BOOST-ALL-REGIMES`
generalizes this to every measurable event on finite pair history times the
candidate arm plus an arbitrary time-zero arm gate, including measurable past
observed clipped-feedback/loss-coordinate gates. It does not expose current,
raw, or latent reward-vector coordinates. Remaining forks are realized/expected gate-open budgets, current-action or latent-law
corruption, stronger corruption models, and paper-sharp constants.

`TSALLIS-FINITE-ARM-IID-HISTORY-ADAPTIVE-EXPECTED-CORRUPTION-ALL-REGIMES`
closes the first remaining fork. It replaces the deterministic schedule charge
by the exact generated-policy finite sum of integrals
`p_t(a) * (|shift_t(a)| + |shift_t(best)|)`, proves this scalar nonnegative and
bounded by the envelope budget, and reuses the refined/log all-regimes split.
The refined branch is selected only when a suboptimal arm exists and its window
holds; all other cases use the logarithmic branch. The measurable history-arm
gate is a direct consumer, and `Fin 1` simplifies to `1 + log(T+1)`. The route
still excludes current-action/nonpredictable and raw/latent-law corruption,
paper-sharp constants, and complete Tsallis-INF.

`TSALLIS-FINITE-ARM-IID-HORIZON-HISTORY-ADAPTIVE-EXPECTED-CORRUPTION-ALL-REGIMES`
closes the horizon-local contract fork. Initial data plus `Fin horizon`
successor shifts, joint history-arm measurability, and envelope witnesses are
extended by zero after the target horizon. The generated law and exact
policy-weighted expected-corruption budget are unchanged on every summed
round, so the existing refined/log endpoint applies without post-horizon
regularity. Both `horizon=0` and `K=1` remain covered. Current-action or other
nonpredictable corruption and raw/latent reward-law transport are still
separate theorem routes.

## Nonidentical Finite-Arm Reward-Law Branch

`TSALLIS-FINITE-ARM-NONIDENTICAL-REWARD-LAW-REGRET` closes the route
`armLaw(t,a)` -> roundwise `Measure.pi` -> cross-round
`Measure.infinitePi` -> canonical trajectory prefix factorization ->
time-varying independent mean-gap law -> exact fixed `model.gap` law ->
logarithmic reciprocal-gap regret.

The per-time arm distributions may differ, but every arm keeps the same model
mean. Conditional, history-dependent, dependent-arm, and drifting-mean
reward laws remain separate branches.

`TSALLIS-FINITE-ARM-NONIDENTICAL-DRIFTING-MEAN-REWARD-LAW-REGRET` now closes
the next generated-policy branch in
`TsallisFiniteArmIndependentDriftingMeanRewardLaw`. It replaces exact
roundwise model means by an armwise absolute mean-deviation envelope, proves
the actual product-law loss gap differs from the fixed model gap by at most
the current-arm plus best-arm deviations, and feeds that result through the
compiled time-varying expected-gap self-bound. The logarithmic theorem is
static-comparator regret against fixed `model.bestArm` and has no free
corruption scalar: its additive term is exactly the
inclusive-horizon double finite sum of the two deviations over non-best arms.
Its actual-mean dynamic-comparator consumer now compiles downstream.

`TSALLIS-FINITE-ARM-NONIDENTICAL-DRIFTING-MEAN-REFINED-REGRET` now compiles
the next theorem on this branch in
`TsallisFiniteArmIndependentDriftingMeanRefinedRegret`. The parent law leaf
exposes its generated terminal self-bound, with corruption equal to the
explicit inclusive-horizon mean-deviation budget. The new theorem specializes
the coefficient-aware `RefinedLocalCorruptionWindow`, derives the scalar
optimizer premises from non-best gaps in `(0,1]`, and obtains the local
`1 + log(T+1) + 10*sqrt(C*S)*(2+sqrt(log(2*(K-1)*(T+1)/(C*S))+1))`
bound. The comparator here is fixed `model.bestArm` and the theorem is
window-conditional. No new probability-law assumptions are introduced beyond
the parent independent nonidentical construction; all-regimes and dynamic
consumers compile downstream.

`TSALLIS-FINITE-ARM-NONIDENTICAL-DRIFTING-MEAN-ALL-REGIMES` closes the
window-composition branch in
`TsallisFiniteArmIndependentDriftingMeanAllRegimes`. Its total envelope first
checks that a non-best arm exists and that the explicit-budget refined window
holds; it uses the compiled `sqrt(C*S)` expression there and the logarithmic
reciprocal-gap-plus-budget expression otherwise. The final generated theorem
has no caller `hwindow` or `hsuboptimal` premise, and `Fin 1` simplifies to
`1 + log(T+1)`. This fixed-comparator result supplies the baseline component
of the dynamic theorem below.

`TSALLIS-FINITE-ARM-NONIDENTICAL-DRIFTING-MEAN-DYNAMIC-REGRET-ALL-REGIMES`
now compiles in `TsallisFiniteArmIndependentDriftingMeanDynamicRegret`.
A finite argmax selects an arm maximizing the actual reward mean at every
round. The moving-comparator regret integral decomposes exactly into the fixed
`model.bestArm` regret plus cumulative actual-mean advantage; baseline model
optimality and the armwise deviation envelope bound that advantage. The final
generated theorem is for expected predictable-environment regret, not realized
sample-path regret, and adds this explicit dynamic-comparator penalty to the fixed
all-regimes bound, requires no caller comparator/max/window/nonempty proof,
and keeps the `Fin 1` value `1 + log(T+1)`. Its cumulative actual-mean
path-variation specialization now compiles downstream.

`TSALLIS-FINITE-ARM-NONIDENTICAL-PATH-VARIATION-DYNAMIC-REGRET-ALL-REGIMES`
now compiles in
`TsallisFiniteArmIndependentPathVariationDynamicRegret`. The exact armwise
sum of consecutive actual-mean increments controls displacement from the
round-zero mean by induction. Initial actual/model mean equality therefore
removes the caller-supplied all-time deviation family from the generated
dynamic-regret endpoint. This closes the law-derived cumulative-envelope
route, not a horizon-compressed or minimax-sharp standard `V_T`, switch-count,
realized sample-path, conditional/history-dependent, dependent-law, or
complete Tsallis-INF theorem. Its per-arm population-mean switch-count
specialization now compiles downstream.

`TSALLIS-FINITE-ARM-NONIDENTICAL-MEAN-SWITCH-COUNT-DYNAMIC-REGRET-ALL-REGIMES`
now compiles in
`TsallisFiniteArmIndependentMeanSwitchCountDynamicRegret`. Probability mass
one and a.e. unit support place every actual arm mean in `[0,1]`, so each
nonzero consecutive mean jump is at most one. The resulting zero-or-one
prefix sum is identified exactly with the real coercion of the filtered
cardinality of changed rounds and dominates the cumulative path variation.
Initial actual/model mean matching then gives the generated expected
moving-comparator dynamic-regret theorem with no caller variation family or
switch budget. This closes the per-arm prefix population-mean count route,
not a global change-point/minimax switch-rate, compressed standard `V_T`,
observable/sample count, realized sample-path, conditional/dependent-law, or
complete Tsallis-INF theorem.

`TSALLIS-FINITE-ARM-NONIDENTICAL-GLOBAL-MEAN-SWITCH-COUNT-DYNAMIC-REGRET-ALL-REGIMES`
now compiles in
`TsallisFiniteArmIndependentGlobalMeanSwitchCountDynamicRegret`. One
zero-or-one prefix indicator records whether any arm's population mean
changes between consecutive rounds. Its sum is exactly the coerced
cardinality of changed rounds and dominates every armwise switch count, so
the existing path and initial-model-match adapters generate the parent
all-time envelope without caller count data. This closes the exact global
prefix population-mean change-point route, not a minimax or
horizon-compressed switch-rate/standard `V_T`, observable sample count,
realized sample-path, conditional/dependent-law, or complete Tsallis-INF
theorem.

`TSALLIS-FINITE-ARM-NONIDENTICAL-GLOBAL-MEAN-SWITCH-COUNT-HORIZON-COMPRESSED-LOG-DYNAMIC-REGRET`
now compiles in
`TsallisFiniteArmIndependentGlobalMeanSwitchCountCompressedDynamicRegret`.
Global count monotonicity compresses both the fixed mean-deviation budget and
moving-comparator penalty to one terminal count, producing the generated
logarithmic dynamic-regret bound with additive
`4*(K-1)*(T+1)*globalCount(T)`, excluding the post-horizon transition. The
erased-arm factor preserves the exact
`Fin 1` endpoint. This closes the linear horizon-level compression only; a
minimax/sublinear switch-rate or sharp standard variation-budget theorem
remains a separate route.

`TSALLIS-FINITE-ARM-NONIDENTICAL-SINGLE-SWITCH-DYNAMIC-COMPARATOR-ADVANTAGE-OBSTRUCTION`
now compiles in
`TsallisFiniteArmIndependentSingleSwitchComparatorObstruction`. Its exact
two-arm one-switch law has terminal global count one but comparator advantage
`T/4` and current repeated-prefix penalty `2*T`. The square-horizon witness
beats every fixed natural multiple of `sqrt(T)`. This closes the diagnostic
route only: it rules out independently bounding the comparator-advantage
summand to get `sqrt(S*T)`, but does not establish a regret lower bound.
The deterministic oracle-restart finite-sum assembly now compiles downstream.

`TSALLIS-ORACLE-RESTART-EPOCH-DYNAMIC-REGRET-ASSEMBLY` now compiles in
`TsallisOracleRestartDynamicRegret`. It partitions the inclusive horizon into
finite epoch fibers, identifies moving-comparator regret with the exact sum of
epoch regrets, and applies finite Cauchy--Schwarz to derive
`C*sqrt(numberEpochs)*sqrt(T+1)`. With at most `switches+1` epochs, the
compiled endpoint is `C*sqrt(switches+1)*sqrt(T+1)`.

`TSALLIS-ORACLE-RESTART-GENERATED-TRAJECTORY-ACTION-LAW` now compiles in
`TsallisOracleRestartGeneratedTrajectory`. The generated policy resets to the
initial half-Tsallis law at each scheduled boundary and otherwise reads only
the measurably reindexed inclusive suffix of the current epoch. The canonical
trajectory kernel, actual-time probability surface, never-restart and
restart-every-round reductions, and successor conditional-action law are
compiled.

`TSALLIS-ORACLE-RESTART-PREDICTABLE-DYNAMIC-REGRET-ASSEMBLY` now compiles in
`TsallisOracleRestartPredictableRegret`. Its fixed and moving regret surfaces
use the generated restart probability directly. The epoch registry is the
image of `schedule.start` over the inclusive horizon, so coverage and exact
fiber decomposition require no independent `epochOf` compatibility premise.
Pointwise epoch certificates yield the schedule-epoch and switch-count
square-root endpoints; never-restart and fixed-plus-moving compatibility also
compile.

`TSALLIS-ORACLE-RESTART-EPOCH-LOCAL-FIXED-COMPARATOR-REGRET-TRANSPORT` now
compiles in `TsallisOracleRestartExpectedRegret`. The successor action law
retains environment plus global prefix, importance-weighted first moments
hold on the actual generated trajectory, and estimated/environment regret
have equal integrals on every schedule fiber. Point masses identify the
existing epoch regret. Stored-reward estimators agree almost everywhere with
the predictable estimators at each global time and epoch, so observed
point-mass epoch integrals and observed certificate consumers now compile as
well. Either certificate surface assembles into the schedule-epoch and
switch-count square-root bounds without fresh-run independence.

The pathwise successor
`TSALLIS-ORACLE-RESTART-EPOCH-LOCAL-SCORE-ALIGNMENT` now compiles. It shifts
the actual path to local time, aligns probabilities and stored-reward scores,
proves visited fibers are contiguous translated ranges with exact
cardinality, and transports the scheduled time-varying FTRL
stability-plus-penalty certificate to actual observed epoch regret. The route
uses schedule monotonicity/idempotence and finite-sum reindexing; it assumes
only finite nonempty decidable arms, valid schedule, visited epoch, comparator
membership, and positive nonincreasing local eta. External canaries,
independent review, and baseline public-import axiom audit pass.

The expected transport successor
`TSALLIS-ORACLE-RESTART-EPOCH-LOCAL-EXPECTED-STABILITY-TRANSPORT` now also
compiles. It uses the environment-plus-global-prefix conditional action law
of the single generated restart trajectory, covers coarse and refined
successor bounds plus global time zero, and keeps finite-prior one-round
constants mass-scaled. Under a probability prior it sums a contiguous local
prefix to its cardinality and integrates the actual observed epoch FTRL
certificate, producing a linear-cardinality expected bound plus deterministic
penalty without any fresh shifted-epoch law.

The theory-tree successors below close refined finite-sum/local-rate tuning and
then the generated moving-comparator consumer under the same global law. A
law-derived bound on schedule epoch count remains separate; concentration is
not used on this route.

The next successor
`TSALLIS-ORACLE-RESTART-EPOCH-LOCAL-REFINED-STABILITY-TUNING` now compiles.
Finite-simplex square-root mass controls every refined successor; the concrete
inverse-square-root schedule yields a `4*sqrt(K)*sqrt(length)` stability
prefix; and the point-mass potential penalty yields another factor four.
Every visited actual epoch therefore exposes the assembly-ready certificate
`E[observed estimated regret] <=
(8*sqrt(K))*sqrt(epochRounds.card)` under the one global law.

This closes the local analytic edge into the generic restart assembly.

The concrete generated consumer
`TSALLIS-ORACLE-RESTART-GENERATED-DYNAMIC-REGRET` now also compiles. It proves
the schedule-cardinality endpoint
`8*sqrt(K)*sqrt(scheduleEpochs.card)*sqrt(T+1)` and, under the explicit epoch
count contract, the switch-facing endpoint
`8*sqrt(K)*sqrt(switches+1)*sqrt(T+1)`. It retains the one global trajectory
law and uses the observed-to-predictable transport already compiled upstream.

Law-derived control of the epoch registry and construction of a concrete
restart policy remain the next distinct successor; complete Tsallis-INF and
constant optimization are not claimed.

That successor now compiles as
`TSALLIS-ORACLE-RESTART-GLOBAL-MEAN-SWITCH-COUNT-DYNAMIC-REGRET`. The exact
change-point schedule restarts after every global population-mean change,
has `S_T+1` epochs, and preserves an epoch-start mean maximizer throughout the
epoch. Under a.e. `[0,1]` support, a compiled loss-gap bridge shows that this
comparator is also optimal for the clipped loss. The concrete independent-law
generated theorem therefore gives
`8*sqrt(K)*sqrt(S_T+1)*sqrt(T+1)`.

This closes the full-information population-mean oracle branch under that
unit-support contract. An
observed-reward detector would require a different random/history-dependent
schedule interface plus concentration-based delay and false-alarm control;
that route and complete Tsallis-INF remain open.

## Canonical Conditional Reward Foundation

The `COND-EXPECT-REWARD` branch now has a compiled canonical endpoint over the
reward-only `historyStepKernelFamily` `trajMeasure`. The route composes the
generated finite-history conditional reward law, centered kernel MGF,
MGF-derived integrability, conditional expectation zero, strong adaptedness,
and the finite-sum ENNReal Azuma-Hoeffding upper tail.

This closes the canonical trajectory foundation only. Arbitrary ambient-law
transport, uniform-time concentration, arm-wise empirical means, and complete
UCB/ETC/RL theorem routes remain downstream branches.

## OFUL Elliptical-Potential Branch

The deterministic OFUL branch now terminates in
`OFUL.standardLogDeterminantAndEllipticalPotential`, which combines the
standard logarithmic terminal determinant bound with the clipped
inverse-quadratic finite-sum bound. The compiled route includes regularized
Gram PosDef, rank-one determinant updates, log-det telescoping, trace/eigenvalue
AM-GM, and scalar logarithmic simplification.

The vector self-normalized concentration route, finite-horizon least-squares
confidence ellipsoid, scalar regularization bias, finite-action optimism,
measurable strict-fold selection, concrete finite-history ridge state,
finite-window confidence, and selected-width summation now compile.
`BanditRLProof.OFULAllTimeConfidence` additionally forms one countable
failure event for one fixed process and proves simultaneous confidence at
every deterministic horizon under the exact telescoping schedule
`delta/((n+1)*(n+2))`. Its proof uses Mathlib countable outer-measure
subadditivity and an exact Real-to-ENNReal reciprocal telescope. It is not a
stopping-time theorem and does not turn the current horizon-dependent
generated algorithm family into one anytime policy.

`BanditRLProof.OFULScheduledAllTimeConfidence` now defines the separate
one-policy route. Its history-index `n` selector uses the telescoping budget at
`n+1`, so the generated successor score and fixed-time confidence event share
the same level. The module compiles strict-fold measurability, scheduled
predictable feature/residual regularity, simultaneous actual-feature
transport, one generated countable confidence tail, and the event that there
exists a successor round violating the matching two-times-bonus optimism
certificate. Both generated events have measure at most `ofReal delta` under
an explicit all-time scheduled residual-law source.

`BanditRLProof.OFULGeneratedTrajectoryConfidenceGap` additionally identifies
the inclusive history state at `n` with the generic state at horizon `n+1`
and sums the concrete successor-action true gap over rounds `1..horizon`
conditional on the uniform-confidence good event. It consumes the strict-fold
score maximum directly and does not equate it with `Classical.choose`.

`BanditRLProof.OFULGeneratedTrajectoryUniformConfidence` now packages those
contracts as `OFUL.CanonicalScalarRidgeConfidenceSource`, specializes the
uniform failure probability to the canonical measure, and proves that the
strict successor-gap violation event has measure at most `ofReal delta`.
This closes the high-probability consumer under an explicit source.

`BanditRLProof.OFULGeneratedTrajectoryPredictableConfidence` now specializes
that source through a strict-past `Filtration.piLE` process. It constructs the
measurable predictable scalar-ridge feature, proves simultaneous all-time a.e.
alignment with the actual selected feature, derives the observed-response
residual adaptedness, response identity, and finite-action projection bound,
and transports both confidence and successor-gap events back to actual
features. Its reduced source retains only theta norm and horizon-local residual
conditional-MGF witnesses; it does not require `Countable Real`.

The concrete initial/feedback-kernel law, normalized radius-times-width
control, fixed initial round, explicit finite-window high-probability
fixed-optimal-arm pseudo-regret rate, bad-event integration, finite-window
expected pseudo-regret, explicit expected rate, and fixed-model asymptotic
expected-rate consumers now compile downstream. The fixed-model
horizon-indexed expected-average pseudo-regret is also proved to tend to zero.
Arbitrary `HistoryEnvironment` values still do not imply a centered MGF law,
but the scheduled kernel-to-conditional-MGF producer now compiles under
`CanonicalLinearSubgaussianEnvironmentLaw`. Reusable algorithm-parametric
initial/successor canonical reward bridges, the scheduled history-step
marginal, and the resulting
`CanonicalScheduledPredictableScalarRidgeResidualLaw` constructor reach direct
environment-backed all-time confidence and existential successor-gap tails on
the same one-policy trajectory measure.

The next all-time branch is an all-horizon cumulative-gap tail obtained by
combining the simultaneous per-round certificates with deterministic
radius-width summation. Stopping-time evaluation remains a subsequent,
separately stated theorem.

The scheduled stopping branch now has a concrete forced-schedule producer.
A generic measurable finite-history selector can be packaged as a deterministic
`HistoryAlgorithm`, and its canonical successor action lies on the selector
graph almost surely. The OFUL specialization selects
`forcedAction (n/window)` when `n%window=0` and otherwise retains the
telescoping strict-fold optimistic action. Hence generated action
`b*window+1` is `forcedAction b` almost surely. Under `2<=window`, this action
belongs to the aligned half-open block and positive forced-arm Nat costs yield
`Budget.AlignedWindowPositiveActionCostAE` under the modified algorithm's own
canonical law. This closes the schedule producer that the previous conditional
theorem assumed. It does not preserve the ordinary OFUL regret proof
definitionally: the next branch must identify non-forced rounds with the
optimistic selector, split pseudo-regret into forced and optimistic sums, and
charge forced rounds explicitly before confidence/width and budget terminals
can be transported. No primal-dual or full BwK comparison is claimed.

## OFUL Fixed-Direction Concentration Edge

`OFUL.fixedDirectionCompensatedScore_hasMGFUpperBoundAt` now compiles the
deterministic-horizon fixed-direction edge of the self-normalized route.
Predictable projections are frozen in the conditional kernel, boundedness
supplies exponential integrability, and the local conditional-MGF composition
API yields the finite compensated sum certificate. For common paper scale
`R`, use proxy `R^2` and Lean direction `lambda/R`.

The branch now contains the multivariate Gaussian mixture identity, joint
measurability and Tonelli transport, score/Gram identification, evaluated
mixture, Markov event bound, common-`R` vector tail, finite-horizon ridge
confidence ellipsoid, scalar bias simplification, finite-window confidence,
optimism, concrete measurable history selection, successor good-event gap
transport, an explicit-source canonical `delta` tail, and its strict-past
predictable-residual specialization. Concrete feedback-kernel-to-residual-MGF
construction, normalized radius/width control, initial-round accounting, the
explicit finite-window `delta/(T+1)` high-probability pseudo-regret rate,
bad-event expectation integration, finite-window expected pseudo-regret, its
explicit rate, and the fixed-model `O(sqrt(T+1)*log(T+1))` expected-regret
corollary also compile. Its little-o consumer proves that complete expected
pseudo-regret divided by `T+1` tends to zero for the horizon-indexed generated
algorithm family. The theorem card and weapon remain retrieval evidence, not
local proofs. Pathwise/probability convergence, one-policy anytime
consistency, minimax, simultaneous high-probability all-horizon,
contextual/dynamic, uniform-over-parameter, and broader linear-bandit routes
remain separate.

## Finite-Horizon RL Generated Visit-Law Edge

The downstream explicit-support edge
`RL-FINITE-HORIZON-EXPLORATORY-PATH-SUPPORT-REACHABILITY-CALIBRATION` now
compiles. It identifies stage zero with the initial marginal, contains one
chosen predecessor transition event in each next-state event, and recursively
multiplies the initial floor by uniform-action and true-transition singleton
floors. The result is independent of the optimistic table, so it supplies the
same state envelope to the initial and every history-selected exploratory
behavior policy and reaches the existing global terminal.

This closes state reachability only under an explicit selected-path support
certificate. The downstream
`RL-FINITE-HORIZON-EXPLORATORY-PATH-SUPPORT-EXPLICIT-COUNT-BONUS-CALIBRATION`
edge now compiles a common state-action visit floor into every expected-count
margin. Its positive denominator gives a uniform transition radius, and the
finite-state/horizon half contraction proves that
`transitionBonus = rewardBound` covers the linear value envelope for the
initial and every successor behavior policy. The resulting source calibration
reaches the same global terminal without caller margin or cover premises.

The further downstream edge
`RL-FINITE-HORIZON-EXPLORATORY-PATH-SUPPORT-EPISODE-THRESHOLD-CALIBRATION`
now compiles. With `q=4*card(State)*horizon+1`, an episode count above
`q^2*log(2/localCoordinateDelta)/(2*visitFloor^2)` yields
`radius<episodes*visitFloor/q`. It therefore proves both the strict count
margin and the positive-denominator half contraction, constructs the positive
reward-bound cover and source calibration, and reaches the same global
terminal. The nondegenerate Bool canary verifies `q=17` and
`9248*log(192)<2^22`.

The next downstream edge
`RL-FINITE-HORIZON-ADAPTIVE-EMPIRICAL-OPTIMISTIC-OCCUPANCY-RADIUS-ENVELOPE`
also compiles. Probability occupancy of a constant cost is exactly horizon
times that cost. The current known-reward empirical plan has selected radius
equal to its fixed transition bonus, so the complete adaptive sum is exactly
`rounds * (horizon * (2 * transitionBonus))`. Rewriting the episode-threshold
terminal gives the same confidence event and optimism with recommended
expected regret at most `rounds * (horizon * (2 * rewardBound))`. The Bool
horizon-two, two-round, bonus-one canary evaluates the expression to `8`.

The downstream edge
`RL-FINITE-HORIZON-ADAPTIVE-CUMULATIVE-COUNT-RADIUS-CONTRACT-REGRET` now
compiles. It measurably sums every transition-count coordinate in the observed
prefix, normalizes the cumulative empirical kernel, selects a plan whose
nonnegative antitone radius shrinks with cumulative visits, and constructs the
next exploratory batch source. The recursive value is bounded using the
zero-count radius. Under one explicit cumulative coordinate-confidence event,
the route proves roundwise optimism and recommendation regret at most
`sum round, horizon * (2 * radiusEnvelope round)`.

This older radius-contract branch closed its accumulated planner/source and
regret consumer, but did not itself prove a statistical rate. Its former next
edge—the adaptive cumulative count-MGF/confidence producer—is now consumed by
the canonical strict-prefix UCBVI-CH branch above. Full predecessor marginal
sums outside the canonical assumptions, stochastic rewards, behavior/realized
regret, and Bernstein/minimax rates remain separate.

The downstream calibration edge
`RL-FINITE-HORIZON-EXPLORATORY-STATE-REACHABILITY-CALIBRATION` now compiles.
It converts the uniform exploratory PMF floor to a Real action-kernel bound,
multiplies it by the exact generated stage-state mass and episode count, and
uses the resulting strict margin to construct every initial/successor policy
calibration. The final theorem directly retains the existing global-delta
confidence, optimism, and recommended expected-regret sum conclusion.

The state-action margin is therefore reduced to a state-only reachability
envelope plus exploration. The explicit path-support producer now supplies that
envelope under true singleton-floor contracts; the explicit scalar count/bonus
calibration, symbolic episode threshold, and exact fixed-bonus occupancy
envelope compile downstream. This older forced-exploration branch itself does
not contain the later canonical strict-prefix aggregate-count UCBVI-CH theorem.
Behavior and realized sampled-return regret remain separate.

The population-law branch now includes
`RL-FINITE-HORIZON-STAGE-VISIT-FACTORIZATION`. At every valid stage, a generated
state/action visit has exactly the generated state-event mass times the policy
action-kernel singleton mass. The Lean route follows the remaining-trace
coordinate recursion, including the successor-stage `compProd` case, and then
integrates over the initial state law. The identity remains true at zero state
mass.

Together with the exploratory action floor, this creates the algebraic bridge
used by the visit-margin calibration branch. State reachability remains an
explicit premise of that older exploratory route; the canonical strict-prefix
UCBVI-CH branch above instead closes its own aggregate-count, bonus, and
high-probability terminal. Behavior/realized regret and Bernstein/minimax
UCB-VI remain separate.

## Finite-Horizon RL Generated Transition-Law Edge

The fixed-policy generated trajectory branch now includes
`RL-FINITE-HORIZON-STAGE-TRANSITION-JOINT-FACTORIZATION`. At each valid stage,
the joint `(state, action, nextState)` event mass is exactly the visit event
mass times the true transition-kernel singleton mass. The Lean proof follows
the recursive finite trajectory kernel and remains valid for zero-occupancy
coordinates.

The downstream edge
`RL-FINITE-HORIZON-IID-ELIGIBLE-EMPIRICAL-TRANSITION-CONFIDENCE` is now compiled.
It joins the empirical count-ratio API, simultaneous count event, eligible
positive denominator, and generated population factorization into one
global-delta singleton-frequency theorem. The next missing edge toward the
finite-batch confidence/regret endpoint was the generated empirical reward
producer below, not another transition union bound.

The reward edge
`RL-FINITE-HORIZON-IID-GENERATED-EMPIRICAL-REWARD-EXACTNESS` also compiles.
Because the present MDP reward is deterministic, generated records are
pointwise reward-consistent and every positive-count empirical reward equals
the true reward exactly. This result shares the existing eligible transition
good event and spends no extra failure probability. Full finite-batch confidence
still needs all planner coordinates covered plus a noncircular generated-value
envelope and transition-radius assembly; stochastic rewards require a separate
model extension rather than concentration assumptions on this deterministic API.

The all-coordinate edge
`RL-FINITE-HORIZON-IID-ALL-COORDINATE-FINITE-BATCH-CONFIDENCE` now compiles as
well. It replaces the random visit-count denominator by the larger deterministic
radius based on `expectedCount - countRadius`, proves the noncircular envelope
`remaining * (rewardBound + transitionBudget)`, and uses an explicit finite
coordinate cover to construct the complete empirical-model confidence data.
Under the mapped iid law this witness exists a.e. off the same global-delta
event and immediately yields global optimism plus the existing one-episode
expected-regret occupancy bound. This iid branch itself does not provide
adaptive cross-episode policy updates or cumulative bonus summation; those are
closed separately by the canonical generated UCBVI-CH branch above. Stochastic
rewards, anytime confidence, and Bernstein/minimax UCB-VI remain downstream.

The finite-product edge
`RL-FINITE-HORIZON-IID-MULTIBATCH-CUMULATIVE-CONFIDENCE-REGRET` now compiles.
It puts finitely many copies of the fixed-policy iid batch law under Mathlib
`Measure.pi`, allocates `delta / rounds` to each pulled-back count event, and
retains a global-delta finite union. Coordinatewise a.e. reward support builds a
confidence witness for every batch model outside that event. The route then
sums all batch-derived optimistic-policy expected-regret bounds and exposes
optimism for every model.

This is an independent offline multibatch edge, not an adaptive UCB-VI process:
the data policy is fixed, later batches do not depend on earlier models, and no
realized trajectories are concatenated. An adaptive episode-history law and a
cumulative selected-radius/bonus-rate theorem remain the next RL boundary.

The adaptive-law edge
`RL-FINITE-HORIZON-ADAPTIVE-EPISODE-BATCH-COUNT-CONFIDENCE` now compiles. It
replaces `Measure.pi` by Mathlib's Ionescu--Tulcea `Kernel.trajMeasure` and
records exact equality between every history-indexed batch kernel and the iid
batch law of the policy selected from that history. Initial and successor laws,
the prefix `compProd` recurrence, and the regular conditional next-batch law
are exposed as named declarations.

Uniform measurable history-fiber event bounds are integrated and unioned at
local budget `delta / rounds`. Instantiating the fibers with each selected
policy's simultaneous count event gives one global-delta adaptive count event
and every visit/transition count deviation outside it, with no independence
assumption. The source and selected-event measurability remain caller contracts
for the generic theorem.

The concrete source edge
`RL-FINITE-HORIZON-ADAPTIVE-EMPIRICAL-OPTIMISTIC-SOURCE-COUNT-CONFIDENCE`
now compiles downstream. It measurably extracts all transition counts from the
latest batch, normalizes empirical transition rows with a zero-count fallback,
computes a known-reward/fixed-bonus optimistic deterministic action table, and
comaps the table-indexed iid batch kernel along that selector. Exact selected
laws, selected-event measurability, next-batch conditional laws, and the
global-delta adaptive count terminal no longer remain caller premises.

This older edge is a concrete empirical-transition process, but is not the
canonical UCBVI-CH source: its bonus is uncalibrated and prior batches are not
accumulated. The later strict-prefix recurrent branch above closes known-reward
adaptive confidence and cumulative bonus control. Stochastic reward confidence,
realized sampled-return regret, and Bernstein/minimax UCB-VI remain downstream.

The downstream edge
`RL-FINITE-HORIZON-ADAPTIVE-EXPLORATORY-EMPIRICAL-OPTIMISTIC-ALL-COORDINATE-CONFIDENCE-RECOMMENDED-REGRET`
now compiles. Uniform exploration around every latest optimistic table gives
each action an explicit mass floor and constructs the exact adaptive behavior
source. Exact empirical-kernel transport, a known-reward value envelope, and
behavior-policy reachability/bonus-cover contracts produce confidence and
optimism for every observed plan outside one global event. The expected regrets
of the optimistic policies recommended by those batches sum below selected-
radius occupancies. Recommendation regret is not exploratory behavior,
generated raw policy-value pseudo-regret, or realized regret. This older branch
did not itself have calibrated accumulated statistics or an explicit UCBVI-CH
rate; those are supplied by the canonical strict-prefix branch above.
