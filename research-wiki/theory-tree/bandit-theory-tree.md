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

## Definition Layer

| Branch | Leaf nodes | Current status |
| --- | --- | --- |
| Finite actions | `Fin K`, nonempty action set, finite policies, arm casts | dependency-light local core plus Mathlib card `MLIB-FINTYPE-FIN` |
| Time traces | action traces, reward traces, histories, filtrations | local finite traces; filtrations are theorem-card/proof-obligation |
| Pull counts | recursive count, monotonicity, split by arm/time, indicator sum bridge | compiled leaves in `BanditRLProof.LeafLemmas`; finite-sum bridge is Mathlib candidate |
| Regret | pseudo-regret, gap decomposition, Bayesian regret, dynamic regret | compiled pseudo-regret leaves plus LML theorem cards |
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

## Compiled Local Leaves

The first dependency-light compiled leaf library is
`BanditRLProof.LeafLemmas`.  It currently exposes:

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
- `UCB.score_eq_empiricalMean`.

Future Mathlib-backed tasks should use these as local bridge lemmas, then
replace or generalize them with Mathlib APIs when the dependency layer is
selected.

## Algorithm Branches

| Branch | Immediate proof leaves | Source cards |
| --- | --- | --- |
| ETC | round-robin count, commit argmax, wrong-commit probability, pull-count after commit | `TXT-LATTIMORE-SZEPESVARI-2020`, LML `Bandits.ETC.regret_le` |
| UCB | positive initial counts, index maximization, good-event pull bound, tail union, regret sum | `TXT-BUBECK-CESABIANCHI-2012`, `TXT-LATTIMORE-SZEPESVARI-2020`, `PPR-AUER-CBF-2002-UCB1`, LML `Bandits.UCB.regret_le` |
| KL-UCB | Bernoulli KL, confidence inversion, bounded stochastic reward contracts | `PPR-GARIVIER-CAPPE-2011-KLUCB`, `TXT-LATTIMORE-SZEPESVARI-2020` |
| Thompson sampling | posterior action identity, Bayesian regret decomposition, clipped confidence bridge | `TXT-SLIVKINS-2019-2024`, `PPR-AGRAWAL-GOYAL-2011-TS`, LML `Bandits.TS.hasCondDistrib_action`, LML `Bandits.integral_regret_le` |
| EXP3/adversarial | importance-weighted loss, exponential weights potential, learning-rate optimization | `TXT-BUBECK-CESABIANCHI-2012`, `TXT-LATTIMORE-SZEPESVARI-2020`, `PPR-AUER-CFS-2002-EXP3` |
| Tsallis-INF/FTRL | simplex probabilities, Tsallis regularizer, stability/penalty split, self-bounding conversion | `PPR-ZIMMERT-SELDIN-2018-TSALLIS-INF`, `PPR-MASOUDIAN-SELDIN-2021-TSALLIS-INF`, `PPR-KATO-ITO-2024-LC-TSALLIS-INF`, `PPR-ADAPTIVE-LR-FTRL-2024` |
| Linear/OFUL | least-squares estimator, confidence ellipsoid, elliptical potential, optimism | `TXT-LATTIMORE-SZEPESVARI-2020`, `PPR-ABBASI-YADKORI-2011-SELF-NORMALIZED`, `PPR-LI-CHU-LANGFORD-SCHAPIRE-2010-LINUCB` |
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

## Expansion Policy

When adding a theorem:

1. attach it to a scenario card;
2. choose the textbook/paper/LML source card;
3. search Mathlib retrieval cards for each general leaf;
4. search local declarations with `list-lean-decls`;
5. make hidden regularity explicit;
6. write one proof-obligation row per lower-agent leaf;
7. keep failed attempts in memory with the mathematical diagnosis;
8. export the compiled theorem to Markdown and LaTeX only after Lean closure.

The tree is intentionally larger than the current Lean package.  Branches
without compiled local declarations remain theorem-card, cited-result, or
open-problem memory until a task imports, ports, or proves the needed lemmas.
