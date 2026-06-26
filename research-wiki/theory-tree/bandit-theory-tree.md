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

## Reusable Mathematical Leaves

| Leaf family | Mathlib cards | Downstream branches |
| --- | --- | --- |
| Finite sums and reindexing | `MLIB-FINSET-SUMS`, `MLIB-FINTYPE-FIN` | regret decomposition, EXP3 weights, combinatorial actions |
| Order and positivity | `MLIB-ORDER-ALGEBRA`, `MLIB-REAL-LOG-SQRT` | UCB widths, KL-UCB, confidence radii, constraint budgets |
| Measurability and integrability | `MLIB-MEASURE-INTEGRAL`, `MLIB-PROBABILITY-KERNEL` | expected regret, Bayesian regret, contextual/RL kernels |
| Independence and conditioning | `MLIB-PROBABILITY-INDEPENDENCE`, `MLIB-CONDITIONAL-EXPECTATION` | Hoeffding routes, martingales, posterior identities |
| Asymptotics | `MLIB-ASYMPTOTICS` | minimax rates, logarithmic regret exports |
| Linear/convex algebra | `MLIB-CONVEX-LINALG` | linear bandits, OFUL, convex action sets |

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
- `pullCount_eq_zero_of_forall_ne`;
- `pullCount_eq_time_of_forall_eq`;
- `pullCount_pos_of_eq_before`;
- `pullCount_const_self`;
- `pullCount_const_of_ne`;
- `sumRewards_succ_of_eq`;
- `sumRewards_succ_of_ne`;
- `sumRewards_eq_zero_of_forall_ne`;
- `sumRewards_const_of_ne`;
- `FiniteBanditModel.bestMean_eq_mean_bestArm`;
- `FiniteBanditModel.gap_of_ne_bestArm`;
- `pseudoRegret_one`;
- `pseudoRegret_succ_of_bestArm`;
- `pseudoRegret_succ_of_gap_zero`;
- `pseudoRegret_eq_zero_of_forall_bestArm`;
- `pseudoRegret_eq_zero_of_forall_gap_zero`;
- `pseudoRegret_const_bestArm`;
- `pseudoRegret_const_of_gap_zero`.

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
| UCB | positive initial counts, index maximization, good-event pull bound, tail union, regret sum | `TXT-BUBECK-CESABIANCHI-2012`, `TXT-LATTIMORE-SZEPESVARI-2020`, LML `Bandits.UCB.regret_le` |
| Thompson sampling | posterior action identity, Bayesian regret decomposition, clipped confidence bridge | `TXT-SLIVKINS-2019-2024`, LML `Bandits.TS.hasCondDistrib_action`, LML `Bandits.integral_regret_le` |
| EXP3/adversarial | importance-weighted loss, exponential weights potential, learning-rate optimization | `TXT-BUBECK-CESABIANCHI-2012`, `TXT-LATTIMORE-SZEPESVARI-2020` |
| Linear/OFUL | least-squares estimator, confidence ellipsoid, elliptical potential, optimism | `TXT-LATTIMORE-SZEPESVARI-2020` |
| Pure exploration | confidence event, stopping rule, sample complexity, lower-bound change-of-measure | `TXT-LATTIMORE-SZEPESVARI-2020`, `TXT-SLIVKINS-2019-2024` |
| Finite-horizon RL/MDP | finite kernels, Bellman recursion, occupancy measures, episode regret, optimism | `TXT-SLIVKINS-2019-2024`, scenario card `SCN-RL-MDP` |

## Expansion Policy

When adding a theorem:

1. attach it to a scenario card;
2. choose the textbook/paper/LML source card;
3. search Mathlib retrieval cards for each general leaf;
4. make hidden regularity explicit;
5. write one proof-obligation row per lower-agent leaf;
6. keep failed attempts in memory with the mathematical diagnosis;
7. export the compiled theorem to Markdown and LaTeX only after Lean closure.

The tree is intentionally larger than the current Lean package.  Branches
without compiled local declarations remain theorem-card, cited-result, or
open-problem memory until a task imports, ports, or proves the needed lemmas.
