# Bandit Scenario Atlas

This atlas is ABRL's current scenario taxonomy as of June 27, 2026.  It is a
living memory file: new papers and formalization routes should add cards here
before lower agents start Lean work.

Refresh/search the compact index with:

```bash
python3 tools/bandit.py reference-index
python3 tools/bandit.py list-scenarios
python3 tools/bandit.py search-memory contextual
```

## Scenario Cards

| Scenario | Algorithms/theorems | Leaf families | Mathlib retrieval |
| --- | --- | --- | --- |
| `SCN-STOCHASTIC-FINITE` finite stochastic bandits | ETC, UCB, MOSS, KL-UCB, Thompson sampling | pull-count algebra, gap decomposition, sub-Gaussian tails, Bernoulli KL | `MLIB-FINSET-SUMS`, `MLIB-ORDER-ALGEBRA`, `MLIB-PROBABILITY-INDEPENDENCE` |
| `SCN-ADVERSARIAL-FINITE` adversarial finite-arm bandits | EXP3, EXP3-IX, FTRL/OMD variants | importance-weighted estimators, exponential weights, potential inequalities | `MLIB-FINSET-SUMS`, `MLIB-REAL-LOG-SQRT`, `MLIB-ORDER-ALGEBRA` |
| `SCN-CONTEXTUAL` contextual bandits | EXP4, LinUCB, contextual Thompson sampling | policy classes, expert advice, context measurability, regret against policies | `MLIB-MEASURE-INTEGRAL`, `MLIB-PROBABILITY-KERNEL`, `MLIB-FINSET-SUMS` |
| `SCN-LINEAR-GLM` linear and generalized-linear bandits | LinUCB, OFUL, linear TS, GLM-UCB | least squares, self-normalized martingales, ellipsoid confidence, determinant algebra | `MLIB-CONVEX-LINALG`, `MLIB-CONDITIONAL-EXPECTATION`, `MLIB-REAL-LOG-SQRT` |
| `SCN-PURE-EXPLORATION` pure exploration | successive elimination, LUCB, Track-and-Stop | stopping rules, fixed-confidence events, sample complexity, change-of-measure | `MLIB-CONDITIONAL-EXPECTATION`, `MLIB-MEASURE-INTEGRAL`, `MLIB-ASYMPTOTICS` |
| `SCN-COMBINATORIAL` combinatorial/semi-bandit feedback | combinatorial UCB, semi-bandit TS, matroid/knapsack variants | set-valued actions, component rewards, oracle contracts, semi-bandit decompositions | `MLIB-FINSET-SUMS`, `MLIB-CONVEX-LINALG`, `MLIB-ORDER-ALGEBRA` |
| `SCN-NONSTATIONARY` nonstationary/rotting/drifting bandits | sliding-window UCB, discounted UCB, change-point UCB | dynamic regret, variation budgets, windowed concentration, change detection | `MLIB-FINSET-SUMS`, `MLIB-PROBABILITY-INDEPENDENCE`, `MLIB-ASYMPTOTICS` |
| `SCN-CONSTRAINTS` safe/conservative/fair/private bandits | conservative UCB, safe-UCB, fair contextual bandits, private UCB | baseline regret, constraint budgets, privacy noise, fairness invariants | `MLIB-MEASURE-INTEGRAL`, `MLIB-ORDER-ALGEBRA`, `MLIB-PROBABILITY-INDEPENDENCE` |
| `SCN-FEDERATED-DISTRIBUTED` federated/distributed bandits | Fed-UCB, personalized federated bandits, Byzantine-robust UCB | client aggregation, heterogeneity, communication rounds, robust mean estimates | `MLIB-FINSET-SUMS`, `MLIB-MEASURE-INTEGRAL`, `MLIB-PROBABILITY-INDEPENDENCE` |
| `SCN-RL-MDP` finite-horizon RL and MDP regret | UCB-VI, posterior sampling RL, optimism under uncertainty, Bellman backups | finite kernels, policies, Bellman recursion, occupancy measures, episode regret | `MLIB-PROBABILITY-KERNEL`, `MLIB-CONDITIONAL-EXPECTATION`, `MLIB-MEASURE-INTEGRAL` |
| `SCN-LLM-REC-SYS` LLM/recommender/neural bandits | neural contextual bandits, bandit prompt optimization, LLM-assisted priors | offline-to-online priors, context embeddings, model-selection regret, adaptive response generation | `MLIB-MEASURE-INTEGRAL`, `MLIB-PROBABILITY-KERNEL`, `MLIB-CONVEX-LINALG` |

## Frontier Rule

Modern scenario cards are not a license to weaken the Lean standard.  Each new
scenario must still decompose into:

- local definitions;
- textbook theorem route;
- Mathlib retrieval cards;
- hidden regularity contracts;
- proof-obligation leaves;
- proof-export surface.

If a scenario depends on technology ABRL does not yet have, add an open-problem
card and keep the result in theorem-card or cited-result status.
