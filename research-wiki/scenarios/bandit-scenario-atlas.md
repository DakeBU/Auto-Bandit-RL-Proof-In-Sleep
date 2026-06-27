# Bandit Scenario Atlas

This atlas is ABRL's current scenario taxonomy as of June 27, 2026.  It is a
living memory file: new papers and formalization routes should add cards here
before lower agents start Lean work.

Refresh/search the compact index with:

```bash
python3 tools/bandit.py reference-index
python3 tools/bandit.py list-scenarios
python3 tools/bandit.py list-papers
python3 tools/bandit.py search-memory contextual
```

## Scenario Cards

| Scenario | Algorithms/theorems | Source cards | Leaf families | Mathlib retrieval |
| --- | --- | --- | --- | --- |
| `SCN-STOCHASTIC-FINITE` finite stochastic bandits | ETC, UCB, MOSS, KL-UCB, Thompson sampling | `TXT-BUBECK-CESABIANCHI-2012`, `TXT-LATTIMORE-SZEPESVARI-2020`, `PPR-AUER-CBF-2002-UCB1`, `PPR-GARIVIER-CAPPE-2011-KLUCB`, `PPR-AGRAWAL-GOYAL-2011-TS` | pull-count algebra, gap decomposition, sub-Gaussian tails, Bernoulli KL | `MLIB-FINSET-SUMS`, `MLIB-ORDER-ALGEBRA`, `MLIB-PROBABILITY-INDEPENDENCE` |
| `SCN-BAYESIAN-POSTERIOR` Bayesian/posterior bandits | Thompson sampling, Bayes-UCB, posterior sampling | `TXT-SLIVKINS-2019-2024`, `PPR-AGRAWAL-GOYAL-2011-TS` | posterior kernels, Bayesian regret, probability matching, update contracts | `MLIB-PROBABILITY-KERNEL`, `MLIB-CONDITIONAL-EXPECTATION`, `MLIB-MEASURE-INTEGRAL` |
| `SCN-ADVERSARIAL-FINITE` adversarial finite-arm bandits | EXP3, EXP3-IX, FTRL/OMD variants | `TXT-BUBECK-CESABIANCHI-2012`, `TXT-LATTIMORE-SZEPESVARI-2020`, `PPR-AUER-CFS-2002-EXP3` | importance-weighted estimators, exponential weights, potential inequalities | `MLIB-FINSET-SUMS`, `MLIB-EXP-LOG-INEQUALITIES`, `MLIB-ORDER-ALGEBRA` |
| `SCN-BOBW-ADAPTIVE` best-of-both-worlds/adaptive bandits | Tsallis-INF, LC-Tsallis-INF, adaptive FTRL | `PPR-ZIMMERT-SELDIN-2018-TSALLIS-INF`, `PPR-MASOUDIAN-SELDIN-2021-TSALLIS-INF`, `PPR-KATO-ITO-2024-LC-TSALLIS-INF`, `PPR-ADAPTIVE-LR-FTRL-2024` | Tsallis regularization, self-bounding conversion, FTRL stability/penalty, adaptive learning rates | `MLIB-REAL-RPOW-TSALLIS`, `MLIB-CONVEX-LINALG`, `MLIB-FINSET-SUMS`, `MLIB-EXP-LOG-INEQUALITIES` |
| `SCN-CONTEXTUAL` contextual bandits | EXP4, LinUCB, contextual Thompson sampling | `TXT-LATTIMORE-SZEPESVARI-2020`, `PPR-LI-CHU-LANGFORD-SCHAPIRE-2010-LINUCB`, `PPR-FAT-2018-MERITOCRATIC-FAIRNESS` | policy classes, expert advice, context measurability, regret against policies | `MLIB-MEASURE-INTEGRAL`, `MLIB-PROBABILITY-KERNEL`, `MLIB-FINSET-SUMS` |
| `SCN-LINEAR-GLM` linear and generalized-linear bandits | LinUCB, OFUL, linear TS, GLM-UCB | `TXT-LATTIMORE-SZEPESVARI-2020`, `PPR-ABBASI-YADKORI-2011-SELF-NORMALIZED`, `PPR-LI-CHU-LANGFORD-SCHAPIRE-2010-LINUCB` | least squares, self-normalized martingales, ellipsoid confidence, determinant algebra | `MLIB-CONVEX-LINALG`, `MLIB-MARTINGALE-STOCHASTIC`, `MLIB-REAL-LOG-SQRT` |
| `SCN-LIPSCHITZ-METRIC` Lipschitz/metric/continuum bandits | zooming, HOO, nearest-neighbor UCB | `TXT-SLIVKINS-2019-2024` | metric balls, covering numbers, Lipschitz reward contracts, near-optimality dimension | `MLIB-METRIC-TOPOLOGY`, `MLIB-FINSET-SUMS`, `MLIB-ASYMPTOTICS` |
| `SCN-PURE-EXPLORATION` pure exploration | successive elimination, LUCB, Track-and-Stop | `TXT-LATTIMORE-SZEPESVARI-2020`, `TXT-SLIVKINS-2019-2024` | stopping rules, fixed-confidence events, sample complexity, change-of-measure | `MLIB-CONDITIONAL-EXPECTATION`, `MLIB-MEASURE-INTEGRAL`, `MLIB-ASYMPTOTICS` |
| `SCN-COMBINATORIAL` combinatorial/semi-bandit feedback | combinatorial UCB, semi-bandit TS, matroid/knapsack variants | `TXT-LATTIMORE-SZEPESVARI-2020` | set-valued actions, component rewards, oracle contracts, semi-bandit decompositions | `MLIB-FINSET-SUMS`, `MLIB-CONVEX-LINALG`, `MLIB-ORDER-ALGEBRA` |
| `SCN-RESOURCE-CONSTRAINED` resource-constrained/BwK | BwK, primal-dual UCB, budgeted TS | `TXT-SLIVKINS-2019-2024`, `PPR-BADANIDIYURU-KLEINBERG-SLIVKINS-2013-BWK` | resource traces, budget stopping times, primal-dual comparison, constraint regret | `MLIB-FINSET-SUMS`, `MLIB-ORDER-ALGEBRA`, `MLIB-MEASURE-INTEGRAL` |
| `SCN-DUELING-PREFERENCE` dueling/preference/ranking bandits | RUCB variants, Borda/Condorcet algorithms, preference elimination | `PPR-IJCAI-2018-DUELING-SURVEY` | pairwise preference matrices, winner notions, comparison regret, partial-monitoring bridge | `MLIB-FINSET-SUMS`, `MLIB-ORDER-ALGEBRA`, `MLIB-PROBABILITY-INDEPENDENCE` |
| `SCN-NONSTATIONARY` nonstationary/rotting/drifting bandits | sliding-window UCB, discounted UCB, change-point UCB | `TXT-SLIVKINS-2019-2024` | dynamic regret, variation budgets, windowed concentration, change detection | `MLIB-FINSET-SUMS`, `MLIB-PROBABILITY-INDEPENDENCE`, `MLIB-ASYMPTOTICS` |
| `SCN-HEAVY-TAILED-ROBUST` heavy-tailed/corrupted/robust bandits | median-of-means UCB, trimmed-mean UCB, corruption-robust contextual algorithms | `TXT-LATTIMORE-SZEPESVARI-2020` | robust mean estimators, moment assumptions, truncation events, corruption budgets | `MLIB-MEASURE-INTEGRAL`, `MLIB-ORDER-ALGEBRA`, `MLIB-ASYMPTOTICS` |
| `SCN-DELAYED-BATCHED` delayed/batched/asynchronous bandits | delayed EXP3, batched UCB, asynchronous TS | `TXT-BUBECK-CESABIANCHI-2012` | delay queues, pending feedback, batch regret, asynchronous filtrations | `MLIB-FINSET-SUMS`, `MLIB-MARTINGALE-STOCHASTIC`, `MLIB-CONDITIONAL-EXPECTATION` |
| `SCN-CONSTRAINTS` safe/conservative/fair/private bandits | conservative UCB, safe-UCB, fair contextual bandits, private UCB | `PPR-AAAI-2020-SAFE-LINEAR-STOCHASTIC`, `PPR-AAAI-2016-DP-MAB`, `PPR-FAT-2018-MERITOCRATIC-FAIRNESS` | baseline regret, constraint budgets, privacy noise, fairness invariants | `MLIB-MEASURE-INTEGRAL`, `MLIB-ORDER-ALGEBRA`, `MLIB-PROBABILITY-INDEPENDENCE` |
| `SCN-FEDERATED-DISTRIBUTED` federated/distributed bandits | Fed-UCB, personalized federated bandits, Byzantine-robust UCB | `PPR-AAAI-2021-FEDERATED-MAB`, `PPR-FEDERATED-NEURAL-BANDITS-2022` | client aggregation, heterogeneity, communication rounds, robust mean estimates | `MLIB-FINSET-SUMS`, `MLIB-MEASURE-INTEGRAL`, `MLIB-PROBABILITY-INDEPENDENCE` |
| `SCN-RL-MDP` finite-horizon RL and MDP regret | UCB-VI, posterior sampling RL, optimism under uncertainty, Bellman backups | `TXT-SLIVKINS-2019-2024`, `PPR-AZAR-OSBAND-MUNOS-2017-UCBVI` | finite kernels, policies, Bellman recursion, occupancy measures, episode regret | `MLIB-PROBABILITY-KERNEL`, `MLIB-CONDITIONAL-EXPECTATION`, `MLIB-MEASURE-INTEGRAL` |
| `SCN-LLM-REC-SYS` LLM/recommender/neural bandits | neural contextual bandits, bandit prompt optimization, LLM-assisted priors | `PPR-LI-CHU-LANGFORD-SCHAPIRE-2010-LINUCB`, `PPR-FEDERATED-NEURAL-BANDITS-2022` | offline-to-online priors, context embeddings, model-selection regret, adaptive response generation | `MLIB-MEASURE-INTEGRAL`, `MLIB-PROBABILITY-KERNEL`, `MLIB-CONVEX-LINALG` |

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
