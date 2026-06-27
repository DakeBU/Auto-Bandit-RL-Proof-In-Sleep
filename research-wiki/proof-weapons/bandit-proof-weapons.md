# Bandit/RL Proof Weapons

Proof weapons are route-generation tools for upper agents.  They are not local
Lean proofs, not theorem cards, and not reusable declarations.  A lower agent
may use a weapon only after middle has turned it into concrete source cards,
local APIs, Mathlib/LML retrieval cards, and proof-obligation leaves.

Refresh/search the compact index with:

```bash
python3 tools/bandit.py reference-index
python3 tools/bandit.py list-weapons
python3 tools/bandit.py search-memory Tsallis
python3 tools/bandit.py search-memory sub-Gaussian
python3 tools/bandit.py list-lean-decls between --statement
```

## Boundary Rule

| Layer | May use proof weapons for | Must not do |
| --- | --- | --- |
| Upper | propose several proof routes, choose the next frontier, detect missing assumptions | claim the weapon proves a theorem |
| Middle | decompose a route into source cards, local APIs, Mathlib searches, and proof obligations | pass a vague technique name to lower agents |
| Lower | use the resulting compiled local lemmas or imported theorem cards | cite `UCB`, `Tsallis`, or `tail inequality` as a proof term |
| Reviewer | reject route drift and check that each weapon became concrete leaves | accept inspiration as certified memory |

## Weapon Cards

| Card | Route inspiration | Direct retrieval cards | First leaves to make concrete |
| --- | --- | --- | --- |
| `WEAPON-UCB-OPTIMISM` | optimism under uncertainty for UCB and UCB-VI | `LML-UCB-REGRET`, `MLIB-REAL-LOG-SQRT`, `MLIB-PROBABILITY-SUBGAUSSIAN` | confidence event, positive pull count, tail summability |
| `WEAPON-TAIL-INEQUALITIES` | choose bounded/sub-Gaussian/conditional/variance tail route | `MLIB-PROBABILITY-SUBGAUSSIAN`, `MLIB-PROBABILITY-MGF`, `MLIB-PROBABILITY-VARIANCE` | integrability, independence/filtration, finite union bound |
| `WEAPON-TSALLIS-INF-FTRL` | Tsallis entropy FTRL and best-of-both-worlds bandits | `MLIB-REAL-RPOW-TSALLIS`, `MLIB-CONVEX-LINALG`, `MLIB-FINSET-SUMS` | simplex API, Tsallis regularizer, FTRL optimality, stability/penalty split |
| `WEAPON-EXP3-POTENTIAL` | adversarial finite-arm potential telescope | `MLIB-EXP-LOG-INEQUALITIES`, `MLIB-FINSET-SUMS` | estimator unbiasedness, potential inequality, learning-rate algebra |
| `WEAPON-SELF-NORMALIZED-OFUL` | linear confidence ellipsoids and OFUL/LinUCB | `MLIB-CONVEX-LINALG`, `MLIB-MARTINGALE-STOCHASTIC` | Gram matrix, determinant/norm side conditions, self-normalized tail |
| `WEAPON-POSTERIOR-SAMPLING` | Thompson sampling probability matching | `LML-TS-POSTERIOR-ACTION`, `LML-TS-BAYES-REGRET`, `MLIB-PROBABILITY-KERNEL` | posterior kernel, conditional distribution identity, Bayesian integrability |
| `WEAPON-KL-CHANGE-OF-MEASURE` | KL-UCB and lower-bound source changes | `MLIB-EXP-LOG-INEQUALITIES`, `MLIB-MEASURE-INTEGRAL` | Bernoulli KL, absolute-continuity contract, confidence inversion |
| `WEAPON-PRIMAL-DUAL-BWK` | resource-constrained and knapsack bandits | `MLIB-FINSET-SUMS`, `MLIB-ORDER-ALGEBRA`, `MLIB-MEASURE-INTEGRAL` | budget trace, stopping by budget, dual feasibility |

## Reviewer Gate

A task using a weapon is incomplete until it records:

- the source card ids;
- the scenario card id;
- the Mathlib/LML/local declaration cards searched;
- the exact Lean leaf statements or proof obligations;
- the hidden regularity contracts;
- the reason for any proof-route pivot.

If a route repeatedly fails, treat the failure as mathematical information:
missing assumption, wrong abstraction, counterexample, or a genuine upstream
lemma gap.
