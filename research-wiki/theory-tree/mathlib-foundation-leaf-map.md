# Mathlib Foundation To Bandit Leaf Map

This file is the fine-grained leaf map that lower agents should consult before
opening a Mathlib-heavy proof.  It starts below bandit algorithms: measure
theory, measurability, integrability, kernels, conditioning, concentration,
functional inequalities, and optimization primitives.

Status vocabulary:

- `compiled-local`: local ABRL declaration builds now;
- `import-route`: likely Mathlib route identified, not yet imported locally;
- `theorem-card`: external theorem route recorded, not local proof;
- `missing-leaf`: needs a small statement and proof/import decision;
- `weapon-only`: proof idea only, not a theorem dependency.

## Foundation Spine

```text
finite index and sums
-> measurable spaces and finite kernels
-> random variables and reward traces
-> integrability / measurability contracts
-> independence / filtration / conditional expectation
-> concentration or posterior identities
-> algorithm-specific control lemma
-> regret/sample-complexity theorem
-> Markdown and LaTeX export
```

## Measure And Measurability Leaves

| Leaf id | Intended statement shape | Current status | Retrieval cards | Regularity contract |
| --- | --- | --- | --- | --- |
| `MEAS-FIN-ACTION` | finite arm type has measurable space and all arm maps are measurable | missing-leaf | `MLIB-FINTYPE-FIN`, `MLIB-MEASURE-INTEGRAL` | finite action space |
| `MEAS-HISTORY` | finite histories/actions/rewards form measurable product objects | missing-leaf | `MLIB-MEASURE-INTEGRAL`, `MLIB-PROBABILITY-KERNEL` | measurable action/reward spaces |
| `MEAS-POLICY` | policy map from history/context to arm is measurable | missing-leaf | `MLIB-MEASURE-INTEGRAL`, `MLIB-PROBABILITY-KERNEL` | measurable history and policy |
| `MEAS-REWARD` | reward random variable for selected arm is measurable | missing-leaf | `MLIB-MEASURE-INTEGRAL` | selected action and reward kernel measurable |
| `MEAS-REGRET` | pseudo/expected regret summand is measurable | missing-leaf | `MLIB-MEASURE-INTEGRAL`, `MLIB-FINSET-SUMS` | measurable means, actions, rewards |

## Integrability And Expectation Leaves

| Leaf id | Intended statement shape | Current status | Retrieval cards | Regularity contract |
| --- | --- | --- | --- | --- |
| `INT-REWARD-BOUNDED` | bounded reward implies integrable reward | import-route | `MLIB-MEASURE-INTEGRAL`, `MLIB-ORDER-ALGEBRA` | bounded reward, measurable reward |
| `INT-FINITE-SUM` | finite sum of integrable regret terms is integrable | import-route | `MLIB-MEASURE-INTEGRAL`, `MLIB-FINSET-SUMS` | each term integrable |
| `EXP-FINITE-SUM` | expectation distributes over finite regret sum | import-route | `MLIB-MEASURE-INTEGRAL`, `MLIB-FINSET-SUMS` | integrability of each summand |
| `EXP-INDICATOR-PULL` | expected pull count as sum of event probabilities | missing-leaf | `MLIB-MEASURE-INTEGRAL`, `MLIB-FINSET-SUMS` | indicator measurability |
| `EXP-REGRET-PULLCOUNT` | expected regret equals gaps times expected pull counts | theorem-card | `LML-BANDIT-REGRET-PULLCOUNT`, `MLIB-MEASURE-INTEGRAL` | finite arms, integrable regret |

## Kernels, Posteriors, And Conditioning

| Leaf id | Intended statement shape | Current status | Retrieval cards | Regularity contract |
| --- | --- | --- | --- | --- |
| `KERNEL-REWARD` | reward distribution is a Markov kernel indexed by arm/context | import-route | `MLIB-PROBABILITY-KERNEL` | measurable index space |
| `KERNEL-POLICY-BIND` | policy and reward kernels compose into a trajectory law | missing-leaf | `MLIB-PROBABILITY-KERNEL` | measurable policy/kernel |
| `COND-EXPECT-REWARD` | conditional expectation of centered reward is zero/sub-Gaussian | missing-leaf | `MLIB-CONDITIONAL-EXPECTATION`, `MLIB-PROBABILITY-SUBGAUSSIAN` | filtration, adapted reward |
| `POSTERIOR-KERNEL` | posterior over environments is a kernel given history | missing-leaf | `MLIB-PROBABILITY-KERNEL`, `MLIB-CONDITIONAL-EXPECTATION` | prior, likelihood, history sigma-algebra |
| `TS-PROB-MATCH` | Thompson action law equals posterior best-arm law | theorem-card | `LML-TS-POSTERIOR-ACTION` | posterior kernel, best-arm measurability |

## Independence, Filtration, And Martingale Leaves

| Leaf id | Intended statement shape | Current status | Retrieval cards | Regularity contract |
| --- | --- | --- | --- | --- |
| `IID-REWARD-FAMILY` | rewards for fixed arms/time form independent or conditionally independent family | import-route | `MLIB-PROBABILITY-INDEPENDENCE` | indexed reward variables |
| `FILTRATION-HISTORY` | history sigma-algebras form a filtration | missing-leaf | `MLIB-CONDITIONAL-EXPECTATION`, `MLIB-MARTINGALE-STOCHASTIC` | monotone history information |
| `ADAPTED-ACTION` | action at time `t` is adapted to past history | missing-leaf | `MLIB-CONDITIONAL-EXPECTATION` | policy is predictable |
| `MART-DIFF-REWARD` | centered reward process is martingale difference | missing-leaf | `MLIB-MARTINGALE-STOCHASTIC` | conditional mean zero, integrable reward |
| `STOPPING-TIME-BUDGET` | budget exhaustion time is a stopping time | missing-leaf | `MLIB-MARTINGALE-STOCHASTIC`, `MLIB-PROBABILITY-KERNEL` | adapted resource trace |

## Concentration And Tail Leaves

| Leaf id | Intended statement shape | Current status | Retrieval cards | Regularity contract |
| --- | --- | --- | --- | --- |
| `TAIL-SUBGAUSS-SUM` | sum of independent centered sub-Gaussian variables has exponential tail | import-route | `MLIB-PROBABILITY-SUBGAUSSIAN`, `MLIB-PROBABILITY-INDEPENDENCE` | sub-Gaussian MGF, independence |
| `TAIL-COND-SUBGAUSS` | adapted conditionally sub-Gaussian sum tail | import-route | `MLIB-PROBABILITY-SUBGAUSSIAN`, `MLIB-CONDITIONAL-EXPECTATION` | filtration, conditional MGF |
| `TAIL-HOEFFDING-BOUNDED` | bounded centered rewards satisfy Hoeffding tail | import-route | `MLIB-PROBABILITY-SUBGAUSSIAN` | reward in interval, centered mean |
| `TAIL-UNION-FINITE` | finite union of bad tail events is bounded by sum of probabilities | import-route | `MLIB-MEASURE-INTEGRAL`, `MLIB-FINSET-SUMS` | finite event family |
| `TAIL-SUMMABILITY-UCB` | UCB bad-event probabilities have finite horizon summation bound | missing-leaf | `MLIB-FINSET-SUMS`, `MLIB-REAL-LOG-SQRT`, `MLIB-ASYMPTOTICS` | positive horizon, log side conditions |
| `TAIL-VARIANCE-ROBUST` | finite-variance/Chebyshev or robust mean tail route | import-route | `MLIB-PROBABILITY-VARIANCE` | finite second moment |

## Functional Inequality And Optimization Leaves

| Leaf id | Intended statement shape | Current status | Retrieval cards | Regularity contract |
| --- | --- | --- | --- | --- |
| `FTRL-ONE-STEP` | FTRL/OMD one-step inequality for a regularizer | missing-leaf | `MLIB-CONVEX-LINALG`, `MLIB-FINSET-SUMS` | convex domain, regularizer, finite action simplex |
| `EXP3-POTENTIAL` | exponential weights potential telescopes | missing-leaf | `MLIB-EXP-LOG-INEQUALITIES`, `MLIB-FINSET-SUMS` | nonnegative weights, learning rate positive |
| `TSALLIS-REGULARIZER` | Tsallis entropy regularizer is well-defined on simplex | missing-leaf | `MLIB-REAL-RPOW-TSALLIS`, `MLIB-CONVEX-LINALG` | nonnegative probabilities, sum one |
| `TSALLIS-STABILITY` | Tsallis-INF stability term bound | weapon-only | `WEAPON-TSALLIS-INF-FTRL`, `MLIB-REAL-RPOW-TSALLIS` | simplex, unbiased loss estimate |
| `SELF-BOUNDING-CONVERSION` | self-bounding condition converts adversarial regret to stochastic/gap-dependent bound | weapon-only | `WEAPON-TSALLIS-INF-FTRL` | problem-dependent lower bound, gaps |
| `OFUL-ELLIPTICAL-POTENTIAL` | elliptical potential / determinant growth bound | missing-leaf | `MLIB-CONVEX-LINALG`, `MLIB-MARTINGALE-STOCHASTIC` | positive semidefinite Gram matrices |

## Finite Bookkeeping Bridges

| Leaf id | Intended statement shape | Current status | Retrieval cards | Regularity contract |
| --- | --- | --- | --- | --- |
| `PULLCOUNT-RECURSIVE` | recursive pull count update lemmas | compiled-local | `LOCAL-LEAF-FINITE-BOOKKEEPING` | decidable arm equality |
| `PULLCOUNT-FINSET` | recursive `pullCount` equals filtered `Finset.range` cardinality | missing-leaf | `MLIB-FINSET-SUMS`, `MLIB-FINTYPE-FIN` | finite time horizon |
| `SUMREWARDS-FINSET` | recursive reward sum equals filtered `Finset.range` sum | missing-leaf | `MLIB-FINSET-SUMS` | additive zero law, selected reward |
| `PSEUDOREGRET-FINSET` | recursive pseudo-regret equals finite sum of gaps | missing-leaf | `MLIB-FINSET-SUMS`, `MLIB-ORDER-ALGEBRA` | finite horizon |
| `REGRET-PULLCOUNT` | finite regret sum reindexed by arm pull counts | theorem-card | `LML-BANDIT-REGRET-PULLCOUNT`, `MLIB-FINSET-SUMS` | finite arms |

## Algorithm Control Leaves

| Branch | Immediate leaves still needed before final theorem |
| --- | --- |
| ETC | exact round-robin counts, empirical mean denominator positivity, wrong-commit event, sub-Gaussian pairwise tail |
| UCB | positive initial counts, index width algebra, suboptimal-pull implication, bad-event union, expected pull-count bound |
| Thompson sampling | posterior action identity import/port, posterior confidence event, Bayes-regret integrability |
| EXP3 | importance-weighted estimator, potential telescope, learning-rate optimization |
| KL-UCB | Bernoulli KL API, monotonicity/inversion, change-of-measure, confidence set |
| Tsallis-INF/FTRL | simplex API, Tsallis regularizer, FTRL optimality, stability/penalty split, self-bounding conversion |
| OFUL/LinUCB | Gram matrix API, confidence ellipsoid, self-normalized concentration, elliptical potential |
| BwK | resource trace, budget stopping time, primal-dual comparison |
| RL/MDP | finite kernel, Bellman recursion, occupancy measure, optimism, episode regret telescope |

## Agent Rule

Do not pass a row label directly to a lower Lean worker.  Middle must turn it
into:

1. exact Lean statement;
2. local APIs/imports;
3. intended proof route;
4. hidden regularity contracts;
5. Mathlib/LML/local declarations searched;
6. fallback if the route fails repeatedly.

This is the minimum granularity needed for one leaf to fit inside a lower-agent
context window.
