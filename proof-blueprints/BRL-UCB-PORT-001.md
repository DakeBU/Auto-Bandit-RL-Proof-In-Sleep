# Proof Blueprint: BRL-UCB-PORT-001

Generated: `2026-06-26T17:44:23+00:00`

## Source Task

# Port the UCB regret proof route

Task id: `BRL-UCB-PORT-001`
Kind: `literaturePort`
Status: `planned`
Harness: `hierarchical`

## Goal

Build a local ABRL route for the finite stochastic UCB regret theorem, starting
from theorem cards and ending in either a compiled local theorem, a documented
import route, or a precise blocked ledger.

## Source

- Repository: [LeanMachineLearning/LML](https://github.com/LeanMachineLearning/LML)
- Upstream declaration: `Bandits.UCB.regret_le`
- Upstream module: `LeanMachineLearning.Online.Bandit.Algorithms.UCB`
- Local surface: `BanditRLProof/Algorithms/UCB.lean`
- Textbook/source cards: `TXT-BUBECK-CESABIANCHI-2012`, `TXT-LATTIMORE-SZEPESVARI-2020`
- Scenario card: `SCN-STOCHASTIC-FINITE`
- Mathlib cards: `MLIB-FINSET-SUMS`, `MLIB-ORDER-ALGEBRA`, `MLIB-REAL-LOG-SQRT`, `MLIB-PROBABILITY-INDEPENDENCE`

## Lean Target

```lean
-- staged targets:
-- BanditRLProof.UCB.obligationNames
-- future local theorem compatible with Bandits.UCB.regret_le
```

## Proof Obligations

- [ ] Decide `card-only`, `port`, or `dependency` route.
- [ ] Map UCB index, width, empirical mean, and pull-count definitions.
- [ ] Record sub-Gaussian tail dependencies.
- [ ] Record expected pull-count bound dependencies.
- [ ] Keep proof export clear that LML is theorem-card status until local closure.

## Mathlib-Ready Leaf Contract

Current leaf classes are recorded in
`proof-obligations/BRL-UCB-PORT-001.md`.  Generic order, algebra, positivity,
summability, and concentration infrastructure should be prepared as Mathlib
candidates.  UCB-specific wrappers should remain thin and should point to
those reusable leaves.  Do not change the proof route without a reviewer-visible
statement, hypothesis, or counterexample audit.

## Build Gate

```bash
python3 tools/bandit.py check
```


## Conversion Window Snapshot

# Conversion Window: UCB regret theorem-card route

Task id: `BRL-UCB-PORT-001`

Source card: `TXT-BUBECK-CESABIANCHI-2012`, `TXT-LATTIMORE-SZEPESVARI-2020`
Scenario card: `SCN-STOCHASTIC-FINITE`

## Natural-Language Statement

For a finite stochastic bandit with sub-Gaussian rewards, UCB chooses the arm
with maximal empirical mean plus a confidence width.  The expected regret is
bounded by a logarithmic pull-count term for suboptimal arms plus summable bad
event terms.

## Lean Mapping

| Source symbol | Meaning | Lean declaration | Type / role | Status |
| --- | --- | --- | --- | --- |
| `K` | number of arms | `K : Nat` | finite action count | typed |
| `A_t` | action at time `t` | `action : Nat -> Fin K` | action trace | local surface |
| `N_{t,a}` | pull count | `pullCount action a t` | count | compiled |
| `Delta_a` | arm gap | `FiniteBanditModel.gap` | rational gap surface | compiled |
| UCB width | confidence radius | `BanditRLProof.UCB.score` placeholder | index surface | typed contract |
| `Bandits.UCB.regret_le` | upstream theorem | LML theorem card | regret bound | theorem-card |

## Assumption Ledger

| Assumption | Lean status | Source | Blocking? |
| --- | --- | --- | --- |
| finite arms | compiled surface | ABRL core | no |
| reward means | compiled rational surface | ABRL core | no |
| sub-Gaussian rewards | theorem-card/obligation | LML/Mathlib route | yes |
| measurable action process | theorem-card/obligation | LML route | yes |
| expected pull-count bound | theorem-card/obligation | LML route | yes |

## Local API And Proof Route

| Leaf | Existing APIs/imports | Retrieval cards | Intended route | Pivot rule |
| --- | --- | --- | --- | --- |
| `UCB-INIT` | pull count recursion, finite arms | `MLIB-FINTYPE-FIN`, `MLIB-FINSET-SUMS` | prove positive counts after initialization | pivot only after positivity statement audit |
| `UCB-INDEX` | UCB score surface, future log/sqrt API | `MLIB-REAL-LOG-SQRT`, `MLIB-ORDER-ALGEBRA` | selected arm maximizes empirical mean plus width | pivot only after confidence-radius API audit |
| `UCB-GOOD` | index inequality, gap algebra | `MLIB-ORDER-ALGEBRA` | good event implies suboptimal arm pull-count bound | pivot only after checking gap/denominator hypotheses |
| `UCB-TAILS` | concentration theorem cards | `MLIB-PROBABILITY-INDEPENDENCE`, `MLIB-MEASURE-INTEGRAL` | one-sided tails plus union/summability | pivot only after sub-Gaussian and measurability contract audit |
| `UCB-REGRET` | regret decomposition, pull-count bound | `LML-UCB-REGRET`, `LML-BANDIT-REGRET-PULLCOUNT` | sum gap times expected pulls plus bad events | pivot only after source theorem mismatch is recorded |

## Proof-DAG

| Node | Interface | Dependencies | Owner | Lean declaration | Regularity contracts | Mathlib status | Gate | Status |
| --- | --- | --- | --- | --- | --- | --- | --- | --- |
| `UCB-INIT` | initial exploration gives positive counts | finite arms | lower Lean | TBD | finite actions, positive arm count, positive horizon | project-local with generic Nat leaves | build | planned |
| `UCB-INDEX` | selected arm maximizes UCB index | UCB definition | lower architect | TBD | positive counts, positive log argument, order/algebra facts | mathlib-candidate for generic order/algebra leaves | build | planned |
| `UCB-GOOD` | good event implies pull count bound | index algebra | lower Lean | TBD | positive gap, denominator positivity, bounded width | mathlib-candidate for generic inequality leaves | build | planned |
| `UCB-TAILS` | upper/lower tail bounds | concentration cards | lower retrieval | cited result | measurability, integrability, sub-Gaussian MGF, summability | theorem-card-only until imported or ported | memory | obligation |
| `UCB-REGRET` | regret bound from pull counts | regret decomposition | lower Lean | future theorem | all contracts above | project-local | build | blocked |

## Route Decision

Current route: `card-only` until a task explicitly aligns Mathlib/LML
dependencies or ports the needed concentration and probability lemmas.


## Obligation Snapshot

# Proof Obligations: BRL-UCB-PORT-001

Source card: `TXT-BUBECK-CESABIANCHI-2012`, `TXT-LATTIMORE-SZEPESVARI-2020`
Scenario card: `SCN-STOCHASTIC-FINITE`

| Node | Target | Dependencies | Local APIs/imports | Retrieval cards | Intended proof route | Regularity contracts | Mathlib status | Owner | Lean declaration | Gate | Status |
| --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- |
| `UCB-ROUTE` | choose card-only, port, or dependency route | task packet | LML theorem cards, ABRL core | `LML-UCB-REGRET`, `TXT-LATTIMORE-SZEPESVARI-2020` | keep route fixed until reviewer records pivot reason | theorem-card status, toolchain alignment | project-local decision | upper | no Lean declaration | memory | planned |
| `UCB-CORE` | verify ABRL finite trace and pseudo-regret surfaces | `BanditRLProof.Core`, `Regret`, `LeafLemmas` | pull counts, segment counts, reward sums, gap surface | `LOCAL-LEAF-FINITE-BOOKKEEPING`, `MLIB-FINSET-SUMS`, `MLIB-FINTYPE-FIN`, `LML-BANDIT-REGRET-PULLCOUNT` | compiled dependency-light bookkeeping | finite arms, horizon, rational mean model | project-local wrappers with generic arithmetic candidates | reviewer | `pullCount_le_time`, `pullCount_add_le`, `sumRewards_add_eq_of_forall_ne_between`, `pseudoRegret_add_eq_of_forall_gap_zero_between` | `python3 tools/bandit.py check` | compiled |
| `UCB-INDEX` | replace placeholder score with UCB width when dependency layer is selected | route decision | UCB score surface, logarithm/confidence API | `LOCAL-LEAF-ALGORITHM-WRAPPERS`, `MLIB-REAL-LOG-SQRT`, `MLIB-ORDER-ALGEBRA` | define width, prove selected arm maximizes index | positive counts, positive horizon, order/algebra facts | mathlib-candidate for generic order/algebra leaves | lower Lean | `UCB.score_eq_empiricalMean` | build | blocked |
| `UCB-CONC` | record or prove sub-Gaussian tail lemmas | concentration cards | LML/Mathlib concentration route | `MLIB-PROBABILITY-INDEPENDENCE`, `MLIB-MEASURE-INTEGRAL`, `MLIB-CONDITIONAL-EXPECTATION` | one-sided and union-bounded tail event control | measurability, integrability, sub-Gaussian MGF, summability | theorem-card-only until imported or ported | lower retrieval | TBD | memory/build | obligation |
| `UCB-FINAL` | local theorem compatible with `Bandits.UCB.regret_le` | all above | regret decomposition, pull-count bound, concentration cards | `LML-UCB-REGRET`, `MLIB-ASYMPTOTICS` | good-event pull-count bound plus bad-event summation | all upstream contracts above | project-local final theorem | lower Lean | TBD | build | blocked |

## Current Reviewer Note

The upstream LML theorem is a theorem card only.  Do not export it as an ABRL
local proof until the route is imported or ported.


## Relevant LML Theorem Cards

```json
[
  {
    "id": "LML-BANDIT-REGRET-GAP",
    "source": "LeanMachineLearning/LML",
    "declaration": "Bandits.regret_eq_sum_gap",
    "module": "LeanMachineLearning.Online.Bandit.Regret",
    "role": "Regret decomposition into a sum of action gaps.",
    "status": "theorem-card"
  },
  {
    "id": "LML-BANDIT-REGRET-PULLCOUNT",
    "source": "LeanMachineLearning/LML",
    "declaration": "Bandits.regret_eq_sum_pullCount_mul_gap",
    "module": "LeanMachineLearning.Online.Bandit.Regret",
    "role": "Regret decomposition through arm pull counts.",
    "status": "theorem-card"
  },
  {
    "id": "LML-ETC-REGRET",
    "source": "LeanMachineLearning/LML",
    "declaration": "Bandits.ETC.regret_le",
    "module": "LeanMachineLearning.Online.Bandit.Algorithms.ETC",
    "role": "Explore-Then-Commit expected regret bound.",
    "status": "theorem-card"
  },
  {
    "id": "LML-UCB-REGRET",
    "source": "LeanMachineLearning/LML",
    "declaration": "Bandits.UCB.regret_le",
    "module": "LeanMachineLearning.Online.Bandit.Algorithms.UCB",
    "role": "UCB logarithmic pull-count regret route.",
    "status": "theorem-card"
  },
  {
    "id": "LML-TS-POSTERIOR-ACTION",
    "source": "LeanMachineLearning/LML",
    "declaration": "Bandits.TS.hasCondDistrib_action",
    "module": "LeanMachineLearning.Online.Bandit.Algorithms.TS",
    "role": "Thompson sampling action distribution equals posterior best-action distribution.",
    "status": "theorem-card"
  },
  {
    "id": "LML-TS-BAYES-REGRET",
    "source": "LeanMachineLearning/LML",
    "declaration": "Bandits.integral_regret_le",
    "module": "LeanMachineLearning.Online.Bandit.Algorithms.Regret.BayesRegretTS",
    "role": "Bayesian regret upper bound for Thompson sampling.",
    "status": "theorem-card"
  }
]
```

## Relevant Mathlib Retrieval Cards

```json
[
  {
    "id": "MLIB-FINSET-SUMS",
    "source": "Mathlib",
    "module": "Mathlib.Data.Finset.Basic; Mathlib.Algebra.BigOperators.Fin",
    "docs": "https://leanprover-community.github.io/mathlib4_docs/Mathlib/Data/Finset/Basic.html",
    "query_terms": [
      "Finset.sum",
      "Finset.range",
      "sum_filter",
      "sum_congr",
      "card_filter"
    ],
    "role": "Finite sums, indicator partitions, pull-count decompositions, and arm/time reindexing.",
    "status": "import-candidate"
  },
  {
    "id": "MLIB-FINTYPE-FIN",
    "source": "Mathlib",
    "module": "Mathlib.Data.Fintype.Basic; Mathlib.Data.Fin.Basic",
    "docs": "https://leanprover-community.github.io/mathlib4_docs/Mathlib/Data/Fintype/Basic.html",
    "query_terms": [
      "Fintype.card",
      "Fin",
      "Finite",
      "Nonempty",
      "Fin.cast"
    ],
    "role": "Finite action spaces, nonempty arm sets, finite policies, and index coercions.",
    "status": "import-candidate"
  },
  {
    "id": "MLIB-ORDER-ALGEBRA",
    "source": "Mathlib",
    "module": "Mathlib.Algebra.Order.Field.Basic; Mathlib.Data.Real.Basic",
    "docs": "https://leanprover-community.github.io/mathlib4_docs/Mathlib/Algebra/Order/Field/Basic.html",
    "query_terms": [
      "linarith",
      "nlinarith",
      "div_le_iff",
      "mul_le_mul",
      "Nat.cast_pos"
    ],
    "role": "Gap nonnegativity, confidence-width algebra, positivity, and denominator side conditions.",
    "status": "import-candidate"
  },
  {
    "id": "MLIB-REAL-LOG-SQRT",
    "source": "Mathlib",
    "module": "Mathlib.Analysis.SpecialFunctions.Log.Basic; Mathlib.Data.Real.Sqrt",
    "docs": "https://leanprover-community.github.io/mathlib4_docs/Mathlib/Analysis/SpecialFunctions/Log/Basic.html",
    "query_terms": [
      "Real.log",
      "Real.sqrt",
      "sq_sqrt",
      "log_nonneg",
      "sqrt_le_sqrt"
    ],
    "role": "UCB radii, logarithmic regret simplification, and square-root confidence bounds.",
    "status": "import-candidate"
  },
  {
    "id": "MLIB-EXP-LOG-INEQUALITIES",
    "source": "Mathlib",
    "module": "Mathlib.Analysis.SpecialFunctions.Log.Basic",
    "docs": "https://leanprover-community.github.io/mathlib4_docs/Mathlib/Analysis/SpecialFunctions/Log/Basic.html",
    "query_terms": [
      "Real.exp",
      "Real.log",
      "exp_le_exp",
      "log_le_iff_le_exp",
      "rpow"
    ],
    "role": "Exponential-weight potentials, Chernoff routes, KL-UCB algebra, and learning-rate optimization.",
    "status": "import-candidate"
  },
  {
    "id": "MLIB-MEASURE-INTEGRAL",
    "source": "Mathlib",
    "module": "Mathlib.MeasureTheory.Integral.Bochner.Basic",
    "docs": "https://leanprover-community.github.io/mathlib4_docs/Mathlib/MeasureTheory/Integral/Bochner/Basic.html",
    "query_terms": [
      "Integrable",
      "lintegral",
      "integral",
      "AEStronglyMeasurable",
      "AEMeasurable"
    ],
    "role": "Expected regret, Bayesian regret, integrability contracts, and expectation linearity routes.",
    "status": "import-candidate"
  },
  {
    "id": "MLIB-PROBABILITY-INDEPENDENCE",
    "source": "Mathlib",
    "module": "Mathlib.Probability.Independence.Basic",
    "docs": "https://leanprover-community.github.io/mathlib4_docs/Mathlib/Probability/Independence/Basic.html",
    "query_terms": [
      "IndepFun",
      "iIndepFun",
      "IndepSet",
      "IdentDistrib",
      "iid"
    ],
    "role": "IID rewards, product event decompositions, Hoeffding-style assumptions, and theorem contracts.",
    "status": "import-candidate"
  },
  {
    "id": "MLIB-CONDITIONAL-EXPECTATION",
    "source": "Mathlib",
    "module": "Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic",
    "docs": "https://leanprover-community.github.io/mathlib4_docs/Mathlib/MeasureTheory/Function/ConditionalExpectation/Basic.html",
    "query_terms": [
      "condexp",
      "filtration",
      "adapted",
      "martingale",
      "stoppingTime"
    ],
    "role": "Adaptive rewards, Thompson posterior identities, martingale concentration, and RL filtrations.",
    "status": "import-candidate"
  },
  {
    "id": "MLIB-MARTINGALE-STOCHASTIC",
    "source": "Mathlib",
    "module": "Mathlib.Probability.Martingale.Basic; Mathlib.Probability.Notation",
    "docs": "https://leanprover-community.github.io/mathlib4_docs/Mathlib/Probability/Martingale/Basic.html",
    "query_terms": [
      "Martingale",
      "Submartingale",
      "Supermartingale",
      "filtration",
      "stoppingTime"
    ],
    "role": "Self-normalized processes, optional-stopping surfaces, delayed feedback, and finite-horizon RL regret.",
    "status": "import-candidate"
  },
  {
    "id": "MLIB-PROBABILITY-KERNEL",
    "source": "Mathlib",
    "module": "Mathlib.Probability.Kernel.Basic",
    "docs": "https://leanprover-community.github.io/mathlib4_docs/Mathlib/Probability/Kernel/Basic.html",
    "query_terms": [
      "Kernel",
      "MarkovKernel",
      "bind",
      "comp",
      "prod"
    ],
    "role": "Reward kernels, posterior kernels, finite-horizon MDP surfaces, and policy-induced laws.",
    "status": "import-candidate"
  },
  {
    "id": "MLIB-ASYMPTOTICS",
    "source": "Mathlib",
    "module": "Mathlib.Analysis.Asymptotics.Asymptotics",
    "docs": "https://leanprover-community.github.io/mathlib4_docs/Mathlib/Analysis/Asymptotics/Asymptotics.html",
    "query_terms": [
      "Asymptotics.IsBigO",
      "IsTheta",
      "Eventually",
      "Filter.atTop"
    ],
    "role": "Asymptotic optimality, logarithmic regret, minimax rates, and exported theorem statements.",
    "status": "import-candidate"
  },
  {
    "id": "MLIB-CONVEX-LINALG",
    "source": "Mathlib",
    "module": "Mathlib.Analysis.Convex.Basic; Mathlib.LinearAlgebra.Matrix",
    "docs": "https://leanprover-community.github.io/mathlib4_docs/Mathlib/Analysis/Convex/Basic.html",
    "query_terms": [
      "Convex",
      "Matrix",
      "inner",
      "norm",
      "IsBounded",
      "projection"
    ],
    "role": "Linear bandits, confidence ellipsoids, least-squares design, and convex action sets.",
    "status": "import-candidate"
  },
  {
    "id": "MLIB-METRIC-TOPOLOGY",
    "source": "Mathlib",
    "module": "Mathlib.Topology.MetricSpace.Basic",
    "docs": "https://leanprover-community.github.io/mathlib4_docs/Mathlib/Topology/MetricSpace/Basic.html",
    "query_terms": [
      "Metric.ball",
      "Metric.closedBall",
      "LipschitzWith",
      "TotallyBounded",
      "diam"
    ],
    "role": "Lipschitz/continuum bandits, covering arguments, nearest-neighbor policies, and metric action spaces.",
    "status": "import-candidate"
  }
]
```

## Bandit Textbook Cards

```json
[
  {
    "id": "TXT-BUBECK-CESABIANCHI-2012",
    "title": "Regret Analysis of Stochastic and Nonstochastic Multi-armed Bandit Problems",
    "authors": "S\u00e9bastien Bubeck; Nicol\u00f2 Cesa-Bianchi",
    "source": "https://arxiv.org/abs/1204.5721",
    "branches": [
      "iid finite-arm",
      "adversarial finite-arm",
      "contextual bandits",
      "lower bounds"
    ],
    "proof_roots": [
      "regret decomposition",
      "UCB",
      "EXP3",
      "minimax lower bounds"
    ],
    "memory_status": "survey-card"
  },
  {
    "id": "TXT-LATTIMORE-SZEPESVARI-2020",
    "title": "Bandit Algorithms",
    "authors": "Tor Lattimore; Csaba Szepesv\u00e1ri",
    "source": "https://tor-lattimore.com/downloads/book/book.pdf",
    "branches": [
      "probability and concentration",
      "finite stochastic arms",
      "adversarial finite arms",
      "lower bounds",
      "contextual and linear bandits",
      "adversarial linear bandits"
    ],
    "proof_roots": [
      "ETC",
      "UCB",
      "MOSS",
      "KL-UCB",
      "EXP3",
      "linear UCB",
      "least-squares confidence"
    ],
    "memory_status": "textbook-card"
  },
  {
    "id": "TXT-SLIVKINS-2019-2024",
    "title": "Introduction to Multi-Armed Bandits",
    "authors": "Aleksandrs Slivkins",
    "source": "https://arxiv.org/abs/1904.07272",
    "branches": [
      "IID rewards",
      "Bayesian priors",
      "Lipschitz rewards",
      "adversarial rewards",
      "contextual bandits",
      "bandits with knapsacks",
      "bandits and agents"
    ],
    "proof_roots": [
      "Bayesian regret",
      "similarity/metric bandits",
      "BwK",
      "incentive-compatible exploration"
    ],
    "memory_status": "textbook-card"
  }
]
```

## Bandit Paper Cards

```json
[
  {
    "id": "PPR-AUER-CBF-2002-UCB1",
    "title": "Finite-time Analysis of the Multiarmed Bandit Problem",
    "authors": "Peter Auer; Nicol\u00f2 Cesa-Bianchi; Paul Fischer",
    "source": "https://doi.org/10.1023/A:1013689704352",
    "scenarios": [
      "SCN-STOCHASTIC-FINITE"
    ],
    "proof_roots": [
      "UCB1",
      "finite-time logarithmic regret",
      "gap-dependent regret"
    ],
    "lean_leaf_families": [
      "pull-count threshold",
      "good event split",
      "tail summability"
    ],
    "memory_status": "paper-card"
  },
  {
    "id": "PPR-AUER-CFS-2002-EXP3",
    "title": "The Nonstochastic Multiarmed Bandit Problem",
    "authors": "Peter Auer; Nicol\u00f2 Cesa-Bianchi; Yoav Freund; Robert E. Schapire",
    "source": "https://doi.org/10.1137/S0097539701398375",
    "scenarios": [
      "SCN-ADVERSARIAL-FINITE"
    ],
    "proof_roots": [
      "EXP3",
      "exponential weights",
      "importance-weighted loss"
    ],
    "lean_leaf_families": [
      "potential inequality",
      "unbiased estimator",
      "learning-rate optimization"
    ],
    "memory_status": "paper-card"
  },
  {
    "id": "PPR-GARIVIER-CAPPE-2011-KLUCB",
    "title": "The KL-UCB Algorithm for Bounded Stochastic Bandits and Beyond",
    "authors": "Aur\u00e9lien Garivier; Olivier Capp\u00e9",
    "source": "https://arxiv.org/abs/1102.2490",
    "scenarios": [
      "SCN-STOCHASTIC-FINITE"
    ],
    "proof_roots": [
      "KL-UCB",
      "bounded stochastic bandits",
      "Bernoulli KL routes"
    ],
    "lean_leaf_families": [
      "KL monotonicity",
      "confidence inversion",
      "bounded reward event"
    ],
    "memory_status": "paper-card"
  },
  {
    "id": "PPR-AGRAWAL-GOYAL-2011-TS",
    "title": "Analysis of Thompson Sampling for the Multi-armed Bandit Problem",
    "authors": "Shipra Agrawal; Navin Goyal",
    "source": "https://arxiv.org/abs/1111.1797",
    "scenarios": [
      "SCN-STOCHASTIC-FINITE",
      "SCN-BAYESIAN-POSTERIOR"
    ],
    "proof_roots": [
      "Thompson sampling",
      "posterior samples",
      "Bayesian regret"
    ],
    "lean_leaf_families": [
      "posterior action identity",
      "Beta-Bernoulli update",
      "probability matching"
    ],
    "memory_status": "paper-card"
  },
  {
    "id": "PPR-ABBASI-YADKORI-2011-SELF-NORMALIZED",
    "title": "Online Least Squares Estimation with Self-Normalized Processes: An Application to Bandit Problems",
    "authors": "Yasin Abbasi-Yadkori; D\u00e1vid P\u00e1l; Csaba Szepesv\u00e1ri",
    "source": "https://arxiv.org/abs/1102.2670",
    "scenarios": [
      "SCN-LINEAR-GLM"
    ],
    "proof_roots": [
      "self-normalized concentration",
      "linear least squares",
      "OFUL confidence"
    ],
    "lean_leaf_families": [
      "Gram matrix monotonicity",
      "elliptical potential",
      "martingale vector bound"
    ],
    "memory_status": "paper-card"
  },
  {
    "id": "PPR-LI-CHU-LANGFORD-SCHAPIRE-2010-LINUCB",
    "title": "A Contextual-Bandit Approach to Personalized News Article Recommendation",
    "authors": "Lihong Li; Wei Chu; John Langford; Robert E. Schapire",
    "source": "https://doi.org/10.1145/1772690.1772758",
    "scenarios": [
      "SCN-CONTEXTUAL",
      "SCN-LINEAR-GLM",
      "SCN-LLM-REC-SYS"
    ],
    "proof_roots": [
      "LinUCB",
      "offline evaluation",
      "contextual reward model"
    ],
    "lean_leaf_families": [
      "feature-vector reward",
      "argmax policy",
      "context-history interface"
    ],
    "memory_status": "paper-card"
  },
  {
    "id": "PPR-AZAR-OSBAND-MUNOS-2017-UCBVI",
    "title": "Minimax Regret Bounds for Reinforcement Learning",
    "authors": "Mohammad Gheshlaghi Azar; Ian Osband; R\u00e9mi Munos",
    "source": "https://arxiv.org/abs/1703.05449",
    "scenarios": [
      "SCN-RL-MDP"
    ],
    "proof_roots": [
      "UCB-VI",
      "finite-horizon MDP regret",
      "Bellman optimism"
    ],
    "lean_leaf_families": [
      "finite kernels",
      "Bellman recursion",
      "episode regret telescope"
    ],
    "memory_status": "paper-card"
  },
  {
    "id": "PPR-BADANIDIYURU-KLEINBERG-SLIVKINS-2013-BWK",
    "title": "Bandits with Knapsacks",
    "authors": "Ashwinkumar Badanidiyuru; Robert Kleinberg; Aleksandrs Slivkins",
    "source": "https://arxiv.org/abs/1305.2545",
    "scenarios": [
      "SCN-RESOURCE-CONSTRAINED"
    ],
    "proof_roots": [
      "bandits with knapsacks",
      "primal-dual resource allocation",
      "budgeted regret"
    ],
    "lean_leaf_families": [
      "resource consumption trace",
      "budget stopping time",
      "Lagrangian comparison"
    ],
    "memory_status": "paper-card"
  },
  {
    "id": "PPR-IJCAI-2018-DUELING-SURVEY",
    "title": "Advancements in Dueling Bandits",
    "authors": "Yanan Sui; Masrour Zoghi; Katja Hofmann; Yisong Yue",
    "source": "https://doi.org/10.24963/ijcai.2018/776",
    "scenarios": [
      "SCN-DUELING-PREFERENCE"
    ],
    "proof_roots": [
      "dueling bandits",
      "preference matrices",
      "Condorcet/Borda regret"
    ],
    "lean_leaf_families": [
      "pairwise action relation",
      "preference probability",
      "winner notion"
    ],
    "memory_status": "survey-card"
  },
  {
    "id": "PPR-AAAI-2020-SAFE-LINEAR-STOCHASTIC",
    "title": "Safe Linear Stochastic Bandits",
    "authors": "Kia Khezeli; Eilyan Bitar",
    "source": "https://doi.org/10.1609/aaai.v34i06.6581",
    "scenarios": [
      "SCN-CONSTRAINTS"
    ],
    "proof_roots": [
      "safe linear bandits",
      "constraint confidence",
      "safe action set"
    ],
    "lean_leaf_families": [
      "baseline feasibility",
      "safe-set monotonicity",
      "constraint regret"
    ],
    "memory_status": "paper-card"
  },
  {
    "id": "PPR-AAAI-2016-DP-MAB",
    "title": "Algorithms for Differentially Private Multi-Armed Bandits",
    "authors": "Aristide Tossou; Christos Dimitrakakis",
    "source": "https://doi.org/10.1609/aaai.v30i1.10212",
    "scenarios": [
      "SCN-CONSTRAINTS"
    ],
    "proof_roots": [
      "differential privacy",
      "private UCB",
      "privacy-regret tradeoff"
    ],
    "lean_leaf_families": [
      "noise distribution contract",
      "privacy composition",
      "private confidence radius"
    ],
    "memory_status": "paper-card"
  },
  {
    "id": "PPR-FAT-2018-MERITOCRATIC-FAIRNESS",
    "title": "Meritocratic Fairness for Infinite and Contextual Bandits",
    "authors": "Matthew Joseph; Michael Kearns; Jamie Morgenstern; Seth Neel; Aaron Roth",
    "source": "https://doi.org/10.1145/3278721.3278764",
    "scenarios": [
      "SCN-CONSTRAINTS",
      "SCN-CONTEXTUAL"
    ],
    "proof_roots": [
      "fair contextual bandits",
      "meritocratic fairness",
      "infinite arms"
    ],
    "lean_leaf_families": [
      "fairness invariant",
      "action dominance relation",
      "contextual policy constraint"
    ],
    "memory_status": "paper-card"
  },
  {
    "id": "PPR-AAAI-2021-FEDERATED-MAB",
    "title": "Federated Multi-Armed Bandits",
    "authors": "Chengshuai Shi; Cong Shen",
    "source": "https://doi.org/10.1609/aaai.v35i11.17156",
    "scenarios": [
      "SCN-FEDERATED-DISTRIBUTED"
    ],
    "proof_roots": [
      "federated MAB",
      "client aggregation",
      "communication-efficient regret"
    ],
    "lean_leaf_families": [
      "client-indexed traces",
      "aggregation invariant",
      "communication round count"
    ],
    "memory_status": "paper-card"
  },
  {
    "id": "PPR-FEDERATED-NEURAL-BANDITS-2022",
    "title": "Federated Neural Bandits",
    "authors": "Federated neural bandit authors",
    "source": "https://arxiv.org/abs/2205.14309",
    "scenarios": [
      "SCN-FEDERATED-DISTRIBUTED",
      "SCN-LLM-REC-SYS"
    ],
    "proof_roots": [
      "federated neural bandits",
      "nonlinear contextual bandits",
      "distributed representation learning"
    ],
    "lean_leaf_families": [
      "client embedding contract",
      "nonlinear confidence surrogate",
      "federated update trace"
    ],
    "memory_status": "paper-card"
  }
]
```

## Bandit Scenario Cards

```json
[
  {
    "id": "SCN-STOCHASTIC-FINITE",
    "name": "finite stochastic bandits",
    "core_algorithms": [
      "ETC",
      "UCB",
      "MOSS",
      "KL-UCB",
      "Thompson sampling"
    ],
    "leaf_families": [
      "pull-count algebra",
      "gap decomposition",
      "sub-Gaussian tails",
      "Bernoulli KL"
    ],
    "mathlib_needs": [
      "MLIB-FINSET-SUMS",
      "MLIB-ORDER-ALGEBRA",
      "MLIB-PROBABILITY-INDEPENDENCE"
    ],
    "source_cards": [
      "TXT-BUBECK-CESABIANCHI-2012",
      "TXT-LATTIMORE-SZEPESVARI-2020",
      "PPR-AUER-CBF-2002-UCB1",
      "PPR-GARIVIER-CAPPE-2011-KLUCB",
      "PPR-AGRAWAL-GOYAL-2011-TS"
    ],
    "status": "seeded"
  },
  {
    "id": "SCN-BAYESIAN-POSTERIOR",
    "name": "Bayesian and posterior-sampling bandits",
    "core_algorithms": [
      "Thompson sampling",
      "Bayes-UCB",
      "posterior sampling with priors"
    ],
    "leaf_families": [
      "posterior kernels",
      "Bayesian regret",
      "probability matching",
      "prior/posterior update contracts"
    ],
    "mathlib_needs": [
      "MLIB-PROBABILITY-KERNEL",
      "MLIB-CONDITIONAL-EXPECTATION",
      "MLIB-MEASURE-INTEGRAL"
    ],
    "source_cards": [
      "TXT-SLIVKINS-2019-2024",
      "PPR-AGRAWAL-GOYAL-2011-TS"
    ],
    "status": "planned"
  },
  {
    "id": "SCN-ADVERSARIAL-FINITE",
    "name": "adversarial finite-arm bandits",
    "core_algorithms": [
      "EXP3",
      "EXP3-IX",
      "FTRL/OMD variants"
    ],
    "leaf_families": [
      "importance-weighted estimators",
      "exponential weights",
      "potential inequalities"
    ],
    "mathlib_needs": [
      "MLIB-FINSET-SUMS",
      "MLIB-EXP-LOG-INEQUALITIES",
      "MLIB-ORDER-ALGEBRA"
    ],
    "source_cards": [
      "TXT-BUBECK-CESABIANCHI-2012",
      "TXT-LATTIMORE-SZEPESVARI-2020",
      "PPR-AUER-CFS-2002-EXP3"
    ],
    "status": "planned"
  },
  {
    "id": "SCN-CONTEXTUAL",
    "name": "contextual bandits",
    "core_algorithms": [
      "EXP4",
      "LinUCB",
      "Thompson contextual variants"
    ],
    "leaf_families": [
      "policy classes",
      "expert advice",
      "context measurability",
      "regret against policies"
    ],
    "mathlib_needs": [
      "MLIB-MEASURE-INTEGRAL",
      "MLIB-PROBABILITY-KERNEL",
      "MLIB-FINSET-SUMS"
    ],
    "source_cards": [
      "TXT-LATTIMORE-SZEPESVARI-2020",
      "PPR-LI-CHU-LANGFORD-SCHAPIRE-2010-LINUCB",
      "PPR-FAT-2018-MERITOCRATIC-FAIRNESS"
    ],
    "status": "planned"
  },
  {
    "id": "SCN-LINEAR-GLM",
    "name": "linear and generalized-linear bandits",
    "core_algorithms": [
      "LinUCB",
      "OFUL",
      "linear Thompson sampling",
      "GLM-UCB"
    ],
    "leaf_families": [
      "least squares",
      "self-normalized martingales",
      "ellipsoid confidence",
      "determinant algebra"
    ],
    "mathlib_needs": [
      "MLIB-CONVEX-LINALG",
      "MLIB-MARTINGALE-STOCHASTIC",
      "MLIB-REAL-LOG-SQRT"
    ],
    "source_cards": [
      "TXT-LATTIMORE-SZEPESVARI-2020",
      "PPR-ABBASI-YADKORI-2011-SELF-NORMALIZED",
      "PPR-LI-CHU-LANGFORD-SCHAPIRE-2010-LINUCB"
    ],
    "status": "planned"
  },
  {
    "id": "SCN-LIPSCHITZ-METRIC",
    "name": "Lipschitz, continuum, and metric bandits",
    "core_algorithms": [
      "zooming",
      "hierarchical optimistic optimization",
      "nearest-neighbor UCB"
    ],
    "leaf_families": [
      "metric balls",
      "covering numbers",
      "Lipschitz reward contracts",
      "near-optimality dimension"
    ],
    "mathlib_needs": [
      "MLIB-METRIC-TOPOLOGY",
      "MLIB-FINSET-SUMS",
      "MLIB-ASYMPTOTICS"
    ],
    "source_cards": [
      "TXT-SLIVKINS-2019-2024"
    ],
    "status": "planned"
  },
  {
    "id": "SCN-PURE-EXPLORATION",
    "name": "pure exploration and best-arm identification",
    "core_algorithms": [
      "successive elimination",
      "LUCB",
      "Track-and-Stop"
    ],
    "leaf_families": [
      "stopping rules",
      "fixed-confidence events",
      "sample complexity",
      "change-of-measure"
    ],
    "mathlib_needs": [
      "MLIB-CONDITIONAL-EXPECTATION",
      "MLIB-MEASURE-INTEGRAL",
      "MLIB-ASYMPTOTICS"
    ],
    "source_cards": [
      "TXT-LATTIMORE-SZEPESVARI-2020",
      "TXT-SLIVKINS-2019-2024"
    ],
    "status": "planned"
  },
  {
    "id": "SCN-COMBINATORIAL",
    "name": "combinatorial and semi-bandit feedback",
    "core_algorithms": [
      "Combinatorial UCB",
      "semi-bandit Thompson",
      "matroid/knapsack variants"
    ],
    "leaf_families": [
      "set-valued actions",
      "component rewards",
      "oracle contracts",
      "semi-bandit decomposition"
    ],
    "mathlib_needs": [
      "MLIB-FINSET-SUMS",
      "MLIB-CONVEX-LINALG",
      "MLIB-ORDER-ALGEBRA"
    ],
    "source_cards": [
      "TXT-LATTIMORE-SZEPESVARI-2020"
    ],
    "status": "planned"
  },
  {
    "id": "SCN-RESOURCE-CONSTRAINED",
    "name": "resource-constrained bandits and bandits with knapsacks",
    "core_algorithms": [
      "BwK",
      "primal-dual UCB",
      "budgeted Thompson sampling"
    ],
    "leaf_families": [
      "resource-consumption traces",
      "budget stopping times",
      "primal-dual comparison",
      "constraint regret"
    ],
    "mathlib_needs": [
      "MLIB-FINSET-SUMS",
      "MLIB-ORDER-ALGEBRA",
      "MLIB-MEASURE-INTEGRAL"
    ],
    "source_cards": [
      "TXT-SLIVKINS-2019-2024",
      "PPR-BADANIDIYURU-KLEINBERG-SLIVKINS-2013-BWK"
    ],
    "status": "planned"
  },
  {
    "id": "SCN-DUELING-PREFERENCE",
    "name": "dueling, preference, and ranking bandits",
    "core_algorithms": [
      "RUCB variants",
      "Borda/Condorcet algorithms",
      "preference-based elimination"
    ],
    "leaf_families": [
      "pairwise preference matrices",
      "winner notions",
      "comparison regret",
      "partial-monitoring bridge"
    ],
    "mathlib_needs": [
      "MLIB-FINSET-SUMS",
      "MLIB-ORDER-ALGEBRA",
      "MLIB-PROBABILITY-INDEPENDENCE"
    ],
    "source_cards": [
      "PPR-IJCAI-2018-DUELING-SURVEY"
    ],
    "status": "planned"
  },
  {
    "id": "SCN-NONSTATIONARY",
    "name": "nonstationary, rotting, and drifting bandits",
    "core_algorithms": [
      "sliding-window UCB",
      "discounted UCB",
      "change-point UCB"
    ],
    "leaf_families": [
      "dynamic regret",
      "variation budgets",
      "windowed concentration",
      "change detection"
    ],
    "mathlib_needs": [
      "MLIB-FINSET-SUMS",
      "MLIB-PROBABILITY-INDEPENDENCE",
      "MLIB-ASYMPTOTICS"
    ],
    "source_cards": [
      "TXT-SLIVKINS-2019-2024"
    ],
    "status": "planned"
  },
  {
    "id": "SCN-HEAVY-TAILED-ROBUST",
    "name": "heavy-tailed, corrupted, and robust bandits",
    "core_algorithms": [
      "median-of-means UCB",
      "trimmed-mean UCB",
      "corruption-robust contextual bandits"
    ],
    "leaf_families": [
      "robust mean estimator",
      "moment assumptions",
      "truncation event",
      "corruption budget"
    ],
    "mathlib_needs": [
      "MLIB-MEASURE-INTEGRAL",
      "MLIB-ORDER-ALGEBRA",
      "MLIB-ASYMPTOTICS"
    ],
    "source_cards": [
      "TXT-LATTIMORE-SZEPESVARI-2020"
    ],
    "status": "watchlist"
  },
  {
    "id": "SCN-DELAYED-BATCHED",
    "name": "delayed-feedback, batched, and asynchronous bandits",
    "core_algorithms": [
      "delayed EXP3",
      "batched UCB",
      "asynchronous Thompson sampling"
    ],
    "leaf_families": [
      "delay queues",
      "pending feedback",
      "batch regret",
      "asynchronous filtration"
    ],
    "mathlib_needs": [
      "MLIB-FINSET-SUMS",
      "MLIB-MARTINGALE-STOCHASTIC",
      "MLIB-CONDITIONAL-EXPECTATION"
    ],
    "source_cards": [
      "TXT-BUBECK-CESABIANCHI-2012"
    ],
    "status": "planned"
  },
  {
    "id": "SCN-CONSTRAINTS",
    "name": "safe, conservative, fair, private, and constrained bandits",
    "core_algorithms": [
      "conservative UCB",
      "safe-UCB",
      "fair contextual bandits",
      "private UCB"
    ],
    "leaf_families": [
      "baseline regret",
      "constraint budgets",
      "privacy noise",
      "fairness invariants"
    ],
    "mathlib_needs": [
      "MLIB-MEASURE-INTEGRAL",
      "MLIB-ORDER-ALGEBRA",
      "MLIB-PROBABILITY-INDEPENDENCE"
    ],
    "source_cards": [
      "PPR-AAAI-2020-SAFE-LINEAR-STOCHASTIC",
      "PPR-AAAI-2016-DP-MAB",
      "PPR-FAT-2018-MERITOCRATIC-FAIRNESS"
    ],
    "status": "planned"
  },
  {
    "id": "SCN-FEDERATED-DISTRIBUTED",
    "name": "federated and distributed bandits",
    "core_algorithms": [
      "Fed-UCB",
      "personalized federated bandits",
      "Byzantine-robust UCB"
    ],
    "leaf_families": [
      "client aggregation",
      "heterogeneity",
      "communication rounds",
      "robust mean estimates"
    ],
    "mathlib_needs": [
      "MLIB-FINSET-SUMS",
      "MLIB-MEASURE-INTEGRAL",
      "MLIB-PROBABILITY-INDEPENDENCE"
    ],
    "source_cards": [
      "PPR-AAAI-2021-FEDERATED-MAB",
      "PPR-FEDERATED-NEURAL-BANDITS-2022"
    ],
    "status": "planned"
  },
  {
    "id": "SCN-RL-MDP",
    "name": "finite-horizon RL and MDP regret",
    "core_algorithms": [
      "UCB-VI",
      "posterior sampling RL",
      "optimism under uncertainty",
      "Bellman backups"
    ],
    "leaf_families": [
      "finite kernels",
      "policies",
      "Bellman recursion",
      "occupancy measures",
      "episode regret"
    ],
    "mathlib_needs": [
      "MLIB-PROBABILITY-KERNEL",
      "MLIB-CONDITIONAL-EXPECTATION",
      "MLIB-MEASURE-INTEGRAL"
    ],
    "source_cards": [
      "TXT-SLIVKINS-2019-2024",
      "PPR-AZAR-OSBAND-MUNOS-2017-UCBVI"
    ],
    "status": "planned"
  },
  {
    "id": "SCN-LLM-REC-SYS",
    "name": "LLM, recommender, and neural bandits",
    "core_algorithms": [
      "neural contextual bandits",
      "bandit prompt optimization",
      "LLM-assisted priors"
    ],
    "leaf_families": [
      "offline-to-online priors",
      "context embeddings",
      "model-selection regret",
      "adaptive response generation"
    ],
    "mathlib_needs": [
      "MLIB-MEASURE-INTEGRAL",
      "MLIB-PROBABILITY-KERNEL",
      "MLIB-CONVEX-LINALG"
    ],
    "source_cards": [
      "PPR-LI-CHU-LANGFORD-SCHAPIRE-2010-LINUCB",
      "PPR-FEDERATED-NEURAL-BANDITS-2022"
    ],
    "status": "watchlist"
  }
]
```

## Local Compiled Leaf Cards

```json
[
  {
    "id": "LOCAL-LEAF-FINITE-BOOKKEEPING",
    "module": "BanditRLProof.LeafLemmas",
    "status": "leanCompiled",
    "declarations": [
      "pullCount_one",
      "pullCount_succ_of_eq",
      "pullCount_succ_of_ne",
      "pullCount_le_succ",
      "pullCount_succ_le_succ",
      "pullCount_mono",
      "pullCount_le_time",
      "pullCount_add_le",
      "pullCount_le_add",
      "pullCount_eq_zero_of_forall_ne",
      "pullCount_eq_time_of_forall_eq",
      "pullCount_pos_of_eq_before",
      "pullCount_const_self",
      "pullCount_const_of_ne",
      "pullCount_add_eq_of_forall_ne_between",
      "pullCount_add_eq_add_of_forall_eq_between",
      "sumRewards_succ_of_eq",
      "sumRewards_succ_of_ne",
      "sumRewards_eq_zero_of_forall_ne",
      "sumRewards_const_of_ne",
      "sumRewards_add_eq_of_forall_ne_between",
      "FiniteBanditModel.bestMean_eq_mean_bestArm",
      "FiniteBanditModel.gap_of_ne_bestArm",
      "pseudoRegret_one",
      "pseudoRegret_succ_of_bestArm",
      "pseudoRegret_succ_of_gap_zero",
      "pseudoRegret_eq_zero_of_forall_bestArm",
      "pseudoRegret_eq_zero_of_forall_gap_zero",
      "pseudoRegret_const_bestArm",
      "pseudoRegret_const_of_gap_zero",
      "pseudoRegret_add_eq_of_forall_bestArm_between",
      "pseudoRegret_add_eq_of_forall_gap_zero_between"
    ],
    "role": "Compiled dependency-light bridge leaves for pull counts, segment counts, reward sums, gaps, and pseudo-regret.",
    "mathlib_routes": [
      "MLIB-FINSET-SUMS",
      "MLIB-FINTYPE-FIN",
      "MLIB-ORDER-ALGEBRA"
    ]
  },
  {
    "id": "LOCAL-LEAF-ALGORITHM-WRAPPERS",
    "module": "BanditRLProof.Algorithms.ETC; BanditRLProof.Algorithms.UCB",
    "status": "leanCompiled",
    "declarations": [
      "ETC.exploreArm_eq_of_mod_eq",
      "UCB.score_eq_empiricalMean"
    ],
    "role": "Compiled dependency-light wrapper leaves for current ETC and UCB surfaces.",
    "mathlib_routes": [
      "MLIB-FINTYPE-FIN",
      "MLIB-ORDER-ALGEBRA"
    ]
  }
]
```

## Local Lean Declaration Index

```json
[
  {
    "kind": "structure",
    "name": "Spec",
    "full_name": "BanditRLProof.ETC.Spec",
    "file": "BanditRLProof/Algorithms/ETC.lean",
    "line": 11,
    "statement": "structure Spec (K : Nat) where"
  },
  {
    "kind": "def",
    "name": "exploreArm",
    "full_name": "BanditRLProof.ETC.exploreArm",
    "file": "BanditRLProof/Algorithms/ETC.lean",
    "line": 16,
    "statement": "def exploreArm (spec : Spec K) (t : Nat) : Fin K :="
  },
  {
    "kind": "theorem",
    "name": "exploreArm_val",
    "full_name": "BanditRLProof.ETC.exploreArm_val",
    "file": "BanditRLProof/Algorithms/ETC.lean",
    "line": 19,
    "statement": "@[simp] theorem exploreArm_val (spec : Spec K) (t : Nat) : (exploreArm spec t).val = t % K"
  },
  {
    "kind": "theorem",
    "name": "exploreArm_eq_of_mod_eq",
    "full_name": "BanditRLProof.ETC.exploreArm_eq_of_mod_eq",
    "file": "BanditRLProof/Algorithms/ETC.lean",
    "line": 22,
    "statement": "theorem exploreArm_eq_of_mod_eq (spec : Spec K) {s t : Nat} (h : s % K = t % K) : exploreArm spec s = exploreArm spec t"
  },
  {
    "kind": "structure",
    "name": "CommitOracle",
    "full_name": "BanditRLProof.ETC.CommitOracle",
    "file": "BanditRLProof/Algorithms/ETC.lean",
    "line": 29,
    "statement": "structure CommitOracle (K : Nat) where"
  },
  {
    "kind": "def",
    "name": "obligationNames",
    "full_name": "BanditRLProof.ETC.obligationNames",
    "file": "BanditRLProof/Algorithms/ETC.lean",
    "line": 34,
    "statement": "def obligationNames : List String :="
  },
  {
    "kind": "structure",
    "name": "PriorSketch",
    "full_name": "BanditRLProof.Thompson.PriorSketch",
    "file": "BanditRLProof/Algorithms/Thompson.lean",
    "line": 11,
    "statement": "structure PriorSketch where"
  },
  {
    "kind": "def",
    "name": "obligationNames",
    "full_name": "BanditRLProof.Thompson.obligationNames",
    "file": "BanditRLProof/Algorithms/Thompson.lean",
    "line": 18,
    "statement": "def obligationNames : List String :="
  },
  {
    "kind": "structure",
    "name": "Spec",
    "full_name": "BanditRLProof.UCB.Spec",
    "file": "BanditRLProof/Algorithms/UCB.lean",
    "line": 11,
    "statement": "structure Spec (K : Nat) where"
  },
  {
    "kind": "structure",
    "name": "IndexState",
    "full_name": "BanditRLProof.UCB.IndexState",
    "file": "BanditRLProof/Algorithms/UCB.lean",
    "line": 16,
    "statement": "structure IndexState (K : Nat) where"
  },
  {
    "kind": "def",
    "name": "score",
    "full_name": "BanditRLProof.UCB.score",
    "file": "BanditRLProof/Algorithms/UCB.lean",
    "line": 26,
    "statement": "def score (_spec : Spec K) (state : IndexState K) (arm : Fin K) : Rat :="
  },
  {
    "kind": "theorem",
    "name": "score_eq_empiricalMean",
    "full_name": "BanditRLProof.UCB.score_eq_empiricalMean",
    "file": "BanditRLProof/Algorithms/UCB.lean",
    "line": 29,
    "statement": "@[simp] theorem score_eq_empiricalMean (spec : Spec K) (state : IndexState K) (arm : Fin K) : score spec state arm = state.empiricalMean arm"
  },
  {
    "kind": "def",
    "name": "obligationNames",
    "full_name": "BanditRLProof.UCB.obligationNames",
    "file": "BanditRLProof/Algorithms/UCB.lean",
    "line": 34,
    "statement": "def obligationNames : List String :="
  },
  {
    "kind": "inductive",
    "name": "HarnessProfile",
    "full_name": "BanditRLProof.HarnessProfile",
    "file": "BanditRLProof/Automation.lean",
    "line": 13,
    "statement": "inductive HarnessProfile where"
  },
  {
    "kind": "inductive",
    "name": "AgentRole",
    "full_name": "BanditRLProof.AgentRole",
    "file": "BanditRLProof/Automation.lean",
    "line": 17,
    "statement": "inductive AgentRole where"
  },
  {
    "kind": "inductive",
    "name": "TaskKind",
    "full_name": "BanditRLProof.TaskKind",
    "file": "BanditRLProof/Automation.lean",
    "line": 24,
    "statement": "inductive TaskKind where"
  },
  {
    "kind": "inductive",
    "name": "TaskStatus",
    "full_name": "BanditRLProof.TaskStatus",
    "file": "BanditRLProof/Automation.lean",
    "line": 32,
    "statement": "inductive TaskStatus where"
  },
  {
    "kind": "structure",
    "name": "ArtifactSpec",
    "full_name": "BanditRLProof.ArtifactSpec",
    "file": "BanditRLProof/Automation.lean",
    "line": 40,
    "statement": "structure ArtifactSpec where"
  },
  {
    "kind": "structure",
    "name": "AcceptanceGate",
    "full_name": "BanditRLProof.AcceptanceGate",
    "file": "BanditRLProof/Automation.lean",
    "line": 46,
    "statement": "structure AcceptanceGate where"
  },
  {
    "kind": "structure",
    "name": "HarnessTask",
    "full_name": "BanditRLProof.HarnessTask",
    "file": "BanditRLProof/Automation.lean",
    "line": 53,
    "statement": "structure HarnessTask where"
  },
  {
    "kind": "def",
    "name": "defaultLeanGate",
    "full_name": "BanditRLProof.defaultLeanGate",
    "file": "BanditRLProof/Automation.lean",
    "line": 63,
    "statement": "def defaultLeanGate : AcceptanceGate where"
  },
  {
    "kind": "def",
    "name": "defaultHarnessProfile",
    "full_name": "BanditRLProof.defaultHarnessProfile",
    "file": "BanditRLProof/Automation.lean",
    "line": 69,
    "statement": "def defaultHarnessProfile : HarnessProfile"
  },
  {
    "kind": "abbrev",
    "name": "ActionTrace",
    "full_name": "BanditRLProof.ActionTrace",
    "file": "BanditRLProof/Core.lean",
    "line": 17,
    "statement": "abbrev ActionTrace (Action : Type u)"
  },
  {
    "kind": "abbrev",
    "name": "RewardTrace",
    "full_name": "BanditRLProof.RewardTrace",
    "file": "BanditRLProof/Core.lean",
    "line": 20,
    "statement": "abbrev RewardTrace (Reward : Type v)"
  },
  {
    "kind": "def",
    "name": "pullCount",
    "full_name": "BanditRLProof.pullCount",
    "file": "BanditRLProof/Core.lean",
    "line": 23,
    "statement": "def pullCount [DecidableEq Action] (action : ActionTrace Action) (a : Action) : Nat \u2192 Nat | 0 => 0 | t + 1 => pullCount action a t + if action t = a then 1 else 0 @[simp] theorem pullCount_zero [DecidableEq Action] (action : ActionTrace Action) (a : Action) : pullCount action a 0 = 0"
  },
  {
    "kind": "theorem",
    "name": "pullCount_zero",
    "full_name": "BanditRLProof.pullCount_zero",
    "file": "BanditRLProof/Core.lean",
    "line": 27,
    "statement": "@[simp] theorem pullCount_zero [DecidableEq Action] (action : ActionTrace Action) (a : Action) : pullCount action a 0 = 0"
  },
  {
    "kind": "theorem",
    "name": "pullCount_succ",
    "full_name": "BanditRLProof.pullCount_succ",
    "file": "BanditRLProof/Core.lean",
    "line": 31,
    "statement": "@[simp] theorem pullCount_succ [DecidableEq Action] (action : ActionTrace Action) (a : Action) (t : Nat) : pullCount action a (t + 1) = pullCount action a t + if action t = a then 1 else 0"
  },
  {
    "kind": "def",
    "name": "sumRewards",
    "full_name": "BanditRLProof.sumRewards",
    "file": "BanditRLProof/Core.lean",
    "line": 37,
    "statement": "def sumRewards [DecidableEq Action] [OfNat Reward 0] [HAdd Reward Reward Reward] (action : ActionTrace Action) (reward : RewardTrace Reward) (a : Action) : Nat \u2192 Reward | 0 => 0 | t + 1 => sumRewards action reward a t + if action t = a then reward t else 0 @[simp] theorem sumRewards_zero [DecidableEq Action] [OfNat Reward 0]"
  },
  {
    "kind": "theorem",
    "name": "sumRewards_zero",
    "full_name": "BanditRLProof.sumRewards_zero",
    "file": "BanditRLProof/Core.lean",
    "line": 44,
    "statement": "@[simp] theorem sumRewards_zero [DecidableEq Action] [OfNat Reward 0] [HAdd Reward Reward Reward] (action : ActionTrace Action) (reward : RewardTrace Reward) (a : Action) : sumRewards action reward a 0 = 0"
  },
  {
    "kind": "theorem",
    "name": "sumRewards_succ",
    "full_name": "BanditRLProof.sumRewards_succ",
    "file": "BanditRLProof/Core.lean",
    "line": 49,
    "statement": "@[simp] theorem sumRewards_succ [DecidableEq Action] [OfNat Reward 0] [HAdd Reward Reward Reward] (action : ActionTrace Action) (reward : RewardTrace Reward) (a : Action) (t : Nat) : sumRewards action reward a (t + 1) = sumRewards action reward a t + if action t = a then reward t else 0"
  },
  {
    "kind": "structure",
    "name": "FiniteBanditModel",
    "full_name": "BanditRLProof.FiniteBanditModel",
    "file": "BanditRLProof/Core.lean",
    "line": 56,
    "statement": "structure FiniteBanditModel (K : Nat) where"
  },
  {
    "kind": "def",
    "name": "bestArm",
    "full_name": "BanditRLProof.FiniteBanditModel.bestArm",
    "file": "BanditRLProof/Core.lean",
    "line": 63,
    "statement": "noncomputable def bestArm (model : FiniteBanditModel K) : Fin K :="
  },
  {
    "kind": "def",
    "name": "bestMean",
    "full_name": "BanditRLProof.FiniteBanditModel.bestMean",
    "file": "BanditRLProof/Core.lean",
    "line": 69,
    "statement": "noncomputable def bestMean (model : FiniteBanditModel K) : Rat :="
  },
  {
    "kind": "def",
    "name": "gap",
    "full_name": "BanditRLProof.FiniteBanditModel.gap",
    "file": "BanditRLProof/Core.lean",
    "line": 73,
    "statement": "noncomputable def gap (model : FiniteBanditModel K) (arm : Fin K) : Rat :="
  },
  {
    "kind": "theorem",
    "name": "gap_bestArm",
    "full_name": "BanditRLProof.FiniteBanditModel.gap_bestArm",
    "file": "BanditRLProof/Core.lean",
    "line": 76,
    "statement": "@[simp] theorem gap_bestArm (model : FiniteBanditModel K) : model.gap model.bestArm = 0"
  },
  {
    "kind": "structure",
    "name": "PolicySketch",
    "full_name": "BanditRLProof.PolicySketch",
    "file": "BanditRLProof/Core.lean",
    "line": 83,
    "statement": "structure PolicySketch (K : Nat) where"
  },
  {
    "kind": "inductive",
    "name": "CertificateStatus",
    "full_name": "BanditRLProof.CertificateStatus",
    "file": "BanditRLProof/Core.lean",
    "line": 88,
    "statement": "inductive CertificateStatus where"
  },
  {
    "kind": "theorem",
    "name": "pullCount_one",
    "full_name": "BanditRLProof.pullCount_one",
    "file": "BanditRLProof/LeafLemmas.lean",
    "line": 18,
    "statement": "@[simp] theorem pullCount_one : pullCount action a 1 = if action 0 = a then 1 else 0"
  },
  {
    "kind": "theorem",
    "name": "pullCount_succ_of_eq",
    "full_name": "BanditRLProof.pullCount_succ_of_eq",
    "file": "BanditRLProof/LeafLemmas.lean",
    "line": 22,
    "statement": "theorem pullCount_succ_of_eq (h : action t = a) : pullCount action a (t + 1) = pullCount action a t + 1"
  },
  {
    "kind": "theorem",
    "name": "pullCount_succ_of_ne",
    "full_name": "BanditRLProof.pullCount_succ_of_ne",
    "file": "BanditRLProof/LeafLemmas.lean",
    "line": 26,
    "statement": "theorem pullCount_succ_of_ne (h : action t \u2260 a) : pullCount action a (t + 1) = pullCount action a t"
  },
  {
    "kind": "theorem",
    "name": "pullCount_le_succ",
    "full_name": "BanditRLProof.pullCount_le_succ",
    "file": "BanditRLProof/LeafLemmas.lean",
    "line": 30,
    "statement": "theorem pullCount_le_succ : pullCount action a t \u2264 pullCount action a (t + 1)"
  },
  {
    "kind": "theorem",
    "name": "pullCount_succ_le_succ",
    "full_name": "BanditRLProof.pullCount_succ_le_succ",
    "file": "BanditRLProof/LeafLemmas.lean",
    "line": 35,
    "statement": "theorem pullCount_succ_le_succ : pullCount action a (t + 1) \u2264 pullCount action a t + 1"
  },
  {
    "kind": "theorem",
    "name": "pullCount_mono",
    "full_name": "BanditRLProof.pullCount_mono",
    "file": "BanditRLProof/LeafLemmas.lean",
    "line": 40,
    "statement": "theorem pullCount_mono {s t : Nat} (h : s \u2264 t) : pullCount action a s \u2264 pullCount action a t"
  },
  {
    "kind": "theorem",
    "name": "pullCount_le_time",
    "full_name": "BanditRLProof.pullCount_le_time",
    "file": "BanditRLProof/LeafLemmas.lean",
    "line": 46,
    "statement": "theorem pullCount_le_time : pullCount action a t \u2264 t"
  },
  {
    "kind": "theorem",
    "name": "pullCount_add_le",
    "full_name": "BanditRLProof.pullCount_add_le",
    "file": "BanditRLProof/LeafLemmas.lean",
    "line": 58,
    "statement": "theorem pullCount_add_le (n : Nat) : pullCount action a (t + n) \u2264 pullCount action a t + n"
  },
  {
    "kind": "theorem",
    "name": "pullCount_le_add",
    "full_name": "BanditRLProof.pullCount_le_add",
    "file": "BanditRLProof/LeafLemmas.lean",
    "line": 67,
    "statement": "theorem pullCount_le_add : pullCount action a t \u2264 pullCount action a (t + n)"
  },
  {
    "kind": "theorem",
    "name": "pullCount_eq_zero_of_forall_ne",
    "full_name": "BanditRLProof.pullCount_eq_zero_of_forall_ne",
    "file": "BanditRLProof/LeafLemmas.lean",
    "line": 71,
    "statement": "theorem pullCount_eq_zero_of_forall_ne (h : \u2200 s, s < t \u2192 action s \u2260 a) : pullCount action a t = 0"
  },
  {
    "kind": "theorem",
    "name": "pullCount_eq_time_of_forall_eq",
    "full_name": "BanditRLProof.pullCount_eq_time_of_forall_eq",
    "file": "BanditRLProof/LeafLemmas.lean",
    "line": 80,
    "statement": "theorem pullCount_eq_time_of_forall_eq (h : \u2200 s, s < t \u2192 action s = a) : pullCount action a t = t"
  },
  {
    "kind": "theorem",
    "name": "pullCount_pos_of_eq_before",
    "full_name": "BanditRLProof.pullCount_pos_of_eq_before",
    "file": "BanditRLProof/LeafLemmas.lean",
    "line": 89,
    "statement": "theorem pullCount_pos_of_eq_before {s t : Nat} (hst : s < t) (h : action s = a) : 0 < pullCount action a t"
  },
  {
    "kind": "theorem",
    "name": "pullCount_const_self",
    "full_name": "BanditRLProof.pullCount_const_self",
    "file": "BanditRLProof/LeafLemmas.lean",
    "line": 101,
    "statement": "@[simp] theorem pullCount_const_self (a : Action) (t : Nat) : pullCount (fun _ => a) a t = t"
  },
  {
    "kind": "theorem",
    "name": "pullCount_const_of_ne",
    "full_name": "BanditRLProof.pullCount_const_of_ne",
    "file": "BanditRLProof/LeafLemmas.lean",
    "line": 107,
    "statement": "theorem pullCount_const_of_ne (b : Action) (h : b \u2260 a) (t : Nat) : pullCount (fun _ => b) a t = 0"
  },
  {
    "kind": "theorem",
    "name": "pullCount_add_eq_of_forall_ne_between",
    "full_name": "BanditRLProof.pullCount_add_eq_of_forall_ne_between",
    "file": "BanditRLProof/LeafLemmas.lean",
    "line": 113,
    "statement": "theorem pullCount_add_eq_of_forall_ne_between (n : Nat) (h : \u2200 s, t \u2264 s \u2192 s < t + n \u2192 action s \u2260 a) : pullCount action a (t + n) = pullCount action a t"
  },
  {
    "kind": "theorem",
    "name": "pullCount_add_eq_add_of_forall_eq_between",
    "full_name": "BanditRLProof.pullCount_add_eq_add_of_forall_eq_between",
    "file": "BanditRLProof/LeafLemmas.lean",
    "line": 125,
    "statement": "theorem pullCount_add_eq_add_of_forall_eq_between (n : Nat) (h : \u2200 s, t \u2264 s \u2192 s < t + n \u2192 action s = a) : pullCount action a (t + n) = pullCount action a t + n"
  },
  {
    "kind": "theorem",
    "name": "sumRewards_succ_of_eq",
    "full_name": "BanditRLProof.sumRewards_succ_of_eq",
    "file": "BanditRLProof/LeafLemmas.lean",
    "line": 147,
    "statement": "theorem sumRewards_succ_of_eq (h : action t = a) : sumRewards action reward a (t + 1) = sumRewards action reward a t + reward t"
  },
  {
    "kind": "theorem",
    "name": "sumRewards_succ_of_ne",
    "full_name": "BanditRLProof.sumRewards_succ_of_ne",
    "file": "BanditRLProof/LeafLemmas.lean",
    "line": 152,
    "statement": "theorem sumRewards_succ_of_ne (hzero : \u2200 x : Reward, x + 0 = x) (h : action t \u2260 a) : sumRewards action reward a (t + 1) = sumRewards action reward a t"
  },
  {
    "kind": "theorem",
    "name": "sumRewards_eq_zero_of_forall_ne",
    "full_name": "BanditRLProof.sumRewards_eq_zero_of_forall_ne",
    "file": "BanditRLProof/LeafLemmas.lean",
    "line": 158,
    "statement": "theorem sumRewards_eq_zero_of_forall_ne (hzero : \u2200 x : Reward, x + 0 = x) (h : \u2200 s, s < t \u2192 action s \u2260 a) : sumRewards action reward a t = 0"
  },
  {
    "kind": "theorem",
    "name": "sumRewards_const_of_ne",
    "full_name": "BanditRLProof.sumRewards_const_of_ne",
    "file": "BanditRLProof/LeafLemmas.lean",
    "line": 167,
    "statement": "theorem sumRewards_const_of_ne (hzero : \u2200 x : Reward, x + 0 = x) (b : Action) (h : b \u2260 a) (t : Nat) : sumRewards (fun _ => b) reward a t = 0"
  },
  {
    "kind": "theorem",
    "name": "sumRewards_add_eq_of_forall_ne_between",
    "full_name": "BanditRLProof.sumRewards_add_eq_of_forall_ne_between",
    "file": "BanditRLProof/LeafLemmas.lean",
    "line": 175,
    "statement": "theorem sumRewards_add_eq_of_forall_ne_between (hzero : \u2200 x : Reward, x + 0 = x) (n : Nat) (h : \u2200 s, t \u2264 s \u2192 s < t + n \u2192 action s \u2260 a) : sumRewards action reward a (t + n) = sumRewards action reward a t"
  },
  {
    "kind": "theorem",
    "name": "bestMean_eq_mean_bestArm",
    "full_name": "BanditRLProof.FiniteBanditModel.bestMean_eq_mean_bestArm",
    "file": "BanditRLProof/LeafLemmas.lean",
    "line": 191,
    "statement": "@[simp] theorem bestMean_eq_mean_bestArm (model : FiniteBanditModel K) : model.bestMean = model.mean model.bestArm"
  },
  {
    "kind": "theorem",
    "name": "gap_of_ne_bestArm",
    "full_name": "BanditRLProof.FiniteBanditModel.gap_of_ne_bestArm",
    "file": "BanditRLProof/LeafLemmas.lean",
    "line": 194,
    "statement": "theorem gap_of_ne_bestArm (model : FiniteBanditModel K) (arm : Fin K) (h : arm \u2260 model.bestArm) : model.gap arm = model.bestMean - model.mean arm"
  },
  {
    "kind": "theorem",
    "name": "pseudoRegret_one",
    "full_name": "BanditRLProof.pseudoRegret_one",
    "file": "BanditRLProof/LeafLemmas.lean",
    "line": 205,
    "statement": "@[simp] theorem pseudoRegret_one : pseudoRegret model action 1 = model.gap (action 0)"
  },
  {
    "kind": "theorem",
    "name": "pseudoRegret_succ_of_bestArm",
    "full_name": "BanditRLProof.pseudoRegret_succ_of_bestArm",
    "file": "BanditRLProof/LeafLemmas.lean",
    "line": 210,
    "statement": "theorem pseudoRegret_succ_of_bestArm (h : action t = model.bestArm) : pseudoRegret model action (t + 1) = pseudoRegret model action t"
  },
  {
    "kind": "theorem",
    "name": "pseudoRegret_succ_of_gap_zero",
    "full_name": "BanditRLProof.pseudoRegret_succ_of_gap_zero",
    "file": "BanditRLProof/LeafLemmas.lean",
    "line": 215,
    "statement": "theorem pseudoRegret_succ_of_gap_zero (h : model.gap (action t) = 0) : pseudoRegret model action (t + 1) = pseudoRegret model action t"
  },
  {
    "kind": "theorem",
    "name": "pseudoRegret_eq_zero_of_forall_bestArm",
    "full_name": "BanditRLProof.pseudoRegret_eq_zero_of_forall_bestArm",
    "file": "BanditRLProof/LeafLemmas.lean",
    "line": 220,
    "statement": "theorem pseudoRegret_eq_zero_of_forall_bestArm (h : \u2200 s, s < t \u2192 action s = model.bestArm) : pseudoRegret model action t = 0"
  },
  {
    "kind": "theorem",
    "name": "pseudoRegret_eq_zero_of_forall_gap_zero",
    "full_name": "BanditRLProof.pseudoRegret_eq_zero_of_forall_gap_zero",
    "file": "BanditRLProof/LeafLemmas.lean",
    "line": 229,
    "statement": "theorem pseudoRegret_eq_zero_of_forall_gap_zero (h : \u2200 s, s < t \u2192 model.gap (action s) = 0) : pseudoRegret model action t = 0"
  },
  {
    "kind": "theorem",
    "name": "pseudoRegret_const_bestArm",
    "full_name": "BanditRLProof.pseudoRegret_const_bestArm",
    "file": "BanditRLProof/LeafLemmas.lean",
    "line": 238,
    "statement": "@[simp] theorem pseudoRegret_const_bestArm : pseudoRegret model (fun _ => model.bestArm) t = 0"
  },
  {
    "kind": "theorem",
    "name": "pseudoRegret_const_of_gap_zero",
    "full_name": "BanditRLProof.pseudoRegret_const_of_gap_zero",
    "file": "BanditRLProof/LeafLemmas.lean",
    "line": 244,
    "statement": "theorem pseudoRegret_const_of_gap_zero (arm : Fin K) (h : model.gap arm = 0) : pseudoRegret model (fun _ => arm) t = 0"
  },
  {
    "kind": "theorem",
    "name": "pseudoRegret_add_eq_of_forall_bestArm_between",
    "full_name": "BanditRLProof.pseudoRegret_add_eq_of_forall_bestArm_between",
    "file": "BanditRLProof/LeafLemmas.lean",
    "line": 250,
    "statement": "theorem pseudoRegret_add_eq_of_forall_bestArm_between (n : Nat) (h : \u2200 s, t \u2264 s \u2192 s < t + n \u2192 action s = model.bestArm) : pseudoRegret model action (t + n) = pseudoRegret model action t"
  },
  {
    "kind": "theorem",
    "name": "pseudoRegret_add_eq_of_forall_gap_zero_between",
    "full_name": "BanditRLProof.pseudoRegret_add_eq_of_forall_gap_zero_between",
    "file": "BanditRLProof/LeafLemmas.lean",
    "line": 262,
    "statement": "theorem pseudoRegret_add_eq_of_forall_gap_zero_between (n : Nat) (h : \u2200 s, t \u2264 s \u2192 s < t + n \u2192 model.gap (action s) = 0) : pseudoRegret model action (t + n) = pseudoRegret model action t"
  },
  {
    "kind": "structure",
    "name": "UpstreamRef",
    "full_name": "BanditRLProof.UpstreamRef",
    "file": "BanditRLProof/Literature.lean",
    "line": 12,
    "statement": "structure UpstreamRef where"
  },
  {
    "kind": "def",
    "name": "lmlRef",
    "full_name": "BanditRLProof.lmlRef",
    "file": "BanditRLProof/Literature.lean",
    "line": 22,
    "statement": "def lmlRef : UpstreamRef where"
  },
  {
    "kind": "def",
    "name": "lmlBanditDeclarationCards",
    "full_name": "BanditRLProof.lmlBanditDeclarationCards",
    "file": "BanditRLProof/Literature.lean",
    "line": 31,
    "statement": "def lmlBanditDeclarationCards : List RegretBoundCard :="
  },
  {
    "kind": "inductive",
    "name": "ProblemArea",
    "full_name": "BanditRLProof.ProblemArea",
    "file": "BanditRLProof/OpenProblems.lean",
    "line": 9,
    "statement": "inductive ProblemArea where"
  },
  {
    "kind": "structure",
    "name": "OpenProblem",
    "full_name": "BanditRLProof.OpenProblem",
    "file": "BanditRLProof/OpenProblems.lean",
    "line": 19,
    "statement": "structure OpenProblem where"
  },
  {
    "kind": "def",
    "name": "seedOpenProblems",
    "full_name": "BanditRLProof.seedOpenProblems",
    "file": "BanditRLProof/OpenProblems.lean",
    "line": 28,
    "statement": "def seedOpenProblems : List OpenProblem :="
  },
  {
    "kind": "def",
    "name": "pseudoRegret",
    "full_name": "BanditRLProof.pseudoRegret",
    "file": "BanditRLProof/Regret.lean",
    "line": 16,
    "statement": "noncomputable def pseudoRegret (model : FiniteBanditModel K) (action : Nat \u2192 Fin K) : Nat \u2192 Rat | 0 => 0 | t + 1 => pseudoRegret model action t + model.gap (action t) @[simp] theorem pseudoRegret_zero (model : FiniteBanditModel K) (action : Nat \u2192 Fin K) : pseudoRegret model action 0 = 0"
  },
  {
    "kind": "theorem",
    "name": "pseudoRegret_zero",
    "full_name": "BanditRLProof.pseudoRegret_zero",
    "file": "BanditRLProof/Regret.lean",
    "line": 21,
    "statement": "@[simp] theorem pseudoRegret_zero (model : FiniteBanditModel K) (action : Nat \u2192 Fin K) : pseudoRegret model action 0 = 0"
  },
  {
    "kind": "theorem",
    "name": "pseudoRegret_succ",
    "full_name": "BanditRLProof.pseudoRegret_succ",
    "file": "BanditRLProof/Regret.lean",
    "line": 25,
    "statement": "@[simp] theorem pseudoRegret_succ (model : FiniteBanditModel K) (action : Nat \u2192 Fin K) (t : Nat) : pseudoRegret model action (t + 1) = pseudoRegret model action t + model.gap (action t)"
  },
  {
    "kind": "structure",
    "name": "RegretBoundCard",
    "full_name": "BanditRLProof.RegretBoundCard",
    "file": "BanditRLProof/Regret.lean",
    "line": 31,
    "statement": "structure RegretBoundCard where"
  },
  {
    "kind": "structure",
    "name": "RegretObligation",
    "full_name": "BanditRLProof.RegretObligation",
    "file": "BanditRLProof/Regret.lean",
    "line": 41,
    "statement": "structure RegretObligation where"
  }
]
```

## Recent Trials

```json
[
  {
    "kind": "plan",
    "notes": "created hierarchical prompt deck with 3 lower prompts",
    "role": "upper",
    "run_id": "20260625-103120-BRL-UCB-PORT-001-cycle01",
    "status": "queued",
    "task": "BRL-UCB-PORT-001",
    "time": "2026-06-25T01:31:20+00:00"
  },
  {
    "kind": "plan",
    "notes": "created hierarchical prompt deck with 1 lower prompts",
    "role": "upper",
    "run_id": "20260625-103252-BRL-UCB-PORT-001-cycle01",
    "status": "queued",
    "task": "BRL-UCB-PORT-001",
    "time": "2026-06-25T01:32:52+00:00"
  },
  {
    "exit_code": 0,
    "kind": "attempt",
    "notes": "executed runs/20260625-103252-BRL-UCB-PORT-001-cycle01/10_upper_director.md in 0.0s",
    "prompt": "runs/20260625-103252-BRL-UCB-PORT-001-cycle01/10_upper_director.md",
    "role": "agent",
    "run_id": "20260625-103252-BRL-UCB-PORT-001-cycle01",
    "status": "compiled",
    "task": "BRL-UCB-PORT-001",
    "time": "2026-06-25T01:32:52+00:00"
  },
  {
    "exit_code": 0,
    "kind": "attempt",
    "notes": "executed runs/20260625-103252-BRL-UCB-PORT-001-cycle01/20_middle_formalizer.md in 0.0s",
    "prompt": "runs/20260625-103252-BRL-UCB-PORT-001-cycle01/20_middle_formalizer.md",
    "role": "agent",
    "run_id": "20260625-103252-BRL-UCB-PORT-001-cycle01",
    "status": "compiled",
    "task": "BRL-UCB-PORT-001",
    "time": "2026-06-25T01:32:52+00:00"
  },
  {
    "exit_code": 0,
    "kind": "attempt",
    "notes": "executed runs/20260625-103252-BRL-UCB-PORT-001-cycle01/31_lower_1.md in 0.0s",
    "prompt": "runs/20260625-103252-BRL-UCB-PORT-001-cycle01/31_lower_1.md",
    "role": "agent",
    "run_id": "20260625-103252-BRL-UCB-PORT-001-cycle01",
    "status": "compiled",
    "task": "BRL-UCB-PORT-001",
    "time": "2026-06-25T01:32:52+00:00"
  },
  {
    "exit_code": 0,
    "kind": "attempt",
    "notes": "executed runs/20260625-103252-BRL-UCB-PORT-001-cycle01/40_reviewer.md in 0.0s",
    "prompt": "runs/20260625-103252-BRL-UCB-PORT-001-cycle01/40_reviewer.md",
    "role": "agent",
    "run_id": "20260625-103252-BRL-UCB-PORT-001-cycle01",
    "status": "compiled",
    "task": "BRL-UCB-PORT-001",
    "time": "2026-06-25T01:32:52+00:00"
  }
]
```

## Reviewer Gate

```bash
python3 tools/bandit.py check
```
