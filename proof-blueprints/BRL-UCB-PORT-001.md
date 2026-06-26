# Proof Blueprint: BRL-UCB-PORT-001

Generated: `2026-06-26T16:53:23+00:00`

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
| `UCB-CORE` | verify ABRL finite trace and pseudo-regret surfaces | `BanditRLProof.Core`, `Regret`, `LeafLemmas` | pull counts, reward sums, gap surface | `LOCAL-LEAF-FINITE-BOOKKEEPING`, `MLIB-FINSET-SUMS`, `MLIB-FINTYPE-FIN`, `LML-BANDIT-REGRET-PULLCOUNT` | compiled dependency-light bookkeeping | finite arms, horizon, rational mean model | project-local wrappers with generic arithmetic candidates | reviewer | `pseudoRegret_succ`, `pullCount_le_succ` | `python3 tools/bandit.py check` | compiled |
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
    "status": "seeded"
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
      "MLIB-REAL-LOG-SQRT",
      "MLIB-ORDER-ALGEBRA"
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
      "MLIB-CONDITIONAL-EXPECTATION",
      "MLIB-REAL-LOG-SQRT"
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
      "pullCount_eq_zero_of_forall_ne",
      "pullCount_eq_time_of_forall_eq",
      "pullCount_pos_of_eq_before",
      "sumRewards_succ_of_eq",
      "sumRewards_succ_of_ne",
      "FiniteBanditModel.bestMean_eq_mean_bestArm",
      "FiniteBanditModel.gap_of_ne_bestArm",
      "pseudoRegret_one",
      "pseudoRegret_succ_of_bestArm",
      "pseudoRegret_succ_of_gap_zero",
      "pseudoRegret_eq_zero_of_forall_bestArm",
      "pseudoRegret_eq_zero_of_forall_gap_zero"
    ],
    "role": "Compiled dependency-light bridge leaves for pull counts, reward sums, gaps, and pseudo-regret.",
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
