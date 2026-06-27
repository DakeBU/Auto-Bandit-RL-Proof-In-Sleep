# Proof Blueprint: BRL-ETC-PORT-001

Generated: `2026-06-27T04:58:26+00:00`

## Source Task

# Port the Explore-Then-Commit regret proof route

Task id: `BRL-ETC-PORT-001`
Kind: `literaturePort`
Status: `planned`
Harness: `hierarchical`

## Goal

Formalize or stage the Explore-Then-Commit regret proof route using ABRL's
finite-action surfaces and LML theorem cards.

## Source

- Repository: [LeanMachineLearning/LML](https://github.com/LeanMachineLearning/LML)
- Upstream declaration: `Bandits.ETC.regret_le`
- Upstream module: `LeanMachineLearning.Online.Bandit.Algorithms.ETC`
- Local surface: `BanditRLProof/Algorithms/ETC.lean`
- Textbook/source card: `TXT-LATTIMORE-SZEPESVARI-2020`
- Scenario card: `SCN-STOCHASTIC-FINITE`
- Mathlib cards: `MLIB-FINTYPE-FIN`, `MLIB-FINSET-SUMS`, `MLIB-PROBABILITY-INDEPENDENCE`

## Lean Target

```lean
-- staged targets:
-- BanditRLProof.ETC.obligationNames
-- future local theorem compatible with Bandits.ETC.regret_le
```

## Proof Obligations

- [ ] Prove or import round-robin exploration counts.
- [ ] Map empirical mean argmax commit.
- [ ] Record wrong-commit probability concentration theorem.
- [ ] Derive pull-count bound after commit.
- [ ] Connect to regret decomposition.

## Mathlib-Ready Leaf Contract

Current leaf classes are recorded in
`proof-obligations/BRL-ETC-PORT-001.md`.  Generic finite-cycle arithmetic and
regularity lemmas should be treated as Mathlib candidates; ETC-specific
algorithm wrappers stay project-local.  Do not change the proof route without
recording the missing assumption, counterexample, or source mismatch.

## Build Gate

```bash
python3 tools/bandit.py check
```


## Conversion Window Snapshot

# Conversion Window: Explore-Then-Commit regret route

Task id: `BRL-ETC-PORT-001`

Source card: `TXT-LATTIMORE-SZEPESVARI-2020`
Scenario card: `SCN-STOCHASTIC-FINITE`

## Natural-Language Statement

Explore-Then-Commit pulls each arm a fixed number of times, commits to the arm
with the largest empirical mean, and pays regret through exploration plus the
probability of committing to a suboptimal arm.

## Lean Mapping

| Source symbol | Meaning | Lean declaration | Type / role | Status |
| --- | --- | --- | --- | --- |
| round-robin exploration | arm `t % K` | `ETC.exploreArm` | finite action selector | compiled |
| `m` | exploration pulls per arm | `ETC.Spec.explorationPulls` | parameter | compiled |
| commit argmax | selected empirical best arm | `ETC.CommitOracle.choose` | contract | typed |
| `Bandits.ETC.regret_le` | upstream theorem | LML theorem card | regret bound | theorem-card |

## Local API And Proof Route

| Leaf | Existing APIs/imports | Retrieval cards | Intended route | Pivot rule |
| --- | --- | --- | --- | --- |
| `ETC-COUNT` | pull count recursion, `ETC.exploreArm` | `MLIB-FINSET-SUMS`, `MLIB-ORDER-ALGEBRA` | induction plus finite-cycle arithmetic | pivot only after modulo/count statement audit |
| `ETC-WRONG` | concentration theorem cards | `MLIB-PROBABILITY-INDEPENDENCE`, `MLIB-MEASURE-INTEGRAL` | pairwise empirical-mean tail event union | pivot only after checking sub-Gaussian and measurability contracts |
| `ETC-REGRET` | regret decomposition cards | `LML-ETC-REGRET`, `LML-BANDIT-REGRET-PULLCOUNT` | exploration term plus wrong-commit term | pivot only after source theorem mismatch is recorded |

## Proof-DAG

| Node | Interface | Dependencies | Owner | Lean declaration | Regularity contracts | Mathlib status | Gate | Status |
| --- | --- | --- | --- | --- | --- | --- | --- | --- |
| `ETC-COUNT` | each arm has `m` exploration pulls | round-robin arithmetic | lower Lean | TBD | finite arms, positive arm count | mathlib-candidate for generic arithmetic leaves | build | planned |
| `ETC-COMMIT` | commit arm maximizes empirical mean | argmax contract | lower architect | TBD | nonempty finite candidates, denominator positivity | project-local wrapper | build | planned |
| `ETC-WRONG` | wrong commit probability | sub-Gaussian tail | retrieval | cited result | measurability, integrability, sub-Gaussian independence | theorem-card-only | memory | obligation |
| `ETC-PULL` | pull count after commit | `ETC-COMMIT`, `ETC-WRONG` | lower Lean | TBD | finite horizon, committed arm exists | project-local | build | planned |
| `ETC-REGRET` | regret bound | pull-count decomposition | lower Lean | future theorem | all contracts above | project-local | build | blocked |


## Obligation Snapshot

# Proof Obligations: BRL-ETC-PORT-001

Source card: `TXT-LATTIMORE-SZEPESVARI-2020`
Scenario card: `SCN-STOCHASTIC-FINITE`

| Node | Target | Dependencies | Local APIs/imports | Retrieval cards | Intended proof route | Regularity contracts | Mathlib status | Owner | Lean declaration | Gate | Status |
| --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- |
| `ETC-CORE` | verify exploration-arm finite selector | ABRL core | `BanditRLProof.Algorithms.ETC` | `LOCAL-LEAF-ALGORITHM-WRAPPERS`, `MLIB-FINTYPE-FIN` | finite selector value proof | finite action count, nonzero exploration horizon | project-local | reviewer | `ETC.exploreArm_val`, `ETC.exploreArm_eq_of_mod_eq` | check | compiled |
| `ETC-COUNT` | prove round-robin pull-count arithmetic | `ETC.exploreArm` | pull count recursion, Nat modulo lemmas | `LOCAL-LEAF-FINITE-BOOKKEEPING`, `MLIB-FINSET-SUMS`, `MLIB-ORDER-ALGEBRA` | induction on time plus finite-cycle arithmetic | finite actions, positive arm count | mathlib-candidate for generic arithmetic leaves | lower Lean | `pullCount_succ_of_eq`, `pullCount_succ_of_ne`, `pullCount_add_eq_of_forall_ne_between`, `pullCount_add_eq_add_of_forall_eq_between` | build | planned |
| `ETC-COMMIT` | define empirical-mean argmax commit | finite history | finite argmax contract, reward sums | `LOCAL-LEAF-FINITE-BOOKKEEPING`, `MLIB-FINTYPE-FIN`, `MLIB-FINSET-SUMS` | expose commit oracle before probability proof | finite arms, nonempty candidate set, denominator positivity | project-local wrapper | middle/lower | `sumRewards_add_eq_of_forall_ne_between` | build | planned |
| `ETC-CONC` | wrong-commit probability bound | sub-Gaussian cards | concentration theorem cards | `MLIB-PROBABILITY-INDEPENDENCE`, `MLIB-MEASURE-INTEGRAL` | reduce wrong commit to pairwise empirical-mean tail events | measurability, integrability, independence/sub-Gaussian contract | theorem-card-only until imported or ported | retrieval | TBD | memory/build | obligation |
| `ETC-FINAL` | local theorem compatible with `Bandits.ETC.regret_le` | all above | regret decomposition, pull-count ledger | `LML-ETC-REGRET`, `LML-BANDIT-REGRET-PULLCOUNT` | exploration regret plus wrong-commit regret | all upstream contracts above | project-local | lower Lean | TBD | build | blocked |


## Completion Gap Audit

# Completion Gap Audit

This audit answers a blunt question: how far is ABRL from fully reproducing the
classic bandit textbook proof weapons and the Mathlib-level foundations they
depend on?

Short answer: ABRL is still early.  The harness, memory indexes, source cards,
proof weapons, and a dependency-light finite bookkeeping layer exist.  The
Mathlib-heavy measure/probability/concentration/optimization layers are mostly
retrieval cards and proof obligations, not compiled local theorem ports.

## Current Evidence

Current local evidence:

| Artifact | Count | Meaning |
| --- | ---: | --- |
| LML theorem cards | 6 | external Lean theorem-card routes, not local proofs |
| Mathlib retrieval cards | 17 | import/search routes for reusable leaves |
| textbook cards | 3 | Bubeck-Cesa-Bianchi, Lattimore-Szepesvari, Slivkins |
| paper cards | 18 | algorithm/frontier source routes |
| scenario cards | 18 | current bandit/RL taxonomy |
| proof weapon cards | 8 | upper-agent route inspiration only |
| compiled local finite-bookkeeping leaves | 32 | local dependency-light leaves |
| compiled local algorithm-wrapper leaves | 2 | thin ETC/UCB wrappers |
| scanned local Lean declarations | 80 | definitions, structures, and theorems in `BanditRLProof/` |

The compiled local layer currently covers:

- finite action traces;
- pull counts and segment counts;
- reward sums and one segment-stability lemma;
- rational finite-arm mean models;
- pseudo-regret zero/segment leaves;
- thin ETC and UCB wrapper lemmas.

The compiled local layer does not yet cover:

- measure spaces, kernels, filtrations, conditional expectations;
- integrability and measurability theorem contracts;
- sub-Gaussian, Hoeffding, Chernoff, variance, or martingale tail proofs;
- regret decomposition into pull counts over a Mathlib finite sum;
- imported or ported LML UCB/ETC/Thompson theorems;
- EXP3, KL-UCB, Tsallis-INF/FTRL, OFUL/LinUCB, BwK, pure exploration, RL/MDP
  final theorem surfaces;
- full Markdown/LaTeX exports for closed textbook theorems.

## Distance By Layer

The table below is an engineering audit, not a mathematical impossibility
claim.  `compiled` means the local Lean gate proves it now.  `carded` means the
source or retrieval route exists.  `missing` means the route still needs leaf
statements, imports, or local proofs.

| Layer | Current status | What remains |
| --- | --- | --- |
| Harness and memory workflow | mostly compiled/tooling | add richer population operations and reviewer audits |
| Source/paper/scenario map | broad card coverage | keep current with new papers and check every source route |
| Proof weapons | carded | must be decomposed per task; not proof certificates |
| Finite bookkeeping | partially compiled | bridge recursive definitions to Mathlib `Finset` sums |
| Regret decomposition | theorem-card plus local pseudo-regret | prove/import pull-count decomposition and expectation form |
| Measure/probability foundation | retrieval-card only | import Mathlib, define local APIs, prove regularity contracts |
| Kernels/posteriors | retrieval-card only | posterior kernels, conditional distributions, Bayesian regret |
| Concentration/tails | retrieval-card only | sub-Gaussian, Hoeffding, conditional tails, finite union bounds |
| UCB/ETC textbook routes | wrappers plus theorem cards | concentration, width algebra, pull-count theorem, final regret |
| Thompson sampling | theorem cards only | posterior identity route, integrability, Bayes-regret decomposition |
| EXP3/adversarial | paper/weapon cards only | estimator, exponential potential, FTRL/OMD leaves |
| Tsallis-INF/FTRL | paper/weapon cards only | simplex, Tsallis regularizer, power algebra, stability/penalty split |
| Linear/OFUL/LinUCB | paper/weapon cards only | Gram matrix, confidence ellipsoid, self-normalized tail |
| RL/MDP | scenario/paper cards only | finite kernels, Bellman recursion, occupancy measures, episode regret |
| Proof export | skeleton exists | exports must be generated from compiled theorem declarations |

## Textbook-Scope Completion Estimate

For the three current textbook/survey roots, ABRL has a broad map but not a
full proof library.

| Source root | Current coverage | Remaining proof strata |
| --- | --- | --- |
| Bubeck-Cesa-Bianchi 2012 | stochastic/adversarial routes and paper cards | UCB/EXP3 tails, lower bounds, minimax routes, final theorem exports |
| Lattimore-Szepesvari 2020 | main scenario tree and Mathlib routes | probability foundation, concentration chapters, ETC/UCB/MOSS/KL-UCB/linear proofs |
| Slivkins 2019/2024 | scenario atlas, Bayesian, Lipschitz, BwK, agents | Bayesian/posterior formalization, Lipschitz/metric trees, BwK and incentive proofs |

Pragmatic estimate: for the desired textbook-scale proof weapon library, the
current compiled Lean is under one tenth of the needed proof surface.  It is
useful because it sets stable harness rules and proves the first finite
bookkeeping leaves, but the major Mathlib-backed layers still need to be
imported, adapted, or proved.

## Required Next Milestones

1. Add a Mathlib-backed probability layer.
2. Convert retrieval cards for sub-Gaussian tails into exact imported theorem
   packets and local wrappers.
3. Prove the Mathlib finite-sum bridge for recursive `pullCount`, `sumRewards`,
   and `pseudoRegret`.
4. Close one narrow textbook theorem end-to-end, likely a small UCB/ETC
   bookkeeping or concentration-dependent theorem.
5. Export that theorem to Markdown and LaTeX from compiled declarations.
6. Only then expand to TS, EXP3, Tsallis-INF/FTRL, OFUL, BwK, and RL/MDP final
   theorem branches.

## Non-Negotiable Leaf Discipline

Every new leaf must satisfy the local contract:

- decompose aggressively;
- target a lemma that fits within one lower-agent context window;
- specify more than the theorem: local APIs, imports, assumptions, intended
  proof route;
- treat persistent failure as mathematical signal;
- promote hidden regularity into reusable theorem contracts;
- do not frequently change the proof route without a reviewer-visible reason.

The point of the audit is not to lower ambition.  It is to prevent agents from
mistaking a broad tree for completed Lean mathematics.


## Adaptive Harness Design

# Adaptive Harness Design

ABRL has two target workflows:

1. complete user-specified proof technology and paper LaTeX proofs;
2. explore new bandit/RL theorem targets and construct a complete Lean proof
   plan, then close leaves one by one.

This design keeps proof weapons as planning inspiration while keeping compiled
Lean and imported theorem cards as the only reusable proof material.

## End-To-End Loop

```text
user theorem / paper proof / new topic
-> upper route population
-> middle source and memory grounding
-> proof-DAG decomposition
-> lower leaf packet
-> choose Lean-direct or NL-prover-assisted route
-> Lean proof attempt
-> reviewer gate
-> memory compression
-> Markdown and LaTeX export after compilation
```

## Role Responsibilities

| Role | Main decisions | Output |
| --- | --- | --- |
| Upper | choose theorem frontier; generate several possible route ideas; decide which proof weapon is only inspiration | route population, selected frontier, rejected route notes |
| Middle | ground route in source cards, Mathlib/LML/local declarations, hidden regularity, and proof-obligation leaves | conversion window, proof-obligation ledger, retrieval index |
| Lower retrieval | find reusable Mathlib/LML/local theorem cards before proof work | retrieval packet with declarations and imports |
| Lower natural-language prover | propose proof sketch for a single leaf when math structure is unclear | sketch, assumptions, possible counterexample, proof route |
| Lower Lean worker | prove exactly one leaf or write a precise blocker | compiled declaration or failed-attempt record |
| Reviewer | reject route drift, hidden assumptions, stale proof weapons, and uncompiled theorem claims | accepted/rejected status, memory update requirements |

## Route Population

Upper keeps a population of candidate routes under `candidate-populations/`.
Each candidate route should contain:

- target theorem;
- source cards;
- scenario card;
- proof weapon ids considered, marked inspiration-only;
- direct reuse cards: Mathlib, LML, local declarations;
- first proof-DAG leaves;
- hidden regularity contracts;
- expected blocker;
- reason for selection or rejection.

The population is not an evolutionary free-for-all.  Every candidate remains
under the same Lean-checkable target unless reviewer records a mathematical
reason to pivot.

## Middle Decomposition Rule

Middle must turn route ideas into leaf packets before lower work.  A valid leaf
packet contains:

| Field | Required content |
| --- | --- |
| Exact statement | Lean-facing theorem shape, not just prose |
| Local APIs | definitions, namespaces, existing declarations |
| Intended route | induction/import/tactic outline |
| Regularity contracts | measurability, integrability, continuity, nonempty, boundedness, positivity, summability, adaptedness |
| Retrieval evidence | `search-memory`, `list-lean-decls --statement`, Mathlib/LML cards |
| Mathlib status | imported, port candidate, Mathlib candidate, project-local, theorem-card-only |
| Failure policy | what repeated failure means and what to audit |

If this packet cannot be written, the task is still upper/middle work and
should not be sent to a lower Lean worker.

## Lean-Direct Versus Natural-Language Prover

Middle chooses the lower route per leaf:

| Leaf situation | Preferred route |
| --- | --- |
| local API and proof route are obvious | Lean-direct lower worker |
| exact theorem exists in Mathlib/LML | lower retrieval worker, then thin wrapper |
| proof shape is mathematical but not yet Lean-shaped | natural-language prover first, then Lean worker |
| repeated Lean failure with same goal | statement/hypothesis/counterexample audit |
| route needs a broad proof weapon | upper/middle decomposes weapon into concrete leaves first |

Natural-language proof is useful only if it sharpens the Lean statement,
assumptions, or proof route.  It is not accepted memory until translated into
compiled Lean or an explicit cited theorem card.

## Memory Card Types

| Card type | Purpose | May be used as proof dependency? |
| --- | --- | --- |
| Local Lean declaration | compiled result in this repository | yes |
| Mathlib retrieval card | import/search route to upstream theorem/API | yes only after imported or wrapped |
| LML theorem card | upstream Lean theorem route | yes only after imported/ported; otherwise theorem-card |
| Textbook card | broad proof source | no |
| Paper card | specific algorithm/source route | no |
| Scenario card | taxonomy and placement | no |
| Proof weapon card | route inspiration for upper planning | no |
| Mathlib candidate card | future upstream lemma proposal | no until compiled/imported |
| Cited result card | external theorem contract | no local proof; can be cited in prose with status |
| Failed-attempt card | mathematical signal and reusable debugging | no |

## Lean And LaTeX Synchronization

ABRL exports only after Lean closure:

```bash
python3 tools/bandit.py export-proof TASK_ID --title "Theorem title"
```

The export must:

- name compiled Lean declarations;
- state no stronger result than Lean proves;
- cite theorem cards and proof weapons only by status;
- include regularity assumptions explicitly;
- record any missing theorem-card dependency as not locally proved.

For a paper proof completion task, middle maintains a conversion window:

```text
paper theorem line
-> assumptions and notation
-> Lean definition/declaration
-> proof-DAG leaves
-> compiled theorem
-> Markdown/LaTeX paragraph
```

## Built-In Experience Rules

The harness encodes the following proof-engineering lessons:

- Decompose aggressively.
- Target small lemmas that fit one lower-agent context window.
- Specify more than the theorem: local APIs and intended proof route.
- Treat persistent failure as mathematical signal.
- Promote hidden regularity into reusable theorem contracts.
- Do not frequently change the proof route without a recorded reason.

Reviewer should reject any cycle that violates these rules even if the text
looks plausible.

## Current Limitation

This design is in place as plain-file harness structure and CLI retrieval
support.  It is not yet a complete automatic prover.  The missing work is the
large body of Mathlib-backed leaves listed in
`research-wiki/theory-tree/mathlib-foundation-leaf-map.md` and the completion
gap audit in `docs/completion_gap_audit.md`.


## Mathlib Foundation Leaf Map

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
  },
  {
    "id": "MLIB-PROBABILITY-SUBGAUSSIAN",
    "source": "Mathlib",
    "module": "Mathlib.Probability.Moments.SubGaussian",
    "docs": "https://leanprover-community.github.io/mathlib4_docs/Mathlib/Probability/Moments/SubGaussian.html",
    "query_terms": [
      "measure_sum_ge_le_of_iIndepFun",
      "hasSubgaussianMGF_of_mem_Icc_of_integral_eq_zero",
      "measure_sum_ge_le_of_HasCondSubgaussianMGF",
      "HasSubgaussianMGF"
    ],
    "role": "Hoeffding-style tails, Azuma-Hoeffding routes, sub-Gaussian reward sums, and UCB/ETC concentration leaves.",
    "status": "import-candidate"
  },
  {
    "id": "MLIB-PROBABILITY-MGF",
    "source": "Mathlib",
    "module": "Mathlib.Probability.Moments.Basic; Mathlib.Probability.Moments.Tilted",
    "docs": "https://leanprover-community.github.io/mathlib4_docs/Mathlib/Probability/Moments/Basic.html",
    "query_terms": [
      "mgf",
      "cgf",
      "IndepFun.mgf_add",
      "IndepFun.cgf_add",
      "tilted"
    ],
    "role": "Moment-generating and cumulant-generating function algebra for Chernoff, exponential weights, and concentration routes.",
    "status": "import-candidate"
  },
  {
    "id": "MLIB-PROBABILITY-VARIANCE",
    "source": "Mathlib",
    "module": "Mathlib.Probability.Moments.Variance",
    "docs": "https://leanprover-community.github.io/mathlib4_docs/Mathlib/Probability/Moments/Variance.html",
    "query_terms": [
      "variance",
      "chebyshev",
      "IndepFun.variance_add",
      "MemLp"
    ],
    "role": "Variance bookkeeping, Chebyshev-style tails, robust/heavy-tailed baselines, and second-moment contracts.",
    "status": "import-candidate"
  },
  {
    "id": "MLIB-REAL-RPOW-TSALLIS",
    "source": "Mathlib",
    "module": "Mathlib.Analysis.SpecialFunctions.Pow.Real; Mathlib.Analysis.SpecialFunctions.Pow.NNReal",
    "docs": "https://leanprover-community.github.io/mathlib4_docs/Mathlib/Analysis/SpecialFunctions/Pow/Real.html",
    "query_terms": [
      "Real.rpow",
      "NNReal.rpow",
      "rpow",
      "rpow_le_rpow",
      "rpow_pos_of_pos"
    ],
    "role": "Tsallis entropy regularizers, power potentials, FTRL/OMD penalty algebra, and nonnegative-probability weights.",
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
    "id": "PPR-ZIMMERT-SELDIN-2018-TSALLIS-INF",
    "title": "Tsallis-INF: An Optimal Algorithm for Stochastic and Adversarial Bandits",
    "authors": "Julian Zimmert; Yevgeny Seldin",
    "source": "https://arxiv.org/abs/1807.07623",
    "scenarios": [
      "SCN-BOBW-ADAPTIVE",
      "SCN-ADVERSARIAL-FINITE",
      "SCN-STOCHASTIC-FINITE"
    ],
    "proof_roots": [
      "Tsallis-INF",
      "Tsallis entropy regularizer",
      "best-of-both-worlds regret"
    ],
    "lean_leaf_families": [
      "FTRL optimality",
      "Tsallis potential algebra",
      "importance-weighted loss",
      "self-bounding regret"
    ],
    "memory_status": "paper-card"
  },
  {
    "id": "PPR-MASOUDIAN-SELDIN-2021-TSALLIS-INF",
    "title": "Improved Analysis of the Tsallis-INF Algorithm in Stochastically Constrained Adversarial Bandits and Stochastic Bandits with Adversarial Corruptions",
    "authors": "Saeed Masoudian; Yevgeny Seldin",
    "source": "https://arxiv.org/abs/2103.12487",
    "scenarios": [
      "SCN-BOBW-ADAPTIVE",
      "SCN-ADVERSARIAL-FINITE",
      "SCN-STOCHASTIC-FINITE"
    ],
    "proof_roots": [
      "Tsallis-INF analysis",
      "stochastic/adversarial interpolation",
      "gap-dependent bounds"
    ],
    "lean_leaf_families": [
      "stability term",
      "penalty term",
      "self-bounding conversion",
      "power-weight algebra"
    ],
    "memory_status": "paper-card"
  },
  {
    "id": "PPR-KATO-ITO-2024-LC-TSALLIS-INF",
    "title": "LC-Tsallis-INF: Generalized Best-of-Both-Worlds Linear Contextual Bandits",
    "authors": "Masahiro Kato; Shinji Ito",
    "source": "https://arxiv.org/abs/2403.03219",
    "scenarios": [
      "SCN-BOBW-ADAPTIVE",
      "SCN-LINEAR-GLM",
      "SCN-CONTEXTUAL"
    ],
    "proof_roots": [
      "Linear contextual Tsallis-INF",
      "hybrid stochastic/adversarial regret",
      "high-probability bounds"
    ],
    "lean_leaf_families": [
      "linear loss estimates",
      "Tsallis regularization",
      "confidence-plus-FTRL bridge"
    ],
    "memory_status": "paper-card"
  },
  {
    "id": "PPR-ADAPTIVE-LR-FTRL-2024",
    "title": "A Simple and Adaptive Learning Rate for FTRL in Online Learning with Minimax Regret of Theta(T^(2/3)) and its Application to Best-of-Both-Worlds",
    "authors": "Taira Tsuchiya; Shinji Ito",
    "source": "https://arxiv.org/abs/2405.20028",
    "scenarios": [
      "SCN-BOBW-ADAPTIVE",
      "SCN-ADVERSARIAL-FINITE"
    ],
    "proof_roots": [
      "adaptive learning rates",
      "FTRL stability",
      "best-of-both-worlds"
    ],
    "lean_leaf_families": [
      "learning-rate schedule",
      "stability/penalty split",
      "self-bounding conversion"
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
    "id": "SCN-BOBW-ADAPTIVE",
    "name": "best-of-both-worlds and adaptive adversarial bandits",
    "core_algorithms": [
      "Tsallis-INF",
      "LC-Tsallis-INF",
      "adaptive-learning-rate FTRL",
      "self-bounding FTRL"
    ],
    "leaf_families": [
      "Tsallis entropy regularization",
      "self-bounding regret conversion",
      "stability/penalty split",
      "adaptive learning-rate schedule"
    ],
    "mathlib_needs": [
      "MLIB-FINSET-SUMS",
      "MLIB-REAL-RPOW-TSALLIS",
      "MLIB-CONVEX-LINALG",
      "MLIB-EXP-LOG-INEQUALITIES"
    ],
    "source_cards": [
      "PPR-ZIMMERT-SELDIN-2018-TSALLIS-INF",
      "PPR-MASOUDIAN-SELDIN-2021-TSALLIS-INF",
      "PPR-KATO-ITO-2024-LC-TSALLIS-INF",
      "PPR-ADAPTIVE-LR-FTRL-2024"
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

## Proof Weapon Cards

These cards are planning inspiration only.  They do not certify any theorem.

```json
[
  {
    "id": "WEAPON-UCB-OPTIMISM",
    "name": "optimism under uncertainty",
    "kind": "proof-inspiration",
    "upper_planning_use": "Generate candidate routes for index-based stochastic bandit and finite-horizon RL regret proofs.",
    "lower_agent_rule": "Do not cite optimism as a theorem; instantiate local index definitions, confidence events, and compiled pull-count/regret leaves.",
    "source_cards": [
      "PPR-AUER-CBF-2002-UCB1",
      "PPR-AZAR-OSBAND-MUNOS-2017-UCBVI",
      "TXT-LATTIMORE-SZEPESVARI-2020"
    ],
    "direct_reuse_cards": [
      "LML-UCB-REGRET",
      "MLIB-REAL-LOG-SQRT",
      "MLIB-PROBABILITY-SUBGAUSSIAN",
      "LOCAL-LEAF-FINITE-BOOKKEEPING"
    ],
    "blocked_leaves": [
      "confidence event API",
      "positive pull count before index use",
      "tail summability"
    ]
  },
  {
    "id": "WEAPON-TAIL-INEQUALITIES",
    "name": "sub-Gaussian, Hoeffding, Chernoff, and variance tails",
    "kind": "proof-inspiration",
    "upper_planning_use": "Select the weakest tail route matching reward assumptions: bounded, sub-Gaussian, conditional sub-Gaussian, or finite-variance.",
    "lower_agent_rule": "Use Mathlib/LML declarations or task-local cited results; do not reprove a tail inequality inside an algorithm file.",
    "source_cards": [
      "TXT-LATTIMORE-SZEPESVARI-2020",
      "TXT-BUBECK-CESABIANCHI-2012"
    ],
    "direct_reuse_cards": [
      "MLIB-PROBABILITY-SUBGAUSSIAN",
      "MLIB-PROBABILITY-MGF",
      "MLIB-PROBABILITY-VARIANCE",
      "MLIB-PROBABILITY-INDEPENDENCE"
    ],
    "blocked_leaves": [
      "measurability/integrability contract",
      "independence or filtration contract",
      "tail-event union bound"
    ]
  },
  {
    "id": "WEAPON-TSALLIS-INF-FTRL",
    "name": "Tsallis entropy FTRL and best-of-both-worlds bandits",
    "kind": "proof-inspiration",
    "upper_planning_use": "Propose routes for stochastic/adversarial interpolation, self-bounding regret, and adaptive learning-rate FTRL tasks.",
    "lower_agent_rule": "Do not treat the weapon as a reusable theorem; first formalize Tsallis regularizer, simplex constraints, FTRL optimality, and stability/penalty leaves.",
    "source_cards": [
      "PPR-ZIMMERT-SELDIN-2018-TSALLIS-INF",
      "PPR-MASOUDIAN-SELDIN-2021-TSALLIS-INF",
      "PPR-KATO-ITO-2024-LC-TSALLIS-INF",
      "PPR-ADAPTIVE-LR-FTRL-2024"
    ],
    "direct_reuse_cards": [
      "MLIB-REAL-RPOW-TSALLIS",
      "MLIB-CONVEX-LINALG",
      "MLIB-FINSET-SUMS",
      "MLIB-EXP-LOG-INEQUALITIES"
    ],
    "blocked_leaves": [
      "simplex probability vector API",
      "Tsallis entropy algebra",
      "FTRL one-step optimality",
      "stability/penalty decomposition"
    ]
  },
  {
    "id": "WEAPON-EXP3-POTENTIAL",
    "name": "exponential weights potential",
    "kind": "proof-inspiration",
    "upper_planning_use": "Plan adversarial finite-arm regret proofs using importance-weighted losses and potential telescoping.",
    "lower_agent_rule": "Use exact exponential/log inequalities from Mathlib and expose estimator unbiasedness as separate leaves.",
    "source_cards": [
      "PPR-AUER-CFS-2002-EXP3",
      "TXT-BUBECK-CESABIANCHI-2012"
    ],
    "direct_reuse_cards": [
      "MLIB-EXP-LOG-INEQUALITIES",
      "MLIB-FINSET-SUMS",
      "MLIB-MEASURE-INTEGRAL"
    ],
    "blocked_leaves": [
      "importance-weighted estimator API",
      "potential telescope",
      "learning-rate algebra"
    ]
  },
  {
    "id": "WEAPON-SELF-NORMALIZED-OFUL",
    "name": "self-normalized concentration for OFUL/LinUCB",
    "kind": "proof-inspiration",
    "upper_planning_use": "Route linear/GLM bandit proofs through Gram matrix monotonicity, confidence ellipsoids, and elliptical potential.",
    "lower_agent_rule": "Separate linear algebra leaves from stochastic-process leaves; do not hide determinant or norm side conditions.",
    "source_cards": [
      "PPR-ABBASI-YADKORI-2011-SELF-NORMALIZED",
      "PPR-LI-CHU-LANGFORD-SCHAPIRE-2010-LINUCB"
    ],
    "direct_reuse_cards": [
      "MLIB-CONVEX-LINALG",
      "MLIB-MARTINGALE-STOCHASTIC",
      "MLIB-REAL-LOG-SQRT"
    ],
    "blocked_leaves": [
      "Gram matrix API",
      "elliptical potential",
      "martingale self-normalized tail"
    ]
  },
  {
    "id": "WEAPON-POSTERIOR-SAMPLING",
    "name": "posterior sampling and probability matching",
    "kind": "proof-inspiration",
    "upper_planning_use": "Plan Thompson-sampling and Bayesian regret proofs around posterior action identities and Bayes-risk decompositions.",
    "lower_agent_rule": "Use LML posterior theorem cards when available; otherwise formalize kernels and conditional distributions before regret algebra.",
    "source_cards": [
      "PPR-AGRAWAL-GOYAL-2011-TS",
      "TXT-SLIVKINS-2019-2024"
    ],
    "direct_reuse_cards": [
      "LML-TS-POSTERIOR-ACTION",
      "LML-TS-BAYES-REGRET",
      "MLIB-PROBABILITY-KERNEL",
      "MLIB-CONDITIONAL-EXPECTATION"
    ],
    "blocked_leaves": [
      "posterior kernel",
      "conditional distribution identity",
      "Bayesian regret integrability"
    ]
  },
  {
    "id": "WEAPON-KL-CHANGE-OF-MEASURE",
    "name": "KL change-of-measure and information lower bounds",
    "kind": "proof-inspiration",
    "upper_planning_use": "Generate lower-bound and KL-UCB confidence-inversion routes for Bernoulli or bounded reward models.",
    "lower_agent_rule": "Record KL definitions, convexity, and absolute-continuity assumptions explicitly before any theorem reuse.",
    "source_cards": [
      "PPR-GARIVIER-CAPPE-2011-KLUCB",
      "TXT-LATTIMORE-SZEPESVARI-2020"
    ],
    "direct_reuse_cards": [
      "MLIB-EXP-LOG-INEQUALITIES",
      "MLIB-MEASURE-INTEGRAL",
      "MLIB-ORDER-ALGEBRA"
    ],
    "blocked_leaves": [
      "Bernoulli KL API",
      "change-of-measure lemma",
      "confidence-set inversion"
    ]
  },
  {
    "id": "WEAPON-PRIMAL-DUAL-BWK",
    "name": "primal-dual resource accounting for bandits with knapsacks",
    "kind": "proof-inspiration",
    "upper_planning_use": "Plan resource-constrained bandit proofs through budget traces, stopping times, and Lagrangian comparisons.",
    "lower_agent_rule": "Expose budget feasibility and stopping-time assumptions as reusable contracts before final regret proof work.",
    "source_cards": [
      "PPR-BADANIDIYURU-KLEINBERG-SLIVKINS-2013-BWK",
      "TXT-SLIVKINS-2019-2024"
    ],
    "direct_reuse_cards": [
      "MLIB-FINSET-SUMS",
      "MLIB-ORDER-ALGEBRA",
      "MLIB-MEASURE-INTEGRAL"
    ],
    "blocked_leaves": [
      "resource consumption trace",
      "budget stopping time",
      "dual feasibility"
    ]
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
[]
```

## Reviewer Gate

```bash
python3 tools/bandit.py check
```
