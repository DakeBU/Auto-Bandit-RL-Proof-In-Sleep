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
