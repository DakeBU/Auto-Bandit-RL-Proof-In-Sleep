# Orabona OGD source contract v1

Task: ONLINE-OGD-CH2-FIXED. State: accepted-local (see runs/online-ogd-20260913/acceptance.json).
The draft and stabilization precede proof search in the retained transition ledger.
Canonical source repository: E:/ABRL/research; isolated implementation branch:
`codex/research-online-ogd`, baseline `eedcda1db4d84f6bd69ec6ee50e174f6cf4056ac`.

## Source provenance and audit

Francesco Orabona, Online Learning: A Modern Introduction Using Convex Optimization,
arXiv:1912.13213v10, 21 June 2026, https://arxiv.org/pdf/1912.13213v10.
Downloaded 2026-09-13 to `tmp/pdfs/orabona-v10.pdf` (ignored local source cache).
SHA256: `cef4edfa97a6e063e53e9c532717c50aa156e5bc782ea49f969b3385011a1b17`.
PDF pages 24-27 (1-based), printed pages 12-15. Theorem 2.7 is on printed p.11.
Text and rendered PDF pages 24-27 were inspected, including all scoped formulas.
The full PDF is not redistributed in the public repository; URL and digest pin retrieval.

Algorithm 2.1 generates the next point by projecting the current gradient step.
Proposition 2.11 decreases distance to a feasible point. Lemma 2.12 includes BOTH
loss linearization and the quadratic potential inequality. Theorem 2.13 has two
branches: only the constant-step branch is in this contract. Its terminal squared
distance is subtracted. Printed p.14 explicitly permits an unbounded domain in
this branch. Eq. (2.1) uses a diameter upper bound and a gradient upper bound,
called L in the source and G here, and a horizon-tuned constant step.

## Semantic signature and exact target

Exact declaration headers are frozen by native statement fences after draft type
elaboration. File: `BanditRLProof/OnlineGradientDescent.lean`, namespace
`BanditRL.OnlineGradientDescent`. Definitions are also part of the frozen contract.

- Carrier: real Hilbert space E; finite-dimensional real Euclidean spaces are
  instances. Completeness enables projection; no compactness or boundedness is
  hidden in the fixed-step target. This is a conservative dimensional generalization.
- Feasible set: `Domain` stores a nonempty closed convex set. It has no losses,
  comparator, claimed descent inequality, or regret certificate as fields.
- Losses: real-valued functions on E, convex and differentiable on an open
  neighborhood of V (`RegularLoss`). Only the neighborhood matters. The finite
  loss prefix may have separate neighborhoods; their finite intersection gives
  a common open neighborhood if desired. No future-gradient oracle is assumed.
- Index: Lean t=0 is printed round 1; `iterate ... 0=x₁`, `iterate ... T=x_(T+1)`;
  sums use `Finset.range T`. Zero horizon is allowed for the fixed-step identity.
- Information: trajectory defined by recursion using loss t only to construct
  point t+1. `iterate_prefix` states strict-prefix causality. Losses are arbitrary
  deterministic functions; pathwise application to an adaptive loss realization
  does not introduce any probabilistic or expected-regret claim.
- Comparator: arbitrary u in V, quantified after the SAME generated trajectory;
  the fixed-step theorem does not tune eta to u or to future gradients.
- Step: eta>0 for bounds; construction itself is total for any eta.
- Tuned endpoint: T>0, D>0, G>0, eta=D/(G sqrt T). Gradient assumption refers to
  this tuned trajectory. `equation_2_1` supplies all comparators from a uniform
  diameter bound; `equation_2_1_distance` is its initial-distance helper.
  D and G are a priori valid bounds, not exact suprema requiring attainment.
- Evidence: exact kernel proof and public canary required. Draft elaboration with
  incomplete bodies is NOT a compiled proof; notes/API search are route evidence.
- Exclusions: decreasing steps, all of Chapter 2, general subgradients/OMD/FTRL,
  Tsallis dual guarantees, merging, and deployment.

## Initial dependency DAG / architect output

| Node | Dependencies | Target / route | Class |
|---|---|---|---|
| projection | mathlib Hilbert minimizer existence/characterization | project_spec, project_eq_of_variational, proposition_2_11 | reusable mathematics |
| linearization | convex secant slope, gradient Frechet derivative | first_order by restriction to an affine line | reusable mathematics |
| algorithm | projection | step, iterate, iterate_mem, iterate_prefix | project-local source algorithm |
| one-step | projection, linearization | lemma_2_12 by squared norm expansion | reusable mathematics |
| fixed-terminal | algorithm, one-step | theorem_2_13_fixed by finite telescoping | source terminal |
| tuned-terminal | fixed-terminal, positive square-root algebra | equation_2_1_distance, equation_2_1 | source terminal |
| canary | all above | changing linear losses with active projection; nonzero terminal residual | validation |

Local APIs searched at pinned mathlib `5e932f97dd25535344f80f9dd8da3aab83df0fe6`:
`exists_norm_eq_iInf_of_complete_convex`, `norm_eq_iInf_iff_real_inner_le_zero`,
`ConvexOn.comp_affineMap`, `ConvexOn.le_slope_of_hasDerivAt`,
`HasFDerivAt.comp_hasDerivAt`, `DifferentiableOn.hasGradientAt`,
`InnerProductSpace.toDual_apply`, `norm_sub_sq_real`, `norm_add_sq_real`.
No multivariate convex-gradient inequality was located; use the existing
one-dimensional secant inequality on the affine segment instead of adding a premise.
Rejected: assumed single-step regret certificate (misses producer), generic FTRL
consumer (wrong algorithm), external unbuilt library (not proof evidence).

## Authority and lifecycle

Same model in sequential director, architect, worker, and reviewer phases;
no independent reviewer or multi-agent experiment is claimed. Authorized edits:
new OGD module, public imports/Tests, this task's evidence, and shared Book mapping.
Preserve unrelated SGB active frontier. Native CLI scaffolding/fences/verifiers
are used; method-level transitions also require written semantic review, not
an invented claim that a single runtime enforces the whole process.
Statement changes after stabilization require a versioned repair and review.
Proof failures with unchanged statements retain logs and repair the proof body.
