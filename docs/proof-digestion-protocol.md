# BanditRLlib Proof Digestion Protocol

BanditRLlib adopts a source-first lifecycle:

Formalize → Audit → Compress → Explain.

The purpose is not merely to produce compiling Lean. It is to make bandit/RL
proofs easier to inspect, compare, and reuse without leaving machine-generated
bookkeeping as the public mathematical interface.

## 0. Three declaration levels

Use the full source audit only where mathematical meaning is public.

- **A. Source Anchor** — a theorem/definition tied to a paper, textbook or
  explicit original-result contract. It requires Statement Seal, binder or
  definition audit, source-proof coverage/topology review, semantic round trip,
  Proof Seal, publication and purification.
- **B. Canonical Library Node** — a reusable Bandit/RL lemma or interface.
  Require Lean proof/axiom cleanliness, search/reuse evidence, canonicality,
  real or plausible consumers, and duplicate/wrapper purification. Do not
  pretend it is a source theorem when it is library infrastructure.
- **C. Internal Provider** — a private or theorem-local implementation helper.
  Require compilation, no fake closure or assumption smuggling, and
  reachability/dead-code cleanup. It earns no independent source-formalization
  credit.

Do not make every internal helper pay the Source-Anchor review cost; concentrate
the strongest audit on the constitutional public mathematical interface.

This protocol complements AGENTS.md, docs/theorem-publication-protocol.md, and
docs/contributor-codex-contract.md.

## 1. Freeze the target before proving it

Every new or materially changed source-facing theorem or definition is a
**Source Anchor**. Before proof search, record:

- exact paper/book/version/section/theorem anchor;
- exact state/action/reward/observation spaces;
- horizon, time index and stopping convention;
- filtration/adaptivity and feedback model;
- probability mode, confidence level and event quantification;
- regret/value/sample-complexity convention and constant-dependence scope;
- the exact final Lean signature and a versioned statement digest.

The exact final signature may be elaborated in an untracked probe. The
production repository remains zero-sorry.

After STATEMENT_SEALED, a proof worker may change proofs and internal helpers,
but it may not strengthen the public theorem to make Lean easier. A real
correction creates a versioned successor and invalidates dependent audit/topology
evidence.

## 2. Binder audit

Recursively expand every project-owned Prop, structure, assumption bundle and
typeclass used by a Source Anchor. Classify every logical input as exactly one
of:

- SOURCE: explicit premise of the cited statement;
- STANDING: field of a separately audited source-wide standing assumption;
- TYPING: carrier/type information implicit in the source convention;
- RULED: explicit human-approved correction;
- EXCESS: any other proof result or convenience premise.

EXCESS fails a source-facing Anchor.

The invariant is:

    proof ingredient = dependency edge
    source hypothesis = theorem binder

If the proof needs a concentration bound, confidence event, martingale
property, occupancy identity, Bellman relation, optimism lemma, stopping-time
bound, coverage estimate or change-of-measure inequality, prove/reuse it and
apply it inside the proof. The existence of a producer does not make the
producer's conclusion a legitimate public hypothesis.

High-risk ABRL drift points include hidden fixed-horizon assumptions,
nonanticipativity/adaptivity moved into a convenience class, full-information
assumptions accidentally replacing bandit feedback, conditioning on an event
that the source only proves later, high-probability and in-expectation
statements silently interchanged, and constants depending on the instance when
the source claims uniformity.

## 3. Definition audit

Every source-facing definition declares one of:

- literal;
- characterized;
- quotient/representative.

A literal definition must agree on its whole carrier.

A characterized object must first receive the true source-level
well-definedness theorem. If uniqueness is part of the source semantics, prove

    exists unique x such that Phi(x)

before using classical choice. A fallback/default branch that invents
off-source behavior is rejected.

For quotient/representative objects, record the equivalence relation and
representative-independence obligations.

Bandit/RL examples needing care include policies modulo null histories,
conditional value functions, occupancy measures, belief states, confidence
regions, stopping rules, stationary distributions, and information-ratio
objects.

## 4. Source Proof Graph: reconstruct the author's proof independently

Before implementation Lean is allowed to shape the exposition, build a
source-only proof graph.

The extractor/reviewer may inspect the source and sealed public Anchor, but may
not use implementation Lean to decide the source topology.

Every in-scope theorem, definition, reused equation, citation, and substantive
proof paragraph is assigned exactly one disposition: NODE with a stable id, or
EXCLUDED with an explicit reason.

Unnamed probability decompositions, union bounds, telescoping steps, confidence
budget allocations and conditioning arguments count as source obligations when
they materially carry the proof.

Missing source bridges are explicit SOURCE_GAP nodes rather than silently
supplied from memory. Each edge cites the consumer use-site and shows where
conditional premises are discharged.

## 5. Alternative proof routes are OR-routes

A target with two sufficient routes

    A and B imply T
    C and D imply T

is represented as

    (A and B) or (C and D) imply T

not as the false AND dependency A,B,C,D -> T.

This matters in BanditRLlib because a bound may admit a confidence-set/optimism
route, a posterior/information route, an occupancy/Bellman route, a coupling or
simulation route, or a change-of-measure/testing lower-bound route.

The source route and the Lean implementation route may differ; provenance for
both remains explicit.

## 6. Four graph views

### Source Proof Graph

**Question:** How did the source prove the result?

Tracks the source theorem/step/citation topology, unnamed bookkeeping, source
gaps and OR-routes.

### Lean Dependency Graph

**Question:** What does the checked implementation actually depend on?

Tracks compiler-backed declarations/modules and reviewed proof dependencies.

### Compressed Bandit/RL Spine

**Question:** After removing implementation bookkeeping, which primitives
actually recur across problems?

Typical families include concentration, confidence sequences, optimism,
telescoping regret decompositions, Bellman/occupancy identities,
martingale/stopping arguments, information inequalities, testing reductions,
change of measure, dynamic programming and covering/complexity control.

### Functor Hypergraph

**Question:** Which mechanisms survive when feedback model, state space, action
space, horizon, oracle, divergence or objective changes?

These are reviewed conceptual transports, not theorem edges unless separately
formalized.

## 7. Paper decomposition for contribution analysis

For each formalized paper/result, maintain the reviewed decomposition

    G_paper = G_existing ∪ G_bookkeeping ∪ G_new_reusable ∪ G_new_topology.

- existing: already available BanditRLlib/Mathlib/LML substrate;
- bookkeeping: source-faithful compositions, event budgets, telescoping,
  conditioning, index manipulations and parameter accounting;
- new reusable: new canonical lemmas/interfaces useful beyond the paper;
- new topology: a genuinely new composition route.

This decomposition is evidence for research understanding. It is **not an
automatic novelty score** and must not be used to make scientific-value claims
from graph counts alone.

## 8. Proof Seal

A Source Anchor becomes PROOF_SEALED only if:

- the final Lean signature matches the Statement Seal;
- the actual target compiles under focused/repository checks;
- no unauthorized axiom, placeholder or wrapper closes the theorem;
- the binder audit has no EXCESS;
- every conditional premise is supplied by dependencies;
- blind reconstruction and independent source review are accepted, or a
  mismatch remains explicitly published;
- the Source Proof Graph shows which source obligations are discharged.

## 9. Purification gate

PROVED and MERGED are not the final reader-facing state.

After integration, a purification pass checks dead declarations, duplicate
semantics, wrapper-only lemmas, import minimization, canonicalization,
proof-route compression, graph compression, elaboration cost, and reader
compression.

The public graph keeps a lossless drill-down to the full Lean/source evidence,
while the default researcher view exposes the compressed proof architecture.

The rule is:

> **Do not leave machine garbage for humans.**

## 10. Lifecycle

    SOURCE_PINNED
      -> STATEMENT_SEALED
      -> SOURCE_TOPOLOGY_REVIEWED
      -> PROVED_LOCAL
      -> PROOF_SEALED
      -> PUBLISHED
      -> MERGED
      -> PURIFIED

Existing contribution/route status fields remain valid repository-integration
states. MERGED must not be interpreted as PURIFIED.

## 11. Required proof-digestion record

New Source Anchors and major paper routes must record these groups:

- statement_seal: source revision, statement version, signature digest,
  binder audit and definition kind;
- source_proof_coverage: inventory, reviewed nodes, excluded-with-reason items,
  source gaps and alternative routes;
- proof_digestion: existing substrate, bookkeeping, new reusable primitives and
  new topology;
- purification: pending/purified status, dead-code audit, duplicate-semantics
  audit, canonicalization, compressed-spine delta and reader default view.

These are normative protocol requirements. Existing machine-readable contracts
may migrate incrementally; no migration may weaken the current source,
semantic, Lean, route, graph or website gates.


## Design provenance

The source-first statement-sealing, independent source dependency/coverage
graph, binder audit, definition audit, explicit alternative-route, and
post-proof cleanup ideas were informed by Scott N. Armstrong's October 2026
autoformalization workflow and the public LeanAutoformalizationSkills project:
https://www.scottnarmstrong.com/2026/10/autoformalization-is-now-very-easy/ and
https://github.com/scottnarmstrong/LeanAutoformalizationSkills.

This library adapts those ideas to its own trust model rather than copying the
workflow verbatim: production Lean remains zero-sorry, the existing
encoder-denoiser/source review remains mandatory, and the four-view
source/Lean/compressed/Functor proof-digestion stack plus PURIFIED reader state
are project-specific requirements.
