# NeurIPS 2025 delayed-feedback BoBW feasibility audit

Task id: `PAPER-AUDIT-NEURIPS-2025-DELAYED-BOBW-FEASIBILITY`

Kind: `literaturePort`

Status: `activePort`

Harness: `hierarchical`

## Goal

Freeze the exact external source and compile the smallest source-semantic
delayed-feedback leaf without claiming either paper-level regret theorem.
Use the result to decide whether the exact coupled route is feasible under the
current BanditRLlib interfaces.

## Source placement

- Source card:
  `PPR-SCHLISSELBERG-LANCEWICKI-AUER-MANSOUR-2025-DELAYED-BOBW`.
- Scenarios: `SCN-DELAYED-BOBW`, `SCN-DELAYED-BATCHED`,
  `SCN-BOBW-ADAPTIVE`.
- Route: `ROUTE-ROBUST-NONSTATIONARY-DELAYED`.
- Mathlib cards: `MLIB-FINSET-SUMS`,
  `MLIB-MARTINGALE-STOCHASTIC`, `MLIB-CONDITIONAL-EXPECTATION`.
- Inspiration only: `WEAPON-TAIL-INEQUALITIES`.

## Exact first target

Compile the page-4 feedback semantics:

```lean
DelayedFeedback.observedBefore delay t ∪
  DelayedFeedback.outstandingAt delay t = Finset.range t
```

and its disjoint/cardinality consequences, using the paper's strict
availability condition `s + delay s < t`.

## Current progress

- [x] Freeze the official camera-ready and its SHA-256 before proof search.
- [x] Compile the exact strict-availability partition and cardinality leaves.
- [x] Compile an action-time outstanding-count maximum and pointwise bounds.
- [x] Prove the one-based/end-of-round bridge to the paper's `sigma(t)`;
  the bridge explicitly shifts paper source round `s + 1` to zero-based `s`.
- [x] Compile the generic same-algorithm multi-regime Lean interface before
  implementing Delayed SAPO state.  This interface packages shared identity
  fields only; it proves neither source endpoint.
- [x] Compile a causal pre-action view that exposes past actions and only
  strictly available losses.  Observation-equivalent hidden worlds induce the
  same decision for every rule typed on this view.
- [x] Compile the set-level `B(t) \ S` processing invariant: available sets are
  monotone, new arrivals are disjoint from processed rounds, and processing
  the whole batch yields exactly the current available set.  Sequence order
  and confidence-state updates remain open.
- [x] Compile Algorithm 5 line 15's active-arm allocation.  Given a nonempty
  active set, nonnegative eliminated-arm probabilities, and eliminated mass at
  most one, every coordinate is nonnegative and the full vector sums to one.
- [x] Compile Algorithm 5 lines 7--8 as an elimination snapshot and close the
  deterministic core of source Lemma D.9: the optimal arm survives whenever
  the relevant stochastic-good-event confidence and `ucbStar` certificates
  hold.  Consequently the post-elimination active set is nonempty.
- [x] Replace the independent `muStar <= ucbStar` projection with a
  source-shaped confidence snapshot.  The elimination slice of Definition
  D.1 now derives that inequality from both upper-confidence surfaces,
  constructs the survival certificate, and transports any supplied
  complement-good-event bound to an optimal-arm-elimination bound.  The full
  event and its D.2--D.7 component probability producers remain open.
- [x] Compile the exact Corollary-D.8 union assembly.  Six named source
  components consume the source-exact three `2/T` and three `1/T` bounds of
  Lemmas D.2--D.7, prove the paper's `9/T` complement-good-event budget, and
  compose a recorded full-event projection with the D.9 optimal-survival
  consumer.  The six component concentration proofs and projection remain
  open upstream obligations.
- [x] Audit the Lemma-D.10-to-D.12 gap-ordering bridge. The frozen PDF's
  prefix-to-elimination width inequality points opposite to the inverse-square-
  root width's count monotonicity. Compile the direction diagnostic, the exact
  conditional four-edge consumer, and conditional same-snapshot factor-20
  skeletons.  Lean now also proves the exact small-count scalar implication
  `count <= 192 * log T -> 1 <= 10 * width` and consumes the source-shaped
  large/small-count disjunction without imposing factor three on the small
  branch.  The downstream processed-prefix producer now supplies those
  algebraic inputs from a source-time ledger and D.1 count certificate.  Keep
  Lemma 4.2 unverified pending the generated-trajectory construction, D.4
  probability proof, ordered elimination trace, and a source-faithful endpoint
  repair or clarification; the deterministic processed-trace-summary adapter
  is now compiled below.
- [x] Compile the source-time processed-prefix count producer.  The ledger
  records the chosen arm and line-15 allocation at each source round, derives
  equal cumulative pull mass for arms that remain active, and combines the
  exact D.1 count inequalities with the source width and recursive-UCB
  definitions.  It produces the large/small branch, the same-prefix
  factor-ten width edge, and a conditional same-snapshot factor-20 gap theorem
  without accepting either target edge as a premise.
- [x] Compile the deterministic processed-trace-summary adapter.  The summary
  records distinct source indices for processed items, permits
  nonchronological processing order, carries the exact strict availability
  witness `s + d_s < t`, and reads actions and line-15 allocations at each
  source index.  It keeps the intra-round active set separate from the
  antitone source-round trace and records current-to-source containment as an
  explicit summary invariant.  A future Algorithm-5 producer must prove both
  that invariant and source-trace antitonicity.  Source width and recursive empirical UCB are
  definitions of the projected snapshot rather than certificate premises.
  Given the two explicit D.4 count inequalities, the adapter constructs the
  existing count certificate and reaches the conditional same-snapshot
  factor-20 theorem.  Constructing this summary from the full randomized
  Algorithm-5 transition system and proving D.4's simultaneous `2/T`
  probability bound remain open.
- [x] Reuse the existing finite-action law to turn the certified line-15
  vector into a probability measure, and lift causal allocation rules to
  measure-valued rules that remain identical in observation-equivalent hidden
  worlds.  Measurable history kernels and recursive trajectories remain open.

## Nonclaims

This task does not compile Theorem 4.1, full Lemma D.9, unconditional Lemma
D.10 or D.12, Lemma 4.2, Theorem
5.1, Corollary 5.4, Algorithm 5, or a best-of-both-worlds endpoint.  The
compiled Lemma-D.9 layer is only a one-snapshot deterministic implication plus
an elimination-event probability-bound consumer.  The full Definition-D.1
event, the D.2--D.7 component producers and full-event projection, and persistence through
the recursive algorithm are open.  This task
does not show that the external paper is correct or audited.  Later promotion requires the same
algorithm, initialization, tuning, information structure, comparator, and
regime endpoints to close in Lean.

## Gate

```bash
lake env lean BanditRLProof/DelayedFeedback/StochasticGapOrderingAudit.lean
lake env lean BanditRLProof/DelayedFeedback/ProcessedPrefixCounts.lean
lake env lean BanditRLProof/DelayedFeedback/RecursiveProcessedState.lean
lake env lean BanditRLProof/DelayedFeedback/Accounting.lean
lake env lean BanditRLProof/DelayedFeedback/MultiRegimeContract.lean
lake env lean BanditRLProof/DelayedFeedback/CausalView.lean
lake env lean BanditRLProof/DelayedFeedback/Processing.lean
lake env lean BanditRLProof/DelayedFeedback/ActiveAllocation.lean
lake env lean BanditRLProof/DelayedFeedback/Elimination.lean
lake env lean BanditRLProof/DelayedFeedback/ActionLaw.lean
lake env lean Tests/DelayedFeedbackPaperAuditCanary.lean
lake env lean Tests/DelayedFeedbackProcessedPrefixCountsCanary.lean
lake env lean Tests/DelayedFeedbackRecursiveProcessedStateCanary.lean
python3 tools/bandit.py check
```

The full 8,838-job Lean gate, proof-graph export, and 118-test Python suite
passed again on 2026-08-18 after adding the D.10--D.12 audit layer.  The
isolated worktree remains at a short Windows path to avoid an unrelated
long-path `.olean` creation failure.

On 2026-08-25, after adding the deterministic processed-trace-summary adapter,
`python -B tools/bandit.py check` passed the complete current gate: the root
Lean build completed 8,830 jobs, the `Tests` build completed 8,852 jobs, the
proof-graph exporter ran, and all 217 Python tests passed (6 skipped).  The
focused trace-summary module and canary also compile, and their reported axioms
are limited to `propext`, `Classical.choice`, and `Quot.sound`.  The target-drift
v2 and external-comparator validators pass structurally while continuing to
report their 450-run and 30-case studies as planned and unrun.  A read-only
frontier shadow reports no lifecycle mismatch.

This verification promotes exactly nine additional source-audit declarations,
for a delayed-feedback total of 133.  It does not promote the Algorithm-5
transition-and-invariant-to-summary producer, a measurable generated Delayed
SAPO trajectory, the simultaneous D.4 probability bound, ordered elimination,
or any terminal regret theorem; those obligations remain open.
