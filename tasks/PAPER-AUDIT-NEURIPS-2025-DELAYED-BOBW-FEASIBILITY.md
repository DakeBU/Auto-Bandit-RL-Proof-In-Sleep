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
  probability proof, unconditional source endpoint,
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
- [x] Compile one ordered no-switch processing step for Algorithm 5 lines
  3--4 and 7--8.  `OrderedProcessingTransition.lean` keeps the paper sequence
  as a duplicate-free list, accepts an arbitrary member of `B(t) \ S`, and
  appends it without sorting before producing the line-7 summary.  Lean derives
  source-index injectivity, the exact strict `s + d_s < t` witness, and
  current-to-source activity containment from an antitone source trace and a
  round-start invariant.  The line-8 successor uses the exact
  `remainingActive` set and preserves that invariant.  A canary processes
  source round one after source round three.  The numerical BSC/EAP updates,
  generated trajectory, D.4 probability theorem, switch path, and every regret
  endpoint remain open.
- [x] Compile the finite ordered no-switch structural trace.  The trace
  combine exact line-8 processing steps with an explicit exhausted-round
  advance, prove active-set monotonicity along the reflexive-transitive path,
  and derive the later-arm-remains premise needed by the existing
  D.4-conditional factor-20 consumer.  The 12-declaration module does not
  accept that temporal premise as an input and does not promote BSC/EAP
  generation, a probability law, D.4, a switch path, or any regret endpoint.
- [x] Audit and compile the deterministic core of Appendix Lemma D.11 on the
  nonnegative stochastic-loss-gap domain used by the Markov step.  The
  six-declaration `StochasticGapHalfSet.lean` leaf states that premise
  explicitly, handles the empty and zero-average cases, and specializes it to
  source stochastic loss gaps using only optimal-arm minimality.  The
  unrestricted real-valued formulation is not promoted; a signed regression
  canary guards that premise boundary without claiming a source correction.
  Lemma D.13 and the stochastic regret endpoint remain open.
- [x] Compile Algorithm 5 line 10's newly eliminated-arm initializer.
  `EliminatedArmInitialization.lean` freezes the line-4 processed order and
  empirical mean, and defines the literal source values
  `p_i^1 = 1/(2K) + n_i(S)/(2T)`, `Delta-tilde_i = 8 width_i(S)`, and
  `N_i^1 = 1280/(p_i^1 * Delta-tilde_i^2)`.  Its 31 declarations update only
  the line-7 eliminated set, preserve surviving-arm bank entries, and prove
  positivity under the explicit nontrivial-horizon boundary `1 < T`.  A
  concrete two-arm canary checks one eliminated and one surviving arm.  This
  is an initialization producer only: EAP phase transitions, BSC, sampling,
  the generated trajectory, and both regret endpoints remain open.
- [x] Reuse the existing finite-action law to turn the certified line-15
  vector into a probability measure, and lift causal allocation rules to
  measure-valued rules that remain identical in observation-equivalent hidden
  worlds.  Measurable history kernels and recursive trajectories remain open.

## Nonclaims

This task does not compile Theorem 4.1, full Lemma D.9, unconditional Lemma
D.10 or D.12, Lemma D.13, Lemma 4.2, Theorem
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
lake env lean BanditRLProof/DelayedFeedback/OrderedProcessingTransition.lean
lake env lean BanditRLProof/DelayedFeedback/OrderedNoSwitchTrace.lean
lake env lean BanditRLProof/DelayedFeedback/StochasticGapHalfSet.lean
lake env lean BanditRLProof/DelayedFeedback/EliminatedArmInitialization.lean
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
lake env lean Tests/DelayedFeedbackOrderedProcessingTransitionCanary.lean
lake env lean Tests/DelayedFeedbackOrderedNoSwitchTraceCanary.lean
lake env lean Tests/DelayedFeedbackStochasticGapHalfSetCanary.lean
lake env lean Tests/DelayedFeedbackEliminatedArmInitializationCanary.lean
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

On 2026-08-25, the focused ordered-processing module and its nonchronological
canary compile.  Their five representative axiom reports contain only
`propext`, `Classical.choice`, and `Quot.sound`.  This structural slice contains
15 named declarations, so the delayed-feedback source-audit total becomes 148
at that checkpoint.  The one-step leaf by itself does not promote the
numeric BSC/EAP transition, a generated trajectory, D.4, a switch decision, an
ordered multi-snapshot theorem, or a regret endpoint; the next trace leaf
closes only the deterministic temporal premise.

On 2026-08-25, the focused ordered no-switch trace module and canary compile.
An independent semantic review verified the direction of active-set
monotonicity, the round-close/advance index alignment, and the temporal
membership transport, with no P0--P2 finding.  Four representative axiom
reports contain only `propext`, `Classical.choice`, and `Quot.sound`.  The
module contributes 12 named declarations, bringing the delayed-feedback
source-audit inventory to 160.  The final factor-20 theorem remains explicitly
conditional on the earlier D.4 count clause and elimination-good projection;
numeric BSC/EAP generation, the randomized trajectory, D.4 probability,
switching, and both regret endpoints remain open.

The repository-wide gate then passed on the same checkout: `lake build` and
the root `Tests` target completed 8,856 jobs, proof-graph export succeeded,
and all 231 Python tests passed with 6 expected skips.  The target-drift
execution template remains structurally valid but deliberately not ready:
26 machine fields and named human/provenance choices are unset, so no
450-primary or 30-external result is claimed.

On 2026-08-25, the focused D.11 domain leaf and Algorithm-5 line-10 initializer,
together with their two canaries, compile in the isolated worktree.  The
former contributes six and the latter 31 named source-audit declarations,
bringing the inventory from 160 to 197.  Representative axiom reports contain
only `propext`, `Classical.choice`, and `Quot.sound`.  After staging the four
new Lean files so the anonymous-supplement inventory could see them and using
the real Python executable rather than the WindowsApps alias, the repository
gate `python -B tools/bandit.py check` passed: the root Lean build completed
8,834 jobs, the `Tests` target completed 8,860 jobs, proof-graph export
succeeded, and all 231 Python tests passed with 6 expected skips.  The
target-drift execution template remains structurally valid but deliberately
`prepared_unbuilt`: 26 machine fields and the named human/provenance choices
remain unset, so no execution result is claimed.

The Lean-verified site build and checker also passed on this checkout.  The
generated site contains 640 HTML pages, 586 modules, 7,844 declarations, 80
milestones, 14 Mermaid blocks, and 16,951 Lean source links; internal links and
anchors, README-relative links, MathJax fallbacks, and the Pages workflow all
validate.  This verification still does not promote D.13, EAP/BSC transitions,
D.4, a generated law, or either endpoint.
