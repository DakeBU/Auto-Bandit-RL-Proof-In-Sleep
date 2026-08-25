# Conversion window: NeurIPS 2025 delayed-feedback BoBW feasibility

Task: `PAPER-AUDIT-NEURIPS-2025-DELAYED-BOBW-FEASIBILITY`

Status: `source-frozen; deterministic availability, action-time count,
one-based/end-of-round sigma bridge, generic shared-identity interface, causal
action-time view, set-level new-arrival processing, line-7/8 optimal-arm
survival, line-15 allocation, a causal one-round action measure, source-exact
  D.2--D.8 budget assembly, a processed-prefix D.1 count-to-width producer,
  its deterministic processed-trace-summary adapter, and one ordered
  no-switch Algorithm-5 structural processing step plus its finite trace
  ordering layer, the nonnegative-gap core of Lemma D.11, and Algorithm 5
  line-10 eliminated-arm initialization compiled; the D.4 count
clause is still conditional, and the D.2--D.7 probability producers,
measurable generated trajectory, unconditional source elimination theorem,
and paper endpoints
remain open`

## Source window

Official camera-ready SHA-256:
`525240c98b67616b4918bf5bffb799577f298786fc46538aff91153380ae0f9e`.

Physical PDF page 4 defines the feedback model.  A loss produced at source
round `s` is received after `d_s` rounds, and is available for the action at
round `t` exactly when `s + d_s < t`.  The source denotes the available set by
`B(t)={s:s+d_s<t}` and the number of missing observations by
`sigma(t)=|{s:s<=t, s+d_s>t}|` under its one-based presentation.

## Lean indexing decision

Lean uses zero-based source rounds `s ∈ Finset.range t` before action round
`t`.  We preserve the strict source condition exactly:

```text
observed before action t: s + delay s < t
outstanding at action t:  not (s + delay s < t)
```

The complement is taken only inside `Finset.range t`; future source rounds are
never counted as outstanding.  No `<=` replacement or action-time knowledge
of `delay s` is introduced into an algorithm interface.

## First leaf declarations

- `DelayedFeedback.observedBefore`;
- `DelayedFeedback.outstandingAt`;
- `DelayedFeedback.observedBefore_disjoint_outstandingAt`;
- `DelayedFeedback.observedBefore_union_outstandingAt`;
- `DelayedFeedback.card_observedBefore_add_card_outstandingAt`.
- `DelayedFeedback.outstandingCount`;
- `DelayedFeedback.maxOutstandingBeforeThrough`;
- `DelayedFeedback.outstandingCount_le_round`;
- `DelayedFeedback.outstandingCount_le_maxOutstandingBeforeThrough`.
- `DelayedFeedback.oneBasedDelayShift`;
- `DelayedFeedback.paperMissingAtEnd`;
- `DelayedFeedback.paperMissingAtEnd_eq_outstandingAt_oneBasedDelayShift`;
- `DelayedFeedback.paperMissingCount`;
- `DelayedFeedback.paperMissingCount_eq_outstandingCount_oneBasedDelayShift`;
- `DelayedFeedback.paperMissingCount_le_round`;
- `DelayedFeedback.paperSigmaMaxThrough`;
- `DelayedFeedback.paperMissingCount_le_paperSigmaMaxThrough`.

## Shared-identity target interface

`DelayedFeedback.SameAlgorithmMultiRegimeContract` packages one algorithm,
initialization, tuning, information object, and comparator.  Its
`stochasticClaim` and `adversarialClaim` definitions instantiate both endpoint
predicates with those same fields.  The two reflexive interface theorems and a
public canary compile.  This is a generic target schema: it does not construct
Delayed SAPO, assert either source theorem, or prove best-of-both-worlds
regret.

## Causal action-time view

`DelayedFeedback.ActionTimeView` exposes past actions as `some` exactly before
the current round and exposes a loss as `some` exactly on
`observedBefore delay t`.  Outstanding and future losses are `none`, and the
view data contains neither the delay trace nor the total loss trace.  The
compiled observation-equivalence theorem shows that two hidden worlds with
the same available source set, past actions, and revealed losses produce the
same view; consequently every `CausalDecisionRule` returns the same decision.
This is a deterministic information-interface theorem, not yet a randomized
action kernel or Delayed SAPO implementation.

## Newly observed processing

`DelayedFeedback.newlyObservedBefore delay processed t` is the set-level
translation of Algorithm 5's `B(t) \ S`.  The compiled layer proves monotonicity
of `observedBefore`, disjointness of processed and new rounds, exact recovery
of the current available set after `processAllNew`, and exclusion of
outstanding rounds from the new batch.  It deliberately does not choose the
source sequence order for simultaneous arrivals and does not update BSC/EAP
confidence state.

## Active-arm probability allocation

`DelayedFeedback.delayedSAPOProbability` formalizes Algorithm 5 line 15: EAP
supplies eliminated-arm coordinates, while the residual mass is divided
equally over a nonempty active set.  The compiled leaf proves active/inactive
coordinate formulas, nonnegativity under nonnegative eliminated coordinates
whose sum is at most one, and exact total mass one.  It does not yet prove that
EAP maintains those hypotheses or construct the sampling kernel.

## Ordered no-switch processing step

Physical PDF page 22, Algorithm 5 lines 3--4 choose an arbitrary
`s in B(t) \ S` and append it to the processed sequence; lines 7--8 test and
remove arms after the confidence surfaces for that appended prefix are formed.
`DelayedSAPONoSwitchProcessOne` refines the set-level `B(t) \ S` operation by
retaining Algorithm 5's ordered sequence as a duplicate-free `List Nat`.  One
step accepts any newly observed source round and appends it to the list without
sorting, so simultaneous arrivals remain intentionally nondeterministic.  The
compiled transition builds the line-7 `DelayedSAPOProcessedTraceSummary` only
after this append, derives source-index injectivity and strict
`s + d_s < t` availability, and derives current-to-source active-set
containment from a round-start invariant plus an antitone source-round trace.
Its line-8 successor uses the exact `remainingActive` set and preserves the
round-start invariant.  The focused canary processes source round one after
source round three.

This is a structural no-switch step.  The empirical means, confidence bounds,
and inactive-arm probabilities are explicit inputs; Lean does not claim that
BSC or EAP generated them.  The switch branch, round finalization, measurable
recursive sampling law, D.4 count probability, multi-snapshot elimination
on the generated trajectory, and regret endpoints remain open.

## Ordered no-switch trace ordering

`DelayedSAPONoSwitchStructuralStep` retains exactly two structural edges: the
line-8 successor of a verified processing step and an action-round advance
whose inner loop is certified exhausted.  Its reflexive-transitive closure is
not called a generated stochastic trajectory.  The compiled trace proves that
the current active set can only shrink, so membership in a later step's
eliminated set transports back to the earlier line-8 `remainingActive` set.
This removes the temporal survival premise previously supplied by the caller
of the repaired factor-20 theorem.

The trace layer has 12 named declarations.  Its final theorem still consumes
the earlier snapshot's explicit D.4 count clause and elimination-good
projection.  It does not generate the numerical BSC/EAP state, prove D.4's
probability, cover the switch branch, or establish an unconditional source
Lemma D.12 / main-text Lemma 4.2 or regret endpoint.

## Appendix Lemma D.11: nonnegative-gap half set

Appendix Lemma D.11 applies a Markov-style counting argument to a finite set
whose elements exceed twice their average.  BanditRLlib promotes exactly the
nonnegative stochastic-loss-gap domain used by that argument: the elements are
loss gaps from a minimum-mean arm and are therefore nonnegative.  The
unrestricted real-valued formulation is not promoted; a signed regression
canary guards the premise boundary without claiming a source correction.

`StochasticGapHalfSet.lean` compiles that source-faithful domain core in six
named declarations.  It proves that at most half of a finite nonnegative gap
family lies strictly above twice its average, including the empty and
zero-average cases, then derives the stochastic-loss-gap specialization from
optimal-arm minimality.  This closes the deterministic counting fact only; it
does not prove Lemma D.13, select the source subset used there, or establish a
regret theorem.

## Algorithm 5 line-10 eliminated-arm initialization

Physical PDF page 22 initializes each arm selected by line 7 before EAP is
called.  `EliminatedArmInitialization.lean` records the exact source values

```text
p_i^1 = 1/(2K) + n_i(S)/(2T)
Delta-tilde_i = 8 width_i(S)
N_i^1 = 1280/(p_i^1 * Delta-tilde_i^2),
```

along with the elimination round, frozen processed order and empirical mean,
zero error count, phase index one, empty phase samples, and empty confidence
sets.  Its pointwise bank update changes only the current line-7 elimination
set, preserves every surviving arm, and retains the invariant that active arms
are uninitialized.  The source probability is positive for any inhabited arm
type; the surrogate gap and first phase target are strictly positive under the
explicit nontrivial-horizon condition `1 < T`.  This condition matters because
Lean's real division is total and the literal `T = 1` formula can have zero
width and denominator.

The 31-declaration module and a concrete two-arm canary compile.  The target
`N_i^1` remains real-valued exactly as printed; rounding belongs to the later
EAP procedure.  The module does not execute EAP, maintain phase/confidence
sets, run BSC, select an action, construct a random trajectory, or prove D.4 or
either regret endpoint.

## Elimination and one-round action law

`DelayedSAPOEliminationSnapshot` is the exact data read by Algorithm 5 line 7,
not a representation of the full algorithm.  Its eliminated and remaining
sets use the source's strict test
`ucbStar < empiricalMean i - 9 * empiricalWidth i`.  The compiled
`optimal_mem_remainingActive_of_certificate` theorem formalizes the
deterministic implication in source Lemma D.9: the empirical-confidence and
`muStar <= ucbStar` projections of the stochastic good event keep the optimal
arm active.  This supplies the nonempty-active premise used by line 15, but it
does not by itself prove the probability of the source good event or full
Lemma D.9.  `DelayedSAPOSourceConfidenceSnapshot` now makes the next bridge
explicit: its Definition-D.1 elimination projection derives
`muStar <= ucbStar` from both source upper-confidence surfaces, constructs the
certificate, and carries any supplied complement-good-event bound to an
optimal-arm-elimination bound.  `DelayedSAPOGoodEventFailureFamily` now
formalizes the source-exact Corollary-D.8 composition: the D.2--D.4 component
bounds contribute `2/T` each and D.5--D.7 contribute `1/T` each, for exactly
`9/T`.  This replaces an earlier local `1/T^2` encoding of D.2--D.4 that did
not match the frozen source.  An explicit full-event projection carries that
budget through the compiled D.9 consumer.  The full event, the six D.2--D.7
component probability proofs, the projection, and recursive persistence remain
open.

`DelayedSAPOAllocation` retains EAP's still-open nonnegativity and mass
hypotheses as explicit fields.  Under them, the existing finite-action law
constructs a genuine one-round probability measure.  A causal allocation rule
can therefore return a probability measure using only `ActionTimeView`, and
observation-equivalent hidden worlds yield the same measure.  Coordinate
measurability, a Markov kernel over generated histories, action sampling, and
the recursive delayed trajectory remain open.

## Lemma D.10 to Lemma D.12 audit window

Physical PDF pp. 26--27 use Lemma D.10 to prove the main-text Lemma 4.2
ordering `Delta_i2 <= 20 * Delta_i1` when arm `i1` is eliminated before arm
`i2`. The displayed D.12 proof needs exactly four edges: the D.10 upper gap
bound at `i2`'s elimination, monotonic transport of `i2`'s width back to
`i1`'s elimination round, D.10's factor-ten width comparison there, and the
D.10 lower surrogate-gap bound for `i1`.

The source's empirical width is inverse-square-root in the pull count. Under
the printed prefix condition `n <= |S-tilde_i|`, the displayed D.10 line
`width_i(S_:n) <= width_i(S-tilde_i)` points opposite to the canonical
antitone count direction. Algorithm 5 also assigns `S-tilde_i = S` only after
the current line-7 elimination test, while the proof says the arm was not
eliminated on the states of `S`. This may be repairable by a different
endpoint convention or a one-update comparison, but neither repair is stated
in the frozen camera-ready. Lean work therefore records the direction
diagnostic and a conditional factor-20 consumer, not an unconditional port of
Lemma D.10/D.12.

A second compiled route stays at one elimination snapshot and thus avoids the
disputed temporal transport.  Its ordered processed-source ledger records the
chosen arm, source-time line-15 allocation, active set, and previous recursive
empirical UCB.  For arms active throughout the prefix, equal allocation and the
exact D.1 count clauses derive
`n_j(S) >= n_i(S) / 4 - 6 * log T`.  Splitting at `192 * log T` produces the
large-count factor-three width comparison and the unconditional same-prefix
factor-ten comparison; the source recursive minimum produces the current-UCB
edge.  The resulting factor-20 theorem therefore no longer assumes a branch or
pair-width premise.  It still consumes a
  `DelayedSAPOProcessedPrefixCountCertificate`.  A deterministic processed
  trace summary now constructs that certificate: its ordered ledger stores
  distinct source indices (without assuming chronological source order),
  carries each exact `s + d_s < t` availability witness, reads the chosen action
  and line-15 allocation at that source index, and keeps the intra-round active
  set separate from the antitone source-round active trace and records their
  containment as an explicit summary invariant.  It defines the
  current width and recursive empirical UCB from the projected summary.  The
  remaining certificate input is the pair of displayed D.4 count inequalities.
  The compiled ordered no-switch step now constructs one such summary from an
  explicit structural round state and preserves its active-set invariant.  It
  does not generate the numerical BSC/EAP fields or the random round state.
  The compiled ordered no-switch trace now derives the later-arm-remains
  premise across exact processing and exhausted-round advances, and then calls
  the same D.4-conditional factor-20 consumer.  Constructing the numerical
  fields on a measurable randomized Algorithm-5 trajectory, proving the
  inequalities' simultaneous `2/T` probability, and closing an unconditional
  source elimination theorem and the terminal regret chains remain open.
  This is a compiled deterministic adapter and conditional same-snapshot repair
  route, not an actual recursive-state producer, source repair, or source
  theorem.

## Hidden regularity and boundary

The accounting, processing, allocation, and elimination implications are
deterministic.  The action-law layer introduces a finite probability measure
only after explicit line-15 simplex premises; it does not introduce a loss law,
history measure, filtration, generated algorithm, horizon theorem, or regret
conclusion.  Subsequent leaves must
separately encode the source's oblivious delays, unknown-at-action-time
information constraint, stochastic iid loss regime, adversarial loss regime,
same-algorithm identity, external `ALG` contract, and expected fixed-arm
regret.

The action-time `outstandingCount` is not identified with the paper's
`sigma(t)` by notation.  The compiled bridge represents paper source round
`s + 1` by zero-based carrier `s` and proves
`t < (s + 1) + delay (s + 1)` equivalent to
`not (s + oneBasedDelayShift delay s < t)`.  This closes the deterministic
indexing obligation while leaving all algorithmic and probabilistic claims
open.

The source-audit inventory contains 197 named declarations: 89
implementation-facing, 19 diagnostic/conditional/repair, 16 processed-prefix,
9 processed-trace-summary, 15 ordered one-step transition, and 12 trace-ordering
declarations, plus six for the nonnegative-domain D.11 core and 31 for line-10
initialization.  The count records the audited Lean slice; it is not a coverage
percentage and does not promote a paper endpoint.
