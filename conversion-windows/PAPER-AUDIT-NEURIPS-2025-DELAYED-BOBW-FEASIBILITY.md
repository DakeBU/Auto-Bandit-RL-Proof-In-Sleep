# Conversion window: NeurIPS 2025 delayed-feedback BoBW feasibility

Task: `PAPER-AUDIT-NEURIPS-2025-DELAYED-BOBW-FEASIBILITY`

Status: `source-frozen; deterministic availability, action-time count,
one-based/end-of-round sigma bridge, generic shared-identity interface, causal
action-time view, set-level new-arrival processing, line-7/8 optimal-arm
survival, line-15 allocation, and a causal one-round action measure compiled;
full Delayed SAPO state, measurable generated trajectory, and paper endpoints
planned`

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
formalizes the Corollary-D.8 composition: the three `1/T^2` and three `1/T`
component bounds imply the source's loose `9/T` failure budget, and an
explicit full-event projection carries that budget through the compiled D.9
consumer.  The full event, the six D.2--D.7 component probability proofs, the
projection, and recursive persistence remain open.

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
