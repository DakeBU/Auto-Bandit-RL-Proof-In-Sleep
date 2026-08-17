# Conversion window: NeurIPS 2025 delayed-feedback BoBW feasibility

Task: `PAPER-AUDIT-NEURIPS-2025-DELAYED-BOBW-FEASIBILITY`

Status: `source-frozen; deterministic availability, action-time count,
one-based/end-of-round sigma bridge, generic shared-identity interface, causal
action-time view, and set-level new-arrival processing compiled; Delayed SAPO
active-arm allocation compiled; Delayed SAPO state and paper endpoints planned`

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

## Hidden regularity and boundary

The compiled leaves are deterministic and need only natural-valued delays and a
finite prefix.  It introduces no loss law, probability measure, filtration,
algorithm, horizon theorem, or regret conclusion.  Subsequent leaves must
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
