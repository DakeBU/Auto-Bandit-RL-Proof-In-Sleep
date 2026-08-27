# Conversion window: prospective SGB phase-transition follow-on

Task: `PAPER-AUDIT-NEURIPS-2025-SGB-PHASE-TRANSITION-PROSPECTIVE`

Status: `target-frozen; Corollary 1 compiled; Theorem 2 blocked after a compiled deterministic starvation consumer`

## Source-to-Lean fence

- Source arm `1` is Lean arm `0`; source arm `2` is Lean arm `1`.
- Source horizon `T` contains actions `1, ..., T`.  Existing Lean
  `tailHorizon` uses `T = tailHorizon + 1`.
- `twoArmTrajectoryMeasure`, `twoArmFixedIIDEnvironment`, and
  `twoArmSampledPseudoRegret` remain the generated-process authority.
- Theorem 2 is frozen only for `K = 2`; its threshold is
  `(1/2) * log ((1 + Delta) / (1 - Delta))`.
- Corollary 1 uses a separate fixed learning rate for each horizon,
  `sqrt(log T / T)`.  It is not the source's later time-varying policy.

## Corollary-1 branch conversion

When `2 * eta * sourceC eta <= Delta`, positivity gives
`eta * sourceC eta < Delta`; the compiled Theorem-1 endpoint applies.  The
same inequality yields

```text
Delta / (2 * eta * (Delta - eta * sourceC eta)) <= 1 / eta.
```

On the complementary branch, each sampled round costs either `0` or `Delta`,
so the exact finite regret is at most `Delta * T`.  The final square-root rate
must be derived from these branches; it may not be inserted as an assumption.

## Theorem-2 process conversion

Appendix C reindexes the process by the number of pulls of the optimal arm.
The Lean bridge must therefore define the nth-pull time on the chronological
trajectory and prove that rewards extracted at those times have the required
finite product law under adaptive action selection.  Existing one-step
conditional laws are not by themselves an independence theorem.

The phase event then combines an unlucky initial block, a ballot-constrained
recovery block, and a deterministic softmax recurrence that drives the next
optimal-arm sampling probability below `1/(2*T)`.  Only after the finite
probability lower bound compiles may it feed the frozen tilde-Omega endpoint.

The current fixed-cutoff milestone defines measurable trigger and starvation
events, proves the exact `Delta * (T - n)` pathwise charge, and specializes
`charge * P(starvation) <= expected sampled regret` to the generated fixed-IID
trajectory measure.  It does not identify the cutoff with the random nth-pull
time and does not prove the source conditional probability lower bound
`P(no return | trigger) >= 1/2`.  Those are producer obligations, not premises
that may be assumed by the terminal.

## Pivot rules

- Do not replace the nth-pull law with an IID premise on the selected reward
  sequence.
- Do not replace actual sampled regret with a probability-schedule proxy.
- If the asymptotic notation becomes a blocker, retain the exact finite
  Appendix-C lower bound and leave the terminal status partial.
- A compiled Corollary 1 does not change Theorem 2 from `not_started` or
  `partial` to `compiled`.
