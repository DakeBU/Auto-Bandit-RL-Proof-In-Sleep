# Conversion window: prospective SGB phase-transition follow-on

Task: `PAPER-AUDIT-NEURIPS-2025-SGB-PHASE-TRANSITION-PROSPECTIVE`

Status: `target-frozen; Corollary 1 compiled; Theorem 2 blocked after compiled nth-pull, latent-product/readout, and deterministic-starvation milestones`

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
trajectory, expose an unconditional latent per-arm reward stream with its
finite product law, prove that every finite nth pull reads the corresponding
latent coordinate, and separately identify the coupling's visible trajectory
law with the native fixed-IID SGB trajectory.  Existing one-step conditional
laws are not by themselves an independence or trajectory-uniqueness theorem.

The chronological half of that bridge compiles.  `twoArmNthOptimalPullTime` uses a
zero-based pull index and returns `WithTop Nat`; `top` is the explicit case in
which the requested pull never occurs.  At a finite time `t`, the compiled
specification proves exactly `pullIndex` prior optimal pulls, action `t = 0`,
and `pullIndex + 1` inclusive pulls.  The stopped reward and post-pull success
probability are measurable and equal the same chronological coordinate.  No
finite product law, IID claim, or future-cylinder probability follows from
this deterministic/stopping-time layer.  A separate compiled latent-reward
layer proves the finite product law for fixed-arm stream coordinates, lifts it
through the coupling's stream marginal, and identifies every finite nth-pull
reward with coordinate `(pullIndex, 0)` almost surely.  It does not prove that
the coupling's trajectory marginal is the native fixed-IID trajectory, and it
does not make totalized or occurrence-conditioned stopped rewards IID.

The phase event then combines an unlucky initial block, a ballot-constrained
recovery block, and a deterministic softmax recurrence that drives the next
optimal-arm sampling probability below `1/(2*T)`.  Only after the finite
probability lower bound compiles may it feed the frozen tilde-Omega endpoint.

The compiled fixed-cutoff milestone defines measurable trigger and starvation
events, proves the exact `Delta * (T - n)` pathwise charge, and specializes
`charge * P(starvation) <= expected sampled regret` to the generated fixed-IID
trajectory measure.  It does not identify the cutoff with the random nth-pull
time and does not prove the source conditional probability lower bound
`P(no return | trigger) >= 1/2`.  Those are producer obligations, not premises
that may be assumed by the terminal.

## Round-15 retrieval packet: latent rewards and native trajectory law

- Card ids: `PPR-BAUDRY-JOHNSON-VARY-PIKEBURKE-REBESCHINI-2025-SGB`,
  `SCN-STOCHASTIC-FINITE`, `MLIB-PROBABILITY-INDEPENDENCE`,
  `MLIB-PROBABILITY-KERNEL`, `MLIB-PROBABILITY-POSTERIOR`, and
  `MLIB-MEASURE-INTEGRAL`.
- Search terms: `selected reward IID`, `arm stream trajectory`,
  `future cylinder`, `condDistrib`, `latentArmStreamTrajectory`, and
  `nthOptimalPull`.
- Local APIs: `UCB.iIndepFun_armStreamMeasure_coordinate`,
  `UCB.armStreamMeasure_map_coord`,
  `Thompson.identDistrib_fst_latentArmStreamTrajectoryMeasure`,
  `Thompson.latentArmStreamTrajectoryReward_eq_rewardFromArmStream_ae`,
  `twoArmNthOptimalPullTime_spec`, and
  `RewardKernel.rewardTrace_map_eq_trajMeasure_of_condDistrib`.
- Source reading: Appendix C, physical pp. 31--32, defines the arm-1 rewards
  in pull order, evaluates the phase-0 and phase-1 blocks as independent
  reward blocks, and only afterwards combines them with the deterministic
  implication into the low-probability trigger.  The source does not state a
  stopped-value product-law lemma or justify totalization when a requested
  pull is absent.
- Safe intermediate route: prove the finite product law for the first `m`
  coordinates of one latent arm stream; lift it through the exact stream
  marginal of the latent trajectory coupling; and prove that every finite
  nth optimal-arm pull reads coordinate `(pullIndex, 0)` almost surely.
- Expected bridge: prove that the trajectory marginal of the stationary
  latent-stream coupling equals the native fixed-IID canonical trajectory,
  preferably through finite prefix/next-pair factorization followed by
  Ionescu--Tulcea uniqueness.  This bridge is project-local and is not supplied
  by the existing deterministic-UCB arm-stream conditional-law theorem.
- Hidden contracts: the action at a round is selected before that round's
  reward, `WithTop.top` remains explicit, conditional-kernel equalities are
  only almost everywhere under their conditioning law, and occurrence of
  `m` pulls may depend on earlier rewards.  Consequently, neither totalized
  stopped rewards nor rewards conditioned on all `m` pulls occurring may be
  declared IID without an additional theorem.
- Status before the round-15 proof attempt: `project-local`; latent finite
  product and finite-pull readout are candidate compiled leaves, while the
  native trajectory-marginal adapter remains the target-faithful blocker.

## Pivot rules

- Do not replace the nth-pull law with an IID premise on the selected reward
  sequence.
- Do not replace actual sampled regret with a probability-schedule proxy.
- If the asymptotic notation becomes a blocker, retain the exact finite
  Appendix-C lower bound and leave the terminal status partial.
- A compiled Corollary 1, nth-pull bridge, or deterministic starvation
  consumer does not change Theorem 2 from `partial` to `compiled`.
