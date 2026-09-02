# Conversion window: prospective SGB phase-transition follow-on

Task: `PAPER-AUDIT-NEURIPS-2025-SGB-PHASE-TRANSITION-PROSPECTIVE`

Status: `target-frozen; Corollary 1 compiled; Theorem 2 blocked after compiled nth-pull, latent-product/readout, deferred-decisions finite-prefix factorization, action/readout interface, count-capped branch locality, one-step selected-reward freshness, native-prefix identification, full native visible-law equality, missing-pull-aware selected-block transport, exact phase-event transport, and deterministic missing-pull expected-regret consumption`

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

## Round-16 retrieval packet: deferred-decisions prefix factorization

- Reused cards: `MLIB-PROBABILITY-KERNEL`,
  `MLIB-PROBABILITY-INDEPENDENCE`, `MLIB-MEASURE-INTEGRAL`,
  `PPR-BAUDRY-JOHNSON-VARY-PIKEBURKE-REBESCHINI-2025-SGB`, and
  `SCN-STOCHASTIC-FINITE`.
- Reused local APIs: `Measure.infinitePi_map_restrict`,
  `KernelTrajectoryPrefix.trajMeasure_map_frestrictLe_congr`,
  `Thompson.canonicalMeasurableEnvironmentTrajectoryKernel_apply_eq_canonical`,
  `Thompson.map_compProd_comap_history`, and the latent next-unused-coordinate
  environment.
- Compiled route: restrict the latent arm stream through the inclusive endpoint
  `n`; prove that two streams agreeing on this finite box induce the same
  visible trajectory-prefix law; package the dependence as a Markov kernel on
  the finite box; and push the joint latent measure forward to obtain the exact
  stream-box/visible-prefix mixture.
- Hidden contracts: `Finset.Iic n` is inclusive; action randomization remains
  inside the canonical trajectory kernel; the finite box contains unused as
  well as consumed coordinates; and a finite mixture representation alone does
  not prove that the next unused selected coordinate is conditionally fresh.
- Remaining native route: prove a branchwise prefix-plus-next-pair factorization
  by removing coordinate `(realHistoryPullCount n history arm, arm)`, then use
  conditional-law and trajectory-uniqueness APIs to identify the visible latent
  law with the native fixed-IID law.
- Nonclaims: no visible-marginal/native-prefix identification or full native
  visible law, no stopped-reward IID theorem, no future-cylinder/no-return producer, and no
  Theorem-2 terminal follows from this packet.

## Round-17 retrieval packet: action/readout split and branch-locality scaffold

This records the historical Round-17 boundary; its locality obligation is
discharged by the Round-18 packet below.

- Reused APIs: `trajectoryMixture_map_history_action_eq_compProd`,
  `indepFun_armStreamMeasure_coordinate_without`, finite/sub-Markov
  semidirect-product factorization, coordinate removal/insertion, and
  `ETC.realHistoryPullCount_finitePairHistoryOfTrace`.
- Compiled action half: the latent mixture maps `(visible prefix, next action)`
  to the visible-prefix marginal followed by `algorithm.policy n`.
- Compiled pathwise support: the actual successor reward equals the latent
  coordinate selected by the visible history and sampled action almost surely.
  This is support, not a conditional freshness or IID theorem.
- Compiled consumer/scaffold at this round: a branch kernel, finite/sub-Markov product
  consumer, count-cap set, its measurability, and the exact pull-count extension
  recurrence.  `LatentArmStreamVisiblePrefixNextActionBranchLocality` is an
  explicit proposition required by the consumer; Round 17 did not yet prove it.
- Round-17 open producer: prove equality of fixed-stream visible-prefix laws after
  restriction to the count cap under equality of all coordinates except the
  target.  Then restrict to the exact count/action branch, obtain freshness,
  identify the native prefix, and apply trajectory uniqueness.
- Off-by-one boundary: an inclusive history through `n` can contain `n + 1`
  pulls of one arm.  The prefix/action law does not consume the selected next
  coordinate, whereas the next reward does; a finite `Iic n` stream box alone
  cannot establish freshness.

## Round-18 retrieval packet: count-capped branch-locality producer

This records the historical Round-18 boundary; its branch-aggregation
obligation is discharged by the Round-19 packet below.

- Reused and extended APIs:
  `Measure.compProd_restrict_eq_of_base_restrict_eq_of_fiber_restrict_eq`,
  `Measure.map_compProd_restrict_eq_of_base_restrict_eq_of_fiber_restrict_eq`,
  trajectory prefix/next-pair recurrence, the exact
  pull-count extension identity, coordinate removal/insertion, and the existing
  finite/sub-Markov branch-product consumer.
- New reusable bridge: two generic declarations show that a semidirect-product
  law restricted to a measurable safe set is determined by the restricted base
  law and the corresponding restricted fibers, and that a measurable successor
  map preserves this equality.
- Compiled base/successor route: time-zero count-cap locality, the successor-cap
  decomposition into strict-count and equal-count/avoid-arm rectangles,
  restricted step-kernel equality, and induction over every finite prefix.
- Compiled producer: `latentArmStreamVisiblePrefixNextActionBranchLocality`
  discharges the uppercase locality contract, and
  `latentArmStreamVisiblePrefixNextAction_coordinate_branch_eq_prod` derives
  the exact branchwise selected-coordinate product law without a locality
  premise.
- Round-18 remaining producer: aggregate the coordinate branches and the a.e.
  reward readout into a selected-reward freshness law, identify the resulting
  visible marginal with the native fixed-IID prefix, and extend it to the native
  trajectory law.  Branchwise product equality alone is not selected-reward
  IID and does not close the stopped-prefix future/no-return route.
- Inventory effect: 28 new indexed declarations (two generic measure bridges
  plus 26 route-specific leaves) raise the SGB audit slice from 316 to 344.

## Round-19 retrieval packet: selected-reward branch aggregation

- Reused source and scenario cards:
  `PPR-BAUDRY-JOHNSON-VARY-PIKEBURKE-REBESCHINI-2025-SGB` and
  `SCN-STOCHASTIC-FINITE`; reused Mathlib cards:
  `MLIB-PROBABILITY-KERNEL`, `MLIB-PROBABILITY-INDEPENDENCE`, and
  `MLIB-MEASURE-INTEGRAL`.
- Search terms: `selected reward conditional law`, `condDistrib compProd`,
  `measure sum restrict branch`, `map restrict`, `branch partition`, and
  `selected coordinate measurable`.
- Reused local APIs:
  `latentArmStreamVisiblePrefixNextAction_coordinate_branch_eq_prod`,
  `latentArmStreamVisibleNextReward_eq_selectedCoordinate_ae`,
  `UCB.measure_eq_sum_restrict_armStreamHistoryActionCoordinateBranch`,
  `Measure.compProd_restrict_prod`, `Measure.restrict_map`,
  `Measure.map_sum`, `Measure.compProd_sum_left`,
  `Measure.compProd_sum_right`, `Measure.compProd_congr`,
  `Measure.compProd_const`, `Measure.compProd_map`, and
  `condDistrib_ae_eq_iff_measure_eq_compProd`.
- Compiled route: prove measurable dynamic coordinate evaluation; on each
  `(pull count, arm)` branch replace the dynamic coordinate by the fixed one;
  sum the countable branch partition on both sides; transport the resulting
  joint law through the latent trajectory coupling; and replace the selected
  latent coordinate by the actual next reward almost everywhere.
- Compiled endpoints:
  `latentArmStreamVisibleNextReward_joint_eq_compProd`,
  `latentArmStreamVisibleNextReward_condDistrib_ae_eq_nu`, and their
  visible-trajectory-marginal forms, ending at
  `latentArmStreamVisibleTrajectoryMeasure_nextReward_condDistrib_ae_eq_nu`.
- Hidden contracts: the condition contains the visible prefix through `n`
  and the selected action at `n + 1`; the right kernel is
  `nu.comap Prod.snd`, so it depends on the selected arm; the branch index is
  the countable type `Nat × Fin K`; branch kernels remain finite/sub-Markov;
  and the a.e. readout is transported only under the exact coupling measure.
- Nonclaims: this deterministic-time one-step conditional law is not a
  selected-reward IID law, an nth-pull stopping-time IID law, a native
  fixed-IID trajectory equality, a future/no-return theorem, or Theorem 2.
- Inventory effect: eight new declarations raise the SGB audit slice from 344
  to 352.  The next exact producer is visible-marginal/native-prefix
  identification, followed by trajectory uniqueness and selected-block
  transport.

## Round-21 retrieval packet: finite-prefix uniqueness to full native law

- Source and scenario cards:
  `PPR-BAUDRY-JOHNSON-VARY-PIKEBURKE-REBESCHINI-2025-SGB` and
  `SCN-STOCHASTIC-FINITE`; Mathlib route:
  `MLIB-PROBABILITY-KERNEL` together with
  `Mathlib.Probability.Process.FiniteDimensionalLaws`.
- Search terms tried: `frestrictLe`, `trajectory uniqueness`, `Ionescu`,
  `IsProjectiveLimit.unique`, and `map_frestrictLe`.
- Reused compiled local declaration:
  `latentArmStreamVisibleTrajectoryMeasure_map_frestrictLe_eq_native`.
  Reused proof pattern:
  `RewardKernel.rewardTrace_map_eq_trajMeasure_of_condDistrib`.
- Intended project-local bridge: use the native law's arbitrary finite
  restrictions as one projective family; derive every arbitrary finite
  restriction of the visible latent marginal from the compiled `Iic n`
  prefix equality by selecting coordinates inside `Iic (I.sup id)`; then use
  `MeasureTheory.IsProjectiveLimit.unique` to identify the two complete
  probability measures.
- Hidden regularity contracts: both complete laws are probability measures;
  every coordinate restriction and finite-coordinate selector is measurable;
  the target is equality of the two complete visible trajectory measures,
  not selected/stopped reward IID or any random-time future law.
- Compiled outcome: `latentArmStreamVisibleTrajectoryMeasure_eq_native`
  derives equality of the complete visible/native trajectory measures from
  the previously compiled `Iic n` prefix identities.  Its canary reports only
  the baseline axioms `propext`, `Classical.choice`, and `Quot.sound`.
- Status after the focused gate: `compiled project-local`.  No new Mathlib
  lemma, source assumption, selected-IID premise, random-time future law, or
  theorem-endpoint promotion was introduced.

## Round-23 retrieval packet: missing-pull-aware selected-block transport

- Reused compiled endpoints:
  `twoArmNthOptimalPullReward_eq_latentCoordinate_ae`,
  `twoArmFixedIIDLatentTrajectoryMeasure_map_optimalPrefix_eq_pi`, and
  `latentArmStreamVisibleTrajectoryMeasure_eq_native`.
- Compiled observable: `twoArmOptimalPullTimeRewardBlock m` records, for every
  `i : Fin m`, both the `WithTop Nat` time of the `i`th optimal-arm pull and
  the stopped reward readout.
- Compiled comparison law: `twoArmLatentMaskedOptimalPullBlock m` replaces the
  reward by latent arm-`0` coordinate `i` only when the pull time is finite; at
  `top` it retains the stopped-value fallback.  The source and native generated
  block laws equal the pushforward of this masked coupling.
- Endpoint:
  `twoArmFixedIIDTrajectoryMeasure_map_optimalPullTimeRewardBlock_eq_latentMasked`.
  Its statement fence preserves the probability-law and finite-block
  assumptions, and its canary reports only the baseline axioms `propext`,
  `Classical.choice`, and `Quot.sound`.
- Boundary: the separately compiled unmasked latent prefix has a product law,
  but this masked selected block is not claimed product-distributed or IID.
  The next producer must formulate the exact Appendix-C phase event together
  with the all-pulls-present occurrence boundary; it may not condition away
  dependence created by adaptive selection.

## Round-24 retrieval packet: exact phase event and occurrence boundary

- Source window: Appendix C, physical PDF pp. 31--34.  `S0` is the first
  `n0` optimal-arm rewards all equal to `-1`; `S1` contains only `{-1,1}`
  rewards, has the source-selected exact terminal sum, and keeps the number of
  `+1` rewards no larger than the number of `-1` rewards at every recovery
  prefix, equivalently every recovery prefix sum is nonpositive.
- Fourteen new public declarations extend the selected-block module from eight
  to 22 declarations.  They define the recovery prefix sum, the exact finite
  reward event, the all-pulls-present event, observed/generated events, and a
  latent event that is explicitly the intersection of the pure latent reward
  pattern with adaptive occurrence.
- Compiled terminal:
  `twoArmFixedIIDTrajectoryMeasure_appendixCGeneratedPhaseEvent_eq_latent`.
  It transports event probability through the Round-23 masked block law.
- Statement fence:
  `runs/statement-fences/SGB-T2-PHASE-EVENT-TRANSPORT.json`, hash
  `abcb66250f7cac25a5ab0506fc6101e2be986637e102f5ca072f7e89394ff67d`.
- Boundary: the theorem does not discard the occurrence intersection and hence
  does not derive a product law, occurrence-conditioned IID, a phase
  probability lower bound, future/no-return, ballot/asymptotic assembly, or
  Theorem 2.  The next exact producer is a missing-pull/all-present dichotomy
  that lets the pure latent phase probability feed either an already-starved
  path or the transported observed phase.

## Round-25 retrieval packet: missing-pull/all-present probability split

- Active leaf: `SGB-T2-PHASE-DICHOTOMY`; status `in progress` until the focused
  module, typed canary, statement fence, and repository gates all pass.
- Source window: Appendix C, physical PDF pp. 31--34.  The finite latent
  `S0/S1` reward pattern is evaluated under the unconditional arm-0 product
  law.  Adaptive occurrence is then split explicitly: either all requested
  optimal-arm pulls occur and the observed phase is available, or at least one
  requested pull is absent.  This split is prior to, and does not prove, the
  stopped-prefix future/no-return or ballot lower bounds.
- Random object: the first `n0+n1` coordinates of the latent arm-0 reward
  stream under `twoArmFixedIIDLatentTrajectoryMeasure armLaw hprob eta`.
- Exact event: `twoArmAppendixCRewardPhaseEvent n0 n1 phaseOneTotal`; its pure
  latent preimage is partitioned by the measurable occurrence event
  `(twoArmLatentMaskedOptimalPullBlock (n0+n1)) ⁻¹'
  twoArmAppendixCAllPullsPresent (n0+n1)` and its complement.
- Local APIs: `twoArmFixedIIDLatentTrajectoryMeasure_map_optimalPrefix_eq_pi`,
  `twoArmAppendixCLatentPhaseEvent`,
  `twoArmFixedIIDTrajectoryMeasure_appendixCGeneratedPhaseEvent_eq_latent`,
  `Measure.map_apply`, `measure_union`, and `Set.disjoint_left`.
- Intended proof route: define measurable pure-latent and missing-pull phase
  events; prove the missing event is exactly the pure reward pattern together
  with an existential `WithTop.top` pull time; prove the pure event is the
  disjoint union of the existing all-present latent phase and the missing
  branch; transfer the pure-event probability through the compiled finite
  product law; finally substitute the compiled generated-event transport.
- Classification: project-local event interface.  No new Mathlib candidate or
  concentration theorem is introduced; the product-law leaf and finite
  measure-union theorem already compile locally.
- Hidden contracts: all events remain measurable; the split is unconditional;
  the missing branch is not yet identified with the source fixed-cutoff trigger
  event; the all-present branch is not occurrence-conditioned IID; no positive
  lower bound, future/no-return law, ballot result, asymptotic assembly, or
  Theorem 2 follows from this leaf alone.

## Round-26 conversion window: missing pull to terminal count

- Frozen statement: if `twoArmNthOptimalPullTime i sample = WithTop.top`, then
  `twoArmOptimalPullCount horizon sample < i + 1` at every finite `horizon`.
  For `i : Fin m`, the result strengthens to count `< m`; membership in the
  Appendix-C missing-pull latent event therefore maps into the measurable
  below-`m` terminal-count event.
- Source semantics retained: `WithTop.top` remains the explicit no-occurrence
  value; the conclusion is uniform over finite horizons and does not replace a
  missing pull with a default reward or finite stopping time.
- Local route: `pullCount_succ_le_succ` plus
  `twoArmNthOptimalPullTime_eq_top_iff` gives the pathwise count inequality;
  exact terminal-count fibers form a finite `Fin m` union and reuse the
  compiled exact sampled-pseudo-regret identity.
- Boundary: this window does not supply the source trigger inequality, a
  stopped-prefix future/no-return law, occurrence-conditioned IID, a lower
  bound on either branch probability, a ballot estimate, asymptotic assembly,
  or Theorem 2.

## Round-33 conversion window: latent missing mass to expected regret

- Frozen statement: for nonnegative `Delta`, latent missing-pull phase mass is
  transported through the exact visible `Unit`-trajectory marginal and charged
  only by `Delta * (horizon - (n0+n1))` in the generated expected sampled
  pseudo-regret.
- Source semantics retained: the left side uses the actual latent missing
  branch from the compiled dichotomy; the right side uses
  `twoArmTrajectoryMeasure` and `twoArmSampledPseudoRegret`.  No surrogate
  action schedule or occurrence-conditioned reward law is introduced.
- Local route: the latent visible marginal and source `Prod.snd` marginal are
  both the compiled native stationary trajectory law; the missing event is a
  subset of the generated below-count event; an indicator integral consumes
  its uniform finite-horizon charge.
- Boundary: the theorem transports and consumes whatever missing probability
  already exists.  It does not prove that probability positive, derive the
  generated all-present phase's source trigger inequality, construct a stopped
  future/no-return law, prove selected IID, establish a ballot lower bound, or
  assemble Theorem 2.
- Next window: `SGB-T2-APPENDIX-C-PHASE-TRIGGER`, restricted to the
  deterministic recurrence implication from the generated all-present
  `S0/S1` phase to the source `1/(2*T)` next-action threshold.

## Pivot rules

- Do not replace the nth-pull law with an IID premise on the selected reward
  sequence.
- Do not replace actual sampled regret with a probability-schedule proxy.
- If the asymptotic notation becomes a blocker, retain the exact finite
  Appendix-C lower bound and leave the terminal status partial.
- Compiled Corollary 1, nth-pull, latent-product/readout, finite-prefix
  factorization, action/readout interface, count-cap branch-locality producer,
  unconditional branch-product law, one-step selected-reward freshness,
  native-prefix identification, full native visible-law equality,
  missing-pull-aware selected-block transport, exact phase-event transport, and
  deterministic missing-pull expected-regret consumers do not compile the
  frozen Theorem 2 terminal; that terminal remains `blocked`.
