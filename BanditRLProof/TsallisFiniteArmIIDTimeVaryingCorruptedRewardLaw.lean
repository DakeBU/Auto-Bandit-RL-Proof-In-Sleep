import BanditRLProof.TsallisScheduledIIDTimeVaryingMeanGap

/-!
# Time-varying corrupted finite-arm IID reward laws

The base reward vector is fresh IID at every round.  Before play begins, a
deterministic arm-dependent reward shift is fixed for every round; shifted
rewards are clipped back to `[0,1]`.  Such a schedule is predictable and
oblivious.  It need not be stationary, but it does not depend on the realized
history.
-/

namespace BanditRLProof
namespace Tsallis

open MeasureTheory ProbabilityTheory

/-- Reward after a deterministic time-indexed arm shift and clipping. -/
noncomputable def finiteArmIIDTimeVaryingCorruptedReward {K : Nat}
    (rewardShift : Nat -> Fin K -> Real) (t : Nat)
    (state : Fin K -> Rat) (arm : Fin K) : Real :=
  finiteArmIIDStationaryCorruptedReward (rewardShift t) state arm

/-- Loss vector induced by the time-indexed clipped reward. -/
noncomputable def finiteArmIIDTimeVaryingCorruptedRewardVectorLoss {K : Nat}
    (rewardShift : Nat -> Fin K -> Real) (t : Nat)
    (state : Fin K -> Rat) (arm : Fin K) : Real :=
  1 - finiteArmIIDTimeVaryingCorruptedReward rewardShift t state arm

theorem measurable_finiteArmIIDTimeVaryingCorruptedRewardVectorLoss
    {K : Nat} (rewardShift : Nat -> Fin K -> Real) (t : Nat) :
    Measurable (fun input : (Fin K -> Rat) × Fin K =>
      finiteArmIIDTimeVaryingCorruptedRewardVectorLoss
        rewardShift t input.1 input.2) := by
  simpa [finiteArmIIDTimeVaryingCorruptedRewardVectorLoss,
    finiteArmIIDTimeVaryingCorruptedReward,
    finiteArmIIDStationaryCorruptedRewardVectorLoss] using
    measurable_finiteArmIIDStationaryCorruptedRewardVectorLoss
      (rewardShift t)

theorem finiteArmIIDTimeVaryingCorruptedRewardVectorLoss_nonneg
    {K : Nat} (rewardShift : Nat -> Fin K -> Real) (t : Nat)
    (state : Fin K -> Rat) (arm : Fin K) :
    0 <= finiteArmIIDTimeVaryingCorruptedRewardVectorLoss
      rewardShift t state arm := by
  simpa [finiteArmIIDTimeVaryingCorruptedRewardVectorLoss,
    finiteArmIIDTimeVaryingCorruptedReward,
    finiteArmIIDStationaryCorruptedRewardVectorLoss] using
    finiteArmIIDStationaryCorruptedRewardVectorLoss_nonneg
      (rewardShift t) state arm

theorem finiteArmIIDTimeVaryingCorruptedRewardVectorLoss_le_one
    {K : Nat} (rewardShift : Nat -> Fin K -> Real) (t : Nat)
    (state : Fin K -> Rat) (arm : Fin K) :
    finiteArmIIDTimeVaryingCorruptedRewardVectorLoss
      rewardShift t state arm <= 1 := by
  simpa [finiteArmIIDTimeVaryingCorruptedRewardVectorLoss,
    finiteArmIIDTimeVaryingCorruptedReward,
    finiteArmIIDStationaryCorruptedRewardVectorLoss] using
    finiteArmIIDStationaryCorruptedRewardVectorLoss_le_one
      (rewardShift t) state arm

/-- The actual mean gap at round `t` differs from the baseline model gap by
at most the two affected arm shifts. -/
theorem abs_iidLossStateTimeVaryingMeanGap_corrupted_sub_modelGap_le
    {K : Nat} (model : FiniteBanditModel K)
    (armLaw : Fin K -> Measure Rat)
    (hprob : ∀ arm, IsProbabilityMeasure (armLaw arm))
    (hbound : ∀ arm, ∀ᵐ reward ∂armLaw arm,
      ((reward : Rat) : Real) ∈ Set.Icc (0 : Real) 1)
    (hmean : ∀ arm,
      integral (armLaw arm) (fun reward : Rat => ((reward : Rat) : Real)) =
        ((model.mean arm : Rat) : Real))
    (rewardShift : Nat -> Fin K -> Real) (t : Nat) (arm : Fin K) :
    |iidLossStateTimeVaryingMeanGap (finiteArmIIDRewardVectorLaw armLaw)
          (finiteArmIIDTimeVaryingCorruptedRewardVectorLoss rewardShift)
          t model.bestArm arm - ((model.gap arm : Rat) : Real)| <=
      |rewardShift t arm| + |rewardShift t model.bestArm| := by
  simpa [iidLossStateTimeVaryingMeanGap,
    iidLossStateMeanGap,
    finiteArmIIDTimeVaryingCorruptedRewardVectorLoss,
    finiteArmIIDTimeVaryingCorruptedReward,
    finiteArmIIDStationaryCorruptedRewardVectorLoss] using
    abs_iidLossStateMeanGap_stationaryCorrupted_sub_modelGap_le
      model armLaw hprob hbound hmean (rewardShift t) arm

/-- Explicit accumulated budget of a time-indexed oblivious reward-shift
schedule through the inclusive horizon. -/
noncomputable def finiteArmIIDTimeVaryingRewardCorruptionBudget {K : Nat}
    (model : FiniteBanditModel K) (horizon : Nat)
    (rewardShift : Nat -> Fin K -> Real) : Real :=
  scheduledTimeVaryingGapDeviationBudget
    (Finset.univ : Finset (Fin K)) model.bestArm horizon
    (fun t arm => |rewardShift t arm| + |rewardShift t model.bestArm|)

theorem finiteArmIIDTimeVaryingRewardCorruptionBudget_eq {K : Nat}
    (model : FiniteBanditModel K) (horizon : Nat)
    (rewardShift : Nat -> Fin K -> Real) :
    finiteArmIIDTimeVaryingRewardCorruptionBudget model horizon rewardShift =
      (Finset.range (horizon + 1)).sum (fun t =>
        ((Finset.univ : Finset (Fin K)).erase model.bestArm).sum
          (fun arm =>
            |rewardShift t arm| + |rewardShift t model.bestArm|)) := by
  rfl

@[simp]
theorem finiteArmIIDTimeVaryingRewardCorruptionBudget_zero {K : Nat}
    (model : FiniteBanditModel K) (horizon : Nat) :
    finiteArmIIDTimeVaryingRewardCorruptionBudget model horizon
      (fun _ _ => 0) = 0 := by
  simp [finiteArmIIDTimeVaryingRewardCorruptionBudget,
    scheduledTimeVaryingGapDeviationBudget]

/-- A constant shift schedule recovers the stationary corruption budget. -/
theorem finiteArmIIDTimeVaryingRewardCorruptionBudget_const_eq_stationary
    {K : Nat} (model : FiniteBanditModel K) (horizon : Nat)
    (rewardShift : Fin K -> Real) :
    finiteArmIIDTimeVaryingRewardCorruptionBudget model horizon
        (fun _ => rewardShift) =
      finiteArmIIDStationaryRewardCorruptionBudget
        model horizon rewardShift := by
  simp [finiteArmIIDTimeVaryingRewardCorruptionBudget,
    scheduledTimeVaryingGapDeviationBudget,
    finiteArmIIDStationaryRewardCorruptionBudget,
    scheduledGapDeviationBudget]

/-- Scheduled half-Tsallis logarithmic regret under an explicit deterministic
time-indexed reward-shift schedule.  The additive allowance is derived from
the schedule and is not a free corruption parameter. -/
theorem integral_sampledScheduledHalfTsallisFiniteArmIIDTimeVaryingCorruptedRewardLawRegret_le_log
    {K : Nat} (model : FiniteBanditModel K)
    (armLaw : Fin K -> Measure Rat)
    (hprob : ∀ arm, IsProbabilityMeasure (armLaw arm))
    (hbound : ∀ arm, ∀ᵐ reward ∂armLaw arm,
      ((reward : Rat) : Real) ∈ Set.Icc (0 : Real) 1)
    (hmean : ∀ arm,
      integral (armLaw arm) (fun reward : Rat => ((reward : Rat) : Real)) =
        ((model.mean arm : Rat) : Real))
    (rewardShift : Nat -> Fin K -> Real)
    (hgapPos : ∀ arm, arm ≠ model.bestArm ->
      0 < ((model.gap arm : Rat) : Real))
    (horizon : Nat) :
    letI : Nonempty (Fin K) := ⟨model.bestArm⟩
    let law := finiteArmIIDRewardVectorLaw armLaw
    let value := finiteArmIIDTimeVaryingCorruptedRewardVectorLoss rewardShift
    let loss := iidTimeVaryingLossStatePredictableLossVector value
      (measurable_finiteArmIIDTimeVaryingCorruptedRewardVectorLoss rewardShift)
      (finiteArmIIDTimeVaryingCorruptedRewardVectorLoss_nonneg rewardShift)
      (finiteArmIIDTimeVaryingCorruptedRewardVectorLoss_le_one rewardShift)
    let selector :=
      canonicalHalfTsallisScheduleGeneratedSelectorMeasurability
        (Finset.univ : Finset (Fin K)) Finset.univ_nonempty
        sampledScheduledHalfTsallisSqrtSchedule loss
    let prior := Measure.infinitePi (fun _ : Nat => law)
    let mu := prior ⊗ₘ sampledScheduledHalfTsallisTrajectoryKernel
      (Finset.univ : Finset (Fin K)) Finset.univ_nonempty
      sampledScheduledHalfTsallisSqrtSchedule
      selector.finiteHistory loss.environment
    integral mu (sampledScheduledHalfTsallisPredictableEnvironmentRegret
        (Finset.univ : Finset (Fin K)) Finset.univ_nonempty
        sampledScheduledHalfTsallisSqrtSchedule loss
        (pointMass model.bestArm) horizon) <=
      (1 + Real.log (((horizon + 1 : Nat) : Real))) *
        (1 + 25 * ((Finset.univ : Finset (Fin K)).erase model.bestArm).sum
          (fun arm => 1 / ((model.gap arm : Rat) : Real))) +
        finiteArmIIDTimeVaryingRewardCorruptionBudget
          model horizon rewardShift := by
  letI : Nonempty (Fin K) := ⟨model.bestArm⟩
  letI (arm : Fin K) : IsProbabilityMeasure (armLaw arm) := hprob arm
  let law := finiteArmIIDRewardVectorLaw armLaw
  letI : IsProbabilityMeasure law := by
    dsimp only [law, finiteArmIIDRewardVectorLaw]
    infer_instance
  let value := finiteArmIIDTimeVaryingCorruptedRewardVectorLoss rewardShift
  let hvalue :=
    measurable_finiteArmIIDTimeVaryingCorruptedRewardVectorLoss rewardShift
  let hvalueNonneg :=
    finiteArmIIDTimeVaryingCorruptedRewardVectorLoss_nonneg rewardShift
  let hvalueLeOne :=
    finiteArmIIDTimeVaryingCorruptedRewardVectorLoss_le_one rewardShift
  let loss := iidTimeVaryingLossStatePredictableLossVector value hvalue
    hvalueNonneg hvalueLeOne
  let arms : Finset (Fin K) := Finset.univ
  let harms : arms.Nonempty := Finset.univ_nonempty
  let eta := sampledScheduledHalfTsallisSqrtSchedule
  let selector := canonicalHalfTsallisScheduleGeneratedSelectorMeasurability
    arms harms eta loss
  let prior := Measure.infinitePi (fun _ : Nat => law)
  let trajectoryKernel := sampledScheduledHalfTsallisTrajectoryKernel
    arms harms eta selector.finiteHistory loss.environment
  let mu := prior ⊗ₘ trajectoryKernel
  let actualGap := fun t arm =>
    iidLossStateTimeVaryingMeanGap law value t model.bestArm arm
  let baseGap := fun arm : Fin K => ((model.gap arm : Rat) : Real)
  let deviation := fun (t : Nat) (arm : Fin K) =>
    |rewardShift t arm| + |rewardShift t model.bestArm|
  have hfactor : HasScheduledIIDPrefixKernelFactorization trajectoryKernel
      horizon := by
    simpa only [trajectoryKernel, selector, eta, loss, value, hvalue,
      hvalueNonneg, hvalueLeOne] using
      hasScheduledIIDPrefixKernelFactorization_sampledScheduledHalfTsallisTimeVaryingTrajectoryKernel
        (fun _ : Fin K => (0 : Rat)) value hvalue hvalueNonneg hvalueLeOne
        arms harms eta selector.finiteHistory horizon
  have hindependent : HasScheduledTimeVaryingIndependentMeanGapLaw
      mu arms loss model.bestArm actualGap horizon := by
    simpa only [mu, prior, trajectoryKernel, actualGap, loss] using
      hasScheduledTimeVaryingIndependentMeanGapLaw_of_iidLossState
        law value hvalue hvalueNonneg hvalueLeOne arms model.bestArm horizon
          trajectoryKernel hfactor
  have hactualGapLaw : HasScheduledTimeVaryingExpectedGapLaw
      mu arms harms eta loss model.bestArm actualGap horizon :=
    hasScheduledTimeVaryingExpectedGapLaw_of_independentMeanGapLaw
      mu arms harms eta loss model.bestArm actualGap horizon hindependent
  have hdeviation : ∀ t, t <= horizon -> ∀ arm,
      arm ∈ arms.erase model.bestArm ->
        |actualGap t arm - baseGap arm| <= deviation t arm := by
    intro t _ht arm _harm
    exact abs_iidLossStateTimeVaryingMeanGap_corrupted_sub_modelGap_le
      model armLaw hprob hbound hmean rewardShift t arm
  have hselfBounding :
      (Finset.range (horizon + 1)).sum (fun t =>
          (arms.erase model.bestArm).sum (fun arm =>
            baseGap arm * sampledScheduledHalfTsallisExpectedProbabilityAt
              mu arms harms eta t arm)) -
        scheduledTimeVaryingGapDeviationBudget
          arms model.bestArm horizon deviation <=
      integral mu (sampledScheduledHalfTsallisPredictableEnvironmentRegret
        arms harms eta loss (pointMass model.bestArm) horizon) :=
    integral_sampledScheduledHalfTsallisPredictableEnvironmentRegret_hasSelfBounding_of_timeVaryingPerturbedExpectedGapLaw
      mu arms harms eta loss (Finset.mem_univ model.bestArm) horizon
      baseGap actualGap deviation hactualGapLaw hdeviation
  have hharmonic :=
    integral_sampledScheduledHalfTsallisPredictableEnvironmentRegret_pointMass_le_sqrtSchedule_of_selfBounding
      prior arms harms loss (Finset.mem_univ model.bestArm) horizon baseGap
      (fun arm harm => hgapPos arm (Finset.ne_of_mem_erase harm))
      (scheduledTimeVaryingGapDeviationBudget
        arms model.bestArm horizon deviation)
      (by simpa only [mu, trajectoryKernel, selector, eta] using hselfBounding)
  let gapFactor := 1 + 25 * (arms.erase model.bestArm).sum
    (fun arm => 1 / baseGap arm)
  have hgapSum : 0 <= (arms.erase model.bestArm).sum
      (fun arm => 1 / baseGap arm) := by
    apply Finset.sum_nonneg
    intro arm harm
    exact le_of_lt (one_div_pos.mpr
      (hgapPos arm (Finset.ne_of_mem_erase harm)))
  have hgapFactor : 0 <= gapFactor := by
    dsimp only [gapFactor]
    nlinarith
  have hbudget := sampledScheduledHalfTsallisHarmonicBudget_le_one_add_log
    horizon
  have hmul : sampledScheduledHalfTsallisHarmonicBudget horizon * gapFactor <=
      (1 + Real.log (((horizon + 1 : Nat) : Real))) * gapFactor :=
    mul_le_mul_of_nonneg_right hbudget hgapFactor
  dsimp only at hharmonic
  calc
    integral mu (sampledScheduledHalfTsallisPredictableEnvironmentRegret
        arms harms eta loss (pointMass model.bestArm) horizon) <=
      sampledScheduledHalfTsallisHarmonicBudget horizon * gapFactor +
        scheduledTimeVaryingGapDeviationBudget
          arms model.bestArm horizon deviation := by
      simpa only [gapFactor, eta, baseGap] using hharmonic
    _ <= (1 + Real.log (((horizon + 1 : Nat) : Real))) * gapFactor +
        scheduledTimeVaryingGapDeviationBudget
          arms model.bestArm horizon deviation := by
      linarith
    _ = (1 + Real.log (((horizon + 1 : Nat) : Real))) *
        (1 + 25 * ((Finset.univ : Finset (Fin K)).erase model.bestArm).sum
          (fun arm => 1 / ((model.gap arm : Rat) : Real))) +
        finiteArmIIDTimeVaryingRewardCorruptionBudget
          model horizon rewardShift := by
      rfl

end Tsallis
end BanditRLProof
