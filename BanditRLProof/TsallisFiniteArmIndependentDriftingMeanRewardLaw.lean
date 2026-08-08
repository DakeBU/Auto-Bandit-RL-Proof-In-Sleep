import BanditRLProof.TsallisFiniteArmIndependentRewardLaw

/-!
# Finite-arm independent reward laws with drifting means

Each round may use a different probability law for every arm.  The roundwise
arm means may drift from a fixed finite-bandit model, with a deterministic
coordinatewise deviation envelope.  The resulting regret theorem charges the
induced two-arm gap deviation explicitly.
-/

namespace BanditRLProof
namespace Tsallis

open MeasureTheory ProbabilityTheory

/-- The actual mean reward of arm `arm` at round `t`. -/
noncomputable def finiteArmIndependentRewardMean {K : Nat}
    (armLaw : Nat -> Fin K -> Measure Rat) (t : Nat) (arm : Fin K) : Real :=
  integral (armLaw t arm) (fun reward : Rat => ((reward : Rat) : Real))

/-- Under the unit-support contract, the roundwise product-law loss gap is the
difference between the actual mean rewards of the best and selected arms. -/
theorem independentLossStateTimeVaryingMeanGap_finiteArmIndependentRewardVectorLoss_eq_mean_sub
    {K : Nat} (armLaw : Nat -> Fin K -> Measure Rat)
    (hprob : forall t arm, IsProbabilityMeasure (armLaw t arm))
    (hbound : forall t arm, ∀ᵐ reward ∂armLaw t arm,
      ((reward : Rat) : Real) ∈ Set.Icc (0 : Real) 1)
    (t : Nat) (best arm : Fin K) :
    independentLossStateTimeVaryingMeanGap
        (finiteArmIndependentRewardVectorLaw armLaw)
        (fun _ => finiteArmIIDRewardVectorLoss)
        t best arm =
      finiteArmIndependentRewardMean armLaw t best -
        finiteArmIndependentRewardMean armLaw t arm := by
  letI (i : Fin K) : IsProbabilityMeasure (armLaw t i) := hprob t i
  have hbestIntegrable : Integrable
      (fun state : Fin K -> Rat => clippedUnitReward (state best))
      (finiteArmIIDRewardVectorLaw (armLaw t)) := by
    exact MeasureTheory.integrable_comp_eval
      (integrable_clippedUnitReward (armLaw t best))
  have harmIntegrable : Integrable
      (fun state : Fin K -> Rat => clippedUnitReward (state arm))
      (finiteArmIIDRewardVectorLaw (armLaw t)) := by
    exact MeasureTheory.integrable_comp_eval
      (integrable_clippedUnitReward (armLaw t arm))
  have hcoordinate (action : Fin K) :
      integral (finiteArmIIDRewardVectorLaw (armLaw t))
          (fun state => clippedUnitReward (state action)) =
        finiteArmIndependentRewardMean armLaw t action := by
    rw [finiteArmIIDRewardVectorLaw,
      MeasureTheory.integral_comp_eval
        (integrable_clippedUnitReward (armLaw t action)).aestronglyMeasurable]
    apply integral_congr_ae
    filter_upwards [hbound t action] with reward hreward
    exact clippedUnitReward_eq_of_mem_Icc reward hreward
  rw [independentLossStateTimeVaryingMeanGap,
    finiteArmIndependentRewardVectorLaw]
  calc
    integral (finiteArmIIDRewardVectorLaw (armLaw t))
        (fun state => finiteArmIIDRewardVectorLoss state arm -
          finiteArmIIDRewardVectorLoss state best) =
        integral (finiteArmIIDRewardVectorLaw (armLaw t))
          (fun state => clippedUnitReward (state best) -
            clippedUnitReward (state arm)) := by
      congr 1
      funext state
      simp only [finiteArmIIDRewardVectorLoss]
      ring
    _ = integral (finiteArmIIDRewardVectorLaw (armLaw t))
          (fun state => clippedUnitReward (state best)) -
        integral (finiteArmIIDRewardVectorLaw (armLaw t))
          (fun state => clippedUnitReward (state arm)) :=
      integral_sub hbestIntegrable harmIntegrable
    _ = finiteArmIndependentRewardMean armLaw t best -
        finiteArmIndependentRewardMean armLaw t arm := by
      rw [hcoordinate best, hcoordinate arm]

/-- The actual loss gap stays within the sum of the two supplied arm-mean
deviation envelopes from the fixed model gap. -/
theorem abs_independentLossStateTimeVaryingMeanGap_sub_modelGap_le
    {K : Nat} (model : FiniteBanditModel K)
    (armLaw : Nat -> Fin K -> Measure Rat)
    (hprob : forall t arm, IsProbabilityMeasure (armLaw t arm))
    (hbound : forall t arm, ∀ᵐ reward ∂armLaw t arm,
      ((reward : Rat) : Real) ∈ Set.Icc (0 : Real) 1)
    (meanDeviation : Nat -> Fin K -> Real)
    (hmeanDeviation : forall t arm,
      |finiteArmIndependentRewardMean armLaw t arm -
          ((model.mean arm : Rat) : Real)| <= meanDeviation t arm)
    (t : Nat) (arm : Fin K) (harm : arm ≠ model.bestArm) :
    |independentLossStateTimeVaryingMeanGap
          (finiteArmIndependentRewardVectorLaw armLaw)
          (fun _ => finiteArmIIDRewardVectorLoss)
          t model.bestArm arm -
        ((model.gap arm : Rat) : Real)| <=
      meanDeviation t arm + meanDeviation t model.bestArm := by
  rw [
    independentLossStateTimeVaryingMeanGap_finiteArmIndependentRewardVectorLoss_eq_mean_sub
      armLaw hprob hbound]
  have hgap :
      ((model.gap arm : Rat) : Real) =
        ((model.mean model.bestArm : Rat) : Real) -
          ((model.mean arm : Rat) : Real) := by
    simp [FiniteBanditModel.gap, FiniteBanditModel.bestMean, harm]
  rw [hgap]
  calc
    |(finiteArmIndependentRewardMean armLaw t model.bestArm -
          finiteArmIndependentRewardMean armLaw t arm) -
        (((model.mean model.bestArm : Rat) : Real) -
          ((model.mean arm : Rat) : Real))| =
        |(finiteArmIndependentRewardMean armLaw t model.bestArm -
            ((model.mean model.bestArm : Rat) : Real)) -
          (finiteArmIndependentRewardMean armLaw t arm -
            ((model.mean arm : Rat) : Real))| := by ring_nf
    _ <= |finiteArmIndependentRewardMean armLaw t model.bestArm -
          ((model.mean model.bestArm : Rat) : Real)| +
        |finiteArmIndependentRewardMean armLaw t arm -
          ((model.mean arm : Rat) : Real)| := abs_sub _ _
    _ <= meanDeviation t model.bestArm + meanDeviation t arm :=
      add_le_add (hmeanDeviation t model.bestArm) (hmeanDeviation t arm)
    _ = meanDeviation t arm + meanDeviation t model.bestArm := add_comm _ _

/-- Explicit accumulated gap-deviation budget induced by armwise drifting
means through the inclusive horizon. -/
noncomputable def finiteArmIndependentMeanDeviationBudget {K : Nat}
    (model : FiniteBanditModel K) (horizon : Nat)
    (meanDeviation : Nat -> Fin K -> Real) : Real :=
  scheduledTimeVaryingGapDeviationBudget
    (Finset.univ : Finset (Fin K)) model.bestArm horizon
    (fun t arm =>
      meanDeviation t arm + meanDeviation t model.bestArm)

theorem finiteArmIndependentMeanDeviationBudget_eq {K : Nat}
    (model : FiniteBanditModel K) (horizon : Nat)
    (meanDeviation : Nat -> Fin K -> Real) :
    finiteArmIndependentMeanDeviationBudget model horizon meanDeviation =
      (Finset.range (horizon + 1)).sum (fun t =>
        ((Finset.univ : Finset (Fin K)).erase model.bestArm).sum
          (fun arm =>
            meanDeviation t arm + meanDeviation t model.bestArm)) := by
  rfl

@[simp]
theorem finiteArmIndependentMeanDeviationBudget_zero {K : Nat}
    (model : FiniteBanditModel K) (horizon : Nat) :
    finiteArmIndependentMeanDeviationBudget model horizon
      (fun _ _ => 0) = 0 := by
  simp [finiteArmIndependentMeanDeviationBudget,
    scheduledTimeVaryingGapDeviationBudget]

/-- Independent nonidentical reward laws with an armwise mean-deviation
envelope supply the terminal self-bound consumed by both logarithmic and
refined square-root schedule routes. -/
theorem integral_sampledScheduledHalfTsallisFiniteArmIndependentDriftingMeanRewardLaw_hasSelfBounding
    {K : Nat} (model : FiniteBanditModel K)
    (armLaw : Nat -> Fin K -> Measure Rat)
    (hprob : forall t arm, IsProbabilityMeasure (armLaw t arm))
    (hbound : forall t arm, ∀ᵐ reward ∂armLaw t arm,
      ((reward : Rat) : Real) ∈ Set.Icc (0 : Real) 1)
    (meanDeviation : Nat -> Fin K -> Real)
    (hmeanDeviation : forall t arm,
      |finiteArmIndependentRewardMean armLaw t arm -
          ((model.mean arm : Rat) : Real)| <= meanDeviation t arm)
    (horizon : Nat) :
    letI : Nonempty (Fin K) := ⟨model.bestArm⟩
    let law := finiteArmIndependentRewardVectorLaw armLaw
    let value := fun _ : Nat => finiteArmIIDRewardVectorLoss
    let loss := iidTimeVaryingLossStatePredictableLossVector value
      (fun _ => measurable_finiteArmIIDRewardVectorLoss)
      (fun _ => finiteArmIIDRewardVectorLoss_nonneg)
      (fun _ => finiteArmIIDRewardVectorLoss_le_one)
    let selector :=
      canonicalHalfTsallisScheduleGeneratedSelectorMeasurability
        (Finset.univ : Finset (Fin K)) Finset.univ_nonempty
        sampledScheduledHalfTsallisSqrtSchedule loss
    let prior := Measure.infinitePi law
    let mu := prior ⊗ₘ sampledScheduledHalfTsallisTrajectoryKernel
      (Finset.univ : Finset (Fin K)) Finset.univ_nonempty
      sampledScheduledHalfTsallisSqrtSchedule
      selector.finiteHistory loss.environment
    let baseGap := fun arm : Fin K => ((model.gap arm : Rat) : Real)
    (Finset.range (horizon + 1)).sum (fun t =>
        ((Finset.univ : Finset (Fin K)).erase model.bestArm).sum (fun arm =>
          baseGap arm * sampledScheduledHalfTsallisExpectedProbabilityAt
            mu (Finset.univ : Finset (Fin K)) Finset.univ_nonempty
              sampledScheduledHalfTsallisSqrtSchedule t arm)) -
      finiteArmIndependentMeanDeviationBudget model horizon meanDeviation <=
        integral mu (sampledScheduledHalfTsallisPredictableEnvironmentRegret
          (Finset.univ : Finset (Fin K)) Finset.univ_nonempty
          sampledScheduledHalfTsallisSqrtSchedule loss
          (pointMass model.bestArm) horizon) := by
  letI : Nonempty (Fin K) := ⟨model.bestArm⟩
  letI (t : Nat) (arm : Fin K) :
      IsProbabilityMeasure (armLaw t arm) := hprob t arm
  letI (t : Nat) :
      IsProbabilityMeasure (finiteArmIndependentRewardVectorLaw armLaw t) := by
    rw [finiteArmIndependentRewardVectorLaw, finiteArmIIDRewardVectorLaw]
    infer_instance
  dsimp only
  let value : Nat -> (Fin K -> Rat) -> Fin K -> Real :=
    fun _ => finiteArmIIDRewardVectorLoss
  let loss := iidTimeVaryingLossStatePredictableLossVector value
    (fun _ => measurable_finiteArmIIDRewardVectorLoss)
    (fun _ => finiteArmIIDRewardVectorLoss_nonneg)
    (fun _ => finiteArmIIDRewardVectorLoss_le_one)
  let arms : Finset (Fin K) := Finset.univ
  let harms : arms.Nonempty := Finset.univ_nonempty
  let eta := sampledScheduledHalfTsallisSqrtSchedule
  let selector := canonicalHalfTsallisScheduleGeneratedSelectorMeasurability
    arms harms eta loss
  let trajectoryKernel := sampledScheduledHalfTsallisTrajectoryKernel
    arms harms eta selector.finiteHistory loss.environment
  let prior := Measure.infinitePi
    (finiteArmIndependentRewardVectorLaw armLaw)
  let mu := prior ⊗ₘ trajectoryKernel
  let actualGap := fun t arm =>
    independentLossStateTimeVaryingMeanGap
      (finiteArmIndependentRewardVectorLaw armLaw)
      (fun _ => finiteArmIIDRewardVectorLoss)
      t model.bestArm arm
  let baseGap := fun arm : Fin K => ((model.gap arm : Rat) : Real)
  let deviation := fun (t : Nat) (arm : Fin K) =>
    meanDeviation t arm + meanDeviation t model.bestArm
  have hfactor : HasScheduledIIDPrefixKernelFactorization trajectoryKernel
      horizon := by
    simpa only [trajectoryKernel, selector, eta, loss, value] using
      hasScheduledIIDPrefixKernelFactorization_sampledScheduledHalfTsallisTimeVaryingTrajectoryKernel
        (fun _ : Fin K => (0 : Rat))
        (fun _ : Nat => finiteArmIIDRewardVectorLoss)
        (fun _ => measurable_finiteArmIIDRewardVectorLoss)
        (fun _ => finiteArmIIDRewardVectorLoss_nonneg)
        (fun _ => finiteArmIIDRewardVectorLoss_le_one)
        arms harms eta selector.finiteHistory horizon
  have hindependent : HasScheduledTimeVaryingIndependentMeanGapLaw
      mu arms loss model.bestArm actualGap horizon := by
    simpa only [mu, prior, actualGap, loss, value] using
      hasScheduledTimeVaryingIndependentMeanGapLaw_of_independentLossState
        (finiteArmIndependentRewardVectorLaw armLaw)
        (fun _ : Nat => finiteArmIIDRewardVectorLoss)
        (fun _ => measurable_finiteArmIIDRewardVectorLoss)
        (fun _ => finiteArmIIDRewardVectorLoss_nonneg)
        (fun _ => finiteArmIIDRewardVectorLoss_le_one)
        arms model.bestArm horizon trajectoryKernel hfactor
  have hactualGapLaw : HasScheduledTimeVaryingExpectedGapLaw
      mu arms harms eta loss model.bestArm actualGap horizon :=
    hasScheduledTimeVaryingExpectedGapLaw_of_independentMeanGapLaw
      mu arms harms eta loss model.bestArm actualGap horizon hindependent
  have hdeviation : forall t, t <= horizon -> forall arm,
      arm ∈ arms.erase model.bestArm ->
        |actualGap t arm - baseGap arm| <= deviation t arm := by
    intro t _ht arm harm
    exact abs_independentLossStateTimeVaryingMeanGap_sub_modelGap_le
      model armLaw hprob hbound meanDeviation hmeanDeviation t arm
        (Finset.ne_of_mem_erase harm)
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
  simpa only [arms, harms, eta, selector, trajectoryKernel, prior, mu, loss,
    value, baseGap, deviation, finiteArmIndependentMeanDeviationBudget] using
      hselfBounding

/-- Generated scheduled half-Tsallis logarithmic regret against the fixed
baseline comparator `model.bestArm` for independent, nonidentical finite-arm
reward laws whose means drift within an explicit coordinatewise envelope.
This is a static-comparator theorem, not dynamic regret against each round's
best actual mean. -/
theorem integral_sampledScheduledHalfTsallisFiniteArmIndependentDriftingMeanRewardLawRegret_le_log
    {K : Nat} (model : FiniteBanditModel K)
    (armLaw : Nat -> Fin K -> Measure Rat)
    (hprob : forall t arm, IsProbabilityMeasure (armLaw t arm))
    (hbound : forall t arm, ∀ᵐ reward ∂armLaw t arm,
      ((reward : Rat) : Real) ∈ Set.Icc (0 : Real) 1)
    (meanDeviation : Nat -> Fin K -> Real)
    (hmeanDeviation : forall t arm,
      |finiteArmIndependentRewardMean armLaw t arm -
          ((model.mean arm : Rat) : Real)| <= meanDeviation t arm)
    (hgapPos : forall arm, arm ≠ model.bestArm ->
      0 < ((model.gap arm : Rat) : Real))
    (horizon : Nat) :
    letI : Nonempty (Fin K) := ⟨model.bestArm⟩
    let law := finiteArmIndependentRewardVectorLaw armLaw
    let value := fun _ : Nat => finiteArmIIDRewardVectorLoss
    let loss := iidTimeVaryingLossStatePredictableLossVector value
      (fun _ => measurable_finiteArmIIDRewardVectorLoss)
      (fun _ => finiteArmIIDRewardVectorLoss_nonneg)
      (fun _ => finiteArmIIDRewardVectorLoss_le_one)
    let selector :=
      canonicalHalfTsallisScheduleGeneratedSelectorMeasurability
        (Finset.univ : Finset (Fin K)) Finset.univ_nonempty
        sampledScheduledHalfTsallisSqrtSchedule loss
    let prior := Measure.infinitePi law
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
        finiteArmIndependentMeanDeviationBudget
          model horizon meanDeviation := by
  letI : Nonempty (Fin K) := ⟨model.bestArm⟩
  letI (t : Nat) (arm : Fin K) :
      IsProbabilityMeasure (armLaw t arm) := hprob t arm
  letI (t : Nat) :
      IsProbabilityMeasure (finiteArmIndependentRewardVectorLaw armLaw t) := by
    rw [finiteArmIndependentRewardVectorLaw, finiteArmIIDRewardVectorLaw]
    infer_instance
  dsimp only
  let value : Nat -> (Fin K -> Rat) -> Fin K -> Real :=
    fun _ => finiteArmIIDRewardVectorLoss
  let loss := iidTimeVaryingLossStatePredictableLossVector value
    (fun _ => measurable_finiteArmIIDRewardVectorLoss)
    (fun _ => finiteArmIIDRewardVectorLoss_nonneg)
    (fun _ => finiteArmIIDRewardVectorLoss_le_one)
  let arms : Finset (Fin K) := Finset.univ
  let harms : arms.Nonempty := Finset.univ_nonempty
  let eta := sampledScheduledHalfTsallisSqrtSchedule
  let selector := canonicalHalfTsallisScheduleGeneratedSelectorMeasurability
    arms harms eta loss
  let trajectoryKernel := sampledScheduledHalfTsallisTrajectoryKernel
    arms harms eta selector.finiteHistory loss.environment
  let prior := Measure.infinitePi
    (finiteArmIndependentRewardVectorLaw armLaw)
  let mu := prior ⊗ₘ trajectoryKernel
  let actualGap := fun t arm =>
    independentLossStateTimeVaryingMeanGap
      (finiteArmIndependentRewardVectorLaw armLaw)
      (fun _ => finiteArmIIDRewardVectorLoss)
      t model.bestArm arm
  let baseGap := fun arm : Fin K => ((model.gap arm : Rat) : Real)
  let deviation := fun (t : Nat) (arm : Fin K) =>
    meanDeviation t arm + meanDeviation t model.bestArm
  have hfactor : HasScheduledIIDPrefixKernelFactorization trajectoryKernel
      horizon := by
    simpa only [trajectoryKernel, selector, eta, loss, value] using
      hasScheduledIIDPrefixKernelFactorization_sampledScheduledHalfTsallisTimeVaryingTrajectoryKernel
        (fun _ : Fin K => (0 : Rat))
        (fun _ : Nat => finiteArmIIDRewardVectorLoss)
        (fun _ => measurable_finiteArmIIDRewardVectorLoss)
        (fun _ => finiteArmIIDRewardVectorLoss_nonneg)
        (fun _ => finiteArmIIDRewardVectorLoss_le_one)
        arms harms eta selector.finiteHistory horizon
  have hindependent : HasScheduledTimeVaryingIndependentMeanGapLaw
      mu arms loss model.bestArm actualGap horizon := by
    simpa only [mu, prior, actualGap, loss, value] using
      hasScheduledTimeVaryingIndependentMeanGapLaw_of_independentLossState
        (finiteArmIndependentRewardVectorLaw armLaw)
        (fun _ : Nat => finiteArmIIDRewardVectorLoss)
        (fun _ => measurable_finiteArmIIDRewardVectorLoss)
        (fun _ => finiteArmIIDRewardVectorLoss_nonneg)
        (fun _ => finiteArmIIDRewardVectorLoss_le_one)
        arms model.bestArm horizon trajectoryKernel hfactor
  have hactualGapLaw : HasScheduledTimeVaryingExpectedGapLaw
      mu arms harms eta loss model.bestArm actualGap horizon :=
    hasScheduledTimeVaryingExpectedGapLaw_of_independentMeanGapLaw
      mu arms harms eta loss model.bestArm actualGap horizon hindependent
  have hdeviation : forall t, t <= horizon -> forall arm,
      arm ∈ arms.erase model.bestArm ->
        |actualGap t arm - baseGap arm| <= deviation t arm := by
    intro t _ht arm harm
    exact abs_independentLossStateTimeVaryingMeanGap_sub_modelGap_le
      model armLaw hprob hbound meanDeviation hmeanDeviation t arm
        (Finset.ne_of_mem_erase harm)
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
        finiteArmIndependentMeanDeviationBudget
          model horizon meanDeviation := by
      rfl

end Tsallis
end BanditRLProof
