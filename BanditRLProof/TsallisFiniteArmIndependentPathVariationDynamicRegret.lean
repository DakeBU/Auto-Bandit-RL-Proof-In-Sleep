import BanditRLProof.TsallisFiniteArmIndependentDriftingMeanDynamicRegret

/-!
# Path-variation dynamic regret for independent nonidentical reward laws

This module derives the mean-deviation envelope used by the compiled
drifting-mean dynamic-regret theorem from the actual reward-mean path. The
only model-alignment premise is equality of the actual and baseline means at
round zero.
-/

open scoped ENNReal NNReal Topology ProbabilityTheory
open MeasureTheory ProbabilityTheory Set Filter Finset

namespace BanditRLProof
namespace Tsallis

/-- Cumulative absolute variation of one arm's actual reward mean before
round `t`. -/
noncomputable def finiteArmIndependentCumulativeMeanPathVariation {K : Nat}
    (armLaw : Nat -> Fin K -> Measure Rat) (t : Nat) (arm : Fin K) : Real :=
  (Finset.range t).sum (fun s =>
    |finiteArmIndependentRewardMean armLaw (s + 1) arm -
      finiteArmIndependentRewardMean armLaw s arm|)

@[simp]
theorem finiteArmIndependentCumulativeMeanPathVariation_zero {K : Nat}
    (armLaw : Nat -> Fin K -> Measure Rat) (arm : Fin K) :
    finiteArmIndependentCumulativeMeanPathVariation armLaw 0 arm = 0 := by
  simp [finiteArmIndependentCumulativeMeanPathVariation]

theorem abs_finiteArmIndependentRewardMean_sub_zero_le_cumulativeMeanPathVariation
    {K : Nat} (armLaw : Nat -> Fin K -> Measure Rat)
    (t : Nat) (arm : Fin K) :
    |finiteArmIndependentRewardMean armLaw t arm -
        finiteArmIndependentRewardMean armLaw 0 arm| <=
      finiteArmIndependentCumulativeMeanPathVariation armLaw t arm := by
  induction t with
  | zero =>
      simp [finiteArmIndependentCumulativeMeanPathVariation]
  | succ t ih =>
      rw [finiteArmIndependentCumulativeMeanPathVariation,
        Finset.sum_range_succ]
      calc
        |finiteArmIndependentRewardMean armLaw (t + 1) arm -
            finiteArmIndependentRewardMean armLaw 0 arm| =
            |(finiteArmIndependentRewardMean armLaw (t + 1) arm -
                finiteArmIndependentRewardMean armLaw t arm) +
              (finiteArmIndependentRewardMean armLaw t arm -
                finiteArmIndependentRewardMean armLaw 0 arm)| := by
          congr 1
          ring
        _ <=
            |finiteArmIndependentRewardMean armLaw (t + 1) arm -
                finiteArmIndependentRewardMean armLaw t arm| +
              |finiteArmIndependentRewardMean armLaw t arm -
                finiteArmIndependentRewardMean armLaw 0 arm| :=
          abs_add_le _ _
        _ <=
            |finiteArmIndependentRewardMean armLaw (t + 1) arm -
                finiteArmIndependentRewardMean armLaw t arm| +
              finiteArmIndependentCumulativeMeanPathVariation armLaw t arm :=
          add_le_add (le_refl _) ih
        _ =
            finiteArmIndependentCumulativeMeanPathVariation armLaw t arm +
              |finiteArmIndependentRewardMean armLaw (t + 1) arm -
                finiteArmIndependentRewardMean armLaw t arm| := by
          ring

/-- Initial mean matching turns cumulative actual-mean path variation into the
all-time model-deviation envelope required by the drifting-mean theorem. -/
theorem abs_finiteArmIndependentRewardMean_sub_model_le_cumulativeMeanPathVariation
    {K : Nat} (model : FiniteBanditModel K)
    (armLaw : Nat -> Fin K -> Measure Rat)
    (hinitialMean : forall arm,
      finiteArmIndependentRewardMean armLaw 0 arm =
        ((model.mean arm : Rat) : Real))
    (t : Nat) (arm : Fin K) :
    |finiteArmIndependentRewardMean armLaw t arm -
        ((model.mean arm : Rat) : Real)| <=
      finiteArmIndependentCumulativeMeanPathVariation armLaw t arm := by
  rw [show ((model.mean arm : Rat) : Real) =
      finiteArmIndependentRewardMean armLaw 0 arm by
    exact (hinitialMean arm).symm]
  exact
    abs_finiteArmIndependentRewardMean_sub_zero_le_cumulativeMeanPathVariation
      armLaw t arm

/-- The compiled dynamic all-regimes bound specialized to the law-derived
cumulative population-mean path-variation envelope. -/
noncomputable def finiteArmIndependentPathVariationDynamicAllRegimeBound
    {K : Nat} (model : FiniteBanditModel K)
    (armLaw : Nat -> Fin K -> Measure Rat) (horizon : Nat) : Real :=
  finiteArmIndependentDriftingMeanDynamicAllRegimeBound
    model armLaw horizon
      (finiteArmIndependentCumulativeMeanPathVariation armLaw)

@[simp]
theorem finiteArmIndependentPathVariationDynamicAllRegimeBound_fin_one
    (model : FiniteBanditModel 1)
    (armLaw : Nat -> Fin 1 -> Measure Rat) (horizon : Nat) :
    finiteArmIndependentPathVariationDynamicAllRegimeBound
        model armLaw horizon =
      1 + Real.log (((horizon + 1 : Nat) : Real)) := by
  simp [finiteArmIndependentPathVariationDynamicAllRegimeBound]

/-- Generated expected predictable-environment dynamic regret with the
all-time deviation envelope derived from the reward laws' population-mean
path variation. No caller supplies a deviation envelope or the moving
comparator. This retains one cumulative prefix envelope at every included
time; it is not a horizon-compressed or minimax-sharp standard `V_T` bound. -/
theorem integral_sampledScheduledHalfTsallisFiniteArmIndependentPathVariationDynamicRegret_le_allRegimes
    {K : Nat} (model : FiniteBanditModel K)
    (armLaw : Nat -> Fin K -> Measure Rat)
    (hprob : forall t arm, IsProbabilityMeasure (armLaw t arm))
    (hbound : forall t arm, ∀ᵐ reward ∂armLaw t arm,
      ((reward : Rat) : Real) ∈ Set.Icc (0 : Real) 1)
    (hinitialMean : forall arm,
      finiteArmIndependentRewardMean armLaw 0 arm =
        ((model.mean arm : Rat) : Real))
    (hgapPos : forall arm, arm ≠ model.bestArm ->
      0 < ((model.gap arm : Rat) : Real))
    (hgapLeOne : forall arm, arm ≠ model.bestArm ->
      ((model.gap arm : Rat) : Real) <= 1)
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
    let mu := prior.compProd
      (sampledScheduledHalfTsallisTrajectoryKernel
        (Finset.univ : Finset (Fin K)) Finset.univ_nonempty
        sampledScheduledHalfTsallisSqrtSchedule
        selector.finiteHistory loss.environment)
    integral mu
        (sampledScheduledHalfTsallisPredictableMovingComparatorEnvironmentRegret
          (Finset.univ : Finset (Fin K)) Finset.univ_nonempty
          sampledScheduledHalfTsallisSqrtSchedule loss
          (finiteArmIndependentBestArmAt model armLaw) horizon) <=
      finiteArmIndependentPathVariationDynamicAllRegimeBound
        model armLaw horizon := by
  simpa only [finiteArmIndependentPathVariationDynamicAllRegimeBound] using
    integral_sampledScheduledHalfTsallisFiniteArmIndependentDriftingMeanDynamicRegret_le_allRegimes
      model armLaw hprob hbound
      (finiteArmIndependentCumulativeMeanPathVariation armLaw)
      (abs_finiteArmIndependentRewardMean_sub_model_le_cumulativeMeanPathVariation
        model armLaw hinitialMean)
      hgapPos hgapLeOne horizon

end Tsallis
end BanditRLProof
