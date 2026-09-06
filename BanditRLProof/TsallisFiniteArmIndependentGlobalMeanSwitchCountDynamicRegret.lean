import BanditRLProof.TsallisFiniteArmIndependentMeanSwitchCountDynamicRegret

/-!
# Global mean-switch-count dynamic regret

This module replaces the arm-indexed population-mean switch envelope by one
global prefix count. A round contributes exactly when at least one arm's
population mean changes.
-/

open scoped ENNReal NNReal Topology ProbabilityTheory
open MeasureTheory ProbabilityTheory Set Filter Finset

namespace BanditRLProof
namespace Tsallis

/-- Real-valued prefix count of rounds before `t` at which at least one arm's
population mean changes. -/
noncomputable def finiteArmIndependentCumulativeGlobalMeanSwitchCount {K : Nat}
    (armLaw : Nat -> Fin K -> Measure Rat) (t : Nat) : Real := by
  classical
  exact (Finset.range t).sum (fun s =>
    if ∃ arm : Fin K,
        finiteArmIndependentRewardMean armLaw (s + 1) arm ≠
          finiteArmIndependentRewardMean armLaw s arm then
      1
    else
      0)

@[simp]
theorem finiteArmIndependentCumulativeGlobalMeanSwitchCount_zero {K : Nat}
    (armLaw : Nat -> Fin K -> Measure Rat) :
    finiteArmIndependentCumulativeGlobalMeanSwitchCount armLaw 0 = 0 := by
  simp [finiteArmIndependentCumulativeGlobalMeanSwitchCount]

/-- The global real-valued count is the coercion of the filtered cardinality
of rounds with at least one population-mean change. -/
theorem finiteArmIndependentCumulativeGlobalMeanSwitchCount_eq_card {K : Nat}
    (armLaw : Nat -> Fin K -> Measure Rat) (t : Nat) :
    finiteArmIndependentCumulativeGlobalMeanSwitchCount armLaw t =
      ((((Finset.range t).filter (fun s =>
        ∃ arm : Fin K,
          finiteArmIndependentRewardMean armLaw (s + 1) arm ≠
            finiteArmIndependentRewardMean armLaw s arm)).card : Nat) : Real) := by
  classical
  rw [finiteArmIndependentCumulativeGlobalMeanSwitchCount, Finset.sum_boole]

/-- Every armwise prefix switch count is bounded by the global count. -/
theorem finiteArmIndependentCumulativeMeanSwitchCount_le_globalMeanSwitchCount
    {K : Nat} (armLaw : Nat -> Fin K -> Measure Rat)
    (t : Nat) (arm : Fin K) :
    finiteArmIndependentCumulativeMeanSwitchCount armLaw t arm <=
      finiteArmIndependentCumulativeGlobalMeanSwitchCount armLaw t := by
  classical
  unfold finiteArmIndependentCumulativeMeanSwitchCount
    finiteArmIndependentCumulativeGlobalMeanSwitchCount
  apply Finset.sum_le_sum
  intro s _hs
  by_cases hchange :
      finiteArmIndependentRewardMean armLaw (s + 1) arm ≠
        finiteArmIndependentRewardMean armLaw s arm
  · have hglobal : ∃ changedArm : Fin K,
        finiteArmIndependentRewardMean armLaw (s + 1) changedArm ≠
          finiteArmIndependentRewardMean armLaw s changedArm :=
      ⟨arm, hchange⟩
    simp [hchange, hglobal]
  · have hsame :
        finiteArmIndependentRewardMean armLaw (s + 1) arm =
          finiteArmIndependentRewardMean armLaw s arm :=
      not_ne_iff.mp hchange
    rw [if_pos hsame]
    split <;> norm_num

/-- Unit-supported cumulative path variation of any arm is bounded by the
single global population-mean switch count. -/
theorem finiteArmIndependentCumulativeMeanPathVariation_le_globalMeanSwitchCount
    {K : Nat} (armLaw : Nat -> Fin K -> Measure Rat)
    (hprob : forall t arm, IsProbabilityMeasure (armLaw t arm))
    (hbound : forall t arm, ∀ᵐ reward ∂armLaw t arm,
      ((reward : Rat) : Real) ∈ Set.Icc (0 : Real) 1)
    (t : Nat) (arm : Fin K) :
    finiteArmIndependentCumulativeMeanPathVariation armLaw t arm <=
      finiteArmIndependentCumulativeGlobalMeanSwitchCount armLaw t := by
  exact
    (finiteArmIndependentCumulativeMeanPathVariation_le_switchCount
      armLaw hprob hbound t arm).trans
        (finiteArmIndependentCumulativeMeanSwitchCount_le_globalMeanSwitchCount
          armLaw t arm)

/-- Initial model matching turns the global prefix switch count into the
all-time deviation envelope required by the dynamic-regret theorem. -/
theorem abs_finiteArmIndependentRewardMean_sub_model_le_globalMeanSwitchCount
    {K : Nat} (model : FiniteBanditModel K)
    (armLaw : Nat -> Fin K -> Measure Rat)
    (hprob : forall t arm, IsProbabilityMeasure (armLaw t arm))
    (hbound : forall t arm, ∀ᵐ reward ∂armLaw t arm,
      ((reward : Rat) : Real) ∈ Set.Icc (0 : Real) 1)
    (hinitialMean : forall arm,
      finiteArmIndependentRewardMean armLaw 0 arm =
        ((model.mean arm : Rat) : Real))
    (t : Nat) (arm : Fin K) :
    |finiteArmIndependentRewardMean armLaw t arm -
        ((model.mean arm : Rat) : Real)| <=
      finiteArmIndependentCumulativeGlobalMeanSwitchCount armLaw t := by
  exact
    (abs_finiteArmIndependentRewardMean_sub_model_le_switchCount
      model armLaw hprob hbound hinitialMean t arm).trans
        (finiteArmIndependentCumulativeMeanSwitchCount_le_globalMeanSwitchCount
          armLaw t arm)

/-- Dynamic all-regimes bound specialized to the exact global prefix
population-mean switch count. -/
noncomputable def
    finiteArmIndependentGlobalMeanSwitchCountDynamicAllRegimeBound
    {K : Nat} (model : FiniteBanditModel K)
    (armLaw : Nat -> Fin K -> Measure Rat) (horizon : Nat) : Real :=
  finiteArmIndependentDriftingMeanDynamicAllRegimeBound
    model armLaw horizon
      (fun t _ => finiteArmIndependentCumulativeGlobalMeanSwitchCount armLaw t)

@[simp]
theorem finiteArmIndependentGlobalMeanSwitchCountDynamicAllRegimeBound_fin_one
    (model : FiniteBanditModel 1)
    (armLaw : Nat -> Fin 1 -> Measure Rat) (horizon : Nat) :
    finiteArmIndependentGlobalMeanSwitchCountDynamicAllRegimeBound
        model armLaw horizon =
      1 + Real.log (((horizon + 1 : Nat) : Real)) := by
  simp [finiteArmIndependentGlobalMeanSwitchCountDynamicAllRegimeBound]

/-- Generated expected predictable-environment dynamic regret with the
all-time deviation envelope derived from one global prefix count of
population-mean change-points. No caller supplies a comparator, variation
family, armwise switch budget, or global switch budget. This is not a minimax
or horizon-compressed switch-rate theorem. -/
theorem integral_sampledScheduledHalfTsallisFiniteArmIndependentGlobalMeanSwitchCountDynamicRegret_le_allRegimes
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
      finiteArmIndependentGlobalMeanSwitchCountDynamicAllRegimeBound
        model armLaw horizon := by
  simpa only [
      finiteArmIndependentGlobalMeanSwitchCountDynamicAllRegimeBound] using
    integral_sampledScheduledHalfTsallisFiniteArmIndependentDriftingMeanDynamicRegret_le_allRegimes
      model armLaw hprob hbound
      (fun t _ => finiteArmIndependentCumulativeGlobalMeanSwitchCount armLaw t)
      (abs_finiteArmIndependentRewardMean_sub_model_le_globalMeanSwitchCount
        model armLaw hprob hbound hinitialMean)
      hgapPos hgapLeOne horizon

end Tsallis
end BanditRLProof
