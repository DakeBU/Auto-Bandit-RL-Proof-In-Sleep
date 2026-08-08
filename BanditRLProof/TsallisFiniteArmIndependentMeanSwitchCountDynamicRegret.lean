import BanditRLProof.TsallisFiniteArmIndependentPathVariationDynamicRegret

/-!
# Mean-switch-count dynamic regret for independent nonidentical reward laws

This module bounds each arm's cumulative population-mean path variation by
the number of its nonzero consecutive mean changes. The generated dynamic
regret theorem therefore needs no caller-supplied variation or switch-count
budget.
-/

open scoped ENNReal NNReal Topology ProbabilityTheory
open MeasureTheory ProbabilityTheory Set Filter Finset

namespace BanditRLProof
namespace Tsallis

/-- A bounded probability reward law has its population mean in the unit
interval. -/
theorem finiteArmIndependentRewardMean_mem_Icc {K : Nat}
    (armLaw : Nat -> Fin K -> Measure Rat)
    (hprob : forall t arm, IsProbabilityMeasure (armLaw t arm))
    (hbound : forall t arm, ∀ᵐ reward ∂armLaw t arm,
      ((reward : Rat) : Real) ∈ Set.Icc (0 : Real) 1)
    (t : Nat) (arm : Fin K) :
    finiteArmIndependentRewardMean armLaw t arm ∈
      Set.Icc (0 : Real) 1 := by
  letI : IsProbabilityMeasure (armLaw t arm) := hprob t arm
  have hmean :
      finiteArmIndependentRewardMean armLaw t arm =
        integral (armLaw t arm) clippedUnitReward := by
    rw [finiteArmIndependentRewardMean]
    apply integral_congr_ae
    filter_upwards [hbound t arm] with reward hreward
    exact (clippedUnitReward_eq_of_mem_Icc reward hreward).symm
  rw [hmean]
  constructor
  · exact integral_nonneg_of_ae
      (Filter.Eventually.of_forall clippedUnitReward_nonneg)
  · have hmono :=
      integral_mono_ae
        (integrable_clippedUnitReward (armLaw t arm))
        (integrable_const (1 : Real))
        (Filter.Eventually.of_forall clippedUnitReward_le_one)
    simpa using hmono

/-- Real-valued prefix count of the rounds before `t` at which one arm's
population mean changes. -/
noncomputable def finiteArmIndependentCumulativeMeanSwitchCount {K : Nat}
    (armLaw : Nat -> Fin K -> Measure Rat)
    (t : Nat) (arm : Fin K) : Real := by
  classical
  exact (Finset.range t).sum (fun s =>
    if finiteArmIndependentRewardMean armLaw (s + 1) arm =
        finiteArmIndependentRewardMean armLaw s arm then
      0
    else
      1)

@[simp]
theorem finiteArmIndependentCumulativeMeanSwitchCount_zero {K : Nat}
    (armLaw : Nat -> Fin K -> Measure Rat) (arm : Fin K) :
    finiteArmIndependentCumulativeMeanSwitchCount armLaw 0 arm = 0 := by
  simp [finiteArmIndependentCumulativeMeanSwitchCount]

/-- The real-valued switch count is exactly the coercion of the filtered
cardinality of nonzero consecutive population-mean changes. -/
theorem finiteArmIndependentCumulativeMeanSwitchCount_eq_card {K : Nat}
    (armLaw : Nat -> Fin K -> Measure Rat)
    (t : Nat) (arm : Fin K) :
    finiteArmIndependentCumulativeMeanSwitchCount armLaw t arm =
      ((((Finset.range t).filter (fun s =>
        finiteArmIndependentRewardMean armLaw (s + 1) arm ≠
          finiteArmIndependentRewardMean armLaw s arm)).card : Nat) : Real) := by
  classical
  simp [finiteArmIndependentCumulativeMeanSwitchCount,
    Finset.card_filter]

/-- Unit-supported reward laws make every nonzero population-mean jump at
most one, so cumulative mean path variation is bounded by switch count. -/
theorem finiteArmIndependentCumulativeMeanPathVariation_le_switchCount
    {K : Nat} (armLaw : Nat -> Fin K -> Measure Rat)
    (hprob : forall t arm, IsProbabilityMeasure (armLaw t arm))
    (hbound : forall t arm, ∀ᵐ reward ∂armLaw t arm,
      ((reward : Rat) : Real) ∈ Set.Icc (0 : Real) 1)
    (t : Nat) (arm : Fin K) :
    finiteArmIndependentCumulativeMeanPathVariation armLaw t arm <=
      finiteArmIndependentCumulativeMeanSwitchCount armLaw t arm := by
  classical
  unfold finiteArmIndependentCumulativeMeanPathVariation
    finiteArmIndependentCumulativeMeanSwitchCount
  apply Finset.sum_le_sum
  intro s _hs
  by_cases hsame :
      finiteArmIndependentRewardMean armLaw (s + 1) arm =
        finiteArmIndependentRewardMean armLaw s arm
  · simp [hsame]
  · rw [if_neg hsame]
    have hnext :=
      finiteArmIndependentRewardMean_mem_Icc
        armLaw hprob hbound (s + 1) arm
    have hcurrent :=
      finiteArmIndependentRewardMean_mem_Icc
        armLaw hprob hbound s arm
    rw [abs_sub_le_iff]
    constructor <;> linarith [hnext.1, hnext.2, hcurrent.1, hcurrent.2]

/-- Initial model matching turns the armwise prefix switch count into the
all-time deviation envelope required by the dynamic-regret theorem. -/
theorem abs_finiteArmIndependentRewardMean_sub_model_le_switchCount
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
      finiteArmIndependentCumulativeMeanSwitchCount armLaw t arm := by
  exact
    (abs_finiteArmIndependentRewardMean_sub_model_le_cumulativeMeanPathVariation
      model armLaw hinitialMean t arm).trans
        (finiteArmIndependentCumulativeMeanPathVariation_le_switchCount
          armLaw hprob hbound t arm)

/-- Dynamic all-regimes bound specialized to the exact armwise prefix
population-mean switch count. -/
noncomputable def finiteArmIndependentMeanSwitchCountDynamicAllRegimeBound
    {K : Nat} (model : FiniteBanditModel K)
    (armLaw : Nat -> Fin K -> Measure Rat) (horizon : Nat) : Real :=
  finiteArmIndependentDriftingMeanDynamicAllRegimeBound
    model armLaw horizon
      (finiteArmIndependentCumulativeMeanSwitchCount armLaw)

@[simp]
theorem finiteArmIndependentMeanSwitchCountDynamicAllRegimeBound_fin_one
    (model : FiniteBanditModel 1)
    (armLaw : Nat -> Fin 1 -> Measure Rat) (horizon : Nat) :
    finiteArmIndependentMeanSwitchCountDynamicAllRegimeBound
        model armLaw horizon =
      1 + Real.log (((horizon + 1 : Nat) : Real)) := by
  simp [finiteArmIndependentMeanSwitchCountDynamicAllRegimeBound]

/-- Generated expected predictable-environment dynamic regret with the
all-time deviation envelope derived from armwise population-mean switch
counts. No caller supplies a comparator, variation family, or switch budget.
This is an exact prefix-envelope specialization, not a minimax change-point
or horizon-compressed standard nonstationary rate. -/
theorem integral_sampledScheduledHalfTsallisFiniteArmIndependentMeanSwitchCountDynamicRegret_le_allRegimes
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
      finiteArmIndependentMeanSwitchCountDynamicAllRegimeBound
        model armLaw horizon := by
  simpa only [finiteArmIndependentMeanSwitchCountDynamicAllRegimeBound] using
    integral_sampledScheduledHalfTsallisFiniteArmIndependentDriftingMeanDynamicRegret_le_allRegimes
      model armLaw hprob hbound
      (finiteArmIndependentCumulativeMeanSwitchCount armLaw)
      (abs_finiteArmIndependentRewardMean_sub_model_le_switchCount
        model armLaw hprob hbound hinitialMean)
      hgapPos hgapLeOne horizon

end Tsallis
end BanditRLProof
