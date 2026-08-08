import BanditRLProof.TsallisFiniteArmIndependentGlobalMeanSwitchCountDynamicRegret

/-!
# Horizon-compressed global mean-switch-count dynamic regret

This module replaces every time-indexed global prefix count in the
logarithmic dynamic-regret route by the single terminal count at `horizon`.
The resulting bound is explicit and finite-sum free in its
nonstationarity term, but remains linear rather than minimax-sharp.
-/

open scoped ENNReal NNReal Topology ProbabilityTheory
open MeasureTheory ProbabilityTheory Set Filter Finset

namespace BanditRLProof
namespace Tsallis

/-- The global population-mean switch count is nonnegative. -/
theorem finiteArmIndependentCumulativeGlobalMeanSwitchCount_nonneg {K : Nat}
    (armLaw : Nat -> Fin K -> Measure Rat) (t : Nat) :
    0 <= finiteArmIndependentCumulativeGlobalMeanSwitchCount armLaw t := by
  classical
  unfold finiteArmIndependentCumulativeGlobalMeanSwitchCount
  apply Finset.sum_nonneg
  intro s _hs
  split <;> norm_num

/-- Enlarging the prefix cannot decrease the global switch count. -/
theorem finiteArmIndependentCumulativeGlobalMeanSwitchCount_mono {K : Nat}
    (armLaw : Nat -> Fin K -> Measure Rat) {t u : Nat} (htu : t <= u) :
    finiteArmIndependentCumulativeGlobalMeanSwitchCount armLaw t <=
      finiteArmIndependentCumulativeGlobalMeanSwitchCount armLaw u := by
  classical
  unfold finiteArmIndependentCumulativeGlobalMeanSwitchCount
  apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono htu)
  intro s _hs _hnot
  split <;> norm_num

/-- The fixed-comparator mean-deviation budget at the global prefix envelope
is bounded by the terminal count times horizon mass and suboptimal-arm
cardinality. -/
theorem finiteArmIndependentMeanDeviationBudget_globalMeanSwitchCount_le
    {K : Nat} (model : FiniteBanditModel K)
    (armLaw : Nat -> Fin K -> Measure Rat) (horizon : Nat) :
    finiteArmIndependentMeanDeviationBudget model horizon
        (fun t _ =>
          finiteArmIndependentCumulativeGlobalMeanSwitchCount armLaw t) <=
      2 *
        (((Finset.univ : Finset (Fin K)).erase model.bestArm).card : Real) *
        (((horizon + 1 : Nat) : Real)) *
        finiteArmIndependentCumulativeGlobalMeanSwitchCount
          armLaw horizon := by
  classical
  rw [finiteArmIndependentMeanDeviationBudget_eq]
  let actions := (Finset.univ : Finset (Fin K)).erase model.bestArm
  let terminalCount :=
    finiteArmIndependentCumulativeGlobalMeanSwitchCount
      armLaw horizon
  change
    (Finset.range (horizon + 1)).sum (fun t =>
      actions.sum (fun _ =>
        finiteArmIndependentCumulativeGlobalMeanSwitchCount armLaw t +
          finiteArmIndependentCumulativeGlobalMeanSwitchCount armLaw t)) <=
      2 * (actions.card : Real) * (((horizon + 1 : Nat) : Real)) *
        terminalCount
  calc
    _ <= (Finset.range (horizon + 1)).sum (fun _ =>
        (actions.card : Real) * (2 * terminalCount)) := by
      apply Finset.sum_le_sum
      intro t ht
      have ht_le : t <= horizon := by
        have ht_lt := Finset.mem_range.mp ht
        omega
      have hcount :=
        finiteArmIndependentCumulativeGlobalMeanSwitchCount_mono
          armLaw ht_le
      have hinner :=
        Finset.sum_le_card_nsmul actions
          (fun _ =>
            finiteArmIndependentCumulativeGlobalMeanSwitchCount armLaw t +
              finiteArmIndependentCumulativeGlobalMeanSwitchCount armLaw t)
          (2 * terminalCount)
          (fun _ _ => by
            linarith)
      simpa [nsmul_eq_mul] using hinner
    _ = 2 * (actions.card : Real) * (((horizon + 1 : Nat) : Real)) *
        terminalCount := by
      simp [nsmul_eq_mul]
      ring

/-- The moving-comparator penalty at the global prefix envelope is bounded by
the same terminal-count expression as the fixed-comparator deviation budget.
The erased-arm cardinality makes the bound exactly zero for `Fin 1`. -/
theorem finiteArmIndependentDynamicComparatorPenalty_globalMeanSwitchCount_le
    {K : Nat} (model : FiniteBanditModel K)
    (armLaw : Nat -> Fin K -> Measure Rat) (horizon : Nat) :
    finiteArmIndependentDynamicComparatorPenalty model armLaw horizon
        (fun t _ =>
          finiteArmIndependentCumulativeGlobalMeanSwitchCount armLaw t) <=
      2 *
        (((Finset.univ : Finset (Fin K)).erase model.bestArm).card : Real) *
        (((horizon + 1 : Nat) : Real)) *
        finiteArmIndependentCumulativeGlobalMeanSwitchCount
          armLaw horizon := by
  classical
  let actions := (Finset.univ : Finset (Fin K)).erase model.bestArm
  let terminalCount :=
    finiteArmIndependentCumulativeGlobalMeanSwitchCount
      armLaw horizon
  unfold finiteArmIndependentDynamicComparatorPenalty
  change
    (Finset.range (horizon + 1)).sum (fun t =>
      if finiteArmIndependentBestArmAt model armLaw t = model.bestArm then
        0
      else
        finiteArmIndependentCumulativeGlobalMeanSwitchCount armLaw t +
          finiteArmIndependentCumulativeGlobalMeanSwitchCount armLaw t) <=
      2 * (actions.card : Real) * (((horizon + 1 : Nat) : Real)) *
        terminalCount
  have hterminalNonneg :
      0 <= terminalCount := by
    exact
      finiteArmIndependentCumulativeGlobalMeanSwitchCount_nonneg
        armLaw horizon
  have hsum :=
    Finset.sum_le_card_nsmul (Finset.range (horizon + 1))
      (fun t =>
        if finiteArmIndependentBestArmAt model armLaw t = model.bestArm then
          0
        else
          finiteArmIndependentCumulativeGlobalMeanSwitchCount armLaw t +
            finiteArmIndependentCumulativeGlobalMeanSwitchCount armLaw t)
      (2 * (actions.card : Real) * terminalCount)
      (fun t ht => by
        by_cases hsame :
            finiteArmIndependentBestArmAt model armLaw t = model.bestArm
        · simp only [hsame, if_true]
          positivity
        · simp only [hsame, if_false]
          have ht_le : t <= horizon := by
            have ht_lt := Finset.mem_range.mp ht
            omega
          have hcount :=
            finiteArmIndependentCumulativeGlobalMeanSwitchCount_mono
              armLaw ht_le
          have hselectedMem : finiteArmIndependentBestArmAt model armLaw t ∈
              actions := by
            exact Finset.mem_erase.mpr ⟨hsame, Finset.mem_univ _⟩
          have hcardNat : 1 <= actions.card :=
            Finset.one_le_card.mpr ⟨_, hselectedMem⟩
          have hcard : (1 : Real) <= (actions.card : Real) := by
            exact_mod_cast hcardNat
          nlinarith)
  calc
    _ <= (horizon + 1) •
        (2 * (actions.card : Real) * terminalCount) := by
      simpa only [Finset.card_range] using hsum
    _ = 2 * (actions.card : Real) * (((horizon + 1 : Nat) : Real)) *
        terminalCount := by
      simp [nsmul_eq_mul]
      ring

/-- One terminal global switch count controls both the fixed-comparator
mean-deviation budget and the moving-comparator penalty. -/
theorem finiteArmIndependentGlobalMeanSwitchCount_totalBudget_le
    {K : Nat} (model : FiniteBanditModel K)
    (armLaw : Nat -> Fin K -> Measure Rat) (horizon : Nat) :
    finiteArmIndependentMeanDeviationBudget model horizon
          (fun t _ =>
            finiteArmIndependentCumulativeGlobalMeanSwitchCount armLaw t) +
        finiteArmIndependentDynamicComparatorPenalty model armLaw horizon
          (fun t _ =>
            finiteArmIndependentCumulativeGlobalMeanSwitchCount armLaw t) <=
      4 *
        (((Finset.univ : Finset (Fin K)).erase model.bestArm).card : Real) *
        (((horizon + 1 : Nat) : Real)) *
        finiteArmIndependentCumulativeGlobalMeanSwitchCount
          armLaw horizon := by
  have hfixed :=
    finiteArmIndependentMeanDeviationBudget_globalMeanSwitchCount_le
      model armLaw horizon
  have hdynamic :=
    finiteArmIndependentDynamicComparatorPenalty_globalMeanSwitchCount_le
      model armLaw horizon
  nlinarith

/-- Explicit logarithmic dynamic-regret bound with a single terminal global
population-mean switch count. -/
noncomputable def
    finiteArmIndependentGlobalMeanSwitchCountHorizonCompressedLogDynamicBound
    {K : Nat} (model : FiniteBanditModel K)
    (armLaw : Nat -> Fin K -> Measure Rat) (horizon : Nat) : Real :=
  (1 + Real.log (((horizon + 1 : Nat) : Real))) *
      (1 + 25 * ((Finset.univ : Finset (Fin K)).erase model.bestArm).sum
        (fun arm => 1 / ((model.gap arm : Rat) : Real))) +
    4 * (((Finset.univ : Finset (Fin K)).erase model.bestArm).card : Real) *
      (((horizon + 1 : Nat) : Real)) *
      finiteArmIndependentCumulativeGlobalMeanSwitchCount
        armLaw horizon

@[simp]
theorem
    finiteArmIndependentGlobalMeanSwitchCountHorizonCompressedLogDynamicBound_fin_one
    (model : FiniteBanditModel 1)
    (armLaw : Nat -> Fin 1 -> Measure Rat) (horizon : Nat) :
    finiteArmIndependentGlobalMeanSwitchCountHorizonCompressedLogDynamicBound
        model armLaw horizon =
      1 + Real.log (((horizon + 1 : Nat) : Real)) := by
  have hbest : model.bestArm = 0 := Subsingleton.elim _ _
  simp [
    finiteArmIndependentGlobalMeanSwitchCountHorizonCompressedLogDynamicBound,
    hbest]

/-- Generated expected predictable-environment dynamic regret with all
time-indexed population-mean switch envelopes compressed into the terminal
global count. This is a linear horizon-level compression, not a minimax
switch-rate theorem. -/
theorem integral_sampledScheduledHalfTsallisFiniteArmIndependentGlobalMeanSwitchCountHorizonCompressedDynamicRegret_le_log
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
      finiteArmIndependentGlobalMeanSwitchCountHorizonCompressedLogDynamicBound
        model armLaw horizon := by
  dsimp only
  have hdecomposition :=
    integral_sampledScheduledHalfTsallisFiniteArmIndependentMovingComparatorRewardLawRegret_eq_fixed_add_meanAdvantage
      model armLaw hprob hbound
        (finiteArmIndependentBestArmAt model armLaw) horizon
  dsimp only at hdecomposition
  rw [hdecomposition]
  have hfixed :=
    integral_sampledScheduledHalfTsallisFiniteArmIndependentDriftingMeanRewardLawRegret_le_log
      model armLaw hprob hbound
      (fun t _ =>
        finiteArmIndependentCumulativeGlobalMeanSwitchCount armLaw t)
      (abs_finiteArmIndependentRewardMean_sub_model_le_globalMeanSwitchCount
        model armLaw hprob hbound hinitialMean)
      hgapPos horizon
  dsimp only at hfixed
  have hdynamic :
      (Finset.range (horizon + 1)).sum (fun t =>
          finiteArmIndependentRewardMean armLaw t
              (finiteArmIndependentBestArmAt model armLaw t) -
            finiteArmIndependentRewardMean armLaw t model.bestArm) <=
        finiteArmIndependentDynamicComparatorPenalty model armLaw horizon
          (fun t _ =>
            finiteArmIndependentCumulativeGlobalMeanSwitchCount armLaw t) := by
    unfold finiteArmIndependentDynamicComparatorPenalty
    apply Finset.sum_le_sum
    intro t _ht
    by_cases hsame :
        finiteArmIndependentBestArmAt model armLaw t = model.bestArm
    · simp [hsame]
    · simp only [hsame, if_false]
      exact
        finiteArmIndependentRewardMean_sub_bestArm_le_meanDeviation
          model armLaw
          (fun t _ =>
            finiteArmIndependentCumulativeGlobalMeanSwitchCount armLaw t)
          (abs_finiteArmIndependentRewardMean_sub_model_le_globalMeanSwitchCount
            model armLaw hprob hbound hinitialMean)
          t (finiteArmIndependentBestArmAt model armLaw t)
  have htotal :=
    finiteArmIndependentGlobalMeanSwitchCount_totalBudget_le
      model armLaw horizon
  unfold
    finiteArmIndependentGlobalMeanSwitchCountHorizonCompressedLogDynamicBound
  calc
    _ <=
        ((1 + Real.log (((horizon + 1 : Nat) : Real))) *
            (1 + 25 *
              ((Finset.univ : Finset (Fin K)).erase model.bestArm).sum
                (fun arm => 1 / ((model.gap arm : Rat) : Real))) +
          finiteArmIndependentMeanDeviationBudget model horizon
            (fun t _ =>
              finiteArmIndependentCumulativeGlobalMeanSwitchCount armLaw t)) +
        finiteArmIndependentDynamicComparatorPenalty model armLaw horizon
          (fun t _ =>
            finiteArmIndependentCumulativeGlobalMeanSwitchCount armLaw t) :=
      add_le_add hfixed hdynamic
    _ =
        (1 + Real.log (((horizon + 1 : Nat) : Real))) *
            (1 + 25 *
              ((Finset.univ : Finset (Fin K)).erase model.bestArm).sum
                (fun arm => 1 / ((model.gap arm : Rat) : Real))) +
          (finiteArmIndependentMeanDeviationBudget model horizon
              (fun t _ =>
                finiteArmIndependentCumulativeGlobalMeanSwitchCount armLaw t) +
            finiteArmIndependentDynamicComparatorPenalty model armLaw horizon
              (fun t _ =>
                finiteArmIndependentCumulativeGlobalMeanSwitchCount armLaw t)) := by
      ring
    _ <=
        (1 + Real.log (((horizon + 1 : Nat) : Real))) *
            (1 + 25 *
              ((Finset.univ : Finset (Fin K)).erase model.bestArm).sum
                (fun arm => 1 / ((model.gap arm : Rat) : Real))) +
          4 *
            (((Finset.univ : Finset (Fin K)).erase model.bestArm).card : Real) *
            (((horizon + 1 : Nat) : Real)) *
            finiteArmIndependentCumulativeGlobalMeanSwitchCount
              armLaw horizon :=
      add_le_add (le_refl _) htotal

end Tsallis
end BanditRLProof
