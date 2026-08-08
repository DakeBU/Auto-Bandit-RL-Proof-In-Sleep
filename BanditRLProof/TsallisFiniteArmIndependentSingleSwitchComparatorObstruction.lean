import BanditRLProof.TsallisFiniteArmIndependentGlobalMeanSwitchCountCompressedDynamicRegret

/-!
# Single-switch obstruction for the current dynamic-comparator route

This module gives an exact two-arm, one-switch calculation. The global
population-mean switch count is one, while the moving-comparator mean
advantage charged by the current fixed-plus-advantage decomposition grows
linearly with the horizon. This is a proof-route obstruction, not a dynamic
regret lower bound.
-/

open scoped ENNReal NNReal Topology ProbabilityTheory
open MeasureTheory ProbabilityTheory Set Filter Finset

namespace BanditRLProof
namespace Tsallis

/-- Baseline two-arm model used by the single-switch obstruction. -/
def finiteArmIndependentSingleSwitchObstructionModel :
    FiniteBanditModel 2 where
  hK := by decide
  mean := fun arm => if arm = 0 then 1 / 2 else 1 / 4

theorem finiteArmIndependentSingleSwitchObstructionModel_bestArm :
    finiteArmIndependentSingleSwitchObstructionModel.bestArm = 0 := by
  norm_num [FiniteBanditModel.bestArm,
    finiteArmIndependentSingleSwitchObstructionModel, List.finRange]

/-- Arm zero stays at mean `1/2`; arm one moves from `1/4` at round zero to
`3/4` forever after round zero. -/
noncomputable def finiteArmIndependentSingleSwitchObstructionLaw
    (t : Nat) (arm : Fin 2) : Measure Rat :=
  if arm = 0 then
    Measure.dirac (1 / 2 : Rat)
  else if t = 0 then
    Measure.dirac (1 / 4 : Rat)
  else
    Measure.dirac (3 / 4 : Rat)

theorem finiteArmIndependentSingleSwitchObstructionLaw_isProbabilityMeasure
    (t : Nat) (arm : Fin 2) :
    IsProbabilityMeasure
      (finiteArmIndependentSingleSwitchObstructionLaw t arm) := by
  unfold finiteArmIndependentSingleSwitchObstructionLaw
  split_ifs <;> infer_instance

theorem finiteArmIndependentSingleSwitchObstructionLaw_mem_Icc_ae
    (t : Nat) (arm : Fin 2) :
    ∀ᵐ reward ∂finiteArmIndependentSingleSwitchObstructionLaw t arm,
      ((reward : Rat) : Real) ∈ Set.Icc (0 : Real) 1 := by
  fin_cases arm <;>
    by_cases ht : t = 0 <;>
    simp [finiteArmIndependentSingleSwitchObstructionLaw, ht] <;>
    norm_num

@[simp]
theorem finiteArmIndependentSingleSwitchObstructionMean_zero
    (t : Nat) :
    finiteArmIndependentRewardMean
        finiteArmIndependentSingleSwitchObstructionLaw t 0 =
      1 / 2 := by
  norm_num [finiteArmIndependentRewardMean,
    finiteArmIndependentSingleSwitchObstructionLaw]

@[simp]
theorem finiteArmIndependentSingleSwitchObstructionMean_one_zero :
    finiteArmIndependentRewardMean
        finiteArmIndependentSingleSwitchObstructionLaw 0 1 =
      1 / 4 := by
  norm_num [finiteArmIndependentRewardMean,
    finiteArmIndependentSingleSwitchObstructionLaw]

@[simp]
theorem finiteArmIndependentSingleSwitchObstructionMean_one_succ
    (t : Nat) :
    finiteArmIndependentRewardMean
        finiteArmIndependentSingleSwitchObstructionLaw (t + 1) 1 =
      3 / 4 := by
  norm_num [finiteArmIndependentRewardMean,
    finiteArmIndependentSingleSwitchObstructionLaw]

theorem finiteArmIndependentSingleSwitchObstructionInitialMean
    (arm : Fin 2) :
    finiteArmIndependentRewardMean
        finiteArmIndependentSingleSwitchObstructionLaw 0 arm =
      ((finiteArmIndependentSingleSwitchObstructionModel.mean arm : Rat) :
        Real) := by
  fin_cases arm <;>
    norm_num [finiteArmIndependentSingleSwitchObstructionModel]

theorem finiteArmIndependentSingleSwitchObstructionGap_pos
    (arm : Fin 2)
    (harm :
      arm ≠ finiteArmIndependentSingleSwitchObstructionModel.bestArm) :
    0 <
      ((finiteArmIndependentSingleSwitchObstructionModel.gap arm : Rat) :
        Real) := by
  rw [finiteArmIndependentSingleSwitchObstructionModel_bestArm] at harm
  fin_cases arm
  · exact (harm rfl).elim
  · rw [FiniteBanditModel.gap, FiniteBanditModel.bestMean,
      finiteArmIndependentSingleSwitchObstructionModel_bestArm]
    norm_num [finiteArmIndependentSingleSwitchObstructionModel]

theorem finiteArmIndependentSingleSwitchObstructionGap_le_one
    (arm : Fin 2)
    (harm :
      arm ≠ finiteArmIndependentSingleSwitchObstructionModel.bestArm) :
    ((finiteArmIndependentSingleSwitchObstructionModel.gap arm : Rat) :
        Real) <= 1 := by
  rw [finiteArmIndependentSingleSwitchObstructionModel_bestArm] at harm
  fin_cases arm
  · exact (harm rfl).elim
  · rw [FiniteBanditModel.gap, FiniteBanditModel.bestMean,
      finiteArmIndependentSingleSwitchObstructionModel_bestArm]
    norm_num [finiteArmIndependentSingleSwitchObstructionModel]

@[simp]
theorem finiteArmIndependentSingleSwitchObstructionBestArmAt_zero :
    finiteArmIndependentBestArmAt
        finiteArmIndependentSingleSwitchObstructionModel
        finiteArmIndependentSingleSwitchObstructionLaw 0 = 0 := by
  have hmax :=
    finiteArmIndependentRewardMean_le_bestArmAt
      finiteArmIndependentSingleSwitchObstructionModel
      finiteArmIndependentSingleSwitchObstructionLaw 0 (0 : Fin 2)
  by_contra hselected
  have hone :
      finiteArmIndependentBestArmAt
          finiteArmIndependentSingleSwitchObstructionModel
          finiteArmIndependentSingleSwitchObstructionLaw 0 = 1 := by
    apply Fin.ext
    have hneVal :
        (finiteArmIndependentBestArmAt
            finiteArmIndependentSingleSwitchObstructionModel
            finiteArmIndependentSingleSwitchObstructionLaw 0).val ≠ 0 := by
      intro hzero
      apply hselected
      apply Fin.ext
      simpa using hzero
    have hlt :=
      (finiteArmIndependentBestArmAt
        finiteArmIndependentSingleSwitchObstructionModel
        finiteArmIndependentSingleSwitchObstructionLaw 0).isLt
    omega
  rw [hone] at hmax
  norm_num at hmax

@[simp]
theorem finiteArmIndependentSingleSwitchObstructionBestArmAt_succ
    (t : Nat) :
    finiteArmIndependentBestArmAt
        finiteArmIndependentSingleSwitchObstructionModel
        finiteArmIndependentSingleSwitchObstructionLaw (t + 1) = 1 := by
  have hmax :=
    finiteArmIndependentRewardMean_le_bestArmAt
      finiteArmIndependentSingleSwitchObstructionModel
      finiteArmIndependentSingleSwitchObstructionLaw (t + 1) (1 : Fin 2)
  by_contra hselected
  have hzero :
      finiteArmIndependentBestArmAt
          finiteArmIndependentSingleSwitchObstructionModel
          finiteArmIndependentSingleSwitchObstructionLaw (t + 1) = 0 := by
    apply Fin.ext
    have hneVal :
        (finiteArmIndependentBestArmAt
            finiteArmIndependentSingleSwitchObstructionModel
            finiteArmIndependentSingleSwitchObstructionLaw (t + 1)).val ≠
          1 := by
      intro hone
      apply hselected
      apply Fin.ext
      simpa using hone
    have hlt :=
      (finiteArmIndependentBestArmAt
        finiteArmIndependentSingleSwitchObstructionModel
        finiteArmIndependentSingleSwitchObstructionLaw (t + 1)).isLt
    omega
  rw [hzero] at hmax
  norm_num at hmax

private theorem finiteArmIndependentSingleSwitchObstructionIndicator
    (s : Nat) :
    (if ∃ arm : Fin 2,
          finiteArmIndependentRewardMean
              finiteArmIndependentSingleSwitchObstructionLaw (s + 1) arm ≠
            finiteArmIndependentRewardMean
              finiteArmIndependentSingleSwitchObstructionLaw s arm then
        (1 : Real)
      else
        0) =
      if s = 0 then 1 else 0 := by
  cases s with
  | zero =>
      have hchange : ∃ arm : Fin 2,
          finiteArmIndependentRewardMean
              finiteArmIndependentSingleSwitchObstructionLaw (0 + 1) arm ≠
            finiteArmIndependentRewardMean
              finiteArmIndependentSingleSwitchObstructionLaw 0 arm := by
        refine ⟨1, ?_⟩
        norm_num
      simp [hchange]
  | succ s =>
      have hsame : ¬ ∃ arm : Fin 2,
          finiteArmIndependentRewardMean
              finiteArmIndependentSingleSwitchObstructionLaw
                (Nat.succ s + 1) arm ≠
            finiteArmIndependentRewardMean
              finiteArmIndependentSingleSwitchObstructionLaw
                (Nat.succ s) arm := by
        push Not
        intro arm
        fin_cases arm <;> simp [Nat.succ_eq_add_one]
      simp [hsame]

/-- Every positive prefix contains exactly the one change at `0 -> 1`. -/
@[simp]
theorem finiteArmIndependentSingleSwitchObstructionGlobalCount_succ
    (t : Nat) :
    finiteArmIndependentCumulativeGlobalMeanSwitchCount
        finiteArmIndependentSingleSwitchObstructionLaw (t + 1) = 1 := by
  classical
  unfold finiteArmIndependentCumulativeGlobalMeanSwitchCount
  simp_rw [finiteArmIndependentSingleSwitchObstructionIndicator]
  simp

/-- Exact actual-mean advantage charged by the moving-comparator
decomposition on the single-switch law. -/
noncomputable def finiteArmIndependentSingleSwitchComparatorAdvantage
    (horizon : Nat) : Real :=
  (Finset.range (horizon + 1)).sum (fun t =>
    finiteArmIndependentRewardMean
        finiteArmIndependentSingleSwitchObstructionLaw t
        (finiteArmIndependentBestArmAt
          finiteArmIndependentSingleSwitchObstructionModel
          finiteArmIndependentSingleSwitchObstructionLaw t) -
      finiteArmIndependentRewardMean
        finiteArmIndependentSingleSwitchObstructionLaw t
        finiteArmIndependentSingleSwitchObstructionModel.bestArm)

@[simp]
theorem finiteArmIndependentSingleSwitchComparatorAdvantage_zero :
    finiteArmIndependentSingleSwitchComparatorAdvantage 0 = 0 := by
  simp [finiteArmIndependentSingleSwitchComparatorAdvantage,
    finiteArmIndependentSingleSwitchObstructionModel_bestArm]

/-- One permanent switch makes the exact comparator advantage equal to
`horizon / 4`, despite the global switch count being one. -/
theorem finiteArmIndependentSingleSwitchComparatorAdvantage_eq
    (horizon : Nat) :
    finiteArmIndependentSingleSwitchComparatorAdvantage horizon =
      (horizon : Real) / 4 := by
  induction horizon with
  | zero =>
      simp
  | succ horizon ih =>
      unfold finiteArmIndependentSingleSwitchComparatorAdvantage at ih ⊢
      rw [show Nat.succ horizon + 1 = (horizon + 1) + 1 by omega]
      rw [Finset.sum_range_succ]
      rw [ih]
      simp [finiteArmIndependentSingleSwitchObstructionModel_bestArm]
      ring

/-- The current repeated-prefix envelope penalty is exactly `2 * horizon`
on the same one-switch law. -/
theorem finiteArmIndependentSingleSwitchDynamicComparatorPenalty_eq
    (horizon : Nat) :
    finiteArmIndependentDynamicComparatorPenalty
        finiteArmIndependentSingleSwitchObstructionModel
        finiteArmIndependentSingleSwitchObstructionLaw horizon
        (fun t _ =>
          finiteArmIndependentCumulativeGlobalMeanSwitchCount
            finiteArmIndependentSingleSwitchObstructionLaw t) =
      2 * (horizon : Real) := by
  induction horizon with
  | zero =>
      simp [finiteArmIndependentDynamicComparatorPenalty,
        finiteArmIndependentSingleSwitchObstructionModel_bestArm]
  | succ horizon ih =>
      unfold finiteArmIndependentDynamicComparatorPenalty at ih ⊢
      rw [show Nat.succ horizon + 1 = (horizon + 1) + 1 by omega]
      rw [Finset.sum_range_succ]
      rw [ih]
      simp [finiteArmIndependentSingleSwitchObstructionModel_bestArm]
      ring

/-- For every natural coefficient, a one-switch horizon exists where the
exact separately charged comparator advantage exceeds that coefficient
times `sqrt(horizon)`. This rules out obtaining a uniform square-root
switch-rate by bounding this term independently. -/
theorem finiteArmIndependentSingleSwitchComparatorAdvantage_gt_nat_mul_sqrt
    (coefficient : Nat) :
    let horizon := (4 * coefficient + 1) ^ 2
    finiteArmIndependentCumulativeGlobalMeanSwitchCount
        finiteArmIndependentSingleSwitchObstructionLaw horizon = 1 ∧
      (coefficient : Real) * Real.sqrt (horizon : Real) <
        finiteArmIndependentSingleSwitchComparatorAdvantage horizon := by
  dsimp only
  have hpos : 0 < 4 * coefficient + 1 := by omega
  have hcount :=
    finiteArmIndependentSingleSwitchObstructionGlobalCount_succ
      ((4 * coefficient + 1) ^ 2 - 1)
  have hsucc :
      (4 * coefficient + 1) ^ 2 - 1 + 1 =
        (4 * coefficient + 1) ^ 2 := by
    have hsquarePos : 0 < (4 * coefficient + 1) ^ 2 := by positivity
    omega
  rw [hsucc] at hcount
  refine ⟨hcount, ?_⟩
  rw [finiteArmIndependentSingleSwitchComparatorAdvantage_eq]
  have hcast :
      (((4 * coefficient + 1) ^ 2 : Nat) : Real) =
        (((4 * coefficient + 1 : Nat) : Real)) ^ 2 := by
    norm_cast
  rw [hcast, Real.sqrt_sq_eq_abs]
  rw [abs_of_nonneg (by positivity :
    0 <= (((4 * coefficient + 1 : Nat) : Real)))]
  push_cast
  nlinarith

/-- Compiled blocker certificate for the current dynamic-comparator proof
route. It does not assert a regret lower bound: a sharper proof could exploit
cancellation between fixed-comparator regret and comparator advantage. -/
theorem finiteArmIndependentSingleSwitchDynamicComparatorRouteObstruction
    (horizon : Nat) (horizon_pos : 0 < horizon) :
    finiteArmIndependentCumulativeGlobalMeanSwitchCount
          finiteArmIndependentSingleSwitchObstructionLaw horizon = 1 ∧
      finiteArmIndependentSingleSwitchComparatorAdvantage horizon =
        (horizon : Real) / 4 ∧
      finiteArmIndependentDynamicComparatorPenalty
          finiteArmIndependentSingleSwitchObstructionModel
          finiteArmIndependentSingleSwitchObstructionLaw horizon
          (fun t _ =>
            finiteArmIndependentCumulativeGlobalMeanSwitchCount
              finiteArmIndependentSingleSwitchObstructionLaw t) =
        2 * (horizon : Real) := by
  obtain ⟨t, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt horizon_pos)
  exact ⟨by simp,
    finiteArmIndependentSingleSwitchComparatorAdvantage_eq _,
    finiteArmIndependentSingleSwitchDynamicComparatorPenalty_eq _⟩

end Tsallis
end BanditRLProof
