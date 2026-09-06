import BanditRLProof.Exp3BestArm
import BanditRLProof.Exp3MixedSquareBernsteinRealizedAllHorizon

/-!
# Best-arm all-horizon Bernstein mixed-square realized EXP3

This module upgrades the fixed-comparator all-horizon Bernstein mixed-square
tail to the best supported arm in hindsight. The fixed-comparator schedule is
calibrated at `delta / K`; all comparators share the same generated trajectory
measure, so a finite union gives total failure probability at most `delta`.
-/

namespace BanditRLProof.Exp3

open MeasureTheory ProbabilityTheory

universe u v

/-- Best-arm Bernstein mixed-square all-horizon threshold. The underlying
fixed-comparator schedule receives the confidence share `delta / K`. -/
noncomputable def bernsteinSquareBestArmAllHorizonRegretThreshold
    {Action : Type v} (arms : Finset Action) (horizon : Nat)
    (delta : Real) : Real :=
  bernsteinSquareAllHorizonRegretThreshold
    arms horizon (delta / (arms.card : Real))

/-- Generated realized-regret tail against the best supported arm in hindsight
for every positive horizon. The finite comparator union spends `delta / K` on
each arm and therefore has total failure probability at most `delta`. -/
theorem sampledPredictable_allHorizonBernsteinSquareBestArmRealizedRegret_tail
    {Env : Type u} {Action : Type v}
    [MeasurableSpace Env] [StandardBorelSpace Env] [Nonempty Env]
    [MeasurableSpace Action] [MeasurableSingletonClass Action]
    [StandardBorelSpace Action] [Nonempty Action] [DecidableEq Action]
    (prior : Measure Env) [IsProbabilityMeasure prior]
    (arms : Finset Action) (harms : arms.Nonempty)
    (hcard_two : 2 <= arms.card)
    (loss : PredictableLossVector Env Action)
    (horizon : Nat) (hhorizon : 0 < horizon)
    (delta : Real) (hdelta : 0 < delta) (hdelta_le_one : delta <= 1) :
    let deltaArm := delta / (arms.card : Real)
    let gamma := bernsteinSquareClippedExplorationRate
      (arms.card : Real) (horizon : Real) deltaArm
    let eta := bernsteinSquareHighProbabilityLearningRate
      arms gamma horizon deltaArm
    let mu := prior ⊗ₘ sampledImportanceWeightedTrajectoryKernel arms harms
      eta gamma
        (bernsteinSquareClippedExplorationRate_pos
          (arms.card : Real) (horizon : Real) deltaArm
          (by exact_mod_cast hcard_two)
          (by exact_mod_cast hhorizon)).le
        (by
          exact (bernsteinSquareClippedExplorationRate_le_half
            (arms.card : Real) (horizon : Real) deltaArm).trans (by norm_num))
        loss.environment
    mu {sample |
        bernsteinSquareBestArmAllHorizonRegretThreshold
            arms horizon delta <=
          (Finset.range horizon).sum (fun t =>
              sampledTrajectoryRealizedLossAt t sample) -
            sampledPredictableBestArmCumulativeLoss
              arms harms loss horizon sample} <=
      ENNReal.ofReal delta := by
  dsimp only
  classical
  let deltaArm : Real := delta / (arms.card : Real)
  let gamma := bernsteinSquareClippedExplorationRate
    (arms.card : Real) (horizon : Real) deltaArm
  let eta := bernsteinSquareHighProbabilityLearningRate
    arms gamma horizon deltaArm
  let mu := prior ⊗ₘ sampledImportanceWeightedTrajectoryKernel arms harms
    eta gamma
      (bernsteinSquareClippedExplorationRate_pos
        (arms.card : Real) (horizon : Real) deltaArm
        (by exact_mod_cast hcard_two)
        (by exact_mod_cast hhorizon)).le
      (by
        exact (bernsteinSquareClippedExplorationRate_le_half
          (arms.card : Real) (horizon : Real) deltaArm).trans (by norm_num))
      loss.environment
  let threshold :=
    bernsteinSquareBestArmAllHorizonRegretThreshold arms horizon delta
  let realizedLoss := fun sample : Env × ((k : Nat) → Action × Real) =>
    (Finset.range horizon).sum fun t =>
      sampledTrajectoryRealizedLossAt t sample
  let comparatorLoss := fun comparator sample =>
    (Finset.range horizon).sum fun t =>
      predictableLossAt loss t sample comparator
  let armBad := fun comparator =>
    {sample : Env × ((k : Nat) → Action × Real) |
      threshold <= realizedLoss sample - comparatorLoss comparator sample}
  have hcardReal_pos : 0 < (arms.card : Real) := by
    exact_mod_cast Finset.card_pos.mpr harms
  have hdeltaArm_pos : 0 < deltaArm :=
    div_pos hdelta hcardReal_pos
  have hdelta_le_card : delta <= (arms.card : Real) := by
    have hcardReal_one : (1 : Real) <= (arms.card : Real) := by
      exact_mod_cast (show 1 <= arms.card by omega)
    exact hdelta_le_one.trans hcardReal_one
  have hdeltaArm_le_one : deltaArm <= 1 :=
    (div_le_one hcardReal_pos).2 hdelta_le_card
  have htail :
      ∀ comparator ∈ arms,
        mu (armBad comparator) <= ENNReal.ofReal deltaArm := by
    intro comparator hcomparator
    have h :=
      sampledPredictable_allHorizonBernsteinSquareRealizedRegret_tail
        prior arms harms hcard_two loss comparator hcomparator horizon hhorizon
          deltaArm hdeltaArm_pos hdeltaArm_le_one
    dsimp only at h
    simpa [
      mu, armBad, threshold, realizedLoss, comparatorLoss,
      bernsteinSquareBestArmAllHorizonRegretThreshold,
      deltaArm, gamma, eta] using h
  have hevent :
      {sample : Env × ((k : Nat) → Action × Real) |
          threshold <=
            realizedLoss sample -
              sampledPredictableBestArmCumulativeLoss
                arms harms loss horizon sample} =
        ⋃ comparator ∈ arms, armBad comparator := by
    ext sample
    simp only [Set.mem_setOf_eq, Set.mem_iUnion]
    simpa [realizedLoss, comparatorLoss, armBad] using
      (threshold_le_sampledPredictableRealizedLoss_sub_bestArmCumulativeLoss_iff
        arms harms loss horizon sample threshold)
  have hcardENN_ne_zero : (arms.card : ENNReal) ≠ 0 := by
    simp [Finset.card_ne_zero.mpr harms]
  have hcardENN_ne_top : (arms.card : ENNReal) ≠ ⊤ := by simp
  change
    mu {sample |
        threshold <=
          realizedLoss sample -
            sampledPredictableBestArmCumulativeLoss
              arms harms loss horizon sample} <=
      ENNReal.ofReal delta
  rw [hevent]
  calc
    mu (⋃ comparator ∈ arms, armBad comparator) <=
        ∑ comparator ∈ arms, mu (armBad comparator) :=
      measure_biUnion_finset_le arms armBad
    _ <= ∑ _comparator ∈ arms, ENNReal.ofReal deltaArm := by
      exact Finset.sum_le_sum fun comparator hcomparator =>
        htail comparator hcomparator
    _ = (arms.card : ENNReal) * ENNReal.ofReal deltaArm := by
      simp [nsmul_eq_mul]
    _ = ENNReal.ofReal delta := by
      dsimp [deltaArm]
      rw [ENNReal.ofReal_div_of_pos hcardReal_pos]
      simp only [ENNReal.ofReal_natCast]
      exact ENNReal.mul_div_cancel hcardENN_ne_zero hcardENN_ne_top

end BanditRLProof.Exp3
