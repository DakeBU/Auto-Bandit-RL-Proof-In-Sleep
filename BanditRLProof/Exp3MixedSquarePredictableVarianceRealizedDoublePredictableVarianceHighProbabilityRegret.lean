import BanditRLProof.Exp3MixedSquarePredictableVarianceHighProbabilityRegret
import BanditRLProof.Exp3RealizedPredictableVarianceTail

/-!
# Realized EXP3 regret with two pathwise predictable variances

The predictable-regret component retains the mixed-square estimator variance,
while the realized-minus-predictable selected-loss component retains its own
exact predictable variance. This replaces the fixed Hoeffding proxy in the
realized component without changing the existing predictable-regret route.
-/

namespace BanditRLProof.Exp3

open MeasureTheory ProbabilityTheory

universe u v

noncomputable def sampledPredictableDoubleVarianceRealizedHighProbabilityRegretBudget
    {Action : Type v} [DecidableEq Action]
    (arms : Finset Action) (eta gamma : Real) (horizon : Nat)
    (mixedVarianceBudget realizedVarianceBudget
      deltaSquare deltaConfidence deltaRealized : Real) : Real :=
  sampledPredictableVarianceSquareHighProbabilityRegretBudget arms eta gamma
      horizon mixedVarianceBudget deltaSquare deltaConfidence +
    sampledRealizedPredictableVarianceRadius
      realizedVarianceBudget deltaRealized

/-- Joint realized-regret tail on simultaneous pathwise budgets for the
mixed-square and selected-loss predictable variances. -/
theorem sampledPredictable_doublePredictableVarianceRealizedHighProbabilityRegret_tail_joint
    {Env : Type u} {Action : Type v}
    [MeasurableSpace Env] [StandardBorelSpace Env] [Nonempty Env]
    [MeasurableSpace Action] [MeasurableSingletonClass Action]
    [StandardBorelSpace Action] [Nonempty Action] [DecidableEq Action]
    (prior : Measure Env) [IsProbabilityMeasure prior]
    (arms : Finset Action) (harms : arms.Nonempty)
    (eta gamma : Real) (heta : 0 < eta)
    (hgamma_pos : 0 < gamma) (hgamma_lt_one : gamma < 1)
    (loss : PredictableLossVector Env Action)
    (comparator : Action) (hcomparator : comparator ∈ arms)
    (horizon : Nat)
    (mixedVarianceBudget realizedVarianceBudget
      deltaSquare deltaConfidence deltaRealized : Real)
    (hmixedVarianceBudget : 0 < mixedVarianceBudget)
    (hrealizedVarianceBudget : 0 < realizedVarianceBudget)
    (hdeltaSquare : 0 < deltaSquare)
    (hdeltaConfidence : 0 < deltaConfidence)
    (hdeltaRealized : 0 < deltaRealized) :
    let mu := prior ⊗ₘ sampledImportanceWeightedTrajectoryKernel arms harms
      eta gamma hgamma_pos.le hgamma_lt_one.le loss.environment
    mu {sample |
        sampledPredictableDoubleVarianceRealizedHighProbabilityRegretBudget
            arms eta gamma horizon mixedVarianceBudget realizedVarianceBudget
              deltaSquare deltaConfidence deltaRealized ≤
          (Finset.range horizon).sum (fun t =>
              sampledTrajectoryRealizedLossAt t sample) -
            (Finset.range horizon).sum (fun t =>
              predictableLossAt loss t sample comparator) ∧
        (Finset.range horizon).sum (fun i =>
          sampledTrajectoryPredictableMixedSquaredVarianceAt
            arms eta gamma loss i sample) ≤ mixedVarianceBudget ∧
        (Finset.range horizon).sum (fun i =>
          sampledTrajectoryPredictableRealizedVarianceAt
            arms eta gamma loss i sample) ≤ realizedVarianceBudget} ≤
      ((ENNReal.ofReal deltaSquare + ENNReal.ofReal deltaConfidence) +
        ENNReal.ofReal deltaConfidence) + ENNReal.ofReal deltaRealized := by
  dsimp only
  let mu := prior ⊗ₘ sampledImportanceWeightedTrajectoryKernel arms harms
    eta gamma hgamma_pos.le hgamma_lt_one.le loss.environment
  let predictableRegret :=
    fun sample : Env × ((k : Nat) → Action × Real) =>
      (Finset.range horizon).sum (fun t =>
          sampledTrajectoryExploredPredictableLossAt
            arms eta gamma loss t sample) -
        (Finset.range horizon).sum (fun t =>
          predictableLossAt loss t sample comparator)
  let realizedDeviation :=
    fun sample : Env × ((k : Nat) → Action × Real) =>
      (Finset.range horizon).sum (fun t =>
        sampledTrajectoryRealizedDeviationAt arms eta gamma loss t sample)
  let realizedRegret :=
    fun sample : Env × ((k : Nat) → Action × Real) =>
      (Finset.range horizon).sum (fun t =>
          sampledTrajectoryRealizedLossAt t sample) -
        (Finset.range horizon).sum (fun t =>
          predictableLossAt loss t sample comparator)
  let mixedVarianceSum :=
    fun sample : Env × ((k : Nat) → Action × Real) =>
      (Finset.range horizon).sum (fun i =>
        sampledTrajectoryPredictableMixedSquaredVarianceAt
          arms eta gamma loss i sample)
  let realizedVarianceSum :=
    fun sample : Env × ((k : Nat) → Action × Real) =>
      (Finset.range horizon).sum (fun i =>
        sampledTrajectoryPredictableRealizedVarianceAt
          arms eta gamma loss i sample)
  let predictableBudget :=
    sampledPredictableVarianceSquareHighProbabilityRegretBudget arms eta gamma
      horizon mixedVarianceBudget deltaSquare deltaConfidence
  let realizedRadius :=
    sampledRealizedPredictableVarianceRadius
      realizedVarianceBudget deltaRealized
  let predictableBad : Set (Env × ((k : Nat) → Action × Real)) :=
    {sample | predictableBudget ≤ predictableRegret sample}
  let mixedVarianceGood : Set (Env × ((k : Nat) → Action × Real)) :=
    {sample | mixedVarianceSum sample ≤ mixedVarianceBudget}
  let realizedBad : Set (Env × ((k : Nat) → Action × Real)) :=
    {sample | realizedRadius ≤ realizedDeviation sample}
  let realizedVarianceGood : Set (Env × ((k : Nat) → Action × Real)) :=
    {sample | realizedVarianceSum sample ≤ realizedVarianceBudget}
  have hpredictableTail : mu (predictableBad ∩ mixedVarianceGood) ≤
      (ENNReal.ofReal deltaSquare + ENNReal.ofReal deltaConfidence) +
        ENNReal.ofReal deltaConfidence := by
    have h :=
      sampledPredictable_predictableVarianceSquareHighProbabilityRegret_tail_joint
        prior arms harms eta gamma heta hgamma_pos hgamma_lt_one loss comparator
          hcomparator horizon mixedVarianceBudget deltaSquare deltaConfidence
          hmixedVarianceBudget hdeltaSquare hdeltaConfidence
    dsimp only at h
    simpa [mu, predictableBad, mixedVarianceGood, predictableBudget,
      predictableRegret, mixedVarianceSum] using h
  have hrealizedTail : mu (realizedBad ∩ realizedVarianceGood) ≤
      ENNReal.ofReal deltaRealized := by
    have h :=
      sampledPredictableRealizedDeviation_sum_tail_predictableVariance_delta
        prior arms harms eta gamma hgamma_pos hgamma_lt_one.le loss horizon
          realizedVarianceBudget deltaRealized hrealizedVarianceBudget
            hdeltaRealized
    dsimp only at h
    simpa [mu, realizedBad, realizedVarianceGood, realizedRadius,
      realizedDeviation, realizedVarianceSum] using h
  have hdecomp : ∀ sample,
      realizedRegret sample =
        predictableRegret sample + realizedDeviation sample := by
    intro sample
    dsimp [realizedRegret, predictableRegret, realizedDeviation,
      sampledTrajectoryRealizedDeviationAt]
    rw [Finset.sum_sub_distrib]
    ring
  have hsubset :
      {sample |
          predictableBudget + realizedRadius ≤ realizedRegret sample ∧
          mixedVarianceSum sample ≤ mixedVarianceBudget ∧
          realizedVarianceSum sample ≤ realizedVarianceBudget} ⊆
        (predictableBad ∩ mixedVarianceGood) ∪
          (realizedBad ∩ realizedVarianceGood) := by
    intro sample hregret
    by_cases hpredictable : sample ∈ predictableBad
    · exact Or.inl ⟨hpredictable, hregret.2.1⟩
    by_cases hrealized : sample ∈ realizedBad
    · exact Or.inr ⟨hrealized, hregret.2.2⟩
    exfalso
    have hpredictableGood :
        predictableRegret sample < predictableBudget := by
      change ¬ predictableBudget ≤ predictableRegret sample at hpredictable
      exact lt_of_not_ge hpredictable
    have hrealizedGood : realizedDeviation sample < realizedRadius := by
      change ¬ realizedRadius ≤ realizedDeviation sample at hrealized
      exact lt_of_not_ge hrealized
    have hregret' :
        predictableBudget + realizedRadius ≤ realizedRegret sample := hregret.1
    rw [hdecomp sample] at hregret'
    linarith
  calc
    mu {sample |
        sampledPredictableDoubleVarianceRealizedHighProbabilityRegretBudget
            arms eta gamma horizon mixedVarianceBudget realizedVarianceBudget
              deltaSquare deltaConfidence deltaRealized ≤
          (Finset.range horizon).sum (fun t =>
              sampledTrajectoryRealizedLossAt t sample) -
            (Finset.range horizon).sum (fun t =>
              predictableLossAt loss t sample comparator) ∧
        (Finset.range horizon).sum (fun i =>
          sampledTrajectoryPredictableMixedSquaredVarianceAt
            arms eta gamma loss i sample) ≤ mixedVarianceBudget ∧
        (Finset.range horizon).sum (fun i =>
          sampledTrajectoryPredictableRealizedVarianceAt
            arms eta gamma loss i sample) ≤ realizedVarianceBudget} ≤
        mu ((predictableBad ∩ mixedVarianceGood) ∪
          (realizedBad ∩ realizedVarianceGood)) := by
      apply measure_mono
      simpa [sampledPredictableDoubleVarianceRealizedHighProbabilityRegretBudget,
        predictableBudget, realizedRadius, realizedRegret, mixedVarianceSum,
        realizedVarianceSum, mu] using hsubset
    _ ≤ mu (predictableBad ∩ mixedVarianceGood) +
          mu (realizedBad ∩ realizedVarianceGood) :=
      measure_union_le _ _
    _ ≤ ((ENNReal.ofReal deltaSquare + ENNReal.ofReal deltaConfidence) +
          ENNReal.ofReal deltaConfidence) + ENNReal.ofReal deltaRealized :=
      add_le_add hpredictableTail hrealizedTail

end BanditRLProof.Exp3
