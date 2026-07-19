import BanditRLProof.Exp3MixedSquarePredictableVarianceSmallLossRealizedMarkovHighProbabilityRegret
import BanditRLProof.Exp3RealizedPredictableVarianceTail

/-!
# Small-loss EXP3 regret with two predictable-variance budgets

The predictable-regret component uses the armwise loss-mass budget and the
mixed-square predictable variance. The realized-minus-predictable component
uses its exact selected-loss predictable variance. An explicit bad set is
retained so probabilistic sparsity can discharge both pathwise budgets without
charging the same failure event more than once.
-/

namespace BanditRLProof.Exp3

open MeasureTheory ProbabilityTheory

universe u v

noncomputable def sampledPredictableVarianceSquareSmallLossDoubleVarianceRealizedHighProbabilityRegretBudget
    {Action : Type v} [DecidableEq Action]
    (arms : Finset Action) (eta gamma : Real) (horizon : Nat)
    (lossMassBudget mixedVarianceBudget realizedVarianceBudget
      deltaSquare deltaConfidence deltaRealized : Real) : Real :=
  sampledPredictableVarianceSquareSmallLossHighProbabilityRegretBudget
      arms eta gamma horizon lossMassBudget mixedVarianceBudget
        deltaSquare deltaConfidence +
    sampledRealizedPredictableVarianceRadius
      realizedVarianceBudget deltaRealized

/-- Joint realized-regret tail away from an explicit loss-mass bad set, with
simultaneous mixed-square and selected-loss predictable-variance budgets. -/
theorem sampledPredictable_smallLossDoublePredictableVarianceRealizedHighProbabilityRegret_tail_joint_off_bad_of_lossMassSum_le_or_mem
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
    (lossMassBudget mixedVarianceBudget realizedVarianceBudget
      deltaSquare deltaConfidence deltaRealized : Real)
    (hmixedVarianceBudget : 0 < mixedVarianceBudget)
    (hrealizedVarianceBudget : 0 < realizedVarianceBudget)
    (hdeltaSquare : 0 < deltaSquare)
    (hdeltaConfidence : 0 < deltaConfidence)
    (hdeltaRealized : 0 < deltaRealized)
    (bad : Set (Env × ((k : Nat) → Action × Real)))
    (hmass : ∀ᵐ sample ∂prior ⊗ₘ
        sampledImportanceWeightedTrajectoryKernel arms harms
          eta gamma hgamma_pos.le hgamma_lt_one.le loss.environment,
      sampledPredictableLossMassSum arms loss horizon sample ≤
        lossMassBudget ∨ sample ∈ bad) :
    let mu := prior ⊗ₘ sampledImportanceWeightedTrajectoryKernel arms harms
      eta gamma hgamma_pos.le hgamma_lt_one.le loss.environment
    mu ({sample |
        sampledPredictableVarianceSquareSmallLossDoubleVarianceRealizedHighProbabilityRegretBudget
            arms eta gamma horizon lossMassBudget mixedVarianceBudget
              realizedVarianceBudget deltaSquare deltaConfidence
                deltaRealized ≤
          (Finset.range horizon).sum (fun t =>
              sampledTrajectoryRealizedLossAt t sample) -
            (Finset.range horizon).sum (fun t =>
              predictableLossAt loss t sample comparator) ∧
        (Finset.range horizon).sum (fun i =>
          sampledTrajectoryPredictableMixedSquaredVarianceAt
            arms eta gamma loss i sample) ≤ mixedVarianceBudget ∧
        (Finset.range horizon).sum (fun i =>
          sampledTrajectoryPredictableRealizedVarianceAt
            arms eta gamma loss i sample) ≤ realizedVarianceBudget} \ bad) ≤
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
    sampledPredictableVarianceSquareSmallLossHighProbabilityRegretBudget
      arms eta gamma horizon lossMassBudget mixedVarianceBudget
        deltaSquare deltaConfidence
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
  have hpredictableTail :
      mu ((predictableBad ∩ mixedVarianceGood) \ bad) ≤
        (ENNReal.ofReal deltaSquare + ENNReal.ofReal deltaConfidence) +
          ENNReal.ofReal deltaConfidence := by
    have h :=
      sampledPredictable_predictableVarianceSquareSmallLossHighProbabilityRegret_tail_joint_off_bad_of_lossMassSum_le_or_mem
        prior arms harms eta gamma heta hgamma_pos hgamma_lt_one loss comparator
          hcomparator horizon lossMassBudget mixedVarianceBudget deltaSquare
          deltaConfidence hmixedVarianceBudget hdeltaSquare hdeltaConfidence
          bad hmass
    dsimp only at h
    simpa [mu, predictableBad, mixedVarianceGood, predictableBudget,
      predictableRegret, mixedVarianceSum] using h
  have hrealizedTail :
      mu (realizedBad ∩ realizedVarianceGood) ≤
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
      ({sample |
          predictableBudget + realizedRadius ≤ realizedRegret sample ∧
          mixedVarianceSum sample ≤ mixedVarianceBudget ∧
          realizedVarianceSum sample ≤ realizedVarianceBudget} \ bad) ⊆
        ((predictableBad ∩ mixedVarianceGood) \ bad) ∪
          (realizedBad ∩ realizedVarianceGood) := by
    intro sample hregret
    by_cases hpredictable : sample ∈ predictableBad
    · exact Or.inl ⟨⟨hpredictable, hregret.1.2.1⟩, hregret.2⟩
    by_cases hrealized : sample ∈ realizedBad
    · exact Or.inr ⟨hrealized, hregret.1.2.2⟩
    exfalso
    have hpredictableGood :
        predictableRegret sample < predictableBudget := by
      change ¬ predictableBudget ≤ predictableRegret sample at hpredictable
      exact lt_of_not_ge hpredictable
    have hrealizedGood : realizedDeviation sample < realizedRadius := by
      change ¬ realizedRadius ≤ realizedDeviation sample at hrealized
      exact lt_of_not_ge hrealized
    have hregret' :
        predictableBudget + realizedRadius ≤ realizedRegret sample :=
      hregret.1.1
    rw [hdecomp sample] at hregret'
    linarith
  calc
    mu ({sample |
        sampledPredictableVarianceSquareSmallLossDoubleVarianceRealizedHighProbabilityRegretBudget
            arms eta gamma horizon lossMassBudget mixedVarianceBudget
              realizedVarianceBudget deltaSquare deltaConfidence
                deltaRealized ≤
          (Finset.range horizon).sum (fun t =>
              sampledTrajectoryRealizedLossAt t sample) -
            (Finset.range horizon).sum (fun t =>
              predictableLossAt loss t sample comparator) ∧
        (Finset.range horizon).sum (fun i =>
          sampledTrajectoryPredictableMixedSquaredVarianceAt
            arms eta gamma loss i sample) ≤ mixedVarianceBudget ∧
        (Finset.range horizon).sum (fun i =>
          sampledTrajectoryPredictableRealizedVarianceAt
            arms eta gamma loss i sample) ≤ realizedVarianceBudget} \ bad) ≤
      mu (((predictableBad ∩ mixedVarianceGood) \ bad) ∪
        (realizedBad ∩ realizedVarianceGood)) := by
          apply measure_mono
          simpa [
            sampledPredictableVarianceSquareSmallLossDoubleVarianceRealizedHighProbabilityRegretBudget,
            predictableBudget, realizedRadius, realizedRegret, mixedVarianceSum,
            realizedVarianceSum, mu] using hsubset
    _ ≤ mu ((predictableBad ∩ mixedVarianceGood) \ bad) +
          mu (realizedBad ∩ realizedVarianceGood) :=
      measure_union_le _ _
    _ ≤ ((ENNReal.ofReal deltaSquare + ENNReal.ofReal deltaConfidence) +
          ENNReal.ofReal deltaConfidence) + ENNReal.ofReal deltaRealized :=
      add_le_add hpredictableTail hrealizedTail

end BanditRLProof.Exp3
