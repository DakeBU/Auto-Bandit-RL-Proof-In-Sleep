import BanditRLProof.Exp3MixedSquarePredictableVarianceHighProbabilityRegret
import BanditRLProof.Exp3RealizedConfidence

/-!
# Realized EXP3 regret with random predictable mixed-square variance

This module adds the generated realized-minus-predictable deviation to the
random predictable-variance regret route.  The resulting selected-loss regret
bound preserves the cumulative variance overflow event explicitly.
-/

namespace BanditRLProof.Exp3

open MeasureTheory ProbabilityTheory

universe u v

/-- Realized selected-loss regret budget with a caller-supplied cumulative
predictable mixed-square variance budget. -/
noncomputable def sampledPredictableVarianceSquareRealizedHighProbabilityRegretBudget
    {Action : Type v} [DecidableEq Action]
    (arms : Finset Action) (eta gamma : Real) (horizon : Nat)
    (varianceBudget deltaSquare deltaConfidence deltaRealized : Real) : Real :=
  sampledPredictableVarianceSquareHighProbabilityRegretBudget arms eta gamma
      horizon varianceBudget deltaSquare deltaConfidence +
    sampledPredictableRealizedDeviationConfidenceRadius horizon deltaRealized

/-- Realized selected-loss regret on the event that cumulative predictable
mixed-square variance stays below `varianceBudget`. -/
theorem sampledPredictable_predictableVarianceSquareRealizedHighProbabilityRegret_tail_joint
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
    (horizon : Nat) (hhorizon : 0 < horizon)
    (varianceBudget deltaSquare deltaConfidence deltaRealized : Real)
    (hvarianceBudget : 0 < varianceBudget)
    (hdeltaSquare : 0 < deltaSquare)
    (hdeltaConfidence : 0 < deltaConfidence)
    (hdeltaRealized : 0 < deltaRealized) :
    let mu := prior ⊗ₘ sampledImportanceWeightedTrajectoryKernel arms harms
      eta gamma hgamma_pos.le hgamma_lt_one.le loss.environment
    mu {sample |
        sampledPredictableVarianceSquareRealizedHighProbabilityRegretBudget
            arms eta gamma horizon varianceBudget deltaSquare deltaConfidence
              deltaRealized <=
          (Finset.range horizon).sum (fun t =>
              sampledTrajectoryRealizedLossAt t sample) -
            (Finset.range horizon).sum (fun t =>
              predictableLossAt loss t sample comparator) ∧
        (Finset.range horizon).sum (fun i =>
          sampledTrajectoryPredictableMixedSquaredVarianceAt
            arms eta gamma loss i sample) <= varianceBudget} <=
      ((ENNReal.ofReal deltaSquare + ENNReal.ofReal deltaConfidence) +
        ENNReal.ofReal deltaConfidence) + ENNReal.ofReal deltaRealized := by
  dsimp only
  let mu := prior ⊗ₘ sampledImportanceWeightedTrajectoryKernel arms harms
    eta gamma hgamma_pos.le hgamma_lt_one.le loss.environment
  let predictableRegret :=
    fun sample : Env × ((k : Nat) -> Action × Real) =>
      (Finset.range horizon).sum (fun t =>
          sampledTrajectoryExploredPredictableLossAt
            arms eta gamma loss t sample) -
        (Finset.range horizon).sum (fun t =>
          predictableLossAt loss t sample comparator)
  let realizedDeviation :=
    fun sample : Env × ((k : Nat) -> Action × Real) =>
      (Finset.range horizon).sum (fun t =>
        sampledTrajectoryRealizedDeviationAt arms eta gamma loss t sample)
  let realizedRegret :=
    fun sample : Env × ((k : Nat) -> Action × Real) =>
      (Finset.range horizon).sum (fun t =>
          sampledTrajectoryRealizedLossAt t sample) -
        (Finset.range horizon).sum (fun t =>
          predictableLossAt loss t sample comparator)
  let varianceSum := fun sample : Env × ((k : Nat) -> Action × Real) =>
    (Finset.range horizon).sum (fun i =>
      sampledTrajectoryPredictableMixedSquaredVarianceAt
        arms eta gamma loss i sample)
  let predictableBudget :=
    sampledPredictableVarianceSquareHighProbabilityRegretBudget arms eta gamma
      horizon varianceBudget deltaSquare deltaConfidence
  let realizedRadius :=
    sampledPredictableRealizedDeviationConfidenceRadius horizon deltaRealized
  let predictableBad : Set (Env × ((k : Nat) -> Action × Real)) :=
    {sample | predictableBudget <= predictableRegret sample}
  let varianceGood : Set (Env × ((k : Nat) -> Action × Real)) :=
    {sample | varianceSum sample <= varianceBudget}
  let realizedBad : Set (Env × ((k : Nat) -> Action × Real)) :=
    {sample | realizedRadius <= realizedDeviation sample}
  have hpredictableTail : mu (predictableBad ∩ varianceGood) <=
      (ENNReal.ofReal deltaSquare + ENNReal.ofReal deltaConfidence) +
        ENNReal.ofReal deltaConfidence := by
    have h :=
      sampledPredictable_predictableVarianceSquareHighProbabilityRegret_tail_joint
        prior arms harms eta gamma heta hgamma_pos hgamma_lt_one loss comparator
          hcomparator horizon varianceBudget deltaSquare deltaConfidence
          hvarianceBudget hdeltaSquare hdeltaConfidence
    dsimp only at h
    simpa [mu, predictableBad, varianceGood, predictableBudget,
      predictableRegret, varianceSum] using h
  have hrealizedTail : mu realizedBad <= ENNReal.ofReal deltaRealized := by
    have h := sampledPredictableRealizedDeviation_sum_tail_delta
      prior arms harms eta gamma hgamma_pos.le hgamma_lt_one.le loss horizon
        hhorizon deltaRealized hdeltaRealized
    dsimp only at h
    simpa [mu, realizedBad, realizedRadius, realizedDeviation] using h
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
          predictableBudget + realizedRadius <= realizedRegret sample ∧
          varianceSum sample <= varianceBudget} ⊆
        (predictableBad ∩ varianceGood) ∪ realizedBad := by
    intro sample hregret
    by_cases hpredictable : sample ∈ predictableBad
    · exact Or.inl ⟨hpredictable, hregret.2⟩
    by_cases hrealized : sample ∈ realizedBad
    · exact Or.inr hrealized
    exfalso
    have hpredictableGood :
        predictableRegret sample < predictableBudget := by
      change ¬ predictableBudget <= predictableRegret sample at hpredictable
      exact lt_of_not_ge hpredictable
    have hrealizedGood : realizedDeviation sample < realizedRadius := by
      change ¬ realizedRadius <= realizedDeviation sample at hrealized
      exact lt_of_not_ge hrealized
    have hregret' :
        predictableBudget + realizedRadius <= realizedRegret sample := hregret.1
    rw [hdecomp sample] at hregret'
    linarith
  calc
    mu {sample |
        sampledPredictableVarianceSquareRealizedHighProbabilityRegretBudget
            arms eta gamma horizon varianceBudget deltaSquare deltaConfidence
              deltaRealized <=
          (Finset.range horizon).sum (fun t =>
              sampledTrajectoryRealizedLossAt t sample) -
            (Finset.range horizon).sum (fun t =>
              predictableLossAt loss t sample comparator) ∧
        (Finset.range horizon).sum (fun i =>
          sampledTrajectoryPredictableMixedSquaredVarianceAt
            arms eta gamma loss i sample) <= varianceBudget} <=
        mu ((predictableBad ∩ varianceGood) ∪ realizedBad) := by
      apply measure_mono
      simpa [sampledPredictableVarianceSquareRealizedHighProbabilityRegretBudget,
        predictableBudget, realizedRadius, realizedRegret, varianceSum, mu]
        using hsubset
    _ <= mu (predictableBad ∩ varianceGood) + mu realizedBad :=
      measure_union_le _ _
    _ <= ((ENNReal.ofReal deltaSquare + ENNReal.ofReal deltaConfidence) +
          ENNReal.ofReal deltaConfidence) + ENNReal.ofReal deltaRealized :=
      add_le_add hpredictableTail hrealizedTail

/-- Unconditional realized selected-loss regret with the cumulative
predictable-variance overflow probability left explicit. -/
theorem sampledPredictable_predictableVarianceSquareRealizedHighProbabilityRegret_tail
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
    (horizon : Nat) (hhorizon : 0 < horizon)
    (varianceBudget deltaSquare deltaConfidence deltaRealized : Real)
    (hvarianceBudget : 0 < varianceBudget)
    (hdeltaSquare : 0 < deltaSquare)
    (hdeltaConfidence : 0 < deltaConfidence)
    (hdeltaRealized : 0 < deltaRealized) :
    let mu := prior ⊗ₘ sampledImportanceWeightedTrajectoryKernel arms harms
      eta gamma hgamma_pos.le hgamma_lt_one.le loss.environment
    mu {sample |
        sampledPredictableVarianceSquareRealizedHighProbabilityRegretBudget
            arms eta gamma horizon varianceBudget deltaSquare deltaConfidence
              deltaRealized <=
          (Finset.range horizon).sum (fun t =>
              sampledTrajectoryRealizedLossAt t sample) -
            (Finset.range horizon).sum (fun t =>
              predictableLossAt loss t sample comparator)} <=
      (((ENNReal.ofReal deltaSquare + ENNReal.ofReal deltaConfidence) +
        ENNReal.ofReal deltaConfidence) + ENNReal.ofReal deltaRealized) +
        mu {sample |
          varianceBudget < (Finset.range horizon).sum (fun i =>
            sampledTrajectoryPredictableMixedSquaredVarianceAt
              arms eta gamma loss i sample)} := by
  dsimp only
  let mu := prior ⊗ₘ sampledImportanceWeightedTrajectoryKernel arms harms
    eta gamma hgamma_pos.le hgamma_lt_one.le loss.environment
  let realizedBad : Set (Env × ((k : Nat) -> Action × Real)) :=
    {sample |
      sampledPredictableVarianceSquareRealizedHighProbabilityRegretBudget
          arms eta gamma horizon varianceBudget deltaSquare deltaConfidence
            deltaRealized <=
        (Finset.range horizon).sum (fun t =>
            sampledTrajectoryRealizedLossAt t sample) -
          (Finset.range horizon).sum (fun t =>
            predictableLossAt loss t sample comparator)}
  let varianceSum := fun sample : Env × ((k : Nat) -> Action × Real) =>
    (Finset.range horizon).sum (fun i =>
      sampledTrajectoryPredictableMixedSquaredVarianceAt
        arms eta gamma loss i sample)
  let varianceGood : Set (Env × ((k : Nat) -> Action × Real)) :=
    {sample | varianceSum sample <= varianceBudget}
  let varianceBad : Set (Env × ((k : Nat) -> Action × Real)) :=
    {sample | varianceBudget < varianceSum sample}
  have hjoint :=
    sampledPredictable_predictableVarianceSquareRealizedHighProbabilityRegret_tail_joint
      prior arms harms eta gamma heta hgamma_pos hgamma_lt_one loss comparator
        hcomparator horizon hhorizon varianceBudget deltaSquare deltaConfidence
        deltaRealized hvarianceBudget hdeltaSquare hdeltaConfidence hdeltaRealized
  dsimp only at hjoint
  have hjoint' : mu (realizedBad ∩ varianceGood) <=
      ((ENNReal.ofReal deltaSquare + ENNReal.ofReal deltaConfidence) +
        ENNReal.ofReal deltaConfidence) + ENNReal.ofReal deltaRealized := by
    simpa [mu, realizedBad, varianceGood, varianceSum] using hjoint
  have hsplit : realizedBad ⊆ (realizedBad ∩ varianceGood) ∪ varianceBad := by
    intro sample hregret
    by_cases hvariance : varianceSum sample <= varianceBudget
    · exact Or.inl ⟨hregret, hvariance⟩
    · exact Or.inr (lt_of_not_ge hvariance)
  calc
    mu realizedBad <= mu ((realizedBad ∩ varianceGood) ∪ varianceBad) :=
      measure_mono hsplit
    _ <= mu (realizedBad ∩ varianceGood) + mu varianceBad :=
      measure_union_le _ _
    _ <= (((ENNReal.ofReal deltaSquare + ENNReal.ofReal deltaConfidence) +
          ENNReal.ofReal deltaConfidence) + ENNReal.ofReal deltaRealized) +
        mu varianceBad := add_le_add hjoint' le_rfl
    _ = (((ENNReal.ofReal deltaSquare + ENNReal.ofReal deltaConfidence) +
          ENNReal.ofReal deltaConfidence) + ENNReal.ofReal deltaRealized) +
        mu {sample |
          varianceBudget < (Finset.range horizon).sum (fun i =>
            sampledTrajectoryPredictableMixedSquaredVarianceAt
              arms eta gamma loss i sample)} := by
      rfl

/-- Total-failure joint-event form with all four confidence events allocated
`delta / 4`. -/
theorem sampledPredictable_predictableVarianceSquareRealizedHighProbabilityRegret_tail_joint_total_delta
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
    (horizon : Nat) (hhorizon : 0 < horizon)
    (varianceBudget delta : Real)
    (hvarianceBudget : 0 < varianceBudget) (hdelta : 0 < delta) :
    let mu := prior ⊗ₘ sampledImportanceWeightedTrajectoryKernel arms harms
      eta gamma hgamma_pos.le hgamma_lt_one.le loss.environment
    mu {sample |
        sampledPredictableVarianceSquareRealizedHighProbabilityRegretBudget
            arms eta gamma horizon varianceBudget (delta / 4) (delta / 4)
              (delta / 4) <=
          (Finset.range horizon).sum (fun t =>
              sampledTrajectoryRealizedLossAt t sample) -
            (Finset.range horizon).sum (fun t =>
              predictableLossAt loss t sample comparator) ∧
        (Finset.range horizon).sum (fun i =>
          sampledTrajectoryPredictableMixedSquaredVarianceAt
            arms eta gamma loss i sample) <= varianceBudget} <=
      ENNReal.ofReal delta := by
  have hquarter_pos : 0 < delta / 4 := div_pos hdelta (by norm_num)
  have h :=
    sampledPredictable_predictableVarianceSquareRealizedHighProbabilityRegret_tail_joint
      prior arms harms eta gamma heta hgamma_pos hgamma_lt_one loss comparator
        hcomparator horizon hhorizon varianceBudget (delta / 4) (delta / 4)
        (delta / 4) hvarianceBudget hquarter_pos hquarter_pos hquarter_pos
  dsimp only at h ⊢
  have hquarter_nonneg : 0 <= delta / 4 := hquarter_pos.le
  have hprob :
      ((ENNReal.ofReal (delta / 4) + ENNReal.ofReal (delta / 4)) +
          ENNReal.ofReal (delta / 4)) + ENNReal.ofReal (delta / 4) =
        ENNReal.ofReal delta := by
    rw [← ENNReal.ofReal_add hquarter_nonneg hquarter_nonneg]
    rw [← ENNReal.ofReal_add
      (add_nonneg hquarter_nonneg hquarter_nonneg) hquarter_nonneg]
    rw [← ENNReal.ofReal_add
      (add_nonneg (add_nonneg hquarter_nonneg hquarter_nonneg)
        hquarter_nonneg) hquarter_nonneg]
    congr 1
    ring
  exact h.trans_eq hprob

/-- Primary residual-variance realized-regret theorem. The four explicit
confidence failures total `delta`; only predictable-variance overflow remains. -/
theorem sampledPredictable_predictableVarianceSquareRealizedHighProbabilityRegret_tail_total_delta
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
    (horizon : Nat) (hhorizon : 0 < horizon)
    (varianceBudget delta : Real)
    (hvarianceBudget : 0 < varianceBudget) (hdelta : 0 < delta) :
    let mu := prior ⊗ₘ sampledImportanceWeightedTrajectoryKernel arms harms
      eta gamma hgamma_pos.le hgamma_lt_one.le loss.environment
    mu {sample |
        sampledPredictableVarianceSquareRealizedHighProbabilityRegretBudget
            arms eta gamma horizon varianceBudget (delta / 4) (delta / 4)
              (delta / 4) <=
          (Finset.range horizon).sum (fun t =>
              sampledTrajectoryRealizedLossAt t sample) -
            (Finset.range horizon).sum (fun t =>
              predictableLossAt loss t sample comparator)} <=
      ENNReal.ofReal delta +
        mu {sample |
          varianceBudget < (Finset.range horizon).sum (fun i =>
            sampledTrajectoryPredictableMixedSquaredVarianceAt
              arms eta gamma loss i sample)} := by
  have hquarter_pos : 0 < delta / 4 := div_pos hdelta (by norm_num)
  have h :=
    sampledPredictable_predictableVarianceSquareRealizedHighProbabilityRegret_tail
      prior arms harms eta gamma heta hgamma_pos hgamma_lt_one loss comparator
        hcomparator horizon hhorizon varianceBudget (delta / 4) (delta / 4)
        (delta / 4) hvarianceBudget hquarter_pos hquarter_pos hquarter_pos
  dsimp only at h ⊢
  have hquarter_nonneg : 0 <= delta / 4 := hquarter_pos.le
  have hprob :
      ((ENNReal.ofReal (delta / 4) + ENNReal.ofReal (delta / 4)) +
          ENNReal.ofReal (delta / 4)) + ENNReal.ofReal (delta / 4) =
        ENNReal.ofReal delta := by
    rw [← ENNReal.ofReal_add hquarter_nonneg hquarter_nonneg]
    rw [← ENNReal.ofReal_add
      (add_nonneg hquarter_nonneg hquarter_nonneg) hquarter_nonneg]
    rw [← ENNReal.ofReal_add
      (add_nonneg (add_nonneg hquarter_nonneg hquarter_nonneg)
        hquarter_nonneg) hquarter_nonneg]
    congr 1
    ring
  rw [hprob] at h
  exact h

end BanditRLProof.Exp3
