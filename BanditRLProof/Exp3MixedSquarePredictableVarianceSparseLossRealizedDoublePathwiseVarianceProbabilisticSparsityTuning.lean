import BanditRLProof.Exp3MixedSquarePredictableVarianceSparseLossRealizedPathwiseVarianceProbabilisticSparsityTuning
import BanditRLProof.Exp3MixedSquarePredictableVarianceSparseLossRealizedDoublePathwiseVarianceProbabilisticSparsity

/-!
# Learning-rate tuning for sparse EXP3 with two predictable variances

This module reuses the pathwise-sparsity learning rate that balances entropy
against the sparse loss-mass and mixed-square radius. The realized-loss term is
replaced by the exact selected-loss predictable-variance radius. Gamma remains
caller-selected, and the common sparsity-failure event is still charged once.
-/

namespace BanditRLProof.Exp3

open MeasureTheory ProbabilityTheory

universe u v

/-- Eta-tuned threshold with both sparse pathwise predictable variances. -/
noncomputable def pathwiseVarianceProbabilisticSparseLossDoubleVarianceRealizedTunedThreshold
    {Action : Type v} [DecidableEq Action]
    (arms : Finset Action) (gamma : Real)
    (horizon sparsity : Nat) (delta : Real) : Real :=
  3 * Real.sqrt
      (Real.log (arms.card : Real) *
        pathwiseVarianceProbabilisticSparseLossHighProbabilityScale
          arms gamma horizon sparsity delta) +
    gamma * (horizon : Real) +
    sampledPurePredictableMinusObservedBernsteinConfidenceRadius
      arms gamma horizon (delta / 4) +
    sampledComparatorEstimatorBernsteinConfidenceRadius
      arms gamma horizon (delta / 4) +
    sampledRealizedPredictableVarianceRadius
      (sampledPredictableSparseRealizedVarianceBudget horizon sparsity)
      (delta / 4)

/-- The sparse small-loss double-variance budget is bounded by the eta-tuned
threshold. -/
theorem sampledPredictableDoubleVarianceProbabilisticSparseLossRealizedHighProbabilityRegretBudget_le_tunedThreshold
    {Action : Type v} [DecidableEq Action]
    (arms : Finset Action) (hcard_two : 2 ≤ arms.card)
    (gamma : Real) (hgamma_pos : 0 < gamma)
    (hgamma_le_half : gamma ≤ 1 / 2)
    (horizon sparsity : Nat) (hhorizon : 0 < horizon)
    (hsparsity : 0 < sparsity) (delta : Real) :
    sampledPredictableDoubleVarianceProbabilisticSparseLossRealizedHighProbabilityRegretBudget
        arms
        (pathwiseVarianceProbabilisticSparseLossHighProbabilityLearningRate
          arms gamma horizon sparsity delta)
        gamma horizon sparsity delta ≤
      pathwiseVarianceProbabilisticSparseLossDoubleVarianceRealizedTunedThreshold
        arms gamma horizon sparsity delta := by
  have hhedge :=
    pathwiseVarianceProbabilisticSparseLossHighProbabilityHedgeBudget_le_three_mul_sqrt
      arms hcard_two gamma hgamma_pos hgamma_le_half horizon sparsity
        hhorizon hsparsity delta
  dsimp [
    sampledPredictableDoubleVarianceProbabilisticSparseLossRealizedHighProbabilityRegretBudget,
    sampledPredictableVarianceSquareSmallLossDoubleVarianceRealizedHighProbabilityRegretBudget,
    sampledPredictableVarianceSquareSmallLossHighProbabilityRegretBudget,
    pathwiseVarianceProbabilisticSparseLossDoubleVarianceRealizedTunedThreshold,
    pathwiseVarianceProbabilisticSparseLossHighProbabilityScale
  ] at hhedge ⊢
  linarith

/-- Eta-tuned generated regret away from the common sparsity-failure event. -/
theorem sampledPredictable_tunedDoubleVarianceProbabilisticSparseLossRealizedRegret_tail_off_sparsityFailure
    {Env : Type u} {Action : Type v}
    [MeasurableSpace Env] [StandardBorelSpace Env] [Nonempty Env]
    [MeasurableSpace Action] [MeasurableSingletonClass Action]
    [StandardBorelSpace Action] [Nonempty Action] [DecidableEq Action]
    (prior : Measure Env) [IsProbabilityMeasure prior]
    (arms : Finset Action) (harms : arms.Nonempty)
    (hcard_two : 2 ≤ arms.card)
    (gamma : Real) (hgamma_pos : 0 < gamma)
    (hgamma_le_half : gamma ≤ 1 / 2)
    (loss : PredictableLossVector Env Action)
    (comparator : Action) (hcomparator : comparator ∈ arms)
    (horizon sparsity : Nat) (hhorizon : 0 < horizon)
    (hsparsity : 0 < sparsity)
    (delta : Real) (hdelta : 0 < delta) :
    let eta :=
      pathwiseVarianceProbabilisticSparseLossHighProbabilityLearningRate
        arms gamma horizon sparsity delta
    let mu := prior ⊗ₘ sampledImportanceWeightedTrajectoryKernel arms harms
      eta gamma hgamma_pos.le (by linarith : gamma ≤ 1) loss.environment
    mu ({sample |
        pathwiseVarianceProbabilisticSparseLossDoubleVarianceRealizedTunedThreshold
            arms gamma horizon sparsity delta ≤
          (Finset.range horizon).sum (fun t =>
              sampledTrajectoryRealizedLossAt t sample) -
            (Finset.range horizon).sum (fun t =>
              predictableLossAt loss t sample comparator)} \
      sampledPredictableSparsityFailure arms loss horizon sparsity) ≤
        ENNReal.ofReal delta := by
  dsimp only
  have heta :
      0 <
        pathwiseVarianceProbabilisticSparseLossHighProbabilityLearningRate
          arms gamma horizon sparsity delta :=
    pathwiseVarianceProbabilisticSparseLossHighProbabilityLearningRate_pos
      arms hcard_two gamma hgamma_pos horizon sparsity hhorizon hsparsity delta
  have hgamma_lt_one : gamma < 1 := by linarith
  have hbudget :=
    sampledPredictableDoubleVarianceProbabilisticSparseLossRealizedHighProbabilityRegretBudget_le_tunedThreshold
      arms hcard_two gamma hgamma_pos hgamma_le_half horizon sparsity
        hhorizon hsparsity delta
  have htail :=
    sampledPredictable_doubleVarianceProbabilisticSparseLossRealizedHighProbabilityRegret_tail_off_sparsityFailure
      prior arms harms
        (pathwiseVarianceProbabilisticSparseLossHighProbabilityLearningRate
          arms gamma horizon sparsity delta)
        gamma heta hgamma_pos hgamma_lt_one loss comparator hcomparator
        horizon sparsity hhorizon hsparsity delta hdelta
  dsimp only at htail ⊢
  calc
    (prior ⊗ₘ sampledImportanceWeightedTrajectoryKernel arms harms
        (pathwiseVarianceProbabilisticSparseLossHighProbabilityLearningRate
          arms gamma horizon sparsity delta)
        gamma hgamma_pos.le hgamma_lt_one.le loss.environment)
        ({sample |
          pathwiseVarianceProbabilisticSparseLossDoubleVarianceRealizedTunedThreshold
              arms gamma horizon sparsity delta ≤
            (Finset.range horizon).sum (fun t =>
                sampledTrajectoryRealizedLossAt t sample) -
              (Finset.range horizon).sum (fun t =>
                predictableLossAt loss t sample comparator)} \
          sampledPredictableSparsityFailure arms loss horizon sparsity) ≤
      (prior ⊗ₘ sampledImportanceWeightedTrajectoryKernel arms harms
        (pathwiseVarianceProbabilisticSparseLossHighProbabilityLearningRate
          arms gamma horizon sparsity delta)
        gamma hgamma_pos.le hgamma_lt_one.le loss.environment)
        ({sample |
          sampledPredictableDoubleVarianceProbabilisticSparseLossRealizedHighProbabilityRegretBudget
              arms
                (pathwiseVarianceProbabilisticSparseLossHighProbabilityLearningRate
                  arms gamma horizon sparsity delta)
              gamma horizon sparsity delta ≤
            (Finset.range horizon).sum (fun t =>
                sampledTrajectoryRealizedLossAt t sample) -
              (Finset.range horizon).sum (fun t =>
                predictableLossAt loss t sample comparator)} \
          sampledPredictableSparsityFailure arms loss horizon sparsity) := by
            apply measure_mono
            intro sample hsample
            exact ⟨hbudget.trans hsample.1, hsample.2⟩
    _ ≤ ENNReal.ofReal delta := htail

/-- Eta-tuned generated regret with the exact sparsity-failure residual. -/
theorem sampledPredictable_tunedDoubleVarianceProbabilisticSparseLossRealizedRegret_tail
    {Env : Type u} {Action : Type v}
    [MeasurableSpace Env] [StandardBorelSpace Env] [Nonempty Env]
    [MeasurableSpace Action] [MeasurableSingletonClass Action]
    [StandardBorelSpace Action] [Nonempty Action] [DecidableEq Action]
    (prior : Measure Env) [IsProbabilityMeasure prior]
    (arms : Finset Action) (harms : arms.Nonempty)
    (hcard_two : 2 ≤ arms.card)
    (gamma : Real) (hgamma_pos : 0 < gamma)
    (hgamma_le_half : gamma ≤ 1 / 2)
    (loss : PredictableLossVector Env Action)
    (comparator : Action) (hcomparator : comparator ∈ arms)
    (horizon sparsity : Nat) (hhorizon : 0 < horizon)
    (hsparsity : 0 < sparsity)
    (delta : Real) (hdelta : 0 < delta) :
    let eta :=
      pathwiseVarianceProbabilisticSparseLossHighProbabilityLearningRate
        arms gamma horizon sparsity delta
    let mu := prior ⊗ₘ sampledImportanceWeightedTrajectoryKernel arms harms
      eta gamma hgamma_pos.le (by linarith : gamma ≤ 1) loss.environment
    mu {sample |
        pathwiseVarianceProbabilisticSparseLossDoubleVarianceRealizedTunedThreshold
            arms gamma horizon sparsity delta ≤
          (Finset.range horizon).sum (fun t =>
              sampledTrajectoryRealizedLossAt t sample) -
            (Finset.range horizon).sum (fun t =>
              predictableLossAt loss t sample comparator)} ≤
      ENNReal.ofReal delta +
        mu (sampledPredictableSparsityFailure arms loss horizon sparsity) := by
  dsimp only
  have heta :
      0 <
        pathwiseVarianceProbabilisticSparseLossHighProbabilityLearningRate
          arms gamma horizon sparsity delta :=
    pathwiseVarianceProbabilisticSparseLossHighProbabilityLearningRate_pos
      arms hcard_two gamma hgamma_pos horizon sparsity hhorizon hsparsity delta
  have hgamma_lt_one : gamma < 1 := by linarith
  have hbudget :=
    sampledPredictableDoubleVarianceProbabilisticSparseLossRealizedHighProbabilityRegretBudget_le_tunedThreshold
      arms hcard_two gamma hgamma_pos hgamma_le_half horizon sparsity
        hhorizon hsparsity delta
  have htail :=
    sampledPredictable_doubleVarianceProbabilisticSparseLossRealizedHighProbabilityRegret_tail
      prior arms harms
        (pathwiseVarianceProbabilisticSparseLossHighProbabilityLearningRate
          arms gamma horizon sparsity delta)
        gamma heta hgamma_pos hgamma_lt_one loss comparator hcomparator
        horizon sparsity hhorizon hsparsity delta hdelta
  dsimp only at htail ⊢
  exact
    (measure_mono (fun _sample hsample => hbudget.trans hsample)).trans htail

/-- Practical eta-tuned `delta + epsilon` theorem under the internally tuned
generated measure. -/
theorem sampledPredictable_tunedDoubleVarianceProbabilisticSparseLossRealizedRegret_tail_of_sparsityFailure_le
    {Env : Type u} {Action : Type v}
    [MeasurableSpace Env] [StandardBorelSpace Env] [Nonempty Env]
    [MeasurableSpace Action] [MeasurableSingletonClass Action]
    [StandardBorelSpace Action] [Nonempty Action] [DecidableEq Action]
    (prior : Measure Env) [IsProbabilityMeasure prior]
    (arms : Finset Action) (harms : arms.Nonempty)
    (hcard_two : 2 ≤ arms.card)
    (gamma : Real) (hgamma_pos : 0 < gamma)
    (hgamma_le_half : gamma ≤ 1 / 2)
    (loss : PredictableLossVector Env Action)
    (comparator : Action) (hcomparator : comparator ∈ arms)
    (horizon sparsity : Nat) (hhorizon : 0 < horizon)
    (hsparsity : 0 < sparsity)
    (delta epsilon : Real) (hdelta : 0 < delta) :
    let eta :=
      pathwiseVarianceProbabilisticSparseLossHighProbabilityLearningRate
        arms gamma horizon sparsity delta
    let mu := prior ⊗ₘ sampledImportanceWeightedTrajectoryKernel arms harms
      eta gamma hgamma_pos.le (by linarith : gamma ≤ 1) loss.environment
    mu (sampledPredictableSparsityFailure arms loss horizon sparsity) ≤
        ENNReal.ofReal epsilon →
      mu {sample |
          pathwiseVarianceProbabilisticSparseLossDoubleVarianceRealizedTunedThreshold
              arms gamma horizon sparsity delta ≤
            (Finset.range horizon).sum (fun t =>
                sampledTrajectoryRealizedLossAt t sample) -
              (Finset.range horizon).sum (fun t =>
                predictableLossAt loss t sample comparator)} ≤
        ENNReal.ofReal delta + ENNReal.ofReal epsilon := by
  dsimp only
  intro hfailure
  have htail :=
    sampledPredictable_tunedDoubleVarianceProbabilisticSparseLossRealizedRegret_tail
      prior arms harms hcard_two gamma hgamma_pos hgamma_le_half loss comparator
        hcomparator horizon sparsity hhorizon hsparsity delta hdelta
  dsimp only at htail
  exact htail.trans (add_le_add le_rfl hfailure)

end BanditRLProof.Exp3
