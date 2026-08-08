import BanditRLProof.Exp3MixedSquarePredictableVarianceSparseLossRealizedDoublePathwiseVarianceProbabilisticSparsityExplicitTuning
import BanditRLProof.Exp3BernsteinAllHorizon

/-!
# All-horizon sparse EXP3 with two predictable variances

The exact double-variance schedule has the refined `16 * gamma * T`
threshold when four horizon inequalities make clipping inactive. Outside that
regime this module uses the strict `T + 1` zero-probability threshold under
the identical internal eta, gamma, and generated trajectory measure.

The common support-sparsity failure event is removed once in the off-bad
theorem and added once in the residual theorem. The practical endpoint
consumes its same-measure `ofReal epsilon` bound.
-/

namespace BanditRLProof.Exp3

open MeasureTheory ProbabilityTheory

universe u v

/-- Regime in which every component of the exact double-variance exploration
schedule is at most one half. -/
def doubleVarianceProbabilisticSparseLossLargeHorizonCondition
    (K S T delta : Real) : Prop :=
  4 * (S * Real.log K) <= T ∧
    32 * (K * S * Real.log K ^ 2 * Real.log (4 / delta)) <= T ^ 3 ∧
    8 * (K * Real.log (4 / delta)) <= T ∧
    4 * (S * Real.log (4 / delta)) <= T

/-- All-horizon threshold for the exact double-variance sparse route: use
the refined threshold in its valid regime and strict `T + 1` otherwise. -/
noncomputable def doubleVarianceProbabilisticSparseLossAllHorizonRegretThreshold
    {Action : Type v} (arms : Finset Action) (horizon sparsity : Nat)
    (delta : Real) : Real := by
  classical
  let gamma :=
    doubleVarianceProbabilisticSparseLossClippedExplorationRate
      (arms.card : Real) (sparsity : Real) (horizon : Real) delta
  exact if doubleVarianceProbabilisticSparseLossLargeHorizonCondition
      (arms.card : Real) (sparsity : Real) (horizon : Real) delta then
    pathwiseVarianceProbabilisticSparseLossDoubleVarianceRealizedExplicitThreshold
      arms gamma horizon sparsity delta
  else
    (horizon : Real) + 1

/-- Generated all-horizon exact double-variance regret away from the common
sparsity-failure event. Both branches use the same eta, gamma, and measure. -/
theorem sampledPredictable_allHorizonDoubleVarianceProbabilisticSparseLossRealizedRegret_tail_off_sparsityFailure
    {Env : Type u} {Action : Type v}
    [MeasurableSpace Env] [StandardBorelSpace Env] [Nonempty Env]
    [MeasurableSpace Action] [MeasurableSingletonClass Action]
    [StandardBorelSpace Action] [Nonempty Action] [DecidableEq Action]
    (prior : Measure Env) [IsProbabilityMeasure prior]
    (arms : Finset Action) (harms : arms.Nonempty)
    (hcard_two : 2 <= arms.card)
    (loss : PredictableLossVector Env Action)
    (comparator : Action) (hcomparator : comparator ∈ arms)
    (horizon sparsity : Nat) (hhorizon : 0 < horizon)
    (hsparsity : 0 < sparsity)
    (delta : Real) (hdelta : 0 < delta) (hdelta_le_one : delta <= 1) :
    let gamma :=
      doubleVarianceProbabilisticSparseLossClippedExplorationRate
        (arms.card : Real) (sparsity : Real) (horizon : Real) delta
    let eta :=
      pathwiseVarianceProbabilisticSparseLossHighProbabilityLearningRate
        arms gamma horizon sparsity delta
    let mu := prior ⊗ₘ sampledImportanceWeightedTrajectoryKernel arms harms
      eta gamma
        (doubleVarianceProbabilisticSparseLossClippedExplorationRate_pos
          (arms.card : Real) (sparsity : Real) (horizon : Real) delta
          (by exact_mod_cast hcard_two)
          (by exact_mod_cast hsparsity)
          (by exact_mod_cast hhorizon)).le
        (by
          exact
            (doubleVarianceProbabilisticSparseLossClippedExplorationRate_le_half
              (arms.card : Real) (sparsity : Real) (horizon : Real)
                delta).trans (by norm_num))
        loss.environment
    mu ({sample |
        doubleVarianceProbabilisticSparseLossAllHorizonRegretThreshold
            arms horizon sparsity delta <=
          (Finset.range horizon).sum (fun t =>
              sampledTrajectoryRealizedLossAt t sample) -
            (Finset.range horizon).sum (fun t =>
              predictableLossAt loss t sample comparator)} \
      sampledPredictableSparsityFailure arms loss horizon sparsity) <=
        ENNReal.ofReal delta := by
  dsimp only
  classical
  by_cases hlarge :
      doubleVarianceProbabilisticSparseLossLargeHorizonCondition
        (arms.card : Real) (sparsity : Real) (horizon : Real) delta
  · rw [
      doubleVarianceProbabilisticSparseLossAllHorizonRegretThreshold,
      if_pos hlarge]
    exact
      sampledPredictable_explicitDoubleVarianceProbabilisticSparseLossRealizedRegret_tail_off_sparsityFailure
        prior arms harms hcard_two loss comparator hcomparator horizon sparsity
          hhorizon hsparsity delta hdelta hdelta_le_one hlarge.1 hlarge.2.1
            hlarge.2.2.1 hlarge.2.2.2
  · rw [
      doubleVarianceProbabilisticSparseLossAllHorizonRegretThreshold,
      if_neg hlarge]
    have htrivial :=
      sampledPredictable_trivialRealizedRegret_tail
        prior arms harms
          (pathwiseVarianceProbabilisticSparseLossHighProbabilityLearningRate
            arms
              (doubleVarianceProbabilisticSparseLossClippedExplorationRate
                (arms.card : Real) (sparsity : Real) (horizon : Real) delta)
              horizon sparsity delta)
          (doubleVarianceProbabilisticSparseLossClippedExplorationRate
            (arms.card : Real) (sparsity : Real) (horizon : Real) delta)
          (doubleVarianceProbabilisticSparseLossClippedExplorationRate_pos
            (arms.card : Real) (sparsity : Real) (horizon : Real) delta
            (by exact_mod_cast hcard_two)
            (by exact_mod_cast hsparsity)
            (by exact_mod_cast hhorizon)).le
          (by
            exact
              (doubleVarianceProbabilisticSparseLossClippedExplorationRate_le_half
                (arms.card : Real) (sparsity : Real) (horizon : Real)
                  delta).trans (by norm_num))
          loss comparator horizon delta
    dsimp only at htrivial
    exact (measure_mono Set.diff_subset).trans htrivial

/-- Generated all-horizon exact double-variance regret with the common
sparsity-failure residual. -/
theorem sampledPredictable_allHorizonDoubleVarianceProbabilisticSparseLossRealizedRegret_tail
    {Env : Type u} {Action : Type v}
    [MeasurableSpace Env] [StandardBorelSpace Env] [Nonempty Env]
    [MeasurableSpace Action] [MeasurableSingletonClass Action]
    [StandardBorelSpace Action] [Nonempty Action] [DecidableEq Action]
    (prior : Measure Env) [IsProbabilityMeasure prior]
    (arms : Finset Action) (harms : arms.Nonempty)
    (hcard_two : 2 <= arms.card)
    (loss : PredictableLossVector Env Action)
    (comparator : Action) (hcomparator : comparator ∈ arms)
    (horizon sparsity : Nat) (hhorizon : 0 < horizon)
    (hsparsity : 0 < sparsity)
    (delta : Real) (hdelta : 0 < delta) (hdelta_le_one : delta <= 1) :
    let gamma :=
      doubleVarianceProbabilisticSparseLossClippedExplorationRate
        (arms.card : Real) (sparsity : Real) (horizon : Real) delta
    let eta :=
      pathwiseVarianceProbabilisticSparseLossHighProbabilityLearningRate
        arms gamma horizon sparsity delta
    let mu := prior ⊗ₘ sampledImportanceWeightedTrajectoryKernel arms harms
      eta gamma
        (doubleVarianceProbabilisticSparseLossClippedExplorationRate_pos
          (arms.card : Real) (sparsity : Real) (horizon : Real) delta
          (by exact_mod_cast hcard_two)
          (by exact_mod_cast hsparsity)
          (by exact_mod_cast hhorizon)).le
        (by
          exact
            (doubleVarianceProbabilisticSparseLossClippedExplorationRate_le_half
              (arms.card : Real) (sparsity : Real) (horizon : Real)
                delta).trans (by norm_num))
        loss.environment
    mu {sample |
        doubleVarianceProbabilisticSparseLossAllHorizonRegretThreshold
            arms horizon sparsity delta <=
          (Finset.range horizon).sum (fun t =>
              sampledTrajectoryRealizedLossAt t sample) -
            (Finset.range horizon).sum (fun t =>
              predictableLossAt loss t sample comparator)} <=
      ENNReal.ofReal delta +
        mu (sampledPredictableSparsityFailure arms loss horizon sparsity) := by
  dsimp only
  classical
  by_cases hlarge :
      doubleVarianceProbabilisticSparseLossLargeHorizonCondition
        (arms.card : Real) (sparsity : Real) (horizon : Real) delta
  · rw [
      doubleVarianceProbabilisticSparseLossAllHorizonRegretThreshold,
      if_pos hlarge]
    exact
      sampledPredictable_explicitDoubleVarianceProbabilisticSparseLossRealizedRegret_tail
        prior arms harms hcard_two loss comparator hcomparator horizon sparsity
          hhorizon hsparsity delta hdelta hdelta_le_one hlarge.1 hlarge.2.1
            hlarge.2.2.1 hlarge.2.2.2
  · rw [
      doubleVarianceProbabilisticSparseLossAllHorizonRegretThreshold,
      if_neg hlarge]
    have htrivial :=
      sampledPredictable_trivialRealizedRegret_tail
        prior arms harms
          (pathwiseVarianceProbabilisticSparseLossHighProbabilityLearningRate
            arms
              (doubleVarianceProbabilisticSparseLossClippedExplorationRate
                (arms.card : Real) (sparsity : Real) (horizon : Real) delta)
              horizon sparsity delta)
          (doubleVarianceProbabilisticSparseLossClippedExplorationRate
            (arms.card : Real) (sparsity : Real) (horizon : Real) delta)
          (doubleVarianceProbabilisticSparseLossClippedExplorationRate_pos
            (arms.card : Real) (sparsity : Real) (horizon : Real) delta
            (by exact_mod_cast hcard_two)
            (by exact_mod_cast hsparsity)
            (by exact_mod_cast hhorizon)).le
          (by
            exact
              (doubleVarianceProbabilisticSparseLossClippedExplorationRate_le_half
                (arms.card : Real) (sparsity : Real) (horizon : Real)
                  delta).trans (by norm_num))
          loss comparator horizon delta
    exact htrivial.trans (le_add_of_nonneg_right (zero_le _))

/-- Practical all-horizon `delta + epsilon` theorem under the exact
same-measure sparsity-failure bound. -/
theorem sampledPredictable_allHorizonDoubleVarianceProbabilisticSparseLossRealizedRegret_tail_of_sparsityFailure_le
    {Env : Type u} {Action : Type v}
    [MeasurableSpace Env] [StandardBorelSpace Env] [Nonempty Env]
    [MeasurableSpace Action] [MeasurableSingletonClass Action]
    [StandardBorelSpace Action] [Nonempty Action] [DecidableEq Action]
    (prior : Measure Env) [IsProbabilityMeasure prior]
    (arms : Finset Action) (harms : arms.Nonempty)
    (hcard_two : 2 <= arms.card)
    (loss : PredictableLossVector Env Action)
    (comparator : Action) (hcomparator : comparator ∈ arms)
    (horizon sparsity : Nat) (hhorizon : 0 < horizon)
    (hsparsity : 0 < sparsity)
    (delta epsilon : Real) (hdelta : 0 < delta)
    (hdelta_le_one : delta <= 1) :
    let gamma :=
      doubleVarianceProbabilisticSparseLossClippedExplorationRate
        (arms.card : Real) (sparsity : Real) (horizon : Real) delta
    let eta :=
      pathwiseVarianceProbabilisticSparseLossHighProbabilityLearningRate
        arms gamma horizon sparsity delta
    let mu := prior ⊗ₘ sampledImportanceWeightedTrajectoryKernel arms harms
      eta gamma
        (doubleVarianceProbabilisticSparseLossClippedExplorationRate_pos
          (arms.card : Real) (sparsity : Real) (horizon : Real) delta
          (by exact_mod_cast hcard_two)
          (by exact_mod_cast hsparsity)
          (by exact_mod_cast hhorizon)).le
        (by
          exact
            (doubleVarianceProbabilisticSparseLossClippedExplorationRate_le_half
              (arms.card : Real) (sparsity : Real) (horizon : Real)
                delta).trans (by norm_num))
        loss.environment
    mu (sampledPredictableSparsityFailure arms loss horizon sparsity) <=
        ENNReal.ofReal epsilon →
      mu {sample |
          doubleVarianceProbabilisticSparseLossAllHorizonRegretThreshold
              arms horizon sparsity delta <=
            (Finset.range horizon).sum (fun t =>
                sampledTrajectoryRealizedLossAt t sample) -
              (Finset.range horizon).sum (fun t =>
                predictableLossAt loss t sample comparator)} <=
        ENNReal.ofReal delta + ENNReal.ofReal epsilon := by
  dsimp only
  intro hfailure
  have htail :=
    sampledPredictable_allHorizonDoubleVarianceProbabilisticSparseLossRealizedRegret_tail
      prior arms harms hcard_two loss comparator hcomparator horizon sparsity
        hhorizon hsparsity delta hdelta hdelta_le_one
  dsimp only at htail
  exact htail.trans (add_le_add le_rfl hfailure)

end BanditRLProof.Exp3
