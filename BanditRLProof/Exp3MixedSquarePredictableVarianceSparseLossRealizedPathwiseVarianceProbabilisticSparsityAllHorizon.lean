import BanditRLProof.Exp3MixedSquarePredictableVarianceSparseLossRealizedPathwiseVarianceProbabilisticSparsityExplicitTuning
import BanditRLProof.Exp3BernsteinAllHorizon

/-!
# All-horizon pathwise-variance EXP3 under probabilistic sparse losses

The explicit pathwise-variance schedule has its refined `14 * gamma * T`
threshold when four horizon inequalities make clipping inactive. Outside that
regime this module uses the strict `T + 1` zero-probability threshold under
exactly the same internal eta, gamma, and generated trajectory measure.

The resulting theorem covers every positive horizon and preserves the exact
support-sparsity failure residual. Its practical endpoint consumes
`mu(sparsityFailure) <= ofReal epsilon` and returns
`ofReal delta + ofReal epsilon`.

The refined branch uses the sparse pathwise variance budget `K * S * T /
gamma`. It does not reintroduce the global `K * T` Markov envelope, the old
`K ^ 2` mixed numerator, or a polynomial `1 / delta` factor.
-/

namespace BanditRLProof.Exp3

open MeasureTheory ProbabilityTheory

universe u v

/-- Regime in which all four components of the pathwise probabilistic-sparsity
exploration schedule are at most one half. -/
def pathwiseVarianceProbabilisticSparseLossLargeHorizonCondition
    (K S T delta : Real) : Prop :=
  4 * (S * Real.log K) <= T ∧
    32 * (K * S * Real.log K ^ 2 * Real.log (4 / delta)) <= T ^ 3 ∧
    8 * (K * Real.log (4 / delta)) <= T ∧
    8 * ((Concentration.intervalVarianceProxy 0 1 : NNReal) : Real) *
      Real.log (4 / delta) <= T

/-- All-horizon threshold for the pathwise probabilistic-sparsity route:
use the explicit large-horizon threshold in its valid regime and `T + 1`
otherwise. -/
noncomputable def pathwiseVarianceProbabilisticSparseLossAllHorizonRegretThreshold
    {Action : Type v} (arms : Finset Action) (horizon sparsity : Nat)
    (delta : Real) : Real := by
  classical
  let gamma :=
    pathwiseVarianceProbabilisticSparseLossClippedExplorationRate
      (arms.card : Real) (sparsity : Real) (horizon : Real) delta
  exact if pathwiseVarianceProbabilisticSparseLossLargeHorizonCondition
      (arms.card : Real) (sparsity : Real) (horizon : Real) delta then
    pathwiseVarianceProbabilisticSparseLossRealizedExplicitThreshold
      arms gamma horizon sparsity delta
  else
    (horizon : Real) + 1

/-- Generated all-horizon realized-regret theorem away from the exact
support-sparsity failure event. Both branches use the same internally selected
eta, gamma, and generated trajectory measure. -/
theorem sampledPredictable_allHorizonProbabilisticSparseLossPathwiseVarianceRealizedRegret_tail_off_sparsityFailure
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
      pathwiseVarianceProbabilisticSparseLossClippedExplorationRate
        (arms.card : Real) (sparsity : Real) (horizon : Real) delta
    let eta :=
      pathwiseVarianceProbabilisticSparseLossHighProbabilityLearningRate
        arms gamma horizon sparsity delta
    let mu := prior ⊗ₘ sampledImportanceWeightedTrajectoryKernel arms harms
      eta gamma
        (pathwiseVarianceProbabilisticSparseLossClippedExplorationRate_pos
          (arms.card : Real) (sparsity : Real) (horizon : Real) delta
          (by exact_mod_cast hcard_two)
          (by exact_mod_cast hsparsity)
          (by exact_mod_cast hhorizon)).le
        (by
          exact
            (pathwiseVarianceProbabilisticSparseLossClippedExplorationRate_le_half
              (arms.card : Real) (sparsity : Real) (horizon : Real)
                delta).trans (by norm_num))
        loss.environment
    mu ({sample |
        pathwiseVarianceProbabilisticSparseLossAllHorizonRegretThreshold
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
      pathwiseVarianceProbabilisticSparseLossLargeHorizonCondition
        (arms.card : Real) (sparsity : Real) (horizon : Real) delta
  · rw [
      pathwiseVarianceProbabilisticSparseLossAllHorizonRegretThreshold,
      if_pos hlarge]
    exact
      sampledPredictable_explicitProbabilisticSparseLossPathwiseVarianceRealizedRegret_tail_off_sparsityFailure
        prior arms harms hcard_two loss comparator hcomparator horizon sparsity
          hhorizon hsparsity delta hdelta hdelta_le_one hlarge.1 hlarge.2.1
            hlarge.2.2.1 hlarge.2.2.2
  · rw [
      pathwiseVarianceProbabilisticSparseLossAllHorizonRegretThreshold,
      if_neg hlarge]
    have htrivial :=
      sampledPredictable_trivialRealizedRegret_tail
        prior arms harms
          (pathwiseVarianceProbabilisticSparseLossHighProbabilityLearningRate
            arms
              (pathwiseVarianceProbabilisticSparseLossClippedExplorationRate
                (arms.card : Real) (sparsity : Real) (horizon : Real) delta)
              horizon sparsity delta)
          (pathwiseVarianceProbabilisticSparseLossClippedExplorationRate
            (arms.card : Real) (sparsity : Real) (horizon : Real) delta)
          (pathwiseVarianceProbabilisticSparseLossClippedExplorationRate_pos
            (arms.card : Real) (sparsity : Real) (horizon : Real) delta
            (by exact_mod_cast hcard_two)
            (by exact_mod_cast hsparsity)
            (by exact_mod_cast hhorizon)).le
          (by
            exact
              (pathwiseVarianceProbabilisticSparseLossClippedExplorationRate_le_half
                (arms.card : Real) (sparsity : Real) (horizon : Real)
                  delta).trans (by norm_num))
          loss comparator horizon delta
    dsimp only at htrivial
    exact (measure_mono Set.diff_subset).trans htrivial

/-- Generated all-horizon realized-regret theorem with the exact
support-sparsity failure residual. -/
theorem sampledPredictable_allHorizonProbabilisticSparseLossPathwiseVarianceRealizedRegret_tail
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
      pathwiseVarianceProbabilisticSparseLossClippedExplorationRate
        (arms.card : Real) (sparsity : Real) (horizon : Real) delta
    let eta :=
      pathwiseVarianceProbabilisticSparseLossHighProbabilityLearningRate
        arms gamma horizon sparsity delta
    let mu := prior ⊗ₘ sampledImportanceWeightedTrajectoryKernel arms harms
      eta gamma
        (pathwiseVarianceProbabilisticSparseLossClippedExplorationRate_pos
          (arms.card : Real) (sparsity : Real) (horizon : Real) delta
          (by exact_mod_cast hcard_two)
          (by exact_mod_cast hsparsity)
          (by exact_mod_cast hhorizon)).le
        (by
          exact
            (pathwiseVarianceProbabilisticSparseLossClippedExplorationRate_le_half
              (arms.card : Real) (sparsity : Real) (horizon : Real)
                delta).trans (by norm_num))
        loss.environment
    mu {sample |
        pathwiseVarianceProbabilisticSparseLossAllHorizonRegretThreshold
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
      pathwiseVarianceProbabilisticSparseLossLargeHorizonCondition
        (arms.card : Real) (sparsity : Real) (horizon : Real) delta
  · rw [
      pathwiseVarianceProbabilisticSparseLossAllHorizonRegretThreshold,
      if_pos hlarge]
    exact
      sampledPredictable_explicitProbabilisticSparseLossPathwiseVarianceRealizedRegret_tail
        prior arms harms hcard_two loss comparator hcomparator horizon sparsity
          hhorizon hsparsity delta hdelta hdelta_le_one hlarge.1 hlarge.2.1
            hlarge.2.2.1 hlarge.2.2.2
  · rw [
      pathwiseVarianceProbabilisticSparseLossAllHorizonRegretThreshold,
      if_neg hlarge]
    have htrivial :=
      sampledPredictable_trivialRealizedRegret_tail
        prior arms harms
          (pathwiseVarianceProbabilisticSparseLossHighProbabilityLearningRate
            arms
              (pathwiseVarianceProbabilisticSparseLossClippedExplorationRate
                (arms.card : Real) (sparsity : Real) (horizon : Real) delta)
              horizon sparsity delta)
          (pathwiseVarianceProbabilisticSparseLossClippedExplorationRate
            (arms.card : Real) (sparsity : Real) (horizon : Real) delta)
          (pathwiseVarianceProbabilisticSparseLossClippedExplorationRate_pos
            (arms.card : Real) (sparsity : Real) (horizon : Real) delta
            (by exact_mod_cast hcard_two)
            (by exact_mod_cast hsparsity)
            (by exact_mod_cast hhorizon)).le
          (by
            exact
              (pathwiseVarianceProbabilisticSparseLossClippedExplorationRate_le_half
                (arms.card : Real) (sparsity : Real) (horizon : Real)
                  delta).trans (by norm_num))
          loss comparator horizon delta
    exact htrivial.trans (le_add_of_nonneg_right (zero_le _))

/-- Practical all-horizon `delta + epsilon` theorem under an exact bound on
the support-sparsity failure event for the same internally tuned measure. -/
theorem sampledPredictable_allHorizonProbabilisticSparseLossPathwiseVarianceRealizedRegret_tail_of_sparsityFailure_le
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
      pathwiseVarianceProbabilisticSparseLossClippedExplorationRate
        (arms.card : Real) (sparsity : Real) (horizon : Real) delta
    let eta :=
      pathwiseVarianceProbabilisticSparseLossHighProbabilityLearningRate
        arms gamma horizon sparsity delta
    let mu := prior ⊗ₘ sampledImportanceWeightedTrajectoryKernel arms harms
      eta gamma
        (pathwiseVarianceProbabilisticSparseLossClippedExplorationRate_pos
          (arms.card : Real) (sparsity : Real) (horizon : Real) delta
          (by exact_mod_cast hcard_two)
          (by exact_mod_cast hsparsity)
          (by exact_mod_cast hhorizon)).le
        (by
          exact
            (pathwiseVarianceProbabilisticSparseLossClippedExplorationRate_le_half
              (arms.card : Real) (sparsity : Real) (horizon : Real)
                delta).trans (by norm_num))
        loss.environment
    mu (sampledPredictableSparsityFailure arms loss horizon sparsity) <=
        ENNReal.ofReal epsilon →
      mu {sample |
          pathwiseVarianceProbabilisticSparseLossAllHorizonRegretThreshold
              arms horizon sparsity delta <=
            (Finset.range horizon).sum (fun t =>
                sampledTrajectoryRealizedLossAt t sample) -
              (Finset.range horizon).sum (fun t =>
                predictableLossAt loss t sample comparator)} <=
        ENNReal.ofReal delta + ENNReal.ofReal epsilon := by
  dsimp only
  intro hfailure
  have htail :=
    sampledPredictable_allHorizonProbabilisticSparseLossPathwiseVarianceRealizedRegret_tail
      prior arms harms hcard_two loss comparator hcomparator horizon sparsity
        hhorizon hsparsity delta hdelta hdelta_le_one
  dsimp only at htail
  exact htail.trans (add_le_add le_rfl hfailure)

end BanditRLProof.Exp3
