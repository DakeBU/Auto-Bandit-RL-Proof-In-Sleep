import BanditRLProof.Exp3MixedSquarePredictableVarianceSparseLossRealizedMarkovProbabilisticSparsityExplicitTuning
import BanditRLProof.Exp3BernsteinAllHorizon

/-!
# All-horizon predictable-variance EXP3 under probabilistic sparse losses

The explicit probabilistic-sparsity schedule has its refined
`14 * gamma * T` threshold when four horizon inequalities make clipping
inactive. Outside that regime this module uses the strict `T + 1`
zero-probability threshold under exactly the same internal eta, gamma, and
generated trajectory measure.

The resulting theorem covers every positive horizon and preserves the exact
support-sparsity failure residual. Its practical endpoint consumes
`mu(sparsityFailure) <= ofReal epsilon` and returns
`ofReal delta + ofReal epsilon`.

The refined branch still uses the global `K * T` Markov envelope. This is not
a pathwise-sparse variance, best-arm first-order, Freedman, anytime, or ideal
EXP3.P theorem.
-/

namespace BanditRLProof.Exp3

open MeasureTheory ProbabilityTheory

universe u v

/-- Regime in which all four components of the probabilistic-sparsity
predictable-variance exploration schedule are at most one half. -/
def probabilisticSparseLossPredictableVarianceLargeHorizonCondition
    (K S T delta : Real) : Prop :=
  4 * (S * Real.log K) <= T ∧
    32 * (5 * K ^ 2 * Real.log K ^ 2 * Real.log (5 / delta)) <=
      delta * T ^ 3 ∧
    8 * (K * Real.log (5 / delta)) <= T ∧
    8 * ((Concentration.intervalVarianceProxy 0 1 : NNReal) : Real) *
      Real.log (5 / delta) <= T

/-- All-horizon threshold for the probabilistic-sparsity route: use the
explicit large-horizon threshold in its valid regime and `T + 1` otherwise. -/
noncomputable def probabilisticSparseLossPredictableVarianceAllHorizonRegretThreshold
    {Action : Type v} (arms : Finset Action) (horizon sparsity : Nat)
    (delta : Real) : Real := by
  classical
  let gamma :=
    probabilisticSparseLossPredictableVarianceClippedExplorationRate
      (arms.card : Real) (sparsity : Real) (horizon : Real) delta
  exact if probabilisticSparseLossPredictableVarianceLargeHorizonCondition
      (arms.card : Real) (sparsity : Real) (horizon : Real) delta then
    probabilisticSparseLossPredictableVarianceRealizedMarkovExplicitThreshold
      arms gamma horizon sparsity delta
  else
    (horizon : Real) + 1

/-- Generated all-horizon realized-regret theorem with the exact
support-sparsity failure residual. -/
theorem sampledPredictable_allHorizonProbabilisticSparseLossPredictableVarianceRealizedMarkovRegret_tail
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
      probabilisticSparseLossPredictableVarianceClippedExplorationRate
        (arms.card : Real) (sparsity : Real) (horizon : Real) delta
    let eta :=
      probabilisticSparseLossPredictableVarianceHighProbabilityLearningRate
        arms gamma horizon sparsity delta
    let mu := prior ⊗ₘ sampledImportanceWeightedTrajectoryKernel arms harms
      eta gamma
        (probabilisticSparseLossPredictableVarianceClippedExplorationRate_pos
          (arms.card : Real) (sparsity : Real) (horizon : Real) delta
          (by exact_mod_cast hcard_two)
          (by exact_mod_cast hsparsity)
          (by exact_mod_cast hhorizon)).le
        (by
          exact
            (probabilisticSparseLossPredictableVarianceClippedExplorationRate_le_half
              (arms.card : Real) (sparsity : Real) (horizon : Real)
                delta).trans (by norm_num))
        loss.environment
    mu {sample |
        probabilisticSparseLossPredictableVarianceAllHorizonRegretThreshold
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
      probabilisticSparseLossPredictableVarianceLargeHorizonCondition
        (arms.card : Real) (sparsity : Real) (horizon : Real) delta
  · rw [
      probabilisticSparseLossPredictableVarianceAllHorizonRegretThreshold,
      if_pos hlarge]
    exact
      sampledPredictable_explicitProbabilisticSparseLossPredictableVarianceRealizedMarkovRegret_tail
        prior arms harms hcard_two loss comparator hcomparator horizon sparsity
          hhorizon hsparsity delta hdelta hdelta_le_one hlarge.1 hlarge.2.1
            hlarge.2.2.1 hlarge.2.2.2
  · rw [
      probabilisticSparseLossPredictableVarianceAllHorizonRegretThreshold,
      if_neg hlarge]
    have htrivial :=
      sampledPredictable_trivialRealizedRegret_tail
        prior arms harms
          (probabilisticSparseLossPredictableVarianceHighProbabilityLearningRate
            arms
              (probabilisticSparseLossPredictableVarianceClippedExplorationRate
                (arms.card : Real) (sparsity : Real) (horizon : Real) delta)
              horizon sparsity delta)
          (probabilisticSparseLossPredictableVarianceClippedExplorationRate
            (arms.card : Real) (sparsity : Real) (horizon : Real) delta)
          (probabilisticSparseLossPredictableVarianceClippedExplorationRate_pos
            (arms.card : Real) (sparsity : Real) (horizon : Real) delta
            (by exact_mod_cast hcard_two)
            (by exact_mod_cast hsparsity)
            (by exact_mod_cast hhorizon)).le
          (by
            exact
              (probabilisticSparseLossPredictableVarianceClippedExplorationRate_le_half
                (arms.card : Real) (sparsity : Real) (horizon : Real)
                  delta).trans (by norm_num))
          loss comparator horizon delta
    exact htrivial.trans (le_add_of_nonneg_right (zero_le _))

/-- Practical all-horizon `delta + epsilon` theorem under an exact bound on
the support-sparsity failure event for the same internally tuned measure. -/
theorem sampledPredictable_allHorizonProbabilisticSparseLossPredictableVarianceRealizedMarkovRegret_tail_of_sparsityFailure_le
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
      probabilisticSparseLossPredictableVarianceClippedExplorationRate
        (arms.card : Real) (sparsity : Real) (horizon : Real) delta
    let eta :=
      probabilisticSparseLossPredictableVarianceHighProbabilityLearningRate
        arms gamma horizon sparsity delta
    let mu := prior ⊗ₘ sampledImportanceWeightedTrajectoryKernel arms harms
      eta gamma
        (probabilisticSparseLossPredictableVarianceClippedExplorationRate_pos
          (arms.card : Real) (sparsity : Real) (horizon : Real) delta
          (by exact_mod_cast hcard_two)
          (by exact_mod_cast hsparsity)
          (by exact_mod_cast hhorizon)).le
        (by
          exact
            (probabilisticSparseLossPredictableVarianceClippedExplorationRate_le_half
              (arms.card : Real) (sparsity : Real) (horizon : Real)
                delta).trans (by norm_num))
        loss.environment
    mu (sampledPredictableSparsityFailure arms loss horizon sparsity) <=
        ENNReal.ofReal epsilon ->
      mu {sample |
          probabilisticSparseLossPredictableVarianceAllHorizonRegretThreshold
              arms horizon sparsity delta <=
            (Finset.range horizon).sum (fun t =>
                sampledTrajectoryRealizedLossAt t sample) -
              (Finset.range horizon).sum (fun t =>
                predictableLossAt loss t sample comparator)} <=
        ENNReal.ofReal delta + ENNReal.ofReal epsilon := by
  dsimp only
  intro hfailure
  have htail :=
    sampledPredictable_allHorizonProbabilisticSparseLossPredictableVarianceRealizedMarkovRegret_tail
      prior arms harms hcard_two loss comparator hcomparator horizon sparsity
        hhorizon hsparsity delta hdelta hdelta_le_one
  dsimp only at htail
  exact htail.trans (add_le_add le_rfl hfailure)

end BanditRLProof.Exp3
