import BanditRLProof.Exp3MixedSquarePredictableVarianceSparseLossRealizedMarkovExplicitTuning
import BanditRLProof.Exp3BernsteinAllHorizon

/-!
# All-horizon sparse-loss predictable-variance EXP3 route

The explicit sparse-loss schedule has its refined `14 * gamma * T` threshold
when four horizon inequalities make clipping inactive. Outside that regime
this module reuses the compiled almost-sure horizon bound and the strict
`T + 1` zero-probability threshold.

This closes active clipping for the current pathwise sparse Markov route. It
does not improve Markov's polynomial confidence dependence, convert armwise
aggregate sparse loss to best-arm first-order regret, or prove Freedman/EXP3.P.
-/

namespace BanditRLProof.Exp3

open MeasureTheory ProbabilityTheory

universe u v

/-- The regime in which all four components of the sparse-loss
predictable-variance exploration schedule are at most one half. -/
def sparseLossPredictableVarianceLargeHorizonCondition
    (K S T delta : Real) : Prop :=
  4 * (S * Real.log K) <= T ∧
    32 * (5 * K * S * Real.log K ^ 2 * Real.log (5 / delta)) <=
      delta * T ^ 3 ∧
    8 * (K * Real.log (5 / delta)) <= T ∧
    8 * ((Concentration.intervalVarianceProxy 0 1 : NNReal) : Real) *
      Real.log (5 / delta) <= T

/-- All-horizon threshold for the sparse-loss predictable-variance route:
use the explicit large-horizon rate in its valid regime and `T + 1`
otherwise. -/
noncomputable def sparseLossPredictableVarianceAllHorizonRegretThreshold
    {Action : Type v} (arms : Finset Action) (horizon sparsity : Nat)
    (delta : Real) : Real := by
  classical
  let gamma := sparseLossPredictableVarianceClippedExplorationRate
    (arms.card : Real) (sparsity : Real) (horizon : Real) delta
  exact if sparseLossPredictableVarianceLargeHorizonCondition
      (arms.card : Real) (sparsity : Real) (horizon : Real) delta then
    sparseLossPredictableVarianceRealizedMarkovExplicitThreshold
      arms gamma horizon sparsity delta
  else
    (horizon : Real) + 1

/-- Generated sparse-loss realized-regret tail for every positive horizon
under the exact eta and clipped gamma schedules. The refined threshold is used
precisely in the four-contract regime; the complementary branch is the
genuine zero-probability `T + 1` fallback. -/
theorem sampledPredictable_allHorizonSparseLossPredictableVarianceRealizedMarkovRegret_tail
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
    (delta : Real) (hdelta : 0 < delta) (hdelta_le_one : delta <= 1)
    (hsparse : ∀ sample t, t < horizon →
      (sampledPredictableLossSupport arms loss t sample).card <= sparsity) :
    let gamma := sparseLossPredictableVarianceClippedExplorationRate
      (arms.card : Real) (sparsity : Real) (horizon : Real) delta
    let eta := sparseLossPredictableVarianceHighProbabilityLearningRate
      arms gamma horizon sparsity delta
    let mu := prior ⊗ₘ sampledImportanceWeightedTrajectoryKernel arms harms
      eta gamma
        (sparseLossPredictableVarianceClippedExplorationRate_pos
          (arms.card : Real) (sparsity : Real) (horizon : Real) delta
          (by exact_mod_cast hcard_two)
          (by exact_mod_cast hsparsity)
          (by exact_mod_cast hhorizon)).le
        (by
          exact
            (sparseLossPredictableVarianceClippedExplorationRate_le_half
              (arms.card : Real) (sparsity : Real) (horizon : Real)
                delta).trans (by norm_num))
        loss.environment
    mu {sample |
        sparseLossPredictableVarianceAllHorizonRegretThreshold
            arms horizon sparsity delta <=
          (Finset.range horizon).sum (fun t =>
              sampledTrajectoryRealizedLossAt t sample) -
            (Finset.range horizon).sum (fun t =>
              predictableLossAt loss t sample comparator)} <=
      ENNReal.ofReal delta := by
  dsimp only
  classical
  by_cases hlarge : sparseLossPredictableVarianceLargeHorizonCondition
      (arms.card : Real) (sparsity : Real) (horizon : Real) delta
  · rw [sparseLossPredictableVarianceAllHorizonRegretThreshold,
      if_pos hlarge]
    exact
      sampledPredictable_explicitSparseLossPredictableVarianceRealizedMarkovRegret_tail
        prior arms harms hcard_two loss comparator hcomparator horizon sparsity
          hhorizon hsparsity delta hdelta hdelta_le_one hlarge.1 hlarge.2.1
            hlarge.2.2.1 hlarge.2.2.2 hsparse
  · rw [sparseLossPredictableVarianceAllHorizonRegretThreshold,
      if_neg hlarge]
    exact sampledPredictable_trivialRealizedRegret_tail
      prior arms harms
        (sparseLossPredictableVarianceHighProbabilityLearningRate
          arms
            (sparseLossPredictableVarianceClippedExplorationRate
              (arms.card : Real) (sparsity : Real) (horizon : Real) delta)
            horizon sparsity delta)
        (sparseLossPredictableVarianceClippedExplorationRate
          (arms.card : Real) (sparsity : Real) (horizon : Real) delta)
        (sparseLossPredictableVarianceClippedExplorationRate_pos
          (arms.card : Real) (sparsity : Real) (horizon : Real) delta
          (by exact_mod_cast hcard_two)
          (by exact_mod_cast hsparsity)
          (by exact_mod_cast hhorizon)).le
        (by
          exact
            (sparseLossPredictableVarianceClippedExplorationRate_le_half
              (arms.card : Real) (sparsity : Real) (horizon : Real)
                delta).trans (by norm_num))
        loss comparator horizon delta

end BanditRLProof.Exp3
