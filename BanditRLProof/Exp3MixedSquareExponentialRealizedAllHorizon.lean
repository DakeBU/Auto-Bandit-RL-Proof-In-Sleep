import BanditRLProof.Exp3MixedSquareExponentialRealizedExplicitTuning
import BanditRLProof.Exp3BernsteinAllHorizon

/-!
# All-horizon exponential mixed-square realized EXP3 route

The explicit exponential-square schedule has its refined `14 * gamma * T`
threshold when four horizon inequalities make clipping inactive. Outside that
regime this module reuses the compiled almost-sure horizon bound and the strict
`T + 1` zero-probability threshold. The fallback closes the active-clipping
presentation without claiming a sharp short-horizon, Freedman, or EXP3.P rate.
-/

namespace BanditRLProof.Exp3

open MeasureTheory ProbabilityTheory

universe u v

/-- The regime in which all four components of the exponential-square
exploration schedule are at most one half. -/
def exponentialSquareBernsteinLargeHorizonCondition
    (K T delta : Real) : Prop :=
  4 * (K * Real.log K) <= T ∧
    64 * (K ^ 2 * Real.log K ^ 2 * Real.log (4 / delta) / 2) <=
      T ^ 3 ∧
    8 * (K * Real.log (4 / delta)) <= T ∧
    8 * ((Concentration.intervalVarianceProxy 0 1 : NNReal) : Real) *
      Real.log (4 / delta) <= T

/-- All-horizon threshold for the exponential-square route: use the explicit
large-horizon rate in its valid regime and `T + 1` otherwise. -/
noncomputable def exponentialSquareBernsteinAllHorizonRegretThreshold
    {Action : Type v} (arms : Finset Action) (horizon : Nat)
    (delta : Real) : Real := by
  classical
  let gamma := exponentialSquareBernsteinClippedExplorationRate
    (arms.card : Real) (horizon : Real) delta
  exact if exponentialSquareBernsteinLargeHorizonCondition
      (arms.card : Real) (horizon : Real) delta then
    exponentialSquareBernsteinRealizedExplicitThreshold
      arms gamma horizon delta
  else
    (horizon : Real) + 1

/-- Generated realized-regret tail for every positive horizon under the exact
exponential-square learning rate and clipped exploration schedule. The refined
threshold is used precisely in the four-contract regime; the complementary
branch is the genuine zero-probability `T + 1` fallback. -/
theorem sampledPredictable_allHorizonExponentialSquareBernsteinRealizedRegret_tail
    {Env : Type u} {Action : Type v}
    [MeasurableSpace Env] [StandardBorelSpace Env] [Nonempty Env]
    [MeasurableSpace Action] [MeasurableSingletonClass Action]
    [StandardBorelSpace Action] [Nonempty Action] [DecidableEq Action]
    (prior : Measure Env) [IsProbabilityMeasure prior]
    (arms : Finset Action) (harms : arms.Nonempty)
    (hcard_two : 2 <= arms.card)
    (loss : PredictableLossVector Env Action)
    (comparator : Action) (hcomparator : comparator ∈ arms)
    (horizon : Nat) (hhorizon : 0 < horizon)
    (delta : Real) (hdelta : 0 < delta) (hdelta_le_one : delta <= 1) :
    let gamma := exponentialSquareBernsteinClippedExplorationRate
      (arms.card : Real) (horizon : Real) delta
    let eta := exponentialSquareHighProbabilityLearningRate
      arms gamma horizon delta
    let mu := prior ⊗ₘ sampledImportanceWeightedTrajectoryKernel arms harms
      eta gamma
        (exponentialSquareBernsteinClippedExplorationRate_pos
          (arms.card : Real) (horizon : Real) delta
          (by exact_mod_cast hcard_two)
          (by exact_mod_cast hhorizon)).le
        (by
          exact (exponentialSquareBernsteinClippedExplorationRate_le_half
            (arms.card : Real) (horizon : Real) delta).trans (by norm_num))
        loss.environment
    mu {sample |
        exponentialSquareBernsteinAllHorizonRegretThreshold
            arms horizon delta <=
          (Finset.range horizon).sum (fun t =>
              sampledTrajectoryRealizedLossAt t sample) -
            (Finset.range horizon).sum (fun t =>
              predictableLossAt loss t sample comparator)} <=
      ENNReal.ofReal delta := by
  dsimp only
  classical
  by_cases hlarge : exponentialSquareBernsteinLargeHorizonCondition
      (arms.card : Real) (horizon : Real) delta
  · rw [exponentialSquareBernsteinAllHorizonRegretThreshold, if_pos hlarge]
    exact
      sampledPredictable_explicitExponentialSquareBernsteinRealizedRegret_tail
        prior arms harms hcard_two loss comparator hcomparator horizon hhorizon
          delta hdelta hdelta_le_one hlarge.1 hlarge.2.1 hlarge.2.2.1
            hlarge.2.2.2
  · rw [exponentialSquareBernsteinAllHorizonRegretThreshold, if_neg hlarge]
    exact sampledPredictable_trivialRealizedRegret_tail
      prior arms harms
        (exponentialSquareHighProbabilityLearningRate
          arms
            (exponentialSquareBernsteinClippedExplorationRate
              (arms.card : Real) (horizon : Real) delta)
            horizon delta)
        (exponentialSquareBernsteinClippedExplorationRate
          (arms.card : Real) (horizon : Real) delta)
        (exponentialSquareBernsteinClippedExplorationRate_pos
          (arms.card : Real) (horizon : Real) delta
          (by exact_mod_cast hcard_two)
          (by exact_mod_cast hhorizon)).le
        (by
          exact (exponentialSquareBernsteinClippedExplorationRate_le_half
            (arms.card : Real) (horizon : Real) delta).trans (by norm_num))
        loss comparator horizon delta

end BanditRLProof.Exp3
