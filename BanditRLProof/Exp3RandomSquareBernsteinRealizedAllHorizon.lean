import BanditRLProof.Exp3RandomSquareBernsteinRealizedExplicitTuning
import BanditRLProof.Exp3BernsteinAllHorizon

/-!
# All-horizon random-square realized EXP3 route

The explicit random-square schedule has its refined threshold when two
large-horizon inequalities make clipping inactive.  Outside that regime this
module reuses the compiled almost-sure horizon bound and a strict `T + 1`
threshold.  The result covers every positive horizon without asserting cubic
or quadratic dominance on the active-clipping branch.
-/

namespace BanditRLProof.Exp3

open MeasureTheory ProbabilityTheory

universe u v

/-- The regime in which the explicit random-square exploration schedule
satisfies both confidence dominance contracts without activating its clip. -/
def randomSquareBernsteinLargeHorizonCondition
    (K T delta : Real) : Prop :=
  8 * (K * Real.log (4 / delta)) <= T ∧
    8 * ((Concentration.intervalVarianceProxy 0 1 : NNReal) : Real) *
      Real.log (4 / delta) <= T

/-- All-horizon threshold for the random-square route: use the explicit
large-horizon rate in its valid regime and `T + 1` otherwise. -/
noncomputable def randomSquareBernsteinAllHorizonRegretThreshold
    {Action : Type v} (arms : Finset Action) (horizon : Nat)
    (delta : Real) : Real := by
  classical
  let gamma := randomSquareBernsteinClippedExplorationRate
    (arms.card : Real) (horizon : Real) delta
  exact if randomSquareBernsteinLargeHorizonCondition
      (arms.card : Real) (horizon : Real) delta then
    randomSquareBernsteinRealizedExplicitThreshold arms gamma horizon delta
  else
    (horizon : Real) + 1

/-- Generated realized-regret tail for every positive horizon under the
random-square learning rate and clipped exploration schedule.  The refined
threshold is used exactly in the two-contract large-horizon regime; the other
branch is the genuine zero-probability `T + 1` fallback. -/
theorem sampledPredictable_allHorizonRandomSquareBernsteinRealizedRegret_tail
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
    let gamma := randomSquareBernsteinClippedExplorationRate
      (arms.card : Real) (horizon : Real) delta
    let eta := randomSquareHighProbabilityLearningRate
      (arms.card : Real) (horizon : Real) delta
    let mu := prior ⊗ₘ sampledImportanceWeightedTrajectoryKernel arms harms
      eta gamma
        (randomSquareBernsteinClippedExplorationRate_pos
          (arms.card : Real) (horizon : Real) delta
          (by positivity) (by exact_mod_cast hhorizon) hdelta hdelta_le_one).le
        (by
          exact (randomSquareBernsteinClippedExplorationRate_le_half
            (arms.card : Real) (horizon : Real) delta).trans (by norm_num))
        loss.environment
    mu {sample |
        randomSquareBernsteinAllHorizonRegretThreshold
            arms horizon delta <=
          (Finset.range horizon).sum (fun t =>
              sampledTrajectoryRealizedLossAt t sample) -
            (Finset.range horizon).sum (fun t =>
              predictableLossAt loss t sample comparator)} <=
      ENNReal.ofReal delta := by
  dsimp only
  classical
  by_cases hlarge : randomSquareBernsteinLargeHorizonCondition
      (arms.card : Real) (horizon : Real) delta
  · rw [randomSquareBernsteinAllHorizonRegretThreshold, if_pos hlarge]
    exact
      sampledPredictable_explicitRandomSquareBernsteinRealizedRegret_tail
        prior arms harms hcard_two loss comparator hcomparator horizon hhorizon
          delta hdelta hdelta_le_one hlarge.1 hlarge.2
  · rw [randomSquareBernsteinAllHorizonRegretThreshold, if_neg hlarge]
    exact sampledPredictable_trivialRealizedRegret_tail
      prior arms harms
        (randomSquareHighProbabilityLearningRate
          (arms.card : Real) (horizon : Real) delta)
        (randomSquareBernsteinClippedExplorationRate
          (arms.card : Real) (horizon : Real) delta)
        (randomSquareBernsteinClippedExplorationRate_pos
          (arms.card : Real) (horizon : Real) delta
          (by positivity) (by exact_mod_cast hhorizon) hdelta hdelta_le_one).le
        (by
          exact (randomSquareBernsteinClippedExplorationRate_le_half
            (arms.card : Real) (horizon : Real) delta).trans (by norm_num))
        loss comparator horizon delta

end BanditRLProof.Exp3
