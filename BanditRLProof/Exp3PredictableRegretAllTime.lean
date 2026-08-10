import BanditRLProof.ConcentrationConfidenceSchedule
import BanditRLProof.Exp3HighProbabilityRegret

/-!
# All-time predictable EXP3 regret

This module gives every positive prefix of one fixed generated EXP3 process a
geometric confidence share and reuses the compiled fixed-horizon pathwise
potential, exploration, and comparator assembly. The result is countable
outer-measure subadditivity, not a Ville/Doob, mixture, optional-stopping,
self-normalized, general Freedman, or tuned horizon-free EXP3 theorem.
-/

namespace BanditRLProof.Exp3

open MeasureTheory ProbabilityTheory
open scoped ENNReal

universe u v

/-- The fixed-horizon predictable-regret budget at prefix `n+1`. The outer
geometric share is divided by two because the parent total-delta theorem
allocates equal shares to its pure-cross and comparator-estimator events. -/
noncomputable def sampledPredictableRegretGeometricAllTimeBudget
    {Action : Type v} (arms : Finset Action) (eta gamma delta : Real)
    (n : Nat) : Real :=
  sampledPredictableHighProbabilityRegretBudget arms eta gamma (n + 1)
    (Concentration.geometricConfidenceShare delta n / 2)

/-- Countable predictable-regret failure event over every positive prefix of
one generated EXP3 trajectory. -/
noncomputable def sampledPredictableRegretGeometricAllTimeFailureSet
    {Env : Type u} {Action : Type v}
    [MeasurableSpace Env] [MeasurableSpace Action] [DecidableEq Action]
    (arms : Finset Action) (eta gamma : Real)
    (loss : PredictableLossVector Env Action) (comparator : Action)
    (delta : Real) : Set (Env × ((k : Nat) -> Action × Real)) :=
  ⋃ n, {sample |
      sampledPredictableRegretGeometricAllTimeBudget
            arms eta gamma delta n <=
          (Finset.range (n + 1)).sum (fun t =>
            sampledTrajectoryExploredPredictableLossAt
              arms eta gamma loss t sample) -
        (Finset.range (n + 1)).sum (fun t =>
          predictableLossAt loss t sample comparator)}

/-- Membership is predictable-regret failure at at least one positive
prefix. -/
theorem mem_sampledPredictableRegretGeometricAllTimeFailureSet_iff
    {Env : Type u} {Action : Type v}
    [MeasurableSpace Env] [MeasurableSpace Action] [DecidableEq Action]
    (arms : Finset Action) (eta gamma : Real)
    (loss : PredictableLossVector Env Action) (comparator : Action)
    (delta : Real) (sample : Env × ((k : Nat) -> Action × Real)) :
    sample ∈ sampledPredictableRegretGeometricAllTimeFailureSet
        arms eta gamma loss comparator delta ↔
      ∃ n,
        sampledPredictableRegretGeometricAllTimeBudget
              arms eta gamma delta n <=
            (Finset.range (n + 1)).sum (fun t =>
              sampledTrajectoryExploredPredictableLossAt
                arms eta gamma loss t sample) -
          (Finset.range (n + 1)).sum (fun t =>
            predictableLossAt loss t sample comparator) := by
  simp [sampledPredictableRegretGeometricAllTimeFailureSet]

/-- On one fixed generated EXP3 process and against one fixed supported
comparator, predictable-regret failures over all positive prefixes have outer
measure at most the geometric confidence budget. -/
theorem measure_sampledPredictableRegretGeometricAllTimeFailureSet_le
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
    (delta : Real) (hdelta : 0 < delta) :
    let mu := prior ⊗ₘ sampledImportanceWeightedTrajectoryKernel arms harms
      eta gamma hgamma_pos.le hgamma_lt_one.le loss.environment
    mu (sampledPredictableRegretGeometricAllTimeFailureSet
        arms eta gamma loss comparator delta) <= ENNReal.ofReal delta := by
  dsimp only
  let mu := prior ⊗ₘ sampledImportanceWeightedTrajectoryKernel arms harms
    eta gamma hgamma_pos.le hgamma_lt_one.le loss.environment
  calc
    mu (sampledPredictableRegretGeometricAllTimeFailureSet
        arms eta gamma loss comparator delta) <=
        ∑' n, mu {sample |
          sampledPredictableRegretGeometricAllTimeBudget
                arms eta gamma delta n <=
              (Finset.range (n + 1)).sum (fun t =>
                sampledTrajectoryExploredPredictableLossAt
                  arms eta gamma loss t sample) -
            (Finset.range (n + 1)).sum (fun t =>
              predictableLossAt loss t sample comparator)} := by
      unfold sampledPredictableRegretGeometricAllTimeFailureSet
      exact MeasureTheory.measure_iUnion_le _
    _ <= ∑' n, ENNReal.ofReal
        (Concentration.geometricConfidenceShare delta n) := by
      apply ENNReal.tsum_le_tsum
      intro n
      have h := sampledPredictable_highProbabilityRegret_tail_total_delta
        prior arms harms eta gamma heta hgamma_pos hgamma_lt_one loss
          comparator hcomparator (n + 1) (Nat.succ_pos n)
          (Concentration.geometricConfidenceShare delta n)
          (Concentration.geometricConfidenceShare_pos hdelta n)
      dsimp only at h
      simpa [mu, sampledPredictableRegretGeometricAllTimeBudget] using h
    _ = ENNReal.ofReal delta :=
      Concentration.tsum_ofReal_geometricConfidenceShare hdelta.le

end BanditRLProof.Exp3
