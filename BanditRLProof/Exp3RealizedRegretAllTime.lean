import BanditRLProof.Exp3PredictableRegretAllTime
import BanditRLProof.Exp3RealizedDeviationAllTime

/-!
# All-time realized EXP3 regret

This module combines the accepted same-process predictable-regret and pure
realized-deviation all-time events. The total confidence budget is split
equally between those two event families. The result is an outer-measure
bound for realized selected-loss regret at every positive prefix, with fixed
process parameters and one fixed supported comparator.
-/

namespace BanditRLProof.Exp3

open MeasureTheory ProbabilityTheory
open scoped ENNReal

universe u v

/-- Exact finite-prefix decomposition of realized selected-loss regret into
exploration-mixed predictable regret and realized deviation. -/
theorem sampledTrajectoryRealizedRegret_eq_predictableRegret_add_realizedDeviation
    {Env : Type u} {Action : Type v}
    [MeasurableSpace Env] [MeasurableSpace Action] [DecidableEq Action]
    (arms : Finset Action) (eta gamma : Real)
    (loss : PredictableLossVector Env Action) (comparator : Action)
    (horizon : Nat) (sample : Env × ((k : Nat) -> Action × Real)) :
    (Finset.range horizon).sum (fun t =>
        sampledTrajectoryRealizedLossAt t sample) -
      (Finset.range horizon).sum (fun t =>
        predictableLossAt loss t sample comparator) =
      ((Finset.range horizon).sum (fun t =>
          sampledTrajectoryExploredPredictableLossAt
            arms eta gamma loss t sample) -
        (Finset.range horizon).sum (fun t =>
          predictableLossAt loss t sample comparator)) +
      (Finset.range horizon).sum (fun t =>
        sampledTrajectoryRealizedDeviationAt
          arms eta gamma loss t sample) := by
  simp only [sampledTrajectoryRealizedDeviationAt, Finset.sum_sub_distrib]
  ring

/-- At prefix `n+1`, add the predictable-regret and pure realized-deviation
schedules after assigning half of the total confidence budget to each event
family. -/
noncomputable def sampledRealizedRegretGeometricAllTimeBudget
    {Action : Type v} (arms : Finset Action) (eta gamma delta : Real)
    (n : Nat) : Real :=
  sampledPredictableRegretGeometricAllTimeBudget
      arms eta gamma (delta / 2) n +
    sampledRealizedDeviationGeometricAllTimeRadius (delta / 2) n

/-- Countable realized selected-loss regret failure event over every positive
prefix of one generated EXP3 trajectory. -/
noncomputable def sampledRealizedRegretGeometricAllTimeFailureSet
    {Env : Type u} {Action : Type v}
    [MeasurableSpace Env] [MeasurableSpace Action] [DecidableEq Action]
    (arms : Finset Action) (eta gamma : Real)
    (loss : PredictableLossVector Env Action) (comparator : Action)
    (delta : Real) : Set (Env × ((k : Nat) -> Action × Real)) :=
  ⋃ n, {sample |
    sampledRealizedRegretGeometricAllTimeBudget
          arms eta gamma delta n <=
        (Finset.range (n + 1)).sum (fun t =>
            sampledTrajectoryRealizedLossAt t sample) -
          (Finset.range (n + 1)).sum (fun t =>
            predictableLossAt loss t sample comparator)}

/-- Membership is realized selected-loss regret failure at at least one
positive prefix. -/
theorem mem_sampledRealizedRegretGeometricAllTimeFailureSet_iff
    {Env : Type u} {Action : Type v}
    [MeasurableSpace Env] [MeasurableSpace Action] [DecidableEq Action]
    (arms : Finset Action) (eta gamma : Real)
    (loss : PredictableLossVector Env Action) (comparator : Action)
    (delta : Real) (sample : Env × ((k : Nat) -> Action × Real)) :
    sample ∈ sampledRealizedRegretGeometricAllTimeFailureSet
        arms eta gamma loss comparator delta ↔
      ∃ n,
        sampledRealizedRegretGeometricAllTimeBudget
              arms eta gamma delta n <=
            (Finset.range (n + 1)).sum (fun t =>
                sampledTrajectoryRealizedLossAt t sample) -
              (Finset.range (n + 1)).sum (fun t =>
                predictableLossAt loss t sample comparator) := by
  simp [sampledRealizedRegretGeometricAllTimeFailureSet]

/-- A combined realized-regret crossing forces either a predictable-regret
crossing or a pure realized-deviation crossing at the same prefix. -/
theorem sampledRealizedRegretGeometricAllTimeFailureSet_subset
    {Env : Type u} {Action : Type v}
    [MeasurableSpace Env] [MeasurableSpace Action] [DecidableEq Action]
    (arms : Finset Action) (eta gamma : Real)
    (loss : PredictableLossVector Env Action) (comparator : Action)
    (delta : Real) :
    sampledRealizedRegretGeometricAllTimeFailureSet
        arms eta gamma loss comparator delta ⊆
      sampledPredictableRegretGeometricAllTimeFailureSet
          arms eta gamma loss comparator (delta / 2) ∪
        sampledRealizedDeviationGeometricAllTimeFailureSet
          arms eta gamma loss (delta / 2) := by
  intro sample hsample
  rw [mem_sampledRealizedRegretGeometricAllTimeFailureSet_iff] at hsample
  obtain ⟨n, hregret⟩ := hsample
  by_cases hpredictable :
      sample ∈ sampledPredictableRegretGeometricAllTimeFailureSet
        arms eta gamma loss comparator (delta / 2)
  · exact Or.inl hpredictable
  by_cases hdeviation :
      sample ∈ sampledRealizedDeviationGeometricAllTimeFailureSet
        arms eta gamma loss (delta / 2)
  · exact Or.inr hdeviation
  exfalso
  rw [mem_sampledPredictableRegretGeometricAllTimeFailureSet_iff] at hpredictable
  rw [mem_sampledRealizedDeviationGeometricAllTimeFailureSet_iff] at hdeviation
  have hpredictableGood :
      (Finset.range (n + 1)).sum (fun t =>
          sampledTrajectoryExploredPredictableLossAt
            arms eta gamma loss t sample) -
        (Finset.range (n + 1)).sum (fun t =>
          predictableLossAt loss t sample comparator) <
      sampledPredictableRegretGeometricAllTimeBudget
        arms eta gamma (delta / 2) n := by
    apply lt_of_not_ge
    intro hcross
    exact hpredictable ⟨n, hcross⟩
  have hdeviationGood :
      (Finset.range (n + 1)).sum (fun t =>
          sampledTrajectoryRealizedDeviationAt
            arms eta gamma loss t sample) <
        sampledRealizedDeviationGeometricAllTimeRadius (delta / 2) n := by
    apply lt_of_not_ge
    intro hcross
    exact hdeviation ⟨n, hcross⟩
  rw [sampledTrajectoryRealizedRegret_eq_predictableRegret_add_realizedDeviation
    arms eta gamma loss comparator (n + 1) sample] at hregret
  unfold sampledRealizedRegretGeometricAllTimeBudget at hregret
  linarith

/-- On one fixed generated EXP3 process and against one fixed supported
comparator, realized selected-loss regret stays below the sum of the scheduled
predictable-regret and realized-deviation budgets at every positive prefix,
outside a set of outer measure at most the total confidence budget. -/
theorem measure_sampledRealizedRegretGeometricAllTimeFailureSet_le
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
    mu (sampledRealizedRegretGeometricAllTimeFailureSet
        arms eta gamma loss comparator delta) <= ENNReal.ofReal delta := by
  dsimp only
  let mu := prior ⊗ₘ sampledImportanceWeightedTrajectoryKernel arms harms
    eta gamma hgamma_pos.le hgamma_lt_one.le loss.environment
  have hpredictable :=
    measure_sampledPredictableRegretGeometricAllTimeFailureSet_le
      prior arms harms eta gamma heta hgamma_pos hgamma_lt_one loss comparator
        hcomparator (delta / 2) (half_pos hdelta)
  have hdeviation :=
    measure_sampledRealizedDeviationGeometricAllTimeFailureSet_le
      prior arms harms eta gamma hgamma_pos hgamma_lt_one.le loss
        (delta / 2) (half_pos hdelta)
  dsimp only at hpredictable hdeviation
  calc
    mu (sampledRealizedRegretGeometricAllTimeFailureSet
        arms eta gamma loss comparator delta) <=
        mu (sampledPredictableRegretGeometricAllTimeFailureSet
              arms eta gamma loss comparator (delta / 2) ∪
            sampledRealizedDeviationGeometricAllTimeFailureSet
              arms eta gamma loss (delta / 2)) := by
      exact measure_mono
        (sampledRealizedRegretGeometricAllTimeFailureSet_subset
          arms eta gamma loss comparator delta)
    _ <=
        mu (sampledPredictableRegretGeometricAllTimeFailureSet
              arms eta gamma loss comparator (delta / 2)) +
          mu (sampledRealizedDeviationGeometricAllTimeFailureSet
              arms eta gamma loss (delta / 2)) := measure_union_le _ _
    _ <= ENNReal.ofReal (delta / 2) + ENNReal.ofReal (delta / 2) :=
      add_le_add hpredictable hdeviation
    _ = ENNReal.ofReal delta := by
      rw [← ENNReal.ofReal_add (half_pos hdelta).le (half_pos hdelta).le,
        add_halves]

end BanditRLProof.Exp3
