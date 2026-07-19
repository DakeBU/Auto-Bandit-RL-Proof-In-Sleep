import BanditRLProof.Exp3HighProbabilityRegret
import BanditRLProof.Exp3RealizedConfidence

/-!
# Generated realized EXP3 high-probability regret

This module composes the generated predictable EXP3 high-probability theorem
with the one-sided realized-minus-exploration-mixed deviation tail. The primary
endpoint controls the scalar loss stored in the generated trajectory, with the
requested total failure probability split equally across the pure-q,
comparator-estimator, and realized-deviation events.

The theorem inherits the range-based importance-weighted confidence radii from
the predictable route. It is therefore a valid realized selected-loss theorem,
but it is not presented as the ideal EXP3.P/Freedman rate.
-/

namespace BanditRLProof.Exp3

open MeasureTheory ProbabilityTheory

universe u v

noncomputable def sampledPredictableRealizedHighProbabilityRegretBudget
    {Action : Type v} (arms : Finset Action) (eta gamma : Real)
    (horizon : Nat) (delta : Real) : Real :=
  sampledPredictableHighProbabilityRegretBudget
      arms eta gamma horizon delta +
    sampledPredictableRealizedDeviationConfidenceRadius horizon delta

/-- Raw three-event form of the generated realized EXP3 regret theorem. The
same `delta` is used for the pure-q, comparator-estimator, and realized
deviation tails, so the displayed failure probability is their three-term
sum. -/
theorem sampledPredictable_realizedHighProbabilityRegret_tail_delta
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
    (delta : Real) (hdelta : 0 < delta) :
    let mu := prior ⊗ₘ sampledImportanceWeightedTrajectoryKernel arms harms
      eta gamma hgamma_pos.le hgamma_lt_one.le loss.environment
    mu {sample |
        sampledPredictableRealizedHighProbabilityRegretBudget
            arms eta gamma horizon delta <=
          (Finset.range horizon).sum (fun t =>
              sampledTrajectoryRealizedLossAt t sample) -
            (Finset.range horizon).sum (fun t =>
              predictableLossAt loss t sample comparator)} <=
      (ENNReal.ofReal delta + ENNReal.ofReal delta) + ENNReal.ofReal delta := by
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
  let predictableBudget := sampledPredictableHighProbabilityRegretBudget
    arms eta gamma horizon delta
  let realizedRadius :=
    sampledPredictableRealizedDeviationConfidenceRadius horizon delta
  let predictableBad : Set (Env × ((k : Nat) -> Action × Real)) :=
    {sample | predictableBudget <= predictableRegret sample}
  let realizedBad : Set (Env × ((k : Nat) -> Action × Real)) :=
    {sample | realizedRadius <= realizedDeviation sample}
  have hpredictableTail :
      mu predictableBad <= ENNReal.ofReal delta + ENNReal.ofReal delta := by
    have h := sampledPredictable_highProbabilityRegret_tail_delta
      prior arms harms eta gamma heta hgamma_pos hgamma_lt_one loss comparator
        hcomparator horizon hhorizon delta hdelta
    dsimp only at h
    simpa [mu, predictableBad, predictableBudget, predictableRegret] using h
  have hrealizedTail : mu realizedBad <= ENNReal.ofReal delta := by
    have h := sampledPredictableRealizedDeviation_sum_tail_delta
      prior arms harms eta gamma hgamma_pos.le hgamma_lt_one.le loss horizon
        hhorizon delta hdelta
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
        predictableBudget + realizedRadius <= realizedRegret sample} ⊆
        predictableBad ∪ realizedBad := by
    intro sample hregret
    by_cases hpredictable : sample ∈ predictableBad
    · exact Or.inl hpredictable
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
        predictableBudget + realizedRadius <= realizedRegret sample := hregret
    rw [hdecomp sample] at hregret'
    linarith
  calc
    mu {sample |
        sampledPredictableRealizedHighProbabilityRegretBudget
            arms eta gamma horizon delta <=
          (Finset.range horizon).sum (fun t =>
              sampledTrajectoryRealizedLossAt t sample) -
            (Finset.range horizon).sum (fun t =>
              predictableLossAt loss t sample comparator)} <=
        mu (predictableBad ∪ realizedBad) := by
      apply measure_mono
      simpa [sampledPredictableRealizedHighProbabilityRegretBudget,
        predictableBudget, realizedRadius, realizedRegret, mu] using hsubset
    _ <= mu predictableBad + mu realizedBad := measure_union_le _ _
    _ <= (ENNReal.ofReal delta + ENNReal.ofReal delta) +
          ENNReal.ofReal delta :=
      add_le_add hpredictableTail hrealizedTail

/-- Standard total-failure-probability form of generated realized EXP3 regret.
Each of the three underlying confidence events receives `delta / 3`. -/
theorem sampledPredictable_realizedHighProbabilityRegret_tail_total_delta
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
    (delta : Real) (hdelta : 0 < delta) :
    let mu := prior ⊗ₘ sampledImportanceWeightedTrajectoryKernel arms harms
      eta gamma hgamma_pos.le hgamma_lt_one.le loss.environment
    mu {sample |
        sampledPredictableRealizedHighProbabilityRegretBudget
            arms eta gamma horizon (delta / 3) <=
          (Finset.range horizon).sum (fun t =>
              sampledTrajectoryRealizedLossAt t sample) -
            (Finset.range horizon).sum (fun t =>
              predictableLossAt loss t sample comparator)} <=
      ENNReal.ofReal delta := by
  have hthird_pos : 0 < delta / 3 := div_pos hdelta (by norm_num)
  have h := sampledPredictable_realizedHighProbabilityRegret_tail_delta
    prior arms harms eta gamma heta hgamma_pos hgamma_lt_one loss comparator
      hcomparator horizon hhorizon (delta / 3) hthird_pos
  dsimp only at h ⊢
  have hthird_nonneg : 0 <= delta / 3 := hthird_pos.le
  have hprob :
      (ENNReal.ofReal (delta / 3) + ENNReal.ofReal (delta / 3)) +
          ENNReal.ofReal (delta / 3) = ENNReal.ofReal delta := by
    rw [← ENNReal.ofReal_add hthird_nonneg hthird_nonneg]
    rw [← ENNReal.ofReal_add (add_nonneg hthird_nonneg hthird_nonneg)
      hthird_nonneg]
    congr 1
    ring
  exact h.trans_eq hprob

end BanditRLProof.Exp3
