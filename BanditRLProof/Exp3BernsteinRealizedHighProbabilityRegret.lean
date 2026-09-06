import BanditRLProof.Exp3BernsteinHighProbabilityRegret
import BanditRLProof.Exp3RealizedConfidence

/-!
# Generated realized EXP3 regret with Bernstein predictable confidence

This module composes the generated predictable Bernstein-radius EXP3 theorem
with the one-sided realized-minus-exploration deviation tail. The two
importance-weighted confidence events use the variance-sensitive fixed-tilt
route; the realized-deviation event retains its bounded-loss Hoeffding/Azuma
radius. The deterministic Hedge-square contribution also remains unchanged.

Thus the endpoint controls generated selected scalar loss, but it is not a
general Freedman theorem or an ideal tuned EXP3.P rate.
-/

namespace BanditRLProof.Exp3

open MeasureTheory ProbabilityTheory

universe u v

/-- Realized selected-loss regret budget whose predictable component uses the
two variance-sensitive Bernstein confidence radii. -/
noncomputable def sampledPredictableBernsteinRealizedHighProbabilityRegretBudget
    {Action : Type v} (arms : Finset Action) (eta gamma : Real)
    (horizon : Nat) (delta : Real) : Real :=
  sampledPredictableBernsteinHighProbabilityRegretBudget
      arms eta gamma horizon delta +
    sampledPredictableRealizedDeviationConfidenceRadius horizon delta

/-- Raw three-event form. The predictable component contributes the pure-cross
and fixed-comparator Bernstein events, while the third event is the bounded
realized-minus-predictable deviation. -/
theorem sampledPredictable_bernsteinRealizedHighProbabilityRegret_tail_delta
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
        sampledPredictableBernsteinRealizedHighProbabilityRegretBudget
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
  let predictableBudget :=
    sampledPredictableBernsteinHighProbabilityRegretBudget
      arms eta gamma horizon delta
  let realizedRadius :=
    sampledPredictableRealizedDeviationConfidenceRadius horizon delta
  let predictableBad : Set (Env × ((k : Nat) -> Action × Real)) :=
    {sample | predictableBudget <= predictableRegret sample}
  let realizedBad : Set (Env × ((k : Nat) -> Action × Real)) :=
    {sample | realizedRadius <= realizedDeviation sample}
  have hpredictableTail :
      mu predictableBad <= ENNReal.ofReal delta + ENNReal.ofReal delta := by
    have h := sampledPredictable_bernsteinHighProbabilityRegret_tail_delta
      prior arms harms eta gamma heta hgamma_pos hgamma_lt_one loss comparator
        hcomparator horizon delta hdelta
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
        sampledPredictableBernsteinRealizedHighProbabilityRegretBudget
            arms eta gamma horizon delta <=
          (Finset.range horizon).sum (fun t =>
              sampledTrajectoryRealizedLossAt t sample) -
            (Finset.range horizon).sum (fun t =>
              predictableLossAt loss t sample comparator)} <=
        mu (predictableBad ∪ realizedBad) := by
      apply measure_mono
      simpa [sampledPredictableBernsteinRealizedHighProbabilityRegretBudget,
        predictableBudget, realizedRadius, realizedRegret, mu] using hsubset
    _ <= mu predictableBad + mu realizedBad := measure_union_le _ _
    _ <= (ENNReal.ofReal delta + ENNReal.ofReal delta) +
          ENNReal.ofReal delta :=
      add_le_add hpredictableTail hrealizedTail

/-- Total-failure form: the pure-cross Bernstein, fixed-comparator Bernstein,
and realized-deviation events each receive `delta / 3`. -/
theorem sampledPredictable_bernsteinRealizedHighProbabilityRegret_tail_total_delta
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
        sampledPredictableBernsteinRealizedHighProbabilityRegretBudget
            arms eta gamma horizon (delta / 3) <=
          (Finset.range horizon).sum (fun t =>
              sampledTrajectoryRealizedLossAt t sample) -
            (Finset.range horizon).sum (fun t =>
              predictableLossAt loss t sample comparator)} <=
      ENNReal.ofReal delta := by
  have hthird_pos : 0 < delta / 3 := div_pos hdelta (by norm_num)
  have h :=
    sampledPredictable_bernsteinRealizedHighProbabilityRegret_tail_delta
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
