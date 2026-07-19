import BanditRLProof.Exp3MixedSquareExponentialHighProbabilityRegret
import BanditRLProof.Exp3RealizedConfidence

/-!
# Generated realized EXP3 regret with exponential mixed-square confidence

This module composes the generated predictable exponential-square Bernstein
result with the one-sided realized-minus-exploration deviation tail. The
resulting four-event route controls generated selected scalar loss while
replacing the Markov estimator-square threshold by logarithmic confidence.

The square radius still uses the interval proxy of order
`(|arms| / gamma)^2`, and the realized deviation retains its bounded-loss
Hoeffding/Azuma radius. This is not a Freedman or ideal EXP3.P theorem.
-/

namespace BanditRLProof.Exp3

open MeasureTheory ProbabilityTheory

universe u v

/-- Realized selected-loss regret budget whose predictable component uses the
exponential mixed estimator-square event and two Bernstein confidence radii. -/
noncomputable def sampledPredictableExponentialSquareBernsteinRealizedHighProbabilityRegretBudget
    {Action : Type v} (arms : Finset Action) (eta gamma : Real)
    (horizon : Nat) (deltaSquare deltaConfidence deltaRealized : Real) : Real :=
  sampledPredictableExponentialSquareBernsteinHighProbabilityRegretBudget
      arms eta gamma horizon deltaSquare deltaConfidence +
    sampledPredictableRealizedDeviationConfidenceRadius horizon deltaRealized

/-- Raw four-event form. The predictable component contributes the exponential
estimator-square event and two Bernstein confidence events; the fourth event is
the bounded realized-minus-predictable deviation. -/
theorem sampledPredictable_exponentialSquareBernsteinRealizedHighProbabilityRegret_tail
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
    (deltaSquare deltaConfidence deltaRealized : Real)
    (hdeltaSquare : 0 < deltaSquare)
    (hdeltaConfidence : 0 < deltaConfidence)
    (hdeltaRealized : 0 < deltaRealized) :
    let mu := prior ⊗ₘ sampledImportanceWeightedTrajectoryKernel arms harms
      eta gamma hgamma_pos.le hgamma_lt_one.le loss.environment
    mu {sample |
        sampledPredictableExponentialSquareBernsteinRealizedHighProbabilityRegretBudget
            arms eta gamma horizon deltaSquare deltaConfidence deltaRealized <=
          (Finset.range horizon).sum (fun t =>
              sampledTrajectoryRealizedLossAt t sample) -
            (Finset.range horizon).sum (fun t =>
              predictableLossAt loss t sample comparator)} <=
      ((ENNReal.ofReal deltaSquare + ENNReal.ofReal deltaConfidence) +
        ENNReal.ofReal deltaConfidence) + ENNReal.ofReal deltaRealized := by
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
    sampledPredictableExponentialSquareBernsteinHighProbabilityRegretBudget
      arms eta gamma horizon deltaSquare deltaConfidence
  let realizedRadius :=
    sampledPredictableRealizedDeviationConfidenceRadius horizon deltaRealized
  let predictableBad : Set (Env × ((k : Nat) -> Action × Real)) :=
    {sample | predictableBudget <= predictableRegret sample}
  let realizedBad : Set (Env × ((k : Nat) -> Action × Real)) :=
    {sample | realizedRadius <= realizedDeviation sample}
  have hpredictableTail :
      mu predictableBad <=
        (ENNReal.ofReal deltaSquare + ENNReal.ofReal deltaConfidence) +
          ENNReal.ofReal deltaConfidence := by
    have h := sampledPredictable_exponentialSquareBernsteinHighProbabilityRegret_tail
      prior arms harms eta gamma heta hgamma_pos hgamma_lt_one loss comparator
        hcomparator horizon hhorizon deltaSquare deltaConfidence
          hdeltaSquare hdeltaConfidence
    dsimp only at h
    simpa [mu, predictableBad, predictableBudget, predictableRegret] using h
  have hrealizedTail : mu realizedBad <= ENNReal.ofReal deltaRealized := by
    have h := sampledPredictableRealizedDeviation_sum_tail_delta
      prior arms harms eta gamma hgamma_pos.le hgamma_lt_one.le loss horizon
        hhorizon deltaRealized hdeltaRealized
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
        sampledPredictableExponentialSquareBernsteinRealizedHighProbabilityRegretBudget
            arms eta gamma horizon deltaSquare deltaConfidence deltaRealized <=
          (Finset.range horizon).sum (fun t =>
              sampledTrajectoryRealizedLossAt t sample) -
            (Finset.range horizon).sum (fun t =>
              predictableLossAt loss t sample comparator)} <=
        mu (predictableBad ∪ realizedBad) := by
      apply measure_mono
      simpa [
        sampledPredictableExponentialSquareBernsteinRealizedHighProbabilityRegretBudget,
        predictableBudget, realizedRadius, realizedRegret, mu] using hsubset
    _ <= mu predictableBad + mu realizedBad := measure_union_le _ _
    _ <= ((ENNReal.ofReal deltaSquare + ENNReal.ofReal deltaConfidence) +
          ENNReal.ofReal deltaConfidence) + ENNReal.ofReal deltaRealized :=
      add_le_add hpredictableTail hrealizedTail

/-- Total-failure form: the exponential square, pure-cross Bernstein,
fixed-comparator Bernstein, and realized-deviation events each receive
`delta / 4`. -/
theorem sampledPredictable_exponentialSquareBernsteinRealizedHighProbabilityRegret_tail_total_delta
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
        sampledPredictableExponentialSquareBernsteinRealizedHighProbabilityRegretBudget
            arms eta gamma horizon (delta / 4) (delta / 4) (delta / 4) <=
          (Finset.range horizon).sum (fun t =>
              sampledTrajectoryRealizedLossAt t sample) -
            (Finset.range horizon).sum (fun t =>
              predictableLossAt loss t sample comparator)} <=
      ENNReal.ofReal delta := by
  have hquarter_pos : 0 < delta / 4 := div_pos hdelta (by norm_num)
  have h :=
    sampledPredictable_exponentialSquareBernsteinRealizedHighProbabilityRegret_tail
      prior arms harms eta gamma heta hgamma_pos hgamma_lt_one loss comparator
        hcomparator horizon hhorizon (delta / 4) (delta / 4) (delta / 4)
          hquarter_pos hquarter_pos hquarter_pos
  dsimp only at h ⊢
  have hquarter_nonneg : 0 <= delta / 4 := hquarter_pos.le
  have hprob :
      ((ENNReal.ofReal (delta / 4) + ENNReal.ofReal (delta / 4)) +
          ENNReal.ofReal (delta / 4)) + ENNReal.ofReal (delta / 4) =
        ENNReal.ofReal delta := by
    rw [← ENNReal.ofReal_add hquarter_nonneg hquarter_nonneg]
    rw [← ENNReal.ofReal_add
      (add_nonneg hquarter_nonneg hquarter_nonneg) hquarter_nonneg]
    rw [← ENNReal.ofReal_add
      (add_nonneg (add_nonneg hquarter_nonneg hquarter_nonneg)
        hquarter_nonneg) hquarter_nonneg]
    congr 1
    ring
  exact h.trans_eq hprob

end BanditRLProof.Exp3
