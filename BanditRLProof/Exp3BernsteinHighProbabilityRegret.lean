import BanditRLProof.Exp3HighProbabilityRegret
import BanditRLProof.Exp3PureBernstein

/-!
# Variance-sensitive predictable EXP3 high-probability regret

This module reassembles the generated predictable EXP3 regret theorem with the
variance-sensitive pure-cross and fixed-comparator confidence radii.  The
random Hedge-square contribution retains its existing pathwise reciprocal-floor
bound; no general Freedman or predictable-variance theorem is claimed.
-/

namespace BanditRLProof.Exp3

open MeasureTheory ProbabilityTheory

universe u v

/-- Predictable generated-regret budget with variance-sensitive confidence
radii and the existing pathwise estimator-square contribution. -/
noncomputable def sampledPredictableBernsteinHighProbabilityRegretBudget
    {Action : Type v} (arms : Finset Action) (eta gamma : Real)
    (horizon : Nat) (delta : Real) : Real :=
  Real.log arms.card / eta +
    (eta * (1 / (1 - gamma))) *
      ((horizon : Real) * (1 / (gamma / (arms.card : Real)))) +
    gamma * (horizon : Real) +
    sampledPurePredictableMinusObservedBernsteinConfidenceRadius
      arms gamma horizon delta +
    sampledComparatorEstimatorBernsteinConfidenceRadius
      arms gamma horizon delta

/-- Generated predictable EXP3 regret with both importance-weighted confidence
events using their variance-sensitive fixed-tilt routes. -/
theorem sampledPredictable_bernsteinHighProbabilityRegret_tail_delta
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
    (horizon : Nat) (delta : Real) (hdelta : 0 < delta) :
    let mu := prior ⊗ₘ sampledImportanceWeightedTrajectoryKernel arms harms
      eta gamma hgamma_pos.le hgamma_lt_one.le loss.environment
    mu {sample |
        sampledPredictableBernsteinHighProbabilityRegretBudget
            arms eta gamma horizon delta <=
          (Finset.range horizon).sum (fun t =>
              sampledTrajectoryExploredPredictableLossAt
                arms eta gamma loss t sample) -
            (Finset.range horizon).sum (fun t =>
              predictableLossAt loss t sample comparator)} <=
      ENNReal.ofReal delta + ENNReal.ofReal delta := by
  dsimp only
  let mu := prior ⊗ₘ sampledImportanceWeightedTrajectoryKernel arms harms
    eta gamma hgamma_pos.le hgamma_lt_one.le loss.environment
  let purePredictable := fun sample : Env × ((k : Nat) -> Action × Real) =>
    (Finset.range horizon).sum (fun t =>
      sampledTrajectoryPurePredictableLossAt arms eta gamma loss t sample)
  let pureObserved := fun sample : Env × ((k : Nat) -> Action × Real) =>
    (Finset.range horizon).sum (fun t =>
      sampledTrajectoryPureObservedLossAt arms eta gamma t sample)
  let comparatorObserved := fun sample : Env × ((k : Nat) -> Action × Real) =>
    (Finset.range horizon).sum (fun t =>
      observedImportanceWeightedLossAt arms eta gamma t sample comparator)
  let comparatorTrue := fun sample : Env × ((k : Nat) -> Action × Real) =>
    (Finset.range horizon).sum (fun t =>
      predictableLossAt loss t sample comparator)
  let exploredPredictable := fun sample : Env × ((k : Nat) -> Action × Real) =>
    (Finset.range horizon).sum (fun t =>
      sampledTrajectoryExploredPredictableLossAt
        arms eta gamma loss t sample)
  let secondMoment := fun sample : Env × ((k : Nat) -> Action × Real) =>
    (Finset.range horizon).sum (fun t =>
      observedMixedSquaredImportanceWeightedLossAt arms eta gamma t sample)
  let pureRadius :=
    sampledPurePredictableMinusObservedBernsteinConfidenceRadius
      arms gamma horizon delta
  let comparatorRadius := sampledComparatorEstimatorBernsteinConfidenceRadius
    arms gamma horizon delta
  let pureBad : Set (Env × ((k : Nat) -> Action × Real)) := {sample | pureRadius <=
    purePredictable sample - pureObserved sample}
  let comparatorBad : Set (Env × ((k : Nat) -> Action × Real)) := {sample |
    comparatorRadius <= comparatorObserved sample - comparatorTrue sample}
  have hpureTail : mu pureBad <= ENNReal.ofReal delta := by
    have h := sampledPurePredictableMinusObserved_sum_tail_bernstein_delta
      prior arms harms eta gamma hgamma_pos hgamma_lt_one.le loss
        horizon delta hdelta
    dsimp only at h
    simpa [mu, pureBad, pureRadius, purePredictable, pureObserved] using h
  have hcomparatorTail : mu comparatorBad <= ENNReal.ofReal delta := by
    have h := sampledObservedComparatorEstimatorDeviation_sum_tail_bernstein_delta
      prior arms harms eta gamma hgamma_pos hgamma_lt_one.le loss comparator
        hcomparator horizon delta hdelta
    dsimp only at h
    simpa [mu, comparatorBad, comparatorRadius, comparatorObserved,
      comparatorTrue,
      sampledTrajectoryObservedComparatorEstimatorDeviationAt] using h
  have hhedge :=
    sampledPredictableTrajectoryMeasure_hedge_exploredSecondMoment_le_ae
      prior arms harms eta gamma heta hgamma_pos hgamma_lt_one loss horizon
        comparator hcomparator
  dsimp only at hhedge
  have hsecond :=
    sampledPredictableTrajectoryMeasure_observedMixedSquared_sum_le_ae
      prior arms harms eta gamma hgamma_pos hgamma_lt_one.le loss horizon
  dsimp only at hsecond
  have hsubset : ∀ᵐ sample ∂mu,
      sampledPredictableBernsteinHighProbabilityRegretBudget
          arms eta gamma horizon delta <=
        exploredPredictable sample - comparatorTrue sample ->
      sample ∈ pureBad ∪ comparatorBad := by
    filter_upwards [hhedge, hsecond] with sample hsampleHedge hsampleSecond
    intro hregret
    by_cases hpure : sample ∈ pureBad
    · exact Or.inl hpure
    by_cases hcomparator : sample ∈ comparatorBad
    · exact Or.inr hcomparator
    exfalso
    have hpureGood :
        purePredictable sample - pureObserved sample < pureRadius := by
      change ¬ pureRadius <= purePredictable sample - pureObserved sample at hpure
      exact lt_of_not_ge hpure
    have hcomparatorGood :
        comparatorObserved sample - comparatorTrue sample <
          comparatorRadius := by
      change ¬ comparatorRadius <=
        comparatorObserved sample - comparatorTrue sample at hcomparator
      exact lt_of_not_ge hcomparator
    have hexploration :
        exploredPredictable sample <=
          purePredictable sample + gamma * (horizon : Real) := by
      have h := (sampledTrajectory_finiteHorizon_explorationBias_secondMoment
        arms harms eta gamma hgamma_pos.le hgamma_lt_one loss horizon sample).1
      simpa [exploredPredictable, purePredictable,
        sampledTrajectoryExploredPredictableLossAt,
        sampledTrajectoryPurePredictableLossAt,
        sampledTrajectoryPureProbabilityAt] using h
    have hcoef_nonneg : 0 <= eta * (1 / (1 - gamma)) :=
      mul_nonneg heta.le (one_div_pos.mpr (sub_pos.mpr hgamma_lt_one)).le
    have hweightedSecond :
        (eta * (1 / (1 - gamma))) * secondMoment sample <=
          (eta * (1 / (1 - gamma))) *
            ((horizon : Real) *
              (1 / (gamma / (arms.card : Real)))) :=
      mul_le_mul_of_nonneg_left
        (by simpa [secondMoment] using hsampleSecond) hcoef_nonneg
    have hhedge' :
        pureObserved sample - comparatorObserved sample <=
          Real.log arms.card / eta +
            (eta * (1 / (1 - gamma))) * secondMoment sample := by
      simpa [pureObserved, comparatorObserved, secondMoment] using hsampleHedge
    have hfinal : exploredPredictable sample - comparatorTrue sample <
        sampledPredictableBernsteinHighProbabilityRegretBudget
          arms eta gamma horizon delta := by
      dsimp [sampledPredictableBernsteinHighProbabilityRegretBudget,
        pureRadius, comparatorRadius]
      linarith
    exact (not_lt_of_ge hregret) hfinal
  calc
    mu {sample |
        sampledPredictableBernsteinHighProbabilityRegretBudget
            arms eta gamma horizon delta <=
          (Finset.range horizon).sum (fun t =>
              sampledTrajectoryExploredPredictableLossAt
                arms eta gamma loss t sample) -
            (Finset.range horizon).sum (fun t =>
              predictableLossAt loss t sample comparator)} <=
        mu (pureBad ∪ comparatorBad) := by
      apply measure_mono_ae
      simpa [exploredPredictable, comparatorTrue, mu] using hsubset
    _ <= mu pureBad + mu comparatorBad := measure_union_le _ _
    _ <= ENNReal.ofReal delta + ENNReal.ofReal delta :=
      add_le_add hpureTail hcomparatorTail

/-- Total-failure form: each variance-sensitive confidence event receives
`delta / 2`.  Unlike the range-Hoeffding predecessor, no positive-horizon
premise is needed. -/
theorem sampledPredictable_bernsteinHighProbabilityRegret_tail_total_delta
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
    (horizon : Nat) (delta : Real) (hdelta : 0 < delta) :
    let mu := prior ⊗ₘ sampledImportanceWeightedTrajectoryKernel arms harms
      eta gamma hgamma_pos.le hgamma_lt_one.le loss.environment
    mu {sample |
        sampledPredictableBernsteinHighProbabilityRegretBudget
            arms eta gamma horizon (delta / 2) <=
          (Finset.range horizon).sum (fun t =>
              sampledTrajectoryExploredPredictableLossAt
                arms eta gamma loss t sample) -
            (Finset.range horizon).sum (fun t =>
              predictableLossAt loss t sample comparator)} <=
      ENNReal.ofReal delta := by
  have h := sampledPredictable_bernsteinHighProbabilityRegret_tail_delta
    prior arms harms eta gamma heta hgamma_pos hgamma_lt_one loss comparator
      hcomparator horizon (delta / 2) (half_pos hdelta)
  dsimp only at h ⊢
  rw [← ENNReal.ofReal_add (half_pos hdelta).le (half_pos hdelta).le,
    add_halves] at h
  exact h

end BanditRLProof.Exp3
