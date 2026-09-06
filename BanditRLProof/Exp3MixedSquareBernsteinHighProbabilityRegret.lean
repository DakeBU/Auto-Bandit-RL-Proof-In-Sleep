import BanditRLProof.Exp3MixedSquareBernstein
import BanditRLProof.Exp3MixedSquareExponentialHighProbabilityRegret

/-!
# Predictable EXP3 regret with variance-sensitive mixed-square confidence

This module consumes the generated mixed-square Bernstein tail in the existing
three-event predictable-regret assembly.  The square-event radius now uses the
second-moment coefficient `K / epsilon`; the pure-cross and fixed-comparator
events retain their compiled Bernstein radii.
-/

namespace BanditRLProof.Exp3

open MeasureTheory ProbabilityTheory

universe u v

/-- Predictable regret budget using the variance-sensitive mixed-square
Bernstein radius. -/
noncomputable def sampledPredictableBernsteinSquareHighProbabilityRegretBudget
    {Action : Type v} (arms : Finset Action) (eta gamma : Real)
    (horizon : Nat) (deltaSquare deltaConfidence : Real) : Real :=
  Real.log arms.card / eta +
    (eta * (1 / (1 - gamma))) *
      ((arms.card : Real) * (horizon : Real) +
        sampledMixedSquaredBernsteinConfidenceRadius
          arms gamma horizon deltaSquare) +
    gamma * (horizon : Real) +
    sampledPurePredictableMinusObservedBernsteinConfidenceRadius
      arms gamma horizon deltaConfidence +
    sampledComparatorEstimatorBernsteinConfidenceRadius
      arms gamma horizon deltaConfidence

/-- Generated predictable EXP3 regret with the mixed-square, pure-cross, and
fixed-comparator Bernstein events. -/
theorem sampledPredictable_bernsteinSquareHighProbabilityRegret_tail
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
    (horizon : Nat)
    (deltaSquare deltaConfidence : Real)
    (hdeltaSquare : 0 < deltaSquare)
    (hdeltaConfidence : 0 < deltaConfidence) :
    let mu := prior ⊗ₘ sampledImportanceWeightedTrajectoryKernel arms harms
      eta gamma hgamma_pos.le hgamma_lt_one.le loss.environment
    mu {sample |
        sampledPredictableBernsteinSquareHighProbabilityRegretBudget
            arms eta gamma horizon deltaSquare deltaConfidence <=
          (Finset.range horizon).sum (fun t =>
              sampledTrajectoryExploredPredictableLossAt
                arms eta gamma loss t sample) -
            (Finset.range horizon).sum (fun t =>
              predictableLossAt loss t sample comparator)} <=
      (ENNReal.ofReal deltaSquare + ENNReal.ofReal deltaConfidence) +
        ENNReal.ofReal deltaConfidence := by
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
      sampledTrajectoryExploredPredictableLossAt arms eta gamma loss t sample)
  let secondMoment := sampledObservedMixedSquaredSum
    (Env := Env) arms eta gamma horizon
  let secondMomentBudget :=
    (arms.card : Real) * (horizon : Real) +
      sampledMixedSquaredBernsteinConfidenceRadius
        arms gamma horizon deltaSquare
  let pureRadius :=
    sampledPurePredictableMinusObservedBernsteinConfidenceRadius
      arms gamma horizon deltaConfidence
  let comparatorRadius := sampledComparatorEstimatorBernsteinConfidenceRadius
    arms gamma horizon deltaConfidence
  let secondMomentBad : Set (Env × ((k : Nat) -> Action × Real)) :=
    {sample | secondMomentBudget <= secondMoment sample}
  let pureBad : Set (Env × ((k : Nat) -> Action × Real)) :=
    {sample | pureRadius <= purePredictable sample - pureObserved sample}
  let comparatorBad : Set (Env × ((k : Nat) -> Action × Real)) :=
    {sample | comparatorRadius <= comparatorObserved sample - comparatorTrue sample}
  have hsecondTail : mu secondMomentBad <= ENNReal.ofReal deltaSquare := by
    have h := sampledPredictableObservedMixedSquared_sum_tail_bernstein_delta
      prior arms harms eta gamma hgamma_pos hgamma_lt_one.le loss horizon
        deltaSquare hdeltaSquare
    dsimp only at h
    simpa [mu, secondMomentBad, secondMomentBudget, secondMoment] using h
  have hpureTail : mu pureBad <= ENNReal.ofReal deltaConfidence := by
    have h := sampledPurePredictableMinusObserved_sum_tail_bernstein_delta
      prior arms harms eta gamma hgamma_pos hgamma_lt_one.le loss
        horizon deltaConfidence hdeltaConfidence
    dsimp only at h
    simpa [mu, pureBad, pureRadius, purePredictable, pureObserved] using h
  have hcomparatorTail : mu comparatorBad <= ENNReal.ofReal deltaConfidence := by
    have h := sampledObservedComparatorEstimatorDeviation_sum_tail_bernstein_delta
      prior arms harms eta gamma hgamma_pos hgamma_lt_one.le loss comparator
        hcomparator horizon deltaConfidence hdeltaConfidence
    dsimp only at h
    simpa [mu, comparatorBad, comparatorRadius, comparatorObserved,
      comparatorTrue,
      sampledTrajectoryObservedComparatorEstimatorDeviationAt] using h
  have hhedge :=
    sampledPredictableTrajectoryMeasure_hedge_exploredSecondMoment_le_ae
      prior arms harms eta gamma heta hgamma_pos hgamma_lt_one loss horizon
        comparator hcomparator
  dsimp only at hhedge
  have hsubset : ∀ᵐ sample ∂mu,
      sampledPredictableBernsteinSquareHighProbabilityRegretBudget
          arms eta gamma horizon deltaSquare deltaConfidence <=
        exploredPredictable sample - comparatorTrue sample ->
      sample ∈ (secondMomentBad ∪ pureBad) ∪ comparatorBad := by
    filter_upwards [hhedge] with sample hsampleHedge
    intro hregret
    by_cases hsecond : sample ∈ secondMomentBad
    · exact Or.inl (Or.inl hsecond)
    by_cases hpure : sample ∈ pureBad
    · exact Or.inl (Or.inr hpure)
    by_cases hcomparator : sample ∈ comparatorBad
    · exact Or.inr hcomparator
    exfalso
    have hsecondGood : secondMoment sample < secondMomentBudget := by
      change ¬ secondMomentBudget <= secondMoment sample at hsecond
      exact lt_of_not_ge hsecond
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
    have hcoef_pos : 0 < eta * (1 / (1 - gamma)) :=
      mul_pos heta (one_div_pos.mpr (sub_pos.mpr hgamma_lt_one))
    have hweightedSecond :
        (eta * (1 / (1 - gamma))) * secondMoment sample <
          (eta * (1 / (1 - gamma))) * secondMomentBudget :=
      mul_lt_mul_of_pos_left hsecondGood hcoef_pos
    have hhedge' :
        pureObserved sample - comparatorObserved sample <=
          Real.log arms.card / eta +
            (eta * (1 / (1 - gamma))) * secondMoment sample := by
      simpa [pureObserved, comparatorObserved, secondMoment,
        sampledObservedMixedSquaredSum] using hsampleHedge
    have hfinal : exploredPredictable sample - comparatorTrue sample <
        sampledPredictableBernsteinSquareHighProbabilityRegretBudget
          arms eta gamma horizon deltaSquare deltaConfidence := by
      dsimp [sampledPredictableBernsteinSquareHighProbabilityRegretBudget,
        secondMomentBudget, pureRadius, comparatorRadius]
      linarith
    exact (not_lt_of_ge hregret) hfinal
  calc
    mu {sample |
        sampledPredictableBernsteinSquareHighProbabilityRegretBudget
            arms eta gamma horizon deltaSquare deltaConfidence <=
          (Finset.range horizon).sum (fun t =>
              sampledTrajectoryExploredPredictableLossAt
                arms eta gamma loss t sample) -
            (Finset.range horizon).sum (fun t =>
              predictableLossAt loss t sample comparator)} <=
        mu ((secondMomentBad ∪ pureBad) ∪ comparatorBad) := by
      apply measure_mono_ae
      simpa [exploredPredictable, comparatorTrue, mu] using hsubset
    _ <= (mu secondMomentBad + mu pureBad) + mu comparatorBad := by
      exact (measure_union_le _ _).trans
        (add_le_add (measure_union_le _ _) le_rfl)
    _ <= (ENNReal.ofReal deltaSquare + ENNReal.ofReal deltaConfidence) +
        ENNReal.ofReal deltaConfidence :=
      add_le_add (add_le_add hsecondTail hpureTail) hcomparatorTail

/-- Total-failure form with all three Bernstein events allocated `delta / 3`. -/
theorem sampledPredictable_bernsteinSquareHighProbabilityRegret_tail_total_delta
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
    (horizon : Nat)
    (delta : Real) (hdelta : 0 < delta) :
    let mu := prior ⊗ₘ sampledImportanceWeightedTrajectoryKernel arms harms
      eta gamma hgamma_pos.le hgamma_lt_one.le loss.environment
    mu {sample |
        sampledPredictableBernsteinSquareHighProbabilityRegretBudget
            arms eta gamma horizon (delta / 3) (delta / 3) <=
          (Finset.range horizon).sum (fun t =>
              sampledTrajectoryExploredPredictableLossAt
                arms eta gamma loss t sample) -
            (Finset.range horizon).sum (fun t =>
              predictableLossAt loss t sample comparator)} <=
      ENNReal.ofReal delta := by
  have hthird_pos : 0 < delta / 3 := div_pos hdelta (by norm_num)
  have h :=
    sampledPredictable_bernsteinSquareHighProbabilityRegret_tail
      prior arms harms eta gamma heta hgamma_pos hgamma_lt_one loss comparator
        hcomparator horizon (delta / 3) (delta / 3) hthird_pos hthird_pos
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
