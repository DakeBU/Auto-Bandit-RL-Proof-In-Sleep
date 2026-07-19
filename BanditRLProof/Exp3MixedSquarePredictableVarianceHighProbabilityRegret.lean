import BanditRLProof.Exp3MixedSquarePredictableVarianceTail
import BanditRLProof.Exp3MixedSquareBernsteinHighProbabilityRegret

/-!
# Predictable EXP3 regret with random predictable mixed-square variance

This module transports the fixed-horizon predictable-variance tail to the
observed mixed estimator-square sum used by the sampled Hedge inequality.  It
then exposes a predictable-regret theorem whose only uncontrolled probability
is the overflow event for the cumulative predictable variance.
-/

namespace BanditRLProof.Exp3

open MeasureTheory ProbabilityTheory

universe u v

/-- The observed mixed estimator-square sum has a random predictable-variance
tail on the event that the cumulative variance is at most `varianceBudget`. -/
theorem sampledPredictableObservedMixedSquared_sum_tail_predictableVariance_delta
    {Env : Type u} {Action : Type v}
    [MeasurableSpace Env] [StandardBorelSpace Env] [Nonempty Env]
    [MeasurableSpace Action] [MeasurableSingletonClass Action]
    [StandardBorelSpace Action] [Nonempty Action] [DecidableEq Action]
    (prior : Measure Env) [IsProbabilityMeasure prior]
    (arms : Finset Action) (harms : arms.Nonempty)
    (eta gamma : Real) (hgamma_pos : 0 < gamma)
    (hgamma_le_one : gamma <= 1)
    (loss : PredictableLossVector Env Action)
    (horizon : Nat) (varianceBudget delta : Real)
    (hvarianceBudget : 0 < varianceBudget) (hdelta : 0 < delta) :
    let mu := prior ⊗ₘ sampledImportanceWeightedTrajectoryKernel arms harms
      eta gamma hgamma_pos.le hgamma_le_one loss.environment
    mu {sample |
        (arms.card : Real) * (horizon : Real) +
            sampledMixedSquaredPredictableVarianceRadius
              arms gamma varianceBudget delta <=
          sampledObservedMixedSquaredSum arms eta gamma horizon sample ∧
        (Finset.range horizon).sum (fun i =>
          sampledTrajectoryPredictableMixedSquaredVarianceAt
            arms eta gamma loss i sample) <= varianceBudget} <=
      ENNReal.ofReal delta := by
  dsimp only
  let mu := prior ⊗ₘ sampledImportanceWeightedTrajectoryKernel arms harms
    eta gamma hgamma_pos.le hgamma_le_one loss.environment
  let radius := sampledMixedSquaredPredictableVarianceRadius
    arms gamma varianceBudget delta
  have htail :=
    sampledPredictableMixedSquaredDeviation_sum_tail_predictableVariance_delta
      prior arms harms eta gamma hgamma_pos hgamma_le_one loss horizon
        varianceBudget delta hvarianceBudget hdelta
  have heq := sampledObservedMixedSquaredSum_eq_predictable_ae
    prior arms harms eta gamma hgamma_pos.le hgamma_le_one loss horizon
  have hsubset : ∀ᵐ sample ∂mu,
      ((arms.card : Real) * (horizon : Real) + radius <=
          sampledObservedMixedSquaredSum arms eta gamma horizon sample ∧
        (Finset.range horizon).sum (fun i =>
          sampledTrajectoryPredictableMixedSquaredVarianceAt
            arms eta gamma loss i sample) <= varianceBudget) ->
      (radius <= (Finset.range horizon).sum (fun i =>
          sampledTrajectoryPredictableMixedSquaredDeviationAt
            arms eta gamma loss i sample) ∧
        (Finset.range horizon).sum (fun i =>
          sampledTrajectoryPredictableMixedSquaredVarianceAt
            arms eta gamma loss i sample) <= varianceBudget) := by
    filter_upwards [heq] with sample hobs
    intro hsample
    refine ⟨?_, hsample.2⟩
    have hmean := sampledPredictableLossSquaredSum_le_card_mul
      arms loss horizon sample
    have hcentered := sampledPredictableMixedSquaredDeviation_sum_eq
      arms eta gamma loss horizon sample
    rw [hobs] at hsample
    linarith
  exact (measure_mono_ae hsubset).trans (by simpa [mu, radius] using htail)

/-- Predictable regret budget with a caller-supplied cumulative predictable
variance budget. -/
noncomputable def sampledPredictableVarianceSquareHighProbabilityRegretBudget
    {Action : Type v} [DecidableEq Action]
    (arms : Finset Action) (eta gamma : Real) (horizon : Nat)
    (varianceBudget deltaSquare deltaConfidence : Real) : Real :=
  Real.log arms.card / eta +
    (eta * (1 / (1 - gamma))) *
      ((arms.card : Real) * (horizon : Real) +
        sampledMixedSquaredPredictableVarianceRadius
          arms gamma varianceBudget deltaSquare) +
    gamma * (horizon : Real) +
    sampledPurePredictableMinusObservedBernsteinConfidenceRadius
      arms gamma horizon deltaConfidence +
    sampledComparatorEstimatorBernsteinConfidenceRadius
      arms gamma horizon deltaConfidence

/-- Generated predictable EXP3 regret on the event that the cumulative
predictable mixed-square variance stays below `varianceBudget`. -/
theorem sampledPredictable_predictableVarianceSquareHighProbabilityRegret_tail_joint
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
    (horizon : Nat) (varianceBudget deltaSquare deltaConfidence : Real)
    (hvarianceBudget : 0 < varianceBudget)
    (hdeltaSquare : 0 < deltaSquare)
    (hdeltaConfidence : 0 < deltaConfidence) :
    let mu := prior ⊗ₘ sampledImportanceWeightedTrajectoryKernel arms harms
      eta gamma hgamma_pos.le hgamma_lt_one.le loss.environment
    mu {sample |
        sampledPredictableVarianceSquareHighProbabilityRegretBudget arms eta
            gamma horizon varianceBudget deltaSquare deltaConfidence <=
          (Finset.range horizon).sum (fun t =>
              sampledTrajectoryExploredPredictableLossAt
                arms eta gamma loss t sample) -
            (Finset.range horizon).sum (fun t =>
              predictableLossAt loss t sample comparator) ∧
        (Finset.range horizon).sum (fun i =>
          sampledTrajectoryPredictableMixedSquaredVarianceAt
            arms eta gamma loss i sample) <= varianceBudget} <=
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
  let predictableVariance := fun sample : Env × ((k : Nat) -> Action × Real) =>
    (Finset.range horizon).sum (fun i =>
      sampledTrajectoryPredictableMixedSquaredVarianceAt
        arms eta gamma loss i sample)
  let secondMomentBudget :=
    (arms.card : Real) * (horizon : Real) +
      sampledMixedSquaredPredictableVarianceRadius
        arms gamma varianceBudget deltaSquare
  let pureRadius :=
    sampledPurePredictableMinusObservedBernsteinConfidenceRadius
      arms gamma horizon deltaConfidence
  let comparatorRadius := sampledComparatorEstimatorBernsteinConfidenceRadius
    arms gamma horizon deltaConfidence
  let secondMomentBad : Set (Env × ((k : Nat) -> Action × Real)) :=
    {sample | secondMomentBudget <= secondMoment sample}
  let varianceGood : Set (Env × ((k : Nat) -> Action × Real)) :=
    {sample | predictableVariance sample <= varianceBudget}
  let pureBad : Set (Env × ((k : Nat) -> Action × Real)) :=
    {sample | pureRadius <= purePredictable sample - pureObserved sample}
  let comparatorBad : Set (Env × ((k : Nat) -> Action × Real)) :=
    {sample | comparatorRadius <= comparatorObserved sample - comparatorTrue sample}
  have hsecondTail : mu (secondMomentBad ∩ varianceGood) <=
      ENNReal.ofReal deltaSquare := by
    have h := sampledPredictableObservedMixedSquared_sum_tail_predictableVariance_delta
      prior arms harms eta gamma hgamma_pos hgamma_lt_one.le loss horizon
        varianceBudget deltaSquare hvarianceBudget hdeltaSquare
    dsimp only at h
    simpa [mu, secondMomentBad, varianceGood, secondMomentBudget, secondMoment,
      predictableVariance] using h
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
      (sampledPredictableVarianceSquareHighProbabilityRegretBudget arms eta
            gamma horizon varianceBudget deltaSquare deltaConfidence <=
          exploredPredictable sample - comparatorTrue sample ∧
        predictableVariance sample <= varianceBudget) ->
      sample ∈ ((secondMomentBad ∩ varianceGood) ∪ pureBad) ∪ comparatorBad := by
    filter_upwards [hhedge] with sample hsampleHedge
    intro hregret
    by_cases hsecond : sample ∈ secondMomentBad
    · exact Or.inl (Or.inl ⟨hsecond, hregret.2⟩)
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
        sampledPredictableVarianceSquareHighProbabilityRegretBudget arms eta
          gamma horizon varianceBudget deltaSquare deltaConfidence := by
      dsimp [sampledPredictableVarianceSquareHighProbabilityRegretBudget,
        secondMomentBudget, pureRadius, comparatorRadius]
      linarith
    exact (not_lt_of_ge hregret.1) hfinal
  calc
    mu {sample |
        sampledPredictableVarianceSquareHighProbabilityRegretBudget arms eta
            gamma horizon varianceBudget deltaSquare deltaConfidence <=
          (Finset.range horizon).sum (fun t =>
              sampledTrajectoryExploredPredictableLossAt
                arms eta gamma loss t sample) -
            (Finset.range horizon).sum (fun t =>
              predictableLossAt loss t sample comparator) ∧
        (Finset.range horizon).sum (fun i =>
          sampledTrajectoryPredictableMixedSquaredVarianceAt
            arms eta gamma loss i sample) <= varianceBudget} <=
        mu ((secondMomentBad ∩ varianceGood) ∪ pureBad ∪ comparatorBad) := by
      apply measure_mono_ae
      filter_upwards [hsubset] with sample hs
      intro hsource
      apply hs
      refine ⟨?_, ?_⟩
      · simpa [exploredPredictable, comparatorTrue] using hsource.1
      · simpa [predictableVariance] using hsource.2
    _ <= (mu (secondMomentBad ∩ varianceGood) + mu pureBad) +
        mu comparatorBad := by
      exact (measure_union_le _ _).trans
        (add_le_add (measure_union_le _ _) le_rfl)
    _ <= (ENNReal.ofReal deltaSquare + ENNReal.ofReal deltaConfidence) +
        ENNReal.ofReal deltaConfidence :=
      add_le_add (add_le_add hsecondTail hpureTail) hcomparatorTail

/-- Unconditional predictable-regret bound with the cumulative predictable
variance overflow probability left explicit. -/
theorem sampledPredictable_predictableVarianceSquareHighProbabilityRegret_tail
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
    (horizon : Nat) (varianceBudget deltaSquare deltaConfidence : Real)
    (hvarianceBudget : 0 < varianceBudget)
    (hdeltaSquare : 0 < deltaSquare)
    (hdeltaConfidence : 0 < deltaConfidence) :
    let mu := prior ⊗ₘ sampledImportanceWeightedTrajectoryKernel arms harms
      eta gamma hgamma_pos.le hgamma_lt_one.le loss.environment
    mu {sample |
        sampledPredictableVarianceSquareHighProbabilityRegretBudget arms eta
            gamma horizon varianceBudget deltaSquare deltaConfidence <=
          (Finset.range horizon).sum (fun t =>
              sampledTrajectoryExploredPredictableLossAt
                arms eta gamma loss t sample) -
            (Finset.range horizon).sum (fun t =>
              predictableLossAt loss t sample comparator)} <=
      ((ENNReal.ofReal deltaSquare + ENNReal.ofReal deltaConfidence) +
        ENNReal.ofReal deltaConfidence) +
        mu {sample |
          varianceBudget < (Finset.range horizon).sum (fun i =>
            sampledTrajectoryPredictableMixedSquaredVarianceAt
              arms eta gamma loss i sample)} := by
  dsimp only
  let mu := prior ⊗ₘ sampledImportanceWeightedTrajectoryKernel arms harms
    eta gamma hgamma_pos.le hgamma_lt_one.le loss.environment
  let regretBad : Set (Env × ((k : Nat) -> Action × Real)) :=
    {sample |
      sampledPredictableVarianceSquareHighProbabilityRegretBudget arms eta
          gamma horizon varianceBudget deltaSquare deltaConfidence <=
        (Finset.range horizon).sum (fun t =>
            sampledTrajectoryExploredPredictableLossAt
              arms eta gamma loss t sample) -
          (Finset.range horizon).sum (fun t =>
            predictableLossAt loss t sample comparator)}
  let varianceSum := fun sample : Env × ((k : Nat) -> Action × Real) =>
    (Finset.range horizon).sum (fun i =>
      sampledTrajectoryPredictableMixedSquaredVarianceAt
        arms eta gamma loss i sample)
  let varianceGood : Set (Env × ((k : Nat) -> Action × Real)) :=
    {sample | varianceSum sample <= varianceBudget}
  let varianceBad : Set (Env × ((k : Nat) -> Action × Real)) :=
    {sample | varianceBudget < varianceSum sample}
  have hjoint :=
    sampledPredictable_predictableVarianceSquareHighProbabilityRegret_tail_joint
      prior arms harms eta gamma heta hgamma_pos hgamma_lt_one loss comparator
        hcomparator horizon varianceBudget deltaSquare deltaConfidence
        hvarianceBudget hdeltaSquare hdeltaConfidence
  dsimp only at hjoint
  have hjoint' : mu (regretBad ∩ varianceGood) <=
      (ENNReal.ofReal deltaSquare + ENNReal.ofReal deltaConfidence) +
        ENNReal.ofReal deltaConfidence := by
    simpa [mu, regretBad, varianceGood, varianceSum] using hjoint
  have hsplit : regretBad ⊆ (regretBad ∩ varianceGood) ∪ varianceBad := by
    intro sample hregret
    by_cases hvariance : varianceSum sample <= varianceBudget
    · exact Or.inl ⟨hregret, hvariance⟩
    · exact Or.inr (lt_of_not_ge hvariance)
  calc
    mu regretBad <= mu ((regretBad ∩ varianceGood) ∪ varianceBad) :=
      measure_mono hsplit
    _ <= mu (regretBad ∩ varianceGood) + mu varianceBad :=
      measure_union_le _ _
    _ <= ((ENNReal.ofReal deltaSquare + ENNReal.ofReal deltaConfidence) +
          ENNReal.ofReal deltaConfidence) + mu varianceBad :=
      add_le_add hjoint' le_rfl
    _ = ((ENNReal.ofReal deltaSquare + ENNReal.ofReal deltaConfidence) +
          ENNReal.ofReal deltaConfidence) +
        mu {sample |
          varianceBudget < (Finset.range horizon).sum (fun i =>
            sampledTrajectoryPredictableMixedSquaredVarianceAt
              arms eta gamma loss i sample)} := by
      rfl

/-- Total-failure joint-event form with the square, pure-cross, and comparator
events allocated `delta / 3`. -/
theorem sampledPredictable_predictableVarianceSquareHighProbabilityRegret_tail_joint_total_delta
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
    (horizon : Nat) (varianceBudget delta : Real)
    (hvarianceBudget : 0 < varianceBudget) (hdelta : 0 < delta) :
    let mu := prior ⊗ₘ sampledImportanceWeightedTrajectoryKernel arms harms
      eta gamma hgamma_pos.le hgamma_lt_one.le loss.environment
    mu {sample |
        sampledPredictableVarianceSquareHighProbabilityRegretBudget arms eta
            gamma horizon varianceBudget (delta / 3) (delta / 3) <=
          (Finset.range horizon).sum (fun t =>
              sampledTrajectoryExploredPredictableLossAt
                arms eta gamma loss t sample) -
            (Finset.range horizon).sum (fun t =>
              predictableLossAt loss t sample comparator) ∧
        (Finset.range horizon).sum (fun i =>
          sampledTrajectoryPredictableMixedSquaredVarianceAt
            arms eta gamma loss i sample) <= varianceBudget} <=
      ENNReal.ofReal delta := by
  have hthird_pos : 0 < delta / 3 := div_pos hdelta (by norm_num)
  have h :=
    sampledPredictable_predictableVarianceSquareHighProbabilityRegret_tail_joint
      prior arms harms eta gamma heta hgamma_pos hgamma_lt_one loss comparator
        hcomparator horizon varianceBudget (delta / 3) (delta / 3)
        hvarianceBudget hthird_pos hthird_pos
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

/-- Primary residual-variance form: total confidence failure is `delta`, and
the only remaining term is the probability that cumulative predictable
variance exceeds `varianceBudget`. -/
theorem sampledPredictable_predictableVarianceSquareHighProbabilityRegret_tail_total_delta
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
    (horizon : Nat) (varianceBudget delta : Real)
    (hvarianceBudget : 0 < varianceBudget) (hdelta : 0 < delta) :
    let mu := prior ⊗ₘ sampledImportanceWeightedTrajectoryKernel arms harms
      eta gamma hgamma_pos.le hgamma_lt_one.le loss.environment
    mu {sample |
        sampledPredictableVarianceSquareHighProbabilityRegretBudget arms eta
            gamma horizon varianceBudget (delta / 3) (delta / 3) <=
          (Finset.range horizon).sum (fun t =>
              sampledTrajectoryExploredPredictableLossAt
                arms eta gamma loss t sample) -
            (Finset.range horizon).sum (fun t =>
              predictableLossAt loss t sample comparator)} <=
      ENNReal.ofReal delta +
        mu {sample |
          varianceBudget < (Finset.range horizon).sum (fun i =>
            sampledTrajectoryPredictableMixedSquaredVarianceAt
              arms eta gamma loss i sample)} := by
  have hthird_pos : 0 < delta / 3 := div_pos hdelta (by norm_num)
  have h :=
    sampledPredictable_predictableVarianceSquareHighProbabilityRegret_tail
      prior arms harms eta gamma heta hgamma_pos hgamma_lt_one loss comparator
        hcomparator horizon varianceBudget (delta / 3) (delta / 3)
        hvarianceBudget hthird_pos hthird_pos
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
  rw [hprob] at h
  exact h

end BanditRLProof.Exp3
