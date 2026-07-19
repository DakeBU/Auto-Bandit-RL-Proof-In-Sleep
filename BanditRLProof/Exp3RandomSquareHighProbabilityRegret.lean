import BanditRLProof.Exp3BernsteinHighProbabilityRegret
import BanditRLProof.Exp3PredictableIntegration

/-!
# Random estimator-square EXP3 high-probability regret

The pathwise EXP3 assembly bounds the mixed importance-weighted estimator-square
sum by `|arms| * T / gamma`.  Its expectation is at most `|arms| * T`.
This module turns that expectation bound into a Markov tail and includes the
square event beside the two existing Bernstein confidence events.  The resulting
regret theorem removes the reciprocal exploration factor from the Hedge-square
budget, at the honest cost of a `1 / deltaSquare` failure allocation.
-/

namespace BanditRLProof.Exp3

open MeasureTheory ProbabilityTheory

universe u v

/-- Finite-horizon sum of the probability-mixed squared importance-weighted
loss estimates observed on a sampled trajectory. -/
noncomputable def sampledObservedMixedSquaredSum
    {Env : Type u} {Action : Type v} [DecidableEq Action]
    (arms : Finset Action) (eta gamma : Real) (horizon : Nat)
    (sample : Env × ((k : Nat) -> Action × Real)) : Real :=
  (Finset.range horizon).sum (fun t =>
    observedMixedSquaredImportanceWeightedLossAt arms eta gamma t sample)

/-- Each observed mixed estimator square is pointwise nonnegative. -/
theorem observedMixedSquaredImportanceWeightedLossAt_nonneg
    {Env : Type u} {Action : Type v} [DecidableEq Action]
    (arms : Finset Action) (harms : arms.Nonempty)
    (eta gamma : Real) (hgamma_nonneg : 0 <= gamma)
    (hgamma_le_one : gamma <= 1) (t : Nat)
    (sample : Env × ((k : Nat) -> Action × Real)) :
    0 <= observedMixedSquaredImportanceWeightedLossAt
      arms eta gamma t sample := by
  unfold observedMixedSquaredImportanceWeightedLossAt
  unfold mixedSquaredImportanceWeightedLoss
  exact Finset.sum_nonneg fun action _haction =>
    mul_nonneg
      (sampledTrajectoryProbabilityAt_nonneg arms harms eta gamma
        hgamma_nonneg hgamma_le_one t sample action)
      (sq_nonneg _)

/-- The finite-horizon observed mixed estimator-square sum is pointwise
nonnegative. -/
theorem sampledObservedMixedSquaredSum_nonneg
    {Env : Type u} {Action : Type v} [DecidableEq Action]
    (arms : Finset Action) (harms : arms.Nonempty)
    (eta gamma : Real) (hgamma_nonneg : 0 <= gamma)
    (hgamma_le_one : gamma <= 1) (horizon : Nat)
    (sample : Env × ((k : Nat) -> Action × Real)) :
    0 <= sampledObservedMixedSquaredSum arms eta gamma horizon sample := by
  unfold sampledObservedMixedSquaredSum
  exact Finset.sum_nonneg fun t _ht =>
    observedMixedSquaredImportanceWeightedLossAt_nonneg arms harms eta gamma
      hgamma_nonneg hgamma_le_one t sample

/-- The finite-horizon observed mixed estimator-square sum is measurable. -/
theorem measurable_sampledObservedMixedSquaredSum
    {Env : Type u} {Action : Type v}
    [MeasurableSpace Env]
    [MeasurableSpace Action] [MeasurableSingletonClass Action]
    [DecidableEq Action]
    (arms : Finset Action) (harms : arms.Nonempty)
    (eta gamma : Real) (hgamma_nonneg : 0 <= gamma)
    (hgamma_le_one : gamma <= 1) (horizon : Nat) :
    Measurable (sampledObservedMixedSquaredSum arms eta gamma horizon :
      (Env × ((k : Nat) -> Action × Real)) -> Real) := by
  unfold sampledObservedMixedSquaredSum
  exact Finset.measurable_sum (Finset.range horizon) fun t _ht =>
    measurable_observedMixedSquaredImportanceWeightedLossAt
      (Env := Env) arms harms eta gamma hgamma_nonneg hgamma_le_one t

/-- The generated finite-horizon observed mixed estimator-square sum is
integrable. -/
theorem integrable_sampledPredictableObservedMixedSquaredSum
    {Env : Type u} {Action : Type v}
    [MeasurableSpace Env] [StandardBorelSpace Env]
    [MeasurableSpace Action] [MeasurableSingletonClass Action]
    [StandardBorelSpace Action] [Nonempty Action] [DecidableEq Action]
    (prior : Measure Env) [IsFiniteMeasure prior]
    (arms : Finset Action) (harms : arms.Nonempty)
    (eta gamma : Real) (hgamma_pos : 0 < gamma)
    (hgamma_le_one : gamma <= 1)
    (loss : PredictableLossVector Env Action) (horizon : Nat) :
    let mu := prior ⊗ₘ sampledImportanceWeightedTrajectoryKernel arms harms
      eta gamma hgamma_pos.le hgamma_le_one loss.environment
    Integrable (sampledObservedMixedSquaredSum arms eta gamma horizon) mu := by
  dsimp only
  let mu := prior ⊗ₘ sampledImportanceWeightedTrajectoryKernel arms harms
    eta gamma hgamma_pos.le hgamma_le_one loss.environment
  unfold sampledObservedMixedSquaredSum
  exact IntegrabilitySums.integrable_finset_sum mu (Finset.range horizon)
    (fun t sample => observedMixedSquaredImportanceWeightedLossAt
      arms eta gamma t sample)
    (fun t _ht => by
      have ht := (integrable_observedAt prior arms harms eta gamma hgamma_pos
        hgamma_le_one loss t (Classical.choose harms)
          (Classical.choose_spec harms)).2
      simpa [mu] using ht)

/-- Markov tail for the random finite-horizon estimator-square sum.  Its
threshold is `|arms| * T / deltaSquare`, with no reciprocal exploration-rate
factor. -/
theorem sampledPredictableObservedMixedSquared_sum_tail_markov
    {Env : Type u} {Action : Type v}
    [MeasurableSpace Env] [StandardBorelSpace Env]
    [MeasurableSpace Action] [MeasurableSingletonClass Action]
    [StandardBorelSpace Action] [Nonempty Action] [DecidableEq Action]
    (prior : Measure Env) [IsProbabilityMeasure prior]
    (arms : Finset Action) (harms : arms.Nonempty)
    (eta gamma : Real) (hgamma_pos : 0 < gamma)
    (hgamma_le_one : gamma <= 1)
    (loss : PredictableLossVector Env Action)
    (horizon : Nat) (hhorizon : 0 < horizon)
    (deltaSquare : Real) (hdeltaSquare : 0 < deltaSquare) :
    let mu := prior ⊗ₘ sampledImportanceWeightedTrajectoryKernel arms harms
      eta gamma hgamma_pos.le hgamma_le_one loss.environment
    mu {sample |
        (arms.card : Real) * (horizon : Real) / deltaSquare <=
          sampledObservedMixedSquaredSum arms eta gamma horizon sample} <=
      ENNReal.ofReal deltaSquare := by
  dsimp only
  let mu := prior ⊗ₘ sampledImportanceWeightedTrajectoryKernel arms harms
    eta gamma hgamma_pos.le hgamma_le_one loss.environment
  let secondMoment := sampledObservedMixedSquaredSum
    (Env := Env) arms eta gamma horizon
  let budget := (arms.card : Real) * (horizon : Real)
  let scale := deltaSquare / budget
  have hcard_pos : 0 < (arms.card : Real) := by
    exact_mod_cast harms.card_pos
  have hhorizon_real : 0 < (horizon : Real) := by exact_mod_cast hhorizon
  have hbudget_pos : 0 < budget := by
    dsimp [budget]
    positivity
  have hscale_pos : 0 < scale := by
    dsimp [scale]
    positivity
  have hsecondIntegrable : Integrable secondMoment mu := by
    have h := integrable_sampledPredictableObservedMixedSquaredSum
      prior arms harms eta gamma hgamma_pos hgamma_le_one loss horizon
    simpa [mu, secondMoment] using h
  have hsecondNonneg : ∀ sample, 0 <= secondMoment sample := by
    intro sample
    exact sampledObservedMixedSquaredSum_nonneg arms harms eta gamma
      hgamma_pos.le hgamma_le_one horizon sample
  have hmean : integral mu secondMoment <= budget := by
    have h := sampledPredictableObserved_finiteHorizon_secondMoment_integral_le_card_mul
      prior arms harms eta gamma hgamma_pos hgamma_le_one loss horizon
    simpa [mu, secondMoment, sampledObservedMixedSquaredSum, budget] using h
  have hscaledIntegrable :
      Integrable (fun sample => scale * secondMoment sample) mu :=
    hsecondIntegrable.const_mul scale
  have hscaledNonneg : ∀ᵐ sample ∂mu, 0 <= scale * secondMoment sample :=
    Filter.Eventually.of_forall fun sample =>
      mul_nonneg hscale_pos.le (hsecondNonneg sample)
  have hnormalize : scale * (budget / deltaSquare) = 1 := by
    dsimp [scale]
    field_simp [hbudget_pos.ne', hdeltaSquare.ne']
  have hscaleBudget : scale * budget = deltaSquare := by
    dsimp [scale]
    field_simp [hbudget_pos.ne']
  have hmarkov :
      mu {sample | budget / deltaSquare <= secondMoment sample} <=
        ENNReal.ofReal (integral mu (fun sample => scale * secondMoment sample)) := by
    apply hscaledIntegrable.measure_le_integral hscaledNonneg
    intro sample hsample
    rw [← hnormalize]
    exact mul_le_mul_of_nonneg_left hsample hscale_pos.le
  have hintegral :
      integral mu (fun sample => scale * secondMoment sample) <= deltaSquare := by
    rw [MeasureTheory.integral_const_mul]
    calc
      scale * integral mu secondMoment <= scale * budget :=
        mul_le_mul_of_nonneg_left hmean hscale_pos.le
      _ = deltaSquare := hscaleBudget
  exact hmarkov.trans (ENNReal.ofReal_le_ofReal hintegral)

/-- Predictable regret budget with a caller-visible random-square failure
allocation and the two variance-sensitive confidence radii. -/
noncomputable def sampledPredictableRandomSquareBernsteinHighProbabilityRegretBudget
    {Action : Type v} (arms : Finset Action) (eta gamma : Real)
    (horizon : Nat) (deltaSquare deltaConfidence : Real) : Real :=
  Real.log arms.card / eta +
    (eta * (1 / (1 - gamma))) *
      ((arms.card : Real) * (horizon : Real) / deltaSquare) +
    gamma * (horizon : Real) +
    sampledPurePredictableMinusObservedBernsteinConfidenceRadius
      arms gamma horizon deltaConfidence +
    sampledComparatorEstimatorBernsteinConfidenceRadius
      arms gamma horizon deltaConfidence

/-- Generated predictable EXP3 regret with a Markov estimator-square event and
the two compiled Bernstein confidence events. -/
theorem sampledPredictable_randomSquareBernsteinHighProbabilityRegret_tail
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
    (deltaSquare deltaConfidence : Real)
    (hdeltaSquare : 0 < deltaSquare)
    (hdeltaConfidence : 0 < deltaConfidence) :
    let mu := prior ⊗ₘ sampledImportanceWeightedTrajectoryKernel arms harms
      eta gamma hgamma_pos.le hgamma_lt_one.le loss.environment
    mu {sample |
        sampledPredictableRandomSquareBernsteinHighProbabilityRegretBudget
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
    (arms.card : Real) * (horizon : Real) / deltaSquare
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
    have h := sampledPredictableObservedMixedSquared_sum_tail_markov
      prior arms harms eta gamma hgamma_pos hgamma_lt_one.le loss horizon
        hhorizon deltaSquare hdeltaSquare
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
      sampledPredictableRandomSquareBernsteinHighProbabilityRegretBudget
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
        sampledPredictableRandomSquareBernsteinHighProbabilityRegretBudget
          arms eta gamma horizon deltaSquare deltaConfidence := by
      dsimp [sampledPredictableRandomSquareBernsteinHighProbabilityRegretBudget,
        secondMomentBudget, pureRadius, comparatorRadius]
      linarith
    exact (not_lt_of_ge hregret) hfinal
  calc
    mu {sample |
        sampledPredictableRandomSquareBernsteinHighProbabilityRegretBudget
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

/-- Total-failure form: the estimator-square event and both Bernstein
confidence events each receive `delta / 3`. -/
theorem sampledPredictable_randomSquareBernsteinHighProbabilityRegret_tail_total_delta
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
        sampledPredictableRandomSquareBernsteinHighProbabilityRegretBudget
            arms eta gamma horizon (delta / 3) (delta / 3) <=
          (Finset.range horizon).sum (fun t =>
              sampledTrajectoryExploredPredictableLossAt
                arms eta gamma loss t sample) -
            (Finset.range horizon).sum (fun t =>
              predictableLossAt loss t sample comparator)} <=
      ENNReal.ofReal delta := by
  have hthird_pos : 0 < delta / 3 := div_pos hdelta (by norm_num)
  have h := sampledPredictable_randomSquareBernsteinHighProbabilityRegret_tail
    prior arms harms eta gamma heta hgamma_pos hgamma_lt_one loss comparator
      hcomparator horizon hhorizon (delta / 3) (delta / 3)
        hthird_pos hthird_pos
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
