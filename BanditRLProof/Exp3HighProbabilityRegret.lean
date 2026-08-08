import BanditRLProof.Exp3PureConfidence

/-!
# Generated predictable EXP3 high-probability regret

This module completes the finite-horizon high-probability pseudo-regret route
for the generated predictable EXP3 trajectory.  A pathwise reciprocal-floor
bound controls the random estimator-square sum almost surely.  The final theorem
then combines the sampled Hedge inequality, exploration bias, the pure-Hedge
predictable-minus-observed confidence event, and the comparator-estimator
confidence event by a two-event union bound.

The resulting theorem is valid but uses range-based Hoeffding radii.  Their
`(|arms| / gamma)^2` per-round proxy is intentionally recorded rather than
silently presented as the ideal EXP3.P/Freedman rate.
-/

namespace BanditRLProof.Exp3

open MeasureTheory ProbabilityTheory

universe u v

theorem observedMixedSquaredImportanceWeightedLossAt_le_inv_explorationFloor
    {Env : Type u} {Action : Type v}
    [MeasurableSpace Env]
    [MeasurableSpace Action] [MeasurableSingletonClass Action]
    [DecidableEq Action]
    (arms : Finset Action) (harms : arms.Nonempty)
    (eta gamma : Real) (hgamma_pos : 0 < gamma)
    (hgamma_le_one : gamma <= 1)
    (loss : PredictableLossVector Env Action) (t : Nat)
    (sample : Env × ((k : Nat) -> Action × Real))
    (hreward : (sample.2 t).2 ∈ Set.Icc (0 : Real) 1) :
    observedMixedSquaredImportanceWeightedLossAt
        arms eta gamma t sample <=
      1 / (gamma / (arms.card : Real)) := by
  let chosen := (sample.2 t).1
  let prob := sampledTrajectoryProbabilityAt arms eta gamma t sample
  let regularity := sampledPredictableTrajectoryLossRegularityAt
    arms harms eta gamma hgamma_pos hgamma_le_one loss t
  by_cases hchosen : chosen ∈ arms
  · have hfloor := regularity.prob_floor sample chosen hchosen
    have hepsilon := regularity.epsilon_pos
    have hprob_pos : 0 < prob chosen := lt_of_lt_of_le hepsilon hfloor
    have hsq : ((sample.2 t).2) ^ 2 <= 1 := by
      nlinarith [hreward.1, hreward.2]
    have hone_le : 1 <= (1 / (gamma / (arms.card : Real))) * prob chosen := by
      rw [one_div_mul_eq_div, le_div_iff₀ hepsilon]
      simpa [regularity] using hfloor
    unfold observedMixedSquaredImportanceWeightedLossAt
    rw [mixedSquaredImportanceWeightedLoss_eq_selectedLoss_sq_div
      arms prob (fun _ => (sample.2 t).2) chosen hchosen hprob_pos.ne']
    apply (div_le_iff₀ hprob_pos).2
    exact hsq.trans hone_le
  · unfold observedMixedSquaredImportanceWeightedLossAt
    have hzero : mixedSquaredImportanceWeightedLoss arms prob
        (fun _ => (sample.2 t).2) chosen = 0 := by
      unfold mixedSquaredImportanceWeightedLoss
      apply Finset.sum_eq_zero
      intro candidate hcandidate
      have hne : chosen ≠ candidate := by
        intro heq
        exact hchosen (heq ▸ hcandidate)
      simp [importanceWeightedLoss, hne]
    rw [hzero]
    exact one_div_nonneg.mpr
      (explorationFloor_pos arms harms gamma hgamma_pos).le

theorem sampledPredictableTrajectoryMeasure_reward_mem_unitInterval_ae
    {Env : Type u} {Action : Type v}
    [MeasurableSpace Env] [StandardBorelSpace Env]
    [MeasurableSpace Action] [MeasurableSingletonClass Action]
    [StandardBorelSpace Action] [Nonempty Action] [DecidableEq Action]
    (prior : Measure Env) [IsFiniteMeasure prior]
    (arms : Finset Action) (harms : arms.Nonempty)
    (eta gamma : Real)
    (hgamma_nonneg : 0 <= gamma) (hgamma_le_one : gamma <= 1)
    (loss : PredictableLossVector Env Action) (t : Nat) :
    let mu := prior ⊗ₘ sampledImportanceWeightedTrajectoryKernel arms harms
      eta gamma hgamma_nonneg hgamma_le_one loss.environment
    ∀ᵐ sample ∂mu, (sample.2 t).2 ∈ Set.Icc (0 : Real) 1 := by
  dsimp only
  let mu := prior ⊗ₘ sampledImportanceWeightedTrajectoryKernel arms harms
    eta gamma hgamma_nonneg hgamma_le_one loss.environment
  cases t with
  | zero =>
      have hreward :
          (fun sample : Env × ((k : Nat) -> Action × Real) =>
            (sample.2 0).2) =ᵐ[mu]
          (fun sample => loss.initial sample.1 (sample.2 0).1) := by
        simpa [mu, sampledImportanceWeightedTrajectoryKernel] using
          (canonicalPredictableTrajectoryMeasure_reward_zero_eq_initialLoss_ae
            prior (sampledImportanceWeightedHistoryAlgorithm arms harms eta gamma
              hgamma_nonneg hgamma_le_one) loss)
      filter_upwards [hreward] with sample hsample
      rw [hsample]
      exact loss.initial_mem_unitInterval sample.1 (sample.2 0).1
  | succ n =>
      have hreward :
          (fun sample : Env × ((k : Nat) -> Action × Real) =>
            (sample.2 (n + 1)).2) =ᵐ[mu]
          (fun sample => loss.successor n sample.1
            (Preorder.frestrictLe n sample.2) (sample.2 (n + 1)).1) := by
        simpa [mu] using
          (sampledPredictableTrajectoryMeasure_reward_eq_successorLoss_ae
            prior arms harms eta gamma hgamma_nonneg hgamma_le_one loss n)
      filter_upwards [hreward] with sample hsample
      rw [hsample]
      exact loss.successor_mem_unitInterval n sample.1
        (Preorder.frestrictLe n sample.2) (sample.2 (n + 1)).1

theorem sampledPredictableTrajectoryMeasure_observedMixedSquared_sum_le_ae
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
    ∀ᵐ sample ∂mu,
      (Finset.range horizon).sum (fun t =>
          observedMixedSquaredImportanceWeightedLossAt
            arms eta gamma t sample) <=
        (horizon : Real) * (1 / (gamma / (arms.card : Real))) := by
  dsimp only
  have hreward : ∀ᵐ sample ∂prior ⊗ₘ
      sampledImportanceWeightedTrajectoryKernel arms harms eta gamma
        hgamma_pos.le hgamma_le_one loss.environment,
      ∀ t, t < horizon -> (sample.2 t).2 ∈ Set.Icc (0 : Real) 1 := by
    rw [ae_all_iff]
    intro t
    have ht := sampledPredictableTrajectoryMeasure_reward_mem_unitInterval_ae
      prior arms harms eta gamma hgamma_pos.le hgamma_le_one loss t
    dsimp only at ht
    filter_upwards [ht] with sample hsample
    intro _ht
    exact hsample
  filter_upwards [hreward] with sample hsample
  calc
    (Finset.range horizon).sum (fun t =>
        observedMixedSquaredImportanceWeightedLossAt
          arms eta gamma t sample) <=
        (Finset.range horizon).sum (fun _t =>
          1 / (gamma / (arms.card : Real))) := by
      apply Finset.sum_le_sum
      intro t ht
      exact observedMixedSquaredImportanceWeightedLossAt_le_inv_explorationFloor
        arms harms eta gamma hgamma_pos hgamma_le_one loss t sample
          (hsample t (Finset.mem_range.mp ht))
    _ = (horizon : Real) * (1 / (gamma / (arms.card : Real))) := by
      simp

noncomputable def sampledPredictableHighProbabilityRegretBudget
    {Action : Type v} (arms : Finset Action) (eta gamma : Real)
    (horizon : Nat) (delta : Real) : Real :=
  Real.log arms.card / eta +
    (eta * (1 / (1 - gamma))) *
      ((horizon : Real) * (1 / (gamma / (arms.card : Real)))) +
    gamma * (horizon : Real) +
    sampledPureObservedDeviationConfidenceRadius arms gamma horizon delta +
    sampledComparatorEstimatorConfidenceRadius arms gamma horizon delta

/-- Generated predictable EXP3 pseudo-regret exceeds the explicit Hedge,
exploration, estimator-square, and two confidence-radius budget with probability
at most the sum of the pure-q and comparator failure probabilities. -/
theorem sampledPredictable_highProbabilityRegret_tail_delta
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
        sampledPredictableHighProbabilityRegretBudget
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
  let pureRadius := sampledPureObservedDeviationConfidenceRadius
    arms gamma horizon delta
  let comparatorRadius := sampledComparatorEstimatorConfidenceRadius
    arms gamma horizon delta
  let pureBad : Set (Env × ((k : Nat) -> Action × Real)) := {sample | pureRadius <=
    purePredictable sample - pureObserved sample}
  let comparatorBad : Set (Env × ((k : Nat) -> Action × Real)) := {sample | comparatorRadius <=
    comparatorObserved sample - comparatorTrue sample}
  have hpureTail : mu pureBad <= ENNReal.ofReal delta := by
    have h := sampledPurePredictableMinusObserved_sum_tail_delta
      prior arms harms eta gamma hgamma_pos hgamma_lt_one.le loss
        horizon hhorizon delta hdelta
    dsimp only at h
    simpa [mu, pureBad, pureRadius, purePredictable, pureObserved] using h
  have hcomparatorTail : mu comparatorBad <= ENNReal.ofReal delta := by
    have h := sampledObservedComparatorEstimatorDeviation_sum_tail_delta
      prior arms harms eta gamma hgamma_pos hgamma_lt_one.le loss comparator
        hcomparator horizon hhorizon delta hdelta
    dsimp only at h
    simpa [mu, comparatorBad, comparatorRadius, comparatorObserved,
      comparatorTrue] using h
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
      sampledPredictableHighProbabilityRegretBudget
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
      change ¬ pureRadius <=
        purePredictable sample - pureObserved sample at hpure
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
        sampledPredictableHighProbabilityRegretBudget
          arms eta gamma horizon delta := by
      dsimp [sampledPredictableHighProbabilityRegretBudget,
        pureRadius, comparatorRadius]
      linarith
    exact (not_lt_of_ge hregret) hfinal
  calc
    mu {sample |
        sampledPredictableHighProbabilityRegretBudget
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

/-- Standard total-failure-probability form of the generated predictable EXP3
pseudo-regret bound. Each of the two confidence events receives `delta / 2`,
so their union has probability at most `delta`. -/
theorem sampledPredictable_highProbabilityRegret_tail_total_delta
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
        sampledPredictableHighProbabilityRegretBudget
            arms eta gamma horizon (delta / 2) <=
          (Finset.range horizon).sum (fun t =>
              sampledTrajectoryExploredPredictableLossAt
                arms eta gamma loss t sample) -
            (Finset.range horizon).sum (fun t =>
              predictableLossAt loss t sample comparator)} <=
      ENNReal.ofReal delta := by
  have h := sampledPredictable_highProbabilityRegret_tail_delta
    prior arms harms eta gamma heta hgamma_pos hgamma_lt_one loss comparator
      hcomparator horizon hhorizon (delta / 2) (half_pos hdelta)
  dsimp only at h ⊢
  rw [← ENNReal.ofReal_add (half_pos hdelta).le (half_pos hdelta).le,
    add_halves] at h
  exact h

end BanditRLProof.Exp3
