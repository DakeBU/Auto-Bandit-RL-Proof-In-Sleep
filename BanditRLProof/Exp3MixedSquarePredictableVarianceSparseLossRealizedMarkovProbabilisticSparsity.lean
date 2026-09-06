import BanditRLProof.Exp3MixedSquarePredictableVarianceSparseLossRealizedMarkovHighProbabilityRegret

/-!
# Probabilistic sparse-loss control of realized predictable-variance EXP3 regret

This module allows the per-round support-cardinality contract to fail on an
explicit generated-trajectory event. On paths outside that event, sparsity
still supplies the `sparsity * horizon` loss-mass budget used by the observed
mixed-square and Hedge terms. The Markov variance closure instead uses the
global `arms.card * horizon` loss-mass envelope, so the exceptional event costs
its actual generated-measure probability without assuming it is null.

The resulting theorem is a caller-parameterized `delta + epsilon` route. It
does not retain the sharper sparse variance mean on exceptional paths and does
not claim the tuned all-horizon `14 * gamma * horizon` threshold.
-/

namespace BanditRLProof.Exp3

open MeasureTheory ProbabilityTheory

universe u v

/-- Generated trajectories on which the requested per-round support cap fails
at some time before the horizon. -/
noncomputable def sampledPredictableSparsityFailure
    {Env : Type u} {Action : Type v}
    [MeasurableSpace Env] [MeasurableSpace Action]
    (arms : Finset Action) (loss : PredictableLossVector Env Action)
    (horizon sparsity : Nat) :
    Set (Env × ((k : Nat) → Action × Real)) :=
  {sample | ∃ t, t < horizon ∧
    sparsity < (sampledPredictableLossSupport arms loss t sample).card}

/-- Every trajectory either obeys the sparse armwise loss-mass budget or lies
in the explicit sparsity-failure event. -/
theorem sampledPredictableLossMassSum_le_or_mem_sparsityFailure
    {Env : Type u} {Action : Type v}
    [MeasurableSpace Env] [MeasurableSpace Action]
    (arms : Finset Action) (loss : PredictableLossVector Env Action)
    (horizon sparsity : Nat)
    (sample : Env × ((k : Nat) → Action × Real)) :
    sampledPredictableLossMassSum arms loss horizon sample ≤
        (sparsity : Real) * (horizon : Real) ∨
      sample ∈ sampledPredictableSparsityFailure arms loss horizon sparsity := by
  classical
  by_cases hsparse : ∀ t, t < horizon →
      (sampledPredictableLossSupport arms loss t sample).card ≤ sparsity
  · exact Or.inl
      (sampledPredictableLossMassSum_le_sparsity_mul_horizon_of_sample
        arms loss horizon sparsity sample hsparse)
  · right
    simp only [sampledPredictableSparsityFailure, Set.mem_setOf_eq]
    push Not at hsparse
    exact hsparse

/-- The number of nonzero active coordinates is always at most the number of
active arms, giving a global pathwise loss-mass envelope. -/
theorem sampledPredictableLossMassSum_le_card_mul_horizon
    {Env : Type u} {Action : Type v}
    [MeasurableSpace Env] [MeasurableSpace Action]
    (arms : Finset Action) (loss : PredictableLossVector Env Action)
    (horizon : Nat) (sample : Env × ((k : Nat) → Action × Real)) :
    sampledPredictableLossMassSum arms loss horizon sample ≤
      (arms.card : Real) * (horizon : Real) := by
  classical
  apply sampledPredictableLossMassSum_le_sparsity_mul_horizon_of_sample
  intro t _ht
  exact Finset.card_le_card (Finset.filter_subset _ _)

/-- Global predictable-variance mean envelope used when sparsity may fail with
positive probability. -/
noncomputable def sampledPredictableGlobalVarianceMeanBudget
    {Action : Type v} [DecidableEq Action]
    (arms : Finset Action) (gamma : Real) (horizon : Nat) : Real :=
  (1 / (gamma / (arms.card : Real))) *
    ((arms.card : Real) * (horizon : Real))

/-- The global `arms.card * horizon` loss-mass envelope closes the cumulative
predictable-variance `lintegral` without any sparsity assumption. -/
theorem sampledPredictableMixedSquaredVarianceLIntegral_le_globalLossMass
    {Env : Type u} {Action : Type v}
    [MeasurableSpace Env]
    [MeasurableSpace Action] [MeasurableSingletonClass Action]
    [DecidableEq Action]
    (mu : Measure (Env × ((k : Nat) → Action × Real)))
    [IsProbabilityMeasure mu]
    (arms : Finset Action) (harms : arms.Nonempty)
    (eta gamma : Real) (hgamma_pos : 0 < gamma)
    (hgamma_le_one : gamma ≤ 1)
    (loss : PredictableLossVector Env Action) (horizon : Nat) :
    sampledPredictableMixedSquaredVarianceLIntegral
        mu arms eta gamma loss horizon ≤
      ENNReal.ofReal
        (sampledPredictableGlobalVarianceMeanBudget arms gamma horizon) := by
  simpa [sampledPredictableGlobalVarianceMeanBudget] using
    sampledPredictableMixedSquaredVarianceLIntegral_le_of_lossMassSum_le
      mu arms harms eta gamma hgamma_pos hgamma_le_one loss horizon
        ((arms.card : Real) * (horizon : Real))
        (Filter.Eventually.of_forall fun sample =>
          sampledPredictableLossMassSum_le_card_mul_horizon
            arms loss horizon sample)

/-- Realized sparse-loss budget with a global Markov variance envelope. The
observed-square mean remains `sparsity * horizon`, while the variance overflow
threshold uses `arms.card * horizon`. -/
noncomputable def sampledPredictableVarianceSquareProbabilisticSparseLossRealizedMarkovHighProbabilityRegretBudget
    {Action : Type v} [DecidableEq Action]
    (arms : Finset Action) (eta gamma : Real) (horizon sparsity : Nat)
    (delta : Real) : Real :=
  sampledPredictableVarianceSquareSmallLossRealizedHighProbabilityRegretBudget
    arms eta gamma horizon ((sparsity : Real) * (horizon : Real))
      (sampledPredictableGlobalVarianceMeanBudget arms gamma horizon / (delta / 5))
      (delta / 5) (delta / 5) (delta / 5)

/-- Generated realized regret with an explicit positive-probability sparsity
failure event. The total tail is the ordinary five-event budget plus the exact
generated measure of that event. -/
theorem sampledPredictable_predictableVarianceSquareProbabilisticSparseLossRealizedMarkovHighProbabilityRegret_tail
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
    (horizon sparsity : Nat) (hhorizon : 0 < horizon)
    (delta : Real) (hdelta : 0 < delta) :
    let mu := prior ⊗ₘ sampledImportanceWeightedTrajectoryKernel arms harms
      eta gamma hgamma_pos.le hgamma_lt_one.le loss.environment
    mu {sample |
        sampledPredictableVarianceSquareProbabilisticSparseLossRealizedMarkovHighProbabilityRegretBudget
            arms eta gamma horizon sparsity delta ≤
          (Finset.range horizon).sum (fun t =>
              sampledTrajectoryRealizedLossAt t sample) -
            (Finset.range horizon).sum (fun t =>
              predictableLossAt loss t sample comparator)} ≤
      ENNReal.ofReal delta +
        mu (sampledPredictableSparsityFailure arms loss horizon sparsity) := by
  let mu := prior ⊗ₘ sampledImportanceWeightedTrajectoryKernel arms harms
    eta gamma hgamma_pos.le hgamma_lt_one.le loss.environment
  let lossMassBudget := (sparsity : Real) * (horizon : Real)
  let varianceMeanBudget :=
    sampledPredictableGlobalVarianceMeanBudget arms gamma horizon
  let varianceBudget := varianceMeanBudget / (delta / 5)
  let realizedBudget :=
    sampledPredictableVarianceSquareSmallLossRealizedHighProbabilityRegretBudget
      arms eta gamma horizon lossMassBudget varianceBudget
        (delta / 5) (delta / 5) (delta / 5)
  let sparsityBad :=
    sampledPredictableSparsityFailure arms loss horizon sparsity
  let realizedBad : Set (Env × ((k : Nat) → Action × Real)) :=
    {sample |
      realizedBudget ≤
        (Finset.range horizon).sum (fun t =>
            sampledTrajectoryRealizedLossAt t sample) -
          (Finset.range horizon).sum (fun t =>
            predictableLossAt loss t sample comparator)}
  let varianceSum := sampledPredictableMixedSquaredVarianceSum
    arms eta gamma loss horizon
  let varianceGood : Set (Env × ((k : Nat) → Action × Real)) :=
    {sample | varianceSum sample ≤ varianceBudget}
  let varianceBad : Set (Env × ((k : Nat) → Action × Real)) :=
    {sample | varianceBudget < varianceSum sample}
  have hfifth_pos : 0 < delta / 5 := div_pos hdelta (by norm_num)
  have hfloor_pos : 0 < gamma / (arms.card : Real) :=
    div_pos hgamma_pos (Nat.cast_pos.2 (Finset.card_pos.mpr harms))
  have hmean_pos : 0 < varianceMeanBudget := by
    dsimp [varianceMeanBudget, sampledPredictableGlobalVarianceMeanBudget]
    exact mul_pos (one_div_pos.2 hfloor_pos)
      (mul_pos (Nat.cast_pos.2 (Finset.card_pos.mpr harms))
        (Nat.cast_pos.2 hhorizon))
  have hvarianceBudget : 0 < varianceBudget :=
    div_pos hmean_pos hfifth_pos
  have hmass : ∀ᵐ sample ∂mu,
      sampledPredictableLossMassSum arms loss horizon sample ≤
          lossMassBudget ∨
        sample ∈ sparsityBad := by
    exact Filter.Eventually.of_forall fun sample => by
      simpa [lossMassBudget, sparsityBad] using
        sampledPredictableLossMassSum_le_or_mem_sparsityFailure
          arms loss horizon sparsity sample
  have hjoint : mu (realizedBad ∩ varianceGood) ≤
      (((ENNReal.ofReal (delta / 5) + ENNReal.ofReal (delta / 5)) +
        ENNReal.ofReal (delta / 5)) + ENNReal.ofReal (delta / 5)) +
          mu sparsityBad := by
    have h :=
      sampledPredictable_predictableVarianceSquareSmallLossRealizedHighProbabilityRegret_tail_joint_of_lossMassSum_le_or_mem
        prior arms harms eta gamma heta hgamma_pos hgamma_lt_one loss comparator
          hcomparator horizon hhorizon lossMassBudget varianceBudget
          (delta / 5) (delta / 5) (delta / 5) hvarianceBudget
          hfifth_pos hfifth_pos hfifth_pos sparsityBad hmass
    dsimp only at h
    simpa [mu, realizedBad, varianceGood, varianceSum, realizedBudget] using h
  have hvarianceLIntegral :
      sampledPredictableMixedSquaredVarianceLIntegral
          mu arms eta gamma loss horizon ≤ ENNReal.ofReal varianceMeanBudget := by
    simpa [varianceMeanBudget] using
      sampledPredictableMixedSquaredVarianceLIntegral_le_globalLossMass
        mu arms harms eta gamma hgamma_pos hgamma_lt_one.le loss horizon
  have hoverflowBase :=
    measure_sampledPredictableMixedSquaredVarianceSum_gt_le_lintegral_div
      mu arms harms eta gamma hgamma_pos hgamma_lt_one.le loss horizon
        varianceBudget hvarianceBudget
  have hmean_ne_zero : ENNReal.ofReal varianceMeanBudget ≠ 0 :=
    (ENNReal.ofReal_pos.2 hmean_pos).ne'
  have hratio :
      ENNReal.ofReal varianceMeanBudget / ENNReal.ofReal varianceBudget =
        ENNReal.ofReal (delta / 5) := by
    dsimp [varianceBudget]
    rw [ENNReal.ofReal_div_of_pos hfifth_pos]
    exact ENNReal.div_div_cancel hmean_ne_zero ENNReal.ofReal_ne_top
  have hoverflow : mu varianceBad ≤ ENNReal.ofReal (delta / 5) := by
    calc
      mu varianceBad ≤
          sampledPredictableMixedSquaredVarianceLIntegral
              mu arms eta gamma loss horizon /
            ENNReal.ofReal varianceBudget := by
        simpa [varianceBad, varianceSum, sampledPredictableMixedSquaredVarianceSum]
          using hoverflowBase
      _ ≤ ENNReal.ofReal varianceMeanBudget /
          ENNReal.ofReal varianceBudget :=
        ENNReal.div_le_div hvarianceLIntegral le_rfl
      _ = ENNReal.ofReal (delta / 5) := hratio
  have hsplit : realizedBad ⊆ (realizedBad ∩ varianceGood) ∪ varianceBad := by
    intro sample hregret
    by_cases hvariance : varianceSum sample ≤ varianceBudget
    · exact Or.inl ⟨hregret, hvariance⟩
    · exact Or.inr (lt_of_not_ge hvariance)
  have hfifth_nonneg : 0 ≤ delta / 5 := hfifth_pos.le
  have hprob :
      (((ENNReal.ofReal (delta / 5) + ENNReal.ofReal (delta / 5)) +
          ENNReal.ofReal (delta / 5)) + ENNReal.ofReal (delta / 5)) +
          ENNReal.ofReal (delta / 5) = ENNReal.ofReal delta := by
    rw [← ENNReal.ofReal_add hfifth_nonneg hfifth_nonneg]
    rw [← ENNReal.ofReal_add
      (add_nonneg hfifth_nonneg hfifth_nonneg) hfifth_nonneg]
    rw [← ENNReal.ofReal_add
      (add_nonneg (add_nonneg hfifth_nonneg hfifth_nonneg)
        hfifth_nonneg) hfifth_nonneg]
    rw [← ENNReal.ofReal_add
      (add_nonneg
        (add_nonneg (add_nonneg hfifth_nonneg hfifth_nonneg)
          hfifth_nonneg) hfifth_nonneg) hfifth_nonneg]
    congr 1
    ring
  have htail : mu realizedBad ≤ ENNReal.ofReal delta + mu sparsityBad := by
    calc
      mu realizedBad ≤ mu ((realizedBad ∩ varianceGood) ∪ varianceBad) :=
        measure_mono hsplit
      _ ≤ mu (realizedBad ∩ varianceGood) + mu varianceBad :=
        measure_union_le _ _
      _ ≤ ((((ENNReal.ofReal (delta / 5) + ENNReal.ofReal (delta / 5)) +
              ENNReal.ofReal (delta / 5)) + ENNReal.ofReal (delta / 5)) +
              mu sparsityBad) + ENNReal.ofReal (delta / 5) :=
        add_le_add hjoint hoverflow
      _ = (((ENNReal.ofReal (delta / 5) + ENNReal.ofReal (delta / 5)) +
              ENNReal.ofReal (delta / 5)) + ENNReal.ofReal (delta / 5) +
              ENNReal.ofReal (delta / 5)) + mu sparsityBad := by
        simp only [add_assoc, add_comm]
      _ = ENNReal.ofReal delta + mu sparsityBad := by rw [hprob]
  simpa [mu, realizedBad, realizedBudget, varianceBudget, varianceMeanBudget,
    lossMassBudget, sparsityBad,
    sampledPredictableVarianceSquareProbabilisticSparseLossRealizedMarkovHighProbabilityRegretBudget]
    using htail

/-- Practical `delta + epsilon` consumer of the explicit sparsity-failure
residual theorem. -/
theorem sampledPredictable_predictableVarianceSquareProbabilisticSparseLossRealizedMarkovHighProbabilityRegret_tail_of_sparsityFailure_le
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
    (horizon sparsity : Nat) (hhorizon : 0 < horizon)
    (delta epsilon : Real) (hdelta : 0 < delta)
    (hfailure :
      (prior ⊗ₘ sampledImportanceWeightedTrajectoryKernel arms harms
        eta gamma hgamma_pos.le hgamma_lt_one.le loss.environment)
          (sampledPredictableSparsityFailure arms loss horizon sparsity) ≤
        ENNReal.ofReal epsilon) :
    let mu := prior ⊗ₘ sampledImportanceWeightedTrajectoryKernel arms harms
      eta gamma hgamma_pos.le hgamma_lt_one.le loss.environment
    mu {sample |
        sampledPredictableVarianceSquareProbabilisticSparseLossRealizedMarkovHighProbabilityRegretBudget
            arms eta gamma horizon sparsity delta ≤
          (Finset.range horizon).sum (fun t =>
              sampledTrajectoryRealizedLossAt t sample) -
            (Finset.range horizon).sum (fun t =>
              predictableLossAt loss t sample comparator)} ≤
      ENNReal.ofReal delta + ENNReal.ofReal epsilon := by
  dsimp only
  have htail :=
    sampledPredictable_predictableVarianceSquareProbabilisticSparseLossRealizedMarkovHighProbabilityRegret_tail
      prior arms harms eta gamma heta hgamma_pos hgamma_lt_one loss comparator
        hcomparator horizon sparsity hhorizon delta hdelta
  dsimp only at htail
  exact htail.trans (add_le_add le_rfl hfailure)

end BanditRLProof.Exp3
