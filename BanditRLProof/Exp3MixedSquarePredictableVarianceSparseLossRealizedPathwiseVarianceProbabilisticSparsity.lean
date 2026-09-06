import BanditRLProof.Exp3MixedSquarePredictableVarianceSparseLossRealizedMarkovProbabilisticSparsity

/-!
# Pathwise sparse variance under probabilistic sparsity

This module removes the global `arms.card * horizon` Markov envelope from the
positive-probability sparsity route. Outside the explicit sparsity-failure
event, the armwise loss mass is at most `sparsity * horizon`; the existing
pointwise mixed-square variance inequality therefore gives the deterministic
variance budget

`(1 / (gamma / arms.card)) * (sparsity * horizon)`.

The realized-regret proof uses four confidence events at `delta / 4`. The
sparsity-failure event is charged exactly once, and no measurability assumption
on that event is required.
-/

namespace BanditRLProof.Exp3

open MeasureTheory ProbabilityTheory

universe u v

/-- Deterministic cumulative predictable-variance budget on trajectories that
obey the requested support-cardinality cap. -/
noncomputable def sampledPredictableSparsePathwiseVarianceBudget
    {Action : Type v} [DecidableEq Action]
    (arms : Finset Action) (gamma : Real) (horizon sparsity : Nat) : Real :=
  (1 / (gamma / (arms.card : Real))) *
    ((sparsity : Real) * (horizon : Real))

/-- Every trajectory either obeys the sparse pathwise variance budget or lies
in the explicit sparsity-failure event. -/
theorem sampledPredictableMixedSquaredVarianceSum_le_sparsePathwiseVarianceBudget_or_mem_sparsityFailure
    {Env : Type u} {Action : Type v}
    [MeasurableSpace Env]
    [MeasurableSpace Action] [MeasurableSingletonClass Action]
    [DecidableEq Action]
    (arms : Finset Action) (harms : arms.Nonempty)
    (eta gamma : Real) (hgamma_pos : 0 < gamma)
    (hgamma_le_one : gamma ≤ 1)
    (loss : PredictableLossVector Env Action)
    (horizon sparsity : Nat)
    (sample : Env × ((k : Nat) → Action × Real)) :
    sampledPredictableMixedSquaredVarianceSum
        arms eta gamma loss horizon sample ≤
        sampledPredictableSparsePathwiseVarianceBudget
          arms gamma horizon sparsity ∨
      sample ∈ sampledPredictableSparsityFailure
        arms loss horizon sparsity := by
  rcases sampledPredictableLossMassSum_le_or_mem_sparsityFailure
      arms loss horizon sparsity sample with hmass | hbad
  · left
    have hfloor_pos : 0 < gamma / (arms.card : Real) :=
      div_pos hgamma_pos (Nat.cast_pos.2 (Finset.card_pos.mpr harms))
    exact
      (sampledPredictableMixedSquaredVarianceSum_le_inv_floor_mul_lossMassSum
        arms harms eta gamma hgamma_pos hgamma_le_one loss horizon sample).trans
        (mul_le_mul_of_nonneg_left hmass (one_div_nonneg.2 hfloor_pos.le))
  · exact Or.inr hbad

/-- Four-event realized sparse-loss budget with deterministic pathwise
predictable variance on the sparsity-good event. -/
noncomputable def sampledPredictableVarianceSquareProbabilisticSparseLossRealizedPathwiseVarianceHighProbabilityRegretBudget
    {Action : Type v} [DecidableEq Action]
    (arms : Finset Action) (eta gamma : Real) (horizon sparsity : Nat)
    (delta : Real) : Real :=
  sampledPredictableVarianceSquareSmallLossRealizedHighProbabilityRegretBudget
    arms eta gamma horizon ((sparsity : Real) * (horizon : Real))
      (sampledPredictableSparsePathwiseVarianceBudget
        arms gamma horizon sparsity)
      (delta / 4) (delta / 4) (delta / 4)

/-- Generated realized regret away from the exact support-sparsity failure
event. Only the four confidence events remain after removing the common
sparsity-failure set. -/
theorem sampledPredictable_predictableVarianceSquareProbabilisticSparseLossRealizedPathwiseVarianceHighProbabilityRegret_tail_off_sparsityFailure
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
    (hsparsity : 0 < sparsity)
    (delta : Real) (hdelta : 0 < delta) :
    let mu := prior ⊗ₘ sampledImportanceWeightedTrajectoryKernel arms harms
      eta gamma hgamma_pos.le hgamma_lt_one.le loss.environment
    mu ({sample |
        sampledPredictableVarianceSquareProbabilisticSparseLossRealizedPathwiseVarianceHighProbabilityRegretBudget
            arms eta gamma horizon sparsity delta ≤
          (Finset.range horizon).sum (fun t =>
              sampledTrajectoryRealizedLossAt t sample) -
            (Finset.range horizon).sum (fun t =>
              predictableLossAt loss t sample comparator)} \
      sampledPredictableSparsityFailure arms loss horizon sparsity) ≤
        ENNReal.ofReal delta := by
  let mu := prior ⊗ₘ sampledImportanceWeightedTrajectoryKernel arms harms
    eta gamma hgamma_pos.le hgamma_lt_one.le loss.environment
  let lossMassBudget := (sparsity : Real) * (horizon : Real)
  let varianceBudget :=
    sampledPredictableSparsePathwiseVarianceBudget
      arms gamma horizon sparsity
  let realizedBudget :=
    sampledPredictableVarianceSquareSmallLossRealizedHighProbabilityRegretBudget
      arms eta gamma horizon lossMassBudget varianceBudget
        (delta / 4) (delta / 4) (delta / 4)
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
  have hquarter_pos : 0 < delta / 4 := div_pos hdelta (by norm_num)
  have hfloor_pos : 0 < gamma / (arms.card : Real) :=
    div_pos hgamma_pos (Nat.cast_pos.2 (Finset.card_pos.mpr harms))
  have hlossMassBudget_pos : 0 < lossMassBudget := by
    dsimp [lossMassBudget]
    exact mul_pos (Nat.cast_pos.2 hsparsity) (Nat.cast_pos.2 hhorizon)
  have hvarianceBudget : 0 < varianceBudget := by
    dsimp [varianceBudget, sampledPredictableSparsePathwiseVarianceBudget]
    exact mul_pos (one_div_pos.2 hfloor_pos) hlossMassBudget_pos
  have hmass : ∀ᵐ sample ∂mu,
      sampledPredictableLossMassSum arms loss horizon sample ≤
          lossMassBudget ∨
        sample ∈ sparsityBad := by
    exact Filter.Eventually.of_forall fun sample => by
      simpa [lossMassBudget, sparsityBad] using
        sampledPredictableLossMassSum_le_or_mem_sparsityFailure
          arms loss horizon sparsity sample
  have hjoint :
      mu ((realizedBad ∩ varianceGood) \ sparsityBad) ≤
        (((ENNReal.ofReal (delta / 4) + ENNReal.ofReal (delta / 4)) +
          ENNReal.ofReal (delta / 4)) + ENNReal.ofReal (delta / 4)) := by
    have h :=
      sampledPredictable_predictableVarianceSquareSmallLossRealizedHighProbabilityRegret_tail_joint_off_bad_of_lossMassSum_le_or_mem
        prior arms harms eta gamma heta hgamma_pos hgamma_lt_one loss comparator
          hcomparator horizon hhorizon lossMassBudget varianceBudget
          (delta / 4) (delta / 4) (delta / 4) hvarianceBudget
          hquarter_pos hquarter_pos hquarter_pos sparsityBad hmass
    dsimp only at h
    simpa [mu, realizedBad, varianceGood, varianceSum, realizedBudget] using h
  have hvarianceOrBad : ∀ sample,
      varianceSum sample ≤ varianceBudget ∨ sample ∈ sparsityBad := by
    intro sample
    simpa [varianceSum, varianceBudget, sparsityBad] using
      sampledPredictableMixedSquaredVarianceSum_le_sparsePathwiseVarianceBudget_or_mem_sparsityFailure
        arms harms eta gamma hgamma_pos hgamma_lt_one.le loss horizon sparsity sample
  have hsplit :
      realizedBad \ sparsityBad ⊆
        (realizedBad ∩ varianceGood) \ sparsityBad := by
    intro sample hsample
    refine ⟨⟨hsample.1, ?_⟩, hsample.2⟩
    rcases hvarianceOrBad sample with hvariance | hbad
    · exact hvariance
    · exact (hsample.2 hbad).elim
  have hquarter_nonneg : 0 ≤ delta / 4 := hquarter_pos.le
  have hprob :
      (((ENNReal.ofReal (delta / 4) + ENNReal.ofReal (delta / 4)) +
          ENNReal.ofReal (delta / 4)) + ENNReal.ofReal (delta / 4)) =
        ENNReal.ofReal delta := by
    rw [← ENNReal.ofReal_add hquarter_nonneg hquarter_nonneg]
    rw [← ENNReal.ofReal_add
      (add_nonneg hquarter_nonneg hquarter_nonneg) hquarter_nonneg]
    rw [← ENNReal.ofReal_add
      (add_nonneg (add_nonneg hquarter_nonneg hquarter_nonneg)
        hquarter_nonneg) hquarter_nonneg]
    congr 1
    ring
  have htail : mu (realizedBad \ sparsityBad) ≤ ENNReal.ofReal delta := by
    calc
      mu (realizedBad \ sparsityBad) ≤
          mu ((realizedBad ∩ varianceGood) \ sparsityBad) :=
        measure_mono hsplit
      _ ≤ (((ENNReal.ofReal (delta / 4) + ENNReal.ofReal (delta / 4)) +
            ENNReal.ofReal (delta / 4)) + ENNReal.ofReal (delta / 4)) :=
        hjoint
      _ = ENNReal.ofReal delta := hprob
  simpa [mu, realizedBad, realizedBudget, varianceBudget, lossMassBudget,
    sparsityBad,
    sampledPredictableVarianceSquareProbabilisticSparseLossRealizedPathwiseVarianceHighProbabilityRegretBudget]
    using htail

/-- Generated realized regret under probabilistic sparsity and deterministic
pathwise variance on the good event. The common support-sparsity failure set
is added exactly once to the off-bad confidence tail. -/
theorem sampledPredictable_predictableVarianceSquareProbabilisticSparseLossRealizedPathwiseVarianceHighProbabilityRegret_tail
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
    (hsparsity : 0 < sparsity)
    (delta : Real) (hdelta : 0 < delta) :
    let mu := prior ⊗ₘ sampledImportanceWeightedTrajectoryKernel arms harms
      eta gamma hgamma_pos.le hgamma_lt_one.le loss.environment
    mu {sample |
        sampledPredictableVarianceSquareProbabilisticSparseLossRealizedPathwiseVarianceHighProbabilityRegretBudget
            arms eta gamma horizon sparsity delta ≤
          (Finset.range horizon).sum (fun t =>
              sampledTrajectoryRealizedLossAt t sample) -
            (Finset.range horizon).sum (fun t =>
              predictableLossAt loss t sample comparator)} ≤
      ENNReal.ofReal delta +
        mu (sampledPredictableSparsityFailure arms loss horizon sparsity) := by
  let mu := prior ⊗ₘ sampledImportanceWeightedTrajectoryKernel arms harms
    eta gamma hgamma_pos.le hgamma_lt_one.le loss.environment
  let sparsityBad :=
    sampledPredictableSparsityFailure arms loss horizon sparsity
  let realizedBad : Set (Env × ((k : Nat) → Action × Real)) :=
    {sample |
      sampledPredictableVarianceSquareProbabilisticSparseLossRealizedPathwiseVarianceHighProbabilityRegretBudget
          arms eta gamma horizon sparsity delta ≤
        (Finset.range horizon).sum (fun t =>
            sampledTrajectoryRealizedLossAt t sample) -
          (Finset.range horizon).sum (fun t =>
            predictableLossAt loss t sample comparator)}
  have hoff :=
    sampledPredictable_predictableVarianceSquareProbabilisticSparseLossRealizedPathwiseVarianceHighProbabilityRegret_tail_off_sparsityFailure
      prior arms harms eta gamma heta hgamma_pos hgamma_lt_one loss comparator
        hcomparator horizon sparsity hhorizon hsparsity delta hdelta
  dsimp only at hoff
  have hsplit : realizedBad ⊆ (realizedBad \ sparsityBad) ∪ sparsityBad := by
    intro sample hsample
    by_cases hbad : sample ∈ sparsityBad
    · exact Or.inr hbad
    · exact Or.inl ⟨hsample, hbad⟩
  have htail : mu realizedBad ≤ ENNReal.ofReal delta + mu sparsityBad := by
    calc
      mu realizedBad ≤ mu ((realizedBad \ sparsityBad) ∪ sparsityBad) :=
        measure_mono hsplit
      _ ≤ mu (realizedBad \ sparsityBad) + mu sparsityBad :=
        measure_union_le _ _
      _ ≤ ENNReal.ofReal delta + mu sparsityBad :=
        add_le_add (by simpa [mu, realizedBad, sparsityBad] using hoff) le_rfl
  simpa [mu, realizedBad, sparsityBad] using htail

/-- Practical `delta + epsilon` consumer of the pathwise-variance residual
theorem. -/
theorem sampledPredictable_predictableVarianceSquareProbabilisticSparseLossRealizedPathwiseVarianceHighProbabilityRegret_tail_of_sparsityFailure_le
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
    (hsparsity : 0 < sparsity)
    (delta epsilon : Real) (hdelta : 0 < delta)
    (hfailure :
      (prior ⊗ₘ sampledImportanceWeightedTrajectoryKernel arms harms
        eta gamma hgamma_pos.le hgamma_lt_one.le loss.environment)
          (sampledPredictableSparsityFailure arms loss horizon sparsity) ≤
        ENNReal.ofReal epsilon) :
    let mu := prior ⊗ₘ sampledImportanceWeightedTrajectoryKernel arms harms
      eta gamma hgamma_pos.le hgamma_lt_one.le loss.environment
    mu {sample |
        sampledPredictableVarianceSquareProbabilisticSparseLossRealizedPathwiseVarianceHighProbabilityRegretBudget
            arms eta gamma horizon sparsity delta ≤
          (Finset.range horizon).sum (fun t =>
              sampledTrajectoryRealizedLossAt t sample) -
            (Finset.range horizon).sum (fun t =>
              predictableLossAt loss t sample comparator)} ≤
      ENNReal.ofReal delta + ENNReal.ofReal epsilon := by
  dsimp only
  have htail :=
    sampledPredictable_predictableVarianceSquareProbabilisticSparseLossRealizedPathwiseVarianceHighProbabilityRegret_tail
      prior arms harms eta gamma heta hgamma_pos hgamma_lt_one loss comparator
        hcomparator horizon sparsity hhorizon hsparsity delta hdelta
  dsimp only at htail
  exact htail.trans (add_le_add le_rfl hfailure)

end BanditRLProof.Exp3
