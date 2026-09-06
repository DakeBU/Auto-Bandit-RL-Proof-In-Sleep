import BanditRLProof.Exp3MixedSquarePredictableVarianceSmallLossRealizedMarkovHighProbabilityRegret

/-!
# Sparse-loss control of realized predictable-variance EXP3 regret

This module discharges the pathwise armwise loss-mass premise of the small-loss
route from a per-round support-cardinality contract. The local proof route is:

1. restrict each predictable loss vector to its nonzero support in `arms`;
2. use the `[0,1]` loss range to bound its mass by the support cardinality;
3. sum a uniform support-cardinality bound over `Finset.range horizon`;
4. instantiate the compiled small-loss realized Markov theorem with
   `lossMassBudget = sparsity * horizon`.

The primary generated theorem only requires the support contract almost
everywhere under its exact trajectory measure. A compatibility theorem retains
the stronger pathwise contract uniform over all generated samples. Neither
surface asserts a best-arm first-order bound, tunes `eta` or `gamma`, or
replaces Markov overflow.
-/

namespace BanditRLProof.Exp3

open MeasureTheory ProbabilityTheory

universe u v

/-- Nonzero predictable-loss coordinates among the active arms at one time. -/
noncomputable def sampledPredictableLossSupport
    {Env : Type u} {Action : Type v}
    [MeasurableSpace Env] [MeasurableSpace Action]
    (arms : Finset Action) (loss : PredictableLossVector Env Action)
    (t : Nat) (sample : Env × ((k : Nat) → Action × Real)) : Finset Action := by
  classical
  exact arms.filter fun action => predictableLossAt loss t sample action ≠ 0

/-- The predictable loss mass at one time is at most the number of active
nonzero loss coordinates. -/
theorem sampledPredictableLossMassAt_le_supportCard
    {Env : Type u} {Action : Type v}
    [MeasurableSpace Env] [MeasurableSpace Action]
    (arms : Finset Action) (loss : PredictableLossVector Env Action)
    (t : Nat) (sample : Env × ((k : Nat) → Action × Real)) :
    arms.sum (fun action => predictableLossAt loss t sample action) ≤
      (sampledPredictableLossSupport arms loss t sample).card := by
  classical
  let support := sampledPredictableLossSupport arms loss t sample
  have hsum :
      arms.sum (fun action => predictableLossAt loss t sample action) =
        support.sum (fun action => predictableLossAt loss t sample action) := by
    symm
    apply Finset.sum_subset
    · exact Finset.filter_subset _ _
    · intro action haction hnot
      simp only [support, sampledPredictableLossSupport, Finset.mem_filter,
        not_and, ne_eq] at hnot
      exact not_ne_iff.mp (hnot haction)
  rw [hsum]
  calc
    support.sum (fun action => predictableLossAt loss t sample action) ≤
        support.sum (fun _action => (1 : Real)) := by
      apply Finset.sum_le_sum
      intro action _haction
      exact (predictableLossAt_mem_unitInterval loss t sample action).2
    _ = (support.card : Real) := by simp

/-- A per-round support-cardinality bound for one trajectory supplies its
armwise loss-mass budget. -/
theorem sampledPredictableLossMassSum_le_sparsity_mul_horizon_of_sample
    {Env : Type u} {Action : Type v}
    [MeasurableSpace Env] [MeasurableSpace Action]
    (arms : Finset Action) (loss : PredictableLossVector Env Action)
    (horizon sparsity : Nat)
    (sample : Env × ((k : Nat) → Action × Real))
    (hsparse : ∀ t, t < horizon →
      (sampledPredictableLossSupport arms loss t sample).card ≤ sparsity) :
    sampledPredictableLossMassSum arms loss horizon sample ≤
      (sparsity : Real) * (horizon : Real) := by
  unfold sampledPredictableLossMassSum
  calc
    (Finset.range horizon).sum (fun t =>
        arms.sum (fun action => predictableLossAt loss t sample action)) ≤
        (Finset.range horizon).sum (fun _t => (sparsity : Real)) := by
      apply Finset.sum_le_sum
      intro t ht
      exact
        (sampledPredictableLossMassAt_le_supportCard arms loss t sample).trans
          (Nat.cast_le.2 (hsparse t (Finset.mem_range.1 ht)))
    _ = (sparsity : Real) * (horizon : Real) := by
      simp [mul_comm]

/-- A uniform per-round support-cardinality bound supplies the pathwise armwise
loss-mass budget used by the small-loss theorem. -/
theorem sampledPredictableLossMassSum_le_sparsity_mul_horizon
    {Env : Type u} {Action : Type v}
    [MeasurableSpace Env] [MeasurableSpace Action]
    (arms : Finset Action) (loss : PredictableLossVector Env Action)
    (horizon sparsity : Nat)
    (hsparse : ∀ sample t, t < horizon →
      (sampledPredictableLossSupport arms loss t sample).card ≤ sparsity)
    (sample : Env × ((k : Nat) → Action × Real)) :
    sampledPredictableLossMassSum arms loss horizon sample ≤
      (sparsity : Real) * (horizon : Real) :=
  sampledPredictableLossMassSum_le_sparsity_mul_horizon_of_sample
    arms loss horizon sparsity sample (hsparse sample)

/-- Sparse-loss specialization of the five-event realized regret budget. -/
noncomputable def sampledPredictableVarianceSquareSparseLossRealizedMarkovHighProbabilityRegretBudget
    {Action : Type v} [DecidableEq Action]
    (arms : Finset Action) (eta gamma : Real) (horizon sparsity : Nat)
    (delta : Real) : Real :=
  sampledPredictableVarianceSquareSmallLossRealizedMarkovHighProbabilityRegretBudget
    arms eta gamma horizon ((sparsity : Real) * (horizon : Real)) delta

/-- Realized predictable-variance EXP3 regret when the per-round nonzero-loss
support-cardinality bound holds almost everywhere under the exact generated
trajectory measure. -/
theorem sampledPredictable_predictableVarianceSquareSparseLossRealizedMarkovHighProbabilityRegret_tail_total_delta_of_ae_sparsity
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
    (hsparsity : 0 < sparsity) (delta : Real) (hdelta : 0 < delta)
    (hsparse : ∀ᵐ sample ∂(prior ⊗ₘ
        sampledImportanceWeightedTrajectoryKernel arms harms
          eta gamma hgamma_pos.le hgamma_lt_one.le loss.environment),
      ∀ t, t < horizon →
      (sampledPredictableLossSupport arms loss t sample).card ≤ sparsity) :
    let mu := prior ⊗ₘ sampledImportanceWeightedTrajectoryKernel arms harms
      eta gamma hgamma_pos.le hgamma_lt_one.le loss.environment
    mu {sample |
        sampledPredictableVarianceSquareSparseLossRealizedMarkovHighProbabilityRegretBudget
            arms eta gamma horizon sparsity delta ≤
          (Finset.range horizon).sum (fun t =>
              sampledTrajectoryRealizedLossAt t sample) -
            (Finset.range horizon).sum (fun t =>
              predictableLossAt loss t sample comparator)} ≤
      ENNReal.ofReal delta := by
  have hmass : ∀ᵐ sample ∂(prior ⊗ₘ
      sampledImportanceWeightedTrajectoryKernel arms harms
        eta gamma hgamma_pos.le hgamma_lt_one.le loss.environment),
      sampledPredictableLossMassSum arms loss horizon sample ≤
        (sparsity : Real) * (horizon : Real) := by
    filter_upwards [hsparse] with sample hsparseSample
    exact
      sampledPredictableLossMassSum_le_sparsity_mul_horizon_of_sample
        arms loss horizon sparsity sample hsparseSample
  have hmass_pos :
      0 < (sparsity : Real) * (horizon : Real) :=
    mul_pos (Nat.cast_pos.2 hsparsity) (Nat.cast_pos.2 hhorizon)
  simpa [
    sampledPredictableVarianceSquareSparseLossRealizedMarkovHighProbabilityRegretBudget
  ] using
    sampledPredictable_predictableVarianceSquareSmallLossRealizedMarkovHighProbabilityRegret_tail_total_delta
      prior arms harms eta gamma heta hgamma_pos hgamma_lt_one loss comparator
        hcomparator horizon hhorizon
        ((sparsity : Real) * (horizon : Real)) delta hmass_pos hdelta hmass

/-- Backward-compatible pathwise sparse-loss wrapper. The stronger universal
contract is converted to the generated-measure almost-everywhere contract used
by the primary theorem. -/
theorem sampledPredictable_predictableVarianceSquareSparseLossRealizedMarkovHighProbabilityRegret_tail_total_delta
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
    (hsparsity : 0 < sparsity) (delta : Real) (hdelta : 0 < delta)
    (hsparse : ∀ sample t, t < horizon →
      (sampledPredictableLossSupport arms loss t sample).card ≤ sparsity) :
    let mu := prior ⊗ₘ sampledImportanceWeightedTrajectoryKernel arms harms
      eta gamma hgamma_pos.le hgamma_lt_one.le loss.environment
    mu {sample |
        sampledPredictableVarianceSquareSparseLossRealizedMarkovHighProbabilityRegretBudget
            arms eta gamma horizon sparsity delta ≤
          (Finset.range horizon).sum (fun t =>
              sampledTrajectoryRealizedLossAt t sample) -
            (Finset.range horizon).sum (fun t =>
              predictableLossAt loss t sample comparator)} ≤
      ENNReal.ofReal delta := by
  apply
    sampledPredictable_predictableVarianceSquareSparseLossRealizedMarkovHighProbabilityRegret_tail_total_delta_of_ae_sparsity
      prior arms harms eta gamma heta hgamma_pos hgamma_lt_one loss comparator
        hcomparator horizon sparsity hhorizon hsparsity delta hdelta
  exact Filter.Eventually.of_forall fun sample t ht => hsparse sample t ht

end BanditRLProof.Exp3
