import BanditRLProof.Exp3MixedSquarePredictableVarianceSparseLossRealizedPathwiseVarianceProbabilisticSparsity

/-!
# Learning-rate tuning with pathwise variance under probabilistic sparsity

This module tunes `eta` for the four-event probabilistic-sparsity route. Its
variance budget is the deterministic good-path bound

`(1 / (gamma / arms.card)) * (sparsity * horizon)`,

and its confidence allocation is `delta / 4`. Thus the tuned theorem retains
the exact sparsity-failure residual without the global `arms.card * horizon`
Markov envelope or a fifth overflow event.

Gamma remains caller-selected.
-/

namespace BanditRLProof.Exp3

open MeasureTheory ProbabilityTheory

universe u v

/-- Complete Hedge scale using sparse loss mass and sparse pathwise variance. -/
noncomputable def pathwiseVarianceProbabilisticSparseLossHighProbabilityScale
    {Action : Type v} [DecidableEq Action]
    (arms : Finset Action) (gamma : Real)
    (horizon sparsity : Nat) (delta : Real) : Real :=
  (sparsity : Real) * (horizon : Real) +
    sampledMixedSquaredPredictableVarianceRadius arms gamma
      (sampledPredictableSparsePathwiseVarianceBudget
        arms gamma horizon sparsity)
      (delta / 4)

theorem pathwiseVarianceProbabilisticSparseLossHighProbabilityScale_pos
    {Action : Type v} [DecidableEq Action]
    (arms : Finset Action) (hcard_two : 2 ≤ arms.card)
    (gamma : Real) (hgamma_pos : 0 < gamma)
    (horizon sparsity : Nat) (hhorizon : 0 < horizon)
    (hsparsity : 0 < sparsity) (delta : Real) :
    0 < pathwiseVarianceProbabilisticSparseLossHighProbabilityScale
      arms gamma horizon sparsity delta := by
  have hcard_pos : 0 < (arms.card : Real) := by positivity
  have hfloor_pos : 0 < gamma / (arms.card : Real) :=
    div_pos hgamma_pos hcard_pos
  have hloss_pos :
      0 < (sparsity : Real) * (horizon : Real) :=
    mul_pos (Nat.cast_pos.2 hsparsity) (Nat.cast_pos.2 hhorizon)
  have hvariance_nonneg :
      0 ≤ sampledPredictableSparsePathwiseVarianceBudget
        arms gamma horizon sparsity := by
    dsimp [sampledPredictableSparsePathwiseVarianceBudget]
    positivity
  have hlog_nonneg : 0 ≤ max (Real.log (1 / (delta / 4))) 0 :=
    le_max_right _ _
  have hradius_nonneg :
      0 ≤ sampledMixedSquaredPredictableVarianceRadius arms gamma
        (sampledPredictableSparsePathwiseVarianceBudget
          arms gamma horizon sparsity)
        (delta / 4) := by
    dsimp [sampledMixedSquaredPredictableVarianceRadius]
    exact add_nonneg
      (mul_nonneg (by norm_num)
        (Real.sqrt_nonneg
          (sampledPredictableSparsePathwiseVarianceBudget
            arms gamma horizon sparsity *
              max (Real.log (1 / (delta / 4))) 0)))
      (div_nonneg hlog_nonneg hfloor_pos.le)
  dsimp [pathwiseVarianceProbabilisticSparseLossHighProbabilityScale]
  linarith

/-- Learning rate balancing entropy against the four-event sparse scale. -/
noncomputable def pathwiseVarianceProbabilisticSparseLossHighProbabilityLearningRate
    {Action : Type v} [DecidableEq Action]
    (arms : Finset Action) (gamma : Real)
    (horizon sparsity : Nat) (delta : Real) : Real :=
  Real.sqrt
    (Real.log (arms.card : Real) /
      pathwiseVarianceProbabilisticSparseLossHighProbabilityScale
        arms gamma horizon sparsity delta)

theorem pathwiseVarianceProbabilisticSparseLossHighProbabilityLearningRate_pos
    {Action : Type v} [DecidableEq Action]
    (arms : Finset Action) (hcard_two : 2 ≤ arms.card)
    (gamma : Real) (hgamma_pos : 0 < gamma)
    (horizon sparsity : Nat) (hhorizon : 0 < horizon)
    (hsparsity : 0 < sparsity) (delta : Real) :
    0 < pathwiseVarianceProbabilisticSparseLossHighProbabilityLearningRate
      arms gamma horizon sparsity delta := by
  have hK_one : 1 < (arms.card : Real) := by
    exact_mod_cast hcard_two
  have hscale :=
    pathwiseVarianceProbabilisticSparseLossHighProbabilityScale_pos
      arms hcard_two gamma hgamma_pos horizon sparsity hhorizon hsparsity delta
  apply Real.sqrt_pos.2
  exact div_pos (Real.log_pos hK_one) hscale

theorem pathwiseVarianceProbabilisticSparseLossHighProbabilityLearningRate_sq_mul_scale
    {Action : Type v} [DecidableEq Action]
    (arms : Finset Action) (hcard_two : 2 ≤ arms.card)
    (gamma : Real) (hgamma_pos : 0 < gamma)
    (horizon sparsity : Nat) (hhorizon : 0 < horizon)
    (hsparsity : 0 < sparsity) (delta : Real) :
    pathwiseVarianceProbabilisticSparseLossHighProbabilityLearningRate
          arms gamma horizon sparsity delta ^ 2 *
        pathwiseVarianceProbabilisticSparseLossHighProbabilityScale
          arms gamma horizon sparsity delta =
      Real.log (arms.card : Real) := by
  have hK_one : 1 < (arms.card : Real) := by
    exact_mod_cast hcard_two
  have hscale :=
    pathwiseVarianceProbabilisticSparseLossHighProbabilityScale_pos
      arms hcard_two gamma hgamma_pos horizon sparsity hhorizon hsparsity delta
  unfold pathwiseVarianceProbabilisticSparseLossHighProbabilityLearningRate
  rw [Real.sq_sqrt
    (div_nonneg (Real.log_pos hK_one).le hscale.le)]
  field_simp [ne_of_gt hscale]

/-- Under `gamma ≤ 1/2`, entropy and stability cost at most three balanced
copies of the four-event sparse scale. -/
theorem pathwiseVarianceProbabilisticSparseLossHighProbabilityHedgeBudget_le_three_mul_sqrt
    {Action : Type v} [DecidableEq Action]
    (arms : Finset Action) (hcard_two : 2 ≤ arms.card)
    (gamma : Real) (hgamma_pos : 0 < gamma)
    (hgamma_le_half : gamma ≤ 1 / 2)
    (horizon sparsity : Nat) (hhorizon : 0 < horizon)
    (hsparsity : 0 < sparsity) (delta : Real) :
    Real.log (arms.card : Real) /
          pathwiseVarianceProbabilisticSparseLossHighProbabilityLearningRate
            arms gamma horizon sparsity delta +
        (pathwiseVarianceProbabilisticSparseLossHighProbabilityLearningRate
            arms gamma horizon sparsity delta * (1 / (1 - gamma))) *
          pathwiseVarianceProbabilisticSparseLossHighProbabilityScale
            arms gamma horizon sparsity delta ≤
      3 * Real.sqrt
        (Real.log (arms.card : Real) *
          pathwiseVarianceProbabilisticSparseLossHighProbabilityScale
            arms gamma horizon sparsity delta) := by
  let eta :=
    pathwiseVarianceProbabilisticSparseLossHighProbabilityLearningRate
      arms gamma horizon sparsity delta
  let scale :=
    pathwiseVarianceProbabilisticSparseLossHighProbabilityScale
      arms gamma horizon sparsity delta
  let entropy := Real.log (arms.card : Real) / eta
  have hK_one : 1 < (arms.card : Real) := by
    exact_mod_cast hcard_two
  have heta : 0 < eta := by
    dsimp [eta]
    exact
      pathwiseVarianceProbabilisticSparseLossHighProbabilityLearningRate_pos
        arms hcard_two gamma hgamma_pos horizon sparsity hhorizon hsparsity delta
  have hscale : 0 < scale := by
    dsimp [scale]
    exact
      pathwiseVarianceProbabilisticSparseLossHighProbabilityScale_pos
        arms hcard_two gamma hgamma_pos horizon sparsity hhorizon hsparsity delta
  have hbalance : eta ^ 2 * scale = Real.log (arms.card : Real) := by
    dsimp [eta, scale]
    exact
      pathwiseVarianceProbabilisticSparseLossHighProbabilityLearningRate_sq_mul_scale
        arms hcard_two gamma hgamma_pos horizon sparsity hhorizon hsparsity delta
  have hentropy_nonneg : 0 ≤ entropy :=
    div_nonneg (Real.log_pos hK_one).le heta.le
  have hentropy_eq_unscaled : entropy = eta * scale := by
    dsimp [entropy]
    field_simp [ne_of_gt heta]
    nlinarith [hbalance]
  have hden : 0 < 1 - gamma := by linarith
  have hfactor : 1 ≤ 2 * (1 - gamma) := by linarith
  have hstable :
      (eta * (1 / (1 - gamma))) * scale ≤ 2 * entropy := by
    rw [show (eta * (1 / (1 - gamma))) * scale =
      (eta * scale) / (1 - gamma) by ring]
    rw [← hentropy_eq_unscaled, div_le_iff₀ hden]
    have hmul := mul_le_mul_of_nonneg_left hfactor hentropy_nonneg
    nlinarith
  have hbalanced_sq :
      entropy ^ 2 = Real.log (arms.card : Real) * scale := by
    rw [hentropy_eq_unscaled]
    calc
      (eta * scale) ^ 2 = (eta ^ 2 * scale) * scale := by ring
      _ = Real.log (arms.card : Real) * scale := by rw [hbalance]
  have hradicand_nonneg :
      0 ≤ Real.log (arms.card : Real) * scale :=
    mul_nonneg (Real.log_pos hK_one).le hscale.le
  have hentropy_eq_sqrt :
      entropy = Real.sqrt
        (Real.log (arms.card : Real) * scale) := by
    have hsqrt_nonneg :=
      Real.sqrt_nonneg (Real.log (arms.card : Real) * scale)
    have hsqrt_sq := Real.sq_sqrt hradicand_nonneg
    nlinarith [hbalanced_sq]
  change entropy + (eta * (1 / (1 - gamma))) * scale ≤
    3 * Real.sqrt (Real.log (arms.card : Real) * scale)
  rw [← hentropy_eq_sqrt]
  linarith

/-- Tuned regret threshold for the four-event pathwise-variance route. -/
noncomputable def pathwiseVarianceProbabilisticSparseLossRealizedTunedThreshold
    {Action : Type v} [DecidableEq Action]
    (arms : Finset Action) (gamma : Real)
    (horizon sparsity : Nat) (delta : Real) : Real :=
  3 * Real.sqrt
      (Real.log (arms.card : Real) *
        pathwiseVarianceProbabilisticSparseLossHighProbabilityScale
          arms gamma horizon sparsity delta) +
    gamma * (horizon : Real) +
    sampledPurePredictableMinusObservedBernsteinConfidenceRadius
      arms gamma horizon (delta / 4) +
    sampledComparatorEstimatorBernsteinConfidenceRadius
      arms gamma horizon (delta / 4) +
    sampledPredictableRealizedDeviationConfidenceRadius horizon (delta / 4)

/-- The raw four-event budget is bounded by the eta-tuned threshold. -/
theorem sampledPredictableVarianceSquareProbabilisticSparseLossRealizedPathwiseVarianceHighProbabilityRegretBudget_le_tunedThreshold
    {Action : Type v} [DecidableEq Action]
    (arms : Finset Action) (hcard_two : 2 ≤ arms.card)
    (gamma : Real) (hgamma_pos : 0 < gamma)
    (hgamma_le_half : gamma ≤ 1 / 2)
    (horizon sparsity : Nat) (hhorizon : 0 < horizon)
    (hsparsity : 0 < sparsity) (delta : Real) :
    sampledPredictableVarianceSquareProbabilisticSparseLossRealizedPathwiseVarianceHighProbabilityRegretBudget
        arms
        (pathwiseVarianceProbabilisticSparseLossHighProbabilityLearningRate
          arms gamma horizon sparsity delta)
        gamma horizon sparsity delta ≤
      pathwiseVarianceProbabilisticSparseLossRealizedTunedThreshold
        arms gamma horizon sparsity delta := by
  have hhedge :=
    pathwiseVarianceProbabilisticSparseLossHighProbabilityHedgeBudget_le_three_mul_sqrt
      arms hcard_two gamma hgamma_pos hgamma_le_half horizon sparsity
        hhorizon hsparsity delta
  dsimp [
    sampledPredictableVarianceSquareProbabilisticSparseLossRealizedPathwiseVarianceHighProbabilityRegretBudget,
    sampledPredictableVarianceSquareSmallLossRealizedHighProbabilityRegretBudget,
    sampledPredictableVarianceSquareSmallLossHighProbabilityRegretBudget,
    pathwiseVarianceProbabilisticSparseLossRealizedTunedThreshold,
    pathwiseVarianceProbabilisticSparseLossHighProbabilityScale
  ] at hhedge ⊢
  linarith

/-- Eta-tuned generated regret away from the exact sparsity-failure event. -/
theorem sampledPredictable_tunedProbabilisticSparseLossPathwiseVarianceRealizedRegret_tail_off_sparsityFailure
    {Env : Type u} {Action : Type v}
    [MeasurableSpace Env] [StandardBorelSpace Env] [Nonempty Env]
    [MeasurableSpace Action] [MeasurableSingletonClass Action]
    [StandardBorelSpace Action] [Nonempty Action] [DecidableEq Action]
    (prior : Measure Env) [IsProbabilityMeasure prior]
    (arms : Finset Action) (harms : arms.Nonempty)
    (hcard_two : 2 ≤ arms.card)
    (gamma : Real) (hgamma_pos : 0 < gamma)
    (hgamma_le_half : gamma ≤ 1 / 2)
    (loss : PredictableLossVector Env Action)
    (comparator : Action) (hcomparator : comparator ∈ arms)
    (horizon sparsity : Nat) (hhorizon : 0 < horizon)
    (hsparsity : 0 < sparsity)
    (delta : Real) (hdelta : 0 < delta) :
    let eta :=
      pathwiseVarianceProbabilisticSparseLossHighProbabilityLearningRate
        arms gamma horizon sparsity delta
    let mu := prior ⊗ₘ sampledImportanceWeightedTrajectoryKernel arms harms
      eta gamma hgamma_pos.le (by linarith : gamma ≤ 1) loss.environment
    mu ({sample |
        pathwiseVarianceProbabilisticSparseLossRealizedTunedThreshold
            arms gamma horizon sparsity delta ≤
          (Finset.range horizon).sum (fun t =>
              sampledTrajectoryRealizedLossAt t sample) -
            (Finset.range horizon).sum (fun t =>
              predictableLossAt loss t sample comparator)} \
      sampledPredictableSparsityFailure arms loss horizon sparsity) ≤
        ENNReal.ofReal delta := by
  dsimp only
  have heta :
      0 <
        pathwiseVarianceProbabilisticSparseLossHighProbabilityLearningRate
          arms gamma horizon sparsity delta :=
    pathwiseVarianceProbabilisticSparseLossHighProbabilityLearningRate_pos
      arms hcard_two gamma hgamma_pos horizon sparsity hhorizon hsparsity delta
  have hgamma_lt_one : gamma < 1 := by linarith
  have hbudget :=
    sampledPredictableVarianceSquareProbabilisticSparseLossRealizedPathwiseVarianceHighProbabilityRegretBudget_le_tunedThreshold
      arms hcard_two gamma hgamma_pos hgamma_le_half horizon sparsity
        hhorizon hsparsity delta
  have htail :=
    sampledPredictable_predictableVarianceSquareProbabilisticSparseLossRealizedPathwiseVarianceHighProbabilityRegret_tail_off_sparsityFailure
      prior arms harms
        (pathwiseVarianceProbabilisticSparseLossHighProbabilityLearningRate
          arms gamma horizon sparsity delta)
        gamma heta hgamma_pos hgamma_lt_one loss comparator hcomparator
        horizon sparsity hhorizon hsparsity delta hdelta
  dsimp only at htail ⊢
  calc
    (prior ⊗ₘ sampledImportanceWeightedTrajectoryKernel arms harms
        (pathwiseVarianceProbabilisticSparseLossHighProbabilityLearningRate
          arms gamma horizon sparsity delta)
        gamma hgamma_pos.le hgamma_lt_one.le loss.environment)
        ({sample |
          pathwiseVarianceProbabilisticSparseLossRealizedTunedThreshold
              arms gamma horizon sparsity delta ≤
            (Finset.range horizon).sum (fun t =>
                sampledTrajectoryRealizedLossAt t sample) -
              (Finset.range horizon).sum (fun t =>
                predictableLossAt loss t sample comparator)} \
          sampledPredictableSparsityFailure arms loss horizon sparsity) ≤
      (prior ⊗ₘ sampledImportanceWeightedTrajectoryKernel arms harms
        (pathwiseVarianceProbabilisticSparseLossHighProbabilityLearningRate
          arms gamma horizon sparsity delta)
        gamma hgamma_pos.le hgamma_lt_one.le loss.environment)
        ({sample |
          sampledPredictableVarianceSquareProbabilisticSparseLossRealizedPathwiseVarianceHighProbabilityRegretBudget
              arms
                (pathwiseVarianceProbabilisticSparseLossHighProbabilityLearningRate
                  arms gamma horizon sparsity delta)
              gamma horizon sparsity delta ≤
            (Finset.range horizon).sum (fun t =>
                sampledTrajectoryRealizedLossAt t sample) -
              (Finset.range horizon).sum (fun t =>
                predictableLossAt loss t sample comparator)} \
          sampledPredictableSparsityFailure arms loss horizon sparsity) := by
        apply measure_mono
        intro sample hsample
        exact ⟨hbudget.trans hsample.1, hsample.2⟩
    _ ≤ ENNReal.ofReal delta := htail

/-- Eta-tuned generated regret with the exact sparsity-failure residual and
the sparse pathwise variance budget. -/
theorem sampledPredictable_tunedProbabilisticSparseLossPathwiseVarianceRealizedRegret_tail
    {Env : Type u} {Action : Type v}
    [MeasurableSpace Env] [StandardBorelSpace Env] [Nonempty Env]
    [MeasurableSpace Action] [MeasurableSingletonClass Action]
    [StandardBorelSpace Action] [Nonempty Action] [DecidableEq Action]
    (prior : Measure Env) [IsProbabilityMeasure prior]
    (arms : Finset Action) (harms : arms.Nonempty)
    (hcard_two : 2 ≤ arms.card)
    (gamma : Real) (hgamma_pos : 0 < gamma)
    (hgamma_le_half : gamma ≤ 1 / 2)
    (loss : PredictableLossVector Env Action)
    (comparator : Action) (hcomparator : comparator ∈ arms)
    (horizon sparsity : Nat) (hhorizon : 0 < horizon)
    (hsparsity : 0 < sparsity)
    (delta : Real) (hdelta : 0 < delta) :
    let eta :=
      pathwiseVarianceProbabilisticSparseLossHighProbabilityLearningRate
        arms gamma horizon sparsity delta
    let mu := prior ⊗ₘ sampledImportanceWeightedTrajectoryKernel arms harms
      eta gamma hgamma_pos.le (by linarith : gamma ≤ 1) loss.environment
    mu {sample |
        pathwiseVarianceProbabilisticSparseLossRealizedTunedThreshold
            arms gamma horizon sparsity delta ≤
          (Finset.range horizon).sum (fun t =>
              sampledTrajectoryRealizedLossAt t sample) -
            (Finset.range horizon).sum (fun t =>
              predictableLossAt loss t sample comparator)} ≤
      ENNReal.ofReal delta +
        mu (sampledPredictableSparsityFailure arms loss horizon sparsity) := by
  dsimp only
  let mu := prior ⊗ₘ sampledImportanceWeightedTrajectoryKernel arms harms
    (pathwiseVarianceProbabilisticSparseLossHighProbabilityLearningRate
      arms gamma horizon sparsity delta)
    gamma hgamma_pos.le (by linarith : gamma ≤ 1) loss.environment
  let sparsityBad :=
    sampledPredictableSparsityFailure arms loss horizon sparsity
  let realizedBad : Set (Env × ((k : Nat) → Action × Real)) :=
    {sample |
      pathwiseVarianceProbabilisticSparseLossRealizedTunedThreshold
          arms gamma horizon sparsity delta ≤
        (Finset.range horizon).sum (fun t =>
            sampledTrajectoryRealizedLossAt t sample) -
          (Finset.range horizon).sum (fun t =>
            predictableLossAt loss t sample comparator)}
  have hoff :=
    sampledPredictable_tunedProbabilisticSparseLossPathwiseVarianceRealizedRegret_tail_off_sparsityFailure
      prior arms harms hcard_two gamma hgamma_pos hgamma_le_half loss comparator
        hcomparator horizon sparsity hhorizon hsparsity delta hdelta
  dsimp only at hoff
  have hsplit : realizedBad ⊆ (realizedBad \ sparsityBad) ∪ sparsityBad := by
    intro sample hsample
    by_cases hbad : sample ∈ sparsityBad
    · exact Or.inr hbad
    · exact Or.inl ⟨hsample, hbad⟩
  calc
    mu realizedBad ≤ mu ((realizedBad \ sparsityBad) ∪ sparsityBad) :=
      measure_mono hsplit
    _ ≤ mu (realizedBad \ sparsityBad) + mu sparsityBad :=
      measure_union_le _ _
    _ ≤ ENNReal.ofReal delta + mu sparsityBad :=
      add_le_add (by simpa [mu, realizedBad, sparsityBad] using hoff) le_rfl

/-- Practical eta-tuned `delta + epsilon` theorem under the exact internally
tuned generated measure. -/
theorem sampledPredictable_tunedProbabilisticSparseLossPathwiseVarianceRealizedRegret_tail_of_sparsityFailure_le
    {Env : Type u} {Action : Type v}
    [MeasurableSpace Env] [StandardBorelSpace Env] [Nonempty Env]
    [MeasurableSpace Action] [MeasurableSingletonClass Action]
    [StandardBorelSpace Action] [Nonempty Action] [DecidableEq Action]
    (prior : Measure Env) [IsProbabilityMeasure prior]
    (arms : Finset Action) (harms : arms.Nonempty)
    (hcard_two : 2 ≤ arms.card)
    (gamma : Real) (hgamma_pos : 0 < gamma)
    (hgamma_le_half : gamma ≤ 1 / 2)
    (loss : PredictableLossVector Env Action)
    (comparator : Action) (hcomparator : comparator ∈ arms)
    (horizon sparsity : Nat) (hhorizon : 0 < horizon)
    (hsparsity : 0 < sparsity)
    (delta epsilon : Real) (hdelta : 0 < delta) :
    let eta :=
      pathwiseVarianceProbabilisticSparseLossHighProbabilityLearningRate
        arms gamma horizon sparsity delta
    let mu := prior ⊗ₘ sampledImportanceWeightedTrajectoryKernel arms harms
      eta gamma hgamma_pos.le (by linarith : gamma ≤ 1) loss.environment
    mu (sampledPredictableSparsityFailure arms loss horizon sparsity) ≤
        ENNReal.ofReal epsilon →
      mu {sample |
          pathwiseVarianceProbabilisticSparseLossRealizedTunedThreshold
              arms gamma horizon sparsity delta ≤
            (Finset.range horizon).sum (fun t =>
                sampledTrajectoryRealizedLossAt t sample) -
              (Finset.range horizon).sum (fun t =>
                predictableLossAt loss t sample comparator)} ≤
        ENNReal.ofReal delta + ENNReal.ofReal epsilon := by
  dsimp only
  intro hfailure
  have htail :=
    sampledPredictable_tunedProbabilisticSparseLossPathwiseVarianceRealizedRegret_tail
      prior arms harms hcard_two gamma hgamma_pos hgamma_le_half loss comparator
        hcomparator horizon sparsity hhorizon hsparsity delta hdelta
  dsimp only at htail
  exact htail.trans (add_le_add le_rfl hfailure)

end BanditRLProof.Exp3
