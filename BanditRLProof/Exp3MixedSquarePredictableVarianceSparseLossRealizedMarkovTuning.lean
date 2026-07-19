import BanditRLProof.Exp3MixedSquarePredictableVarianceSparseLossRealizedMarkovHighProbabilityRegret

/-!
# Learning-rate tuning for sparse-loss predictable-variance EXP3 regret

This module chooses the learning rate for the compiled sparse-loss realized
Markov route. With `L = sparsity * horizon`, the exact Hedge stability scale is

`L + sampledMixedSquaredPredictableVarianceRadius arms gamma v (delta / 5)`,

where `v = ((1 / (gamma / K)) * L) / (delta / 5)` is the Markov variance
threshold used by the five-event theorem. The learning rate

`eta = sqrt (log K / scale)`

balances entropy against this full scale. Under `gamma <= 1 / 2`, the two
learning-rate-dependent terms cost at most
`3 * sqrt (log K * scale)`.

The theorem remains a pathwise armwise sparse-loss result. It does not tune
`gamma`, replace Markov overflow, or claim a best-arm first-order rate.
-/

namespace BanditRLProof.Exp3

open MeasureTheory ProbabilityTheory

universe u v

/-- Markov threshold for cumulative predictable mixed-square variance under
the sparse armwise loss-mass budget. -/
noncomputable def sparseLossPredictableVarianceBudget
    {Action : Type v} (arms : Finset Action) (gamma : Real)
    (horizon sparsity : Nat) (delta : Real) : Real :=
  ((1 / (gamma / (arms.card : Real))) *
      ((sparsity : Real) * (horizon : Real))) / (delta / 5)

theorem sparseLossPredictableVarianceBudget_pos
    {Action : Type v} (arms : Finset Action) (hcard_two : 2 ≤ arms.card)
    (gamma : Real) (hgamma_pos : 0 < gamma)
    (horizon sparsity : Nat) (hhorizon : 0 < horizon)
    (hsparsity : 0 < sparsity) (delta : Real) (hdelta : 0 < delta) :
    0 < sparseLossPredictableVarianceBudget
      arms gamma horizon sparsity delta := by
  have hcard_pos : 0 < (arms.card : Real) := by positivity
  have hfloor_pos : 0 < gamma / (arms.card : Real) :=
    div_pos hgamma_pos hcard_pos
  have hloss_pos :
      0 < (sparsity : Real) * (horizon : Real) :=
    mul_pos (Nat.cast_pos.2 hsparsity) (Nat.cast_pos.2 hhorizon)
  unfold sparseLossPredictableVarianceBudget
  exact div_pos (mul_pos (one_div_pos.2 hfloor_pos) hloss_pos)
    (div_pos hdelta (by norm_num))

/-- Complete sparse-loss Hedge scale at the public five-event allocation. -/
noncomputable def sparseLossPredictableVarianceHighProbabilityScale
    {Action : Type v} [DecidableEq Action]
    (arms : Finset Action) (gamma : Real)
    (horizon sparsity : Nat) (delta : Real) : Real :=
  (sparsity : Real) * (horizon : Real) +
    sampledMixedSquaredPredictableVarianceRadius arms gamma
      (sparseLossPredictableVarianceBudget
        arms gamma horizon sparsity delta)
      (delta / 5)

theorem sparseLossPredictableVarianceHighProbabilityScale_pos
    {Action : Type v} [DecidableEq Action]
    (arms : Finset Action) (hcard_two : 2 ≤ arms.card)
    (gamma : Real) (hgamma_pos : 0 < gamma)
    (horizon sparsity : Nat) (hhorizon : 0 < horizon)
    (hsparsity : 0 < sparsity) (delta : Real) (hdelta : 0 < delta) :
    0 < sparseLossPredictableVarianceHighProbabilityScale
      arms gamma horizon sparsity delta := by
  have hcard_pos : 0 < (arms.card : Real) := by positivity
  have hfloor_pos : 0 < gamma / (arms.card : Real) :=
    div_pos hgamma_pos hcard_pos
  have hvariance_pos :=
    sparseLossPredictableVarianceBudget_pos
      arms hcard_two gamma hgamma_pos horizon sparsity hhorizon hsparsity
        delta hdelta
  have hbudget_nonneg : 0 ≤ max (Real.log (1 / (delta / 5))) 0 :=
    le_max_right _ _
  have hradius_nonneg :
      0 ≤ sampledMixedSquaredPredictableVarianceRadius arms gamma
        (sparseLossPredictableVarianceBudget
          arms gamma horizon sparsity delta)
        (delta / 5) := by
    dsimp [sampledMixedSquaredPredictableVarianceRadius]
    exact add_nonneg
      (mul_nonneg (by norm_num) (Real.sqrt_nonneg _))
      (div_nonneg hbudget_nonneg hfloor_pos.le)
  have hloss_pos :
      0 < (sparsity : Real) * (horizon : Real) :=
    mul_pos (Nat.cast_pos.2 hsparsity) (Nat.cast_pos.2 hhorizon)
  dsimp [sparseLossPredictableVarianceHighProbabilityScale]
  linarith

/-- Learning rate balancing entropy against the complete sparse-loss
predictable-variance scale. -/
noncomputable def sparseLossPredictableVarianceHighProbabilityLearningRate
    {Action : Type v} [DecidableEq Action]
    (arms : Finset Action) (gamma : Real)
    (horizon sparsity : Nat) (delta : Real) : Real :=
  Real.sqrt
    (Real.log (arms.card : Real) /
      sparseLossPredictableVarianceHighProbabilityScale
        arms gamma horizon sparsity delta)

theorem sparseLossPredictableVarianceHighProbabilityLearningRate_pos
    {Action : Type v} [DecidableEq Action]
    (arms : Finset Action) (hcard_two : 2 ≤ arms.card)
    (gamma : Real) (hgamma_pos : 0 < gamma)
    (horizon sparsity : Nat) (hhorizon : 0 < horizon)
    (hsparsity : 0 < sparsity) (delta : Real) (hdelta : 0 < delta) :
    0 < sparseLossPredictableVarianceHighProbabilityLearningRate
      arms gamma horizon sparsity delta := by
  have hK_one : 1 < (arms.card : Real) := by
    exact_mod_cast hcard_two
  have hscale :=
    sparseLossPredictableVarianceHighProbabilityScale_pos
      arms hcard_two gamma hgamma_pos horizon sparsity hhorizon hsparsity
        delta hdelta
  apply Real.sqrt_pos.2
  exact div_pos (Real.log_pos hK_one) hscale

theorem sparseLossPredictableVarianceHighProbabilityLearningRate_sq_mul_scale
    {Action : Type v} [DecidableEq Action]
    (arms : Finset Action) (hcard_two : 2 ≤ arms.card)
    (gamma : Real) (hgamma_pos : 0 < gamma)
    (horizon sparsity : Nat) (hhorizon : 0 < horizon)
    (hsparsity : 0 < sparsity) (delta : Real) (hdelta : 0 < delta) :
    sparseLossPredictableVarianceHighProbabilityLearningRate
          arms gamma horizon sparsity delta ^ 2 *
        sparseLossPredictableVarianceHighProbabilityScale
          arms gamma horizon sparsity delta =
      Real.log (arms.card : Real) := by
  have hK_one : 1 < (arms.card : Real) := by
    exact_mod_cast hcard_two
  have hscale :=
    sparseLossPredictableVarianceHighProbabilityScale_pos
      arms hcard_two gamma hgamma_pos horizon sparsity hhorizon hsparsity
        delta hdelta
  unfold sparseLossPredictableVarianceHighProbabilityLearningRate
  rw [Real.sq_sqrt
    (div_nonneg (Real.log_pos hK_one).le hscale.le)]
  field_simp [ne_of_gt hscale]

/-- With `gamma <= 1/2`, entropy and sparse-loss stability cost at most three
copies of their balanced square-root scale. -/
theorem sparseLossPredictableVarianceHighProbabilityHedgeBudget_le_three_mul_sqrt
    {Action : Type v} [DecidableEq Action]
    (arms : Finset Action) (hcard_two : 2 ≤ arms.card)
    (gamma : Real) (hgamma_pos : 0 < gamma)
    (hgamma_le_half : gamma ≤ 1 / 2)
    (horizon sparsity : Nat) (hhorizon : 0 < horizon)
    (hsparsity : 0 < sparsity) (delta : Real) (hdelta : 0 < delta) :
    Real.log (arms.card : Real) /
          sparseLossPredictableVarianceHighProbabilityLearningRate
            arms gamma horizon sparsity delta +
        (sparseLossPredictableVarianceHighProbabilityLearningRate
            arms gamma horizon sparsity delta * (1 / (1 - gamma))) *
          sparseLossPredictableVarianceHighProbabilityScale
            arms gamma horizon sparsity delta ≤
      3 * Real.sqrt
        (Real.log (arms.card : Real) *
          sparseLossPredictableVarianceHighProbabilityScale
            arms gamma horizon sparsity delta) := by
  let eta := sparseLossPredictableVarianceHighProbabilityLearningRate
    arms gamma horizon sparsity delta
  let scale := sparseLossPredictableVarianceHighProbabilityScale
    arms gamma horizon sparsity delta
  let entropy := Real.log (arms.card : Real) / eta
  have hK_one : 1 < (arms.card : Real) := by
    exact_mod_cast hcard_two
  have heta : 0 < eta := by
    dsimp [eta]
    exact sparseLossPredictableVarianceHighProbabilityLearningRate_pos
      arms hcard_two gamma hgamma_pos horizon sparsity hhorizon hsparsity
        delta hdelta
  have hscale : 0 < scale := by
    dsimp [scale]
    exact sparseLossPredictableVarianceHighProbabilityScale_pos
      arms hcard_two gamma hgamma_pos horizon sparsity hhorizon hsparsity
        delta hdelta
  have hbalance : eta ^ 2 * scale = Real.log (arms.card : Real) := by
    dsimp [eta, scale]
    exact
      sparseLossPredictableVarianceHighProbabilityLearningRate_sq_mul_scale
        arms hcard_two gamma hgamma_pos horizon sparsity hhorizon hsparsity
          delta hdelta
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

/-- Explicit sparse-loss threshold after tuning every learning-rate-dependent
term. Gamma and the three non-square confidence contributions remain visible. -/
noncomputable def sparseLossPredictableVarianceRealizedMarkovTunedThreshold
    {Action : Type v} [DecidableEq Action]
    (arms : Finset Action) (gamma : Real)
    (horizon sparsity : Nat) (delta : Real) : Real :=
  3 * Real.sqrt
      (Real.log (arms.card : Real) *
        sparseLossPredictableVarianceHighProbabilityScale
          arms gamma horizon sparsity delta) +
    gamma * (horizon : Real) +
    sampledPurePredictableMinusObservedBernsteinConfidenceRadius
      arms gamma horizon (delta / 5) +
    sampledComparatorEstimatorBernsteinConfidenceRadius
      arms gamma horizon (delta / 5) +
    sampledPredictableRealizedDeviationConfidenceRadius horizon (delta / 5)

/-- The complete sparse-loss Markov budget is bounded by the eta-tuned
threshold. -/
theorem sampledPredictableVarianceSquareSparseLossRealizedMarkovHighProbabilityRegretBudget_le_tunedThreshold
    {Action : Type v} [DecidableEq Action]
    (arms : Finset Action) (hcard_two : 2 ≤ arms.card)
    (gamma : Real) (hgamma_pos : 0 < gamma)
    (hgamma_le_half : gamma ≤ 1 / 2)
    (horizon sparsity : Nat) (hhorizon : 0 < horizon)
    (hsparsity : 0 < sparsity) (delta : Real) (hdelta : 0 < delta) :
    sampledPredictableVarianceSquareSparseLossRealizedMarkovHighProbabilityRegretBudget
        arms
        (sparseLossPredictableVarianceHighProbabilityLearningRate
          arms gamma horizon sparsity delta)
        gamma horizon sparsity delta ≤
      sparseLossPredictableVarianceRealizedMarkovTunedThreshold
        arms gamma horizon sparsity delta := by
  have hhedge :=
    sparseLossPredictableVarianceHighProbabilityHedgeBudget_le_three_mul_sqrt
      arms hcard_two gamma hgamma_pos hgamma_le_half horizon sparsity
        hhorizon hsparsity delta hdelta
  dsimp [
    sampledPredictableVarianceSquareSparseLossRealizedMarkovHighProbabilityRegretBudget,
    sampledPredictableVarianceSquareSmallLossRealizedMarkovHighProbabilityRegretBudget,
    sampledPredictableVarianceSquareSmallLossRealizedHighProbabilityRegretBudget,
    sampledPredictableVarianceSquareSmallLossHighProbabilityRegretBudget,
    sparseLossPredictableVarianceRealizedMarkovTunedThreshold,
    sparseLossPredictableVarianceHighProbabilityScale,
    sparseLossPredictableVarianceBudget] at hhedge ⊢
  linarith

/-- Generated sparse-loss realized-regret tail with the exact
predictable-variance-balanced learning rate. -/
theorem sampledPredictable_tunedSparseLossPredictableVarianceRealizedMarkovRegret_tail
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
    (delta : Real) (hdelta : 0 < delta)
    (hsparse : ∀ sample t, t < horizon →
      (sampledPredictableLossSupport arms loss t sample).card ≤ sparsity) :
    let eta := sparseLossPredictableVarianceHighProbabilityLearningRate
      arms gamma horizon sparsity delta
    let mu := prior ⊗ₘ sampledImportanceWeightedTrajectoryKernel arms harms
      eta gamma hgamma_pos.le (by linarith : gamma ≤ 1) loss.environment
    mu {sample |
        sparseLossPredictableVarianceRealizedMarkovTunedThreshold
            arms gamma horizon sparsity delta ≤
          (Finset.range horizon).sum (fun t =>
              sampledTrajectoryRealizedLossAt t sample) -
            (Finset.range horizon).sum (fun t =>
              predictableLossAt loss t sample comparator)} ≤
      ENNReal.ofReal delta := by
  dsimp only
  have heta :
      0 < sparseLossPredictableVarianceHighProbabilityLearningRate
        arms gamma horizon sparsity delta :=
    sparseLossPredictableVarianceHighProbabilityLearningRate_pos
      arms hcard_two gamma hgamma_pos horizon sparsity hhorizon hsparsity
        delta hdelta
  have hgamma_lt_one : gamma < 1 := by linarith
  have hbudget :=
    sampledPredictableVarianceSquareSparseLossRealizedMarkovHighProbabilityRegretBudget_le_tunedThreshold
      arms hcard_two gamma hgamma_pos hgamma_le_half horizon sparsity
        hhorizon hsparsity delta hdelta
  have htail :=
    sampledPredictable_predictableVarianceSquareSparseLossRealizedMarkovHighProbabilityRegret_tail_total_delta
      prior arms harms
        (sparseLossPredictableVarianceHighProbabilityLearningRate
          arms gamma horizon sparsity delta)
        gamma heta hgamma_pos hgamma_lt_one loss comparator hcomparator
        horizon sparsity hhorizon hsparsity delta hdelta hsparse
  dsimp only at htail ⊢
  calc
    (prior ⊗ₘ sampledImportanceWeightedTrajectoryKernel arms harms
        (sparseLossPredictableVarianceHighProbabilityLearningRate
          arms gamma horizon sparsity delta)
        gamma hgamma_pos.le hgamma_lt_one.le loss.environment)
        {sample |
          sparseLossPredictableVarianceRealizedMarkovTunedThreshold
              arms gamma horizon sparsity delta ≤
            (Finset.range horizon).sum (fun t =>
                sampledTrajectoryRealizedLossAt t sample) -
              (Finset.range horizon).sum (fun t =>
                predictableLossAt loss t sample comparator)} ≤
      (prior ⊗ₘ sampledImportanceWeightedTrajectoryKernel arms harms
        (sparseLossPredictableVarianceHighProbabilityLearningRate
          arms gamma horizon sparsity delta)
        gamma hgamma_pos.le hgamma_lt_one.le loss.environment)
        {sample |
          sampledPredictableVarianceSquareSparseLossRealizedMarkovHighProbabilityRegretBudget
              arms
                (sparseLossPredictableVarianceHighProbabilityLearningRate
                  arms gamma horizon sparsity delta)
              gamma horizon sparsity delta ≤
            (Finset.range horizon).sum (fun t =>
                sampledTrajectoryRealizedLossAt t sample) -
              (Finset.range horizon).sum (fun t =>
                predictableLossAt loss t sample comparator)} := by
        apply measure_mono
        intro sample hsample
        exact hbudget.trans hsample
    _ ≤ ENNReal.ofReal delta := htail

end BanditRLProof.Exp3
