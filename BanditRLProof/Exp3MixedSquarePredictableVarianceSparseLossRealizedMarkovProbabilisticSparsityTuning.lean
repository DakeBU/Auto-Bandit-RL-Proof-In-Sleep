import BanditRLProof.Exp3MixedSquarePredictableVarianceSparseLossRealizedMarkovProbabilisticSparsity

/-!
# Learning-rate tuning under probabilistic sparse losses

This module tunes `eta` for the generated realized predictable-variance EXP3
route whose support-sparsity contract may fail with positive probability.
The exact learning-rate scale is

`S * T + sampledMixedSquaredPredictableVarianceRadius arms gamma v (delta / 5)`,

where `v` is based on the unconditional `K * T` loss-mass envelope rather than
the sparse `S * T` envelope. The final theorem preserves the exact generated
sparsity-failure residual, and its practical consumer proves a
`delta + epsilon` tail.

Gamma remains caller-selected. This module does not transfer the pathwise
sparse `14 * gamma * T` threshold to the probabilistic-sparsity setting.
-/

namespace BanditRLProof.Exp3

open MeasureTheory ProbabilityTheory

universe u v

/-- Markov threshold for cumulative predictable mixed-square variance when
positive-probability sparsity failures require the global `K * T` envelope. -/
noncomputable def probabilisticSparseLossPredictableVarianceBudget
    {Action : Type v} [DecidableEq Action]
    (arms : Finset Action) (gamma : Real) (horizon : Nat)
    (delta : Real) : Real :=
  sampledPredictableGlobalVarianceMeanBudget arms gamma horizon / (delta / 5)

theorem probabilisticSparseLossPredictableVarianceBudget_pos
    {Action : Type v} [DecidableEq Action]
    (arms : Finset Action) (hcard_two : 2 ≤ arms.card)
    (gamma : Real) (hgamma_pos : 0 < gamma)
    (horizon : Nat) (hhorizon : 0 < horizon)
    (delta : Real) (hdelta : 0 < delta) :
    0 < probabilisticSparseLossPredictableVarianceBudget
      arms gamma horizon delta := by
  have hcard_pos : 0 < (arms.card : Real) := by positivity
  have hfloor_pos : 0 < gamma / (arms.card : Real) :=
    div_pos hgamma_pos hcard_pos
  have hglobal_pos :
      0 < sampledPredictableGlobalVarianceMeanBudget
        arms gamma horizon := by
    unfold sampledPredictableGlobalVarianceMeanBudget
    exact mul_pos (one_div_pos.2 hfloor_pos)
      (mul_pos hcard_pos (Nat.cast_pos.2 hhorizon))
  unfold probabilisticSparseLossPredictableVarianceBudget
  exact div_pos hglobal_pos (div_pos hdelta (by norm_num))

/-- Complete Hedge scale with sparse observed-square mean and global Markov
variance control. -/
noncomputable def probabilisticSparseLossPredictableVarianceHighProbabilityScale
    {Action : Type v} [DecidableEq Action]
    (arms : Finset Action) (gamma : Real)
    (horizon sparsity : Nat) (delta : Real) : Real :=
  (sparsity : Real) * (horizon : Real) +
    sampledMixedSquaredPredictableVarianceRadius arms gamma
      (probabilisticSparseLossPredictableVarianceBudget
        arms gamma horizon delta)
      (delta / 5)

theorem probabilisticSparseLossPredictableVarianceHighProbabilityScale_pos
    {Action : Type v} [DecidableEq Action]
    (arms : Finset Action) (hcard_two : 2 ≤ arms.card)
    (gamma : Real) (hgamma_pos : 0 < gamma)
    (horizon sparsity : Nat) (hhorizon : 0 < horizon)
    (hsparsity : 0 < sparsity) (delta : Real) :
    0 < probabilisticSparseLossPredictableVarianceHighProbabilityScale
      arms gamma horizon sparsity delta := by
  have hcard_pos : 0 < (arms.card : Real) := by positivity
  have hfloor_pos : 0 < gamma / (arms.card : Real) :=
    div_pos hgamma_pos hcard_pos
  have hbudget_nonneg : 0 ≤ max (Real.log (1 / (delta / 5))) 0 :=
    le_max_right _ _
  have hradius_nonneg :
      0 ≤ sampledMixedSquaredPredictableVarianceRadius arms gamma
        (probabilisticSparseLossPredictableVarianceBudget
          arms gamma horizon delta)
        (delta / 5) := by
    dsimp [sampledMixedSquaredPredictableVarianceRadius]
    exact add_nonneg
      (mul_nonneg (by norm_num) (Real.sqrt_nonneg _))
      (div_nonneg hbudget_nonneg hfloor_pos.le)
  have hloss_pos :
      0 < (sparsity : Real) * (horizon : Real) :=
    mul_pos (Nat.cast_pos.2 hsparsity) (Nat.cast_pos.2 hhorizon)
  dsimp [probabilisticSparseLossPredictableVarianceHighProbabilityScale]
  linarith

/-- Learning rate balancing entropy against the probabilistic-sparsity scale. -/
noncomputable def probabilisticSparseLossPredictableVarianceHighProbabilityLearningRate
    {Action : Type v} [DecidableEq Action]
    (arms : Finset Action) (gamma : Real)
    (horizon sparsity : Nat) (delta : Real) : Real :=
  Real.sqrt
    (Real.log (arms.card : Real) /
      probabilisticSparseLossPredictableVarianceHighProbabilityScale
        arms gamma horizon sparsity delta)

theorem probabilisticSparseLossPredictableVarianceHighProbabilityLearningRate_pos
    {Action : Type v} [DecidableEq Action]
    (arms : Finset Action) (hcard_two : 2 ≤ arms.card)
    (gamma : Real) (hgamma_pos : 0 < gamma)
    (horizon sparsity : Nat) (hhorizon : 0 < horizon)
    (hsparsity : 0 < sparsity) (delta : Real) :
    0 < probabilisticSparseLossPredictableVarianceHighProbabilityLearningRate
      arms gamma horizon sparsity delta := by
  have hK_one : 1 < (arms.card : Real) := by
    exact_mod_cast hcard_two
  have hscale :=
    probabilisticSparseLossPredictableVarianceHighProbabilityScale_pos
      arms hcard_two gamma hgamma_pos horizon sparsity hhorizon hsparsity delta
  apply Real.sqrt_pos.2
  exact div_pos (Real.log_pos hK_one) hscale

theorem probabilisticSparseLossPredictableVarianceHighProbabilityLearningRate_sq_mul_scale
    {Action : Type v} [DecidableEq Action]
    (arms : Finset Action) (hcard_two : 2 ≤ arms.card)
    (gamma : Real) (hgamma_pos : 0 < gamma)
    (horizon sparsity : Nat) (hhorizon : 0 < horizon)
    (hsparsity : 0 < sparsity) (delta : Real) :
    probabilisticSparseLossPredictableVarianceHighProbabilityLearningRate
          arms gamma horizon sparsity delta ^ 2 *
        probabilisticSparseLossPredictableVarianceHighProbabilityScale
          arms gamma horizon sparsity delta =
      Real.log (arms.card : Real) := by
  have hK_one : 1 < (arms.card : Real) := by
    exact_mod_cast hcard_two
  have hscale :=
    probabilisticSparseLossPredictableVarianceHighProbabilityScale_pos
      arms hcard_two gamma hgamma_pos horizon sparsity hhorizon hsparsity delta
  unfold probabilisticSparseLossPredictableVarianceHighProbabilityLearningRate
  rw [Real.sq_sqrt
    (div_nonneg (Real.log_pos hK_one).le hscale.le)]
  field_simp [ne_of_gt hscale]

/-- Under `gamma ≤ 1/2`, entropy and stability cost at most three copies of
the balanced probabilistic-sparsity scale. -/
theorem probabilisticSparseLossPredictableVarianceHighProbabilityHedgeBudget_le_three_mul_sqrt
    {Action : Type v} [DecidableEq Action]
    (arms : Finset Action) (hcard_two : 2 ≤ arms.card)
    (gamma : Real) (hgamma_pos : 0 < gamma)
    (hgamma_le_half : gamma ≤ 1 / 2)
    (horizon sparsity : Nat) (hhorizon : 0 < horizon)
    (hsparsity : 0 < sparsity) (delta : Real) :
    Real.log (arms.card : Real) /
          probabilisticSparseLossPredictableVarianceHighProbabilityLearningRate
            arms gamma horizon sparsity delta +
        (probabilisticSparseLossPredictableVarianceHighProbabilityLearningRate
            arms gamma horizon sparsity delta * (1 / (1 - gamma))) *
          probabilisticSparseLossPredictableVarianceHighProbabilityScale
            arms gamma horizon sparsity delta ≤
      3 * Real.sqrt
        (Real.log (arms.card : Real) *
          probabilisticSparseLossPredictableVarianceHighProbabilityScale
            arms gamma horizon sparsity delta) := by
  let eta :=
    probabilisticSparseLossPredictableVarianceHighProbabilityLearningRate
      arms gamma horizon sparsity delta
  let scale :=
    probabilisticSparseLossPredictableVarianceHighProbabilityScale
      arms gamma horizon sparsity delta
  let entropy := Real.log (arms.card : Real) / eta
  have hK_one : 1 < (arms.card : Real) := by
    exact_mod_cast hcard_two
  have heta : 0 < eta := by
    dsimp [eta]
    exact
      probabilisticSparseLossPredictableVarianceHighProbabilityLearningRate_pos
        arms hcard_two gamma hgamma_pos horizon sparsity hhorizon hsparsity delta
  have hscale : 0 < scale := by
    dsimp [scale]
    exact
      probabilisticSparseLossPredictableVarianceHighProbabilityScale_pos
        arms hcard_two gamma hgamma_pos horizon sparsity hhorizon hsparsity delta
  have hbalance : eta ^ 2 * scale = Real.log (arms.card : Real) := by
    dsimp [eta, scale]
    exact
      probabilisticSparseLossPredictableVarianceHighProbabilityLearningRate_sq_mul_scale
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

/-- Tuned regret threshold retaining the global Markov variance radius and the
three non-Hedge confidence terms. -/
noncomputable def probabilisticSparseLossPredictableVarianceRealizedMarkovTunedThreshold
    {Action : Type v} [DecidableEq Action]
    (arms : Finset Action) (gamma : Real)
    (horizon sparsity : Nat) (delta : Real) : Real :=
  3 * Real.sqrt
      (Real.log (arms.card : Real) *
        probabilisticSparseLossPredictableVarianceHighProbabilityScale
          arms gamma horizon sparsity delta) +
    gamma * (horizon : Real) +
    sampledPurePredictableMinusObservedBernsteinConfidenceRadius
      arms gamma horizon (delta / 5) +
    sampledComparatorEstimatorBernsteinConfidenceRadius
      arms gamma horizon (delta / 5) +
    sampledPredictableRealizedDeviationConfidenceRadius horizon (delta / 5)

/-- The raw probabilistic-sparsity budget is bounded by the eta-tuned
threshold. -/
theorem sampledPredictableVarianceSquareProbabilisticSparseLossRealizedMarkovHighProbabilityRegretBudget_le_tunedThreshold
    {Action : Type v} [DecidableEq Action]
    (arms : Finset Action) (hcard_two : 2 ≤ arms.card)
    (gamma : Real) (hgamma_pos : 0 < gamma)
    (hgamma_le_half : gamma ≤ 1 / 2)
    (horizon sparsity : Nat) (hhorizon : 0 < horizon)
    (hsparsity : 0 < sparsity) (delta : Real) :
    sampledPredictableVarianceSquareProbabilisticSparseLossRealizedMarkovHighProbabilityRegretBudget
        arms
        (probabilisticSparseLossPredictableVarianceHighProbabilityLearningRate
          arms gamma horizon sparsity delta)
        gamma horizon sparsity delta ≤
      probabilisticSparseLossPredictableVarianceRealizedMarkovTunedThreshold
        arms gamma horizon sparsity delta := by
  have hhedge :=
    probabilisticSparseLossPredictableVarianceHighProbabilityHedgeBudget_le_three_mul_sqrt
      arms hcard_two gamma hgamma_pos hgamma_le_half horizon sparsity
        hhorizon hsparsity delta
  dsimp [
    sampledPredictableVarianceSquareProbabilisticSparseLossRealizedMarkovHighProbabilityRegretBudget,
    sampledPredictableVarianceSquareSmallLossRealizedHighProbabilityRegretBudget,
    sampledPredictableVarianceSquareSmallLossHighProbabilityRegretBudget,
    probabilisticSparseLossPredictableVarianceRealizedMarkovTunedThreshold,
    probabilisticSparseLossPredictableVarianceHighProbabilityScale,
    probabilisticSparseLossPredictableVarianceBudget
  ] at hhedge ⊢
  linarith

/-- Eta-tuned generated regret with the exact sparsity-failure residual. -/
theorem sampledPredictable_tunedProbabilisticSparseLossPredictableVarianceRealizedMarkovRegret_tail
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
      probabilisticSparseLossPredictableVarianceHighProbabilityLearningRate
        arms gamma horizon sparsity delta
    let mu := prior ⊗ₘ sampledImportanceWeightedTrajectoryKernel arms harms
      eta gamma hgamma_pos.le (by linarith : gamma ≤ 1) loss.environment
    mu {sample |
        probabilisticSparseLossPredictableVarianceRealizedMarkovTunedThreshold
            arms gamma horizon sparsity delta ≤
          (Finset.range horizon).sum (fun t =>
              sampledTrajectoryRealizedLossAt t sample) -
            (Finset.range horizon).sum (fun t =>
              predictableLossAt loss t sample comparator)} ≤
      ENNReal.ofReal delta +
        mu (sampledPredictableSparsityFailure arms loss horizon sparsity) := by
  dsimp only
  have heta :
      0 <
        probabilisticSparseLossPredictableVarianceHighProbabilityLearningRate
          arms gamma horizon sparsity delta :=
    probabilisticSparseLossPredictableVarianceHighProbabilityLearningRate_pos
      arms hcard_two gamma hgamma_pos horizon sparsity hhorizon hsparsity delta
  have hgamma_lt_one : gamma < 1 := by linarith
  have hbudget :=
    sampledPredictableVarianceSquareProbabilisticSparseLossRealizedMarkovHighProbabilityRegretBudget_le_tunedThreshold
      arms hcard_two gamma hgamma_pos hgamma_le_half horizon sparsity
        hhorizon hsparsity delta
  have htail :=
    sampledPredictable_predictableVarianceSquareProbabilisticSparseLossRealizedMarkovHighProbabilityRegret_tail
      prior arms harms
        (probabilisticSparseLossPredictableVarianceHighProbabilityLearningRate
          arms gamma horizon sparsity delta)
        gamma heta hgamma_pos hgamma_lt_one loss comparator hcomparator
        horizon sparsity hhorizon delta hdelta
  dsimp only at htail ⊢
  calc
    (prior ⊗ₘ sampledImportanceWeightedTrajectoryKernel arms harms
        (probabilisticSparseLossPredictableVarianceHighProbabilityLearningRate
          arms gamma horizon sparsity delta)
        gamma hgamma_pos.le hgamma_lt_one.le loss.environment)
        {sample |
          probabilisticSparseLossPredictableVarianceRealizedMarkovTunedThreshold
              arms gamma horizon sparsity delta ≤
            (Finset.range horizon).sum (fun t =>
                sampledTrajectoryRealizedLossAt t sample) -
              (Finset.range horizon).sum (fun t =>
                predictableLossAt loss t sample comparator)} ≤
      (prior ⊗ₘ sampledImportanceWeightedTrajectoryKernel arms harms
        (probabilisticSparseLossPredictableVarianceHighProbabilityLearningRate
          arms gamma horizon sparsity delta)
        gamma hgamma_pos.le hgamma_lt_one.le loss.environment)
        {sample |
          sampledPredictableVarianceSquareProbabilisticSparseLossRealizedMarkovHighProbabilityRegretBudget
              arms
                (probabilisticSparseLossPredictableVarianceHighProbabilityLearningRate
                  arms gamma horizon sparsity delta)
              gamma horizon sparsity delta ≤
            (Finset.range horizon).sum (fun t =>
                sampledTrajectoryRealizedLossAt t sample) -
              (Finset.range horizon).sum (fun t =>
                predictableLossAt loss t sample comparator)} := by
        apply measure_mono
        intro sample hsample
        exact hbudget.trans hsample
    _ ≤ ENNReal.ofReal delta +
        (prior ⊗ₘ sampledImportanceWeightedTrajectoryKernel arms harms
          (probabilisticSparseLossPredictableVarianceHighProbabilityLearningRate
            arms gamma horizon sparsity delta)
          gamma hgamma_pos.le hgamma_lt_one.le loss.environment)
          (sampledPredictableSparsityFailure arms loss horizon sparsity) := htail

/-- Practical eta-tuned `delta + epsilon` theorem under an exact generated-
measure bound on the sparsity-failure event. -/
theorem sampledPredictable_tunedProbabilisticSparseLossPredictableVarianceRealizedMarkovRegret_tail_of_sparsityFailure_le
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
      probabilisticSparseLossPredictableVarianceHighProbabilityLearningRate
        arms gamma horizon sparsity delta
    let mu := prior ⊗ₘ sampledImportanceWeightedTrajectoryKernel arms harms
      eta gamma hgamma_pos.le (by linarith : gamma ≤ 1) loss.environment
    mu (sampledPredictableSparsityFailure arms loss horizon sparsity) ≤
        ENNReal.ofReal epsilon →
      mu {sample |
          probabilisticSparseLossPredictableVarianceRealizedMarkovTunedThreshold
              arms gamma horizon sparsity delta ≤
            (Finset.range horizon).sum (fun t =>
                sampledTrajectoryRealizedLossAt t sample) -
              (Finset.range horizon).sum (fun t =>
                predictableLossAt loss t sample comparator)} ≤
        ENNReal.ofReal delta + ENNReal.ofReal epsilon := by
  dsimp only
  intro hfailure
  have htail :=
    sampledPredictable_tunedProbabilisticSparseLossPredictableVarianceRealizedMarkovRegret_tail
      prior arms harms hcard_two gamma hgamma_pos hgamma_le_half loss comparator
        hcomparator horizon sparsity hhorizon hsparsity delta hdelta
  dsimp only at htail
  exact htail.trans (add_le_add le_rfl hfailure)

end BanditRLProof.Exp3
