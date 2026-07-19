import BanditRLProof.Exp3RandomSquareBernsteinRealizedHighProbabilityRegret
import BanditRLProof.Exp3BernsteinTuning

/-!
# Learning-rate tuning for random-square realized EXP3 regret

The random estimator-square route replaces the pathwise `K * T / gamma`
budget by `K * T / deltaSquare`. At the public four-event allocation,
`deltaSquare = delta / 4`. This module chooses

`eta = sqrt (log K * (delta / 4) / (T * K))`

and balances the entropy and Markov-square terms. The remaining exploration,
importance-weighted Bernstein, and realized-deviation terms are kept explicit;
they are not relabeled as an ideal EXP3.P or Freedman rate.
-/

namespace BanditRLProof.Exp3

open MeasureTheory ProbabilityTheory

universe u v

/-- Learning rate balancing entropy against the Markov estimator-square term
when the square event receives `delta / 4`. -/
noncomputable def randomSquareHighProbabilityLearningRate
    (K T delta : Real) : Real :=
  bernsteinHighProbabilityLearningRate K T (delta / 4)

theorem randomSquareHighProbabilityLearningRate_pos
    (K T delta : Real) (hK_one : 1 < K) (hT : 0 < T)
    (hdelta : 0 < delta) :
    0 < randomSquareHighProbabilityLearningRate K T delta := by
  exact bernsteinHighProbabilityLearningRate_pos K T (delta / 4)
    hK_one hT (div_pos hdelta (by norm_num))

theorem randomSquareHighProbabilityLearningRate_sq_mul
    (K T delta : Real) (hK_one : 1 < K) (hT : 0 < T)
    (hdelta : 0 < delta) :
    randomSquareHighProbabilityLearningRate K T delta ^ 2 * (T * K) =
      Real.log K * (delta / 4) := by
  exact bernsteinHighProbabilityLearningRate_sq_mul K T (delta / 4)
    hK_one hT (div_pos hdelta (by norm_num))

/-- With `gamma <= 1/2`, the entropy and stability-amplified random-square
terms cost at most three copies of their balanced square-root scale. -/
theorem randomSquareHighProbabilityHedgeBudget_le_three_mul_sqrt
    (K T gamma delta : Real)
    (hK_one : 1 < K) (hT : 0 < T)
    (hgamma_pos : 0 < gamma) (hgamma_le_half : gamma <= 1 / 2)
    (hdelta : 0 < delta) :
    Real.log K / randomSquareHighProbabilityLearningRate K T delta +
        (randomSquareHighProbabilityLearningRate K T delta *
          (1 / (1 - gamma))) * (K * T / (delta / 4)) <=
      3 * Real.sqrt (4 * K * T * Real.log K / delta) := by
  let eta := randomSquareHighProbabilityLearningRate K T delta
  let q := delta / 4
  let entropy := Real.log K / eta
  have hK : 0 < K := lt_trans zero_lt_one hK_one
  have heta : 0 < eta := by
    dsimp [eta]
    exact randomSquareHighProbabilityLearningRate_pos K T delta
      hK_one hT hdelta
  have hq : 0 < q := by
    dsimp [q]
    exact div_pos hdelta (by norm_num)
  have hbalance : eta ^ 2 * (T * K) = Real.log K * q := by
    dsimp [eta, q]
    exact randomSquareHighProbabilityLearningRate_sq_mul K T delta
      hK_one hT hdelta
  have hentropy_nonneg : 0 <= entropy := by
    exact div_nonneg (Real.log_pos hK_one).le heta.le
  have hentropy_eq_unscaled : entropy = eta * (K * T / q) := by
    dsimp [entropy]
    field_simp [ne_of_gt heta, ne_of_gt hq]
    nlinarith [hbalance]
  have hden : 0 < 1 - gamma := by linarith
  have hfactor : 1 <= 2 * (1 - gamma) := by linarith
  have hstable :
      (eta * (1 / (1 - gamma))) * (K * T / q) <= 2 * entropy := by
    rw [show
      (eta * (1 / (1 - gamma))) * (K * T / q) =
        (eta * (K * T / q)) / (1 - gamma) by ring]
    rw [← hentropy_eq_unscaled, div_le_iff₀ hden]
    have hmul := mul_le_mul_of_nonneg_left hfactor hentropy_nonneg
    nlinarith
  have hbalanced_sq :
      entropy ^ 2 = 4 * K * T * Real.log K / delta := by
    dsimp [entropy, q] at hbalance ⊢
    field_simp [ne_of_gt heta, ne_of_gt hdelta]
    linear_combination -4 * Real.log K * hbalance
  have hradicand_nonneg :
      0 <= 4 * K * T * Real.log K / delta := by
    exact div_nonneg
      (mul_nonneg
        (mul_nonneg (mul_nonneg (by norm_num) hK.le) hT.le)
        (Real.log_pos hK_one).le)
      hdelta.le
  have hentropy_eq_sqrt :
      entropy = Real.sqrt (4 * K * T * Real.log K / delta) := by
    have hsqrt_nonneg :=
      Real.sqrt_nonneg (4 * K * T * Real.log K / delta)
    have hsqrt_sq := Real.sq_sqrt hradicand_nonneg
    nlinarith [hbalanced_sq]
  change entropy +
      (eta * (1 / (1 - gamma))) * (K * T / q) <=
    3 * Real.sqrt (4 * K * T * Real.log K / delta)
  rw [← hentropy_eq_sqrt]
  linarith

/-- Explicit threshold after tuning only the learning-rate-dependent terms.
The exploration and three confidence contributions remain visible. -/
noncomputable def randomSquareBernsteinRealizedTunedThreshold
    {Action : Type v} (arms : Finset Action) (gamma : Real)
    (horizon : Nat) (delta : Real) : Real :=
  3 * Real.sqrt
      (4 * (arms.card : Real) * (horizon : Real) *
        Real.log (arms.card : Real) / delta) +
    gamma * (horizon : Real) +
    sampledPurePredictableMinusObservedBernsteinConfidenceRadius
      arms gamma horizon (delta / 4) +
    sampledComparatorEstimatorBernsteinConfidenceRadius
      arms gamma horizon (delta / 4) +
    sampledPredictableRealizedDeviationConfidenceRadius horizon (delta / 4)

/-- The complete four-event realized budget is bounded by the explicit
learning-rate-tuned threshold. -/
theorem sampledPredictableRandomSquareBernsteinRealizedHighProbabilityRegretBudget_le_tunedThreshold
    {Action : Type v} [DecidableEq Action]
    (arms : Finset Action) (hcard_two : 2 <= arms.card)
    (horizon : Nat) (hhorizon : 0 < horizon)
    (gamma delta : Real) (hgamma_pos : 0 < gamma)
    (hgamma_le_half : gamma <= 1 / 2) (hdelta : 0 < delta) :
    sampledPredictableRandomSquareBernsteinRealizedHighProbabilityRegretBudget
        arms
        (randomSquareHighProbabilityLearningRate
          (arms.card : Real) (horizon : Real) delta)
        gamma horizon (delta / 4) (delta / 4) (delta / 4) <=
      randomSquareBernsteinRealizedTunedThreshold
        arms gamma horizon delta := by
  have hK_one : 1 < (arms.card : Real) := by
    exact_mod_cast hcard_two
  have hT : 0 < (horizon : Real) := by
    exact_mod_cast hhorizon
  have hhedge :=
    randomSquareHighProbabilityHedgeBudget_le_three_mul_sqrt
      (arms.card : Real) (horizon : Real) gamma delta hK_one hT
        hgamma_pos hgamma_le_half hdelta
  dsimp [
    sampledPredictableRandomSquareBernsteinRealizedHighProbabilityRegretBudget,
    sampledPredictableRandomSquareBernsteinHighProbabilityRegretBudget,
    randomSquareBernsteinRealizedTunedThreshold]
  linarith

/-- Generated realized-regret tail with the random-square learning rate. This
optimizes the entropy/Markov-square pair while leaving the exploration-floor
and realized-deviation confidence terms explicit. -/
theorem sampledPredictable_tunedRandomSquareBernsteinRealizedRegret_tail
    {Env : Type u} {Action : Type v}
    [MeasurableSpace Env] [StandardBorelSpace Env] [Nonempty Env]
    [MeasurableSpace Action] [MeasurableSingletonClass Action]
    [StandardBorelSpace Action] [Nonempty Action] [DecidableEq Action]
    (prior : Measure Env) [IsProbabilityMeasure prior]
    (arms : Finset Action) (harms : arms.Nonempty)
    (hcard_two : 2 <= arms.card)
    (gamma : Real) (hgamma_pos : 0 < gamma)
    (hgamma_le_half : gamma <= 1 / 2)
    (loss : PredictableLossVector Env Action)
    (comparator : Action) (hcomparator : comparator ∈ arms)
    (horizon : Nat) (hhorizon : 0 < horizon)
    (delta : Real) (hdelta : 0 < delta) :
    let eta := randomSquareHighProbabilityLearningRate
      (arms.card : Real) (horizon : Real) delta
    let mu := prior ⊗ₘ sampledImportanceWeightedTrajectoryKernel arms harms
      eta gamma hgamma_pos.le (by linarith : gamma <= 1) loss.environment
    mu {sample |
        randomSquareBernsteinRealizedTunedThreshold
            arms gamma horizon delta <=
          (Finset.range horizon).sum (fun t =>
              sampledTrajectoryRealizedLossAt t sample) -
            (Finset.range horizon).sum (fun t =>
              predictableLossAt loss t sample comparator)} <=
      ENNReal.ofReal delta := by
  dsimp only
  have hK_one : 1 < (arms.card : Real) := by
    exact_mod_cast hcard_two
  have hT : 0 < (horizon : Real) := by
    exact_mod_cast hhorizon
  have heta :
      0 < randomSquareHighProbabilityLearningRate
        (arms.card : Real) (horizon : Real) delta :=
    randomSquareHighProbabilityLearningRate_pos
      (arms.card : Real) (horizon : Real) delta hK_one hT hdelta
  have hgamma_lt_one : gamma < 1 := by linarith
  have hbudget :=
    sampledPredictableRandomSquareBernsteinRealizedHighProbabilityRegretBudget_le_tunedThreshold
      arms hcard_two horizon hhorizon gamma delta hgamma_pos
        hgamma_le_half hdelta
  have htail :=
    sampledPredictable_randomSquareBernsteinRealizedHighProbabilityRegret_tail_total_delta
      prior arms harms
        (randomSquareHighProbabilityLearningRate
          (arms.card : Real) (horizon : Real) delta)
        gamma heta hgamma_pos hgamma_lt_one loss comparator hcomparator
        horizon hhorizon delta hdelta
  dsimp only at htail ⊢
  calc
    (prior ⊗ₘ sampledImportanceWeightedTrajectoryKernel arms harms
        (randomSquareHighProbabilityLearningRate
          (arms.card : Real) (horizon : Real) delta)
        gamma hgamma_pos.le hgamma_lt_one.le loss.environment)
        {sample |
          randomSquareBernsteinRealizedTunedThreshold
              arms gamma horizon delta <=
            (Finset.range horizon).sum (fun t =>
                sampledTrajectoryRealizedLossAt t sample) -
              (Finset.range horizon).sum (fun t =>
                predictableLossAt loss t sample comparator)} <=
      (prior ⊗ₘ sampledImportanceWeightedTrajectoryKernel arms harms
        (randomSquareHighProbabilityLearningRate
          (arms.card : Real) (horizon : Real) delta)
        gamma hgamma_pos.le hgamma_lt_one.le loss.environment)
        {sample |
          sampledPredictableRandomSquareBernsteinRealizedHighProbabilityRegretBudget
              arms
                (randomSquareHighProbabilityLearningRate
                  (arms.card : Real) (horizon : Real) delta)
              gamma horizon (delta / 4) (delta / 4) (delta / 4) <=
            (Finset.range horizon).sum (fun t =>
                sampledTrajectoryRealizedLossAt t sample) -
              (Finset.range horizon).sum (fun t =>
                predictableLossAt loss t sample comparator)} := by
        apply measure_mono
        intro sample hsample
        exact hbudget.trans hsample
    _ <= ENNReal.ofReal delta := htail

end BanditRLProof.Exp3
