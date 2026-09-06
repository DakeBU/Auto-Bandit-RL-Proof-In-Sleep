import BanditRLProof.Exp3MixedSquareBernsteinRealizedHighProbabilityRegret

/-!
# Learning-rate tuning for Bernstein-square realized EXP3 regret

The variance-sensitive mixed-square route uses

`K * T + sampledMixedSquaredBernsteinConfidenceRadius`.

This module chooses the exact learning rate

`eta = sqrt (log K / (K * T + squareRadius))`

at the public four-event allocation. It balances entropy against the complete
Bernstein-square stability scale. Exploration, the two action-confidence
radii, and realized deviation remain explicit for a later gamma schedule.
-/

namespace BanditRLProof.Exp3

open MeasureTheory ProbabilityTheory

universe u v

/-- Positive scale appearing in the Bernstein-square Hedge term when the
square event receives `delta / 4`. -/
noncomputable def bernsteinSquareHighProbabilityScale
    {Action : Type v} (arms : Finset Action) (gamma : Real)
    (horizon : Nat) (delta : Real) : Real :=
  (arms.card : Real) * (horizon : Real) +
    sampledMixedSquaredBernsteinConfidenceRadius arms gamma horizon (delta / 4)

theorem bernsteinSquareHighProbabilityScale_pos
    {Action : Type v} (arms : Finset Action) (hcard_two : 2 <= arms.card)
    (gamma : Real) (hgamma_pos : 0 < gamma)
    (horizon : Nat) (hhorizon : 0 < horizon) (delta : Real) :
    0 < bernsteinSquareHighProbabilityScale arms gamma horizon delta := by
  have hK : 0 < (arms.card : Real) := by
    positivity
  have hT : 0 < (horizon : Real) := by
    exact_mod_cast hhorizon
  have hepsilon : 0 < gamma / (arms.card : Real) := div_pos hgamma_pos hK
  have hvariance :
      0 < sampledMixedSquaredBernsteinVarianceCoefficient arms gamma := by
    dsimp [sampledMixedSquaredBernsteinVarianceCoefficient]
    exact div_pos hK hepsilon
  have hbudget : 0 <= max (Real.log (1 / (delta / 4))) 0 := le_max_right _ _
  have hradius :
      0 <= sampledMixedSquaredBernsteinConfidenceRadius
        arms gamma horizon (delta / 4) := by
    dsimp [sampledMixedSquaredBernsteinConfidenceRadius]
    exact add_nonneg
      (mul_nonneg (by norm_num) (Real.sqrt_nonneg _))
      (div_nonneg hbudget hepsilon.le)
  have hbase : 0 < (arms.card : Real) * (horizon : Real) := mul_pos hK hT
  dsimp [bernsteinSquareHighProbabilityScale]
  linarith

/-- Learning rate balancing entropy against the complete Bernstein-square
stability scale at the public `delta / 4` square allocation. -/
noncomputable def bernsteinSquareHighProbabilityLearningRate
    {Action : Type v} (arms : Finset Action) (gamma : Real)
    (horizon : Nat) (delta : Real) : Real :=
  Real.sqrt
    (Real.log (arms.card : Real) /
      bernsteinSquareHighProbabilityScale arms gamma horizon delta)

theorem bernsteinSquareHighProbabilityLearningRate_pos
    {Action : Type v} (arms : Finset Action) (hcard_two : 2 <= arms.card)
    (gamma : Real) (hgamma_pos : 0 < gamma)
    (horizon : Nat) (hhorizon : 0 < horizon) (delta : Real) :
    0 < bernsteinSquareHighProbabilityLearningRate
      arms gamma horizon delta := by
  have hK_one : 1 < (arms.card : Real) := by
    exact_mod_cast hcard_two
  have hscale := bernsteinSquareHighProbabilityScale_pos
    arms hcard_two gamma hgamma_pos horizon hhorizon delta
  apply Real.sqrt_pos.2
  exact div_pos (Real.log_pos hK_one) hscale

theorem bernsteinSquareHighProbabilityLearningRate_sq_mul_scale
    {Action : Type v} (arms : Finset Action) (hcard_two : 2 <= arms.card)
    (gamma : Real) (hgamma_pos : 0 < gamma)
    (horizon : Nat) (hhorizon : 0 < horizon) (delta : Real) :
    bernsteinSquareHighProbabilityLearningRate arms gamma horizon delta ^ 2 *
        bernsteinSquareHighProbabilityScale arms gamma horizon delta =
      Real.log (arms.card : Real) := by
  have hK_one : 1 < (arms.card : Real) := by
    exact_mod_cast hcard_two
  have hscale := bernsteinSquareHighProbabilityScale_pos
    arms hcard_two gamma hgamma_pos horizon hhorizon delta
  unfold bernsteinSquareHighProbabilityLearningRate
  rw [Real.sq_sqrt
    (div_nonneg (Real.log_pos hK_one).le hscale.le)]
  field_simp [ne_of_gt hscale]

/-- With `gamma <= 1/2`, entropy and the stability-amplified Bernstein-square
scale cost at most three copies of their balanced square-root scale. -/
theorem bernsteinSquareHighProbabilityHedgeBudget_le_three_mul_sqrt
    {Action : Type v} (arms : Finset Action) (hcard_two : 2 <= arms.card)
    (gamma : Real) (hgamma_pos : 0 < gamma)
    (hgamma_le_half : gamma <= 1 / 2)
    (horizon : Nat) (hhorizon : 0 < horizon) (delta : Real) :
    Real.log (arms.card : Real) /
          bernsteinSquareHighProbabilityLearningRate
            arms gamma horizon delta +
        (bernsteinSquareHighProbabilityLearningRate
            arms gamma horizon delta * (1 / (1 - gamma))) *
          bernsteinSquareHighProbabilityScale arms gamma horizon delta <=
      3 * Real.sqrt
        (Real.log (arms.card : Real) *
          bernsteinSquareHighProbabilityScale arms gamma horizon delta) := by
  let eta := bernsteinSquareHighProbabilityLearningRate
    arms gamma horizon delta
  let scale := bernsteinSquareHighProbabilityScale
    arms gamma horizon delta
  let entropy := Real.log (arms.card : Real) / eta
  have hK_one : 1 < (arms.card : Real) := by
    exact_mod_cast hcard_two
  have heta : 0 < eta := by
    dsimp [eta]
    exact bernsteinSquareHighProbabilityLearningRate_pos
      arms hcard_two gamma hgamma_pos horizon hhorizon delta
  have hscale : 0 < scale := by
    dsimp [scale]
    exact bernsteinSquareHighProbabilityScale_pos
      arms hcard_two gamma hgamma_pos horizon hhorizon delta
  have hbalance : eta ^ 2 * scale = Real.log (arms.card : Real) := by
    dsimp [eta, scale]
    exact bernsteinSquareHighProbabilityLearningRate_sq_mul_scale
      arms hcard_two gamma hgamma_pos horizon hhorizon delta
  have hentropy_nonneg : 0 <= entropy := by
    exact div_nonneg (Real.log_pos hK_one).le heta.le
  have hentropy_eq_unscaled : entropy = eta * scale := by
    dsimp [entropy]
    field_simp [ne_of_gt heta]
    nlinarith [hbalance]
  have hden : 0 < 1 - gamma := by linarith
  have hfactor : 1 <= 2 * (1 - gamma) := by linarith
  have hstable :
      (eta * (1 / (1 - gamma))) * scale <= 2 * entropy := by
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
      0 <= Real.log (arms.card : Real) * scale :=
    mul_nonneg (Real.log_pos hK_one).le hscale.le
  have hentropy_eq_sqrt :
      entropy = Real.sqrt
        (Real.log (arms.card : Real) * scale) := by
    have hsqrt_nonneg := Real.sqrt_nonneg
      (Real.log (arms.card : Real) * scale)
    have hsqrt_sq := Real.sq_sqrt hradicand_nonneg
    nlinarith [hbalanced_sq]
  change entropy + (eta * (1 / (1 - gamma))) * scale <=
    3 * Real.sqrt (Real.log (arms.card : Real) * scale)
  rw [← hentropy_eq_sqrt]
  linarith

/-- Explicit threshold after tuning all learning-rate-dependent terms. The
exploration and three confidence contributions remain visible. -/
noncomputable def bernsteinSquareRealizedTunedThreshold
    {Action : Type v} (arms : Finset Action) (gamma : Real)
    (horizon : Nat) (delta : Real) : Real :=
  3 * Real.sqrt
      (Real.log (arms.card : Real) *
        bernsteinSquareHighProbabilityScale arms gamma horizon delta) +
    gamma * (horizon : Real) +
    sampledPurePredictableMinusObservedBernsteinConfidenceRadius
      arms gamma horizon (delta / 4) +
    sampledComparatorEstimatorBernsteinConfidenceRadius
      arms gamma horizon (delta / 4) +
    sampledPredictableRealizedDeviationConfidenceRadius horizon (delta / 4)

/-- The complete Bernstein-square four-event realized budget is bounded by the
learning-rate-tuned threshold. -/
theorem sampledPredictableBernsteinSquareRealizedHighProbabilityRegretBudget_le_tunedThreshold
    {Action : Type v} [DecidableEq Action]
    (arms : Finset Action) (hcard_two : 2 <= arms.card)
    (gamma : Real) (hgamma_pos : 0 < gamma)
    (hgamma_le_half : gamma <= 1 / 2)
    (horizon : Nat) (hhorizon : 0 < horizon) (delta : Real) :
    sampledPredictableBernsteinSquareRealizedHighProbabilityRegretBudget
        arms
        (bernsteinSquareHighProbabilityLearningRate
          arms gamma horizon delta)
        gamma horizon (delta / 4) (delta / 4) (delta / 4) <=
      bernsteinSquareRealizedTunedThreshold arms gamma horizon delta := by
  have hhedge :=
    bernsteinSquareHighProbabilityHedgeBudget_le_three_mul_sqrt
      arms hcard_two gamma hgamma_pos hgamma_le_half horizon hhorizon delta
  dsimp [bernsteinSquareHighProbabilityScale] at hhedge
  dsimp [
    sampledPredictableBernsteinSquareRealizedHighProbabilityRegretBudget,
    sampledPredictableBernsteinSquareHighProbabilityRegretBudget,
    bernsteinSquareRealizedTunedThreshold,
    bernsteinSquareHighProbabilityScale]
  linarith

/-- Generated realized-regret tail with the Bernstein-square-balanced learning
rate. Gamma scheduling and confidence-radius simplification remain for
downstream consumers. -/
theorem sampledPredictable_tunedBernsteinSquareRealizedRegret_tail
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
    let eta := bernsteinSquareHighProbabilityLearningRate
      arms gamma horizon delta
    let mu := prior ⊗ₘ sampledImportanceWeightedTrajectoryKernel arms harms
      eta gamma hgamma_pos.le (by linarith : gamma <= 1) loss.environment
    mu {sample |
        bernsteinSquareRealizedTunedThreshold arms gamma horizon delta <=
          (Finset.range horizon).sum (fun t =>
              sampledTrajectoryRealizedLossAt t sample) -
            (Finset.range horizon).sum (fun t =>
              predictableLossAt loss t sample comparator)} <=
      ENNReal.ofReal delta := by
  dsimp only
  have heta :
      0 < bernsteinSquareHighProbabilityLearningRate
        arms gamma horizon delta :=
    bernsteinSquareHighProbabilityLearningRate_pos
      arms hcard_two gamma hgamma_pos horizon hhorizon delta
  have hgamma_lt_one : gamma < 1 := by linarith
  have hbudget :=
    sampledPredictableBernsteinSquareRealizedHighProbabilityRegretBudget_le_tunedThreshold
      arms hcard_two gamma hgamma_pos hgamma_le_half horizon hhorizon delta
  have htail :=
    sampledPredictable_bernsteinSquareRealizedHighProbabilityRegret_tail_total_delta
      prior arms harms
        (bernsteinSquareHighProbabilityLearningRate arms gamma horizon delta)
        gamma heta hgamma_pos hgamma_lt_one loss comparator hcomparator
        horizon hhorizon delta hdelta
  dsimp only at htail ⊢
  calc
    (prior ⊗ₘ sampledImportanceWeightedTrajectoryKernel arms harms
        (bernsteinSquareHighProbabilityLearningRate arms gamma horizon delta)
        gamma hgamma_pos.le hgamma_lt_one.le loss.environment)
        {sample |
          bernsteinSquareRealizedTunedThreshold arms gamma horizon delta <=
            (Finset.range horizon).sum (fun t =>
                sampledTrajectoryRealizedLossAt t sample) -
              (Finset.range horizon).sum (fun t =>
                predictableLossAt loss t sample comparator)} <=
      (prior ⊗ₘ sampledImportanceWeightedTrajectoryKernel arms harms
        (bernsteinSquareHighProbabilityLearningRate arms gamma horizon delta)
        gamma hgamma_pos.le hgamma_lt_one.le loss.environment)
        {sample |
          sampledPredictableBernsteinSquareRealizedHighProbabilityRegretBudget
              arms
                (bernsteinSquareHighProbabilityLearningRate
                  arms gamma horizon delta)
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
