import BanditRLProof.Exp3RandomSquareBernsteinRealizedTuning
import BanditRLProof.Exp3BernsteinExplicitTuning

/-!
# Explicit exploration tuning for the random-square realized EXP3 route

The random-square theorem already tunes the learning rate independently of
the exploration parameter.  This module chooses the remaining exploration
parameter from the two confidence scales at failure budget `delta / 4` and
obtains a fully explicit generated realized-regret threshold.
-/

namespace BanditRLProof.Exp3

open MeasureTheory ProbabilityTheory

universe u v

/-- Dividing a total failure probability by four changes the logarithmic
budget to `log (4 / delta)`. -/
theorem log_one_div_fourth_eq_log_four_div
    (delta : Real) (hdelta : 0 < delta) :
    Real.log (1 / (delta / 4)) = Real.log (4 / delta) := by
  congr 1
  field_simp [ne_of_gt hdelta]

/-- The threshold after controlling both exploration-floor Bernstein radii
and the realized-deviation radius by the exploration scale. -/
noncomputable def randomSquareBernsteinRealizedExplicitThreshold
    {Action : Type v} (arms : Finset Action) (gamma : Real)
    (horizon : Nat) (delta : Real) : Real :=
  3 * Real.sqrt
      (4 * (arms.card : Real) * (horizon : Real) *
        Real.log (arms.card : Real) / delta) +
    8 * gamma * (horizon : Real)

/-- Cubic and quadratic exploration contracts turn the three remaining
confidence radii in the learning-rate-tuned threshold into `7 * gamma * T`;
together with exploration bias this contributes `8 * gamma * T`. -/
theorem randomSquareBernsteinRealizedTunedThreshold_le_explicitThreshold
    {Action : Type v} [DecidableEq Action]
    (arms : Finset Action) (hcard_two : 2 <= arms.card)
    (horizon : Nat) (hhorizon : 0 < horizon)
    (gamma delta : Real) (hgamma_pos : 0 < gamma)
    (hgamma_le_half : gamma <= 1 / 2)
    (hdelta : 0 < delta) (hdelta_le_one : delta <= 1)
    (hcubic_confidence :
      (arms.card : Real) * Real.log (4 / delta) <=
        gamma ^ 3 * (horizon : Real))
    (hquadratic_realized :
      2 * ((Concentration.intervalVarianceProxy 0 1 : NNReal) : Real) *
          Real.log (4 / delta) <=
        gamma ^ 2 * (horizon : Real)) :
    randomSquareBernsteinRealizedTunedThreshold
        arms gamma horizon delta <=
      randomSquareBernsteinRealizedExplicitThreshold
        arms gamma horizon delta := by
  let K : Real := arms.card
  let T : Real := horizon
  let budget : Real := Real.log (4 / delta)
  let variance : Real :=
    ((Concentration.intervalVarianceProxy 0 1 : NNReal) : Real)
  have hK_one : 1 < K := by
    dsimp [K]
    exact_mod_cast hcard_two
  have hK : 0 < K := lt_trans zero_lt_one hK_one
  have hT : 0 < T := by
    dsimp [T]
    exact_mod_cast hhorizon
  have hone_lt_four_div : 1 < 4 / delta := by
    rw [lt_div_iff₀ hdelta]
    nlinarith
  have hbudget_pos : 0 < budget := Real.log_pos hone_lt_four_div
  have hlog_fourth : Real.log (1 / (delta / 4)) = budget := by
    dsimp [budget]
    exact log_one_div_fourth_eq_log_four_div delta hdelta
  have hmax_fourth : max (Real.log (1 / (delta / 4))) 0 = budget := by
    rw [hlog_fourth]
    exact max_eq_left hbudget_pos.le
  have hconfidence :
      2 * Real.sqrt (T * budget / (gamma / K)) +
          budget / (gamma / K) <=
        3 * gamma * T :=
    bernsteinConfidenceRadius_le_three_mul_gamma_mul_horizon
      K T budget gamma hK hT hbudget_pos.le hgamma_pos (by linarith)
        (by simpa [K, T, budget] using hcubic_confidence)
  have hvariance_pos : 0 < variance := by
    simpa [variance] using intervalVarianceProxy_zero_one_pos
  have hrealized :
      Real.sqrt (2 * (T * variance) * budget) <= gamma * T :=
    realizedDeviationRadius_le_mul_gamma_mul_horizon
      T budget variance gamma hT hbudget_pos.le hvariance_pos.le hgamma_pos
        (by simpa [T, budget, variance] using hquadratic_realized)
  dsimp [randomSquareBernsteinRealizedTunedThreshold,
    randomSquareBernsteinRealizedExplicitThreshold,
    sampledPurePredictableMinusObservedBernsteinConfidenceRadius,
    sampledComparatorEstimatorBernsteinConfidenceRadius,
    sampledPredictableRealizedDeviationConfidenceRadius]
  rw [hmax_fourth, hlog_fourth]
  change
    3 * Real.sqrt (4 * K * T * Real.log K / delta) +
        gamma * T +
        (2 * Real.sqrt (T * budget / (gamma / K)) +
          budget / (gamma / K)) +
        (2 * Real.sqrt (T * budget / (gamma / K)) +
          budget / (gamma / K)) +
        Real.sqrt (2 * (T * variance) * budget) <=
      3 * Real.sqrt (4 * K * T * Real.log K / delta) +
        8 * gamma * T
  linarith

/-- Generated realized-regret tail after characterizing the remaining
exploration parameter by one cubic and one quadratic dominance contract. -/
theorem sampledPredictable_gammaCharacterizedRandomSquareBernsteinRealizedRegret_tail
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
    (delta : Real) (hdelta : 0 < delta) (hdelta_le_one : delta <= 1)
    (hcubic_confidence :
      (arms.card : Real) * Real.log (4 / delta) <=
        gamma ^ 3 * (horizon : Real))
    (hquadratic_realized :
      2 * ((Concentration.intervalVarianceProxy 0 1 : NNReal) : Real) *
          Real.log (4 / delta) <=
        gamma ^ 2 * (horizon : Real)) :
    let eta := randomSquareHighProbabilityLearningRate
      (arms.card : Real) (horizon : Real) delta
    let mu := prior ⊗ₘ sampledImportanceWeightedTrajectoryKernel arms harms
      eta gamma hgamma_pos.le (by linarith : gamma <= 1) loss.environment
    mu {sample |
        randomSquareBernsteinRealizedExplicitThreshold
            arms gamma horizon delta <=
          (Finset.range horizon).sum (fun t =>
              sampledTrajectoryRealizedLossAt t sample) -
            (Finset.range horizon).sum (fun t =>
              predictableLossAt loss t sample comparator)} <=
      ENNReal.ofReal delta := by
  dsimp only
  have hthreshold :=
    randomSquareBernsteinRealizedTunedThreshold_le_explicitThreshold
      arms hcard_two horizon hhorizon gamma delta hgamma_pos hgamma_le_half
        hdelta hdelta_le_one hcubic_confidence hquadratic_realized
  have htail :=
    sampledPredictable_tunedRandomSquareBernsteinRealizedRegret_tail
      prior arms harms hcard_two gamma hgamma_pos hgamma_le_half loss comparator
        hcomparator horizon hhorizon delta hdelta
  dsimp only at htail ⊢
  calc
    (prior ⊗ₘ sampledImportanceWeightedTrajectoryKernel arms harms
        (randomSquareHighProbabilityLearningRate
          (arms.card : Real) (horizon : Real) delta)
        gamma hgamma_pos.le (by linarith : gamma <= 1) loss.environment)
        {sample |
          randomSquareBernsteinRealizedExplicitThreshold
              arms gamma horizon delta <=
            (Finset.range horizon).sum (fun t =>
                sampledTrajectoryRealizedLossAt t sample) -
              (Finset.range horizon).sum (fun t =>
                predictableLossAt loss t sample comparator)} <=
      (prior ⊗ₘ sampledImportanceWeightedTrajectoryKernel arms harms
        (randomSquareHighProbabilityLearningRate
          (arms.card : Real) (horizon : Real) delta)
        gamma hgamma_pos.le (by linarith : gamma <= 1) loss.environment)
        {sample |
          randomSquareBernsteinRealizedTunedThreshold
              arms gamma horizon delta <=
            (Finset.range horizon).sum (fun t =>
                sampledTrajectoryRealizedLossAt t sample) -
              (Finset.range horizon).sum (fun t =>
                predictableLossAt loss t sample comparator)} := by
        apply measure_mono
        intro sample hsample
        exact hthreshold.trans hsample
    _ <= ENNReal.ofReal delta := htail

/-- Cube-root scale required by both `delta / 4` importance-weighted
Bernstein radii. -/
noncomputable def randomSquareBernsteinConfidenceExplorationScale
    (K T delta : Real) : Real :=
  (K * Real.log (4 / delta) / T) ^ (3 : Real)⁻¹

/-- Square-root scale required by the `delta / 4` realized-deviation radius. -/
noncomputable def randomSquareBernsteinRealizedExplorationScale
    (T delta : Real) : Real :=
  Real.sqrt
    (2 * ((Concentration.intervalVarianceProxy 0 1 : NNReal) : Real) *
      Real.log (4 / delta) / T)

/-- Unclipped exploration scale covering both remaining confidence contracts. -/
noncomputable def randomSquareBernsteinRawExplorationRate
    (K T delta : Real) : Real :=
  max (randomSquareBernsteinConfidenceExplorationScale K T delta)
    (randomSquareBernsteinRealizedExplorationScale T delta)

/-- Explicit exploration schedule clipped into the Hedge stability regime. -/
noncomputable def randomSquareBernsteinClippedExplorationRate
    (K T delta : Real) : Real :=
  min (1 / 2) (randomSquareBernsteinRawExplorationRate K T delta)

theorem randomSquareBernsteinClippedExplorationRate_le_half
    (K T delta : Real) :
    randomSquareBernsteinClippedExplorationRate K T delta <= 1 / 2 := by
  exact min_le_left _ _

theorem randomSquareBernsteinClippedExplorationRate_eq_raw
    (K T delta : Real)
    (hraw : randomSquareBernsteinRawExplorationRate K T delta <= 1 / 2) :
    randomSquareBernsteinClippedExplorationRate K T delta =
      randomSquareBernsteinRawExplorationRate K T delta := by
  exact min_eq_right hraw

theorem randomSquareBernsteinRawExplorationRate_pos
    (K T delta : Real) (hK : 0 < K) (hT : 0 < T)
    (hdelta : 0 < delta) (hdelta_le_one : delta <= 1) :
    0 < randomSquareBernsteinRawExplorationRate K T delta := by
  have hone_lt_four_div : 1 < 4 / delta := by
    rw [lt_div_iff₀ hdelta]
    nlinarith
  have hbase : 0 < K * Real.log (4 / delta) / T :=
    div_pos (mul_pos hK (Real.log_pos hone_lt_four_div)) hT
  have hscale :
      0 < randomSquareBernsteinConfidenceExplorationScale K T delta := by
    exact Real.rpow_pos_of_pos hbase _
  exact hscale.trans_le (le_max_left _ _)

theorem randomSquareBernsteinClippedExplorationRate_pos
    (K T delta : Real) (hK : 0 < K) (hT : 0 < T)
    (hdelta : 0 < delta) (hdelta_le_one : delta <= 1) :
    0 < randomSquareBernsteinClippedExplorationRate K T delta := by
  apply lt_min
  · norm_num
  · exact randomSquareBernsteinRawExplorationRate_pos
      K T delta hK hT hdelta hdelta_le_one

/-- Transparent large-horizon conditions ensure clipping is inactive. -/
theorem randomSquareBernsteinRawExplorationRate_le_half_of_horizon_contracts
    (K T delta : Real) (hK : 0 < K) (hT : 0 < T)
    (hdelta : 0 < delta) (hdelta_le_one : delta <= 1)
    (hlarge_confidence : 8 * (K * Real.log (4 / delta)) <= T)
    (hlarge_realized :
      8 * ((Concentration.intervalVarianceProxy 0 1 : NNReal) : Real) *
          Real.log (4 / delta) <= T) :
    randomSquareBernsteinRawExplorationRate K T delta <= 1 / 2 := by
  have hone_lt_four_div : 1 < 4 / delta := by
    rw [lt_div_iff₀ hdelta]
    nlinarith
  have hlog : 0 <= Real.log (4 / delta) :=
    (Real.log_pos hone_lt_four_div).le
  have hvariance :
      0 <= ((Concentration.intervalVarianceProxy 0 1 : NNReal) : Real) :=
    NNReal.coe_nonneg _
  rw [randomSquareBernsteinRawExplorationRate]
  apply max_le
  · exact rpow_inv_three_le_half_of_eight_mul_le
      (K * Real.log (4 / delta)) T (mul_nonneg hK.le hlog) hT
        hlarge_confidence
  · apply sqrt_div_le_half_of_four_mul_le
    · exact hT
    · convert hlarge_realized using 1
      all_goals ring

/-- The clipped schedule satisfies the exact cubic and quadratic contracts
consumed by the characterized random-square theorem. -/
theorem randomSquareBernsteinClippedExplorationRate_contracts
    (K T delta : Real) (hK : 0 < K) (hT : 0 < T)
    (hdelta : 0 < delta) (hdelta_le_one : delta <= 1)
    (hlarge_confidence : 8 * (K * Real.log (4 / delta)) <= T)
    (hlarge_realized :
      8 * ((Concentration.intervalVarianceProxy 0 1 : NNReal) : Real) *
          Real.log (4 / delta) <= T) :
    let gamma := randomSquareBernsteinClippedExplorationRate K T delta
    0 < gamma ∧ gamma <= 1 / 2 ∧
      K * Real.log (4 / delta) <= gamma ^ 3 * T ∧
      2 * ((Concentration.intervalVarianceProxy 0 1 : NNReal) : Real) *
          Real.log (4 / delta) <= gamma ^ 2 * T := by
  dsimp only
  let variance : Real :=
    ((Concentration.intervalVarianceProxy 0 1 : NNReal) : Real)
  have hone_lt_four_div : 1 < 4 / delta := by
    rw [lt_div_iff₀ hdelta]
    nlinarith
  have hlog : 0 <= Real.log (4 / delta) :=
    (Real.log_pos hone_lt_four_div).le
  have hvariance : 0 <= variance := NNReal.coe_nonneg _
  have hraw :=
    randomSquareBernsteinRawExplorationRate_le_half_of_horizon_contracts
      K T delta hK hT hdelta hdelta_le_one hlarge_confidence hlarge_realized
  have hclip : randomSquareBernsteinClippedExplorationRate K T delta =
      randomSquareBernsteinRawExplorationRate K T delta :=
    randomSquareBernsteinClippedExplorationRate_eq_raw K T delta hraw
  have hconfidence_component :
      randomSquareBernsteinConfidenceExplorationScale K T delta <=
        randomSquareBernsteinClippedExplorationRate K T delta := by
    rw [hclip, randomSquareBernsteinRawExplorationRate]
    exact le_max_left _ _
  have hrealized_component :
      randomSquareBernsteinRealizedExplorationScale T delta <=
        randomSquareBernsteinClippedExplorationRate K T delta := by
    rw [hclip, randomSquareBernsteinRawExplorationRate]
    exact le_max_right _ _
  refine ⟨randomSquareBernsteinClippedExplorationRate_pos
      K T delta hK hT hdelta hdelta_le_one,
    randomSquareBernsteinClippedExplorationRate_le_half K T delta, ?_, ?_⟩
  · exact numerator_le_cube_mul_of_rpow_inv_three_le
      (K * Real.log (4 / delta)) T
        (randomSquareBernsteinClippedExplorationRate K T delta)
        (mul_nonneg hK.le hlog) hT (by
          simpa [randomSquareBernsteinConfidenceExplorationScale] using
            hconfidence_component)
  · exact numerator_le_sq_mul_of_sqrt_div_le
      (2 * variance * Real.log (4 / delta)) T
        (randomSquareBernsteinClippedExplorationRate K T delta)
        (mul_nonneg (mul_nonneg (by norm_num) hvariance) hlog) hT (by
          simpa [randomSquareBernsteinRealizedExplorationScale, variance] using
            hrealized_component)

/-- Generated realized-regret tail for the explicit clipped maximum of the
confidence cube-root and realized square-root scales. -/
theorem sampledPredictable_explicitRandomSquareBernsteinRealizedRegret_tail
    {Env : Type u} {Action : Type v}
    [MeasurableSpace Env] [StandardBorelSpace Env] [Nonempty Env]
    [MeasurableSpace Action] [MeasurableSingletonClass Action]
    [StandardBorelSpace Action] [Nonempty Action] [DecidableEq Action]
    (prior : Measure Env) [IsProbabilityMeasure prior]
    (arms : Finset Action) (harms : arms.Nonempty)
    (hcard_two : 2 <= arms.card)
    (loss : PredictableLossVector Env Action)
    (comparator : Action) (hcomparator : comparator ∈ arms)
    (horizon : Nat) (hhorizon : 0 < horizon)
    (delta : Real) (hdelta : 0 < delta) (hdelta_le_one : delta <= 1)
    (hlarge_confidence :
      8 * ((arms.card : Real) * Real.log (4 / delta)) <=
        (horizon : Real))
    (hlarge_realized :
      8 * ((Concentration.intervalVarianceProxy 0 1 : NNReal) : Real) *
          Real.log (4 / delta) <=
        (horizon : Real)) :
    let gamma := randomSquareBernsteinClippedExplorationRate
      (arms.card : Real) (horizon : Real) delta
    let eta := randomSquareHighProbabilityLearningRate
      (arms.card : Real) (horizon : Real) delta
    let mu := prior ⊗ₘ sampledImportanceWeightedTrajectoryKernel arms harms
      eta gamma
        (randomSquareBernsteinClippedExplorationRate_pos
          (arms.card : Real) (horizon : Real) delta
          (by positivity) (by exact_mod_cast hhorizon) hdelta hdelta_le_one).le
        (by
          exact (randomSquareBernsteinClippedExplorationRate_le_half
            (arms.card : Real) (horizon : Real) delta).trans (by norm_num))
        loss.environment
    mu {sample |
        randomSquareBernsteinRealizedExplicitThreshold
            arms gamma horizon delta <=
          (Finset.range horizon).sum (fun t =>
              sampledTrajectoryRealizedLossAt t sample) -
            (Finset.range horizon).sum (fun t =>
              predictableLossAt loss t sample comparator)} <=
      ENNReal.ofReal delta := by
  dsimp only
  have hK : 0 < (arms.card : Real) := by positivity
  have hT : 0 < (horizon : Real) := by exact_mod_cast hhorizon
  have hcontracts :=
    randomSquareBernsteinClippedExplorationRate_contracts
      (arms.card : Real) (horizon : Real) delta hK hT hdelta hdelta_le_one
        hlarge_confidence hlarge_realized
  dsimp only at hcontracts
  rcases hcontracts with
    ⟨hgamma_pos, hgamma_le_half, hcubic_confidence, hquadratic_realized⟩
  exact
    sampledPredictable_gammaCharacterizedRandomSquareBernsteinRealizedRegret_tail
      prior arms harms hcard_two
        (randomSquareBernsteinClippedExplorationRate
          (arms.card : Real) (horizon : Real) delta)
        hgamma_pos hgamma_le_half loss comparator hcomparator horizon hhorizon
        delta hdelta hdelta_le_one hcubic_confidence hquadratic_realized

end BanditRLProof.Exp3
