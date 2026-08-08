import BanditRLProof.Exp3MixedSquareBernsteinRealizedTuning
import BanditRLProof.Exp3MixedSquareExponentialRealizedExplicitTuning

/-!
# Explicit exploration tuning for Bernstein-square realized EXP3

The existing four-scale clipped exploration schedule is strong enough for the
variance-sensitive mixed-square radius. Its sixth-power contract controls the
new square-root term when `gamma <= 1/2`, while its arm and confidence
contracts jointly control the linear `log_+ / epsilon` term. Thus the complete
tuned threshold remains bounded by `14 * gamma * T`.

This is still deterministic fixed-tilt control, not random predictable
quadratic variation, a general Freedman theorem, or ideal EXP3.P.
-/

namespace BanditRLProof.Exp3

open MeasureTheory ProbabilityTheory

universe u v

/-- The deterministic mixed-square Bernstein variance coefficient is exactly
`K^2 / gamma`. -/
theorem sampledMixedSquaredBernsteinVarianceCoefficient_eq_card_sq_div_gamma
    {Action : Type v} (arms : Finset Action) (hcard_two : 2 <= arms.card)
    (gamma : Real) (hgamma_pos : 0 < gamma) :
    sampledMixedSquaredBernsteinVarianceCoefficient arms gamma =
      (arms.card : Real) ^ 2 / gamma := by
  have hK : 0 < (arms.card : Real) := by positivity
  dsimp [sampledMixedSquaredBernsteinVarianceCoefficient]
  field_simp [ne_of_gt hK, ne_of_gt hgamma_pos]

/-- Under the existing arm, sixth-power mixed, and confidence contracts, the
log-weighted Bernstein mixed-square radius is at most `3 * gamma^2 * T^2`.
The first two copies control the square-root term; the third controls the
linear `log_+ / epsilon` correction. -/
theorem log_mul_sampledMixedSquaredBernsteinConfidenceRadius_le_three_mul_sq_mul_horizon_sq
    {Action : Type v} (arms : Finset Action) (hcard_two : 2 <= arms.card)
    (gamma : Real) (hgamma_pos : 0 < gamma)
    (hgamma_le_half : gamma <= 1 / 2)
    (horizon : Nat) (hhorizon : 0 < horizon)
    (delta : Real) (hdelta : 0 < delta) (hdelta_le_one : delta <= 1)
    (hbase :
      (arms.card : Real) * Real.log (arms.card : Real) <=
        gamma ^ 2 * (horizon : Real))
    (hmixed :
      (arms.card : Real) ^ 2 * Real.log (arms.card : Real) ^ 2 *
            Real.log (4 / delta) / 2 <=
        gamma ^ 6 * (horizon : Real) ^ 3)
    (hconfidence :
      (arms.card : Real) * Real.log (4 / delta) <=
        gamma ^ 3 * (horizon : Real)) :
    Real.log (arms.card : Real) *
        sampledMixedSquaredBernsteinConfidenceRadius
          arms gamma horizon (delta / 4) <=
      3 * gamma ^ 2 * (horizon : Real) ^ 2 := by
  let K : Real := arms.card
  let T : Real := horizon
  let L : Real := Real.log (4 / delta)
  let variance := sampledMixedSquaredBernsteinVarianceCoefficient arms gamma
  have hK_one : 1 < K := by
    dsimp [K]
    exact_mod_cast hcard_two
  have hK : 0 < K := lt_trans zero_lt_one hK_one
  have hT : 0 < T := by
    dsimp [T]
    exact_mod_cast hhorizon
  have hlogK : 0 <= Real.log K := (Real.log_pos hK_one).le
  have hone_lt_four_div : 1 < 4 / delta := by
    rw [lt_div_iff₀ hdelta]
    nlinarith
  have hL : 0 < L := by
    dsimp [L]
    exact Real.log_pos hone_lt_four_div
  have hlog_fourth : Real.log (1 / (delta / 4)) = L := by
    dsimp [L]
    exact log_one_div_fourth_eq_log_four_div delta hdelta
  have hmax_fourth : max (Real.log (1 / (delta / 4))) 0 = L := by
    rw [hlog_fourth]
    exact max_eq_left hL.le
  have hvariance : variance = K ^ 2 / gamma := by
    dsimp [variance, K]
    exact sampledMixedSquaredBernsteinVarianceCoefficient_eq_card_sq_div_gamma
      arms hcard_two gamma hgamma_pos
  have hradicand : 0 <= T * variance * L := by
    rw [hvariance]
    positivity
  have hroot_nonneg :
      0 <= Real.log K * Real.sqrt (T * variance * L) :=
    mul_nonneg hlogK (Real.sqrt_nonneg _)
  have hroot_right_nonneg : 0 <= gamma ^ 2 * T ^ 2 := by positivity
  have hmixed' : K ^ 2 * Real.log K ^ 2 * L <=
      2 * gamma ^ 6 * T ^ 3 := by
    dsimp [K, T, L] at hmixed ⊢
    nlinarith [hmixed]
  have hgamma_fifth_nonneg : 0 <= gamma ^ 5 := by positivity
  have hpow : 2 * gamma ^ 6 <= gamma ^ 5 := by
    have htwo_gamma : 2 * gamma <= 1 := by linarith
    calc
      2 * gamma ^ 6 = (2 * gamma) * gamma ^ 5 := by ring
      _ <= 1 * gamma ^ 5 :=
        mul_le_mul_of_nonneg_right htwo_gamma hgamma_fifth_nonneg
      _ = gamma ^ 5 := one_mul _
  have hpowT : 2 * gamma ^ 6 * T ^ 3 <= gamma ^ 5 * T ^ 3 :=
    mul_le_mul_of_nonneg_right hpow (by positivity)
  have hmixed_fifth :
      K ^ 2 * Real.log K ^ 2 * L <= gamma ^ 5 * T ^ 3 :=
    hmixed'.trans hpowT
  have hroot :
      Real.log K * Real.sqrt (T * variance * L) <=
        gamma ^ 2 * T ^ 2 := by
    apply le_of_sq_le_sq
    · rw [mul_pow, Real.sq_sqrt hradicand, hvariance]
      dsimp [K, T, L] at hmixed ⊢
      field_simp [ne_of_gt hgamma_pos]
      nlinarith [hmixed_fifth]
    · exact hroot_right_nonneg
  have hgamma_sq_le_one : gamma ^ 2 <= 1 := by
    nlinarith [hgamma_pos, hgamma_le_half]
  have hlog_le_Klog : Real.log K <= K * Real.log K := by
    have hmul := mul_nonneg (sub_nonneg.mpr hK_one.le) hlogK
    nlinarith
  have hgamma_sq_T_le_T : gamma ^ 2 * T <= T := by
    have hmul := mul_nonneg (sub_nonneg.mpr hgamma_sq_le_one) hT.le
    nlinarith
  have hlog_le_T : Real.log K <= T := by
    have hbase' : K * Real.log K <= gamma ^ 2 * T := by
      simpa [K, T] using hbase
    linarith
  have hconfidence' : K * L <= gamma ^ 3 * T := by
    simpa [K, T, L] using hconfidence
  have hconfidence_nonneg : 0 <= gamma ^ 3 * T := by positivity
  have hprod_one := mul_le_mul_of_nonneg_right hconfidence' hlogK
  have hprod_two :=
    mul_le_mul_of_nonneg_left hlog_le_T hconfidence_nonneg
  have hprod : (K * L) * Real.log K <= gamma ^ 3 * T ^ 2 := by
    calc
      (K * L) * Real.log K <= (gamma ^ 3 * T) * Real.log K := hprod_one
      _ <= (gamma ^ 3 * T) * T := hprod_two
      _ = gamma ^ 3 * T ^ 2 := by ring
  have hlinear :
      Real.log K * (L / (gamma / K)) <= gamma ^ 2 * T ^ 2 := by
    calc
      Real.log K * (L / (gamma / K)) =
          ((K * L) * Real.log K) / gamma := by
        field_simp [ne_of_gt hK, ne_of_gt hgamma_pos]
      _ <= (gamma ^ 3 * T ^ 2) / gamma :=
        div_le_div_of_nonneg_right hprod hgamma_pos.le
      _ = gamma ^ 2 * T ^ 2 := by
        field_simp [ne_of_gt hgamma_pos]
  dsimp [sampledMixedSquaredBernsteinConfidenceRadius]
  rw [hmax_fourth]
  change
    Real.log K * (2 * Real.sqrt (T * variance * L) + L / (gamma / K)) <=
      3 * gamma ^ 2 * T ^ 2
  rw [mul_add]
  nlinarith [hroot, hlinear]

/-- The armwise base term and the variance-sensitive mixed-square radius make
the learning-rate-balanced square root at most `2 * gamma * T`. -/
theorem bernsteinSquareBalancedSqrt_le_two_mul_gamma_mul_horizon
    {Action : Type v} (arms : Finset Action) (hcard_two : 2 <= arms.card)
    (gamma : Real) (hgamma_pos : 0 < gamma)
    (hgamma_le_half : gamma <= 1 / 2)
    (horizon : Nat) (hhorizon : 0 < horizon)
    (delta : Real) (hdelta : 0 < delta) (hdelta_le_one : delta <= 1)
    (hbase :
      (arms.card : Real) * Real.log (arms.card : Real) <=
        gamma ^ 2 * (horizon : Real))
    (hmixed :
      (arms.card : Real) ^ 2 * Real.log (arms.card : Real) ^ 2 *
            Real.log (4 / delta) / 2 <=
        gamma ^ 6 * (horizon : Real) ^ 3)
    (hconfidence :
      (arms.card : Real) * Real.log (4 / delta) <=
        gamma ^ 3 * (horizon : Real)) :
    Real.sqrt
        (Real.log (arms.card : Real) *
          bernsteinSquareHighProbabilityScale arms gamma horizon delta) <=
      2 * gamma * (horizon : Real) := by
  let K : Real := arms.card
  let T : Real := horizon
  let radius := sampledMixedSquaredBernsteinConfidenceRadius
    arms gamma horizon (delta / 4)
  have hT : 0 < T := by
    dsimp [T]
    exact_mod_cast hhorizon
  have hK_one : 1 < K := by
    dsimp [K]
    exact_mod_cast hcard_two
  have hlogK : 0 <= Real.log K := (Real.log_pos hK_one).le
  have hradius_nonneg : 0 <= radius := by
    have hK : 0 < K := lt_trans zero_lt_one hK_one
    have hepsilon : 0 < gamma / K := div_pos hgamma_pos hK
    have hbudget : 0 <= max (Real.log (1 / (delta / 4))) 0 := le_max_right _ _
    dsimp [radius, sampledMixedSquaredBernsteinConfidenceRadius, K]
    exact add_nonneg
      (mul_nonneg (by norm_num) (Real.sqrt_nonneg _))
      (div_nonneg hbudget hepsilon.le)
  have hmixed_bound :
      Real.log K * radius <= 3 * gamma ^ 2 * T ^ 2 := by
    dsimp [K, T, radius]
    exact
      log_mul_sampledMixedSquaredBernsteinConfidenceRadius_le_three_mul_sq_mul_horizon_sq
        arms hcard_two gamma hgamma_pos hgamma_le_half horizon hhorizon delta
          hdelta hdelta_le_one hbase hmixed hconfidence
  have hbase_bound : Real.log K * (K * T) <= gamma ^ 2 * T ^ 2 := by
    have hbase' : K * Real.log K <= gamma ^ 2 * T := by
      simpa [K, T] using hbase
    nlinarith
  rw [Real.sqrt_le_iff]
  constructor
  · positivity
  · dsimp [bernsteinSquareHighProbabilityScale, K, T, radius] at *
    nlinarith

/-- Explicit threshold after controlling the balanced square root and all
three remaining confidence contributions by the exploration scale. -/
noncomputable def bernsteinSquareRealizedExplicitThreshold
    {Action : Type v} (_arms : Finset Action) (gamma : Real)
    (horizon : Nat) (_delta : Real) : Real :=
  14 * gamma * (horizon : Real)

/-- The existing quadratic, sixth-power, cubic, and realized quadratic
contracts reduce the variance-sensitive tuned threshold to `14 * gamma * T`.
The sixth-power contract is conservative for the new square-root term, while
the arm and confidence contracts jointly control the linear correction. -/
theorem bernsteinSquareRealizedTunedThreshold_le_explicitThreshold
    {Action : Type v} [DecidableEq Action]
    (arms : Finset Action) (hcard_two : 2 <= arms.card)
    (horizon : Nat) (hhorizon : 0 < horizon)
    (gamma delta : Real) (hgamma_pos : 0 < gamma)
    (hgamma_le_half : gamma <= 1 / 2)
    (hdelta : 0 < delta) (hdelta_le_one : delta <= 1)
    (hbase :
      (arms.card : Real) * Real.log (arms.card : Real) <=
        gamma ^ 2 * (horizon : Real))
    (hmixed :
      (arms.card : Real) ^ 2 * Real.log (arms.card : Real) ^ 2 *
            Real.log (4 / delta) / 2 <=
        gamma ^ 6 * (horizon : Real) ^ 3)
    (hconfidence :
      (arms.card : Real) * Real.log (4 / delta) <=
        gamma ^ 3 * (horizon : Real))
    (hrealized :
      2 * ((Concentration.intervalVarianceProxy 0 1 : NNReal) : Real) *
          Real.log (4 / delta) <=
        gamma ^ 2 * (horizon : Real)) :
    bernsteinSquareRealizedTunedThreshold arms gamma horizon delta <=
      bernsteinSquareRealizedExplicitThreshold arms gamma horizon delta := by
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
  have hbalanced :
      Real.sqrt
          (Real.log K *
            bernsteinSquareHighProbabilityScale arms gamma horizon delta) <=
        2 * gamma * T := by
    simpa [K, T] using
      bernsteinSquareBalancedSqrt_le_two_mul_gamma_mul_horizon
        arms hcard_two gamma hgamma_pos hgamma_le_half horizon hhorizon delta
          hdelta hdelta_le_one hbase hmixed hconfidence
  have hconfidence_radius :
      2 * Real.sqrt (T * budget / (gamma / K)) +
          budget / (gamma / K) <=
        3 * gamma * T :=
    bernsteinConfidenceRadius_le_three_mul_gamma_mul_horizon
      K T budget gamma hK hT hbudget_pos.le hgamma_pos (by linarith)
        (by simpa [K, T, budget] using hconfidence)
  have hvariance_pos : 0 < variance := by
    simpa [variance] using intervalVarianceProxy_zero_one_pos
  have hrealized_radius :
      Real.sqrt (2 * (T * variance) * budget) <= gamma * T :=
    realizedDeviationRadius_le_mul_gamma_mul_horizon
      T budget variance gamma hT hbudget_pos.le hvariance_pos.le hgamma_pos
        (by simpa [T, budget, variance] using hrealized)
  dsimp [bernsteinSquareRealizedTunedThreshold,
    bernsteinSquareRealizedExplicitThreshold,
    sampledPurePredictableMinusObservedBernsteinConfidenceRadius,
    sampledComparatorEstimatorBernsteinConfidenceRadius,
    sampledPredictableRealizedDeviationConfidenceRadius]
  rw [hmax_fourth, hlog_fourth]
  change
    3 * Real.sqrt
          (Real.log K *
            bernsteinSquareHighProbabilityScale arms gamma horizon delta) +
        gamma * T +
        (2 * Real.sqrt (T * budget / (gamma / K)) +
          budget / (gamma / K)) +
        (2 * Real.sqrt (T * budget / (gamma / K)) +
          budget / (gamma / K)) +
        Real.sqrt (2 * (T * variance) * budget) <=
      14 * gamma * T
  linarith

/-- Generated realized-regret tail under the four algebraic exploration
contracts. -/
theorem sampledPredictable_gammaCharacterizedBernsteinSquareRealizedRegret_tail
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
    (hbase :
      (arms.card : Real) * Real.log (arms.card : Real) <=
        gamma ^ 2 * (horizon : Real))
    (hmixed :
      (arms.card : Real) ^ 2 * Real.log (arms.card : Real) ^ 2 *
            Real.log (4 / delta) / 2 <=
        gamma ^ 6 * (horizon : Real) ^ 3)
    (hconfidence :
      (arms.card : Real) * Real.log (4 / delta) <=
        gamma ^ 3 * (horizon : Real))
    (hrealized :
      2 * ((Concentration.intervalVarianceProxy 0 1 : NNReal) : Real) *
          Real.log (4 / delta) <=
        gamma ^ 2 * (horizon : Real)) :
    let eta := bernsteinSquareHighProbabilityLearningRate
      arms gamma horizon delta
    let mu := prior ⊗ₘ sampledImportanceWeightedTrajectoryKernel arms harms
      eta gamma hgamma_pos.le (by linarith : gamma <= 1) loss.environment
    mu {sample |
        bernsteinSquareRealizedExplicitThreshold arms gamma horizon delta <=
          (Finset.range horizon).sum (fun t =>
              sampledTrajectoryRealizedLossAt t sample) -
            (Finset.range horizon).sum (fun t =>
              predictableLossAt loss t sample comparator)} <=
      ENNReal.ofReal delta := by
  dsimp only
  have hthreshold :=
    bernsteinSquareRealizedTunedThreshold_le_explicitThreshold
      arms hcard_two horizon hhorizon gamma delta hgamma_pos hgamma_le_half
        hdelta hdelta_le_one hbase hmixed hconfidence hrealized
  have htail :=
    sampledPredictable_tunedBernsteinSquareRealizedRegret_tail
      prior arms harms hcard_two gamma hgamma_pos hgamma_le_half loss comparator
        hcomparator horizon hhorizon delta hdelta
  dsimp only at htail ⊢
  calc
    (prior ⊗ₘ sampledImportanceWeightedTrajectoryKernel arms harms
        (bernsteinSquareHighProbabilityLearningRate arms gamma horizon delta)
        gamma hgamma_pos.le (by linarith : gamma <= 1) loss.environment)
        {sample |
          bernsteinSquareRealizedExplicitThreshold arms gamma horizon delta <=
            (Finset.range horizon).sum (fun t =>
                sampledTrajectoryRealizedLossAt t sample) -
              (Finset.range horizon).sum (fun t =>
                predictableLossAt loss t sample comparator)} <=
      (prior ⊗ₘ sampledImportanceWeightedTrajectoryKernel arms harms
        (bernsteinSquareHighProbabilityLearningRate arms gamma horizon delta)
        gamma hgamma_pos.le (by linarith : gamma <= 1) loss.environment)
        {sample |
          bernsteinSquareRealizedTunedThreshold arms gamma horizon delta <=
            (Finset.range horizon).sum (fun t =>
                sampledTrajectoryRealizedLossAt t sample) -
              (Finset.range horizon).sum (fun t =>
                predictableLossAt loss t sample comparator)} := by
        apply measure_mono
        intro sample hsample
        exact hthreshold.trans hsample
    _ <= ENNReal.ofReal delta := htail

/-- The variance-sensitive route reuses the already compiled four-scale
clipped schedule. -/
noncomputable def bernsteinSquareClippedExplorationRate
    (K T delta : Real) : Real :=
  exponentialSquareBernsteinClippedExplorationRate K T delta

theorem bernsteinSquareClippedExplorationRate_pos
    (K T delta : Real) (hK_one : 1 < K) (hT : 0 < T) :
    0 < bernsteinSquareClippedExplorationRate K T delta := by
  simpa [bernsteinSquareClippedExplorationRate] using
    exponentialSquareBernsteinClippedExplorationRate_pos
      K T delta hK_one hT

theorem bernsteinSquareClippedExplorationRate_le_half
    (K T delta : Real) :
    bernsteinSquareClippedExplorationRate K T delta <= 1 / 2 := by
  simpa [bernsteinSquareClippedExplorationRate] using
    exponentialSquareBernsteinClippedExplorationRate_le_half K T delta

/-- The reused clipped schedule satisfies all four contracts needed by the
variance-sensitive gamma-characterized theorem. -/
theorem bernsteinSquareClippedExplorationRate_contracts
    (K T delta : Real) (hK_one : 1 < K) (hT : 0 < T)
    (hdelta : 0 < delta) (hdelta_le_one : delta <= 1)
    (hlarge_arm : 4 * (K * Real.log K) <= T)
    (hlarge_mixed :
      64 * (K ^ 2 * Real.log K ^ 2 * Real.log (4 / delta) / 2) <=
        T ^ 3)
    (hlarge_confidence : 8 * (K * Real.log (4 / delta)) <= T)
    (hlarge_realized :
      8 * ((Concentration.intervalVarianceProxy 0 1 : NNReal) : Real) *
          Real.log (4 / delta) <= T) :
    let gamma := bernsteinSquareClippedExplorationRate K T delta
    0 < gamma ∧ gamma <= 1 / 2 ∧
      K * Real.log K <= gamma ^ 2 * T ∧
      K ^ 2 * Real.log K ^ 2 * Real.log (4 / delta) / 2 <=
        gamma ^ 6 * T ^ 3 ∧
      K * Real.log (4 / delta) <= gamma ^ 3 * T ∧
      2 * ((Concentration.intervalVarianceProxy 0 1 : NNReal) : Real) *
          Real.log (4 / delta) <= gamma ^ 2 * T := by
  simpa [bernsteinSquareClippedExplorationRate] using
    exponentialSquareBernsteinClippedExplorationRate_contracts
      K T delta hK_one hT hdelta hdelta_le_one hlarge_arm hlarge_mixed
        hlarge_confidence hlarge_realized

/-- Fully explicit generated realized-regret tail for the variance-sensitive
route, using the reused clipped maximum of four exploration scales. -/
theorem sampledPredictable_explicitBernsteinSquareRealizedRegret_tail
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
    (hlarge_arm :
      4 * ((arms.card : Real) * Real.log (arms.card : Real)) <=
        (horizon : Real))
    (hlarge_mixed :
      64 * ((arms.card : Real) ^ 2 * Real.log (arms.card : Real) ^ 2 *
          Real.log (4 / delta) / 2) <= (horizon : Real) ^ 3)
    (hlarge_confidence :
      8 * ((arms.card : Real) * Real.log (4 / delta)) <=
        (horizon : Real))
    (hlarge_realized :
      8 * ((Concentration.intervalVarianceProxy 0 1 : NNReal) : Real) *
          Real.log (4 / delta) <= (horizon : Real)) :
    let gamma := bernsteinSquareClippedExplorationRate
      (arms.card : Real) (horizon : Real) delta
    let eta := bernsteinSquareHighProbabilityLearningRate
      arms gamma horizon delta
    let mu := prior ⊗ₘ sampledImportanceWeightedTrajectoryKernel arms harms
      eta gamma
        (bernsteinSquareClippedExplorationRate_pos
          (arms.card : Real) (horizon : Real) delta
          (by exact_mod_cast hcard_two)
          (by exact_mod_cast hhorizon)).le
        (by
          exact (bernsteinSquareClippedExplorationRate_le_half
            (arms.card : Real) (horizon : Real) delta).trans (by norm_num))
        loss.environment
    mu {sample |
        bernsteinSquareRealizedExplicitThreshold arms gamma horizon delta <=
          (Finset.range horizon).sum (fun t =>
              sampledTrajectoryRealizedLossAt t sample) -
            (Finset.range horizon).sum (fun t =>
              predictableLossAt loss t sample comparator)} <=
      ENNReal.ofReal delta := by
  dsimp only
  have hK_one : 1 < (arms.card : Real) := by exact_mod_cast hcard_two
  have hT : 0 < (horizon : Real) := by exact_mod_cast hhorizon
  have hcontracts :=
    bernsteinSquareClippedExplorationRate_contracts
      (arms.card : Real) (horizon : Real) delta hK_one hT hdelta hdelta_le_one
        hlarge_arm hlarge_mixed hlarge_confidence hlarge_realized
  dsimp only at hcontracts
  rcases hcontracts with
    ⟨hgamma_pos, hgamma_le_half, hbase, hmixed, hconfidence, hrealized⟩
  exact
    sampledPredictable_gammaCharacterizedBernsteinSquareRealizedRegret_tail
      prior arms harms hcard_two
        (bernsteinSquareClippedExplorationRate
          (arms.card : Real) (horizon : Real) delta)
        hgamma_pos hgamma_le_half loss comparator hcomparator horizon hhorizon
        delta hdelta hdelta_le_one hbase hmixed hconfidence hrealized

end BanditRLProof.Exp3
