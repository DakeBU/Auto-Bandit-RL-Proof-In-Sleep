import BanditRLProof.Exp3MixedSquareExponentialRealizedTuning
import BanditRLProof.Exp3RandomSquareBernsteinRealizedExplicitTuning

/-!
# Explicit exploration tuning for exponential-square realized EXP3

This module closes the remaining exploration-parameter leaf in the generated
exponential mixed-square route.  The interval sub-Gaussian proxy contributes a
sixth-root scale because its range is `|arms| / gamma`; the two Bernstein
radii contribute a cube-root scale, and the realized deviation contributes a
square-root scale.  The resulting rate is deliberately recorded as the output
of the current Hoeffding-proxy route, not as a Freedman or EXP3.P rate.
-/

namespace BanditRLProof.Exp3

open MeasureTheory ProbabilityTheory

universe u v

/-- The mixed-square interval proxy is exactly `(K / (2 * gamma))^2`. -/
theorem sampledMixedSquaredVarianceProxy_coe_eq_card_div_two_gamma_sq
    {Action : Type v} (arms : Finset Action) (gamma : Real)
    (hgamma_pos : 0 < gamma) :
    ((sampledMixedSquaredVarianceProxy arms gamma : NNReal) : Real) =
      ((arms.card : Real) / (2 * gamma)) ^ 2 := by
  have hcard_nonneg : 0 <= (arms.card : Real) := by positivity
  have hfloor_nonneg : 0 <= gamma / (arms.card : Real) :=
    div_nonneg hgamma_pos.le hcard_nonneg
  unfold sampledMixedSquaredVarianceProxy Concentration.intervalVarianceProxy
  push_cast
  rw [Real.norm_of_nonneg]
  · field_simp [ne_of_gt hgamma_pos]
    ring
  · simpa using one_div_nonneg.mpr hfloor_nonneg

/-- The logarithmically weighted mixed-square confidence radius is controlled
by `gamma^2 T^2` under the sixth-power dominance contract. -/
theorem log_mul_sampledMixedSquaredConfidenceRadius_le_sq_mul_horizon_sq
    {Action : Type v} (arms : Finset Action) (gamma : Real)
    (hgamma_pos : 0 < gamma) (horizon : Nat) (hhorizon : 0 < horizon)
    (delta : Real) (hdelta : 0 < delta) (hdelta_le_one : delta <= 1)
    (hmixed :
      (arms.card : Real) ^ 2 * Real.log (arms.card : Real) ^ 2 *
            Real.log (4 / delta) / 2 <=
        gamma ^ 6 * (horizon : Real) ^ 3) :
    Real.log (arms.card : Real) *
        sampledMixedSquaredConfidenceRadius arms gamma horizon (delta / 4) <=
      gamma ^ 2 * (horizon : Real) ^ 2 := by
  let K : Real := arms.card
  let T : Real := horizon
  let L : Real := Real.log (4 / delta)
  let radius := sampledMixedSquaredConfidenceRadius
    arms gamma horizon (delta / 4)
  have hT : 0 < T := by
    dsimp [T]
    exact_mod_cast hhorizon
  have hK_nonneg : 0 <= K := by positivity
  have hlogK_nonneg : 0 <= Real.log K := by
    by_cases hK : K = 0
    · simp [hK]
    · exact Real.log_nonneg (by
        have hK_nat : 1 <= arms.card := Nat.one_le_iff_ne_zero.mpr (by
          intro hcard
          apply hK
          simp [K, hcard])
        dsimp [K]
        exact_mod_cast hK_nat)
  have hone_lt_four_div : 1 < 4 / delta := by
    rw [lt_div_iff₀ hdelta]
    nlinarith
  have hL : 0 <= L := (Real.log_pos hone_lt_four_div).le
  have hlog_fourth : Real.log (1 / (delta / 4)) = L := by
    dsimp [L]
    exact log_one_div_fourth_eq_log_four_div delta hdelta
  have hproxy :=
    sampledMixedSquaredVarianceProxy_coe_eq_card_div_two_gamma_sq
      arms gamma hgamma_pos
  have hradicand :
      0 <= 2 * (T * ((sampledMixedSquaredVarianceProxy arms gamma : NNReal) : Real)) * L := by
    positivity
  have hradius_nonneg : 0 <= radius := by
    dsimp [radius]
    exact Real.sqrt_nonneg _
  have hradius_sq :
      radius ^ 2 =
        2 * (T * ((sampledMixedSquaredVarianceProxy arms gamma : NNReal) : Real)) * L := by
    dsimp [radius, sampledMixedSquaredConfidenceRadius]
    push_cast
    rw [hlog_fourth, Real.sq_sqrt hradicand]
  have hleft_nonneg : 0 <= Real.log K * radius :=
    mul_nonneg hlogK_nonneg hradius_nonneg
  have hright_nonneg : 0 <= gamma ^ 2 * T ^ 2 := by positivity
  apply le_of_sq_le_sq
  · rw [mul_pow, hradius_sq, hproxy]
    dsimp [K, T, L] at hmixed ⊢
    have hgamma_ne : gamma ≠ 0 := ne_of_gt hgamma_pos
    have hT_nonneg : 0 <= (horizon : Real) := hT.le
    field_simp [hgamma_ne]
    nlinarith [hmixed]
  · simpa [K, T, radius] using hright_nonneg

/-- The armwise base term and the mixed-square confidence radius together
make the learning-rate-balanced square root at most `2 * gamma * T`. -/
theorem exponentialSquareBalancedSqrt_le_two_mul_gamma_mul_horizon
    {Action : Type v} (arms : Finset Action) (hcard_two : 2 <= arms.card)
    (gamma : Real) (hgamma_pos : 0 < gamma)
    (horizon : Nat) (hhorizon : 0 < horizon)
    (delta : Real) (hdelta : 0 < delta) (hdelta_le_one : delta <= 1)
    (hbase :
      (arms.card : Real) * Real.log (arms.card : Real) <=
        gamma ^ 2 * (horizon : Real))
    (hmixed :
      (arms.card : Real) ^ 2 * Real.log (arms.card : Real) ^ 2 *
            Real.log (4 / delta) / 2 <=
        gamma ^ 6 * (horizon : Real) ^ 3) :
    Real.sqrt
        (Real.log (arms.card : Real) *
          exponentialSquareHighProbabilityScale arms gamma horizon delta) <=
      2 * gamma * (horizon : Real) := by
  let K : Real := arms.card
  let T : Real := horizon
  let radius := sampledMixedSquaredConfidenceRadius
    arms gamma horizon (delta / 4)
  have hT : 0 < T := by
    dsimp [T]
    exact_mod_cast hhorizon
  have hK_one : 1 < K := by
    dsimp [K]
    exact_mod_cast hcard_two
  have hlogK : 0 <= Real.log K := (Real.log_pos hK_one).le
  have hradius_nonneg : 0 <= radius := by
    dsimp [radius, sampledMixedSquaredConfidenceRadius]
    exact Real.sqrt_nonneg _
  have hmixed_bound : Real.log K * radius <= gamma ^ 2 * T ^ 2 := by
    dsimp [K, T, radius]
    exact log_mul_sampledMixedSquaredConfidenceRadius_le_sq_mul_horizon_sq
      arms gamma hgamma_pos horizon hhorizon delta hdelta hdelta_le_one hmixed
  have hbase_bound : Real.log K * (K * T) <= gamma ^ 2 * T ^ 2 := by
    have hbase' : K * Real.log K <= gamma ^ 2 * T := by
      simpa [K, T] using hbase
    nlinarith
  rw [Real.sqrt_le_iff]
  constructor
  · positivity
  · dsimp [exponentialSquareHighProbabilityScale, K, T, radius] at *
    nlinarith

/-- Explicit threshold after controlling the balanced square root and all
three confidence contributions by the exploration scale. -/
noncomputable def exponentialSquareBernsteinRealizedExplicitThreshold
    {Action : Type v} (_arms : Finset Action) (gamma : Real)
    (horizon : Nat) (_delta : Real) : Real :=
  14 * gamma * (horizon : Real)

/-- Quadratic, sixth-power, cubic, and realized quadratic contracts reduce the
learning-rate-tuned threshold to `14 * gamma * T`. -/
theorem exponentialSquareBernsteinRealizedTunedThreshold_le_explicitThreshold
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
    exponentialSquareBernsteinRealizedTunedThreshold
        arms gamma horizon delta <=
      exponentialSquareBernsteinRealizedExplicitThreshold
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
  have hbalanced :
      Real.sqrt
          (Real.log K *
            exponentialSquareHighProbabilityScale arms gamma horizon delta) <=
        2 * gamma * T := by
    simpa [K, T] using
      exponentialSquareBalancedSqrt_le_two_mul_gamma_mul_horizon
        arms hcard_two gamma hgamma_pos horizon hhorizon delta hdelta
          hdelta_le_one hbase hmixed
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
  dsimp [exponentialSquareBernsteinRealizedTunedThreshold,
    exponentialSquareBernsteinRealizedExplicitThreshold,
    sampledPurePredictableMinusObservedBernsteinConfidenceRadius,
    sampledComparatorEstimatorBernsteinConfidenceRadius,
    sampledPredictableRealizedDeviationConfidenceRadius]
  rw [hmax_fourth, hlog_fourth]
  change
    3 * Real.sqrt
          (Real.log K *
            exponentialSquareHighProbabilityScale arms gamma horizon delta) +
        gamma * T +
        (2 * Real.sqrt (T * budget / (gamma / K)) +
          budget / (gamma / K)) +
        (2 * Real.sqrt (T * budget / (gamma / K)) +
          budget / (gamma / K)) +
        Real.sqrt (2 * (T * variance) * budget) <=
      14 * gamma * T
  linarith

/-- Generated realized-regret tail under the four algebraic exploration
contracts consumed by the explicit schedule below. -/
theorem sampledPredictable_gammaCharacterizedExponentialSquareBernsteinRealizedRegret_tail
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
    let eta := exponentialSquareHighProbabilityLearningRate
      arms gamma horizon delta
    let mu := prior ⊗ₘ sampledImportanceWeightedTrajectoryKernel arms harms
      eta gamma hgamma_pos.le (by linarith : gamma <= 1) loss.environment
    mu {sample |
        exponentialSquareBernsteinRealizedExplicitThreshold
            arms gamma horizon delta <=
          (Finset.range horizon).sum (fun t =>
              sampledTrajectoryRealizedLossAt t sample) -
            (Finset.range horizon).sum (fun t =>
              predictableLossAt loss t sample comparator)} <=
      ENNReal.ofReal delta := by
  dsimp only
  have hthreshold :=
    exponentialSquareBernsteinRealizedTunedThreshold_le_explicitThreshold
      arms hcard_two horizon hhorizon gamma delta hgamma_pos hgamma_le_half
        hdelta hdelta_le_one hbase hmixed hconfidence hrealized
  have htail :=
    sampledPredictable_tunedExponentialSquareBernsteinRealizedRegret_tail
      prior arms harms hcard_two gamma hgamma_pos hgamma_le_half loss comparator
        hcomparator horizon hhorizon delta hdelta
  dsimp only at htail ⊢
  calc
    (prior ⊗ₘ sampledImportanceWeightedTrajectoryKernel arms harms
        (exponentialSquareHighProbabilityLearningRate
          arms gamma horizon delta)
        gamma hgamma_pos.le (by linarith : gamma <= 1) loss.environment)
        {sample |
          exponentialSquareBernsteinRealizedExplicitThreshold
              arms gamma horizon delta <=
            (Finset.range horizon).sum (fun t =>
                sampledTrajectoryRealizedLossAt t sample) -
              (Finset.range horizon).sum (fun t =>
                predictableLossAt loss t sample comparator)} <=
      (prior ⊗ₘ sampledImportanceWeightedTrajectoryKernel arms harms
        (exponentialSquareHighProbabilityLearningRate
          arms gamma horizon delta)
        gamma hgamma_pos.le (by linarith : gamma <= 1) loss.environment)
        {sample |
          exponentialSquareBernsteinRealizedTunedThreshold
              arms gamma horizon delta <=
            (Finset.range horizon).sum (fun t =>
                sampledTrajectoryRealizedLossAt t sample) -
              (Finset.range horizon).sum (fun t =>
                predictableLossAt loss t sample comparator)} := by
        apply measure_mono
        intro sample hsample
        exact hthreshold.trans hsample
    _ <= ENNReal.ofReal delta := htail

/-- Square-root component required by the armwise `K * T` part of the
exponential-square scale. -/
noncomputable def exponentialSquareArmExplorationScale
    (K T : Real) : Real :=
  Real.sqrt (K * Real.log K / T)

/-- Sixth-root component forced by the current interval variance proxy
`(K / (2 * gamma))^2`. -/
noncomputable def exponentialSquareMixedExplorationScale
    (K T delta : Real) : Real :=
  (K ^ 2 * Real.log K ^ 2 * Real.log (4 / delta) /
      (2 * T ^ 3)) ^ (6 : Real)⁻¹

/-- Unclipped maximum of the arm, mixed-square, Bernstein-confidence, and
realized-deviation exploration scales. -/
noncomputable def exponentialSquareBernsteinRawExplorationRate
    (K T delta : Real) : Real :=
  max (exponentialSquareArmExplorationScale K T)
    (max (exponentialSquareMixedExplorationScale K T delta)
      (max (randomSquareBernsteinConfidenceExplorationScale K T delta)
        (randomSquareBernsteinRealizedExplorationScale T delta)))

/-- Explicit exploration schedule clipped into the Hedge stability regime. -/
noncomputable def exponentialSquareBernsteinClippedExplorationRate
    (K T delta : Real) : Real :=
  min (1 / 2) (exponentialSquareBernsteinRawExplorationRate K T delta)

/-- A nonnegative sixth-root scale is at most one half when its numerator is
at most one sixty-fourth of its positive denominator. -/
theorem rpow_inv_six_le_half_of_sixtyfour_mul_le
    (numerator denominator : Real) (hnumerator : 0 <= numerator)
    (hdenominator : 0 < denominator)
    (hlarge : 64 * numerator <= denominator) :
    (numerator / denominator) ^ (6 : Real)⁻¹ <= 1 / 2 := by
  have hsix :
      ((numerator / denominator) ^ (6 : Real)⁻¹) ^ (6 : Nat) =
        numerator / denominator := by
    convert Real.rpow_inv_natCast_pow (n := 6)
      (div_nonneg hnumerator hdenominator.le) (by norm_num) using 1
  apply le_of_pow_le_pow_left₀ (n := 6) (by positivity) (by norm_num)
  rw [hsix]
  norm_num
  rw [div_le_iff₀ hdenominator]
  nlinarith

/-- If a sixth-root scale is below `gamma`, its numerator satisfies the
corresponding sixth-power dominance contract. -/
theorem numerator_le_pow_six_mul_of_rpow_inv_six_le
    (numerator denominator gamma : Real) (hnumerator : 0 <= numerator)
    (hdenominator : 0 < denominator)
    (hroot : (numerator / denominator) ^ (6 : Real)⁻¹ <= gamma) :
    numerator <= gamma ^ 6 * denominator := by
  have hroot_nonneg :
      0 <= (numerator / denominator) ^ (6 : Real)⁻¹ :=
    Real.rpow_nonneg (div_nonneg hnumerator hdenominator.le) _
  have hsix :
      ((numerator / denominator) ^ (6 : Real)⁻¹) ^ (6 : Nat) =
        numerator / denominator := by
    convert Real.rpow_inv_natCast_pow (n := 6)
      (div_nonneg hnumerator hdenominator.le) (by norm_num) using 1
  have hpow := pow_le_pow_left₀ hroot_nonneg hroot 6
  rw [hsix] at hpow
  calc
    numerator = (numerator / denominator) * denominator := by
      field_simp [ne_of_gt hdenominator]
    _ <= gamma ^ 6 * denominator :=
      mul_le_mul_of_nonneg_right hpow hdenominator.le

theorem exponentialSquareBernsteinClippedExplorationRate_le_half
    (K T delta : Real) :
    exponentialSquareBernsteinClippedExplorationRate K T delta <= 1 / 2 := by
  exact min_le_left _ _

theorem exponentialSquareBernsteinClippedExplorationRate_eq_raw
    (K T delta : Real)
    (hraw : exponentialSquareBernsteinRawExplorationRate K T delta <= 1 / 2) :
    exponentialSquareBernsteinClippedExplorationRate K T delta =
      exponentialSquareBernsteinRawExplorationRate K T delta := by
  exact min_eq_right hraw

theorem exponentialSquareBernsteinRawExplorationRate_pos
    (K T delta : Real) (hK_one : 1 < K) (hT : 0 < T) :
    0 < exponentialSquareBernsteinRawExplorationRate K T delta := by
  have hbase : 0 < K * Real.log K / T :=
    div_pos (mul_pos (lt_trans zero_lt_one hK_one) (Real.log_pos hK_one)) hT
  have hscale : 0 < exponentialSquareArmExplorationScale K T := by
    exact Real.sqrt_pos.2 hbase
  exact hscale.trans_le (le_max_left _ _)

theorem exponentialSquareBernsteinClippedExplorationRate_pos
    (K T delta : Real) (hK_one : 1 < K) (hT : 0 < T) :
    0 < exponentialSquareBernsteinClippedExplorationRate K T delta := by
  apply lt_min
  · norm_num
  · exact exponentialSquareBernsteinRawExplorationRate_pos
      K T delta hK_one hT

/-- Four transparent horizon contracts ensure every raw schedule component is
at most one half, hence clipping is inactive. -/
theorem exponentialSquareBernsteinRawExplorationRate_le_half_of_horizon_contracts
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
    exponentialSquareBernsteinRawExplorationRate K T delta <= 1 / 2 := by
  have hK : 0 < K := lt_trans zero_lt_one hK_one
  have hlogK : 0 <= Real.log K := (Real.log_pos hK_one).le
  have hone_lt_four_div : 1 < 4 / delta := by
    rw [lt_div_iff₀ hdelta]
    nlinarith
  have hlog : 0 <= Real.log (4 / delta) :=
    (Real.log_pos hone_lt_four_div).le
  have hmixed_nonneg :
      0 <= K ^ 2 * Real.log K ^ 2 * Real.log (4 / delta) / 2 := by
    positivity
  rw [exponentialSquareBernsteinRawExplorationRate]
  apply max_le
  · exact sqrt_div_le_half_of_four_mul_le
      (K * Real.log K) T hT hlarge_arm
  apply max_le
  · dsimp [exponentialSquareMixedExplorationScale]
    have hsplit :
        K ^ 2 * Real.log K ^ 2 * Real.log (4 / delta) / (2 * T ^ 3) =
          (K ^ 2 * Real.log K ^ 2 * Real.log (4 / delta) / 2) /
            T ^ 3 := by
      field_simp [ne_of_gt hT]
    rw [hsplit]
    exact rpow_inv_six_le_half_of_sixtyfour_mul_le
      (K ^ 2 * Real.log K ^ 2 * Real.log (4 / delta) / 2)
      (T ^ 3) hmixed_nonneg (by positivity) hlarge_mixed
  apply max_le
  · exact rpow_inv_three_le_half_of_eight_mul_le
      (K * Real.log (4 / delta)) T (mul_nonneg hK.le hlog) hT
        hlarge_confidence
  · apply sqrt_div_le_half_of_four_mul_le
    · exact hT
    · nlinarith [hlarge_realized]

/-- The clipped maximum satisfies exactly the four contracts consumed by the
gamma-characterized tail theorem. -/
theorem exponentialSquareBernsteinClippedExplorationRate_contracts
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
    let gamma := exponentialSquareBernsteinClippedExplorationRate K T delta
    0 < gamma ∧ gamma <= 1 / 2 ∧
      K * Real.log K <= gamma ^ 2 * T ∧
      K ^ 2 * Real.log K ^ 2 * Real.log (4 / delta) / 2 <=
        gamma ^ 6 * T ^ 3 ∧
      K * Real.log (4 / delta) <= gamma ^ 3 * T ∧
      2 * ((Concentration.intervalVarianceProxy 0 1 : NNReal) : Real) *
          Real.log (4 / delta) <= gamma ^ 2 * T := by
  dsimp only
  let variance : Real :=
    ((Concentration.intervalVarianceProxy 0 1 : NNReal) : Real)
  have hK : 0 < K := lt_trans zero_lt_one hK_one
  have hlogK : 0 <= Real.log K := (Real.log_pos hK_one).le
  have hone_lt_four_div : 1 < 4 / delta := by
    rw [lt_div_iff₀ hdelta]
    nlinarith
  have hlog : 0 <= Real.log (4 / delta) :=
    (Real.log_pos hone_lt_four_div).le
  have hvariance : 0 <= variance := NNReal.coe_nonneg _
  have hmixed_nonneg :
      0 <= K ^ 2 * Real.log K ^ 2 * Real.log (4 / delta) / 2 := by
    positivity
  have hsplit :
      K ^ 2 * Real.log K ^ 2 * Real.log (4 / delta) / (2 * T ^ 3) =
        (K ^ 2 * Real.log K ^ 2 * Real.log (4 / delta) / 2) /
          T ^ 3 := by
    field_simp [ne_of_gt hT]
  have hraw :=
    exponentialSquareBernsteinRawExplorationRate_le_half_of_horizon_contracts
      K T delta hK_one hT hdelta hdelta_le_one hlarge_arm hlarge_mixed
        hlarge_confidence hlarge_realized
  have hclip : exponentialSquareBernsteinClippedExplorationRate K T delta =
      exponentialSquareBernsteinRawExplorationRate K T delta :=
    exponentialSquareBernsteinClippedExplorationRate_eq_raw K T delta hraw
  have harm_component : exponentialSquareArmExplorationScale K T <=
      exponentialSquareBernsteinClippedExplorationRate K T delta := by
    rw [hclip, exponentialSquareBernsteinRawExplorationRate]
    exact le_max_left _ _
  have hmixed_component : exponentialSquareMixedExplorationScale K T delta <=
      exponentialSquareBernsteinClippedExplorationRate K T delta := by
    rw [hclip, exponentialSquareBernsteinRawExplorationRate]
    exact le_max_of_le_right (le_max_left _ _)
  have hconfidence_component :
      randomSquareBernsteinConfidenceExplorationScale K T delta <=
        exponentialSquareBernsteinClippedExplorationRate K T delta := by
    rw [hclip, exponentialSquareBernsteinRawExplorationRate]
    exact le_max_of_le_right (le_max_of_le_right (le_max_left _ _))
  have hrealized_component :
      randomSquareBernsteinRealizedExplorationScale T delta <=
        exponentialSquareBernsteinClippedExplorationRate K T delta := by
    rw [hclip, exponentialSquareBernsteinRawExplorationRate]
    exact le_max_of_le_right (le_max_of_le_right (le_max_right _ _))
  refine ⟨
    exponentialSquareBernsteinClippedExplorationRate_pos
      K T delta hK_one hT,
    exponentialSquareBernsteinClippedExplorationRate_le_half K T delta,
    ?_, ?_, ?_, ?_⟩
  · exact numerator_le_sq_mul_of_sqrt_div_le
      (K * Real.log K) T
        (exponentialSquareBernsteinClippedExplorationRate K T delta)
        (mul_nonneg hK.le hlogK) hT (by
          simpa [exponentialSquareArmExplorationScale] using harm_component)
  · have hroot :
        (K ^ 2 * Real.log K ^ 2 * Real.log (4 / delta) / 2 /
            T ^ 3) ^ (6 : Real)⁻¹ <=
          exponentialSquareBernsteinClippedExplorationRate K T delta := by
      simpa only [exponentialSquareMixedExplorationScale, hsplit] using
        hmixed_component
    exact numerator_le_pow_six_mul_of_rpow_inv_six_le
      (K ^ 2 * Real.log K ^ 2 * Real.log (4 / delta) / 2) (T ^ 3)
        (exponentialSquareBernsteinClippedExplorationRate K T delta)
        hmixed_nonneg (by positivity) hroot
  · exact numerator_le_cube_mul_of_rpow_inv_three_le
      (K * Real.log (4 / delta)) T
        (exponentialSquareBernsteinClippedExplorationRate K T delta)
        (mul_nonneg hK.le hlog) hT (by
          simpa [randomSquareBernsteinConfidenceExplorationScale] using
            hconfidence_component)
  · exact numerator_le_sq_mul_of_sqrt_div_le
      (2 * variance * Real.log (4 / delta)) T
        (exponentialSquareBernsteinClippedExplorationRate K T delta)
        (mul_nonneg (mul_nonneg (by norm_num) hvariance) hlog) hT (by
          simpa [randomSquareBernsteinRealizedExplorationScale, variance] using
            hrealized_component)

/-- Fully explicit generated realized-regret tail for the clipped maximum of
the four exploration scales. -/
theorem sampledPredictable_explicitExponentialSquareBernsteinRealizedRegret_tail
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
    let gamma := exponentialSquareBernsteinClippedExplorationRate
      (arms.card : Real) (horizon : Real) delta
    let eta := exponentialSquareHighProbabilityLearningRate
      arms gamma horizon delta
    let mu := prior ⊗ₘ sampledImportanceWeightedTrajectoryKernel arms harms
      eta gamma
        (exponentialSquareBernsteinClippedExplorationRate_pos
          (arms.card : Real) (horizon : Real) delta
          (by exact_mod_cast hcard_two)
          (by exact_mod_cast hhorizon)).le
        (by
          exact (exponentialSquareBernsteinClippedExplorationRate_le_half
            (arms.card : Real) (horizon : Real) delta).trans (by norm_num))
        loss.environment
    mu {sample |
        exponentialSquareBernsteinRealizedExplicitThreshold
            arms gamma horizon delta <=
          (Finset.range horizon).sum (fun t =>
              sampledTrajectoryRealizedLossAt t sample) -
            (Finset.range horizon).sum (fun t =>
              predictableLossAt loss t sample comparator)} <=
      ENNReal.ofReal delta := by
  dsimp only
  have hK_one : 1 < (arms.card : Real) := by exact_mod_cast hcard_two
  have hT : 0 < (horizon : Real) := by exact_mod_cast hhorizon
  have hcontracts :=
    exponentialSquareBernsteinClippedExplorationRate_contracts
      (arms.card : Real) (horizon : Real) delta hK_one hT hdelta hdelta_le_one
        hlarge_arm hlarge_mixed hlarge_confidence hlarge_realized
  dsimp only at hcontracts
  rcases hcontracts with
    ⟨hgamma_pos, hgamma_le_half, hbase, hmixed, hconfidence, hrealized⟩
  exact
    sampledPredictable_gammaCharacterizedExponentialSquareBernsteinRealizedRegret_tail
      prior arms harms hcard_two
        (exponentialSquareBernsteinClippedExplorationRate
          (arms.card : Real) (horizon : Real) delta)
        hgamma_pos hgamma_le_half loss comparator hcomparator horizon hhorizon
        delta hdelta hdelta_le_one hbase hmixed hconfidence hrealized

end BanditRLProof.Exp3
