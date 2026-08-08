import BanditRLProof.Exp3MixedSquarePredictableVarianceSparseLossRealizedMarkovTuning
import BanditRLProof.Exp3MixedSquareExponentialRealizedExplicitTuning

/-!
# Explicit exploration tuning for sparse-loss predictable-variance EXP3

This module closes the exploration-parameter leaf for the sparse-loss
predictable-variance Markov route. Besides the usual sparse arm, Bernstein
confidence, and realized-deviation scales, the Markov variance threshold
introduces the fifth-root scale

`(5 K s (log K)^2 log(5 / delta) / (delta T^3))^(1/5)`.

Under transparent large-horizon contracts, the clipped maximum of these four
scales is positive, at most `1 / 2`, and satisfies every algebraic premise of
the gamma-characterized theorem. The resulting generated realized-regret tail
has threshold `14 * gamma * T`.

The result still assumes pathwise armwise sparse losses and uses Markov control
for predictable-variance overflow. It is not a best-arm first-order theorem.
-/

namespace BanditRLProof.Exp3

open MeasureTheory ProbabilityTheory

universe u v

/-- The five-way confidence allocation has logarithmic budget
`log (5 / delta)`. -/
theorem log_one_div_fifth_eq_log_five_div
    (delta : Real) (hdelta : 0 < delta) :
    Real.log (1 / (delta / 5)) = Real.log (5 / delta) := by
  congr 1
  field_simp [ne_of_gt hdelta]

/-- Closed form of the sparse-loss Markov predictable-variance budget. -/
theorem sparseLossPredictableVarianceBudget_eq
    {Action : Type v} (arms : Finset Action) (hcard_two : 2 <= arms.card)
    (gamma : Real) (hgamma_pos : 0 < gamma)
    (horizon sparsity : Nat) (delta : Real) (hdelta : 0 < delta) :
    sparseLossPredictableVarianceBudget arms gamma horizon sparsity delta =
      5 * (arms.card : Real) * (sparsity : Real) * (horizon : Real) /
        (gamma * delta) := by
  have hK : 0 < (arms.card : Real) := by positivity
  dsimp [sparseLossPredictableVarianceBudget]
  field_simp [ne_of_gt hK, ne_of_gt hgamma_pos, ne_of_gt hdelta]

/-- Under the sparse base, fifth-power Markov, and cubic confidence
contracts, the log-weighted mixed-square radius is at most
`3 * gamma^2 * T^2`. -/
theorem log_mul_sparseLossPredictableVarianceRadius_le_three_mul_sq_mul_horizon_sq
    {Action : Type v} [DecidableEq Action]
    (arms : Finset Action) (hcard_two : 2 <= arms.card)
    (gamma : Real) (hgamma_pos : 0 < gamma)
    (hgamma_le_half : gamma <= 1 / 2)
    (horizon sparsity : Nat) (hhorizon : 0 < horizon)
    (hsparsity : 0 < sparsity)
    (delta : Real) (hdelta : 0 < delta) (hdelta_le_one : delta <= 1)
    (hbase :
      (sparsity : Real) * Real.log (arms.card : Real) <=
        gamma ^ 2 * (horizon : Real))
    (hmixed :
      5 * (arms.card : Real) * (sparsity : Real) *
            Real.log (arms.card : Real) ^ 2 * Real.log (5 / delta) <=
        gamma ^ 5 * delta * (horizon : Real) ^ 3)
    (hconfidence :
      (arms.card : Real) * Real.log (5 / delta) <=
        gamma ^ 3 * (horizon : Real)) :
    Real.log (arms.card : Real) *
        sampledMixedSquaredPredictableVarianceRadius arms gamma
          (sparseLossPredictableVarianceBudget
            arms gamma horizon sparsity delta)
          (delta / 5) <=
      3 * gamma ^ 2 * (horizon : Real) ^ 2 := by
  let K : Real := arms.card
  let S : Real := sparsity
  let T : Real := horizon
  let B : Real := Real.log (5 / delta)
  let variance :=
    sparseLossPredictableVarianceBudget arms gamma horizon sparsity delta
  have hK_one : 1 < K := by
    dsimp [K]
    exact_mod_cast hcard_two
  have hK : 0 < K := lt_trans zero_lt_one hK_one
  have hS_one : 1 <= S := by
    dsimp [S]
    exact_mod_cast hsparsity
  have hS : 0 < S := lt_of_lt_of_le zero_lt_one hS_one
  have hT : 0 < T := by
    dsimp [T]
    exact_mod_cast hhorizon
  have hlogK : 0 <= Real.log K := (Real.log_pos hK_one).le
  have hone_lt_five_div : 1 < 5 / delta := by
    rw [lt_div_iff₀ hdelta]
    nlinarith
  have hB : 0 < B := by
    dsimp [B]
    exact Real.log_pos hone_lt_five_div
  have hlog_fifth : Real.log (1 / (delta / 5)) = B := by
    dsimp [B]
    exact log_one_div_fifth_eq_log_five_div delta hdelta
  have hmax_fifth : max (Real.log (1 / (delta / 5))) 0 = B := by
    rw [hlog_fifth]
    exact max_eq_left hB.le
  have hvariance :
      variance = 5 * K * S * T / (gamma * delta) := by
    dsimp [variance, K, S, T]
    exact sparseLossPredictableVarianceBudget_eq
      arms hcard_two gamma hgamma_pos horizon sparsity delta hdelta
  have hvariance_pos : 0 < variance := by
    rw [hvariance]
    positivity
  have hradicand : 0 <= variance * B :=
    mul_nonneg hvariance_pos.le hB.le
  have hroot_nonneg :
      0 <= Real.log K * Real.sqrt (variance * B) :=
    mul_nonneg hlogK (Real.sqrt_nonneg _)
  have hroot_right_nonneg : 0 <= gamma ^ 2 * T ^ 2 := by positivity
  have hmixed' :
      5 * K * S * Real.log K ^ 2 * B <=
        gamma ^ 5 * delta * T ^ 3 := by
    simpa [K, S, T, B] using hmixed
  have hroot :
      Real.log K * Real.sqrt (variance * B) <=
        gamma ^ 2 * T ^ 2 := by
    apply le_of_sq_le_sq
    · rw [mul_pow, Real.sq_sqrt hradicand, hvariance]
      field_simp [ne_of_gt hgamma_pos, ne_of_gt hdelta]
      nlinarith [hmixed']
    · exact hroot_right_nonneg
  have hgamma_sq_le_one : gamma ^ 2 <= 1 := by
    nlinarith [hgamma_pos, hgamma_le_half]
  have hlog_le_Slog : Real.log K <= S * Real.log K := by
    have hmul := mul_nonneg (sub_nonneg.mpr hS_one) hlogK
    nlinarith
  have hgamma_sq_T_le_T : gamma ^ 2 * T <= T := by
    have hmul := mul_nonneg (sub_nonneg.mpr hgamma_sq_le_one) hT.le
    nlinarith
  have hlog_le_T : Real.log K <= T := by
    have hbase' : S * Real.log K <= gamma ^ 2 * T := by
      simpa [K, S, T] using hbase
    linarith
  have hconfidence' : K * B <= gamma ^ 3 * T := by
    simpa [K, T, B] using hconfidence
  have hconfidence_nonneg : 0 <= gamma ^ 3 * T := by positivity
  have hprod_one := mul_le_mul_of_nonneg_right hconfidence' hlogK
  have hprod_two :=
    mul_le_mul_of_nonneg_left hlog_le_T hconfidence_nonneg
  have hprod : (K * B) * Real.log K <= gamma ^ 3 * T ^ 2 := by
    calc
      (K * B) * Real.log K <= (gamma ^ 3 * T) * Real.log K := hprod_one
      _ <= (gamma ^ 3 * T) * T := hprod_two
      _ = gamma ^ 3 * T ^ 2 := by ring
  have hlinear :
      Real.log K * (B / (gamma / K)) <= gamma ^ 2 * T ^ 2 := by
    calc
      Real.log K * (B / (gamma / K)) =
          ((K * B) * Real.log K) / gamma := by
        field_simp [ne_of_gt hK, ne_of_gt hgamma_pos]
      _ <= (gamma ^ 3 * T ^ 2) / gamma :=
        div_le_div_of_nonneg_right hprod hgamma_pos.le
      _ = gamma ^ 2 * T ^ 2 := by
        field_simp [ne_of_gt hgamma_pos]
  dsimp [sampledMixedSquaredPredictableVarianceRadius]
  rw [hmax_fifth]
  change
    Real.log K * (2 * Real.sqrt (variance * B) + B / (gamma / K)) <=
      3 * gamma ^ 2 * T ^ 2
  rw [mul_add]
  nlinarith [hroot, hlinear]

/-- The sparse base term and Markov predictable-variance radius make the
learning-rate-balanced square root at most `2 * gamma * T`. -/
theorem sparseLossPredictableVarianceBalancedSqrt_le_two_mul_gamma_mul_horizon
    {Action : Type v} [DecidableEq Action]
    (arms : Finset Action) (hcard_two : 2 <= arms.card)
    (gamma : Real) (hgamma_pos : 0 < gamma)
    (hgamma_le_half : gamma <= 1 / 2)
    (horizon sparsity : Nat) (hhorizon : 0 < horizon)
    (hsparsity : 0 < sparsity)
    (delta : Real) (hdelta : 0 < delta) (hdelta_le_one : delta <= 1)
    (hbase :
      (sparsity : Real) * Real.log (arms.card : Real) <=
        gamma ^ 2 * (horizon : Real))
    (hmixed :
      5 * (arms.card : Real) * (sparsity : Real) *
            Real.log (arms.card : Real) ^ 2 * Real.log (5 / delta) <=
        gamma ^ 5 * delta * (horizon : Real) ^ 3)
    (hconfidence :
      (arms.card : Real) * Real.log (5 / delta) <=
        gamma ^ 3 * (horizon : Real)) :
    Real.sqrt
        (Real.log (arms.card : Real) *
          sparseLossPredictableVarianceHighProbabilityScale
            arms gamma horizon sparsity delta) <=
      2 * gamma * (horizon : Real) := by
  let K : Real := arms.card
  let S : Real := sparsity
  let T : Real := horizon
  let radius :=
    sampledMixedSquaredPredictableVarianceRadius arms gamma
      (sparseLossPredictableVarianceBudget
        arms gamma horizon sparsity delta)
      (delta / 5)
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
    have hbudget : 0 <= max (Real.log (1 / (delta / 5))) 0 :=
      le_max_right _ _
    dsimp [radius, sampledMixedSquaredPredictableVarianceRadius, K]
    exact add_nonneg
      (mul_nonneg (by norm_num) (Real.sqrt_nonneg _))
      (div_nonneg hbudget hepsilon.le)
  have hradius_bound :
      Real.log K * radius <= 3 * gamma ^ 2 * T ^ 2 := by
    dsimp [K, T, radius]
    exact
      log_mul_sparseLossPredictableVarianceRadius_le_three_mul_sq_mul_horizon_sq
        arms hcard_two gamma hgamma_pos hgamma_le_half horizon sparsity
          hhorizon hsparsity delta hdelta hdelta_le_one hbase hmixed hconfidence
  have hbase_bound :
      Real.log K * (S * T) <= gamma ^ 2 * T ^ 2 := by
    have hbase' : S * Real.log K <= gamma ^ 2 * T := by
      simpa [K, S, T] using hbase
    nlinarith
  rw [Real.sqrt_le_iff]
  constructor
  · positivity
  · dsimp [sparseLossPredictableVarianceHighProbabilityScale,
      K, S, T, radius] at *
    nlinarith

/-- Explicit sparse-loss realized-regret threshold after exploration tuning. -/
noncomputable def sparseLossPredictableVarianceRealizedMarkovExplicitThreshold
    {Action : Type v} (_arms : Finset Action) (gamma : Real)
    (horizon _sparsity : Nat) (_delta : Real) : Real :=
  14 * gamma * (horizon : Real)

/-- The four algebraic exploration contracts reduce the eta-tuned threshold
to `14 * gamma * T`. -/
theorem sparseLossPredictableVarianceRealizedMarkovTunedThreshold_le_explicitThreshold
    {Action : Type v} [DecidableEq Action]
    (arms : Finset Action) (hcard_two : 2 <= arms.card)
    (horizon sparsity : Nat) (hhorizon : 0 < horizon)
    (hsparsity : 0 < sparsity)
    (gamma delta : Real) (hgamma_pos : 0 < gamma)
    (hgamma_le_half : gamma <= 1 / 2)
    (hdelta : 0 < delta) (hdelta_le_one : delta <= 1)
    (hbase :
      (sparsity : Real) * Real.log (arms.card : Real) <=
        gamma ^ 2 * (horizon : Real))
    (hmixed :
      5 * (arms.card : Real) * (sparsity : Real) *
            Real.log (arms.card : Real) ^ 2 * Real.log (5 / delta) <=
        gamma ^ 5 * delta * (horizon : Real) ^ 3)
    (hconfidence :
      (arms.card : Real) * Real.log (5 / delta) <=
        gamma ^ 3 * (horizon : Real))
    (hrealized :
      2 * ((Concentration.intervalVarianceProxy 0 1 : NNReal) : Real) *
          Real.log (5 / delta) <=
        gamma ^ 2 * (horizon : Real)) :
    sparseLossPredictableVarianceRealizedMarkovTunedThreshold
        arms gamma horizon sparsity delta <=
      sparseLossPredictableVarianceRealizedMarkovExplicitThreshold
        arms gamma horizon sparsity delta := by
  let K : Real := arms.card
  let T : Real := horizon
  let budget : Real := Real.log (5 / delta)
  let variance : Real :=
    ((Concentration.intervalVarianceProxy 0 1 : NNReal) : Real)
  have hK_one : 1 < K := by
    dsimp [K]
    exact_mod_cast hcard_two
  have hK : 0 < K := lt_trans zero_lt_one hK_one
  have hT : 0 < T := by
    dsimp [T]
    exact_mod_cast hhorizon
  have hone_lt_five_div : 1 < 5 / delta := by
    rw [lt_div_iff₀ hdelta]
    nlinarith
  have hbudget_pos : 0 < budget := by
    dsimp [budget]
    exact Real.log_pos hone_lt_five_div
  have hlog_fifth : Real.log (1 / (delta / 5)) = budget := by
    dsimp [budget]
    exact log_one_div_fifth_eq_log_five_div delta hdelta
  have hmax_fifth : max (Real.log (1 / (delta / 5))) 0 = budget := by
    rw [hlog_fifth]
    exact max_eq_left hbudget_pos.le
  have hbalanced :
      Real.sqrt
          (Real.log K *
            sparseLossPredictableVarianceHighProbabilityScale
              arms gamma horizon sparsity delta) <=
        2 * gamma * T := by
    simpa [K, T] using
      sparseLossPredictableVarianceBalancedSqrt_le_two_mul_gamma_mul_horizon
        arms hcard_two gamma hgamma_pos hgamma_le_half horizon sparsity
          hhorizon hsparsity delta hdelta hdelta_le_one hbase hmixed hconfidence
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
  dsimp [sparseLossPredictableVarianceRealizedMarkovTunedThreshold,
    sparseLossPredictableVarianceRealizedMarkovExplicitThreshold,
    sampledPurePredictableMinusObservedBernsteinConfidenceRadius,
    sampledComparatorEstimatorBernsteinConfidenceRadius,
    sampledPredictableRealizedDeviationConfidenceRadius]
  rw [hmax_fifth, hlog_fifth]
  change
    3 * Real.sqrt
          (Real.log K *
            sparseLossPredictableVarianceHighProbabilityScale
              arms gamma horizon sparsity delta) +
        gamma * T +
        (2 * Real.sqrt (T * budget / (gamma / K)) +
          budget / (gamma / K)) +
        (2 * Real.sqrt (T * budget / (gamma / K)) +
          budget / (gamma / K)) +
        Real.sqrt (2 * (T * variance) * budget) <=
      14 * gamma * T
  linarith

/-- Generated sparse-loss realized-regret tail under four algebraic
exploration contracts. -/
theorem sampledPredictable_gammaCharacterizedSparseLossPredictableVarianceRealizedMarkovRegret_tail
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
    (horizon sparsity : Nat) (hhorizon : 0 < horizon)
    (hsparsity : 0 < sparsity)
    (delta : Real) (hdelta : 0 < delta) (hdelta_le_one : delta <= 1)
    (hbase :
      (sparsity : Real) * Real.log (arms.card : Real) <=
        gamma ^ 2 * (horizon : Real))
    (hmixed :
      5 * (arms.card : Real) * (sparsity : Real) *
            Real.log (arms.card : Real) ^ 2 * Real.log (5 / delta) <=
        gamma ^ 5 * delta * (horizon : Real) ^ 3)
    (hconfidence :
      (arms.card : Real) * Real.log (5 / delta) <=
        gamma ^ 3 * (horizon : Real))
    (hrealized :
      2 * ((Concentration.intervalVarianceProxy 0 1 : NNReal) : Real) *
          Real.log (5 / delta) <=
        gamma ^ 2 * (horizon : Real))
    (hsparse : ∀ sample t, t < horizon →
      (sampledPredictableLossSupport arms loss t sample).card <= sparsity) :
    let eta := sparseLossPredictableVarianceHighProbabilityLearningRate
      arms gamma horizon sparsity delta
    let mu := prior ⊗ₘ sampledImportanceWeightedTrajectoryKernel arms harms
      eta gamma hgamma_pos.le (by linarith : gamma <= 1) loss.environment
    mu {sample |
        sparseLossPredictableVarianceRealizedMarkovExplicitThreshold
            arms gamma horizon sparsity delta <=
          (Finset.range horizon).sum (fun t =>
              sampledTrajectoryRealizedLossAt t sample) -
            (Finset.range horizon).sum (fun t =>
              predictableLossAt loss t sample comparator)} <=
      ENNReal.ofReal delta := by
  dsimp only
  have hgamma_lt_one : gamma < 1 := by linarith
  have hthreshold :=
    sparseLossPredictableVarianceRealizedMarkovTunedThreshold_le_explicitThreshold
      arms hcard_two horizon sparsity hhorizon hsparsity gamma delta
        hgamma_pos hgamma_le_half hdelta hdelta_le_one hbase hmixed
        hconfidence hrealized
  have htail :=
    sampledPredictable_tunedSparseLossPredictableVarianceRealizedMarkovRegret_tail
      prior arms harms hcard_two gamma hgamma_pos hgamma_le_half loss comparator
        hcomparator horizon sparsity hhorizon hsparsity delta hdelta hsparse
  dsimp only at htail ⊢
  calc
    (prior ⊗ₘ sampledImportanceWeightedTrajectoryKernel arms harms
        (sparseLossPredictableVarianceHighProbabilityLearningRate
          arms gamma horizon sparsity delta)
        gamma hgamma_pos.le hgamma_lt_one.le loss.environment)
        {sample |
          sparseLossPredictableVarianceRealizedMarkovExplicitThreshold
              arms gamma horizon sparsity delta <=
            (Finset.range horizon).sum (fun t =>
                sampledTrajectoryRealizedLossAt t sample) -
              (Finset.range horizon).sum (fun t =>
                predictableLossAt loss t sample comparator)} <=
      (prior ⊗ₘ sampledImportanceWeightedTrajectoryKernel arms harms
        (sparseLossPredictableVarianceHighProbabilityLearningRate
          arms gamma horizon sparsity delta)
        gamma hgamma_pos.le hgamma_lt_one.le loss.environment)
        {sample |
          sparseLossPredictableVarianceRealizedMarkovTunedThreshold
              arms gamma horizon sparsity delta <=
            (Finset.range horizon).sum (fun t =>
                sampledTrajectoryRealizedLossAt t sample) -
              (Finset.range horizon).sum (fun t =>
                predictableLossAt loss t sample comparator)} := by
        apply measure_mono
        intro sample hsample
        exact hthreshold.trans hsample
    _ <= ENNReal.ofReal delta := htail

/-- Square-root component required by the pathwise sparse-loss base term. -/
noncomputable def sparseLossPredictableVarianceArmExplorationScale
    (K S T : Real) : Real :=
  Real.sqrt (S * Real.log K / T)

/-- Fifth-root component forced by the sparse-loss Markov variance threshold. -/
noncomputable def sparseLossPredictableVarianceMarkovExplorationScale
    (K S T delta : Real) : Real :=
  (5 * K * S * Real.log K ^ 2 * Real.log (5 / delta) /
      (delta * T ^ 3)) ^ (5 : Real)⁻¹

/-- Cube-root component required by both Bernstein confidence radii. -/
noncomputable def sparseLossPredictableVarianceConfidenceExplorationScale
    (K T delta : Real) : Real :=
  (K * Real.log (5 / delta) / T) ^ (3 : Real)⁻¹

/-- Square-root component required by the bounded realized-deviation radius. -/
noncomputable def sparseLossPredictableVarianceRealizedExplorationScale
    (T delta : Real) : Real :=
  Real.sqrt
    (2 * ((Concentration.intervalVarianceProxy 0 1 : NNReal) : Real) *
      Real.log (5 / delta) / T)

/-- Unclipped maximum of the four sparse-loss exploration scales. -/
noncomputable def sparseLossPredictableVarianceRawExplorationRate
    (K S T delta : Real) : Real :=
  max (sparseLossPredictableVarianceArmExplorationScale K S T)
    (max (sparseLossPredictableVarianceMarkovExplorationScale K S T delta)
      (max (sparseLossPredictableVarianceConfidenceExplorationScale K T delta)
        (sparseLossPredictableVarianceRealizedExplorationScale T delta)))

/-- Explicit exploration schedule clipped into the Hedge stability regime. -/
noncomputable def sparseLossPredictableVarianceClippedExplorationRate
    (K S T delta : Real) : Real :=
  min (1 / 2)
    (sparseLossPredictableVarianceRawExplorationRate K S T delta)

/-- A nonnegative fifth-root scale is at most one half when its numerator is
at most one thirty-second of its positive denominator. -/
theorem rpow_inv_five_le_half_of_thirtytwo_mul_le
    (numerator denominator : Real) (hnumerator : 0 <= numerator)
    (hdenominator : 0 < denominator)
    (hlarge : 32 * numerator <= denominator) :
    (numerator / denominator) ^ (5 : Real)⁻¹ <= 1 / 2 := by
  have hfifth :
      ((numerator / denominator) ^ (5 : Real)⁻¹) ^ (5 : Nat) =
        numerator / denominator := by
    convert Real.rpow_inv_natCast_pow (n := 5)
      (div_nonneg hnumerator hdenominator.le) (by norm_num) using 1
  apply le_of_pow_le_pow_left₀ (n := 5) (by positivity) (by norm_num)
  rw [hfifth]
  norm_num
  rw [div_le_iff₀ hdenominator]
  nlinarith

/-- If a fifth-root scale is below `gamma`, its numerator satisfies the
corresponding fifth-power dominance contract. -/
theorem numerator_le_pow_five_mul_of_rpow_inv_five_le
    (numerator denominator gamma : Real) (hnumerator : 0 <= numerator)
    (hdenominator : 0 < denominator)
    (hroot : (numerator / denominator) ^ (5 : Real)⁻¹ <= gamma) :
    numerator <= gamma ^ 5 * denominator := by
  have hroot_nonneg :
      0 <= (numerator / denominator) ^ (5 : Real)⁻¹ :=
    Real.rpow_nonneg (div_nonneg hnumerator hdenominator.le) _
  have hfifth :
      ((numerator / denominator) ^ (5 : Real)⁻¹) ^ (5 : Nat) =
        numerator / denominator := by
    convert Real.rpow_inv_natCast_pow (n := 5)
      (div_nonneg hnumerator hdenominator.le) (by norm_num) using 1
  have hpow := pow_le_pow_left₀ hroot_nonneg hroot 5
  rw [hfifth] at hpow
  calc
    numerator = (numerator / denominator) * denominator := by
      field_simp [ne_of_gt hdenominator]
    _ <= gamma ^ 5 * denominator :=
      mul_le_mul_of_nonneg_right hpow hdenominator.le

theorem sparseLossPredictableVarianceClippedExplorationRate_le_half
    (K S T delta : Real) :
    sparseLossPredictableVarianceClippedExplorationRate K S T delta <=
      1 / 2 :=
  min_le_left _ _

theorem sparseLossPredictableVarianceClippedExplorationRate_eq_raw
    (K S T delta : Real)
    (hraw :
      sparseLossPredictableVarianceRawExplorationRate K S T delta <= 1 / 2) :
    sparseLossPredictableVarianceClippedExplorationRate K S T delta =
      sparseLossPredictableVarianceRawExplorationRate K S T delta :=
  min_eq_right hraw

theorem sparseLossPredictableVarianceRawExplorationRate_pos
    (K S T delta : Real) (hK_one : 1 < K) (hS : 0 < S) (hT : 0 < T) :
    0 < sparseLossPredictableVarianceRawExplorationRate K S T delta := by
  have hbase : 0 < S * Real.log K / T :=
    div_pos (mul_pos hS (Real.log_pos hK_one)) hT
  have hscale :
      0 < sparseLossPredictableVarianceArmExplorationScale K S T :=
    Real.sqrt_pos.2 hbase
  exact hscale.trans_le (le_max_left _ _)

theorem sparseLossPredictableVarianceClippedExplorationRate_pos
    (K S T delta : Real) (hK_one : 1 < K) (hS : 0 < S) (hT : 0 < T) :
    0 < sparseLossPredictableVarianceClippedExplorationRate K S T delta := by
  apply lt_min
  · norm_num
  · exact sparseLossPredictableVarianceRawExplorationRate_pos
      K S T delta hK_one hS hT

/-- Four transparent horizon contracts ensure every raw schedule component is
at most one half, so clipping is inactive. -/
theorem sparseLossPredictableVarianceRawExplorationRate_le_half_of_horizon_contracts
    (K S T delta : Real) (hK_one : 1 < K) (hS : 0 < S) (hT : 0 < T)
    (hdelta : 0 < delta) (hdelta_le_one : delta <= 1)
    (hlarge_arm : 4 * (S * Real.log K) <= T)
    (hlarge_mixed :
      32 * (5 * K * S * Real.log K ^ 2 * Real.log (5 / delta)) <=
        delta * T ^ 3)
    (hlarge_confidence : 8 * (K * Real.log (5 / delta)) <= T)
    (hlarge_realized :
      8 * ((Concentration.intervalVarianceProxy 0 1 : NNReal) : Real) *
          Real.log (5 / delta) <= T) :
    sparseLossPredictableVarianceRawExplorationRate K S T delta <=
      1 / 2 := by
  have hK : 0 < K := lt_trans zero_lt_one hK_one
  have hlogK : 0 <= Real.log K := (Real.log_pos hK_one).le
  have hone_lt_five_div : 1 < 5 / delta := by
    rw [lt_div_iff₀ hdelta]
    nlinarith
  have hlog : 0 <= Real.log (5 / delta) :=
    (Real.log_pos hone_lt_five_div).le
  have hmixed_nonneg :
      0 <= 5 * K * S * Real.log K ^ 2 * Real.log (5 / delta) := by
    positivity
  have hdenominator : 0 < delta * T ^ 3 := by positivity
  rw [sparseLossPredictableVarianceRawExplorationRate]
  apply max_le
  · exact sqrt_div_le_half_of_four_mul_le
      (S * Real.log K) T hT hlarge_arm
  apply max_le
  · exact rpow_inv_five_le_half_of_thirtytwo_mul_le
      (5 * K * S * Real.log K ^ 2 * Real.log (5 / delta))
      (delta * T ^ 3) hmixed_nonneg hdenominator hlarge_mixed
  apply max_le
  · exact rpow_inv_three_le_half_of_eight_mul_le
      (K * Real.log (5 / delta)) T (mul_nonneg hK.le hlog) hT
        hlarge_confidence
  · apply sqrt_div_le_half_of_four_mul_le
    · exact hT
    · nlinarith [hlarge_realized]

/-- The clipped maximum satisfies exactly the four contracts consumed by the
gamma-characterized sparse-loss theorem. -/
theorem sparseLossPredictableVarianceClippedExplorationRate_contracts
    (K S T delta : Real) (hK_one : 1 < K) (hS : 0 < S) (hT : 0 < T)
    (hdelta : 0 < delta) (hdelta_le_one : delta <= 1)
    (hlarge_arm : 4 * (S * Real.log K) <= T)
    (hlarge_mixed :
      32 * (5 * K * S * Real.log K ^ 2 * Real.log (5 / delta)) <=
        delta * T ^ 3)
    (hlarge_confidence : 8 * (K * Real.log (5 / delta)) <= T)
    (hlarge_realized :
      8 * ((Concentration.intervalVarianceProxy 0 1 : NNReal) : Real) *
          Real.log (5 / delta) <= T) :
    let gamma :=
      sparseLossPredictableVarianceClippedExplorationRate K S T delta
    0 < gamma ∧ gamma <= 1 / 2 ∧
      S * Real.log K <= gamma ^ 2 * T ∧
      5 * K * S * Real.log K ^ 2 * Real.log (5 / delta) <=
        gamma ^ 5 * delta * T ^ 3 ∧
      K * Real.log (5 / delta) <= gamma ^ 3 * T ∧
      2 * ((Concentration.intervalVarianceProxy 0 1 : NNReal) : Real) *
          Real.log (5 / delta) <= gamma ^ 2 * T := by
  dsimp only
  let variance : Real :=
    ((Concentration.intervalVarianceProxy 0 1 : NNReal) : Real)
  let numerator : Real :=
    5 * K * S * Real.log K ^ 2 * Real.log (5 / delta)
  let denominator : Real := delta * T ^ 3
  have hK : 0 < K := lt_trans zero_lt_one hK_one
  have hlogK : 0 <= Real.log K := (Real.log_pos hK_one).le
  have hone_lt_five_div : 1 < 5 / delta := by
    rw [lt_div_iff₀ hdelta]
    nlinarith
  have hlog : 0 <= Real.log (5 / delta) :=
    (Real.log_pos hone_lt_five_div).le
  have hvariance : 0 <= variance := NNReal.coe_nonneg _
  have hnumerator : 0 <= numerator := by
    dsimp [numerator]
    positivity
  have hdenominator : 0 < denominator := by
    dsimp [denominator]
    positivity
  have hraw :=
    sparseLossPredictableVarianceRawExplorationRate_le_half_of_horizon_contracts
      K S T delta hK_one hS hT hdelta hdelta_le_one hlarge_arm hlarge_mixed
        hlarge_confidence hlarge_realized
  have hclip :
      sparseLossPredictableVarianceClippedExplorationRate K S T delta =
        sparseLossPredictableVarianceRawExplorationRate K S T delta :=
    sparseLossPredictableVarianceClippedExplorationRate_eq_raw
      K S T delta hraw
  have harm_component :
      sparseLossPredictableVarianceArmExplorationScale K S T <=
        sparseLossPredictableVarianceClippedExplorationRate K S T delta := by
    rw [hclip, sparseLossPredictableVarianceRawExplorationRate]
    exact le_max_left _ _
  have hmixed_component :
      sparseLossPredictableVarianceMarkovExplorationScale K S T delta <=
        sparseLossPredictableVarianceClippedExplorationRate K S T delta := by
    rw [hclip, sparseLossPredictableVarianceRawExplorationRate]
    exact le_max_of_le_right (le_max_left _ _)
  have hconfidence_component :
      sparseLossPredictableVarianceConfidenceExplorationScale K T delta <=
        sparseLossPredictableVarianceClippedExplorationRate K S T delta := by
    rw [hclip, sparseLossPredictableVarianceRawExplorationRate]
    exact le_max_of_le_right (le_max_of_le_right (le_max_left _ _))
  have hrealized_component :
      sparseLossPredictableVarianceRealizedExplorationScale T delta <=
        sparseLossPredictableVarianceClippedExplorationRate K S T delta := by
    rw [hclip, sparseLossPredictableVarianceRawExplorationRate]
    exact le_max_of_le_right (le_max_of_le_right (le_max_right _ _))
  refine ⟨
    sparseLossPredictableVarianceClippedExplorationRate_pos
      K S T delta hK_one hS hT,
    sparseLossPredictableVarianceClippedExplorationRate_le_half K S T delta,
    ?_, ?_, ?_, ?_⟩
  · exact numerator_le_sq_mul_of_sqrt_div_le
      (S * Real.log K) T
        (sparseLossPredictableVarianceClippedExplorationRate K S T delta)
        (mul_nonneg hS.le hlogK) hT (by
          simpa [sparseLossPredictableVarianceArmExplorationScale] using
            harm_component)
  · have hroot :
        (numerator / denominator) ^ (5 : Real)⁻¹ <=
          sparseLossPredictableVarianceClippedExplorationRate K S T delta := by
      simpa [sparseLossPredictableVarianceMarkovExplorationScale,
        numerator, denominator] using hmixed_component
    have hpower :=
      numerator_le_pow_five_mul_of_rpow_inv_five_le
        numerator denominator
          (sparseLossPredictableVarianceClippedExplorationRate K S T delta)
        hnumerator hdenominator hroot
    simpa [numerator, denominator, mul_assoc] using hpower
  · exact numerator_le_cube_mul_of_rpow_inv_three_le
      (K * Real.log (5 / delta)) T
        (sparseLossPredictableVarianceClippedExplorationRate K S T delta)
        (mul_nonneg hK.le hlog) hT (by
          simpa [sparseLossPredictableVarianceConfidenceExplorationScale] using
            hconfidence_component)
  · exact numerator_le_sq_mul_of_sqrt_div_le
      (2 * variance * Real.log (5 / delta)) T
        (sparseLossPredictableVarianceClippedExplorationRate K S T delta)
        (mul_nonneg (mul_nonneg (by norm_num) hvariance) hlog) hT (by
          simpa [sparseLossPredictableVarianceRealizedExplorationScale,
            variance] using hrealized_component)

/-- Fully explicit generated sparse-loss realized-regret tail for the clipped
maximum of the four exploration scales. -/
theorem sampledPredictable_explicitSparseLossPredictableVarianceRealizedMarkovRegret_tail
    {Env : Type u} {Action : Type v}
    [MeasurableSpace Env] [StandardBorelSpace Env] [Nonempty Env]
    [MeasurableSpace Action] [MeasurableSingletonClass Action]
    [StandardBorelSpace Action] [Nonempty Action] [DecidableEq Action]
    (prior : Measure Env) [IsProbabilityMeasure prior]
    (arms : Finset Action) (harms : arms.Nonempty)
    (hcard_two : 2 <= arms.card)
    (loss : PredictableLossVector Env Action)
    (comparator : Action) (hcomparator : comparator ∈ arms)
    (horizon sparsity : Nat) (hhorizon : 0 < horizon)
    (hsparsity : 0 < sparsity)
    (delta : Real) (hdelta : 0 < delta) (hdelta_le_one : delta <= 1)
    (hlarge_arm :
      4 * ((sparsity : Real) * Real.log (arms.card : Real)) <=
        (horizon : Real))
    (hlarge_mixed :
      32 * (5 * (arms.card : Real) * (sparsity : Real) *
          Real.log (arms.card : Real) ^ 2 * Real.log (5 / delta)) <=
        delta * (horizon : Real) ^ 3)
    (hlarge_confidence :
      8 * ((arms.card : Real) * Real.log (5 / delta)) <=
        (horizon : Real))
    (hlarge_realized :
      8 * ((Concentration.intervalVarianceProxy 0 1 : NNReal) : Real) *
          Real.log (5 / delta) <= (horizon : Real))
    (hsparse : ∀ sample t, t < horizon →
      (sampledPredictableLossSupport arms loss t sample).card <= sparsity) :
    let gamma := sparseLossPredictableVarianceClippedExplorationRate
      (arms.card : Real) (sparsity : Real) (horizon : Real) delta
    let eta := sparseLossPredictableVarianceHighProbabilityLearningRate
      arms gamma horizon sparsity delta
    let mu := prior ⊗ₘ sampledImportanceWeightedTrajectoryKernel arms harms
      eta gamma
        (sparseLossPredictableVarianceClippedExplorationRate_pos
          (arms.card : Real) (sparsity : Real) (horizon : Real) delta
          (by exact_mod_cast hcard_two)
          (by exact_mod_cast hsparsity)
          (by exact_mod_cast hhorizon)).le
        (by
          exact
            (sparseLossPredictableVarianceClippedExplorationRate_le_half
              (arms.card : Real) (sparsity : Real) (horizon : Real)
                delta).trans (by norm_num))
        loss.environment
    mu {sample |
        sparseLossPredictableVarianceRealizedMarkovExplicitThreshold
            arms gamma horizon sparsity delta <=
          (Finset.range horizon).sum (fun t =>
              sampledTrajectoryRealizedLossAt t sample) -
            (Finset.range horizon).sum (fun t =>
              predictableLossAt loss t sample comparator)} <=
      ENNReal.ofReal delta := by
  dsimp only
  have hK_one : 1 < (arms.card : Real) := by exact_mod_cast hcard_two
  have hS : 0 < (sparsity : Real) := by exact_mod_cast hsparsity
  have hT : 0 < (horizon : Real) := by exact_mod_cast hhorizon
  have hcontracts :=
    sparseLossPredictableVarianceClippedExplorationRate_contracts
      (arms.card : Real) (sparsity : Real) (horizon : Real) delta
        hK_one hS hT hdelta hdelta_le_one hlarge_arm hlarge_mixed
        hlarge_confidence hlarge_realized
  dsimp only at hcontracts
  rcases hcontracts with
    ⟨hgamma_pos, hgamma_le_half, hbase, hmixed, hconfidence, hrealized⟩
  exact
    sampledPredictable_gammaCharacterizedSparseLossPredictableVarianceRealizedMarkovRegret_tail
      prior arms harms hcard_two
        (sparseLossPredictableVarianceClippedExplorationRate
          (arms.card : Real) (sparsity : Real) (horizon : Real) delta)
        hgamma_pos hgamma_le_half loss comparator hcomparator horizon sparsity
        hhorizon hsparsity delta hdelta hdelta_le_one hbase hmixed hconfidence
        hrealized hsparse

end BanditRLProof.Exp3
