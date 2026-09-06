import BanditRLProof.Exp3MixedSquarePredictableVarianceSparseLossRealizedMarkovProbabilisticSparsityTuning
import BanditRLProof.Exp3MixedSquarePredictableVarianceSparseLossRealizedMarkovExplicitTuning

/-!
# Explicit exploration tuning under probabilistic sparse losses

This module closes the exploration-rate leaf for the generated realized
predictable-variance EXP3 route whose support-sparsity condition may fail with
positive probability. The global `K * T` loss-mass envelope makes the Markov
component

`(5 K^2 (log K)^2 log(5 / delta) / (delta T^3))^(1/5)`.

Together with the sparse base, Bernstein-confidence, and realized-deviation
components, a clipped maximum supplies every algebraic premise needed to
reduce the eta-tuned threshold to `14 * gamma * T`. The final theorem keeps the
exact sparsity-failure residual and exposes the practical `delta + epsilon`
endpoint under the same internally tuned generated measure.

This is still a global-envelope Markov theorem. It is not a pathwise-sparsity,
best-arm first-order, Freedman, anytime, or ideal EXP3.P result.
-/

namespace BanditRLProof.Exp3

open MeasureTheory ProbabilityTheory

universe u v

/-- Closed form of the global-envelope Markov variance threshold. -/
theorem probabilisticSparseLossPredictableVarianceBudget_eq
    {Action : Type v} [DecidableEq Action]
    (arms : Finset Action) (hcard_two : 2 <= arms.card)
    (gamma : Real) (hgamma_pos : 0 < gamma)
    (horizon : Nat) (delta : Real) (hdelta : 0 < delta) :
    probabilisticSparseLossPredictableVarianceBudget
        arms gamma horizon delta =
      5 * (arms.card : Real) ^ 2 * (horizon : Real) /
        (gamma * delta) := by
  have hK : 0 < (arms.card : Real) := by positivity
  unfold probabilisticSparseLossPredictableVarianceBudget
    sampledPredictableGlobalVarianceMeanBudget
  field_simp [ne_of_gt hK, ne_of_gt hgamma_pos, ne_of_gt hdelta]

/-- Under the sparse-base, global-envelope fifth-power, and cubic confidence
contracts, the log-weighted mixed-square radius is at most
`3 * gamma^2 * T^2`. -/
theorem log_mul_probabilisticSparseLossPredictableVarianceRadius_le_three_mul_sq_mul_horizon_sq
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
      5 * (arms.card : Real) ^ 2 *
            Real.log (arms.card : Real) ^ 2 * Real.log (5 / delta) <=
        gamma ^ 5 * delta * (horizon : Real) ^ 3)
    (hconfidence :
      (arms.card : Real) * Real.log (5 / delta) <=
        gamma ^ 3 * (horizon : Real)) :
    Real.log (arms.card : Real) *
        sampledMixedSquaredPredictableVarianceRadius arms gamma
          (probabilisticSparseLossPredictableVarianceBudget
            arms gamma horizon delta)
          (delta / 5) <=
      3 * gamma ^ 2 * (horizon : Real) ^ 2 := by
  let K : Real := arms.card
  let S : Real := sparsity
  let T : Real := horizon
  let B : Real := Real.log (5 / delta)
  let variance :=
    probabilisticSparseLossPredictableVarianceBudget
      arms gamma horizon delta
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
      variance = 5 * K ^ 2 * T / (gamma * delta) := by
    dsimp [variance, K, T]
    exact probabilisticSparseLossPredictableVarianceBudget_eq
      arms hcard_two gamma hgamma_pos horizon delta hdelta
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
      5 * K ^ 2 * Real.log K ^ 2 * B <=
        gamma ^ 5 * delta * T ^ 3 := by
    simpa [K, T, B] using hmixed
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

/-- The sparse base and global-envelope predictable-variance radius make the
learning-rate-balanced square root at most `2 * gamma * T`. -/
theorem probabilisticSparseLossPredictableVarianceBalancedSqrt_le_two_mul_gamma_mul_horizon
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
      5 * (arms.card : Real) ^ 2 *
            Real.log (arms.card : Real) ^ 2 * Real.log (5 / delta) <=
        gamma ^ 5 * delta * (horizon : Real) ^ 3)
    (hconfidence :
      (arms.card : Real) * Real.log (5 / delta) <=
        gamma ^ 3 * (horizon : Real)) :
    Real.sqrt
        (Real.log (arms.card : Real) *
          probabilisticSparseLossPredictableVarianceHighProbabilityScale
            arms gamma horizon sparsity delta) <=
      2 * gamma * (horizon : Real) := by
  let K : Real := arms.card
  let S : Real := sparsity
  let T : Real := horizon
  let radius :=
    sampledMixedSquaredPredictableVarianceRadius arms gamma
      (probabilisticSparseLossPredictableVarianceBudget
        arms gamma horizon delta)
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
      log_mul_probabilisticSparseLossPredictableVarianceRadius_le_three_mul_sq_mul_horizon_sq
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
  · dsimp [probabilisticSparseLossPredictableVarianceHighProbabilityScale,
      K, S, T, radius] at *
    nlinarith

/-- Explicit probabilistic-sparsity realized-regret threshold after tuning
both eta and gamma. -/
noncomputable def probabilisticSparseLossPredictableVarianceRealizedMarkovExplicitThreshold
    {Action : Type v} (_arms : Finset Action) (gamma : Real)
    (horizon _sparsity : Nat) (_delta : Real) : Real :=
  14 * gamma * (horizon : Real)

/-- The four algebraic exploration contracts reduce the probabilistic-
sparsity eta-tuned threshold to `14 * gamma * T`. -/
theorem probabilisticSparseLossPredictableVarianceRealizedMarkovTunedThreshold_le_explicitThreshold
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
      5 * (arms.card : Real) ^ 2 *
            Real.log (arms.card : Real) ^ 2 * Real.log (5 / delta) <=
        gamma ^ 5 * delta * (horizon : Real) ^ 3)
    (hconfidence :
      (arms.card : Real) * Real.log (5 / delta) <=
        gamma ^ 3 * (horizon : Real))
    (hrealized :
      2 * ((Concentration.intervalVarianceProxy 0 1 : NNReal) : Real) *
          Real.log (5 / delta) <=
        gamma ^ 2 * (horizon : Real)) :
    probabilisticSparseLossPredictableVarianceRealizedMarkovTunedThreshold
        arms gamma horizon sparsity delta <=
      probabilisticSparseLossPredictableVarianceRealizedMarkovExplicitThreshold
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
            probabilisticSparseLossPredictableVarianceHighProbabilityScale
              arms gamma horizon sparsity delta) <=
        2 * gamma * T := by
    simpa [K, T] using
      probabilisticSparseLossPredictableVarianceBalancedSqrt_le_two_mul_gamma_mul_horizon
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
  dsimp [
    probabilisticSparseLossPredictableVarianceRealizedMarkovTunedThreshold,
    probabilisticSparseLossPredictableVarianceRealizedMarkovExplicitThreshold,
    sampledPurePredictableMinusObservedBernsteinConfidenceRadius,
    sampledComparatorEstimatorBernsteinConfidenceRadius,
    sampledPredictableRealizedDeviationConfidenceRadius]
  rw [hmax_fifth, hlog_fifth]
  change
    3 * Real.sqrt
          (Real.log K *
            probabilisticSparseLossPredictableVarianceHighProbabilityScale
              arms gamma horizon sparsity delta) +
        gamma * T +
        (2 * Real.sqrt (T * budget / (gamma / K)) +
          budget / (gamma / K)) +
        (2 * Real.sqrt (T * budget / (gamma / K)) +
          budget / (gamma / K)) +
        Real.sqrt (2 * (T * variance) * budget) <=
      14 * gamma * T
  linarith

/-- Generated probabilistic-sparsity regret under four algebraic exploration
contracts, retaining the exact sparsity-failure residual. -/
theorem sampledPredictable_gammaCharacterizedProbabilisticSparseLossPredictableVarianceRealizedMarkovRegret_tail
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
      5 * (arms.card : Real) ^ 2 *
            Real.log (arms.card : Real) ^ 2 * Real.log (5 / delta) <=
        gamma ^ 5 * delta * (horizon : Real) ^ 3)
    (hconfidence :
      (arms.card : Real) * Real.log (5 / delta) <=
        gamma ^ 3 * (horizon : Real))
    (hrealized :
      2 * ((Concentration.intervalVarianceProxy 0 1 : NNReal) : Real) *
          Real.log (5 / delta) <=
        gamma ^ 2 * (horizon : Real)) :
    let eta :=
      probabilisticSparseLossPredictableVarianceHighProbabilityLearningRate
        arms gamma horizon sparsity delta
    let mu := prior ⊗ₘ sampledImportanceWeightedTrajectoryKernel arms harms
      eta gamma hgamma_pos.le (by linarith : gamma <= 1) loss.environment
    mu {sample |
        probabilisticSparseLossPredictableVarianceRealizedMarkovExplicitThreshold
            arms gamma horizon sparsity delta <=
          (Finset.range horizon).sum (fun t =>
              sampledTrajectoryRealizedLossAt t sample) -
            (Finset.range horizon).sum (fun t =>
              predictableLossAt loss t sample comparator)} <=
      ENNReal.ofReal delta +
        mu (sampledPredictableSparsityFailure arms loss horizon sparsity) := by
  dsimp only
  have hgamma_lt_one : gamma < 1 := by linarith
  have hthreshold :=
    probabilisticSparseLossPredictableVarianceRealizedMarkovTunedThreshold_le_explicitThreshold
      arms hcard_two horizon sparsity hhorizon hsparsity gamma delta
        hgamma_pos hgamma_le_half hdelta hdelta_le_one hbase hmixed
        hconfidence hrealized
  have htail :=
    sampledPredictable_tunedProbabilisticSparseLossPredictableVarianceRealizedMarkovRegret_tail
      prior arms harms hcard_two gamma hgamma_pos hgamma_le_half loss comparator
        hcomparator horizon sparsity hhorizon hsparsity delta hdelta
  dsimp only at htail ⊢
  calc
    (prior ⊗ₘ sampledImportanceWeightedTrajectoryKernel arms harms
        (probabilisticSparseLossPredictableVarianceHighProbabilityLearningRate
          arms gamma horizon sparsity delta)
        gamma hgamma_pos.le hgamma_lt_one.le loss.environment)
        {sample |
          probabilisticSparseLossPredictableVarianceRealizedMarkovExplicitThreshold
              arms gamma horizon sparsity delta <=
            (Finset.range horizon).sum (fun t =>
                sampledTrajectoryRealizedLossAt t sample) -
              (Finset.range horizon).sum (fun t =>
                predictableLossAt loss t sample comparator)} <=
      (prior ⊗ₘ sampledImportanceWeightedTrajectoryKernel arms harms
        (probabilisticSparseLossPredictableVarianceHighProbabilityLearningRate
          arms gamma horizon sparsity delta)
        gamma hgamma_pos.le hgamma_lt_one.le loss.environment)
        {sample |
          probabilisticSparseLossPredictableVarianceRealizedMarkovTunedThreshold
              arms gamma horizon sparsity delta <=
            (Finset.range horizon).sum (fun t =>
                sampledTrajectoryRealizedLossAt t sample) -
              (Finset.range horizon).sum (fun t =>
                predictableLossAt loss t sample comparator)} := by
        apply measure_mono
        intro sample hsample
        exact hthreshold.trans hsample
    _ <= ENNReal.ofReal delta +
        (prior ⊗ₘ sampledImportanceWeightedTrajectoryKernel arms harms
          (probabilisticSparseLossPredictableVarianceHighProbabilityLearningRate
            arms gamma horizon sparsity delta)
          gamma hgamma_pos.le hgamma_lt_one.le loss.environment)
          (sampledPredictableSparsityFailure arms loss horizon sparsity) := htail

/-- Practical gamma-characterized theorem under an exact generated-measure
bound on the sparsity-failure event. -/
theorem sampledPredictable_gammaCharacterizedProbabilisticSparseLossPredictableVarianceRealizedMarkovRegret_tail_of_sparsityFailure_le
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
    (delta epsilon : Real) (hdelta : 0 < delta)
    (hdelta_le_one : delta <= 1)
    (hbase :
      (sparsity : Real) * Real.log (arms.card : Real) <=
        gamma ^ 2 * (horizon : Real))
    (hmixed :
      5 * (arms.card : Real) ^ 2 *
            Real.log (arms.card : Real) ^ 2 * Real.log (5 / delta) <=
        gamma ^ 5 * delta * (horizon : Real) ^ 3)
    (hconfidence :
      (arms.card : Real) * Real.log (5 / delta) <=
        gamma ^ 3 * (horizon : Real))
    (hrealized :
      2 * ((Concentration.intervalVarianceProxy 0 1 : NNReal) : Real) *
          Real.log (5 / delta) <=
        gamma ^ 2 * (horizon : Real)) :
    let eta :=
      probabilisticSparseLossPredictableVarianceHighProbabilityLearningRate
        arms gamma horizon sparsity delta
    let mu := prior ⊗ₘ sampledImportanceWeightedTrajectoryKernel arms harms
      eta gamma hgamma_pos.le (by linarith : gamma <= 1) loss.environment
    mu (sampledPredictableSparsityFailure arms loss horizon sparsity) <=
        ENNReal.ofReal epsilon ->
      mu {sample |
          probabilisticSparseLossPredictableVarianceRealizedMarkovExplicitThreshold
              arms gamma horizon sparsity delta <=
            (Finset.range horizon).sum (fun t =>
                sampledTrajectoryRealizedLossAt t sample) -
              (Finset.range horizon).sum (fun t =>
                predictableLossAt loss t sample comparator)} <=
        ENNReal.ofReal delta + ENNReal.ofReal epsilon := by
  dsimp only
  intro hfailure
  have htail :=
    sampledPredictable_gammaCharacterizedProbabilisticSparseLossPredictableVarianceRealizedMarkovRegret_tail
      prior arms harms hcard_two gamma hgamma_pos hgamma_le_half loss comparator
        hcomparator horizon sparsity hhorizon hsparsity delta hdelta
        hdelta_le_one hbase hmixed hconfidence hrealized
  dsimp only at htail
  exact htail.trans (add_le_add le_rfl hfailure)

/-- Fifth-root component forced by the global `K * T` Markov envelope. -/
noncomputable def probabilisticSparseLossPredictableVarianceMarkovExplorationScale
    (K T delta : Real) : Real :=
  (5 * K ^ 2 * Real.log K ^ 2 * Real.log (5 / delta) /
      (delta * T ^ 3)) ^ (5 : Real)⁻¹

/-- Unclipped maximum of the sparse base, global Markov, Bernstein, and
realized-deviation exploration scales. -/
noncomputable def probabilisticSparseLossPredictableVarianceRawExplorationRate
    (K S T delta : Real) : Real :=
  max (sparseLossPredictableVarianceArmExplorationScale K S T)
    (max
      (probabilisticSparseLossPredictableVarianceMarkovExplorationScale
        K T delta)
      (max
        (sparseLossPredictableVarianceConfidenceExplorationScale K T delta)
        (sparseLossPredictableVarianceRealizedExplorationScale T delta)))

/-- Explicit probabilistic-sparsity exploration schedule clipped into the
Hedge stability regime. -/
noncomputable def probabilisticSparseLossPredictableVarianceClippedExplorationRate
    (K S T delta : Real) : Real :=
  min (1 / 2)
    (probabilisticSparseLossPredictableVarianceRawExplorationRate
      K S T delta)

theorem probabilisticSparseLossPredictableVarianceClippedExplorationRate_le_half
    (K S T delta : Real) :
    probabilisticSparseLossPredictableVarianceClippedExplorationRate
        K S T delta <=
      1 / 2 :=
  min_le_left _ _

theorem probabilisticSparseLossPredictableVarianceClippedExplorationRate_eq_raw
    (K S T delta : Real)
    (hraw :
      probabilisticSparseLossPredictableVarianceRawExplorationRate
          K S T delta <=
        1 / 2) :
    probabilisticSparseLossPredictableVarianceClippedExplorationRate
        K S T delta =
      probabilisticSparseLossPredictableVarianceRawExplorationRate
        K S T delta :=
  min_eq_right hraw

theorem probabilisticSparseLossPredictableVarianceRawExplorationRate_pos
    (K S T delta : Real) (hK_one : 1 < K) (hS : 0 < S) (hT : 0 < T) :
    0 <
      probabilisticSparseLossPredictableVarianceRawExplorationRate
        K S T delta := by
  have hbase : 0 < S * Real.log K / T :=
    div_pos (mul_pos hS (Real.log_pos hK_one)) hT
  have hscale :
      0 < sparseLossPredictableVarianceArmExplorationScale K S T :=
    Real.sqrt_pos.2 hbase
  exact hscale.trans_le (le_max_left _ _)

theorem probabilisticSparseLossPredictableVarianceClippedExplorationRate_pos
    (K S T delta : Real) (hK_one : 1 < K) (hS : 0 < S) (hT : 0 < T) :
    0 <
      probabilisticSparseLossPredictableVarianceClippedExplorationRate
        K S T delta := by
  apply lt_min
  · norm_num
  · exact
      probabilisticSparseLossPredictableVarianceRawExplorationRate_pos
        K S T delta hK_one hS hT

/-- Transparent horizon contracts ensure every raw schedule component is at
most one half, so clipping is inactive. -/
theorem probabilisticSparseLossPredictableVarianceRawExplorationRate_le_half_of_horizon_contracts
    (K S T delta : Real) (hK_one : 1 < K) (hT : 0 < T)
    (hdelta : 0 < delta) (hdelta_le_one : delta <= 1)
    (hlarge_arm : 4 * (S * Real.log K) <= T)
    (hlarge_mixed :
      32 * (5 * K ^ 2 * Real.log K ^ 2 * Real.log (5 / delta)) <=
        delta * T ^ 3)
    (hlarge_confidence : 8 * (K * Real.log (5 / delta)) <= T)
    (hlarge_realized :
      8 * ((Concentration.intervalVarianceProxy 0 1 : NNReal) : Real) *
          Real.log (5 / delta) <= T) :
    probabilisticSparseLossPredictableVarianceRawExplorationRate
        K S T delta <=
      1 / 2 := by
  have hK : 0 < K := lt_trans zero_lt_one hK_one
  have hlogK : 0 <= Real.log K := (Real.log_pos hK_one).le
  have hone_lt_five_div : 1 < 5 / delta := by
    rw [lt_div_iff₀ hdelta]
    nlinarith
  have hlog : 0 <= Real.log (5 / delta) :=
    (Real.log_pos hone_lt_five_div).le
  have hmixed_nonneg :
      0 <= 5 * K ^ 2 * Real.log K ^ 2 * Real.log (5 / delta) := by
    positivity
  have hdenominator : 0 < delta * T ^ 3 := by positivity
  rw [probabilisticSparseLossPredictableVarianceRawExplorationRate]
  apply max_le
  · exact sqrt_div_le_half_of_four_mul_le
      (S * Real.log K) T hT hlarge_arm
  apply max_le
  · exact rpow_inv_five_le_half_of_thirtytwo_mul_le
      (5 * K ^ 2 * Real.log K ^ 2 * Real.log (5 / delta))
      (delta * T ^ 3) hmixed_nonneg hdenominator hlarge_mixed
  apply max_le
  · exact rpow_inv_three_le_half_of_eight_mul_le
      (K * Real.log (5 / delta)) T (mul_nonneg hK.le hlog) hT
        hlarge_confidence
  · apply sqrt_div_le_half_of_four_mul_le
    · exact hT
    · nlinarith [hlarge_realized]

/-- The clipped maximum supplies exactly the four contracts consumed by the
gamma-characterized probabilistic-sparsity theorem. -/
theorem probabilisticSparseLossPredictableVarianceClippedExplorationRate_contracts
    (K S T delta : Real) (hK_one : 1 < K) (hS : 0 < S) (hT : 0 < T)
    (hdelta : 0 < delta) (hdelta_le_one : delta <= 1)
    (hlarge_arm : 4 * (S * Real.log K) <= T)
    (hlarge_mixed :
      32 * (5 * K ^ 2 * Real.log K ^ 2 * Real.log (5 / delta)) <=
        delta * T ^ 3)
    (hlarge_confidence : 8 * (K * Real.log (5 / delta)) <= T)
    (hlarge_realized :
      8 * ((Concentration.intervalVarianceProxy 0 1 : NNReal) : Real) *
          Real.log (5 / delta) <= T) :
    let gamma :=
      probabilisticSparseLossPredictableVarianceClippedExplorationRate
        K S T delta
    0 < gamma ∧
      gamma <= 1 / 2 ∧
      S * Real.log K <= gamma ^ 2 * T ∧
      5 * K ^ 2 * Real.log K ^ 2 * Real.log (5 / delta) <=
        gamma ^ 5 * delta * T ^ 3 ∧
      K * Real.log (5 / delta) <= gamma ^ 3 * T ∧
      2 * ((Concentration.intervalVarianceProxy 0 1 : NNReal) : Real) *
          Real.log (5 / delta) <= gamma ^ 2 * T := by
  dsimp only
  let variance : Real :=
    ((Concentration.intervalVarianceProxy 0 1 : NNReal) : Real)
  let numerator : Real :=
    5 * K ^ 2 * Real.log K ^ 2 * Real.log (5 / delta)
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
    probabilisticSparseLossPredictableVarianceRawExplorationRate_le_half_of_horizon_contracts
      K S T delta hK_one hT hdelta hdelta_le_one hlarge_arm
        hlarge_mixed hlarge_confidence hlarge_realized
  have hclip :
      probabilisticSparseLossPredictableVarianceClippedExplorationRate
          K S T delta =
        probabilisticSparseLossPredictableVarianceRawExplorationRate
          K S T delta :=
    probabilisticSparseLossPredictableVarianceClippedExplorationRate_eq_raw
      K S T delta hraw
  have harm_component :
      sparseLossPredictableVarianceArmExplorationScale K S T <=
        probabilisticSparseLossPredictableVarianceClippedExplorationRate
          K S T delta := by
    rw [hclip,
      probabilisticSparseLossPredictableVarianceRawExplorationRate]
    exact le_max_left _ _
  have hmixed_component :
      probabilisticSparseLossPredictableVarianceMarkovExplorationScale
          K T delta <=
        probabilisticSparseLossPredictableVarianceClippedExplorationRate
          K S T delta := by
    rw [hclip,
      probabilisticSparseLossPredictableVarianceRawExplorationRate]
    exact le_max_of_le_right (le_max_left _ _)
  have hconfidence_component :
      sparseLossPredictableVarianceConfidenceExplorationScale K T delta <=
        probabilisticSparseLossPredictableVarianceClippedExplorationRate
          K S T delta := by
    rw [hclip,
      probabilisticSparseLossPredictableVarianceRawExplorationRate]
    exact le_max_of_le_right (le_max_of_le_right (le_max_left _ _))
  have hrealized_component :
      sparseLossPredictableVarianceRealizedExplorationScale T delta <=
        probabilisticSparseLossPredictableVarianceClippedExplorationRate
          K S T delta := by
    rw [hclip,
      probabilisticSparseLossPredictableVarianceRawExplorationRate]
    exact le_max_of_le_right (le_max_of_le_right (le_max_right _ _))
  refine ⟨
    probabilisticSparseLossPredictableVarianceClippedExplorationRate_pos
      K S T delta hK_one hS hT,
    probabilisticSparseLossPredictableVarianceClippedExplorationRate_le_half
      K S T delta,
    ?_, ?_, ?_, ?_⟩
  · exact numerator_le_sq_mul_of_sqrt_div_le
      (S * Real.log K) T
        (probabilisticSparseLossPredictableVarianceClippedExplorationRate
          K S T delta)
        (mul_nonneg hS.le hlogK) hT (by
          simpa [sparseLossPredictableVarianceArmExplorationScale] using
            harm_component)
  · have hroot :
        (numerator / denominator) ^ (5 : Real)⁻¹ <=
          probabilisticSparseLossPredictableVarianceClippedExplorationRate
            K S T delta := by
      simpa [
        probabilisticSparseLossPredictableVarianceMarkovExplorationScale,
        numerator, denominator] using hmixed_component
    have hpower :=
      numerator_le_pow_five_mul_of_rpow_inv_five_le
        numerator denominator
          (probabilisticSparseLossPredictableVarianceClippedExplorationRate
            K S T delta)
        hnumerator hdenominator hroot
    simpa [numerator, denominator, mul_assoc] using hpower
  · exact numerator_le_cube_mul_of_rpow_inv_three_le
      (K * Real.log (5 / delta)) T
        (probabilisticSparseLossPredictableVarianceClippedExplorationRate
          K S T delta)
        (mul_nonneg hK.le hlog) hT (by
          simpa [sparseLossPredictableVarianceConfidenceExplorationScale] using
            hconfidence_component)
  · exact numerator_le_sq_mul_of_sqrt_div_le
      (2 * variance * Real.log (5 / delta)) T
        (probabilisticSparseLossPredictableVarianceClippedExplorationRate
          K S T delta)
        (mul_nonneg (mul_nonneg (by norm_num) hvariance) hlog) hT (by
          simpa [sparseLossPredictableVarianceRealizedExplorationScale,
            variance] using hrealized_component)

/-- Fully explicit generated probabilistic-sparsity regret tail for the
clipped maximum schedule, retaining the exact failure residual. -/
theorem sampledPredictable_explicitProbabilisticSparseLossPredictableVarianceRealizedMarkovRegret_tail
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
      32 * (5 * (arms.card : Real) ^ 2 *
          Real.log (arms.card : Real) ^ 2 * Real.log (5 / delta)) <=
        delta * (horizon : Real) ^ 3)
    (hlarge_confidence :
      8 * ((arms.card : Real) * Real.log (5 / delta)) <=
        (horizon : Real))
    (hlarge_realized :
      8 * ((Concentration.intervalVarianceProxy 0 1 : NNReal) : Real) *
          Real.log (5 / delta) <= (horizon : Real)) :
    let gamma :=
      probabilisticSparseLossPredictableVarianceClippedExplorationRate
        (arms.card : Real) (sparsity : Real) (horizon : Real) delta
    let eta :=
      probabilisticSparseLossPredictableVarianceHighProbabilityLearningRate
        arms gamma horizon sparsity delta
    let mu := prior ⊗ₘ sampledImportanceWeightedTrajectoryKernel arms harms
      eta gamma
        (probabilisticSparseLossPredictableVarianceClippedExplorationRate_pos
          (arms.card : Real) (sparsity : Real) (horizon : Real) delta
          (by exact_mod_cast hcard_two)
          (by exact_mod_cast hsparsity)
          (by exact_mod_cast hhorizon)).le
        (by
          exact
            (probabilisticSparseLossPredictableVarianceClippedExplorationRate_le_half
              (arms.card : Real) (sparsity : Real) (horizon : Real)
                delta).trans (by norm_num))
        loss.environment
    mu {sample |
        probabilisticSparseLossPredictableVarianceRealizedMarkovExplicitThreshold
            arms gamma horizon sparsity delta <=
          (Finset.range horizon).sum (fun t =>
              sampledTrajectoryRealizedLossAt t sample) -
            (Finset.range horizon).sum (fun t =>
              predictableLossAt loss t sample comparator)} <=
      ENNReal.ofReal delta +
        mu (sampledPredictableSparsityFailure arms loss horizon sparsity) := by
  dsimp only
  have hK_one : 1 < (arms.card : Real) := by exact_mod_cast hcard_two
  have hS : 0 < (sparsity : Real) := by exact_mod_cast hsparsity
  have hT : 0 < (horizon : Real) := by exact_mod_cast hhorizon
  have hcontracts :=
    probabilisticSparseLossPredictableVarianceClippedExplorationRate_contracts
      (arms.card : Real) (sparsity : Real) (horizon : Real) delta
        hK_one hS hT hdelta hdelta_le_one hlarge_arm hlarge_mixed
        hlarge_confidence hlarge_realized
  dsimp only at hcontracts
  rcases hcontracts with
    ⟨hgamma_pos, hgamma_le_half, hbase, hmixed, hconfidence, hrealized⟩
  exact
    sampledPredictable_gammaCharacterizedProbabilisticSparseLossPredictableVarianceRealizedMarkovRegret_tail
      prior arms harms hcard_two
        (probabilisticSparseLossPredictableVarianceClippedExplorationRate
          (arms.card : Real) (sparsity : Real) (horizon : Real) delta)
        hgamma_pos hgamma_le_half loss comparator hcomparator horizon sparsity
        hhorizon hsparsity delta hdelta hdelta_le_one hbase hmixed hconfidence
        hrealized

/-- Fully explicit practical `delta + epsilon` theorem under an exact bound on
the sparsity-failure event for the internally eta/gamma-tuned measure. -/
theorem sampledPredictable_explicitProbabilisticSparseLossPredictableVarianceRealizedMarkovRegret_tail_of_sparsityFailure_le
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
    (delta epsilon : Real) (hdelta : 0 < delta)
    (hdelta_le_one : delta <= 1)
    (hlarge_arm :
      4 * ((sparsity : Real) * Real.log (arms.card : Real)) <=
        (horizon : Real))
    (hlarge_mixed :
      32 * (5 * (arms.card : Real) ^ 2 *
          Real.log (arms.card : Real) ^ 2 * Real.log (5 / delta)) <=
        delta * (horizon : Real) ^ 3)
    (hlarge_confidence :
      8 * ((arms.card : Real) * Real.log (5 / delta)) <=
        (horizon : Real))
    (hlarge_realized :
      8 * ((Concentration.intervalVarianceProxy 0 1 : NNReal) : Real) *
          Real.log (5 / delta) <= (horizon : Real)) :
    let gamma :=
      probabilisticSparseLossPredictableVarianceClippedExplorationRate
        (arms.card : Real) (sparsity : Real) (horizon : Real) delta
    let eta :=
      probabilisticSparseLossPredictableVarianceHighProbabilityLearningRate
        arms gamma horizon sparsity delta
    let mu := prior ⊗ₘ sampledImportanceWeightedTrajectoryKernel arms harms
      eta gamma
        (probabilisticSparseLossPredictableVarianceClippedExplorationRate_pos
          (arms.card : Real) (sparsity : Real) (horizon : Real) delta
          (by exact_mod_cast hcard_two)
          (by exact_mod_cast hsparsity)
          (by exact_mod_cast hhorizon)).le
        (by
          exact
            (probabilisticSparseLossPredictableVarianceClippedExplorationRate_le_half
              (arms.card : Real) (sparsity : Real) (horizon : Real)
                delta).trans (by norm_num))
        loss.environment
    mu (sampledPredictableSparsityFailure arms loss horizon sparsity) <=
        ENNReal.ofReal epsilon ->
      mu {sample |
          probabilisticSparseLossPredictableVarianceRealizedMarkovExplicitThreshold
              arms gamma horizon sparsity delta <=
            (Finset.range horizon).sum (fun t =>
                sampledTrajectoryRealizedLossAt t sample) -
              (Finset.range horizon).sum (fun t =>
                predictableLossAt loss t sample comparator)} <=
        ENNReal.ofReal delta + ENNReal.ofReal epsilon := by
  dsimp only
  intro hfailure
  have htail :=
    sampledPredictable_explicitProbabilisticSparseLossPredictableVarianceRealizedMarkovRegret_tail
      prior arms harms hcard_two loss comparator hcomparator horizon sparsity
        hhorizon hsparsity delta hdelta hdelta_le_one hlarge_arm hlarge_mixed
        hlarge_confidence hlarge_realized
  dsimp only at htail
  exact htail.trans (add_le_add le_rfl hfailure)

end BanditRLProof.Exp3
