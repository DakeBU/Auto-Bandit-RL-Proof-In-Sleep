import BanditRLProof.Exp3MixedSquarePredictableVarianceSparseLossRealizedPathwiseVarianceProbabilisticSparsityTuning
import BanditRLProof.Exp3MixedSquarePredictableVarianceSparseLossRealizedMarkovExplicitTuning

/-!
# Explicit exploration tuning for sparse pathwise variance

This module closes the exploration-rate route for the four-event generated
realized-regret theorem under probabilistic sparsity. On the good event, the
predictable-variance budget is

`(1 / (gamma / K)) * S * T`.

Consequently the mixed fifth-root scale is driven by

`K * S * (log K)^2 * log (4 / delta) / T^3`,

with neither the extra factor `K` nor the polynomial `1 / delta` from the old
global-envelope Markov route. The final generated theorem retains the exact
sparsity-failure residual, and its practical endpoint has failure budget
`delta + epsilon` under the same internally eta/gamma-tuned measure.

This is still an armwise aggregate sparse-loss theorem with bounded realized
deviation. It is not an all-horizon, best-arm first-order, Freedman, anytime,
or ideal EXP3.P result.
-/

namespace BanditRLProof.Exp3

open MeasureTheory ProbabilityTheory

universe u v

/-- Closed form of the deterministic sparse pathwise variance budget. -/
theorem sampledPredictableSparsePathwiseVarianceBudget_eq
    {Action : Type v} [DecidableEq Action]
    (arms : Finset Action) (hcard_two : 2 <= arms.card)
    (gamma : Real) (hgamma_pos : 0 < gamma)
    (horizon sparsity : Nat) :
    sampledPredictableSparsePathwiseVarianceBudget
        arms gamma horizon sparsity =
      (arms.card : Real) * (sparsity : Real) * (horizon : Real) / gamma := by
  have hK : 0 < (arms.card : Real) := by positivity
  unfold sampledPredictableSparsePathwiseVarianceBudget
  field_simp [ne_of_gt hK, ne_of_gt hgamma_pos]

/-- The sparse base, pathwise fifth-power, and cubic confidence contracts
bound the log-weighted predictable-variance radius by
`3 * gamma^2 * T^2`. -/
theorem log_mul_pathwiseVarianceProbabilisticSparseLossRadius_le_three_mul_sq_mul_horizon_sq
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
      (arms.card : Real) * (sparsity : Real) *
            Real.log (arms.card : Real) ^ 2 * Real.log (4 / delta) <=
        gamma ^ 5 * (horizon : Real) ^ 3)
    (hconfidence :
      (arms.card : Real) * Real.log (4 / delta) <=
        gamma ^ 3 * (horizon : Real)) :
    Real.log (arms.card : Real) *
        sampledMixedSquaredPredictableVarianceRadius arms gamma
          (sampledPredictableSparsePathwiseVarianceBudget
            arms gamma horizon sparsity)
          (delta / 4) <=
      3 * gamma ^ 2 * (horizon : Real) ^ 2 := by
  let K : Real := arms.card
  let S : Real := sparsity
  let T : Real := horizon
  let B : Real := Real.log (4 / delta)
  let variance :=
    sampledPredictableSparsePathwiseVarianceBudget
      arms gamma horizon sparsity
  have hK_one : 1 < K := by
    dsimp [K]
    exact_mod_cast hcard_two
  have hK : 0 < K := lt_trans zero_lt_one hK_one
  have hS_one : 1 <= S := by
    dsimp [S]
    exact_mod_cast hsparsity
  have hT : 0 < T := by
    dsimp [T]
    exact_mod_cast hhorizon
  have hlogK : 0 <= Real.log K := (Real.log_pos hK_one).le
  have hone_lt_four_div : 1 < 4 / delta := by
    rw [lt_div_iff₀ hdelta]
    nlinarith
  have hB : 0 < B := by
    dsimp [B]
    exact Real.log_pos hone_lt_four_div
  have hlog_fourth : Real.log (1 / (delta / 4)) = B := by
    dsimp [B]
    exact log_one_div_fourth_eq_log_four_div delta hdelta
  have hmax_fourth : max (Real.log (1 / (delta / 4))) 0 = B := by
    rw [hlog_fourth]
    exact max_eq_left hB.le
  have hvariance :
      variance = K * S * T / gamma := by
    dsimp [variance, K, S, T]
    exact
      sampledPredictableSparsePathwiseVarianceBudget_eq
        arms hcard_two gamma hgamma_pos horizon sparsity
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
      K * S * Real.log K ^ 2 * B <= gamma ^ 5 * T ^ 3 := by
    simpa [K, S, T, B] using hmixed
  have hroot :
      Real.log K * Real.sqrt (variance * B) <=
        gamma ^ 2 * T ^ 2 := by
    apply le_of_sq_le_sq
    · rw [mul_pow, Real.sq_sqrt hradicand, hvariance]
      field_simp [ne_of_gt hgamma_pos]
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
  rw [hmax_fourth]
  change
    Real.log K * (2 * Real.sqrt (variance * B) + B / (gamma / K)) <=
      3 * gamma ^ 2 * T ^ 2
  rw [mul_add]
  nlinarith [hroot, hlinear]

/-- The sparse base and pathwise predictable-variance radius make the
learning-rate-balanced square root at most `2 * gamma * T`. -/
theorem pathwiseVarianceProbabilisticSparseLossBalancedSqrt_le_two_mul_gamma_mul_horizon
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
      (arms.card : Real) * (sparsity : Real) *
            Real.log (arms.card : Real) ^ 2 * Real.log (4 / delta) <=
        gamma ^ 5 * (horizon : Real) ^ 3)
    (hconfidence :
      (arms.card : Real) * Real.log (4 / delta) <=
        gamma ^ 3 * (horizon : Real)) :
    Real.sqrt
        (Real.log (arms.card : Real) *
          pathwiseVarianceProbabilisticSparseLossHighProbabilityScale
            arms gamma horizon sparsity delta) <=
      2 * gamma * (horizon : Real) := by
  let K : Real := arms.card
  let S : Real := sparsity
  let T : Real := horizon
  let radius :=
    sampledMixedSquaredPredictableVarianceRadius arms gamma
      (sampledPredictableSparsePathwiseVarianceBudget
        arms gamma horizon sparsity)
      (delta / 4)
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
    have hbudget : 0 <= max (Real.log (1 / (delta / 4))) 0 :=
      le_max_right _ _
    dsimp [radius, sampledMixedSquaredPredictableVarianceRadius, K]
    exact add_nonneg
      (mul_nonneg (by norm_num) (Real.sqrt_nonneg _))
      (div_nonneg hbudget hepsilon.le)
  have hradius_bound :
      Real.log K * radius <= 3 * gamma ^ 2 * T ^ 2 := by
    dsimp [K, T, radius]
    exact
      log_mul_pathwiseVarianceProbabilisticSparseLossRadius_le_three_mul_sq_mul_horizon_sq
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
  · dsimp [pathwiseVarianceProbabilisticSparseLossHighProbabilityScale,
      K, S, T, radius] at *
    nlinarith

/-- Explicit realized-regret threshold after tuning eta and gamma. -/
noncomputable def pathwiseVarianceProbabilisticSparseLossRealizedExplicitThreshold
    {Action : Type v} (_arms : Finset Action) (gamma : Real)
    (horizon _sparsity : Nat) (_delta : Real) : Real :=
  14 * gamma * (horizon : Real)

/-- Four algebraic exploration contracts reduce the eta-tuned pathwise
threshold to `14 * gamma * T`. -/
theorem pathwiseVarianceProbabilisticSparseLossRealizedTunedThreshold_le_explicitThreshold
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
      (arms.card : Real) * (sparsity : Real) *
            Real.log (arms.card : Real) ^ 2 * Real.log (4 / delta) <=
        gamma ^ 5 * (horizon : Real) ^ 3)
    (hconfidence :
      (arms.card : Real) * Real.log (4 / delta) <=
        gamma ^ 3 * (horizon : Real))
    (hrealized :
      2 * ((Concentration.intervalVarianceProxy 0 1 : NNReal) : Real) *
          Real.log (4 / delta) <=
        gamma ^ 2 * (horizon : Real)) :
    pathwiseVarianceProbabilisticSparseLossRealizedTunedThreshold
        arms gamma horizon sparsity delta <=
      pathwiseVarianceProbabilisticSparseLossRealizedExplicitThreshold
        arms gamma horizon sparsity delta := by
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
  have hbudget_pos : 0 < budget := by
    dsimp [budget]
    exact Real.log_pos hone_lt_four_div
  have hlog_fourth : Real.log (1 / (delta / 4)) = budget := by
    dsimp [budget]
    exact log_one_div_fourth_eq_log_four_div delta hdelta
  have hmax_fourth : max (Real.log (1 / (delta / 4))) 0 = budget := by
    rw [hlog_fourth]
    exact max_eq_left hbudget_pos.le
  have hbalanced :
      Real.sqrt
          (Real.log K *
            pathwiseVarianceProbabilisticSparseLossHighProbabilityScale
              arms gamma horizon sparsity delta) <=
        2 * gamma * T := by
    simpa [K, T] using
      pathwiseVarianceProbabilisticSparseLossBalancedSqrt_le_two_mul_gamma_mul_horizon
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
    pathwiseVarianceProbabilisticSparseLossRealizedTunedThreshold,
    pathwiseVarianceProbabilisticSparseLossRealizedExplicitThreshold,
    sampledPurePredictableMinusObservedBernsteinConfidenceRadius,
    sampledComparatorEstimatorBernsteinConfidenceRadius,
    sampledPredictableRealizedDeviationConfidenceRadius]
  rw [hmax_fourth, hlog_fourth]
  change
    3 * Real.sqrt
          (Real.log K *
            pathwiseVarianceProbabilisticSparseLossHighProbabilityScale
              arms gamma horizon sparsity delta) +
        gamma * T +
        (2 * Real.sqrt (T * budget / (gamma / K)) +
          budget / (gamma / K)) +
        (2 * Real.sqrt (T * budget / (gamma / K)) +
          budget / (gamma / K)) +
        Real.sqrt (2 * (T * variance) * budget) <=
      14 * gamma * T
  linarith

/-- Gamma-characterized generated regret away from the exact
sparsity-failure event and without a global-envelope Markov term. -/
theorem sampledPredictable_gammaCharacterizedProbabilisticSparseLossPathwiseVarianceRealizedRegret_tail_off_sparsityFailure
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
      (arms.card : Real) * (sparsity : Real) *
            Real.log (arms.card : Real) ^ 2 * Real.log (4 / delta) <=
        gamma ^ 5 * (horizon : Real) ^ 3)
    (hconfidence :
      (arms.card : Real) * Real.log (4 / delta) <=
        gamma ^ 3 * (horizon : Real))
    (hrealized :
      2 * ((Concentration.intervalVarianceProxy 0 1 : NNReal) : Real) *
          Real.log (4 / delta) <=
        gamma ^ 2 * (horizon : Real)) :
    let eta :=
      pathwiseVarianceProbabilisticSparseLossHighProbabilityLearningRate
        arms gamma horizon sparsity delta
    let mu := prior ⊗ₘ sampledImportanceWeightedTrajectoryKernel arms harms
      eta gamma hgamma_pos.le (by linarith : gamma <= 1) loss.environment
    mu ({sample |
        pathwiseVarianceProbabilisticSparseLossRealizedExplicitThreshold
            arms gamma horizon sparsity delta <=
          (Finset.range horizon).sum (fun t =>
              sampledTrajectoryRealizedLossAt t sample) -
            (Finset.range horizon).sum (fun t =>
              predictableLossAt loss t sample comparator)} \
      sampledPredictableSparsityFailure arms loss horizon sparsity) <=
        ENNReal.ofReal delta := by
  dsimp only
  have hgamma_lt_one : gamma < 1 := by linarith
  have hthreshold :=
    pathwiseVarianceProbabilisticSparseLossRealizedTunedThreshold_le_explicitThreshold
      arms hcard_two horizon sparsity hhorizon hsparsity gamma delta
        hgamma_pos hgamma_le_half hdelta hdelta_le_one hbase hmixed
        hconfidence hrealized
  have htail :=
    sampledPredictable_tunedProbabilisticSparseLossPathwiseVarianceRealizedRegret_tail_off_sparsityFailure
      prior arms harms hcard_two gamma hgamma_pos hgamma_le_half loss comparator
        hcomparator horizon sparsity hhorizon hsparsity delta hdelta
  dsimp only at htail ⊢
  calc
    (prior ⊗ₘ sampledImportanceWeightedTrajectoryKernel arms harms
        (pathwiseVarianceProbabilisticSparseLossHighProbabilityLearningRate
          arms gamma horizon sparsity delta)
        gamma hgamma_pos.le hgamma_lt_one.le loss.environment)
        ({sample |
          pathwiseVarianceProbabilisticSparseLossRealizedExplicitThreshold
              arms gamma horizon sparsity delta <=
            (Finset.range horizon).sum (fun t =>
                sampledTrajectoryRealizedLossAt t sample) -
              (Finset.range horizon).sum (fun t =>
                predictableLossAt loss t sample comparator)} \
          sampledPredictableSparsityFailure arms loss horizon sparsity) <=
      (prior ⊗ₘ sampledImportanceWeightedTrajectoryKernel arms harms
        (pathwiseVarianceProbabilisticSparseLossHighProbabilityLearningRate
          arms gamma horizon sparsity delta)
        gamma hgamma_pos.le hgamma_lt_one.le loss.environment)
        ({sample |
          pathwiseVarianceProbabilisticSparseLossRealizedTunedThreshold
              arms gamma horizon sparsity delta <=
            (Finset.range horizon).sum (fun t =>
                sampledTrajectoryRealizedLossAt t sample) -
              (Finset.range horizon).sum (fun t =>
                predictableLossAt loss t sample comparator)} \
          sampledPredictableSparsityFailure arms loss horizon sparsity) := by
        apply measure_mono
        intro sample hsample
        exact ⟨hthreshold.trans hsample.1, hsample.2⟩
    _ <= ENNReal.ofReal delta := htail

/-- Gamma-characterized generated regret with the exact sparsity-failure
residual and no global-envelope Markov term. -/
theorem sampledPredictable_gammaCharacterizedProbabilisticSparseLossPathwiseVarianceRealizedRegret_tail
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
      (arms.card : Real) * (sparsity : Real) *
            Real.log (arms.card : Real) ^ 2 * Real.log (4 / delta) <=
        gamma ^ 5 * (horizon : Real) ^ 3)
    (hconfidence :
      (arms.card : Real) * Real.log (4 / delta) <=
        gamma ^ 3 * (horizon : Real))
    (hrealized :
      2 * ((Concentration.intervalVarianceProxy 0 1 : NNReal) : Real) *
          Real.log (4 / delta) <=
        gamma ^ 2 * (horizon : Real)) :
    let eta :=
      pathwiseVarianceProbabilisticSparseLossHighProbabilityLearningRate
        arms gamma horizon sparsity delta
    let mu := prior ⊗ₘ sampledImportanceWeightedTrajectoryKernel arms harms
      eta gamma hgamma_pos.le (by linarith : gamma <= 1) loss.environment
    mu {sample |
        pathwiseVarianceProbabilisticSparseLossRealizedExplicitThreshold
            arms gamma horizon sparsity delta <=
          (Finset.range horizon).sum (fun t =>
              sampledTrajectoryRealizedLossAt t sample) -
            (Finset.range horizon).sum (fun t =>
              predictableLossAt loss t sample comparator)} <=
      ENNReal.ofReal delta +
        mu (sampledPredictableSparsityFailure arms loss horizon sparsity) := by
  dsimp only
  have hgamma_lt_one : gamma < 1 := by linarith
  let mu := prior ⊗ₘ sampledImportanceWeightedTrajectoryKernel arms harms
    (pathwiseVarianceProbabilisticSparseLossHighProbabilityLearningRate
      arms gamma horizon sparsity delta)
    gamma hgamma_pos.le hgamma_lt_one.le loss.environment
  let sparsityBad :=
    sampledPredictableSparsityFailure arms loss horizon sparsity
  let realizedBad : Set (Env × ((k : Nat) → Action × Real)) :=
    {sample |
      pathwiseVarianceProbabilisticSparseLossRealizedExplicitThreshold
          arms gamma horizon sparsity delta <=
        (Finset.range horizon).sum (fun t =>
            sampledTrajectoryRealizedLossAt t sample) -
          (Finset.range horizon).sum (fun t =>
            predictableLossAt loss t sample comparator)}
  have hoff :=
    sampledPredictable_gammaCharacterizedProbabilisticSparseLossPathwiseVarianceRealizedRegret_tail_off_sparsityFailure
      prior arms harms hcard_two gamma hgamma_pos hgamma_le_half loss comparator
        hcomparator horizon sparsity hhorizon hsparsity delta hdelta
        hdelta_le_one hbase hmixed hconfidence hrealized
  dsimp only at hoff
  have hsplit : realizedBad ⊆ (realizedBad \ sparsityBad) ∪ sparsityBad := by
    intro sample hsample
    by_cases hbad : sample ∈ sparsityBad
    · exact Or.inr hbad
    · exact Or.inl ⟨hsample, hbad⟩
  calc
    mu realizedBad <= mu ((realizedBad \ sparsityBad) ∪ sparsityBad) :=
      measure_mono hsplit
    _ <= mu (realizedBad \ sparsityBad) + mu sparsityBad :=
      measure_union_le _ _
    _ <= ENNReal.ofReal delta + mu sparsityBad :=
      add_le_add (by simpa [mu, realizedBad, sparsityBad] using hoff) le_rfl

/-- Practical gamma-characterized endpoint under the exact generated-measure
bound on the sparsity-failure event. -/
theorem sampledPredictable_gammaCharacterizedProbabilisticSparseLossPathwiseVarianceRealizedRegret_tail_of_sparsityFailure_le
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
      (arms.card : Real) * (sparsity : Real) *
            Real.log (arms.card : Real) ^ 2 * Real.log (4 / delta) <=
        gamma ^ 5 * (horizon : Real) ^ 3)
    (hconfidence :
      (arms.card : Real) * Real.log (4 / delta) <=
        gamma ^ 3 * (horizon : Real))
    (hrealized :
      2 * ((Concentration.intervalVarianceProxy 0 1 : NNReal) : Real) *
          Real.log (4 / delta) <=
        gamma ^ 2 * (horizon : Real)) :
    let eta :=
      pathwiseVarianceProbabilisticSparseLossHighProbabilityLearningRate
        arms gamma horizon sparsity delta
    let mu := prior ⊗ₘ sampledImportanceWeightedTrajectoryKernel arms harms
      eta gamma hgamma_pos.le (by linarith : gamma <= 1) loss.environment
    mu (sampledPredictableSparsityFailure arms loss horizon sparsity) <=
        ENNReal.ofReal epsilon →
      mu {sample |
          pathwiseVarianceProbabilisticSparseLossRealizedExplicitThreshold
              arms gamma horizon sparsity delta <=
            (Finset.range horizon).sum (fun t =>
                sampledTrajectoryRealizedLossAt t sample) -
              (Finset.range horizon).sum (fun t =>
                predictableLossAt loss t sample comparator)} <=
        ENNReal.ofReal delta + ENNReal.ofReal epsilon := by
  dsimp only
  intro hfailure
  have htail :=
    sampledPredictable_gammaCharacterizedProbabilisticSparseLossPathwiseVarianceRealizedRegret_tail
      prior arms harms hcard_two gamma hgamma_pos hgamma_le_half loss comparator
        hcomparator horizon sparsity hhorizon hsparsity delta hdelta
        hdelta_le_one hbase hmixed hconfidence hrealized
  dsimp only at htail
  exact htail.trans (add_le_add le_rfl hfailure)

/-- Fifth-root scale forced by the sparse pathwise predictable-variance
radius. Unlike the Markov scale, it has no polynomial `1 / delta` factor. -/
noncomputable def pathwiseVarianceProbabilisticSparseLossMixedExplorationScale
    (K S T delta : Real) : Real :=
  (K * S * Real.log K ^ 2 * Real.log (4 / delta) / T ^ 3) ^
    (5 : Real)⁻¹

/-- Unclipped maximum of the sparse arm, pathwise mixed-square, Bernstein,
and realized-deviation exploration scales. -/
noncomputable def pathwiseVarianceProbabilisticSparseLossRawExplorationRate
    (K S T delta : Real) : Real :=
  max (sparseLossPredictableVarianceArmExplorationScale K S T)
    (max
      (pathwiseVarianceProbabilisticSparseLossMixedExplorationScale
        K S T delta)
      (max
        (randomSquareBernsteinConfidenceExplorationScale K T delta)
        (randomSquareBernsteinRealizedExplorationScale T delta)))

/-- Explicit pathwise-variance exploration schedule clipped into the Hedge
stability regime. -/
noncomputable def pathwiseVarianceProbabilisticSparseLossClippedExplorationRate
    (K S T delta : Real) : Real :=
  min (1 / 2)
    (pathwiseVarianceProbabilisticSparseLossRawExplorationRate K S T delta)

theorem pathwiseVarianceProbabilisticSparseLossClippedExplorationRate_le_half
    (K S T delta : Real) :
    pathwiseVarianceProbabilisticSparseLossClippedExplorationRate
        K S T delta <=
      1 / 2 :=
  min_le_left _ _

theorem pathwiseVarianceProbabilisticSparseLossClippedExplorationRate_eq_raw
    (K S T delta : Real)
    (hraw :
      pathwiseVarianceProbabilisticSparseLossRawExplorationRate
          K S T delta <=
        1 / 2) :
    pathwiseVarianceProbabilisticSparseLossClippedExplorationRate
        K S T delta =
      pathwiseVarianceProbabilisticSparseLossRawExplorationRate
        K S T delta :=
  min_eq_right hraw

theorem pathwiseVarianceProbabilisticSparseLossRawExplorationRate_pos
    (K S T delta : Real) (hK_one : 1 < K) (hS : 0 < S) (hT : 0 < T) :
    0 <
      pathwiseVarianceProbabilisticSparseLossRawExplorationRate
        K S T delta := by
  have hbase : 0 < S * Real.log K / T :=
    div_pos (mul_pos hS (Real.log_pos hK_one)) hT
  have hscale :
      0 < sparseLossPredictableVarianceArmExplorationScale K S T :=
    Real.sqrt_pos.2 hbase
  exact hscale.trans_le (le_max_left _ _)

theorem pathwiseVarianceProbabilisticSparseLossClippedExplorationRate_pos
    (K S T delta : Real) (hK_one : 1 < K) (hS : 0 < S) (hT : 0 < T) :
    0 <
      pathwiseVarianceProbabilisticSparseLossClippedExplorationRate
        K S T delta := by
  apply lt_min
  · norm_num
  · exact
      pathwiseVarianceProbabilisticSparseLossRawExplorationRate_pos
        K S T delta hK_one hS hT

/-- Transparent horizon contracts ensure every raw schedule component is at
most one half, so clipping is inactive. -/
theorem pathwiseVarianceProbabilisticSparseLossRawExplorationRate_le_half_of_horizon_contracts
    (K S T delta : Real) (hK_one : 1 < K) (hS : 0 < S) (hT : 0 < T)
    (hdelta : 0 < delta) (hdelta_le_one : delta <= 1)
    (hlarge_arm : 4 * (S * Real.log K) <= T)
    (hlarge_mixed :
      32 * (K * S * Real.log K ^ 2 * Real.log (4 / delta)) <= T ^ 3)
    (hlarge_confidence : 8 * (K * Real.log (4 / delta)) <= T)
    (hlarge_realized :
      8 * ((Concentration.intervalVarianceProxy 0 1 : NNReal) : Real) *
          Real.log (4 / delta) <= T) :
    pathwiseVarianceProbabilisticSparseLossRawExplorationRate
        K S T delta <=
      1 / 2 := by
  have hK : 0 < K := lt_trans zero_lt_one hK_one
  have hlogK : 0 <= Real.log K := (Real.log_pos hK_one).le
  have hone_lt_four_div : 1 < 4 / delta := by
    rw [lt_div_iff₀ hdelta]
    nlinarith
  have hlog : 0 <= Real.log (4 / delta) :=
    (Real.log_pos hone_lt_four_div).le
  have hmixed_nonneg :
      0 <= K * S * Real.log K ^ 2 * Real.log (4 / delta) := by
    positivity
  have hdenominator : 0 < T ^ 3 := by positivity
  rw [pathwiseVarianceProbabilisticSparseLossRawExplorationRate]
  apply max_le
  · exact sqrt_div_le_half_of_four_mul_le
      (S * Real.log K) T hT hlarge_arm
  apply max_le
  · exact rpow_inv_five_le_half_of_thirtytwo_mul_le
      (K * S * Real.log K ^ 2 * Real.log (4 / delta))
      (T ^ 3) hmixed_nonneg hdenominator hlarge_mixed
  apply max_le
  · exact rpow_inv_three_le_half_of_eight_mul_le
      (K * Real.log (4 / delta)) T (mul_nonneg hK.le hlog) hT
        hlarge_confidence
  · apply sqrt_div_le_half_of_four_mul_le
    · exact hT
    · nlinarith [hlarge_realized]

/-- The clipped maximum supplies exactly the four contracts consumed by the
gamma-characterized pathwise-variance theorem. -/
theorem pathwiseVarianceProbabilisticSparseLossClippedExplorationRate_contracts
    (K S T delta : Real) (hK_one : 1 < K) (hS : 0 < S) (hT : 0 < T)
    (hdelta : 0 < delta) (hdelta_le_one : delta <= 1)
    (hlarge_arm : 4 * (S * Real.log K) <= T)
    (hlarge_mixed :
      32 * (K * S * Real.log K ^ 2 * Real.log (4 / delta)) <= T ^ 3)
    (hlarge_confidence : 8 * (K * Real.log (4 / delta)) <= T)
    (hlarge_realized :
      8 * ((Concentration.intervalVarianceProxy 0 1 : NNReal) : Real) *
          Real.log (4 / delta) <= T) :
    let gamma :=
      pathwiseVarianceProbabilisticSparseLossClippedExplorationRate
        K S T delta
    0 < gamma ∧
      gamma <= 1 / 2 ∧
      S * Real.log K <= gamma ^ 2 * T ∧
      K * S * Real.log K ^ 2 * Real.log (4 / delta) <=
        gamma ^ 5 * T ^ 3 ∧
      K * Real.log (4 / delta) <= gamma ^ 3 * T ∧
      2 * ((Concentration.intervalVarianceProxy 0 1 : NNReal) : Real) *
          Real.log (4 / delta) <= gamma ^ 2 * T := by
  dsimp only
  let variance : Real :=
    ((Concentration.intervalVarianceProxy 0 1 : NNReal) : Real)
  let numerator : Real :=
    K * S * Real.log K ^ 2 * Real.log (4 / delta)
  let denominator : Real := T ^ 3
  have hK : 0 < K := lt_trans zero_lt_one hK_one
  have hlogK : 0 <= Real.log K := (Real.log_pos hK_one).le
  have hone_lt_four_div : 1 < 4 / delta := by
    rw [lt_div_iff₀ hdelta]
    nlinarith
  have hlog : 0 <= Real.log (4 / delta) :=
    (Real.log_pos hone_lt_four_div).le
  have hvariance : 0 <= variance := NNReal.coe_nonneg _
  have hnumerator : 0 <= numerator := by
    dsimp [numerator]
    positivity
  have hdenominator : 0 < denominator := by
    dsimp [denominator]
    positivity
  have hraw :=
    pathwiseVarianceProbabilisticSparseLossRawExplorationRate_le_half_of_horizon_contracts
      K S T delta hK_one hS hT hdelta hdelta_le_one hlarge_arm
        hlarge_mixed hlarge_confidence hlarge_realized
  have hclip :
      pathwiseVarianceProbabilisticSparseLossClippedExplorationRate
          K S T delta =
        pathwiseVarianceProbabilisticSparseLossRawExplorationRate
          K S T delta :=
    pathwiseVarianceProbabilisticSparseLossClippedExplorationRate_eq_raw
      K S T delta hraw
  have harm_component :
      sparseLossPredictableVarianceArmExplorationScale K S T <=
        pathwiseVarianceProbabilisticSparseLossClippedExplorationRate
          K S T delta := by
    rw [hclip, pathwiseVarianceProbabilisticSparseLossRawExplorationRate]
    exact le_max_left _ _
  have hmixed_component :
      pathwiseVarianceProbabilisticSparseLossMixedExplorationScale
          K S T delta <=
        pathwiseVarianceProbabilisticSparseLossClippedExplorationRate
          K S T delta := by
    rw [hclip, pathwiseVarianceProbabilisticSparseLossRawExplorationRate]
    exact le_max_of_le_right (le_max_left _ _)
  have hconfidence_component :
      randomSquareBernsteinConfidenceExplorationScale K T delta <=
        pathwiseVarianceProbabilisticSparseLossClippedExplorationRate
          K S T delta := by
    rw [hclip, pathwiseVarianceProbabilisticSparseLossRawExplorationRate]
    exact le_max_of_le_right (le_max_of_le_right (le_max_left _ _))
  have hrealized_component :
      randomSquareBernsteinRealizedExplorationScale T delta <=
        pathwiseVarianceProbabilisticSparseLossClippedExplorationRate
          K S T delta := by
    rw [hclip, pathwiseVarianceProbabilisticSparseLossRawExplorationRate]
    exact le_max_of_le_right (le_max_of_le_right (le_max_right _ _))
  refine ⟨
    pathwiseVarianceProbabilisticSparseLossClippedExplorationRate_pos
      K S T delta hK_one hS hT,
    pathwiseVarianceProbabilisticSparseLossClippedExplorationRate_le_half
      K S T delta,
    ?_, ?_, ?_, ?_⟩
  · exact numerator_le_sq_mul_of_sqrt_div_le
      (S * Real.log K) T
        (pathwiseVarianceProbabilisticSparseLossClippedExplorationRate
          K S T delta)
        (mul_nonneg hS.le hlogK) hT (by
          simpa [sparseLossPredictableVarianceArmExplorationScale] using
            harm_component)
  · have hroot :
        (numerator / denominator) ^ (5 : Real)⁻¹ <=
          pathwiseVarianceProbabilisticSparseLossClippedExplorationRate
            K S T delta := by
      simpa [
        pathwiseVarianceProbabilisticSparseLossMixedExplorationScale,
        numerator, denominator] using hmixed_component
    have hpower :=
      numerator_le_pow_five_mul_of_rpow_inv_five_le
        numerator denominator
          (pathwiseVarianceProbabilisticSparseLossClippedExplorationRate
            K S T delta)
        hnumerator hdenominator hroot
    simpa [numerator, denominator, mul_assoc] using hpower
  · exact numerator_le_cube_mul_of_rpow_inv_three_le
      (K * Real.log (4 / delta)) T
        (pathwiseVarianceProbabilisticSparseLossClippedExplorationRate
          K S T delta)
        (mul_nonneg hK.le hlog) hT (by
          simpa [randomSquareBernsteinConfidenceExplorationScale] using
            hconfidence_component)
  · exact numerator_le_sq_mul_of_sqrt_div_le
      (2 * variance * Real.log (4 / delta)) T
        (pathwiseVarianceProbabilisticSparseLossClippedExplorationRate
          K S T delta)
        (mul_nonneg (mul_nonneg (by norm_num) hvariance) hlog) hT (by
          simpa [randomSquareBernsteinRealizedExplorationScale, variance] using
            hrealized_component)

/-- Fully explicit generated pathwise-variance regret tail away from the
exact sparsity-failure event for the clipped maximum schedule. -/
theorem sampledPredictable_explicitProbabilisticSparseLossPathwiseVarianceRealizedRegret_tail_off_sparsityFailure
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
      32 * ((arms.card : Real) * (sparsity : Real) *
          Real.log (arms.card : Real) ^ 2 * Real.log (4 / delta)) <=
        (horizon : Real) ^ 3)
    (hlarge_confidence :
      8 * ((arms.card : Real) * Real.log (4 / delta)) <=
        (horizon : Real))
    (hlarge_realized :
      8 * ((Concentration.intervalVarianceProxy 0 1 : NNReal) : Real) *
          Real.log (4 / delta) <= (horizon : Real)) :
    let gamma :=
      pathwiseVarianceProbabilisticSparseLossClippedExplorationRate
        (arms.card : Real) (sparsity : Real) (horizon : Real) delta
    let eta :=
      pathwiseVarianceProbabilisticSparseLossHighProbabilityLearningRate
        arms gamma horizon sparsity delta
    let mu := prior ⊗ₘ sampledImportanceWeightedTrajectoryKernel arms harms
      eta gamma
        (pathwiseVarianceProbabilisticSparseLossClippedExplorationRate_pos
          (arms.card : Real) (sparsity : Real) (horizon : Real) delta
          (by exact_mod_cast hcard_two)
          (by exact_mod_cast hsparsity)
          (by exact_mod_cast hhorizon)).le
        (by
          exact
            (pathwiseVarianceProbabilisticSparseLossClippedExplorationRate_le_half
              (arms.card : Real) (sparsity : Real) (horizon : Real)
                delta).trans (by norm_num))
        loss.environment
    mu ({sample |
        pathwiseVarianceProbabilisticSparseLossRealizedExplicitThreshold
            arms gamma horizon sparsity delta <=
          (Finset.range horizon).sum (fun t =>
              sampledTrajectoryRealizedLossAt t sample) -
            (Finset.range horizon).sum (fun t =>
              predictableLossAt loss t sample comparator)} \
      sampledPredictableSparsityFailure arms loss horizon sparsity) <=
        ENNReal.ofReal delta := by
  dsimp only
  have hK_one : 1 < (arms.card : Real) := by exact_mod_cast hcard_two
  have hS : 0 < (sparsity : Real) := by exact_mod_cast hsparsity
  have hT : 0 < (horizon : Real) := by exact_mod_cast hhorizon
  have hcontracts :=
    pathwiseVarianceProbabilisticSparseLossClippedExplorationRate_contracts
      (arms.card : Real) (sparsity : Real) (horizon : Real) delta
        hK_one hS hT hdelta hdelta_le_one hlarge_arm hlarge_mixed
        hlarge_confidence hlarge_realized
  dsimp only at hcontracts
  rcases hcontracts with
    ⟨hgamma_pos, hgamma_le_half, hbase, hmixed, hconfidence, hrealized⟩
  exact
    sampledPredictable_gammaCharacterizedProbabilisticSparseLossPathwiseVarianceRealizedRegret_tail_off_sparsityFailure
      prior arms harms hcard_two
        (pathwiseVarianceProbabilisticSparseLossClippedExplorationRate
          (arms.card : Real) (sparsity : Real) (horizon : Real) delta)
        hgamma_pos hgamma_le_half loss comparator hcomparator horizon sparsity
        hhorizon hsparsity delta hdelta hdelta_le_one hbase hmixed hconfidence
        hrealized

/-- Fully explicit generated pathwise-variance regret tail for the clipped
maximum schedule, retaining the exact sparsity-failure residual. -/
theorem sampledPredictable_explicitProbabilisticSparseLossPathwiseVarianceRealizedRegret_tail
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
      32 * ((arms.card : Real) * (sparsity : Real) *
          Real.log (arms.card : Real) ^ 2 * Real.log (4 / delta)) <=
        (horizon : Real) ^ 3)
    (hlarge_confidence :
      8 * ((arms.card : Real) * Real.log (4 / delta)) <=
        (horizon : Real))
    (hlarge_realized :
      8 * ((Concentration.intervalVarianceProxy 0 1 : NNReal) : Real) *
          Real.log (4 / delta) <= (horizon : Real)) :
    let gamma :=
      pathwiseVarianceProbabilisticSparseLossClippedExplorationRate
        (arms.card : Real) (sparsity : Real) (horizon : Real) delta
    let eta :=
      pathwiseVarianceProbabilisticSparseLossHighProbabilityLearningRate
        arms gamma horizon sparsity delta
    let mu := prior ⊗ₘ sampledImportanceWeightedTrajectoryKernel arms harms
      eta gamma
        (pathwiseVarianceProbabilisticSparseLossClippedExplorationRate_pos
          (arms.card : Real) (sparsity : Real) (horizon : Real) delta
          (by exact_mod_cast hcard_two)
          (by exact_mod_cast hsparsity)
          (by exact_mod_cast hhorizon)).le
        (by
          exact
            (pathwiseVarianceProbabilisticSparseLossClippedExplorationRate_le_half
              (arms.card : Real) (sparsity : Real) (horizon : Real)
                delta).trans (by norm_num))
        loss.environment
    mu {sample |
        pathwiseVarianceProbabilisticSparseLossRealizedExplicitThreshold
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
    pathwiseVarianceProbabilisticSparseLossClippedExplorationRate_contracts
      (arms.card : Real) (sparsity : Real) (horizon : Real) delta
        hK_one hS hT hdelta hdelta_le_one hlarge_arm hlarge_mixed
        hlarge_confidence hlarge_realized
  dsimp only at hcontracts
  rcases hcontracts with
    ⟨hgamma_pos, hgamma_le_half, hbase, hmixed, hconfidence, hrealized⟩
  exact
    sampledPredictable_gammaCharacterizedProbabilisticSparseLossPathwiseVarianceRealizedRegret_tail
      prior arms harms hcard_two
        (pathwiseVarianceProbabilisticSparseLossClippedExplorationRate
          (arms.card : Real) (sparsity : Real) (horizon : Real) delta)
        hgamma_pos hgamma_le_half loss comparator hcomparator horizon sparsity
        hhorizon hsparsity delta hdelta hdelta_le_one hbase hmixed hconfidence
        hrealized

/-- Fully explicit practical `delta + epsilon` theorem under the exact
sparsity-failure bound for the internally eta/gamma-tuned measure. -/
theorem sampledPredictable_explicitProbabilisticSparseLossPathwiseVarianceRealizedRegret_tail_of_sparsityFailure_le
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
      32 * ((arms.card : Real) * (sparsity : Real) *
          Real.log (arms.card : Real) ^ 2 * Real.log (4 / delta)) <=
        (horizon : Real) ^ 3)
    (hlarge_confidence :
      8 * ((arms.card : Real) * Real.log (4 / delta)) <=
        (horizon : Real))
    (hlarge_realized :
      8 * ((Concentration.intervalVarianceProxy 0 1 : NNReal) : Real) *
          Real.log (4 / delta) <= (horizon : Real)) :
    let gamma :=
      pathwiseVarianceProbabilisticSparseLossClippedExplorationRate
        (arms.card : Real) (sparsity : Real) (horizon : Real) delta
    let eta :=
      pathwiseVarianceProbabilisticSparseLossHighProbabilityLearningRate
        arms gamma horizon sparsity delta
    let mu := prior ⊗ₘ sampledImportanceWeightedTrajectoryKernel arms harms
      eta gamma
        (pathwiseVarianceProbabilisticSparseLossClippedExplorationRate_pos
          (arms.card : Real) (sparsity : Real) (horizon : Real) delta
          (by exact_mod_cast hcard_two)
          (by exact_mod_cast hsparsity)
          (by exact_mod_cast hhorizon)).le
        (by
          exact
            (pathwiseVarianceProbabilisticSparseLossClippedExplorationRate_le_half
              (arms.card : Real) (sparsity : Real) (horizon : Real)
                delta).trans (by norm_num))
        loss.environment
    mu (sampledPredictableSparsityFailure arms loss horizon sparsity) <=
        ENNReal.ofReal epsilon →
      mu {sample |
          pathwiseVarianceProbabilisticSparseLossRealizedExplicitThreshold
              arms gamma horizon sparsity delta <=
            (Finset.range horizon).sum (fun t =>
                sampledTrajectoryRealizedLossAt t sample) -
              (Finset.range horizon).sum (fun t =>
                predictableLossAt loss t sample comparator)} <=
        ENNReal.ofReal delta + ENNReal.ofReal epsilon := by
  dsimp only
  intro hfailure
  have htail :=
    sampledPredictable_explicitProbabilisticSparseLossPathwiseVarianceRealizedRegret_tail
      prior arms harms hcard_two loss comparator hcomparator horizon sparsity
        hhorizon hsparsity delta hdelta hdelta_le_one hlarge_arm hlarge_mixed
        hlarge_confidence hlarge_realized
  dsimp only at htail
  exact htail.trans (add_le_add le_rfl hfailure)

end BanditRLProof.Exp3
