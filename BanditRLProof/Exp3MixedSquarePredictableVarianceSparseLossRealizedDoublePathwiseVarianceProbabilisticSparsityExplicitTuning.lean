import BanditRLProof.Exp3MixedSquarePredictableVarianceSparseLossRealizedDoublePathwiseVarianceProbabilisticSparsityTuning
import BanditRLProof.Exp3MixedSquarePredictableVarianceSparseLossRealizedPathwiseVarianceProbabilisticSparsityExplicitTuning

/-!
# Explicit exploration tuning for sparse EXP3 with two predictable variances

This module closes gamma tuning for the sparse generated-regret theorem that
uses both the mixed-square predictable variance and the exact selected-loss
predictable variance. The first three exploration scales are shared with the
single-variance pathwise route. The additional selected-loss scale is

`sqrt (S * log (4 / delta) / T)`.

Under four transparent horizon contracts, the internally eta/gamma-tuned
threshold is at most `16 * gamma * T`. The exact sparsity-failure event is
charged once; the practical endpoint has failure budget `delta + epsilon`.
-/

namespace BanditRLProof.Exp3

open MeasureTheory ProbabilityTheory

universe u v

/-- Exploration scale forced by the exact selected-loss predictable-variance
radius with budget `S * T`. -/
noncomputable def doubleVarianceProbabilisticSparseLossRealizedExplorationScale
    (S T delta : Real) : Real :=
  Real.sqrt (S * Real.log (4 / delta) / T)

/-- The previous pathwise raw schedule augmented by the exact selected-loss
predictable-variance scale. -/
noncomputable def doubleVarianceProbabilisticSparseLossRawExplorationRate
    (K S T delta : Real) : Real :=
  max
    (pathwiseVarianceProbabilisticSparseLossRawExplorationRate K S T delta)
    (doubleVarianceProbabilisticSparseLossRealizedExplorationScale S T delta)

/-- Explicit double-variance exploration schedule clipped into the Hedge
stability regime. -/
noncomputable def doubleVarianceProbabilisticSparseLossClippedExplorationRate
    (K S T delta : Real) : Real :=
  min (1 / 2)
    (doubleVarianceProbabilisticSparseLossRawExplorationRate K S T delta)

theorem doubleVarianceProbabilisticSparseLossClippedExplorationRate_le_half
    (K S T delta : Real) :
    doubleVarianceProbabilisticSparseLossClippedExplorationRate
        K S T delta <=
      1 / 2 :=
  min_le_left _ _

theorem doubleVarianceProbabilisticSparseLossClippedExplorationRate_eq_raw
    (K S T delta : Real)
    (hraw :
      doubleVarianceProbabilisticSparseLossRawExplorationRate
          K S T delta <=
        1 / 2) :
    doubleVarianceProbabilisticSparseLossClippedExplorationRate
        K S T delta =
      doubleVarianceProbabilisticSparseLossRawExplorationRate
        K S T delta :=
  min_eq_right hraw

theorem doubleVarianceProbabilisticSparseLossRawExplorationRate_pos
    (K S T delta : Real) (hK_one : 1 < K) (hS : 0 < S) (hT : 0 < T) :
    0 <
      doubleVarianceProbabilisticSparseLossRawExplorationRate
        K S T delta :=
  (pathwiseVarianceProbabilisticSparseLossRawExplorationRate_pos
    K S T delta hK_one hS hT).trans_le (le_max_left _ _)

theorem doubleVarianceProbabilisticSparseLossClippedExplorationRate_pos
    (K S T delta : Real) (hK_one : 1 < K) (hS : 0 < S) (hT : 0 < T) :
    0 <
      doubleVarianceProbabilisticSparseLossClippedExplorationRate
        K S T delta := by
  apply lt_min
  · norm_num
  · exact
      doubleVarianceProbabilisticSparseLossRawExplorationRate_pos
        K S T delta hK_one hS hT

/-- The selected-loss horizon contract also controls the older bounded
realized-deviation component retained by the shared raw schedule. -/
theorem boundedRealizedLargeHorizon_of_doubleVarianceLargeHorizon
    (S T delta : Real) (hS_one : 1 <= S)
    (hdelta : 0 < delta) (hdelta_le_one : delta <= 1)
    (hlarge_realized :
      4 * (S * Real.log (4 / delta)) <= T) :
    8 * ((Concentration.intervalVarianceProxy 0 1 : NNReal) : Real) *
          Real.log (4 / delta) <=
      T := by
  have hone_lt_four_div : 1 < 4 / delta := by
    rw [lt_div_iff₀ hdelta]
    nlinarith
  have hlog : 0 <= Real.log (4 / delta) :=
    (Real.log_pos hone_lt_four_div).le
  have hlog_le : Real.log (4 / delta) <= S * Real.log (4 / delta) := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hS_one) hlog]
  norm_num [Concentration.intervalVarianceProxy]
  linarith

/-- Four horizon contracts place every component of the double-variance raw
schedule below one half. -/
theorem doubleVarianceProbabilisticSparseLossRawExplorationRate_le_half_of_horizon_contracts
    (K S T delta : Real) (hK_one : 1 < K) (hS_one : 1 <= S)
    (hT : 0 < T) (hdelta : 0 < delta) (hdelta_le_one : delta <= 1)
    (hlarge_arm : 4 * (S * Real.log K) <= T)
    (hlarge_mixed :
      32 * (K * S * Real.log K ^ 2 * Real.log (4 / delta)) <= T ^ 3)
    (hlarge_confidence : 8 * (K * Real.log (4 / delta)) <= T)
    (hlarge_realized :
      4 * (S * Real.log (4 / delta)) <= T) :
    doubleVarianceProbabilisticSparseLossRawExplorationRate
        K S T delta <=
      1 / 2 := by
  have hS : 0 < S := lt_of_lt_of_le zero_lt_one hS_one
  have hold_realized :
      8 * ((Concentration.intervalVarianceProxy 0 1 : NNReal) : Real) *
            Real.log (4 / delta) <=
        T :=
    boundedRealizedLargeHorizon_of_doubleVarianceLargeHorizon
      S T delta hS_one hdelta hdelta_le_one hlarge_realized
  have hold :
      pathwiseVarianceProbabilisticSparseLossRawExplorationRate
          K S T delta <=
        1 / 2 :=
    pathwiseVarianceProbabilisticSparseLossRawExplorationRate_le_half_of_horizon_contracts
      K S T delta hK_one hS hT hdelta hdelta_le_one hlarge_arm
        hlarge_mixed hlarge_confidence hold_realized
  have hnew :
      doubleVarianceProbabilisticSparseLossRealizedExplorationScale
          S T delta <=
        1 / 2 := by
    apply sqrt_div_le_half_of_four_mul_le
    · exact hT
    · exact hlarge_realized
  rw [doubleVarianceProbabilisticSparseLossRawExplorationRate]
  exact max_le hold hnew

/-- The clipped schedule supplies the base, mixed-square, Bernstein, and
selected-loss predictable-variance contracts. -/
theorem doubleVarianceProbabilisticSparseLossClippedExplorationRate_contracts
    (K S T delta : Real) (hK_one : 1 < K) (hS_one : 1 <= S)
    (hT : 0 < T) (hdelta : 0 < delta) (hdelta_le_one : delta <= 1)
    (hlarge_arm : 4 * (S * Real.log K) <= T)
    (hlarge_mixed :
      32 * (K * S * Real.log K ^ 2 * Real.log (4 / delta)) <= T ^ 3)
    (hlarge_confidence : 8 * (K * Real.log (4 / delta)) <= T)
    (hlarge_realized :
      4 * (S * Real.log (4 / delta)) <= T) :
    let gamma :=
      doubleVarianceProbabilisticSparseLossClippedExplorationRate
        K S T delta
    0 < gamma ∧
      gamma <= 1 / 2 ∧
      S * Real.log K <= gamma ^ 2 * T ∧
      K * S * Real.log K ^ 2 * Real.log (4 / delta) <=
        gamma ^ 5 * T ^ 3 ∧
      K * Real.log (4 / delta) <= gamma ^ 3 * T ∧
      S * Real.log (4 / delta) <= gamma ^ 2 * T := by
  dsimp only
  let numerator : Real :=
    K * S * Real.log K ^ 2 * Real.log (4 / delta)
  let denominator : Real := T ^ 3
  have hS : 0 < S := lt_of_lt_of_le zero_lt_one hS_one
  have hK : 0 < K := lt_trans zero_lt_one hK_one
  have hlogK : 0 <= Real.log K := (Real.log_pos hK_one).le
  have hone_lt_four_div : 1 < 4 / delta := by
    rw [lt_div_iff₀ hdelta]
    nlinarith
  have hlog : 0 <= Real.log (4 / delta) :=
    (Real.log_pos hone_lt_four_div).le
  have hnumerator : 0 <= numerator := by
    dsimp [numerator]
    positivity
  have hdenominator : 0 < denominator := by
    dsimp [denominator]
    positivity
  have hraw :=
    doubleVarianceProbabilisticSparseLossRawExplorationRate_le_half_of_horizon_contracts
      K S T delta hK_one hS_one hT hdelta hdelta_le_one hlarge_arm
        hlarge_mixed hlarge_confidence hlarge_realized
  have hclip :
      doubleVarianceProbabilisticSparseLossClippedExplorationRate
          K S T delta =
        doubleVarianceProbabilisticSparseLossRawExplorationRate
          K S T delta :=
    doubleVarianceProbabilisticSparseLossClippedExplorationRate_eq_raw
      K S T delta hraw
  have hold_component :
      pathwiseVarianceProbabilisticSparseLossRawExplorationRate
          K S T delta <=
        doubleVarianceProbabilisticSparseLossClippedExplorationRate
          K S T delta := by
    rw [hclip, doubleVarianceProbabilisticSparseLossRawExplorationRate]
    exact le_max_left _ _
  have harm_component :
      sparseLossPredictableVarianceArmExplorationScale K S T <=
        doubleVarianceProbabilisticSparseLossClippedExplorationRate
          K S T delta :=
    (le_max_left _ _).trans hold_component
  have hmixed_component :
      pathwiseVarianceProbabilisticSparseLossMixedExplorationScale
          K S T delta <=
        doubleVarianceProbabilisticSparseLossClippedExplorationRate
          K S T delta :=
    (le_max_of_le_right (le_max_left _ _)).trans hold_component
  have hconfidence_component :
      randomSquareBernsteinConfidenceExplorationScale K T delta <=
        doubleVarianceProbabilisticSparseLossClippedExplorationRate
          K S T delta :=
    (le_max_of_le_right (le_max_of_le_right (le_max_left _ _))).trans
      hold_component
  have hrealized_component :
      doubleVarianceProbabilisticSparseLossRealizedExplorationScale
          S T delta <=
        doubleVarianceProbabilisticSparseLossClippedExplorationRate
          K S T delta := by
    rw [hclip, doubleVarianceProbabilisticSparseLossRawExplorationRate]
    exact le_max_right _ _
  refine ⟨
    doubleVarianceProbabilisticSparseLossClippedExplorationRate_pos
      K S T delta hK_one hS hT,
    doubleVarianceProbabilisticSparseLossClippedExplorationRate_le_half
      K S T delta,
    ?_, ?_, ?_, ?_⟩
  · exact numerator_le_sq_mul_of_sqrt_div_le
      (S * Real.log K) T
        (doubleVarianceProbabilisticSparseLossClippedExplorationRate
          K S T delta)
        (mul_nonneg hS.le hlogK) hT (by
          simpa [sparseLossPredictableVarianceArmExplorationScale] using
            harm_component)
  · have hroot :
        (numerator / denominator) ^ (5 : Real)⁻¹ <=
          doubleVarianceProbabilisticSparseLossClippedExplorationRate
            K S T delta := by
      simpa [
        pathwiseVarianceProbabilisticSparseLossMixedExplorationScale,
        numerator, denominator] using hmixed_component
    have hpower :=
      numerator_le_pow_five_mul_of_rpow_inv_five_le
        numerator denominator
          (doubleVarianceProbabilisticSparseLossClippedExplorationRate
            K S T delta)
        hnumerator hdenominator hroot
    simpa [numerator, denominator, mul_assoc] using hpower
  · exact numerator_le_cube_mul_of_rpow_inv_three_le
      (K * Real.log (4 / delta)) T
        (doubleVarianceProbabilisticSparseLossClippedExplorationRate
          K S T delta)
        (mul_nonneg hK.le hlog) hT (by
          simpa [randomSquareBernsteinConfidenceExplorationScale] using
            hconfidence_component)
  · exact numerator_le_sq_mul_of_sqrt_div_le
      (S * Real.log (4 / delta)) T
        (doubleVarianceProbabilisticSparseLossClippedExplorationRate
          K S T delta)
        (mul_nonneg hS.le hlog) hT (by
          simpa [
            doubleVarianceProbabilisticSparseLossRealizedExplorationScale]
            using hrealized_component)

/-- Explicit double-variance threshold after tuning eta and gamma. -/
noncomputable def pathwiseVarianceProbabilisticSparseLossDoubleVarianceRealizedExplicitThreshold
    {Action : Type v} (_arms : Finset Action) (gamma : Real)
    (horizon _sparsity : Nat) (_delta : Real) : Real :=
  16 * gamma * (horizon : Real)

/-- The exact selected-loss predictable-variance radius is at most
`3 * gamma * T` under its sparse variance contract. -/
theorem sparseRealizedPredictableVarianceRadius_le_three_mul_gamma_mul_horizon
    (S T gamma delta : Real) (hS_one : 1 <= S)
    (hT : 0 < T) (hgamma_pos : 0 < gamma)
    (hgamma_le_half : gamma <= 1 / 2)
    (hdelta : 0 < delta) (hdelta_le_one : delta <= 1)
    (hrealized :
      S * Real.log (4 / delta) <= gamma ^ 2 * T) :
    sampledRealizedPredictableVarianceRadius
        (S * T) (delta / 4) <=
      3 * gamma * T := by
  let budget : Real := Real.log (4 / delta)
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
  have hrealized' : S * budget <= gamma ^ 2 * T := by
    simpa [budget] using hrealized
  have hsq : S * T * budget <= (gamma * T) ^ 2 := by
    have hmul := mul_le_mul_of_nonneg_right hrealized' hT.le
    nlinarith
  have hroot : Real.sqrt (S * T * budget) <= gamma * T := by
    rw [Real.sqrt_le_iff]
    constructor
    · positivity
    · exact hsq
  have hbudget_le_sparse : budget <= S * budget := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hS_one) hbudget_pos.le]
  have hgamma_sq_le_gamma : gamma ^ 2 <= gamma := by
    nlinarith
  have hgamma_sq_T_le : gamma ^ 2 * T <= gamma * T :=
    mul_le_mul_of_nonneg_right hgamma_sq_le_gamma hT.le
  have hbudget_le : budget <= gamma * T :=
    hbudget_le_sparse.trans (hrealized'.trans hgamma_sq_T_le)
  dsimp [sampledRealizedPredictableVarianceRadius]
  rw [hmax_fourth]
  linarith

/-- The four exploration contracts reduce the eta-tuned double-variance
threshold to `16 * gamma * T`. -/
theorem pathwiseVarianceProbabilisticSparseLossDoubleVarianceRealizedTunedThreshold_le_explicitThreshold
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
      (sparsity : Real) * Real.log (4 / delta) <=
        gamma ^ 2 * (horizon : Real)) :
    pathwiseVarianceProbabilisticSparseLossDoubleVarianceRealizedTunedThreshold
        arms gamma horizon sparsity delta <=
      pathwiseVarianceProbabilisticSparseLossDoubleVarianceRealizedExplicitThreshold
        arms gamma horizon sparsity delta := by
  let K : Real := arms.card
  let S : Real := sparsity
  let T : Real := horizon
  let budget : Real := Real.log (4 / delta)
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
  have hrealized_radius :
      sampledRealizedPredictableVarianceRadius
          (S * T) (delta / 4) <=
        3 * gamma * T :=
    sparseRealizedPredictableVarianceRadius_le_three_mul_gamma_mul_horizon
      S T gamma delta hS_one hT hgamma_pos hgamma_le_half hdelta
        hdelta_le_one (by simpa [S, T, budget] using hrealized)
  dsimp [
    pathwiseVarianceProbabilisticSparseLossDoubleVarianceRealizedTunedThreshold,
    pathwiseVarianceProbabilisticSparseLossDoubleVarianceRealizedExplicitThreshold,
    sampledPurePredictableMinusObservedBernsteinConfidenceRadius,
    sampledComparatorEstimatorBernsteinConfidenceRadius,
    sampledPredictableSparseRealizedVarianceBudget]
  rw [hmax_fourth]
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
        sampledRealizedPredictableVarianceRadius (S * T) (delta / 4) <=
      16 * gamma * T
  linarith

/-- Gamma-characterized double-variance regret tail away from the exact
sparsity-failure event. -/
theorem sampledPredictable_gammaCharacterizedDoubleVarianceProbabilisticSparseLossRealizedRegret_tail_off_sparsityFailure
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
      (sparsity : Real) * Real.log (4 / delta) <=
        gamma ^ 2 * (horizon : Real)) :
    let eta :=
      pathwiseVarianceProbabilisticSparseLossHighProbabilityLearningRate
        arms gamma horizon sparsity delta
    let mu := prior ⊗ₘ sampledImportanceWeightedTrajectoryKernel arms harms
      eta gamma hgamma_pos.le (by linarith : gamma <= 1) loss.environment
    mu ({sample |
        pathwiseVarianceProbabilisticSparseLossDoubleVarianceRealizedExplicitThreshold
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
    pathwiseVarianceProbabilisticSparseLossDoubleVarianceRealizedTunedThreshold_le_explicitThreshold
      arms hcard_two horizon sparsity hhorizon hsparsity gamma delta
        hgamma_pos hgamma_le_half hdelta hdelta_le_one hbase hmixed
        hconfidence hrealized
  have htail :=
    sampledPredictable_tunedDoubleVarianceProbabilisticSparseLossRealizedRegret_tail_off_sparsityFailure
      prior arms harms hcard_two gamma hgamma_pos hgamma_le_half loss comparator
        hcomparator horizon sparsity hhorizon hsparsity delta hdelta
  dsimp only at htail ⊢
  calc
    (prior ⊗ₘ sampledImportanceWeightedTrajectoryKernel arms harms
        (pathwiseVarianceProbabilisticSparseLossHighProbabilityLearningRate
          arms gamma horizon sparsity delta)
        gamma hgamma_pos.le hgamma_lt_one.le loss.environment)
        ({sample |
          pathwiseVarianceProbabilisticSparseLossDoubleVarianceRealizedExplicitThreshold
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
          pathwiseVarianceProbabilisticSparseLossDoubleVarianceRealizedTunedThreshold
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

/-- Gamma-characterized double-variance regret with the exact
sparsity-failure residual. -/
theorem sampledPredictable_gammaCharacterizedDoubleVarianceProbabilisticSparseLossRealizedRegret_tail
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
      (sparsity : Real) * Real.log (4 / delta) <=
        gamma ^ 2 * (horizon : Real)) :
    let eta :=
      pathwiseVarianceProbabilisticSparseLossHighProbabilityLearningRate
        arms gamma horizon sparsity delta
    let mu := prior ⊗ₘ sampledImportanceWeightedTrajectoryKernel arms harms
      eta gamma hgamma_pos.le (by linarith : gamma <= 1) loss.environment
    mu {sample |
        pathwiseVarianceProbabilisticSparseLossDoubleVarianceRealizedExplicitThreshold
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
    pathwiseVarianceProbabilisticSparseLossDoubleVarianceRealizedTunedThreshold_le_explicitThreshold
      arms hcard_two horizon sparsity hhorizon hsparsity gamma delta
        hgamma_pos hgamma_le_half hdelta hdelta_le_one hbase hmixed
        hconfidence hrealized
  have htail :=
    sampledPredictable_tunedDoubleVarianceProbabilisticSparseLossRealizedRegret_tail
      prior arms harms hcard_two gamma hgamma_pos hgamma_le_half loss comparator
        hcomparator horizon sparsity hhorizon hsparsity delta hdelta
  dsimp only at htail ⊢
  exact
    (measure_mono (fun _sample hsample => hthreshold.trans hsample)).trans htail

/-- Practical gamma-characterized endpoint under the exact generated-measure
bound on the sparsity-failure event. -/
theorem sampledPredictable_gammaCharacterizedDoubleVarianceProbabilisticSparseLossRealizedRegret_tail_of_sparsityFailure_le
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
      (sparsity : Real) * Real.log (4 / delta) <=
        gamma ^ 2 * (horizon : Real)) :
    let eta :=
      pathwiseVarianceProbabilisticSparseLossHighProbabilityLearningRate
        arms gamma horizon sparsity delta
    let mu := prior ⊗ₘ sampledImportanceWeightedTrajectoryKernel arms harms
      eta gamma hgamma_pos.le (by linarith : gamma <= 1) loss.environment
    mu (sampledPredictableSparsityFailure arms loss horizon sparsity) <=
        ENNReal.ofReal epsilon →
      mu {sample |
          pathwiseVarianceProbabilisticSparseLossDoubleVarianceRealizedExplicitThreshold
              arms gamma horizon sparsity delta <=
            (Finset.range horizon).sum (fun t =>
                sampledTrajectoryRealizedLossAt t sample) -
              (Finset.range horizon).sum (fun t =>
                predictableLossAt loss t sample comparator)} <=
        ENNReal.ofReal delta + ENNReal.ofReal epsilon := by
  dsimp only
  intro hfailure
  have htail :=
    sampledPredictable_gammaCharacterizedDoubleVarianceProbabilisticSparseLossRealizedRegret_tail
      prior arms harms hcard_two gamma hgamma_pos hgamma_le_half loss comparator
        hcomparator horizon sparsity hhorizon hsparsity delta hdelta
        hdelta_le_one hbase hmixed hconfidence hrealized
  dsimp only at htail
  exact htail.trans (add_le_add le_rfl hfailure)

/-- Fully explicit double-variance regret tail away from the exact
sparsity-failure event for the clipped schedule. -/
theorem sampledPredictable_explicitDoubleVarianceProbabilisticSparseLossRealizedRegret_tail_off_sparsityFailure
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
      4 * ((sparsity : Real) * Real.log (4 / delta)) <=
        (horizon : Real)) :
    let gamma :=
      doubleVarianceProbabilisticSparseLossClippedExplorationRate
        (arms.card : Real) (sparsity : Real) (horizon : Real) delta
    let eta :=
      pathwiseVarianceProbabilisticSparseLossHighProbabilityLearningRate
        arms gamma horizon sparsity delta
    let mu := prior ⊗ₘ sampledImportanceWeightedTrajectoryKernel arms harms
      eta gamma
        (doubleVarianceProbabilisticSparseLossClippedExplorationRate_pos
          (arms.card : Real) (sparsity : Real) (horizon : Real) delta
          (by exact_mod_cast hcard_two)
          (by exact_mod_cast hsparsity)
          (by exact_mod_cast hhorizon)).le
        (by
          exact
            (doubleVarianceProbabilisticSparseLossClippedExplorationRate_le_half
              (arms.card : Real) (sparsity : Real) (horizon : Real)
                delta).trans (by norm_num))
        loss.environment
    mu ({sample |
        pathwiseVarianceProbabilisticSparseLossDoubleVarianceRealizedExplicitThreshold
            arms gamma horizon sparsity delta <=
          (Finset.range horizon).sum (fun t =>
              sampledTrajectoryRealizedLossAt t sample) -
            (Finset.range horizon).sum (fun t =>
              predictableLossAt loss t sample comparator)} \
      sampledPredictableSparsityFailure arms loss horizon sparsity) <=
        ENNReal.ofReal delta := by
  dsimp only
  have hK_one : 1 < (arms.card : Real) := by exact_mod_cast hcard_two
  have hS_one : 1 <= (sparsity : Real) := by exact_mod_cast hsparsity
  have hT : 0 < (horizon : Real) := by exact_mod_cast hhorizon
  have hcontracts :=
    doubleVarianceProbabilisticSparseLossClippedExplorationRate_contracts
      (arms.card : Real) (sparsity : Real) (horizon : Real) delta
        hK_one hS_one hT hdelta hdelta_le_one hlarge_arm hlarge_mixed
        hlarge_confidence hlarge_realized
  dsimp only at hcontracts
  rcases hcontracts with
    ⟨hgamma_pos, hgamma_le_half, hbase, hmixed, hconfidence, hrealized⟩
  exact
    sampledPredictable_gammaCharacterizedDoubleVarianceProbabilisticSparseLossRealizedRegret_tail_off_sparsityFailure
      prior arms harms hcard_two
        (doubleVarianceProbabilisticSparseLossClippedExplorationRate
          (arms.card : Real) (sparsity : Real) (horizon : Real) delta)
        hgamma_pos hgamma_le_half loss comparator hcomparator horizon sparsity
        hhorizon hsparsity delta hdelta hdelta_le_one hbase hmixed hconfidence
        hrealized

/-- Fully explicit double-variance regret with the exact sparsity-failure
residual. -/
theorem sampledPredictable_explicitDoubleVarianceProbabilisticSparseLossRealizedRegret_tail
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
      4 * ((sparsity : Real) * Real.log (4 / delta)) <=
        (horizon : Real)) :
    let gamma :=
      doubleVarianceProbabilisticSparseLossClippedExplorationRate
        (arms.card : Real) (sparsity : Real) (horizon : Real) delta
    let eta :=
      pathwiseVarianceProbabilisticSparseLossHighProbabilityLearningRate
        arms gamma horizon sparsity delta
    let mu := prior ⊗ₘ sampledImportanceWeightedTrajectoryKernel arms harms
      eta gamma
        (doubleVarianceProbabilisticSparseLossClippedExplorationRate_pos
          (arms.card : Real) (sparsity : Real) (horizon : Real) delta
          (by exact_mod_cast hcard_two)
          (by exact_mod_cast hsparsity)
          (by exact_mod_cast hhorizon)).le
        (by
          exact
            (doubleVarianceProbabilisticSparseLossClippedExplorationRate_le_half
              (arms.card : Real) (sparsity : Real) (horizon : Real)
                delta).trans (by norm_num))
        loss.environment
    mu {sample |
        pathwiseVarianceProbabilisticSparseLossDoubleVarianceRealizedExplicitThreshold
            arms gamma horizon sparsity delta <=
          (Finset.range horizon).sum (fun t =>
              sampledTrajectoryRealizedLossAt t sample) -
            (Finset.range horizon).sum (fun t =>
              predictableLossAt loss t sample comparator)} <=
      ENNReal.ofReal delta +
        mu (sampledPredictableSparsityFailure arms loss horizon sparsity) := by
  dsimp only
  have hK_one : 1 < (arms.card : Real) := by exact_mod_cast hcard_two
  have hS_one : 1 <= (sparsity : Real) := by exact_mod_cast hsparsity
  have hT : 0 < (horizon : Real) := by exact_mod_cast hhorizon
  have hcontracts :=
    doubleVarianceProbabilisticSparseLossClippedExplorationRate_contracts
      (arms.card : Real) (sparsity : Real) (horizon : Real) delta
        hK_one hS_one hT hdelta hdelta_le_one hlarge_arm hlarge_mixed
        hlarge_confidence hlarge_realized
  dsimp only at hcontracts
  rcases hcontracts with
    ⟨hgamma_pos, hgamma_le_half, hbase, hmixed, hconfidence, hrealized⟩
  exact
    sampledPredictable_gammaCharacterizedDoubleVarianceProbabilisticSparseLossRealizedRegret_tail
      prior arms harms hcard_two
        (doubleVarianceProbabilisticSparseLossClippedExplorationRate
          (arms.card : Real) (sparsity : Real) (horizon : Real) delta)
        hgamma_pos hgamma_le_half loss comparator hcomparator horizon sparsity
        hhorizon hsparsity delta hdelta hdelta_le_one hbase hmixed hconfidence
        hrealized

/-- Fully explicit practical `delta + epsilon` theorem under the exact
sparsity-failure bound for the internally eta/gamma-tuned measure. -/
theorem sampledPredictable_explicitDoubleVarianceProbabilisticSparseLossRealizedRegret_tail_of_sparsityFailure_le
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
      4 * ((sparsity : Real) * Real.log (4 / delta)) <=
        (horizon : Real)) :
    let gamma :=
      doubleVarianceProbabilisticSparseLossClippedExplorationRate
        (arms.card : Real) (sparsity : Real) (horizon : Real) delta
    let eta :=
      pathwiseVarianceProbabilisticSparseLossHighProbabilityLearningRate
        arms gamma horizon sparsity delta
    let mu := prior ⊗ₘ sampledImportanceWeightedTrajectoryKernel arms harms
      eta gamma
        (doubleVarianceProbabilisticSparseLossClippedExplorationRate_pos
          (arms.card : Real) (sparsity : Real) (horizon : Real) delta
          (by exact_mod_cast hcard_two)
          (by exact_mod_cast hsparsity)
          (by exact_mod_cast hhorizon)).le
        (by
          exact
            (doubleVarianceProbabilisticSparseLossClippedExplorationRate_le_half
              (arms.card : Real) (sparsity : Real) (horizon : Real)
                delta).trans (by norm_num))
        loss.environment
    mu (sampledPredictableSparsityFailure arms loss horizon sparsity) <=
        ENNReal.ofReal epsilon →
      mu {sample |
          pathwiseVarianceProbabilisticSparseLossDoubleVarianceRealizedExplicitThreshold
              arms gamma horizon sparsity delta <=
            (Finset.range horizon).sum (fun t =>
                sampledTrajectoryRealizedLossAt t sample) -
              (Finset.range horizon).sum (fun t =>
                predictableLossAt loss t sample comparator)} <=
        ENNReal.ofReal delta + ENNReal.ofReal epsilon := by
  dsimp only
  intro hfailure
  have htail :=
    sampledPredictable_explicitDoubleVarianceProbabilisticSparseLossRealizedRegret_tail
      prior arms harms hcard_two loss comparator hcomparator horizon sparsity
        hhorizon hsparsity delta hdelta hdelta_le_one hlarge_arm hlarge_mixed
        hlarge_confidence hlarge_realized
  dsimp only at htail
  exact htail.trans (add_le_add le_rfl hfailure)

end BanditRLProof.Exp3
