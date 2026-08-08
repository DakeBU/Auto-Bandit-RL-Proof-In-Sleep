import BanditRLProof.Exp3BernsteinRealizedHighProbabilityRegret

/-!
# Parameter tuning for the realized EXP3 Bernstein-confidence route

The compiled high-probability theorem retains a pathwise estimator-square
term. Consequently, the expected-regret choice `eta = gamma / K` leaves a
linear term. This module instead balances the Hedge terms with
`eta = sqrt (log K * gamma / (T * K))` and records the cubic exploration
conditions required by the current Bernstein confidence radii.
-/

namespace BanditRLProof.Exp3

open MeasureTheory ProbabilityTheory

universe u v

/-- Learning rate balancing the entropy and pathwise estimator-square terms
for the current high-probability budget. -/
noncomputable def bernsteinHighProbabilityLearningRate
    (K T gamma : Real) : Real :=
  Real.sqrt (Real.log K * gamma / (T * K))

/-- A cubic exploration budget makes one current Bernstein confidence radius
at most `3 * gamma * T`. -/
theorem bernsteinConfidenceRadius_le_three_mul_gamma_mul_horizon
    (K T budget gamma : Real)
    (hK : 0 < K) (hT : 0 < T) (_hbudget : 0 <= budget)
    (hgamma_pos : 0 < gamma) (hgamma_le_one : gamma <= 1)
    (hcubic : K * budget <= gamma ^ 3 * T) :
    2 * Real.sqrt (T * budget / (gamma / K)) +
        budget / (gamma / K) <=
      3 * gamma * T := by
  have hK_ne : K ≠ 0 := ne_of_gt hK
  have hgamma_ne : gamma ≠ 0 := ne_of_gt hgamma_pos
  have hepsilon_pos : 0 < gamma / K := div_pos hgamma_pos hK
  have hnum : T * (K * budget) <= T * (gamma ^ 3 * T) :=
    mul_le_mul_of_nonneg_left hcubic hT.le
  have hradicand : T * budget / (gamma / K) <= (gamma * T) ^ 2 := by
    calc
      T * budget / (gamma / K) = T * (K * budget) / gamma := by
        field_simp [hK_ne, hgamma_ne]
      _ <= T * (gamma ^ 3 * T) / gamma :=
        (div_le_div_iff_of_pos_right hgamma_pos).2 hnum
      _ = (gamma * T) ^ 2 := by
        field_simp [hgamma_ne]
  have hsqrt :
      Real.sqrt (T * budget / (gamma / K)) <= gamma * T := by
    rw [Real.sqrt_le_iff]
    exact ⟨mul_nonneg hgamma_pos.le hT.le, hradicand⟩
  have hlinear : budget / (gamma / K) <= gamma * T := by
    have hlinear_sq : budget / (gamma / K) <= gamma ^ 2 * T := by
      calc
        budget / (gamma / K) = K * budget / gamma := by
          field_simp [hK_ne, hgamma_ne]
        _ <= gamma ^ 2 * T := by
          rw [div_le_iff₀ hgamma_pos]
          nlinarith [hcubic]
    have hgamma_sq_le : gamma ^ 2 * T <= gamma * T := by
      have hgamma_sq_le_gamma : gamma ^ 2 <= gamma := by
        nlinarith [mul_nonneg hgamma_pos.le (sub_nonneg.mpr hgamma_le_one)]
      exact mul_le_mul_of_nonneg_right hgamma_sq_le_gamma hT.le
    exact hlinear_sq.trans hgamma_sq_le
  linarith

/-- The bounded realized-loss deviation radius is at most `gamma * T` under
its matching quadratic exploration budget. -/
theorem realizedDeviationRadius_le_mul_gamma_mul_horizon
    (T budget variance gamma : Real)
    (hT : 0 < T) (_hbudget : 0 <= budget) (_hvariance : 0 <= variance)
    (hgamma_pos : 0 < gamma)
    (hquadratic : 2 * variance * budget <= gamma ^ 2 * T) :
    Real.sqrt (2 * (T * variance) * budget) <= gamma * T := by
  rw [Real.sqrt_le_iff]
  constructor
  · exact mul_nonneg hgamma_pos.le hT.le
  have hmul := mul_le_mul_of_nonneg_left hquadratic hT.le
  nlinarith

/-- The tuned learning rate is positive in the nondegenerate finite-arm,
positive-horizon regime. -/
theorem bernsteinHighProbabilityLearningRate_pos
    (K T gamma : Real) (hK_one : 1 < K) (hT : 0 < T)
    (hgamma_pos : 0 < gamma) :
    0 < bernsteinHighProbabilityLearningRate K T gamma := by
  apply Real.sqrt_pos.2
  exact div_pos (mul_pos (Real.log_pos hK_one) hgamma_pos)
    (mul_pos hT (lt_trans zero_lt_one hK_one))

/-- Squared balance identity for the tuned learning rate. -/
theorem bernsteinHighProbabilityLearningRate_sq_mul
    (K T gamma : Real) (hK_one : 1 < K) (hT : 0 < T)
    (hgamma_pos : 0 < gamma) :
    bernsteinHighProbabilityLearningRate K T gamma ^ 2 * (T * K) =
      Real.log K * gamma := by
  rw [bernsteinHighProbabilityLearningRate, Real.sq_sqrt]
  · field_simp [ne_of_gt hT, ne_of_gt (lt_trans zero_lt_one hK_one)]
  · exact (div_nonneg
      (mul_nonneg (Real.log_pos hK_one).le hgamma_pos.le)
      (mul_nonneg hT.le (le_of_lt (lt_trans zero_lt_one hK_one))))

/-- The cubic exploration contract places the tuned learning rate below the
scale `gamma ^ 2 / K`. -/
theorem bernsteinHighProbabilityLearningRate_le_sq_div
    (K T gamma : Real) (hK_one : 1 < K) (hT : 0 < T)
    (hgamma_pos : 0 < gamma)
    (hcubic_log : K * Real.log K <= gamma ^ 3 * T) :
    bernsteinHighProbabilityLearningRate K T gamma <= gamma ^ 2 / K := by
  have hK : 0 < K := lt_trans zero_lt_one hK_one
  have hmul := mul_le_mul_of_nonneg_left hcubic_log
    (div_nonneg hgamma_pos.le hK.le)
  rw [bernsteinHighProbabilityLearningRate, Real.sqrt_le_iff]
  constructor
  · exact div_nonneg (sq_nonneg gamma) hK.le
  · rw [div_le_iff₀ (mul_pos hT hK)]
    calc
      Real.log K * gamma = (gamma / K) * (K * Real.log K) := by
        field_simp [ne_of_gt hK]
      _ <= (gamma / K) * (gamma ^ 3 * T) := hmul
      _ = (gamma ^ 2 / K) ^ 2 * (T * K) := by
        field_simp [ne_of_gt hK]

/-- The entropy contribution is at most `gamma * T` under the cubic arm-log
budget. -/
theorem bernsteinEntropyBudget_le_mul_gamma_mul_horizon
    (K T gamma : Real) (hK_one : 1 < K) (hT : 0 < T)
    (hgamma_pos : 0 < gamma)
    (hcubic_log : K * Real.log K <= gamma ^ 3 * T) :
    Real.log K / bernsteinHighProbabilityLearningRate K T gamma <=
      gamma * T := by
  let eta := bernsteinHighProbabilityLearningRate K T gamma
  have hK : 0 < K := lt_trans zero_lt_one hK_one
  have heta : 0 < eta :=
    bernsteinHighProbabilityLearningRate_pos K T gamma hK_one hT hgamma_pos
  have heta_le : eta <= gamma ^ 2 / K :=
    bernsteinHighProbabilityLearningRate_le_sq_div
      K T gamma hK_one hT hgamma_pos hcubic_log
  have hbalance : eta ^ 2 * (T * K) = Real.log K * gamma :=
    bernsteinHighProbabilityLearningRate_sq_mul
      K T gamma hK_one hT hgamma_pos
  have heq : Real.log K / eta = eta * T * K / gamma := by
    field_simp [ne_of_gt heta, ne_of_gt hgamma_pos]
    nlinarith [hbalance]
  rw [heq]
  calc
    eta * T * K / gamma <= (gamma ^ 2 / K) * T * K / gamma := by
      exact div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right heta_le hT.le) hK.le)
        hgamma_pos.le
    _ = gamma * T := by
      field_simp [ne_of_gt hK, ne_of_gt hgamma_pos]

/-- Before the stability factor `1 / (1 - gamma)`, the pathwise square term
has the same tuned scale as the entropy term. -/
theorem bernsteinUnscaledSquareBudget_le_mul_gamma_mul_horizon
    (K T gamma : Real) (hK_one : 1 < K) (hT : 0 < T)
    (hgamma_pos : 0 < gamma)
    (hcubic_log : K * Real.log K <= gamma ^ 3 * T) :
    bernsteinHighProbabilityLearningRate K T gamma *
        (T * (1 / (gamma / K))) <=
      gamma * T := by
  have hK : 0 < K := lt_trans zero_lt_one hK_one
  have heta_le := bernsteinHighProbabilityLearningRate_le_sq_div
    K T gamma hK_one hT hgamma_pos hcubic_log
  calc
    bernsteinHighProbabilityLearningRate K T gamma *
        (T * (1 / (gamma / K))) =
        bernsteinHighProbabilityLearningRate K T gamma * T * K / gamma := by
      field_simp [ne_of_gt hK, ne_of_gt hgamma_pos]
    _ <= (gamma ^ 2 / K) * T * K / gamma := by
      exact div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right heta_le hT.le) hK.le)
        hgamma_pos.le
    _ = gamma * T := by
      field_simp [ne_of_gt hK, ne_of_gt hgamma_pos]

/-- The entropy and pathwise square terms together cost at most
`3 * gamma * T` when `gamma <= 1 / 2`. -/
theorem bernsteinHedgeBudget_le_three_mul_gamma_mul_horizon
    (K T gamma : Real) (hK_one : 1 < K) (hT : 0 < T)
    (hgamma_pos : 0 < gamma) (hgamma_le_half : gamma <= 1 / 2)
    (hcubic_log : K * Real.log K <= gamma ^ 3 * T) :
    Real.log K / bernsteinHighProbabilityLearningRate K T gamma +
        (bernsteinHighProbabilityLearningRate K T gamma *
          (1 / (1 - gamma))) * (T * (1 / (gamma / K))) <=
      3 * gamma * T := by
  have hden : 0 < 1 - gamma := by linarith
  have hentropy := bernsteinEntropyBudget_le_mul_gamma_mul_horizon
    K T gamma hK_one hT hgamma_pos hcubic_log
  have hraw := bernsteinUnscaledSquareBudget_le_mul_gamma_mul_horizon
    K T gamma hK_one hT hgamma_pos hcubic_log
  have hgammaT_nonneg : 0 <= gamma * T :=
    mul_nonneg hgamma_pos.le hT.le
  have hfactor : 1 <= 2 * (1 - gamma) := by linarith
  have hstable :
      (bernsteinHighProbabilityLearningRate K T gamma *
          (1 / (1 - gamma))) * (T * (1 / (gamma / K))) <=
        2 * gamma * T := by
    rw [show
      (bernsteinHighProbabilityLearningRate K T gamma *
          (1 / (1 - gamma))) * (T * (1 / (gamma / K))) =
        (bernsteinHighProbabilityLearningRate K T gamma *
          (T * (1 / (gamma / K)))) / (1 - gamma) by ring]
    rw [div_le_iff₀ hden]
    calc
      bernsteinHighProbabilityLearningRate K T gamma *
          (T * (1 / (gamma / K))) <= gamma * T := hraw
      _ <= (gamma * T) * (2 * (1 - gamma)) :=
        by simpa using mul_le_mul_of_nonneg_left hfactor hgammaT_nonneg
      _ = 2 * gamma * T * (1 - gamma) := by ring
  linarith

/-- Dividing a total failure probability by three changes the logarithmic
budget to `log (3 / delta)`. -/
theorem log_one_div_third_eq_log_three_div (delta : Real) (hdelta : 0 < delta) :
    Real.log (1 / (delta / 3)) = Real.log (3 / delta) := by
  congr 1
  field_simp [ne_of_gt hdelta]

/-- Under the explicit cubic and quadratic dominance contracts, the complete
three-event realized Bernstein budget is at most `11 * gamma * T`. -/
theorem sampledPredictableBernsteinRealizedHighProbabilityRegretBudget_le_eleven_mul
    {Action : Type v} [DecidableEq Action]
    (arms : Finset Action) (hcard_two : 2 <= arms.card)
    (horizon : Nat) (hhorizon : 0 < horizon)
    (gamma delta : Real) (hgamma_pos : 0 < gamma)
    (hgamma_le_half : gamma <= 1 / 2)
    (hdelta : 0 < delta) (hdelta_le_one : delta <= 1)
    (hcubic_log :
      (arms.card : Real) * Real.log (arms.card : Real) <=
        gamma ^ 3 * (horizon : Real))
    (hcubic_confidence :
      (arms.card : Real) * Real.log (3 / delta) <=
        gamma ^ 3 * (horizon : Real))
    (hquadratic_realized :
      2 * ((Concentration.intervalVarianceProxy 0 1 : NNReal) : Real) *
          Real.log (3 / delta) <=
        gamma ^ 2 * (horizon : Real)) :
    sampledPredictableBernsteinRealizedHighProbabilityRegretBudget
        arms
        (bernsteinHighProbabilityLearningRate
          (arms.card : Real) (horizon : Real) gamma)
        gamma horizon (delta / 3) <=
      11 * gamma * (horizon : Real) := by
  let K : Real := arms.card
  let T : Real := horizon
  let budget : Real := Real.log (3 / delta)
  let variance : Real :=
    ((Concentration.intervalVarianceProxy 0 1 : NNReal) : Real)
  have hK_one : 1 < K := by
    dsimp [K]
    exact_mod_cast hcard_two
  have hK : 0 < K := lt_trans zero_lt_one hK_one
  have hT : 0 < T := by
    dsimp [T]
    exact_mod_cast hhorizon
  have hone_lt_three_div : 1 < 3 / delta := by
    rw [lt_div_iff₀ hdelta]
    nlinarith
  have hbudget_pos : 0 < budget := Real.log_pos hone_lt_three_div
  have hlog_third : Real.log (1 / (delta / 3)) = budget := by
    dsimp [budget]
    exact log_one_div_third_eq_log_three_div delta hdelta
  have hmax_third : max (Real.log (1 / (delta / 3))) 0 = budget := by
    rw [hlog_third]
    exact max_eq_left hbudget_pos.le
  have hhedge :
      Real.log K / bernsteinHighProbabilityLearningRate K T gamma +
          (bernsteinHighProbabilityLearningRate K T gamma *
            (1 / (1 - gamma))) * (T * (1 / (gamma / K))) <=
        3 * gamma * T :=
    bernsteinHedgeBudget_le_three_mul_gamma_mul_horizon
      K T gamma hK_one hT hgamma_pos hgamma_le_half (by
        simpa [K, T] using hcubic_log)
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
  dsimp [sampledPredictableBernsteinRealizedHighProbabilityRegretBudget,
    sampledPredictableBernsteinHighProbabilityRegretBudget,
    sampledPurePredictableMinusObservedBernsteinConfidenceRadius,
    sampledComparatorEstimatorBernsteinConfidenceRadius,
    sampledPredictableRealizedDeviationConfidenceRadius]
  rw [hmax_third, hlog_third]
  change
    Real.log K / bernsteinHighProbabilityLearningRate K T gamma +
          (bernsteinHighProbabilityLearningRate K T gamma *
            (1 / (1 - gamma))) * (T * (1 / (gamma / K))) +
        gamma * T +
        (2 * Real.sqrt (T * budget / (gamma / K)) +
          budget / (gamma / K)) +
        (2 * Real.sqrt (T * budget / (gamma / K)) +
          budget / (gamma / K)) +
        Real.sqrt (2 * (T * variance) * budget) <=
      11 * gamma * T
  linarith

/-- Tuned generated realized-regret tail with an explicit `11 * gamma * T`
threshold. The current confidence route yields a `T^(2/3)`-type contract:
the arm entropy and both importance-weighted confidence budgets must be
dominated by `gamma ^ 3 * T`, while the bounded realized deviation uses the
displayed quadratic contract. -/
theorem sampledPredictable_tunedBernsteinRealizedHighProbabilityRegret_tail
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
    (hcubic_log :
      (arms.card : Real) * Real.log (arms.card : Real) <=
        gamma ^ 3 * (horizon : Real))
    (hcubic_confidence :
      (arms.card : Real) * Real.log (3 / delta) <=
        gamma ^ 3 * (horizon : Real))
    (hquadratic_realized :
      2 * ((Concentration.intervalVarianceProxy 0 1 : NNReal) : Real) *
          Real.log (3 / delta) <=
        gamma ^ 2 * (horizon : Real)) :
    let eta := bernsteinHighProbabilityLearningRate
      (arms.card : Real) (horizon : Real) gamma
    let mu := prior ⊗ₘ sampledImportanceWeightedTrajectoryKernel arms harms
      eta gamma hgamma_pos.le (by linarith : gamma <= 1) loss.environment
    mu {sample |
        11 * gamma * (horizon : Real) <=
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
      0 < bernsteinHighProbabilityLearningRate
        (arms.card : Real) (horizon : Real) gamma :=
    bernsteinHighProbabilityLearningRate_pos
      (arms.card : Real) (horizon : Real) gamma hK_one hT hgamma_pos
  have hgamma_lt_one : gamma < 1 := by linarith
  have hbudget :=
    sampledPredictableBernsteinRealizedHighProbabilityRegretBudget_le_eleven_mul
      arms hcard_two horizon hhorizon gamma delta hgamma_pos hgamma_le_half
        hdelta hdelta_le_one hcubic_log hcubic_confidence hquadratic_realized
  have htail :=
    sampledPredictable_bernsteinRealizedHighProbabilityRegret_tail_total_delta
      prior arms harms
        (bernsteinHighProbabilityLearningRate
          (arms.card : Real) (horizon : Real) gamma)
        gamma heta hgamma_pos hgamma_lt_one loss comparator hcomparator
        horizon hhorizon delta hdelta
  dsimp only at htail ⊢
  calc
    (prior ⊗ₘ sampledImportanceWeightedTrajectoryKernel arms harms
        (bernsteinHighProbabilityLearningRate
          (arms.card : Real) (horizon : Real) gamma)
        gamma hgamma_pos.le hgamma_lt_one.le loss.environment)
        {sample |
          11 * gamma * (horizon : Real) <=
            (Finset.range horizon).sum (fun t =>
                sampledTrajectoryRealizedLossAt t sample) -
              (Finset.range horizon).sum (fun t =>
                predictableLossAt loss t sample comparator)} <=
      (prior ⊗ₘ sampledImportanceWeightedTrajectoryKernel arms harms
        (bernsteinHighProbabilityLearningRate
          (arms.card : Real) (horizon : Real) gamma)
        gamma hgamma_pos.le hgamma_lt_one.le loss.environment)
        {sample |
          sampledPredictableBernsteinRealizedHighProbabilityRegretBudget
              arms
                (bernsteinHighProbabilityLearningRate
                  (arms.card : Real) (horizon : Real) gamma)
              gamma horizon (delta / 3) <=
            (Finset.range horizon).sum (fun t =>
                sampledTrajectoryRealizedLossAt t sample) -
              (Finset.range horizon).sum (fun t =>
                predictableLossAt loss t sample comparator)} := by
        apply measure_mono
        intro sample hsample
        exact hbudget.trans hsample
    _ <= ENNReal.ofReal delta := htail

end BanditRLProof.Exp3
