import BanditRLProof.Exp3BernsteinTuning

/-!
# Explicit exploration tuning for realized EXP3 Bernstein confidence

This module discharges the three dominance premises of the characterized
`11 * gamma * T` theorem with an explicit maximum of two cube-root scales and
one square-root scale. The schedule is clipped at `1 / 2`; transparent
large-horizon premises ensure that the clip is inactive.
-/

namespace BanditRLProof.Exp3

open MeasureTheory ProbabilityTheory

universe u v

/-- Cube-root scale required by the arm-entropy term. -/
noncomputable def bernsteinArmEntropyExplorationScale
    (K T : Real) : Real :=
  (K * Real.log K / T) ^ (3 : Real)⁻¹

/-- Cube-root scale required by both importance-weighted Bernstein radii. -/
noncomputable def bernsteinConfidenceExplorationScale
    (K T delta : Real) : Real :=
  (K * Real.log (3 / delta) / T) ^ (3 : Real)⁻¹

/-- Square-root scale required by the bounded realized-deviation radius. -/
noncomputable def bernsteinRealizedExplorationScale
    (T delta : Real) : Real :=
  Real.sqrt
    (2 * ((Concentration.intervalVarianceProxy 0 1 : NNReal) : Real) *
      Real.log (3 / delta) / T)

/-- Unclipped exploration scale simultaneously covering arm entropy, the two
importance-weighted confidence radii, and the realized-deviation radius. -/
noncomputable def bernsteinRawExplorationRate
    (K T delta : Real) : Real :=
  max (bernsteinArmEntropyExplorationScale K T)
    (max (bernsteinConfidenceExplorationScale K T delta)
      (bernsteinRealizedExplorationScale T delta))

/-- Explicit exploration schedule, clipped into the stability regime
`gamma <= 1 / 2`. -/
noncomputable def bernsteinClippedExplorationRate
    (K T delta : Real) : Real :=
  min (1 / 2) (bernsteinRawExplorationRate K T delta)

/-- A cube-root scale is at most one half when its numerator is at most one
eighth of the positive horizon. -/
theorem rpow_inv_three_le_half_of_eight_mul_le
    (numerator T : Real) (hnumerator : 0 <= numerator) (hT : 0 < T)
    (hlarge : 8 * numerator <= T) :
    (numerator / T) ^ (3 : Real)⁻¹ <= 1 / 2 := by
  have hcube :
      ((numerator / T) ^ (3 : Real)⁻¹) ^ (3 : Nat) = numerator / T := by
    convert Real.rpow_inv_natCast_pow (n := 3)
      (div_nonneg hnumerator hT.le) (by norm_num) using 1
  apply le_of_pow_le_pow_left₀ (n := 3) (by norm_num) (by norm_num)
  rw [hcube]
  norm_num
  rw [div_le_iff₀ hT]
  nlinarith

/-- A square-root scale is at most one half when its numerator is at most one
quarter of the positive horizon. -/
theorem sqrt_div_le_half_of_four_mul_le
    (numerator T : Real) (hT : 0 < T)
    (hlarge : 4 * numerator <= T) :
    Real.sqrt (numerator / T) <= 1 / 2 := by
  rw [Real.sqrt_le_iff]
  constructor
  · norm_num
  rw [div_le_iff₀ hT]
  norm_num
  nlinarith

/-- If the cube-root scale is below `gamma`, then the corresponding numerator
obeys the cubic dominance contract. -/
theorem numerator_le_cube_mul_of_rpow_inv_three_le
    (numerator T gamma : Real) (hnumerator : 0 <= numerator) (hT : 0 < T)
    (hroot : (numerator / T) ^ (3 : Real)⁻¹ <= gamma) :
    numerator <= gamma ^ 3 * T := by
  have hroot_nonneg : 0 <= (numerator / T) ^ (3 : Real)⁻¹ :=
    Real.rpow_nonneg (div_nonneg hnumerator hT.le) _
  have hcube :
      ((numerator / T) ^ (3 : Real)⁻¹) ^ (3 : Nat) = numerator / T := by
    convert Real.rpow_inv_natCast_pow (n := 3)
      (div_nonneg hnumerator hT.le) (by norm_num) using 1
  have hpow := pow_le_pow_left₀ hroot_nonneg hroot 3
  rw [hcube] at hpow
  calc
    numerator = (numerator / T) * T := by
      field_simp [ne_of_gt hT]
    _ <= gamma ^ 3 * T := mul_le_mul_of_nonneg_right hpow hT.le

/-- If the square-root scale is below `gamma`, then the corresponding
numerator obeys the quadratic dominance contract. -/
theorem numerator_le_sq_mul_of_sqrt_div_le
    (numerator T gamma : Real) (hnumerator : 0 <= numerator) (hT : 0 < T)
    (hroot : Real.sqrt (numerator / T) <= gamma) :
    numerator <= gamma ^ 2 * T := by
  have hpow := pow_le_pow_left₀ (Real.sqrt_nonneg _) hroot 2
  rw [Real.sq_sqrt (div_nonneg hnumerator hT.le)] at hpow
  calc
    numerator = (numerator / T) * T := by
      field_simp [ne_of_gt hT]
    _ <= gamma ^ 2 * T := mul_le_mul_of_nonneg_right hpow hT.le

/-- The clipped schedule never exceeds the stability threshold. -/
theorem bernsteinClippedExplorationRate_le_half (K T delta : Real) :
    bernsteinClippedExplorationRate K T delta <= 1 / 2 := by
  exact min_le_left _ _

/-- If the raw schedule is already stable, clipping leaves it unchanged. -/
theorem bernsteinClippedExplorationRate_eq_raw
    (K T delta : Real)
    (hraw : bernsteinRawExplorationRate K T delta <= 1 / 2) :
    bernsteinClippedExplorationRate K T delta =
      bernsteinRawExplorationRate K T delta := by
  exact min_eq_right hraw

/-- The raw schedule is positive as soon as there are at least two arms and
the horizon is positive. -/
theorem bernsteinRawExplorationRate_pos
    (K T delta : Real) (hK_one : 1 < K) (hT : 0 < T) :
    0 < bernsteinRawExplorationRate K T delta := by
  have hK : 0 < K := lt_trans zero_lt_one hK_one
  have hbase : 0 < K * Real.log K / T :=
    div_pos (mul_pos hK (Real.log_pos hK_one)) hT
  have hscale : 0 < bernsteinArmEntropyExplorationScale K T := by
    exact Real.rpow_pos_of_pos hbase _
  exact hscale.trans_le (le_max_left _ _)

/-- The clipped schedule remains positive in the nondegenerate finite-arm,
positive-horizon regime. -/
theorem bernsteinClippedExplorationRate_pos
    (K T delta : Real) (hK_one : 1 < K) (hT : 0 < T) :
    0 < bernsteinClippedExplorationRate K T delta := by
  apply lt_min
  · norm_num
  · exact bernsteinRawExplorationRate_pos K T delta hK_one hT

/-- Three transparent horizon inequalities ensure that every raw component is
at most one half, so the clipping branch is inactive. -/
theorem bernsteinRawExplorationRate_le_half_of_horizon_contracts
    (K T delta : Real) (hK_one : 1 < K) (hT : 0 < T)
    (hdelta : 0 < delta) (hdelta_le_one : delta <= 1)
    (hlarge_arm : 8 * (K * Real.log K) <= T)
    (hlarge_confidence : 8 * (K * Real.log (3 / delta)) <= T)
    (hlarge_realized :
      8 * ((Concentration.intervalVarianceProxy 0 1 : NNReal) : Real) *
          Real.log (3 / delta) <= T) :
    bernsteinRawExplorationRate K T delta <= 1 / 2 := by
  have hK : 0 < K := lt_trans zero_lt_one hK_one
  have hlogK : 0 <= Real.log K := (Real.log_pos hK_one).le
  have hone_lt_three_div : 1 < 3 / delta := by
    rw [lt_div_iff₀ hdelta]
    nlinarith
  have hlog_conf : 0 <= Real.log (3 / delta) :=
    (Real.log_pos hone_lt_three_div).le
  have hvariance :
      0 <= ((Concentration.intervalVarianceProxy 0 1 : NNReal) : Real) :=
    NNReal.coe_nonneg _
  rw [bernsteinRawExplorationRate]
  apply max_le
  · exact rpow_inv_three_le_half_of_eight_mul_le
      (K * Real.log K) T (mul_nonneg hK.le hlogK) hT hlarge_arm
  apply max_le
  · exact rpow_inv_three_le_half_of_eight_mul_le
      (K * Real.log (3 / delta)) T (mul_nonneg hK.le hlog_conf) hT
        hlarge_confidence
  · apply sqrt_div_le_half_of_four_mul_le
    · exact hT
    · convert hlarge_realized using 1
      all_goals ring

/-- Under the large-horizon regime, the clipped schedule satisfies positivity,
stability, both cubic dominance contracts, and the realized quadratic
dominance contract required by the tuned tail theorem. -/
theorem bernsteinClippedExplorationRate_contracts
    (K T delta : Real) (hK_one : 1 < K) (hT : 0 < T)
    (hdelta : 0 < delta) (hdelta_le_one : delta <= 1)
    (hlarge_arm : 8 * (K * Real.log K) <= T)
    (hlarge_confidence : 8 * (K * Real.log (3 / delta)) <= T)
    (hlarge_realized :
      8 * ((Concentration.intervalVarianceProxy 0 1 : NNReal) : Real) *
          Real.log (3 / delta) <= T) :
    let gamma := bernsteinClippedExplorationRate K T delta
    0 < gamma ∧ gamma <= 1 / 2 ∧
      K * Real.log K <= gamma ^ 3 * T ∧
      K * Real.log (3 / delta) <= gamma ^ 3 * T ∧
      2 * ((Concentration.intervalVarianceProxy 0 1 : NNReal) : Real) *
          Real.log (3 / delta) <= gamma ^ 2 * T := by
  dsimp only
  let variance : Real :=
    ((Concentration.intervalVarianceProxy 0 1 : NNReal) : Real)
  have hK : 0 < K := lt_trans zero_lt_one hK_one
  have hlogK : 0 <= Real.log K := (Real.log_pos hK_one).le
  have hone_lt_three_div : 1 < 3 / delta := by
    rw [lt_div_iff₀ hdelta]
    nlinarith
  have hlog_conf : 0 <= Real.log (3 / delta) :=
    (Real.log_pos hone_lt_three_div).le
  have hvariance : 0 <= variance := by
    exact NNReal.coe_nonneg _
  have hraw := bernsteinRawExplorationRate_le_half_of_horizon_contracts
    K T delta hK_one hT hdelta hdelta_le_one hlarge_arm hlarge_confidence
      hlarge_realized
  have hclip : bernsteinClippedExplorationRate K T delta =
      bernsteinRawExplorationRate K T delta :=
    bernsteinClippedExplorationRate_eq_raw K T delta hraw
  have harm_component : bernsteinArmEntropyExplorationScale K T <=
      bernsteinClippedExplorationRate K T delta := by
    rw [hclip, bernsteinRawExplorationRate]
    exact le_max_left _ _
  have hconfidence_component :
      bernsteinConfidenceExplorationScale K T delta <=
        bernsteinClippedExplorationRate K T delta := by
    rw [hclip, bernsteinRawExplorationRate]
    exact le_trans (le_max_left _ _) (le_max_right _ _)
  have hrealized_component : bernsteinRealizedExplorationScale T delta <=
      bernsteinClippedExplorationRate K T delta := by
    rw [hclip, bernsteinRawExplorationRate]
    exact le_trans (le_max_right _ _) (le_max_right _ _)
  refine ⟨bernsteinClippedExplorationRate_pos K T delta hK_one hT,
    bernsteinClippedExplorationRate_le_half K T delta, ?_, ?_, ?_⟩
  · exact numerator_le_cube_mul_of_rpow_inv_three_le
      (K * Real.log K) T (bernsteinClippedExplorationRate K T delta)
        (mul_nonneg hK.le hlogK) hT (by
          simpa [bernsteinArmEntropyExplorationScale] using harm_component)
  · exact numerator_le_cube_mul_of_rpow_inv_three_le
      (K * Real.log (3 / delta)) T
        (bernsteinClippedExplorationRate K T delta)
        (mul_nonneg hK.le hlog_conf) hT (by
          simpa [bernsteinConfidenceExplorationScale] using
            hconfidence_component)
  · exact numerator_le_sq_mul_of_sqrt_div_le
      (2 * variance * Real.log (3 / delta)) T
        (bernsteinClippedExplorationRate K T delta)
        (mul_nonneg (mul_nonneg (by norm_num) hvariance) hlog_conf) hT (by
          simpa [bernsteinRealizedExplorationScale, variance] using
            hrealized_component)

/-- Generated realized-regret tail for the explicit clipped maximum of the two
cube-root Bernstein scales and the realized square-root scale. The three
large-horizon premises are sufficient conditions ensuring that clipping is
inactive and all contracts of the characterized `11 * gamma * T` theorem
hold. -/
theorem sampledPredictable_explicitBernsteinRealizedHighProbabilityRegret_tail
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
      8 * ((arms.card : Real) * Real.log (arms.card : Real)) <=
        (horizon : Real))
    (hlarge_confidence :
      8 * ((arms.card : Real) * Real.log (3 / delta)) <=
        (horizon : Real))
    (hlarge_realized :
      8 * ((Concentration.intervalVarianceProxy 0 1 : NNReal) : Real) *
          Real.log (3 / delta) <=
        (horizon : Real)) :
    let gamma := bernsteinClippedExplorationRate
      (arms.card : Real) (horizon : Real) delta
    let eta := bernsteinHighProbabilityLearningRate
      (arms.card : Real) (horizon : Real) gamma
    let mu := prior ⊗ₘ sampledImportanceWeightedTrajectoryKernel arms harms
      eta gamma
        (bernsteinClippedExplorationRate_pos
          (arms.card : Real) (horizon : Real) delta
          (by exact_mod_cast hcard_two)
          (by exact_mod_cast hhorizon)).le
        (by
          exact (bernsteinClippedExplorationRate_le_half
            (arms.card : Real) (horizon : Real) delta).trans (by norm_num))
        loss.environment
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
  have hcontracts := bernsteinClippedExplorationRate_contracts
    (arms.card : Real) (horizon : Real) delta hK_one hT hdelta hdelta_le_one
      hlarge_arm hlarge_confidence hlarge_realized
  dsimp only at hcontracts
  rcases hcontracts with
    ⟨hgamma_pos, hgamma_le_half, hcubic_log, hcubic_confidence,
      hquadratic_realized⟩
  exact sampledPredictable_tunedBernsteinRealizedHighProbabilityRegret_tail
    prior arms harms hcard_two
      (bernsteinClippedExplorationRate
        (arms.card : Real) (horizon : Real) delta)
      hgamma_pos hgamma_le_half loss comparator hcomparator horizon hhorizon
      delta hdelta hdelta_le_one hcubic_log hcubic_confidence
        hquadratic_realized

end BanditRLProof.Exp3
