import BanditRLProof.ConcentrationFixedMGF

/-!
# Quadratic fixed-MGF optimization

This module turns a family of fixed-tilt quadratic exponential tails into a
delta-shaped bound.  The probabilistic construction of each fixed-tilt tail
remains separate, so model-specific consumers only need to expose the common
quadratic exponent and admissible tilt cap.
-/

namespace BanditRLProof.Concentration

open MeasureTheory ProbabilityTheory Real

open scoped ENNReal

/-- Optimize a quadratic fixed-tilt MGF budget when the quadratic coefficient
and admissible tilt cap are separate parameters. -/
theorem exists_tilt_quadratic_fixedMGF_exponent_le_neg
    (horizon variance cap budget : Real)
    (hhorizon : 0 <= horizon) (hvariance : 0 < variance)
    (hcap : 0 < cap) (hbudget : 0 <= budget) :
    exists tilt : Real, 0 <= tilt ∧ tilt <= cap ∧
      -tilt *
          (2 * Real.sqrt (horizon * variance * budget) + budget / cap) +
        horizon * (tilt ^ 2 * variance) <= -budget := by
  by_cases hbudget_zero : budget = 0
  · refine ⟨0, le_rfl, hcap.le, ?_⟩
    simp [hbudget_zero]
  have hbudget_pos : 0 < budget :=
    lt_of_le_of_ne hbudget (Ne.symm hbudget_zero)
  by_cases hsmall : budget <= cap ^ 2 * horizon * variance
  · have hhorizon_pos : 0 < horizon := by
      by_contra h
      have hhorizon_zero : horizon = 0 := le_antisymm (le_of_not_gt h) hhorizon
      simp [hhorizon_zero] at hsmall
      exact (not_lt_of_ge hsmall) hbudget_pos
    let tilt := Real.sqrt (budget / (horizon * variance))
    let scale := Real.sqrt (horizon * variance * budget)
    have htilt_nonneg : 0 <= tilt := Real.sqrt_nonneg _
    have hscale_nonneg : 0 <= scale := Real.sqrt_nonneg _
    have hden_pos : 0 < horizon * variance := mul_pos hhorizon_pos hvariance
    have htilt_sq : tilt ^ 2 = budget / (horizon * variance) := by
      dsimp only [tilt]
      rw [Real.sq_sqrt]
      positivity
    have hscale_sq : scale ^ 2 = horizon * variance * budget := by
      dsimp only [scale]
      rw [Real.sq_sqrt]
      positivity
    have hprod_sq : (tilt * scale) ^ 2 = budget ^ 2 := by
      rw [mul_pow, htilt_sq, hscale_sq]
      field_simp
    have hprod : tilt * scale = budget := by
      nlinarith [mul_nonneg htilt_nonneg hscale_nonneg]
    have htilt_sq_le : tilt ^ 2 <= cap ^ 2 := by
      rw [htilt_sq, div_le_iff₀ hden_pos]
      simpa [mul_assoc, mul_comm, mul_left_comm] using hsmall
    have htilt_le : tilt <= cap :=
      (sq_le_sq₀ htilt_nonneg hcap.le).mp htilt_sq_le
    refine ⟨tilt, htilt_nonneg, htilt_le, ?_⟩
    change -tilt * (2 * scale + budget / cap) +
      horizon * (tilt ^ 2 * variance) <= -budget
    have hbudget_term : horizon * (tilt ^ 2 * variance) = budget := by
      rw [htilt_sq]
      field_simp
    have hextra : 0 <= tilt * (budget / cap) :=
      mul_nonneg htilt_nonneg (div_nonneg hbudget hcap.le)
    rw [hbudget_term]
    nlinarith
  · refine ⟨cap, hcap.le, le_rfl, ?_⟩
    let scale := Real.sqrt (horizon * variance * budget)
    have hscale_nonneg : 0 <= scale := Real.sqrt_nonneg _
    have hscale_sq : scale ^ 2 = horizon * variance * budget := by
      dsimp only [scale]
      rw [Real.sq_sqrt]
      positivity
    have hlarge : cap ^ 2 * horizon * variance < budget := lt_of_not_ge hsmall
    have hhv_nonneg : 0 <= horizon * variance :=
      mul_nonneg hhorizon hvariance.le
    have hbase_sq : (horizon * variance * cap) ^ 2 <= scale ^ 2 := by
      rw [hscale_sq]
      have hmul := mul_le_mul_of_nonneg_right hlarge.le hhv_nonneg
      nlinarith
    have hbase_nonneg : 0 <= horizon * variance * cap :=
      mul_nonneg hhv_nonneg hcap.le
    have hbase_le : horizon * variance * cap <= scale :=
      (sq_le_sq₀ hbase_nonneg hscale_nonneg).mp hbase_sq
    have hcover : horizon * variance * cap ^ 2 <= 2 * cap * scale := by
      calc
        horizon * variance * cap ^ 2 = cap * (horizon * variance * cap) := by ring
        _ <= cap * scale := mul_le_mul_of_nonneg_left hbase_le hcap.le
        _ <= 2 * cap * scale := by
          nlinarith [mul_nonneg hcap.le hscale_nonneg]
    calc
      -cap * (2 * Real.sqrt (horizon * variance * budget) + budget / cap) +
          horizon * (cap ^ 2 * variance) =
        -2 * cap * scale - budget + horizon * variance * cap ^ 2 := by
          field_simp
          ring
      _ <= -budget := by nlinarith

/-- Radius obtained by optimizing a quadratic fixed-tilt exponent over
`0 <= tilt <= tiltCap`. -/
noncomputable def quadraticFixedMGFRadius
    (varianceScale varianceBudget tiltCap delta : Real) : Real :=
  let budget := max (Real.log (1 / delta)) 0
  2 * Real.sqrt (varianceScale * varianceBudget * budget) + budget / tiltCap

/-- A family of fixed-tilt quadratic tails yields a delta-shaped joint
deviation and variance-budget tail. -/
theorem measure_deviation_ge_inter_variance_le_delta_of_fixedTilt_quadratic_tail
    {Omega : Type*} [MeasurableSpace Omega]
    (mu : Measure Omega) (deviation predictableVariance : Omega -> Real)
    (varianceScale varianceBudget tiltCap delta : Real)
    (hvarianceScale : 0 < varianceScale)
    (hvarianceBudget : 0 < varianceBudget) (htiltCap : 0 < tiltCap)
    (hdelta : 0 < delta)
    (hfixed : forall tilt, 0 <= tilt -> tilt <= tiltCap ->
      mu {omega |
          quadraticFixedMGFRadius varianceScale varianceBudget tiltCap delta <=
              deviation omega ∧
            predictableVariance omega <= varianceBudget} <=
        ENNReal.ofReal (Real.exp
          (-tilt * quadraticFixedMGFRadius
              varianceScale varianceBudget tiltCap delta +
            varianceScale * (tilt ^ 2 * varianceBudget)))) :
    mu {omega |
        quadraticFixedMGFRadius varianceScale varianceBudget tiltCap delta <=
            deviation omega ∧
          predictableVariance omega <= varianceBudget} <=
      ENNReal.ofReal delta := by
  let budget := max (Real.log (1 / delta)) 0
  let radius :=
    2 * Real.sqrt (varianceScale * varianceBudget * budget) + budget / tiltCap
  have hbudget : 0 <= budget := le_max_right _ _
  obtain ⟨tilt, htilt_nonneg, htilt_le, hexponent⟩ :=
    exists_tilt_quadratic_fixedMGF_exponent_le_neg
      varianceScale varianceBudget tiltCap budget hvarianceScale.le
        hvarianceBudget htiltCap hbudget
  have htail := hfixed tilt htilt_nonneg htilt_le
  have hexponent' :
      -tilt * radius + varianceScale * (tilt ^ 2 * varianceBudget) <=
        -budget := by
    simpa [radius, mul_assoc] using hexponent
  have hbudget_tail :
      mu {omega | radius <= deviation omega ∧
          predictableVariance omega <= varianceBudget} <=
        ENNReal.ofReal (Real.exp (-budget)) := by
    have htail' :
        mu {omega | radius <= deviation omega ∧
            predictableVariance omega <= varianceBudget} <=
          ENNReal.ofReal (Real.exp
            (-tilt * radius + varianceScale * (tilt ^ 2 * varianceBudget))) := by
      simpa [quadraticFixedMGFRadius, radius, budget] using htail
    exact htail'.trans
      (ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr hexponent'))
  have hscale : 0 < 1 / delta := one_div_pos.mpr hdelta
  have hexp_le_delta : Real.exp (-budget) <= delta := by
    by_cases hdelta_le_one : delta <= 1
    · have hone_le_inv : 1 <= 1 / delta := by
        simpa using one_div_le_one_div_of_le hdelta hdelta_le_one
      have hlog_nonneg : 0 <= Real.log (1 / delta) :=
        Real.log_nonneg hone_le_inv
      have hbudget_eq : budget = Real.log (1 / delta) :=
        max_eq_left hlog_nonneg
      rw [hbudget_eq, Real.exp_neg, Real.exp_log hscale]
      field_simp
      exact le_rfl
    · have hone_lt_delta : 1 < delta := lt_of_not_ge hdelta_le_one
      have hinv_le_one : 1 / delta <= 1 := by
        simpa using one_div_le_one_div_of_le (by norm_num : (0 : Real) < 1)
          hone_lt_delta.le
      have hlog_nonpos : Real.log (1 / delta) <= 0 :=
        Real.log_nonpos hscale.le hinv_le_one
      have hbudget_eq : budget = 0 := max_eq_right hlog_nonpos
      rw [hbudget_eq, neg_zero, Real.exp_zero]
      exact hone_lt_delta.le
  have hfinal := hbudget_tail.trans (ENNReal.ofReal_le_ofReal hexp_le_delta)
  simpa [quadraticFixedMGFRadius, radius, budget] using hfinal

end BanditRLProof.Concentration
