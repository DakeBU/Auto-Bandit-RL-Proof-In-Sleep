import BanditRLProof.RL.FiniteHorizonAdaptiveCumulativeUCBVITransitionValueConfidence

/-! Fixed-tilt arithmetic used by the finite UCBVI confidence union. -/

namespace BanditRLProof.FiniteHorizonRL.AdaptiveCumulativeHoeffdingUCBVI

/-- Bernstein tilt optimized for a deterministic variance budget, totalized at
zero variance. -/
noncomputable def bernsteinTilt (logBudget varianceBudget : Real) : Real :=
  if varianceBudget = 0 then 1
  else min 1 (Real.sqrt (2 * logBudget / varianceBudget))

noncomputable def bernsteinCoordinateThreshold
    (logBudget varianceBudget : Real) : Real :=
  2 * Real.sqrt (2 * varianceBudget * logBudget) + 2 * logBudget

theorem bernsteinTilt_pos
    {logBudget varianceBudget : Real}
    (hlog : 0 < logBudget) (hvariance : 0 <= varianceBudget) :
    0 < bernsteinTilt logBudget varianceBudget := by
  unfold bernsteinTilt
  split
  · norm_num
  · apply lt_min (by norm_num)
    exact Real.sqrt_pos.2 (div_pos (mul_pos (by norm_num) hlog)
      (lt_of_le_of_ne hvariance (Ne.symm ‹varianceBudget ≠ 0›)))

theorem bernsteinTilt_le_one
    (logBudget varianceBudget : Real) :
    bernsteinTilt logBudget varianceBudget <= 1 := by
  unfold bernsteinTilt
  split <;> simp

theorem bernsteinTilt_abs_le_one
    {logBudget varianceBudget : Real}
    (hlog : 0 < logBudget) (hvariance : 0 <= varianceBudget) :
    |bernsteinTilt logBudget varianceBudget| <= 1 := by
  rw [abs_of_pos (bernsteinTilt_pos hlog hvariance)]
  exact bernsteinTilt_le_one _ _

theorem bernsteinTilt_exponent_le
    {logBudget varianceBudget : Real}
    (hlog : 0 < logBudget) (hvariance : 0 <= varianceBudget) :
    -bernsteinTilt logBudget varianceBudget *
          bernsteinCoordinateThreshold logBudget varianceBudget +
        bernsteinTilt logBudget varianceBudget ^ 2 * varianceBudget <=
      -2 * logBudget := by
  by_cases hzero : varianceBudget = 0
  · subst varianceBudget
    simp [bernsteinTilt, bernsteinCoordinateThreshold]
  have hvariancePos : 0 < varianceBudget := lt_of_le_of_ne hvariance (Ne.symm hzero)
  let s := Real.sqrt (2 * logBudget / varianceBudget)
  let q := Real.sqrt (2 * varianceBudget * logBudget)
  have hs0 : 0 <= s := Real.sqrt_nonneg _
  have hq0 : 0 <= q := Real.sqrt_nonneg _
  have hs_sq : s ^ 2 = 2 * logBudget / varianceBudget := by
    exact Real.sq_sqrt (div_nonneg (mul_nonneg (by norm_num) hlog.le)
      hvariance)
  have hq_sq : q ^ 2 = 2 * varianceBudget * logBudget := by
    exact Real.sq_sqrt (mul_nonneg
      (mul_nonneg (by norm_num) hvariance) hlog.le)
  have hs_mul_q : s * q = 2 * logBudget := by
    have hsqrtVar : Real.sqrt varianceBudget ≠ 0 := by
      exact ne_of_gt (Real.sqrt_pos.2 hvariancePos)
    have hs_repr : s = Real.sqrt (2 * logBudget) /
        Real.sqrt varianceBudget := by
      simp only [s]
      rw [Real.sqrt_div (mul_nonneg (by norm_num) hlog.le)]
    have hq_repr : q = Real.sqrt (2 * logBudget) *
        Real.sqrt varianceBudget := by
      simp only [q]
      rw [show 2 * varianceBudget * logBudget =
          (2 * logBudget) * varianceBudget by ring]
      rw [Real.sqrt_mul (mul_nonneg (by norm_num) hlog.le)]
    rw [hs_repr, hq_repr]
    field_simp
    rw [Real.sq_sqrt (mul_nonneg (by norm_num) hlog.le)]
  rw [bernsteinTilt, if_neg hzero]
  change -min 1 s * (2 * q + 2 * logBudget) +
      min 1 s ^ 2 * varianceBudget <= -2 * logBudget
  by_cases hs : s <= 1
  · rw [min_eq_right hs]
    have hsqBudget : s ^ 2 * varianceBudget = 2 * logBudget := by
      rw [hs_sq]
      field_simp
    nlinarith [hs_mul_q]
  · have hone : 1 <= s := le_of_not_ge hs
    rw [min_eq_left hone]
    have hvariance_le : varianceBudget <= 2 * logBudget := by
      have honeSq : (1 : Real) ^ 2 <= s ^ 2 :=
        (sq_le_sq₀ (by norm_num) hs0).2 hone
      rw [hs_sq] at honeSq
      have hmul := (le_div_iff₀ hvariancePos).mp honeSq
      nlinarith
    have hvariance_le_q : varianceBudget <= q := by
      apply (sq_le_sq₀ hvariance hq0).1
      rw [hq_sq]
      nlinarith
    nlinarith

end BanditRLProof.FiniteHorizonRL.AdaptiveCumulativeHoeffdingUCBVI
