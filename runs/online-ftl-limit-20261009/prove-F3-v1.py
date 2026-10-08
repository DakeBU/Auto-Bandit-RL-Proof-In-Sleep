from append_leaf_v1 import *
append_leaf('F3','''  have hlo : ∀ᶠ T : ℕ in atTop,
      0 ≤ squaredBestRegret y (meanPredict y) T / (T : ℝ) := by
    apply Eventually.of_forall
    intro T
    rw [squaredBestRegret_eq_comparatorRegret y (meanPredict y) T (fun t _ => hy t)]
    exact div_nonneg (meanPredict_bestLoss_nonneg y T) (Nat.cast_nonneg T)
  have hup : ∀ᶠ T : ℕ in atTop,
      squaredBestRegret y (meanPredict y) T / (T : ℝ) ≤
        (4 + 4 * Real.log (T : ℝ)) / (T : ℝ) := by
    filter_upwards [eventually_gt_atTop (0 : ℕ)] with T hT
    exact div_le_div_of_nonneg_right
      (meanPredict_bestRegret_bound y T hT (fun t _ => hy t)) (Nat.cast_nonneg T)
  have h0 : Tendsto (fun x : ℝ => 1 / x) atTop (nhds 0) := by
    simpa using Real.tendsto_pow_log_div_mul_add_atTop 1 0 0 one_ne_zero
  have h1 : Tendsto (fun x : ℝ => Real.log x / x) atTop (nhds 0) := by
    simpa using Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero
  have hc : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have hbound : Tendsto (fun T : ℕ => (4 + 4 * Real.log (T : ℝ)) / (T : ℝ))
      atTop (nhds 0) := by
    have hh := ((h0.comp hc).const_mul 4).add ((h1.comp hc).const_mul 4)
    simp only [mul_zero, add_zero] at hh
    convert hh using 1
    ext T
    dsimp [Function.comp_def]
    ring
  exact squeeze_zero' hlo hup hbound
''',requires=['F1'])
