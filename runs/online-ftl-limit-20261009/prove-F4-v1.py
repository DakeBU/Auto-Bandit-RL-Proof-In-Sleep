from append_leaf_v1 import *
append_leaf('F4','''  have hb := meanPredict_bestRegret_average_tendsto_zero y hy
  have heq : ∀ᶠ T : ℕ in atTop,
      comparatorRegret (fun t x => (x - y t)^2) (meanPredict y) u T / (T : ℝ) =
        squaredBestRegret y (meanPredict y) T / (T : ℝ) -
          (u - empiricalMean y T)^2 := by
    filter_upwards [eventually_gt_atTop (0 : ℕ)] with T hT
    rw [meanPredict_comparator_decomposition,
      squaredBestRegret_eq_comparatorRegret y (meanPredict y) T (fun t _ => hy t)]
    have hT0 : (T : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hT
    field_simp
  constructor
  · intro ha
    have hh := hb.sub ha
    simp only [zero_sub] at hh
    apply hh.congr'
    filter_upwards [heq] with T hT
    linarith
  · intro hd
    have hh := hb.sub hd
    simp only [zero_sub, neg_neg] at hh
    apply hh.congr'
    filter_upwards [heq] with T hT
    exact hT.symm
''',requires=['F2','F3'])
