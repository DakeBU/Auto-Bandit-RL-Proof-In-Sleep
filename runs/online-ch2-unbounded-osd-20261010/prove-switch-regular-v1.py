from leaf_driver import *
assert load(RUN/'phi_limit-fence-compared-v2.json')['unchanged']
lower('switching_loss_regular','''  constructor
  · refine ⟨convex_univ, ?_⟩
    intro x hx y hy a b ha hb hab
    dsimp [switchLoss]
    simp only [inner_add_right, inner_smul_right, smul_eq_mul]
    exact le_of_eq (by ring)
  · apply LipschitzWith.mk_one
    intro x y
    have hs : |switchSlope T t| = 1 := by
      unfold switchSlope
      split <;> norm_num
    calc
      dist (switchLoss T v t x) (switchLoss T v t y) =
          |switchSlope T t| * |inner ℝ v (x - y)| := by
        rw [Real.dist_eq]
        simp only [switchLoss, inner_sub_right, mul_sub, abs_mul]
      _ ≤ 1 * (‖v‖ * ‖x - y‖) := by
        rw [hs]
        exact mul_le_mul_of_nonneg_left (abs_real_inner_le_norm v (x - y)) zero_le_one
      _ = dist x y := by rw [hv, one_mul, one_mul, dist_eq_norm]
''',['actual real affine algebra','abs_real_inner_le_norm Cauchy-Schwarz primary mathlib API','switchSlope definition ±1'])
write(RUN/'switching-regular-local-milestone-v1.json',dict(leaf=targets['switching_loss_regular']['name'],status='focused compiled/frozen only',algorithm_lower_bound_open=True,phi_range_open=True,BODY_accepted=False,whole_Goal='ACTIVE'))
