from body_repair import *
repair('switching_scalar_lower_bound',2,[
 ('''    simp only [show -α + 1 = β by dsimp [β]; ring, Real.one_rpow] at h''','''    simp only [show -α + 1 = β by dsimp [β]; ring, Nat.cast_one, Real.one_rpow] at h'''),
 ('''    have h := hm.integral_le_sum_Ico (Nat.zero_le T)
    rw [integral_rpow (Or.inl (by linarith : -1 < β)),
      Real.zero_rpow hbp.ne', sub_zero, Nat.Ico_zero_eq_range] at h''','''    have hm' : MonotoneOn (fun x : ℝ => x ^ β) (Set.Icc ((0 : ℕ) : ℝ) T) := by simpa using hm
    have h := hm'.integral_le_sum_Ico (Nat.zero_le T)
    rw [integral_rpow (Or.inl (by linarith : -1 < β)), Nat.cast_zero,
      Real.zero_rpow hbp.ne', sub_zero, Nat.Ico_zero_eq_range] at h'''),
 ('''    rw [he] at hreg
    linarith''','''    rw [he] at hreg
    linear_combination hreg + hmdiv + hldiv + hinv'''),
 ('''  rw [hpow] at happrox
  nlinarith''','''  rw [hpow] at happrox
  linear_combination happrox + hmul''')],
 'Integral endpoints cast1/cast0 were not normalized or definitionally matching; linarith treated signed division/inverse-product forms as unrelated atoms',
 'Normalize concrete natural endpoints and use exact linear_combination of proved inequalities so ring normalization identifies division expressions. Source bounds/threshold untouched.')
