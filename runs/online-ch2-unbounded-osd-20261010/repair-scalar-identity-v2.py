from body_repair import *
repair('switching_scalar_regret_identity',2,[
 ('''  let m : ℕ := (T + 1) / 2
  let k : ℕ := T / 2''','''  have hin (a b : ℝ) : inner ℝ a b = b * a := rfl
  let m : ℕ := (T + 1) / 2
  let k : ℕ := T / 2'''),
 ('show switchSlope T n = -1 by simp [switchSlope, ← m, hn]','show switchSlope T n = -1 by change (if n < m then (-1 : ℝ) else 1) = -1; exact if_pos hn'),
 ('show switchSlope T n = 1 by simp [switchSlope, ← m, hn]','show switchSlope T n = 1 by change (if n < m then (-1 : ℝ) else 1) = 1; exact if_neg hn'),
 ('show switchSlope T i = -1 by simp [switchSlope, ← m, him]','show switchSlope T i = -1 by change (if i < m then (-1 : ℝ) else 1) = -1; exact if_pos him'),
 ('show switchSlope T i = 1 by simp [switchSlope, ← m, not_lt.mpr him]','show switchSlope T i = 1 by change (if i < m then (-1 : ℝ) else 1) = 1; exact if_neg (not_lt.mpr him)'),
 ('simp [switchLoss, mul_comm]','simp [switchLoss, hin, mul_comm]'),
 ('''    simp only [hrun, EReal.toReal_coe, switchLoss, RCLike.inner_apply, conj_trivial,
      mul_one, mul_zero, sub_zero]''','''    simp only [EReal.toReal_coe]
    simp_rw [hrun]
    simp only [switchLoss, hin, mul_one, mul_zero, sub_zero]''')],
 'Local let names cannot be simp-refolded; concrete Real inner uses toInnerProductSpaceReal rather than the RCLike scalar instance; unfolding switchLoss too early erased syntactic trajectory rewrite',
 'Expose local if by change; prove actual concrete inner equation by rfl; rewrite canonical trajectory before unfolding loss definition. Same finite sum derivation and terminal.')
