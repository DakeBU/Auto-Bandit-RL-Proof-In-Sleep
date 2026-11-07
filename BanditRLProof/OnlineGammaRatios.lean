import Mathlib

namespace BanditRL.OnlineGamma
noncomputable section

private theorem gamma_step_upper (x s : ℝ) (hx : 0 < x) (hs₀ : 0 < s) (hs₁ : s < 1) :
    Real.Gamma (x + s) ≤ x ^ s * Real.Gamma x := by
  have gx := Real.Gamma_pos_of_pos hx
  have h := Real.Gamma_mul_add_mul_le_rpow_Gamma_mul_rpow_Gamma hx
    (show 0 < x + 1 by linarith) (show 0 < 1 - s by linarith) hs₀ (by ring)
  rw [show (1-s)*x+s*(x+1)=x+s by ring, Real.Gamma_add_one hx.ne',
    Real.mul_rpow hx.le gx.le] at h
  calc
    _ ≤ _ := h
    _ = x ^ s * (Real.Gamma x ^ (1-s) * Real.Gamma x ^ s) := by ring
    _ = _ := by rw [← Real.rpow_add gx, sub_add_cancel, Real.rpow_one]

theorem gamma_wendel_ratio (x s : ℝ) (hx : 0 < x) (hs₀ : 0 < s) (hs₁ : s < 1) :
  (x / (x + s)) ^ (1 - s) ≤ Real.Gamma (x + s) / (x ^ s * Real.Gamma x) ∧
  Real.Gamma (x + s) / (x ^ s * Real.Gamma x) ≤ 1 := by
  have den := mul_pos (Real.rpow_pos_of_pos hx s) (Real.Gamma_pos_of_pos hx)
  have hxs : 0 < x+s := by linarith
  have shifted := gamma_step_upper (x+s) (1-s) hxs (by linarith) (by linarith)
  rw [show x+s+(1-s)=x+1 by ring, Real.Gamma_add_one hx.ne'] at shifted
  constructor
  · apply (le_div_iff₀ den).2
    calc
      _ = (x ^ (1-s) * x ^ s) * Real.Gamma x / (x+s) ^ (1-s) := by
        rw [Real.div_rpow hx.le hxs.le]; ring
      _ = x * Real.Gamma x / (x+s) ^ (1-s) := by rw [← Real.rpow_add hx, sub_add_cancel, Real.rpow_one]
      _ ≤ _ := (div_le_iff₀ (Real.rpow_pos_of_pos hxs _)).2 (by simpa [mul_comm] using shifted)
  · exact (div_le_one den).2 (gamma_step_upper x s hx hs₀ hs₁)

theorem gamma_ratio_dimension_two (T : ℕ) (hT : 1 ≤ T) :
  Real.Gamma ((T : ℝ) + 1) / Real.Gamma ((T : ℝ) + 1 / 2) ≤
  ((T : ℝ) + 1 / 2) ^ (1 / 2 : ℝ) := by
  have ht : (1:ℝ) ≤ T := by exact_mod_cast hT
  have hx : 0 < (T:ℝ) + 1/2 := by linarith
  have hu := (gamma_wendel_ratio ((T:ℝ)+1/2) (1/2) hx (by norm_num) (by norm_num)).2
  have g := Real.Gamma_pos_of_pos hx
  have hh := (div_le_one (mul_pos (Real.rpow_pos_of_pos hx (1/2)) g)).mp hu
  apply (div_le_iff₀ g).2
  convert hh using 1 <;> ring_nf

theorem log_gamma_ratio_dimension_two (T : ℕ) (hT : 1 ≤ T) :
  Real.log (Real.sqrt Real.pi * Real.Gamma ((T : ℝ) + 1) /
    (Real.Gamma 1 * Real.Gamma ((T : ℝ) + 1 / 2))) ≤
    (1 / 2 : ℝ) * Real.log (Real.pi * (T : ℝ) + Real.pi / 2) ∧
  (1 / 2 : ℝ) * Real.log (Real.pi * (T : ℝ) + Real.pi / 2) ≤
    (1 / 2 : ℝ) * Real.log (T : ℝ) + 1 := by
  have ht : (1:ℝ) ≤ T := by exact_mod_cast hT
  have ht0 : 0 < (T:ℝ) := by linarith
  have hx : 0 < (T:ℝ) + 1/2 := by linarith
  have hp := Real.pi_pos
  have hr := gamma_ratio_dimension_two T hT
  rw [← Real.sqrt_eq_rpow] at hr
  constructor
  · rw [Real.Gamma_one, one_mul, mul_div_assoc]
    have lpos := mul_pos (Real.sqrt_pos.2 hp)
      (div_pos (Real.Gamma_pos_of_pos (by linarith : 0 < (T:ℝ)+1)) (Real.Gamma_pos_of_pos hx))
    have h := Real.log_le_log lpos (mul_le_mul_of_nonneg_left hr (Real.sqrt_nonneg _))
    rw [← Real.sqrt_mul hp.le, Real.log_sqrt (mul_nonneg hp.le hx.le)] at h
    convert h using 1 <;> ring_nf
  · have e := Real.exp_one_gt_d9
    have e2 : (6:ℝ) ≤ Real.exp 1 * Real.exp 1 := by nlinarith [sq_nonneg (Real.exp 1 - 2.7)]
    have hpi : Real.pi * (T:ℝ) + Real.pi/2 ≤ (T:ℝ)*(Real.exp 1 * Real.exp 1) := by
      nlinarith [mul_nonneg (sub_nonneg.mpr ht) hp.le, mul_nonneg (sub_nonneg.mpr Real.pi_lt_four.le) ht0.le,
        mul_nonneg (sub_nonneg.mpr e2) ht0.le, Real.pi_lt_four]
    have h := Real.log_le_log (show 0 < Real.pi * (T:ℝ)+Real.pi/2 by positivity) hpi
    rw [Real.log_mul ht0.ne' (mul_pos (Real.exp_pos _) (Real.exp_pos _)).ne',
      Real.log_mul (Real.exp_pos _).ne' (Real.exp_pos _).ne', Real.log_exp] at h
    linarith
end
end BanditRL.OnlineGamma
