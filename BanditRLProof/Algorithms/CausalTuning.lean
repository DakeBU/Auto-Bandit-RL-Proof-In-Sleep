import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic

/-! The fixed source tuning used for the causal importance estimator. -/
namespace BanditRLProof.Causal
set_option autoImplicit false

noncomputable def sourceThreshold (m T L : ℝ) : ℝ := Real.sqrt (m*T/L)

noncomputable def sourceRadius (m T L : ℝ) : ℝ :=
  Real.sqrt (2*m*L/T) + 3*sourceThreshold m T L*L/T

noncomputable def sourceLog (T K : ℕ) : ℝ := Real.log (2*(T:ℝ)*K)

theorem sourceLog_pos (T K : ℕ) (hT : 0 < T) (hK : 0 < K) : 0 < sourceLog T K := by
  have hT' : (1:ℝ) ≤ T := by exact_mod_cast hT
  have hK' : (1:ℝ) ≤ K := by exact_mod_cast hK
  apply Real.log_pos
  nlinarith

theorem sourceLog_union_budget (T K : ℕ) (hT : 0 < T) (hK : 0 < K) :
    (K:ℝ)*(2*Real.exp (-sourceLog T K)) = 1/(T:ℝ) := by
  have hT' : (0:ℝ) < T := by exact_mod_cast hT
  have hK' : (0:ℝ) < K := by exact_mod_cast hK
  rw [Real.exp_neg, sourceLog, Real.exp_log (by positivity)]
  field_simp

theorem sourceThreshold_pos (m T L : ℝ) (hm : 0 < m) (hT : 0 < T) (hL : 0 < L) :
    0 < sourceThreshold m T L := Real.sqrt_pos.2 (div_pos (mul_pos hm hT) hL)

theorem sourceThreshold_sq (m T L : ℝ) (hm : 0 ≤ m) (hT : 0 ≤ T) (hL : 0 ≤ L) :
    (sourceThreshold m T L)^2 = m*T/L := Real.sq_sqrt (div_nonneg (mul_nonneg hm hT) hL)

theorem sourceTilt_admissible (m T L : ℝ) (hm : 0 < m) (hT : 0 < T) (hL : 0 < L) :
    |1/(2*sourceThreshold m T L)| * (2*sourceThreshold m T L) ≤ 1 := by
  have hB := sourceThreshold_pos m T L hm hT hL
  rw [abs_of_pos (div_pos zero_lt_one (mul_pos (by norm_num) hB))]
  exact (div_mul_cancel₀ 1 (ne_of_gt (mul_pos (by norm_num) hB))).le

theorem sourceTilt_budget (m T L : ℝ) (hm : 0 < m) (hT : 0 < T) (hL : 0 < L) :
    T * ((1/(2*sourceThreshold m T L))^2*m) = L/4 := by
  have hB := sourceThreshold_pos m T L hm hT hL
  have hsq := sourceThreshold_sq m T L hm.le hT.le hL.le
  have hprod : (sourceThreshold m T L)^2 * L = m*T :=
    (eq_div_iff hL.ne').mp hsq
  field_simp
  nlinarith

theorem sourceTilt_exponent_le (m T L : ℝ) (hm : 0 < m) (hT : 0 < T) (hL : 0 < L) :
    -(1/(2*sourceThreshold m T L)) * (T*sourceRadius m T L) +
      T * ((1/(2*sourceThreshold m T L))^2*m) ≤ -L := by
  have hB := sourceThreshold_pos m T L hm hT hL
  have ht : 0 < 1/(2*sourceThreshold m T L) := by positivity
  have hr : 3*sourceThreshold m T L*L/T ≤ sourceRadius m T L := by
    unfold sourceRadius
    linarith [Real.sqrt_nonneg (2*m*L/T)]
  rw [sourceTilt_budget m T L hm hT hL]
  calc
    -(1/(2*sourceThreshold m T L)) * (T*sourceRadius m T L) + L/4 ≤
        -(1/(2*sourceThreshold m T L)) * (T*(3*sourceThreshold m T L*L/T)) + L/4 := by
      have h := mul_le_mul_of_nonneg_left hr hT.le
      nlinarith [mul_le_mul_of_nonpos_left h (neg_nonpos.mpr ht.le)]
    _ = -(5*L)/4 := by field_simp; ring
    _ ≤ -L := by linarith

theorem sourceThreshold_scale (m T L : ℝ) (hm : 0 < m) (hT : 0 < T) (hL : 0 < L) :
    sourceThreshold m T L * L / T = Real.sqrt (m*L/T) := by
  have hB := sourceThreshold_pos m T L hm hT hL
  have hsq := sourceThreshold_sq m T L hm.le hT.le hL.le
  have hrad := Real.sq_sqrt (show 0 ≤ m*L/T by positivity)
  have hleft : 0 ≤ sourceThreshold m T L * L / T := by positivity
  have heq : (sourceThreshold m T L * L / T)^2 = m*L/T := by
    rw [div_pow, mul_pow, hsq]
    field_simp
  nlinarith [Real.sqrt_nonneg (m*L/T)]

theorem sourceThreshold_bias_scale (m T L : ℝ) (hm : 0 < m) (hT : 0 < T) (hL : 0 < L) :
    m/sourceThreshold m T L = Real.sqrt (m*L/T) := by
  have hB := sourceThreshold_pos m T L hm hT hL
  have hsq := sourceThreshold_sq m T L hm.le hT.le hL.le
  rw [← sourceThreshold_scale m T L hm hT hL]
  apply (div_eq_iff hB.ne').mpr
  have hprod := (eq_div_iff hL.ne').mp hsq
  field_simp
  nlinarith [hprod]

theorem sourceRegret_scale (m T L : ℝ) (hm : 0 < m) (hT : 0 < T) (hL : 0 < L) :
    2*sourceRadius m T L + m/sourceThreshold m T L =
      (2*Real.sqrt 2+7)*Real.sqrt (m*L/T) := by
  have hroot : Real.sqrt (2*m*L/T) = Real.sqrt 2 * Real.sqrt (m*L/T) := by
    rw [← Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 2)]
    congr 1
    ring
  unfold sourceRadius
  rw [sourceThreshold_bias_scale m T L hm hT hL, hroot]
  have hscale := sourceThreshold_scale m T L hm hT hL
  calc
    _ = 2*(Real.sqrt 2*Real.sqrt (m*L/T) + 3*(sourceThreshold m T L*L/T)) + Real.sqrt (m*L/T) := by ring
    _ = _ := by rw [hscale]; ring

theorem sourceLog_half_le (T K : ℕ) (hT : 0 < T) (hK : 0 < K) :
    (1:ℝ)/2 ≤ sourceLog T K := by
  have ht : (1:ℝ) ≤ T := by exact_mod_cast hT
  have hk : (1:ℝ) ≤ K := by exact_mod_cast hK
  have h2 : (1:ℝ)/2 ≤ Real.log 2 := by
    have h := Real.one_sub_inv_le_log_of_pos (by norm_num : (0:ℝ) < 2)
    norm_num at h ⊢
    exact h
  exact h2.trans (Real.log_le_log (by norm_num) (by nlinarith))

theorem sourceResidual_le_scale (m : ℝ) (hm : 1 ≤ m) (T K : ℕ)
    (hT : 0 < T) (hK : 0 < K) :
    1/(T:ℝ) ≤ Real.sqrt 2 * Real.sqrt (m*sourceLog T K/T) := by
  have ht : (1:ℝ) ≤ T := by exact_mod_cast hT
  have ht0 : (0:ℝ) < T := by exact_mod_cast hT
  have hl := sourceLog_half_le T K hT hK
  have hml : (1:ℝ)/2 ≤ m*sourceLog T K := by nlinarith
  have hprod : 1 ≤ 2*m*sourceLog T K*(T:ℝ) := by nlinarith
  have hs := Real.sq_sqrt (show 0 ≤ m*sourceLog T K/T by positivity)
  have hs2 : (Real.sqrt 2)^2 = 2 := Real.sq_sqrt (by norm_num)
  have hsq : (Real.sqrt 2 * Real.sqrt (m*sourceLog T K/T) * (T:ℝ))^2 =
      2*m*sourceLog T K*(T:ℝ) := by
    rw [mul_pow, mul_pow, hs2, hs]
    field_simp
  apply (div_le_iff₀ ht0).mpr
  have hnon : 0 ≤ Real.sqrt 2 * Real.sqrt (m*sourceLog T K/T) * (T:ℝ) := by positivity
  nlinarith

end BanditRLProof.Causal
