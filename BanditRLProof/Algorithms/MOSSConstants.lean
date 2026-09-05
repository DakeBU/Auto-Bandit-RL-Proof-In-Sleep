import Mathlib.Analysis.SpecialFunctions.Log.Monotone
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Tactic
import BanditRLProof.Algorithms.MOSS

noncomputable section
open Real
namespace BanditRLProof.MOSS

theorem log_sixtyFour_le : log (64 : ℝ) ≤ 17/4 := by
  have he : (64 : ℝ) = 2^6 := by norm_num
  rw [he, log_pow]
  nlinarith [log_two_lt_d9]

/-- Dimensionless large-gap numerical estimate used in source Theorem 9.1. -/
theorem largeGap_constant_fifteen (q : ℝ) (hq : 64 ≤ q) :
    (1+8*(2*log q+sqrt (Real.pi*(2*log q))+1))/sqrt q ≤ 15 := by
  have hq0 : 0 < q := by linarith
  have hsq : 8 ≤ sqrt q := by
    have h := sqrt_le_sqrt hq
    norm_num at h
    exact h
  have he1 : exp 1 ≤ (64 : ℝ) := by linarith [exp_one_lt_three]
  have he2 : exp 2 ≤ (64 : ℝ) := by
    have he : exp (2 : ℝ) = (exp 1)^2 := by rw [← exp_nat_mul]; norm_num
    rw [he]
    nlinarith [exp_one_lt_three, exp_pos (1 : ℝ)]
  have hl := log_div_sqrt_antitoneOn he2 (he2.trans hq) hq
  dsimp only at hl
  have hl' : log q ≤ (17/32)*sqrt q := by
    have h64 : sqrt (64 : ℝ) = 8 := by norm_num
    rw [h64] at hl
    have h := hl.trans (div_le_div_of_nonneg_right log_sixtyFour_le (by norm_num))
    exact (div_le_iff₀ (sqrt_pos.mpr hq0)).mp (by convert h using 1 <;> norm_num)
  have hr := log_div_self_antitoneOn he1 (he1.trans hq) hq
  dsimp only at hr
  have hlq : log q ≤ (17/256)*q := by
    have h := hr.trans (div_le_div_of_nonneg_right log_sixtyFour_le (by norm_num))
    exact (div_le_iff₀ hq0).mp (by convert h using 1 <;> norm_num)
  have hlog : 0 ≤ log q := log_nonneg (by linarith)
  have hprod : Real.pi*(2*log q) ≤ (1071/2560)*q := by
    have h := mul_le_mul_of_nonneg_left hlq (by positivity : 0 ≤ 2*Real.pi)
    have h' := mul_le_mul_of_nonneg_right pi_lt_d2.le (by positivity : 0 ≤ (17/128)*q)
    nlinarith
  have hroot : sqrt (Real.pi*(2*log q)) ≤ (21/32)*sqrt q := by
    have ha := sq_sqrt (by positivity : 0 ≤ Real.pi*(2*log q))
    have hb := sq_sqrt hq0.le
    have hc : ((21/32 : ℝ)*sqrt q)^2 = (441/1024)*q := by rw [mul_pow, hb]; ring
    nlinarith [sqrt_nonneg (Real.pi*(2*log q)), sqrt_nonneg q]
  apply (div_le_iff₀ (sqrt_pos.mpr hq0)).mpr
  nlinarith

theorem largeGap_scaled_constant_fifteen (δ gap : ℝ) (hδ : 0 < δ)
    (hg : 0 < gap) (hlarge : 8*sqrt δ ≤ gap) :
    gap*(1/gap^2+1+(8/gap^2)*(2*logPlus (gap^2/δ)+
      sqrt (Real.pi*(2*logPlus (gap^2/δ)))+1)) ≤ gap+15/sqrt δ := by
  have hsd : 0 < sqrt δ := sqrt_pos.mpr hδ
  have hsd2 := sq_sqrt hδ.le
  have hq : 64 ≤ gap^2/δ := by
    apply (le_div_iff₀ hδ).mpr
    nlinarith [sq_nonneg (gap-8*sqrt δ)]
  have hs : sqrt (gap^2/δ) = gap/sqrt δ := by
    rw [sqrt_div (sq_nonneg gap), sqrt_sq hg.le]
  have hl : logPlus (gap^2/δ) = log (gap^2/δ) := by
    unfold logPlus
    rw [max_eq_right (by linarith)]
  rw [hl]
  have hb := div_le_div_of_nonneg_right (largeGap_constant_fifteen (gap^2/δ) hq) hsd.le
  have he : gap*(1/gap^2+1+(8/gap^2)*(2*log (gap^2/δ)+
      sqrt (Real.pi*(2*log (gap^2/δ)))+1)) = gap+
      ((1+8*(2*log (gap^2/δ)+sqrt (Real.pi*(2*log (gap^2/δ)))+1))/sqrt (gap^2/δ))/sqrt δ := by
    rw [hs]
    field_simp
    ring
  rw [he]
  linarith

end BanditRLProof.MOSS
