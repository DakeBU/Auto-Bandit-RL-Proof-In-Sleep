import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Tactic

noncomputable section
open MeasureTheory Real Set Filter
namespace BanditRLProof.Concentration

theorem integral_mul_exp_neg_mul_sq_Ioi (b : ℝ) (hb : 0 < b) :
    ∫ x : ℝ in Ioi 0, x*exp (-b*x^2) = (2*b)⁻¹ := by
  have hd : ∀ x : ℝ, HasDerivAt (fun x => -(2*b)⁻¹*exp (-b*x^2))
      (x*exp (-b*x^2)) x := by
    intro x
    convert (((hasDerivAt_pow 2 x).const_mul (-b)).exp).const_mul (-(2*b)⁻¹) using 1
    field_simp
    ring
  have ht : Tendsto (fun x : ℝ => -(2*b)⁻¹*exp (-b*x^2)) atTop (nhds (-(2*b)⁻¹*0)) := by
    apply Tendsto.const_mul
    exact tendsto_exp_atBot.comp
      ((tendsto_pow_atTop two_ne_zero).const_mul_atTop_of_neg (by linarith : -b < 0))
  convert integral_Ioi_of_hasDerivAt_of_tendsto' (fun x _ => hd x)
    (integrable_mul_exp_neg_mul_sq hb).integrableOn ht using 1 <;> simp

/-- Exact transformed tail integral in source Lemma 8.2. -/
theorem integral_transformed_occupancy_tail (a ε : ℝ) (ha : 0 < a) (hε : 0 < ε) :
    ∫ z : ℝ in Ioi 0, (2/ε^2)*(z+sqrt (2*a))*exp (-(1/2 : ℝ)*z^2) =
      (2/ε^2)*(1+sqrt (Real.pi*a)) := by
  have hi := (integrable_mul_exp_neg_mul_sq (by norm_num : 0 < (1/2 : ℝ))).integrableOn (s := Ioi 0)
  have hj := ((integrable_exp_neg_mul_sq (by norm_num : 0 < (1/2 : ℝ))).const_mul
    (sqrt (2*a))).integrableOn (s := Ioi 0)
  have heq : (fun z : ℝ => (2/ε^2)*(z+sqrt (2*a))*exp (-(1/2 : ℝ)*z^2)) =
      (fun z => (2/ε^2)*(z*exp (-(1/2 : ℝ)*z^2)+sqrt (2*a)*exp (-(1/2 : ℝ)*z^2))) := by
    funext z; ring
  rw [heq, integral_const_mul, integral_add hi hj, integral_const_mul,
    integral_mul_exp_neg_mul_sq_Ioi (1/2) (by norm_num), integral_gaussian_Ioi]
  have hs : sqrt (2*a)*sqrt (Real.pi/(1/2)) = 2*sqrt (Real.pi*a) := by
    rw [← sqrt_mul (by positivity)]
    have he : 2*a*(Real.pi/(1/2)) = (2:ℝ)^2*(Real.pi*a) := by ring
    rw [he, sqrt_mul (by positivity), sqrt_sq (by norm_num : (0:ℝ) ≤ 2)]
  norm_num only [mul_one_div, one_mul, inv_one] at *
  rw [← mul_div_assoc, hs]
  ring

/-- The shifted Gaussian kernel after the algebraic square-root rewrite. -/
def occupancyTail (a ε t : ℝ) : ℝ := exp (-(ε*sqrt t-sqrt (2*a))^2/2)

theorem occupancyTail_antitoneOn (a ε : ℝ) (ha : 0 < a) (hε : 0 < ε) :
    AntitoneOn (occupancyTail a ε) (Ici (2*a/ε^2)) := by
  intro x hx y hy hxy
  have hu : 0 < 2*a/ε^2 := by positivity
  have hx0 : 0 ≤ x := hu.le.trans hx
  have hy0 : 0 ≤ y := hx0.trans hxy
  have hsx : (ε*sqrt x)^2 = ε^2*x := by rw [mul_pow, sq_sqrt hx0]
  have hlarge : 2*a ≤ x*ε^2 := (div_le_iff₀ (sq_pos_of_pos hε)).mp hx
  have hnon : 0 ≤ ε*sqrt x-sqrt (2*a) := by
    nlinarith [sq_sqrt (by positivity : 0 ≤ 2*a), sqrt_nonneg (2*a),
      mul_nonneg hε.le (sqrt_nonneg x)]
  have hm : ε*sqrt x-sqrt (2*a) ≤ ε*sqrt y-sqrt (2*a) :=
    sub_le_sub_right (mul_le_mul_of_nonneg_left (sqrt_le_sqrt hxy) hε.le) _
  unfold occupancyTail
  apply exp_le_exp.mpr
  nlinarith

end BanditRLProof.Concentration
