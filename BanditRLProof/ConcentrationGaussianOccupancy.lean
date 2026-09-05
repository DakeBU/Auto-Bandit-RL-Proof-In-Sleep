import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Function.JacobianOneDim
import Mathlib.Analysis.SumIntegralComparisons
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

def occupancySubstitution (a ε z : ℝ) : ℝ := ((z+sqrt (2*a))/ε)^2

theorem occupancySubstitution_image (a ε : ℝ) (ha : 0 < a) (hε : 0 < ε) :
    occupancySubstitution a ε '' Ioi 0 = Ioi (2*a/ε^2) := by
  have hc : 0 < sqrt (2*a) := sqrt_pos.mpr (by positivity)
  have hc2 := sq_sqrt (by positivity : 0 ≤ 2*a)
  ext t
  constructor
  · rintro ⟨z, hz, rfl⟩
    change 0 < z at hz
    change 2*a/ε^2 < ((z+sqrt (2*a))/ε)^2
    rw [div_pow]
    apply (div_lt_div_iff_of_pos_right (sq_pos_of_pos hε)).mpr
    nlinarith [mul_pos hz hc]
  · intro ht
    have ht0 : 0 < t := (by positivity : 0 < 2*a/ε^2).trans ht
    have htlarge : 2*a < t*ε^2 := (div_lt_iff₀ (sq_pos_of_pos hε)).mp ht
    have hsq : (ε*sqrt t)^2 = ε^2*t := by rw [mul_pow, sq_sqrt ht0.le]
    refine ⟨ε*sqrt t-sqrt (2*a), ?_, ?_⟩
    · change 0 < ε*sqrt t-sqrt (2*a)
      nlinarith [mul_pos hε (sqrt_pos.mpr ht0)]
    · unfold occupancySubstitution
      rw [sub_add_cancel, mul_div_cancel_left₀ _ hε.ne', sq_sqrt ht0.le]

theorem occupancySubstitution_injOn (a ε : ℝ) (ha : 0 < a) (hε : 0 < ε) :
    InjOn (occupancySubstitution a ε) (Ioi 0) := by
  intro x hx y hy he
  change 0 < x at hx
  change 0 < y at hy
  have hx0 : 0 < (x+sqrt (2*a))/ε := by positivity
  have hy0 : 0 < (y+sqrt (2*a))/ε := by positivity
  have heq : (x+sqrt (2*a))/ε = (y+sqrt (2*a))/ε := by
    unfold occupancySubstitution at he
    nlinarith
  have heq' := (div_left_inj' hε.ne').mp heq
  linarith

theorem hasDerivAt_occupancySubstitution (a ε z : ℝ) :
    HasDerivAt (occupancySubstitution a ε) ((2/ε^2)*(z+sqrt (2*a))) z := by
  convert (((hasDerivAt_id z).add_const (sqrt (2*a))).div_const ε).pow 2 using 1
  dsimp
  ring

theorem integral_occupancyTail (a ε : ℝ) (ha : 0 < a) (hε : 0 < ε) :
    ∫ t in Ioi (2*a/ε^2), occupancyTail a ε t = (2/ε^2)*(1+sqrt (Real.pi*a)) := by
  rw [← occupancySubstitution_image a ε ha hε]
  rw [integral_image_eq_integral_abs_deriv_smul measurableSet_Ioi
    (fun z _ => (hasDerivAt_occupancySubstitution a ε z).hasDerivWithinAt)
    (occupancySubstitution_injOn a ε ha hε)]
  rw [← integral_transformed_occupancy_tail a ε ha hε]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro z hz
  change 0 < z at hz
  dsimp only
  have hpos : 0 ≤ (z+sqrt (2*a))/ε := by positivity
  have hd : 0 ≤ (2/ε^2)*(z+sqrt (2*a)) := by positivity
  rw [abs_of_nonneg hd, smul_eq_mul]
  unfold occupancyTail occupancySubstitution
  rw [sqrt_sq hpos, mul_div_cancel₀ _ hε.ne', add_sub_cancel_right]
  congr 1
  ring

theorem integrableOn_occupancyTail (a ε : ℝ) (ha : 0 < a) (hε : 0 < ε) :
    IntegrableOn (occupancyTail a ε) (Ioi (2*a/ε^2)) := by
  rw [← occupancySubstitution_image a ε ha hε,
    integrableOn_image_iff_integrableOn_abs_deriv_smul measurableSet_Ioi
      (fun z _ => (hasDerivAt_occupancySubstitution a ε z).hasDerivWithinAt)
      (occupancySubstitution_injOn a ε ha hε)]
  have hi := (integrable_mul_exp_neg_mul_sq (by norm_num : 0 < (1/2 : ℝ))).integrableOn (s := Ioi 0)
  have hj := ((integrable_exp_neg_mul_sq (by norm_num : 0 < (1/2 : ℝ))).const_mul
    (sqrt (2*a))).integrableOn (s := Ioi 0)
  apply ((hi.add hj).const_mul (2/ε^2)).congr
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with z hz
  change 0 < z at hz
  rw [abs_of_nonneg (by positivity : 0 ≤ (2/ε^2)*(z+sqrt (2*a))), smul_eq_mul]
  unfold occupancyTail occupancySubstitution
  rw [sqrt_sq (by positivity : 0 ≤ (z+sqrt (2*a))/ε),
    mul_div_cancel₀ _ hε.ne', add_sub_cancel_right]
  have he : -(1/2 : ℝ)*z^2 = -z^2/2 := by ring
  simp only [Pi.add_apply]
  rw [he]
  ring

theorem sum_occupancyTail_shift_le (a ε r : ℝ) (ha : 0 < a) (hε : 0 < ε)
    (hr : 2*a/ε^2 ≤ r) (N : ℕ) :
    (∑ i ∈ Finset.range N, occupancyTail a ε (r+(i+1 : ℕ))) ≤
      (2/ε^2)*(1+sqrt (Real.pi*a)) := by
  have hm : AntitoneOn (occupancyTail a ε) (Icc r (r+N)) :=
    (occupancyTail_antitoneOn a ε ha hε).mono (fun x hx => hr.trans hx.1)
  calc
    _ ≤ ∫ t in r..r+N, occupancyTail a ε t := hm.sum_le_integral
    _ = ∫ t in Ioc r (r+N), occupancyTail a ε t :=
      intervalIntegral.integral_of_le (le_add_of_nonneg_right (Nat.cast_nonneg N))
    _ ≤ ∫ t in Ioi (2*a/ε^2), occupancyTail a ε t :=
      setIntegral_mono_set (integrableOn_occupancyTail a ε ha hε)
        (Eventually.of_forall (fun t => (exp_pos _).le))
        (Eventually.of_forall (fun t ht => hr.trans_lt ht.1))
    _ = _ := integral_occupancyTail a ε ha hε

end BanditRLProof.Concentration
