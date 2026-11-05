import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

noncomputable section
namespace BanditRL.OnlineEntropy

def scalarGap (u : ℝ) : ℝ :=
  (u - 1) * Real.log u - 2 * (u - 1)^2 / (u + 1)

private theorem first_derivative (u : ℝ) (hu : 0 < u) :
    HasDerivAt scalarGap (Real.log u - 1 - 1 / u + 8 / (u + 1)^2) u := by
  have hi := hasDerivAt_id u
  have hm := hi.sub_const 1
  have hp := hi.add_const 1
  have h := (hm.mul (Real.hasDerivAt_log hu.ne')).sub
    (((hm.pow 2).const_mul 2).div hp (by dsimp; positivity))
  convert h using 1 <;> first | rfl | (dsimp; field_simp [ne_of_gt hu, show u+1 ≠ 0 by positivity]; ring)


theorem scalarGap_curvature (u : ℝ) (hu : 0 < u) :
    HasDerivAt scalarGap (Real.log u - 1 - 1 / u + 8 / (u + 1)^2) u ∧
    HasDerivAt (deriv scalarGap)
      ((u - 1)^2 * (u^2 + 6*u + 1) / (u^2 * (u + 1)^3)) u ∧
    0 ≤ deriv (deriv scalarGap) u ∧ (deriv (deriv scalarGap) u = 0 ↔ u = 1) := by
  have hfirst := first_derivative u hu
  have hi := hasDerivAt_id u
  have hp := hi.add_const 1
  have hc := ((Real.hasDerivAt_log hu.ne').sub_const 1).sub
    ((hasDerivAt_const u (1:ℝ)).div hi hu.ne')
  have hcalc := hc.add ((hasDerivAt_const u (8:ℝ)).div (hp.pow 2) (by dsimp; positivity))
  have hsecond : HasDerivAt (fun t : ℝ => Real.log t - 1 - 1 / t + 8 / (t + 1)^2)
      ((u-1)^2*(u^2+6*u+1)/(u^2*(u+1)^3)) u := by
    convert hcalc using 1 <;> first | rfl | (dsimp; field_simp [ne_of_gt hu, show u+1 ≠ 0 by positivity]; ring)
  have he : Filter.EventuallyEq (nhds u) (deriv scalarGap)
      (fun t : ℝ => Real.log t - 1 - 1/t + 8/(t+1)^2) := by
    filter_upwards [lt_mem_nhds hu] with t ht using (first_derivative t ht).deriv
  have hs := hsecond.congr_of_eventuallyEq he
  refine ⟨hfirst,hs,?_,?_⟩
  · rw [hs.deriv]; positivity
  · rw [hs.deriv]
    constructor
    · intro hz
      by_contra hn
      have hsq : 0 < (u-1)^2 := sq_pos_of_ne_zero (sub_ne_zero.mpr hn)
      have hpos : 0 < (u-1)^2*(u^2+6*u+1)/(u^2*(u+1)^3) := by positivity
      exact hpos.ne' hz
    · rintro rfl; norm_num

theorem scalarGap_nonneg :
    scalarGap 1 = 0 ∧ deriv scalarGap 1 = 0 ∧
    ConvexOn ℝ (Set.Ioi 0) scalarGap ∧ ∀ u : ℝ, 0 < u → 0 ≤ scalarGap u := by
  have h1 : scalarGap 1 = 0 := by norm_num [scalarGap]
  have hd : HasDerivAt scalarGap 0 1 := by
    convert (scalarGap_curvature 1 (by norm_num)).1 using 1 <;> norm_num
  have hc : ConvexOn ℝ (Set.Ioi 0) scalarGap :=
    convexOn_of_deriv2_nonneg' (convex_Ioi _) (fun u hu =>
      (scalarGap_curvature u hu).1.differentiableAt.differentiableWithinAt)
      (fun u hu => (scalarGap_curvature u hu).2.1.differentiableAt.differentiableWithinAt)
      (fun u hu => (scalarGap_curvature u hu).2.2.1)
  refine ⟨h1,hd.deriv,hc,?_⟩
  intro u hu
  rcases lt_trichotomy u 1 with hlo | rfl | hhi
  · have h := hc.slope_le_of_hasDerivAt hu (show (1:ℝ) ∈ Set.Ioi 0 by norm_num) hlo hd
    rw [slope_def_field,h1] at h
    have k := (div_le_iff₀ (sub_pos.mpr hlo)).mp h
    linarith
  · exact h1.ge
  · have h := hc.le_slope_of_hasDerivAt (show (1:ℝ) ∈ Set.Ioi 0 by norm_num) hu hhi hd
    rw [slope_def_field,h1] at h
    have k := (le_div_iff₀ (sub_pos.mpr hhi)).mp h
    linarith

theorem positive_pair_log_ratio (x y : ℝ) (hx : 0 < x) (hy : 0 < y) :
    2 * (x-y)^2 / (x+y) ≤ (x-y) * (Real.log x - Real.log y) ∧
    (x = y → 2 * (x-y)^2 / (x+y) = (x-y) * (Real.log x - Real.log y)) := by
  have h := scalarGap_nonneg.2.2.2 (x/y) (div_pos hx hy)
  have hscale := mul_nonneg hy.le h
  have e : (x-y)*(Real.log x-Real.log y)-2*(x-y)^2/(x+y) = y*scalarGap (x/y) := by
    unfold scalarGap
    rw [Real.log_div hx.ne' hy.ne']
    have he : x/y+1 = (x+y)/y := by field_simp
    rw [he]
    field_simp [hy.ne',show x+y ≠ 0 by positivity]
    <;> ring
  exact ⟨sub_nonneg.mp (e.symm ▸ hscale),by rintro rfl; simp⟩

end BanditRL.OnlineEntropy
