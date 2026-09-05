import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Tactic

/-! Analytic comparison functions for Chapter 13 Eq. (13.4).
The exact lower improper-integral bound compiles; the upper bound remains open. -/

namespace BanditRLProof.LowerBounds

noncomputable def gaussianMillsComparison (c x : ℝ) : ℝ :=
  Real.exp (-x ^ 2) / (x + Real.sqrt (x ^ 2 + c))

theorem gaussianMillsComparison_denominator_pos {c x : ℝ} (hc : 0 < c) :
    0 < x + Real.sqrt (x ^ 2 + c) := by
  have hp : 0 < x ^ 2 + c := by positivity
  have hs := Real.sq_sqrt hp.le
  have hn := Real.sqrt_nonneg (x ^ 2 + c)
  nlinarith

theorem hasDerivAt_gaussianMillsComparison {c x : ℝ} (hc : 0 < c) :
    HasDerivAt (gaussianMillsComparison c)
      (-gaussianMillsComparison c x * (2 * x + 1 / Real.sqrt (x ^ 2 + c))) x := by
  have hp : 0 < x ^ 2 + c := by positivity
  have hs : Real.sqrt (x ^ 2 + c) ≠ 0 := (Real.sqrt_pos.2 hp).ne'
  have hd := (gaussianMillsComparison_denominator_pos (x := x) hc).ne'
  have hsq := Real.sq_sqrt hp.le
  have h := (((hasDerivAt_id x).pow 2).neg.exp).div
    ((hasDerivAt_id x).add ((((hasDerivAt_id x).pow 2).add_const c).sqrt hp.ne')) hd
  convert h using 1; dsimp [gaussianMillsComparison]
  field_simp
  nlinarith [hsq]

theorem gaussianMillsComparison_lower_derivative_bound (x : ℝ) :
    gaussianMillsComparison 2 x * (2 * x + 1 / Real.sqrt (x ^ 2 + 2)) ≤
      Real.exp (-x ^ 2) := by
  have hp : 0 < x ^ 2 + 2 := by positivity
  have hs : 0 < Real.sqrt (x ^ 2 + 2) := Real.sqrt_pos.2 hp
  have hsq := Real.sq_sqrt hp.le
  have hd := gaussianMillsComparison_denominator_pos (x := x) (c := 2) (by norm_num)
  have hprod : x * Real.sqrt (x ^ 2 + 2) ≤ x ^ 2 + 1 := by
    nlinarith [sq_nonneg (x * Real.sqrt (x ^ 2 + 2) - (x ^ 2 + 1)),
      sq_nonneg (Real.sqrt (x ^ 2 + 2) - x)]
  unfold gaussianMillsComparison
  apply (div_mul_eq_mul_div _ _ _).le.trans
  rw [div_le_iff₀ hd]
  apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
  have hi : 1 / Real.sqrt (x ^ 2 + 2) ≤ Real.sqrt (x ^ 2 + 2) - x := by
    apply (div_le_iff₀ hs).2
    nlinarith
  linarith

open Filter MeasureTheory Set
open scoped Topology

theorem gaussianMillsComparison_pos {c : ℝ} (hc : 0 < c) (x : ℝ) :
    0 < gaussianMillsComparison c x :=
  div_pos (Real.exp_pos _) (gaussianMillsComparison_denominator_pos hc)

theorem tendsto_gaussianMillsComparison {c : ℝ} (hc : 0 < c) :
    Tendsto (gaussianMillsComparison c) atTop (𝓝 0) := by
  apply squeeze_zero' (Filter.Eventually.of_forall (fun x => (gaussianMillsComparison_pos hc x).le))
    _ tendsto_inv_atTop_zero
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
  unfold gaussianMillsComparison
  calc
    Real.exp (-x ^ 2) / (x + Real.sqrt (x ^ 2 + c)) ≤
        1 / (x + Real.sqrt (x ^ 2 + c)) :=
      div_le_div_of_nonneg_right (Real.exp_le_one_iff.mpr (by nlinarith [sq_nonneg x]))
        (gaussianMillsComparison_denominator_pos hc).le
    _ ≤ x⁻¹ := by
      rw [one_div]
      exact inv_anti₀ hx (le_add_of_nonneg_right (Real.sqrt_nonneg _))

/-- The exact lower half of Lattimore--Szepesvari Eq. (13.4). -/
theorem gaussianMills_lower_integral {x : ℝ} (hx : 0 ≤ x) :
    Real.exp (-x ^ 2) / (x + Real.sqrt (x ^ 2 + 2)) ≤
      ∫ t in Ioi x, Real.exp (-t ^ 2) := by
  let d : ℝ → ℝ := fun t =>
    -gaussianMillsComparison 2 t * (2 * t + 1 / Real.sqrt (t ^ 2 + 2))
  have hd : ∀ t ∈ Ici x, HasDerivAt (gaussianMillsComparison 2) (d t) t := by
    intro t _
    exact hasDerivAt_gaussianMillsComparison (by norm_num)
  have hn : ∀ t ∈ Ioi x, d t ≤ 0 := by
    intro t ht
    have ht0 : 0 ≤ t := le_trans hx ht.le
    have hg := (gaussianMillsComparison_pos (c := 2) (by norm_num) t).le
    dsimp [d]
    apply mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hg)
    positivity
  have hl := tendsto_gaussianMillsComparison (c := 2) (by norm_num)
  have hi := integrableOn_Ioi_deriv_of_nonpos' hd hn hl
  have he := integral_Ioi_of_hasDerivAt_of_nonpos' hd hn hl
  have hg : Integrable (fun t : ℝ => Real.exp (-t ^ 2)) := by
    simpa using integrable_exp_neg_mul_sq (b := (1 : ℝ)) (by norm_num)
  have hle : (∫ t in Ioi x, -d t) ≤ ∫ t in Ioi x, Real.exp (-t ^ 2) := by
    apply setIntegral_mono_on hi.neg hg.integrableOn measurableSet_Ioi
    intro t _
    simpa [d] using gaussianMillsComparison_lower_derivative_bound t
  rw [integral_neg, he] at hle
  simpa [gaussianMillsComparison] using hle

end BanditRLProof.LowerBounds
