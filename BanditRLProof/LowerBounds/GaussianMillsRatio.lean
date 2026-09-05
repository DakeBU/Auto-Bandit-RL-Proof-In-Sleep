import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Real.Pi.Bounds
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

/-- Algebraic sign test for the derivative of the upper comparison error. -/
theorem gaussianMills_sign_iff {c x : ℝ} (hc : 1 < c) (hx : 0 ≤ x) :
    0 ≤ x ^ 2 + c - 1 - x * Real.sqrt (x ^ 2 + c) ↔
      x ^ 2 * (2 - c) ≤ (c - 1) ^ 2 := by
  have hp : 0 < x ^ 2 + c := by positivity
  have hs := Real.sq_sqrt hp.le
  have hxs : 0 ≤ x * Real.sqrt (x ^ 2 + c) := mul_nonneg hx (Real.sqrt_nonneg _)
  have ha : 0 < x ^ 2 + c - 1 := by nlinarith [sq_nonneg x]
  have he : (x * Real.sqrt (x ^ 2 + c)) ^ 2 = x ^ 2 * (x ^ 2 + c) := by
    rw [mul_pow, hs]
  constructor
  · intro h
    have hh := mul_self_le_mul_self hxs (show x * Real.sqrt (x ^ 2 + c) ≤ x ^ 2 + c - 1 by linarith)
    nlinarith
  · intro h
    by_contra hn
    have hh := mul_self_lt_mul_self ha.le (show x ^ 2 + c - 1 < x * Real.sqrt (x ^ 2 + c) by linarith)
    nlinarith

/-- The sign changes at exactly one nonnegative threshold when `1<c<2`. -/
theorem gaussianMills_sign_threshold {c x : ℝ} (hc : 1 < c) (hc2 : c < 2)
    (hx : 0 ≤ x) :
    0 ≤ x ^ 2 + c - 1 - x * Real.sqrt (x ^ 2 + c) ↔
      x ≤ (c - 1) / Real.sqrt (2 - c) := by
  rw [gaussianMills_sign_iff hc hx]
  have hs : 0 < Real.sqrt (2 - c) := Real.sqrt_pos.mpr (by linarith)
  have he := Real.sq_sqrt (show 0 ≤ 2 - c by linarith)
  rw [le_div_iff₀ hs]
  have hp : 0 ≤ x * Real.sqrt (2 - c) := mul_nonneg hx hs.le
  constructor
  · intro h
    nlinarith [sq_nonneg (x * Real.sqrt (2 - c) - (c - 1)),
      show (x * Real.sqrt (2 - c)) ^ 2 = x ^ 2 * (2 - c) by rw [mul_pow, he]]
  · intro h
    have hh := mul_self_le_mul_self hp h
    nlinarith [show (x * Real.sqrt (2 - c)) ^ 2 = x ^ 2 * (2 - c) by rw [mul_pow, he]]

/-- The derivative of comparison minus Gaussian tail has this explicit value. -/
noncomputable def gaussianMillsErrorDerivative (c x : ℝ) : ℝ :=
  Real.exp (-x ^ 2) -
    gaussianMillsComparison c x * (2 * x + 1 / Real.sqrt (x ^ 2 + c))

theorem gaussianMillsErrorDerivative_factor {c x : ℝ} (hc : 0 < c) :
    gaussianMillsErrorDerivative c x =
      Real.exp (-x ^ 2) * (x ^ 2 + c - 1 - x * Real.sqrt (x ^ 2 + c)) /
        ((x + Real.sqrt (x ^ 2 + c)) * Real.sqrt (x ^ 2 + c)) := by
  have hp : 0 < x ^ 2 + c := by positivity
  have hs := (Real.sqrt_pos.mpr hp).ne'
  have hd := (gaussianMillsComparison_denominator_pos (x := x) hc).ne'
  have he := Real.sq_sqrt hp.le
  unfold gaussianMillsErrorDerivative gaussianMillsComparison
  field_simp
  nlinarith [he]

theorem gaussianMillsErrorDerivative_nonneg_iff {c x : ℝ}
    (hc : 1 < c) (hc2 : c < 2) (hx : 0 ≤ x) :
    0 ≤ gaussianMillsErrorDerivative c x ↔
      x ≤ (c - 1) / Real.sqrt (2 - c) := by
  have hc0 : 0 < c := by linarith
  have hs : 0 < Real.sqrt (x ^ 2 + c) := Real.sqrt_pos.mpr (by positivity)
  have hd := mul_pos (gaussianMillsComparison_denominator_pos (x := x) hc0) hs
  rw [gaussianMillsErrorDerivative_factor hc0]
  rw [le_div_iff₀ hd]
  simp only [zero_mul]
  rw [mul_nonneg_iff_of_pos_left (Real.exp_pos _)]
  exact gaussianMills_sign_threshold hc hc2 hx

/-- Specialization to the exact upper-bound constant in source Eq. (13.4). -/
theorem gaussianMillsErrorDerivative_source_nonneg_iff {x : ℝ} (hx : 0 ≤ x) :
    0 ≤ gaussianMillsErrorDerivative (4 / Real.pi) x ↔
      x ≤ (4 / Real.pi - 1) / Real.sqrt (2 - 4 / Real.pi) := by
  apply gaussianMillsErrorDerivative_nonneg_iff _ _ hx
  · rw [lt_div_iff₀ Real.pi_pos]
    nlinarith [Real.pi_lt_four]
  · rw [div_lt_iff₀ Real.pi_pos]
    nlinarith [Real.pi_gt_three]

/-- Comparison error expressed using a finite-interval Gaussian integral. -/
noncomputable def gaussianMillsError (c x : ℝ) : ℝ :=
  gaussianMillsComparison c x + (∫ t in (0 : ℝ)..x, Real.exp (-t ^ 2)) -
    Real.sqrt Real.pi / 2

theorem hasDerivAt_gaussianMillsError {c x : ℝ} (hc : 0 < c) :
    HasDerivAt (gaussianMillsError c) (gaussianMillsErrorDerivative c x) x := by
  have hcont : Continuous (fun t : ℝ => Real.exp (-t ^ 2)) := by fun_prop
  have hi := intervalIntegral.integral_hasDerivAt_right
    (hcont.intervalIntegrable (0 : ℝ) x)
    hcont.stronglyMeasurable.stronglyMeasurableAtFilter hcont.continuousAt
  convert ((hasDerivAt_gaussianMillsComparison hc).add hi).sub_const
    (Real.sqrt Real.pi / 2) using 1; dsimp [gaussianMillsError, gaussianMillsErrorDerivative]
  ring

end BanditRLProof.LowerBounds
