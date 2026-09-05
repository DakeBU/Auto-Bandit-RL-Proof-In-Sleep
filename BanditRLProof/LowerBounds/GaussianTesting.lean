import BanditRLProof.LowerBounds.Minimax
import Mathlib.Analysis.Complex.ExponentialBounds

namespace BanditRLProof.LowerBounds

open MeasureTheory ProbabilityTheory Real
open scoped ENNReal NNReal

noncomputable section

theorem log_gaussianPDFReal_div_same_variance
    (m n x : ℝ) (v : ℝ≥0) (hv : v ≠ 0) :
    Real.log (gaussianPDFReal m v x / gaussianPDFReal n v x) =
      ((m - n) * x + (n ^ 2 - m ^ 2) / 2) / v := by
  have hvpos : (0 : ℝ) < v := NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr hv)
  rw [gaussianPDFReal_def, gaussianPDFReal_def]
  have hn : (Real.sqrt (2 * Real.pi * v))⁻¹ ≠ 0 := by positivity
  rw [mul_div_mul_left _ _ hn, Real.log_div (Real.exp_ne_zero _) (Real.exp_ne_zero _),
    Real.log_exp, Real.log_exp]
  ring

theorem llr_gaussianReal_same_variance_ae
    (m n : ℝ) (v : ℝ≥0) (hv : v ≠ 0) :
    llr (gaussianReal m v) (gaussianReal n v) =ᵐ[gaussianReal m v]
      fun x => ((m - n) * x + (n ^ 2 - m ^ 2) / 2) / v := by
  have hP := gaussianReal_absolutelyContinuous m hv
  have hQ := gaussianReal_absolutelyContinuous n hv
  have hPQ := hP.trans (gaussianReal_absolutelyContinuous' n hv)
  filter_upwards [hPQ.ae_le (Measure.rnDeriv_eq_div hP hQ),
    hP.ae_le (rnDeriv_gaussianReal m v), hP.ae_le (rnDeriv_gaussianReal n v)]
    with x hr hp hq
  rw [llr, hr, hp, hq, ENNReal.toReal_div, toReal_gaussianPDF, toReal_gaussianPDF]
  exact log_gaussianPDFReal_div_same_variance m n x v hv

theorem integrable_llr_gaussianReal_same_variance
    (m n : ℝ) (v : ℝ≥0) (hv : v ≠ 0) :
    Integrable (llr (gaussianReal m v) (gaussianReal n v)) (gaussianReal m v) := by
  rw [integrable_congr (llr_gaussianReal_same_variance_ae m n v hv)]
  have hi : Integrable (fun x : ℝ => x) (gaussianReal m v) :=
    (memLp_id_gaussianReal (μ := m) (v := v) 1).integrable (by norm_num)
  exact ((hi.const_mul (m - n)).add (integrable_const _)).div_const _

/-- The common positive variance Gaussian KL formula in Chapter 14. -/
theorem klDiv_gaussianReal_same_variance
    (m n : ℝ) (v : ℝ≥0) (hv : v ≠ 0) :
    InformationTheory.klDiv (gaussianReal m v) (gaussianReal n v) =
      ENNReal.ofReal ((m - n) ^ 2 / (2 * v)) := by
  have hPQ := (gaussianReal_absolutelyContinuous m hv).trans
    (gaussianReal_absolutelyContinuous' n hv)
  rw [InformationTheory.klDiv_of_ac_of_integrable hPQ
    (integrable_llr_gaussianReal_same_variance m n v hv)]
  simp only [probReal_univ, add_sub_cancel_right]
  rw [integral_congr_ae (llr_gaussianReal_same_variance_ae m n v hv), integral_div]
  have hi : Integrable (fun x : ℝ => x) (gaussianReal m v) :=
    (memLp_id_gaussianReal (μ := m) (v := v) 1).integrable (by norm_num)
  rw [integral_add (hi.const_mul (m - n)) (integrable_const _),
    integral_const_mul, integral_id_gaussianReal]
  simp only [integral_const, probReal_univ, one_smul]
  congr 1
  ring

/-- Exact rational certification of the displayed Gaussian testing constant. -/
theorem three_fifths_le_exp_neg_half :
    (3 / 5 : ℝ) ≤ Real.exp (-(1 / 2 : ℝ)) := by
  have he : Real.exp 1 < (25 / 9 : ℝ) := Real.exp_one_lt_d9.trans (by norm_num)
  have hi := one_div_lt_one_div_of_lt (Real.exp_pos 1) he
  have hs : Real.exp (-(1 / 2 : ℝ)) ^ 2 = (Real.exp 1)⁻¹ := by
    rw [pow_two, ← Real.exp_add]
    convert Real.exp_neg 1 using 1 <;> norm_num
  norm_num [div_eq_mul_inv] at hi
  nlinarith [Real.exp_pos (-(1 / 2 : ℝ))]

/-- Testing two Gaussian means from one observation, with arbitrary positive variance. -/
theorem gaussian_testing_error_lower_bound
    (Δ : ℝ) (v : ℝ≥0) (hv : v ≠ 0) {A : Set ℝ} (hA : MeasurableSet A) :
    (1 / 2 : ℝ) * Real.exp (-(Δ ^ 2 / (2 * v))) ≤
      (gaussianReal 0 v).real A + (gaussianReal Δ v).real Aᶜ := by
  have h := bretagnolleHuber (P := gaussianReal 0 v) (Q := gaussianReal Δ v) hA
  have hn : 0 ≤ Δ ^ 2 / (2 * (v : ℝ)) := by positivity
  simpa only [relativeEntropy, klDiv_gaussianReal_same_variance 0 Δ v hv,
    zero_sub, neg_sq, bretagnolleHuberScale, ENNReal.ofReal_ne_top, ↓reduceIte,
    ENNReal.toReal_ofReal hn] using h

/-- Under signal-to-noise ratio at most one, the sum of errors is at least 3/10. -/
theorem gaussian_testing_error_three_tenths
    (Δ : ℝ) (v : ℝ≥0) (hv : v ≠ 0) (hsnr : Δ ^ 2 / (v : ℝ) ≤ 1)
    {A : Set ℝ} (hA : MeasurableSet A) :
    (3 / 10 : ℝ) ≤ (gaussianReal 0 v).real A + (gaussianReal Δ v).real Aᶜ := by
  have hr : Δ ^ 2 / (2 * (v : ℝ)) ≤ 1 / 2 := by
    have he : Δ ^ 2 / (2 * (v : ℝ)) = (Δ ^ 2 / (v : ℝ)) / 2 := by ring
    rw [he]
    linarith
  have he := Real.exp_le_exp.mpr (neg_le_neg hr)
  have ht := gaussian_testing_error_lower_bound Δ v hv hA
  linarith [three_fifths_le_exp_neg_half]

/-- No measurable decision rule has both errors below 3/20 in the low-SNR regime. -/
theorem gaussian_testing_max_error_three_twentieths
    (Δ : ℝ) (v : ℝ≥0) (hv : v ≠ 0) (hsnr : Δ ^ 2 / (v : ℝ) ≤ 1)
    {A : Set ℝ} (hA : MeasurableSet A) :
    (3 / 20 : ℝ) ≤ max ((gaussianReal 0 v).real A) ((gaussianReal Δ v).real Aᶜ) := by
  have h := gaussian_testing_error_three_tenths Δ v hv hsnr hA
  have hp := le_max_left ((gaussianReal 0 v).real A) ((gaussianReal Δ v).real Aᶜ)
  have hq := le_max_right ((gaussianReal 0 v).real A) ((gaussianReal Δ v).real Aᶜ)
  linarith

end
end BanditRLProof.LowerBounds
