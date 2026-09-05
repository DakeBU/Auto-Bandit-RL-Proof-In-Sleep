import BanditRLProof

namespace BanditRLProof.TextbookPartIVChapter14GaussianCanary

open MeasureTheory ProbabilityTheory LowerBounds
open scoped NNReal

example (m n : ℝ) (v : ℝ≥0) (hv : v ≠ 0) :
    InformationTheory.klDiv (gaussianReal m v) (gaussianReal n v) =
      ENNReal.ofReal ((m - n) ^ 2 / (2 * v)) :=
  klDiv_gaussianReal_same_variance m n v hv

example {A : Set ℝ} (hA : MeasurableSet A) :
    (3 / 20 : ℝ) ≤ max ((gaussianReal 0 4).real A) ((gaussianReal 2 4).real Aᶜ) :=
  gaussian_testing_max_error_three_twentieths 2 4 (by norm_num) (by norm_num) hA

example (Δ : ℝ) (v : ℝ≥0) (hv : v ≠ 0) {A : Set ℝ} (hA : MeasurableSet A) :
    (1 / 2 : ℝ) * Real.exp (-(Δ ^ 2 / (2 * v))) ≤
      (gaussianReal 0 v).real A + (gaussianReal Δ v).real Aᶜ :=
  gaussian_testing_error_lower_bound Δ v hv hA

#print axioms LowerBounds.log_gaussianPDFReal_div_same_variance
#print axioms LowerBounds.llr_gaussianReal_same_variance_ae
#print axioms LowerBounds.integrable_llr_gaussianReal_same_variance
#print axioms LowerBounds.klDiv_gaussianReal_same_variance
#print axioms LowerBounds.three_fifths_le_exp_neg_half
#print axioms LowerBounds.gaussian_testing_error_lower_bound
#print axioms LowerBounds.gaussian_testing_error_three_tenths
#print axioms LowerBounds.gaussian_testing_max_error_three_twentieths

end BanditRLProof.TextbookPartIVChapter14GaussianCanary
