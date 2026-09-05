import BanditRLProof.LowerBounds.GaussianTesting

namespace BanditRLProof.LowerBounds

open ProbabilityTheory
open scoped ENNReal NNReal

/-- A finite-valued Gaussian counterexample to the triangle inequality. -/
theorem relativeEntropy_triangle_counterexample :
    relativeEntropy (gaussianReal 0 1) (gaussianReal 1 1) +
      relativeEntropy (gaussianReal 1 1) (gaussianReal 2 1) <
      relativeEntropy (gaussianReal 0 1) (gaussianReal 2 1) := by
  simp only [relativeEntropy, klDiv_gaussianReal_same_variance _ _ 1 (by norm_num)]
  norm_num
  rw [← ENNReal.ofReal_add (by norm_num) (by norm_num)]
  norm_num

/-- Reversing the Bernoulli comparison can change finite KL to infinite KL. -/
theorem bernoulliRelativeEntropy_asymmetry :
    bernoulliRelativeEntropy 0 (1 / 2) ≠ bernoulliRelativeEntropy (1 / 2) 0 := by
  change KLUCB.bernoulliKL 0 (1 / 2) ≠ KLUCB.bernoulliKL (1 / 2) 0
  rw [KLUCB.bernoulliKL_zero_left_of_interior (by norm_num) (by norm_num),
    KLUCB.bernoulliKL_eq_top_right_zero (by constructor <;> norm_num) (by norm_num)]
  exact ENNReal.ofReal_ne_top

end BanditRLProof.LowerBounds
