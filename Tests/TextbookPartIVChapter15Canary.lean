import BanditRLProof
import Mathlib.Tactic.NormNum

/-!
# Textbook Part IV Chapter 15 public canary

This root-import canary exercises only the compiled Gaussian dependency slice
of Chapter 15.  It does not claim the adaptive-history divergence decomposition
of Lemma 15.1 or the minimax lower bound of Theorem 15.2; both remain blocked
on the stochastic-policy history and conditional-kernel KL bridge.
-/

namespace BanditRLProof.TextbookPartIVChapter15Canary

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal
open LowerBounds

/-- The finite Gaussian environment constructor exposes one law per arm. -/
example (mean : Fin 3 -> Real) (arm : Fin 3) :
    unitGaussianBandit mean arm = gaussianReal (mean arm) (1 : NNReal) := rfl

/-- Nontrivial exact KL instance through the public root import. -/
example :
    InformationTheory.klDiv (unitGaussianArm 1) (unitGaussianArm 3) =
      ENNReal.ofReal 2 := by
  rw [klDiv_gaussianReal_one]
  norm_num

/-- Source changed-arm specialization at `Delta=1/4`. -/
example :
    InformationTheory.klDiv (unitGaussianArm 0) (unitGaussianArm (2 * (1 / 4))) =
      ENNReal.ofReal (1 / 8) := by
  rw [klDiv_unitGaussianArm_zero_two_mul]
  norm_num

#print axioms LowerBounds.log_gaussianPDFReal_div_gaussianPDFReal_one
#print axioms LowerBounds.llr_gaussianReal_one_ae
#print axioms LowerBounds.integrable_llr_gaussianReal_one
#print axioms LowerBounds.klDiv_gaussianReal_one
#print axioms LowerBounds.klDiv_unitGaussianArm_zero_two_mul

end BanditRLProof.TextbookPartIVChapter15Canary
