import BanditRLProof
import Mathlib.Tactic.NormNum

/-!
# Textbook Part IV Chapter 15 public canary

This root-import canary exercises the compiled Gaussian dependency slice and
the adaptive same-policy divergence decomposition of Lemma 15.1.  The Gaussian
minimax lower bound of Theorem 15.2 remains a separate open terminal.
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

/-- Two alternative arms and horizon eight give the source exponent one half. -/
example :
    2 * 8 * gaussianMinimaxGap 2 8 ^ 2 / 2 = (1 / 2 : Real) := by
  exact gaussianMinimaxGap_informationExponent_eq_half (by norm_num) (by norm_num)

/-- The source horizon condition keeps the tuned changed mean in the unit cube. -/
example : gaussianMinimaxGap 2 8 ≤ (1 / 2 : Real) := by
  exact gaussianMinimaxGap_le_half (by norm_num) (by norm_num)

#check LowerBounds.klDiv_compProd_same_left_eq_lintegral_klDiv_of_measurable
#check LowerBounds.klDiv_finiteAction_compProd_eq_lintegral_armKL
#check LowerBounds.klDiv_historyStep_samePolicy_eq_iterated_lintegral_armKL_general
#check LowerBounds.canonicalBanditHistoryMeasure
#check LowerBounds.canonicalRealizedExpectedPullCountThrough
#check LowerBounds.canonicalRealizedExpectedPullCountThrough_eq_expectedPullCountThrough
#check LowerBounds.klDiv_canonicalBanditHistoryMeasure_succ_general
#check LowerBounds.klDiv_canonicalBanditHistoryMeasure_eq_sum_realizedExpectedPullCount_mul_armKL
#check LowerBounds.banditHistoryRelativeEntropy_eq_expectedPulls_sum

#print axioms LowerBounds.log_gaussianPDFReal_div_gaussianPDFReal_one
#print axioms LowerBounds.llr_gaussianReal_one_ae
#print axioms LowerBounds.integrable_llr_gaussianReal_one
#print axioms LowerBounds.klDiv_gaussianReal_one
#print axioms LowerBounds.klDiv_unitGaussianArm_zero_two_mul
#print axioms LowerBounds.gaussianMinimaxGap_sq
#print axioms LowerBounds.gaussianMinimaxGap_informationExponent_eq_half
#print axioms LowerBounds.gaussianMinimaxGap_le_half
#print axioms LowerBounds.klDiv_compProd_same_left_eq_lintegral_klDiv_of_measurable
#print axioms LowerBounds.klDiv_historyStep_samePolicy_eq_iterated_lintegral_armKL_general
#print axioms LowerBounds.canonicalRealizedExpectedPullCountThrough_eq_expectedPullCountThrough
#print axioms LowerBounds.klDiv_canonicalBanditHistoryMeasure_eq_sum_realizedExpectedPullCount_mul_armKL
#print axioms LowerBounds.banditHistoryRelativeEntropy_eq_expectedPulls_sum

end BanditRLProof.TextbookPartIVChapter15Canary
