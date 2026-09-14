import BanditRLProof
import Mathlib.MeasureTheory.Measure.Count
import Mathlib.MeasureTheory.Integral.Lebesgue.Countable

noncomputable section
open Set Filter MeasureTheory BanditRL.OnlineConvex
open scoped ENNReal
namespace Tests.OnlineExpectation

def twoAtoms : Measure ℝ := Measure.dirac (-1) + Measure.dirac 3

theorem identity_integrable : Integrable (fun x : ℝ => x) twoAtoms := by
  exact (integrable_dirac (by simp)).add_measure (integrable_dirac (by simp))

theorem signed_two_atoms : signedExpectation twoAtoms (fun x : ℝ => (x : EReal)) =
    ((2 : ℝ) : EReal) := by
  rw [signedExpectation_coe_integrable twoAtoms (fun x : ℝ => x) identity_integrable]
  have h1 : Integrable (fun x : ℝ => x) (Measure.dirac (-1)) := integrable_dirac (by simp)
  have h3 : Integrable (fun x : ℝ => x) (Measure.dirac 3) := integrable_dirac (by simp)
  simp only [twoAtoms, integral_add_measure h1 h3, integral_dirac]
  norm_num

def growing (n : ℕ) : EReal := (((n : ℝ) + 1 : ℝ) : EReal)

theorem growing_nonnegative (n : ℕ) : 0 ≤ growing n := by
  unfold growing
  exact_mod_cast (show (0 : ℝ) ≤ (n : ℝ) + 1 by positivity)

theorem growing_positive_infinite : positiveIntegral Measure.count growing = ∞ := by
  have hl : (∫⁻ _ : ℕ, (1 : ℝ≥0∞) ∂Measure.count) ≤ positiveIntegral Measure.count growing := by
    apply lintegral_mono
    intro n
    change (1 : ℝ≥0∞) ≤ (((n : ℝ) + 1 : ℝ) : EReal).toENNReal
    simp only [EReal.toENNReal_of_ne_top (EReal.coe_ne_top _), EReal.toReal_coe]
    rw [← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal (by linarith [show (0 : ℝ) ≤ (n : ℝ) from Nat.cast_nonneg n])
  simpa [lintegral_const, Measure.count_univ] using hl

theorem growing_negative_zero : negativeIntegral Measure.count growing = 0 := by
  unfold negativeIntegral
  have he : (fun n : ℕ => (-growing n).toENNReal) = fun _ => (0 : ℝ≥0∞) := by
    funext n
    exact EReal.toENNReal_of_nonpos (EReal.neg_le_zero.mpr (growing_nonnegative n))
  rw [he, lintegral_zero]

theorem finite_values_infinite_integral : signedExpectation Measure.count growing = ⊤ ∧
    growing 0 = 1 ∧ growing 1 = 2 ∧ (∀ n, growing n ≠ ⊤ ∧ growing n ≠ ⊥) := by
  refine ⟨signedExpectation_eq_top Measure.count growing growing_positive_infinite
    (by rw [growing_negative_zero]; exact ENNReal.zero_ne_top), ?_, ?_, ?_⟩
  · norm_num [growing]
  · norm_num [growing]; rfl
  · intro n; exact ⟨EReal.coe_ne_top _, EReal.coe_ne_bot _⟩

#print axioms BanditRL.OnlineConvex.positiveIntegral_coe
#print axioms BanditRL.OnlineConvex.negativeIntegral_coe
#print axioms BanditRL.OnlineConvex.positiveIntegral_coe_ne_top
#print axioms BanditRL.OnlineConvex.negativeIntegral_coe_ne_top
#print axioms BanditRL.OnlineConvex.signedExpectation_coe_integrable
#print axioms BanditRL.OnlineConvex.signedExpectation_of_nonneg
#print axioms BanditRL.OnlineConvex.signedExpectation_eq_top
#print axioms signed_two_atoms
#print axioms finite_values_infinite_integral
end Tests.OnlineExpectation
