import BanditRLProof.OnlineConvexExtended
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Real

noncomputable section
open Set Filter MeasureTheory
open scoped ENNReal
namespace BanditRL.OnlineConvex
variable {Ω : Type*} [MeasurableSpace Ω]

def positiveIntegral (μ : Measure Ω) (f : Ω → EReal) : ℝ≥0∞ :=
  ∫⁻ ω, (f ω).toENNReal ∂μ

def negativeIntegral (μ : Measure Ω) (f : Ω → EReal) : ℝ≥0∞ :=
  ∫⁻ ω, (-f ω).toENNReal ∂μ

/-- Signed positive-minus-negative expectation. Mathematical use requires at least one
part to be finite; Jensen's source assumptions will prove the negative part finite. -/
def signedExpectation (μ : Measure Ω) (f : Ω → EReal) : EReal :=
  (positiveIntegral μ f : EReal) - (negativeIntegral μ f : EReal)

theorem positiveIntegral_coe (μ : Measure Ω) (f : Ω → ℝ) :
    positiveIntegral μ (fun ω => (f ω : EReal)) = ∫⁻ ω, ENNReal.ofReal (f ω) ∂μ := by
  simp [positiveIntegral]

theorem negativeIntegral_coe (μ : Measure Ω) (f : Ω → ℝ) :
    negativeIntegral μ (fun ω => (f ω : EReal)) = ∫⁻ ω, ENNReal.ofReal (-f ω) ∂μ := by
  simp [negativeIntegral, ← EReal.coe_neg]

theorem positiveIntegral_coe_ne_top (μ : Measure Ω) (f : Ω → ℝ) (hf : Integrable f μ) :
    positiveIntegral μ (fun ω => (f ω : EReal)) ≠ ∞ := by
  rw [positiveIntegral_coe]
  have hp := (lintegral_ofReal_ne_top_iff_integrable
    hf.pos_part.aestronglyMeasurable
    (ae_of_all μ (fun ω => le_max_right (f ω) 0))).mpr hf.pos_part
  simpa using hp

theorem negativeIntegral_coe_ne_top (μ : Measure Ω) (f : Ω → ℝ) (hf : Integrable f μ) :
    negativeIntegral μ (fun ω => (f ω : EReal)) ≠ ∞ := by
  simpa only [negativeIntegral_coe, positiveIntegral_coe] using
    positiveIntegral_coe_ne_top μ (fun ω => -f ω) hf.neg

theorem signedExpectation_coe_integrable (μ : Measure Ω) (f : Ω → ℝ) (hf : Integrable f μ) :
    signedExpectation μ (fun ω => (f ω : EReal)) = ((∫ ω, f ω ∂μ : ℝ) : EReal) := by
  rw [signedExpectation,
    ← EReal.coe_ennreal_toReal (positiveIntegral_coe_ne_top μ f hf),
    ← EReal.coe_ennreal_toReal (negativeIntegral_coe_ne_top μ f hf),
    ← EReal.coe_sub]
  congr 1
  rw [positiveIntegral_coe, negativeIntegral_coe]
  exact (integral_eq_lintegral_pos_part_sub_lintegral_neg_part hf).symm

theorem signedExpectation_of_nonneg (μ : Measure Ω) (f : Ω → EReal)
    (hf : ∀ᵐ ω ∂μ, 0 ≤ f ω) :
    signedExpectation μ f = (positiveIntegral μ f : EReal) := by
  have hn : negativeIntegral μ f = 0 := by
    unfold negativeIntegral
    calc
      (∫⁻ ω, (-f ω).toENNReal ∂μ) = ∫⁻ _ : Ω, (0 : ℝ≥0∞) ∂μ := by
        apply lintegral_congr_ae
        filter_upwards [hf] with ω hω
        exact EReal.toENNReal_of_nonpos (EReal.neg_le_zero.mpr hω)
      _ = 0 := lintegral_zero
  simp [signedExpectation, hn]

theorem signedExpectation_eq_top (μ : Measure Ω) (f : Ω → EReal)
    (hp : positiveIntegral μ f = ∞) (hn : negativeIntegral μ f ≠ ∞) :
    signedExpectation μ f = ⊤ := by
  rw [signedExpectation, hp, EReal.coe_ennreal_top]
  exact EReal.top_sub (fun h => hn (EReal.coe_ennreal_eq_top_iff.mp h))

end BanditRL.OnlineConvex
