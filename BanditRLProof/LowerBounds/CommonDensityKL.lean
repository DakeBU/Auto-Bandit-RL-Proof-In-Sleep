import BanditRLProof.LowerBounds.InformationTheory

/-! Chapter 14 Eq. (14.6), with exact common-density and infinite branches. -/

namespace BanditRLProof.LowerBounds

open MeasureTheory Set
open scoped ENNReal

noncomputable section

/-- The log likelihood ratio is the log ratio of two common-measure densities. -/
theorem llr_ae_eq_log_commonDensity
    {α : Type*} [MeasurableSpace α] (P Q μ : Measure α)
    [IsFiniteMeasure P] [IsFiniteMeasure Q] [SigmaFinite μ]
    (hP : P ≪ μ) (hQ : Q ≪ μ) (hPQ : P ≪ Q) :
    llr P Q =ᵐ[P] fun x => Real.log ((P.rnDeriv μ x).toReal / (Q.rnDeriv μ x).toReal) := by
  filter_upwards [hPQ.ae_le (Measure.rnDeriv_eq_div hP hQ)] with x hx
  simp [llr, hx, ENNReal.toReal_div]

/-- Integrability of the common-density logarithmic integrand is exactly that of LLR. -/
theorem integrable_commonDensity_iff
    {α : Type*} [MeasurableSpace α] (P Q μ : Measure α)
    [IsFiniteMeasure P] [IsFiniteMeasure Q] [SigmaFinite μ]
    (hP : P ≪ μ) (hQ : Q ≪ μ) (hPQ : P ≪ Q) :
    Integrable (fun x => (P.rnDeriv μ x).toReal *
      Real.log ((P.rnDeriv μ x).toReal / (Q.rnDeriv μ x).toReal)) μ ↔
      Integrable (llr P Q) P := by
  rw [integrable_toReal_rnDeriv_mul_iff hP]
  exact integrable_congr (llr_ae_eq_log_commonDensity P Q μ hP hQ hPQ).symm

/-- Eq. (14.6) in its supported, integrable probability-measure branch. -/
theorem relativeEntropy_commonDensity_of_integrable
    {α : Type*} [MeasurableSpace α] (P Q μ : Measure α)
    [IsProbabilityMeasure P] [IsProbabilityMeasure Q] [SigmaFinite μ]
    (hP : P ≪ μ) (hQ : Q ≪ μ) (hPQ : P ≪ Q)
    (hi : Integrable (fun x => (P.rnDeriv μ x).toReal *
      Real.log ((P.rnDeriv μ x).toReal / (Q.rnDeriv μ x).toReal)) μ) :
    relativeEntropy P Q = ENNReal.ofReal (∫ x, (P.rnDeriv μ x).toReal *
      Real.log ((P.rnDeriv μ x).toReal / (Q.rnDeriv μ x).toReal) ∂μ) := by
  rw [relativeEntropy_of_probability_absolutelyContinuous_of_integrable P Q hPQ
    ((integrable_commonDensity_iff P Q μ hP hQ hPQ).1 hi)]
  congr 1
  exact (integral_congr_ae (llr_ae_eq_log_commonDensity P Q μ hP hQ hPQ)).trans
    (integral_toReal_rnDeriv_mul hP).symm

open Classical in
/-- Common-density formula with singular and nonintegrable branches kept infinite. -/
theorem relativeEntropy_commonDensity_eq_if
    {α : Type*} [MeasurableSpace α] (P Q μ : Measure α)
    [IsProbabilityMeasure P] [IsProbabilityMeasure Q] [SigmaFinite μ]
    (hP : P ≪ μ) (hQ : Q ≪ μ) :
    relativeEntropy P Q = if P ≪ Q ∧
      Integrable (fun x => (P.rnDeriv μ x).toReal *
        Real.log ((P.rnDeriv μ x).toReal / (Q.rnDeriv μ x).toReal)) μ then
      ENNReal.ofReal (∫ x, (P.rnDeriv μ x).toReal *
        Real.log ((P.rnDeriv μ x).toReal / (Q.rnDeriv μ x).toReal) ∂μ)
      else (⊤ : ENNReal) := by
  classical
  split_ifs with h
  · exact relativeEntropy_commonDensity_of_integrable P Q μ hP hQ h.1 h.2
  · apply not_ne_iff.mp
    intro hne
    have hr := relativeEntropy_ne_top_iff.1 hne
    exact h ⟨hr.1, (integrable_commonDensity_iff P Q μ hP hQ hr.1).2 hr.2⟩

/-- Nonnegative common-density KL integral, valid even at infinite KL under AC. -/
theorem relativeEntropy_commonDensity_klFun
    {α : Type*} [MeasurableSpace α] (P Q μ : Measure α)
    [IsFiniteMeasure P] [IsFiniteMeasure Q] [SigmaFinite μ]
    (hP : P ≪ μ) (hQ : Q ≪ μ) (hPQ : P ≪ Q) :
    relativeEntropy P Q = ∫⁻ x, Q.rnDeriv μ x * ENNReal.ofReal
      (InformationTheory.klFun ((P.rnDeriv μ x / Q.rnDeriv μ x).toReal)) ∂μ := by
  calc
    _ = ∫⁻ x, ENNReal.ofReal (InformationTheory.klFun (P.rnDeriv Q x).toReal) ∂Q :=
      InformationTheory.klDiv_eq_lintegral_klFun_of_ac hPQ
    _ = ∫⁻ x, ENNReal.ofReal
        (InformationTheory.klFun ((P.rnDeriv μ x / Q.rnDeriv μ x).toReal)) ∂Q := by
      apply lintegral_congr_ae
      filter_upwards [Measure.rnDeriv_eq_div hP hQ] with x hx
      rw [hx]
    _ = _ := (lintegral_rnDeriv_mul hQ (by fun_prop)).symm

end
end BanditRLProof.LowerBounds
