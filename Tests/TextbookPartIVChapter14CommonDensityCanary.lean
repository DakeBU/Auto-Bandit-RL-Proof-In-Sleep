import BanditRLProof.LowerBounds.CommonDensityKL

/-! Focused common-density checks; the dominating measure need not be finite. -/

namespace BanditRLProof.TextbookPartIVChapter14CommonDensityCanary

open MeasureTheory LowerBounds Classical
open scoped ENNReal

example {α : Type*} [MeasurableSpace α] (P Q μ : Measure α)
    [IsProbabilityMeasure P] [IsProbabilityMeasure Q] [SigmaFinite μ]
    (hP : P ≪ μ) (hQ : Q ≪ μ) :
    relativeEntropy P Q = if P ≪ Q ∧
      Integrable (fun x => (P.rnDeriv μ x).toReal *
        Real.log ((P.rnDeriv μ x).toReal / (Q.rnDeriv μ x).toReal)) μ then
      ENNReal.ofReal (∫ x, (P.rnDeriv μ x).toReal *
        Real.log ((P.rnDeriv μ x).toReal / (Q.rnDeriv μ x).toReal) ∂μ)
      else (⊤ : ENNReal) :=
  relativeEntropy_commonDensity_eq_if P Q μ hP hQ

-- Lebesgue measure on the real line is an allowed, non-finite dominating measure.
example (P Q : Measure ℝ) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (hP : P ≪ volume) (hQ : Q ≪ volume) (hPQ : P ≪ Q) :
    relativeEntropy P Q = ∫⁻ x, Q.rnDeriv volume x * ENNReal.ofReal
      (InformationTheory.klFun ((P.rnDeriv volume x / Q.rnDeriv volume x).toReal)) ∂volume :=
  relativeEntropy_commonDensity_klFun P Q volume hP hQ hPQ

#print axioms LowerBounds.llr_ae_eq_log_commonDensity
#print axioms LowerBounds.integrable_commonDensity_iff
#print axioms LowerBounds.relativeEntropy_commonDensity_of_integrable
#print axioms LowerBounds.relativeEntropy_commonDensity_eq_if
#print axioms LowerBounds.relativeEntropy_commonDensity_klFun

end BanditRLProof.TextbookPartIVChapter14CommonDensityCanary
