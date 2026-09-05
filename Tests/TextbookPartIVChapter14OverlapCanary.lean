import BanditRLProof.LowerBounds.CommonDensityOverlap

/-! Focused overlap/affinity checks, with no positive-density hypothesis. -/

namespace BanditRLProof.TextbookPartIVChapter14OverlapCanary

open MeasureTheory LowerBounds

example {α : Type*} [MeasurableSpace α] (P Q μ : Measure α)
    [IsProbabilityMeasure P] [IsProbabilityMeasure Q] [SigmaFinite μ]
    (hP : P ≪ μ) (hQ : Q ≪ μ) :
    (1 / 2 : ℝ) * commonDensityAffinity P Q μ ^ 2 ≤ commonDensityOverlap P Q μ :=
  half_commonDensityAffinity_sq_le_overlap P Q μ hP hQ

example (P Q : Measure ℝ) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (hP : P ≪ volume) (hQ : Q ≪ volume) :
    bretagnolleHuberScale (relativeEntropy P Q) ≤ commonDensityOverlap P Q volume :=
  bretagnolleHuberScale_le_commonDensityOverlap P Q volume hP hQ

example {α : Type*} [MeasurableSpace α] (P Q μ : Measure α)
    [IsFiniteMeasure P] [IsFiniteMeasure Q] :
    Integrable (fun x => Real.sqrt
      ((P.rnDeriv μ x).toReal * (Q.rnDeriv μ x).toReal)) μ :=
  integrable_commonDensityAffinity P Q μ

#print axioms LowerBounds.memLp_sqrt_of_integrable_nonneg
#print axioms LowerBounds.integral_sqrt_mul_sq_le
#print axioms LowerBounds.integrable_commonDensityAffinity
#print axioms LowerBounds.half_commonDensityAffinity_sq_le_overlap
#print axioms LowerBounds.commonDensityOverlap_eq_testingError
#print axioms LowerBounds.bretagnolleHuberScale_le_commonDensityOverlap

end BanditRLProof.TextbookPartIVChapter14OverlapCanary
