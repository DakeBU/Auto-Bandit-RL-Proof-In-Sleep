import BanditRLProof

namespace BanditRLProof.TextbookPartIVChapter14AffinityCanary

open MeasureTheory LowerBounds

example {α : Type*} [MeasurableSpace α] (P Q μ : Measure α)
    [IsProbabilityMeasure P] [IsProbabilityMeasure Q] [SigmaFinite μ]
    (hQ : Q ≪ μ) :
    bretagnolleHuberScale (relativeEntropy P Q) ≤
      (1 / 2 : ℝ) * commonDensityAffinity P Q μ ^ 2 :=
  bretagnolleHuberScale_le_half_commonDensityAffinity_sq P Q μ hQ

-- Eq. (14.8) now follows through the source's Jensen/Cauchy--Schwarz route.
example (P Q : Measure ℝ) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (hP : P ≪ volume) (hQ : Q ≪ volume) :
    bretagnolleHuberScale (relativeEntropy P Q) ≤ commonDensityOverlap P Q volume :=
  (bretagnolleHuberScale_le_half_commonDensityAffinity_sq P Q volume hQ).trans
    (half_commonDensityAffinity_sq_le_overlap P Q volume hP hQ)

-- The complete source proof route reaches every measurable testing event.
example {α : Type*} [MeasurableSpace α] (P Q μ : Measure α)
    [IsProbabilityMeasure P] [IsProbabilityMeasure Q] [SigmaFinite μ]
    (hP : P ≪ μ) (hQ : Q ≪ μ) {A : Set α} (hA : MeasurableSet A) :
    bretagnolleHuberScale (relativeEntropy P Q) ≤ P.real A + Q.real Aᶜ :=
  ((bretagnolleHuberScale_le_half_commonDensityAffinity_sq P Q μ hQ).trans
    (half_commonDensityAffinity_sq_le_overlap P Q μ hP hQ)).trans
      (commonDensityOverlap_le_testingError P Q μ hP hQ hA)

-- The source also permits the reversed KL direction on the same error sum.
example {α : Type*} [MeasurableSpace α] (P Q : Measure α)
    [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    {A : Set α} (hA : MeasurableSet A) :
    bretagnolleHuberScale (relativeEntropy Q P) ≤ P.real A + Q.real Aᶜ := by
  simpa only [compl_compl, add_comm] using
    (bretagnolleHuber (P := Q) (Q := P) hA.compl)

#print axioms LowerBounds.commonDensityOverlap_le_testingError

example : (0 : ℝ) * Real.exp (-Real.log 0 / 2) = Real.sqrt 0 :=
  mul_exp_neg_half_log_eq_sqrt le_rfl

#print axioms LowerBounds.mul_exp_neg_half_log_eq_sqrt
#print axioms LowerBounds.integrable_sqrt_rnDeriv
#print axioms LowerBounds.integrable_exp_neg_half_llr
#print axioms LowerBounds.integral_exp_neg_half_llr_eq
#print axioms LowerBounds.exp_neg_half_integral_llr_le_rnAffinity
#print axioms LowerBounds.rnAffinity_eq_commonDensityAffinity
#print axioms LowerBounds.exp_neg_half_integral_llr_le_commonDensityAffinity
#print axioms LowerBounds.bretagnolleHuberScale_le_half_commonDensityAffinity_sq

end BanditRLProof.TextbookPartIVChapter14AffinityCanary
