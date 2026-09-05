import BanditRLProof.LowerBounds.CommonDomination

namespace BanditRLProof.TextbookPartIVChapter14DominationCanary

open LowerBounds MeasureTheory

example {α : Type*} [MeasurableSpace α] (P Q : Measure α)
    [IsProbabilityMeasure P] [IsProbabilityMeasure Q] :
    ∃ μ : Measure α, SigmaFinite μ ∧ P ≪ μ ∧ Q ≪ μ :=
  exists_commonSigmaFiniteDominatingMeasure P Q

#print axioms LowerBounds.exists_commonFiniteDominatingMeasure
#print axioms LowerBounds.exists_commonSigmaFiniteDominatingMeasure
#print axioms LowerBounds.relativeEntropy_finite_lt_top_iff_ac

end BanditRLProof.TextbookPartIVChapter14DominationCanary
