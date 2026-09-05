import BanditRLProof.LowerBounds.CrossEntropy

namespace BanditRLProof.TextbookPartIVChapter14CrossEntropyCanary

open LowerBounds MeasureTheory

example {α : Type*} [Fintype α] [MeasurableSpace α] [MeasurableSingletonClass α]
    (P Q : Measure α) [IsProbabilityMeasure P] [IsProbabilityMeasure Q] (h : P ≪ Q) :
    relativeEntropy P Q = ENNReal.ofReal
      (discreteCrossEntropy (fun i => (P {i}).toReal) (fun i => (Q {i}).toReal) -
        discreteEntropy Finset.univ (fun i => (P {i}).toReal)) :=
  relativeEntropy_finite_crossEntropy P Q h

#print axioms LowerBounds.discreteCrossEntropy_sub_entropy
#print axioms LowerBounds.relativeEntropy_finite_crossEntropy
#print axioms LowerBounds.entropyTerm_tendsto_zero_right

end BanditRLProof.TextbookPartIVChapter14CrossEntropyCanary
