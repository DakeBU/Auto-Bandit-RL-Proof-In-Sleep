import BanditRLProof.LowerBounds.RelativeEntropyNonMetric

namespace BanditRLProof.TextbookPartIVChapter14NonMetricCanary

open LowerBounds ProbabilityTheory

example : ¬ relativeEntropy (gaussianReal 0 1) (gaussianReal 2 1) ≤
    relativeEntropy (gaussianReal 0 1) (gaussianReal 1 1) +
      relativeEntropy (gaussianReal 1 1) (gaussianReal 2 1) :=
  not_le_of_gt relativeEntropy_triangle_counterexample

example : bernoulliRelativeEntropy 0 (1 / 2) ≠ bernoulliRelativeEntropy (1 / 2) 0 :=
  bernoulliRelativeEntropy_asymmetry

#print axioms LowerBounds.relativeEntropy_triangle_counterexample
#print axioms LowerBounds.bernoulliRelativeEntropy_asymmetry

end BanditRLProof.TextbookPartIVChapter14NonMetricCanary
