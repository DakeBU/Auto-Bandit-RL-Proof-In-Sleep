import BanditRLProof.LowerBounds.BlockEntropy

namespace BanditRLProof.TextbookPartIVChapter14BlockCanary

open LowerBounds

example {α : Type*} [Fintype α] [DecidableEq α] (p : α → ℝ)
    (hp : ∀ i, 0 ≤ p i) (hs : ∑ i, p i = 1) (n : ℕ) (hn : 0 < n) :
    ∃ code : BinaryPrefixCode (SourceBlock α n),
      discreteEntropyBaseTwo Finset.univ p ≤ expectedCodeLength (sourceBlockMass p n) code / n ∧
      expectedCodeLength (sourceBlockMass p n) code / n ≤
        discreteEntropyBaseTwo Finset.univ p + 1 / n :=
  exists_sourceBlock_code_rate_sandwich p hp hs n hn

example {α : Type*} [Fintype α] (p : α → ℝ) (hs : ∑ i, p i = 1) :
    discreteEntropyBaseTwo Finset.univ (sourceBlockMass p 3) =
      3 * discreteEntropyBaseTwo Finset.univ p :=
  discreteEntropyBaseTwo_sourceBlockMass p hs 3

#print axioms LowerBounds.entropy_product_term
#print axioms LowerBounds.discreteEntropy_prod
#print axioms LowerBounds.sum_sourceBlockMass
#print axioms LowerBounds.discreteEntropyBaseTwo_sourceBlockMass
#print axioms LowerBounds.exists_sourceBlock_code_rate_sandwich
#print axioms LowerBounds.sourceBlock_code_rate_lower_bound

end BanditRLProof.TextbookPartIVChapter14BlockCanary
