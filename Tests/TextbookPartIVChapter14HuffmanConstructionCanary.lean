import BanditRLProof.LowerBounds.HuffmanConstruction

namespace BanditRLProof.TextbookPartIVChapter14HuffmanConstructionCanary

open LowerBounds

example {α : Type*} [Fintype α] (p : α → ℝ) (hp : ∀ i, 0 ≤ p i)
    (other : BinaryPrefixCode α) :
    expectedCodeLength p (huffmanCode p hp) ≤ expectedCodeLength p other :=
  huffmanCode_optimal p hp other

example {α : Type*} [Fintype α] (p : α → ℝ) (hp : ∀ i, 0 ≤ p i)
    (hs : ∑ i, p i = 1) :
    discreteEntropyBaseTwo Finset.univ p ≤ expectedCodeLength p (huffmanCode p hp) ∧
      expectedCodeLength p (huffmanCode p hp) ≤ discreteEntropyBaseTwo Finset.univ p + 1 :=
  huffmanCode_entropy_sandwich p hp hs

#print axioms LowerBounds.huffmanOptimalCode
#print axioms LowerBounds.huffmanCode_optimal
#print axioms LowerBounds.huffmanCode_entropy_sandwich

end BanditRLProof.TextbookPartIVChapter14HuffmanConstructionCanary
