import BanditRLProof

namespace BanditRLProof.TextbookPartIVChapter14CodingBoundCanary

open LowerBounds

example {α : Type*} [Fintype α] [DecidableEq α] (p : α → ℝ)
    (hp : ∀ i, 0 ≤ p i) (hs : ∑ i, p i = 1) (c : BinaryPrefixCode α) :
    discreteEntropyBaseTwo Finset.univ p ≤ expectedCodeLength p c :=
  discreteEntropyBaseTwo_le_expectedCodeLength p hp hs c

example (l : ℕ) : (0 : ℝ) * Real.log (0 : ℝ)⁻¹ ≤
    0 * l * Real.log 2 + (1 / 2 : ℝ) ^ l - 0 :=
  entropy_term_le_codeLength_remainder le_rfl l

#print axioms LowerBounds.entropy_term_le_codeLength_remainder
#print axioms LowerBounds.discreteEntropyBaseTwo_le_expectedCodeLength

end BanditRLProof.TextbookPartIVChapter14CodingBoundCanary
