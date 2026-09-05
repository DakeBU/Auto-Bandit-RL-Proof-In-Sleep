import BanditRLProof.LowerBounds.ArithmeticZeroExtension

namespace BanditRLProof.TextbookPartIVChapter14ArithmeticZeroCanary

open LowerBounds

example {α : Type*} [Fintype α] (p : α → ℝ)
    (hp : ∀ a, 0 ≤ p a) (hs : ∑ a, p a = 1)
    (positive : BinaryPrefixCode {a // 0 < p a}) (fallback : BinaryPrefixCode α)
    (hpos : ∀ a (ha : 0 < p a), ((positive.encode ⟨a, ha⟩).length : ℝ) ≤
      Real.log (p a)⁻¹ / Real.log 2 + 2) :
    expectedCodeLength p (positive.extendZeroMass p fallback) ≤
      discreteEntropyBaseTwo Finset.univ p + 3 :=
  expectedCodeLength_extendZeroMass_le p hp hs positive fallback hpos

#print axioms LowerBounds.supportTaggedWord_prefixFree
#print axioms LowerBounds.expectedCodeLength_extendZeroMass_le
#print axioms LowerBounds.exists_zeroSafe_arithmeticCode

end BanditRLProof.TextbookPartIVChapter14ArithmeticZeroCanary
