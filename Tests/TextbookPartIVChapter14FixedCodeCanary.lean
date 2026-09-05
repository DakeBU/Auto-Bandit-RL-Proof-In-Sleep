import BanditRLProof.LowerBounds.FixedLengthCoding

namespace BanditRLProof.TextbookPartIVChapter14FixedCodeCanary

open LowerBounds

example : ∃ code : BinaryPrefixCode (Fin 5), ∀ a, (code.encode a).length = 3 :=
  exists_fixedLengthPrefixCode 3 (by norm_num) (by norm_num)

example {α : Type*} [Fintype α] (hcard : 1 < Fintype.card α) :
    ∃ code : BinaryPrefixCode α, ∀ a, (code.encode a).length = Nat.clog 2 (Fintype.card α) :=
  exists_ceilingLogPrefixCode hcard

#print axioms LowerBounds.exists_fixedLengthPrefixCode
#print axioms LowerBounds.exists_ceilingLogPrefixCode
#print axioms LowerBounds.expectedCodeLength_fixedLength

end BanditRLProof.TextbookPartIVChapter14FixedCodeCanary
