import BanditRLProof.LowerBounds.PrefixCodeSiblings

namespace BanditRLProof.TextbookPartIVChapter14SiblingCanary

open LowerBounds

example {α : Type*} [Fintype α] (code : BinaryPrefixCode (Option α))
    (p : α → ℝ) (q r : ℝ) :
    expectedCodeLength (Sum.elim p (fun b => if b then r else q)) code.expandSibling =
      expectedCodeLength (fun a => a.elim (q + r) p) code + q + r :=
  expectedCodeLength_expandSibling code p q r

example {α : Type*} (code : BinaryPrefixCode (Option α)) (b : Bool) :
    (code.expandSibling.encode (Sum.inr b)).length = (code.encode none).length + 1 := by
  simp [BinaryPrefixCode.expandSibling, siblingExpandedWord]

#print axioms LowerBounds.BinaryPrefixCode.extended_prefix_parent_eq
#print axioms LowerBounds.siblingExpandedWord_prefixFree
#print axioms LowerBounds.expectedCodeLength_expandSibling

end BanditRLProof.TextbookPartIVChapter14SiblingCanary
