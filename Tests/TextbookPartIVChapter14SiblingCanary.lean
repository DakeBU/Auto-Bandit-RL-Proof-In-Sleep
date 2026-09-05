import BanditRLProof

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

example {α : Type*} [Fintype α] (code : BinaryPrefixCode (α ⊕ Bool))
    (w : List Bool) (hw : w ≠ []) (hs : ∀ b, code.encode (.inr b) = w ++ [b])
    (p : α → ℝ) (q r : ℝ) :
    expectedCodeLength (fun a => a.elim (q + r) p) (code.contractSibling w hw hs) + q + r =
      expectedCodeLength (Sum.elim p (fun b => if b then r else q)) code :=
  expectedCodeLength_contractSibling code w hw hs p q r

example : IsOptimalPrefixCode (fun b : Bool => if b then (1 : ℝ) else 0) binaryRootPrefixCode :=
  binaryRootPrefixCode_optimal _ (by intro b; cases b <;> norm_num) (by simp)

#print axioms LowerBounds.sibling_parent_not_prefix_other
#print axioms LowerBounds.siblingContractedWord_prefixFree
#print axioms LowerBounds.expectedCodeLength_contractSibling
#print axioms LowerBounds.binaryRootPrefixCode_optimal

end BanditRLProof.TextbookPartIVChapter14SiblingCanary
