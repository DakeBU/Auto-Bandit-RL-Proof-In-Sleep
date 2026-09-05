import BanditRLProof.LowerBounds.PrefixCodePruning

namespace BanditRLProof.TextbookPartIVChapter14PruningCanary

open LowerBounds

example {α : Type*} [Fintype α] [DecidableEq α] (p : α → ℝ)
    (code : BinaryPrefixCode α) (a : α) (w : List Bool) (b : Bool)
    (hw : w ≠ []) (ha : code.encode a = w ++ [b])
    (hm : ∀ i, (code.encode i).length ≤ (code.encode a).length)
    (hs : ∀ i, code.encode i ≠ w ++ [!b]) :
    expectedCodeLength p (code.pruneDeepest a w b hw ha hm hs) =
      expectedCodeLength p code - p a :=
  expectedCodeLength_pruneDeepest p code a w b hw ha hm hs

#print axioms LowerBounds.deepest_parent_incomparable
#print axioms LowerBounds.expectedCodeLength_replaceWord
#print axioms LowerBounds.expectedCodeLength_pruneDeepest
#print axioms LowerBounds.expectedCodeLength_pruneDeepest_le

end BanditRLProof.TextbookPartIVChapter14PruningCanary
