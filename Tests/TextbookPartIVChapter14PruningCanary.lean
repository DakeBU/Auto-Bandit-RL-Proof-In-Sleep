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

example {α : Type*} [Fintype α] [DecidableEq α] [Nontrivial α]
    (p : α → ℝ) (hp : ∀ i, 0 ≤ p i) (original : BinaryPrefixCode α) :
    ∃ code : BinaryPrefixCode α, expectedCodeLength p code ≤ expectedCodeLength p original ∧
      ∃ a j w b, a ≠ j ∧ code.encode a = w ++ [b] ∧ code.encode j = w ++ [!b] ∧
        ∀ i, (code.encode i).length ≤ (code.encode a).length :=
  exists_no_worse_deepest_sibling_pair p hp original

#print axioms LowerBounds.totalCodeLength_pruneDeepest
#print axioms LowerBounds.exists_minimal_totalCodeLength_competitor
#print axioms LowerBounds.exists_competitor_with_deepest_siblings
#print axioms LowerBounds.exists_no_worse_deepest_sibling_pair

end BanditRLProof.TextbookPartIVChapter14PruningCanary
