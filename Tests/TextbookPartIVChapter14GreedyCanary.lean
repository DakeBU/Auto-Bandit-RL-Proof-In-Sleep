import BanditRLProof.LowerBounds.PrefixCodeGreedy

namespace BanditRLProof.TextbookPartIVChapter14GreedyCanary

open LowerBounds

example {α : Type*} [Fintype α] [DecidableEq α] [Nontrivial α]
    (p : α → ℝ) (hp : ∀ i, 0 ≤ p i) (original : BinaryPrefixCode α)
    (a b : α) (hab : a ≠ b) (ha : ∀ i, p a ≤ p i)
    (hb : ∀ i, i ≠ a → p b ≤ p i) :
    ∃ code : BinaryPrefixCode α, expectedCodeLength p code ≤ expectedCodeLength p original ∧
      ∃ w bit, code.encode a = w ++ [bit] ∧ code.encode b = w ++ [!bit] ∧
        ∀ i, (code.encode i).length ≤ (code.encode a).length :=
  exists_no_worse_least_weight_siblings p hp original a b hab ha hb

#print axioms LowerBounds.expectedCodeLength_swap_le_allow_eq
#print axioms LowerBounds.exists_no_worse_least_weight_siblings

end BanditRLProof.TextbookPartIVChapter14GreedyCanary
