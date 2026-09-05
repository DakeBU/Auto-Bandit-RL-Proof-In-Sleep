import BanditRLProof.LowerBounds.PrefixCodeConstruction

namespace BanditRLProof.TextbookPartIVChapter14PrefixConstructionCanary

open LowerBounds

example : (binaryWords 3).card = 8 := by rw [card_binaryWords]; norm_num

example (S : Finset (List Bool)) (n : ℕ) (hl : ∀ w ∈ S, w.length ≤ n)
    (hb : (∑ w ∈ S, 2 ^ (n - w.length)) < 2 ^ n) :
    ∃ v : List Bool, v.length = n ∧ ∀ w ∈ S, ¬ w <+: v :=
  exists_binaryWord_avoiding_prefixes S n hl hb

#print axioms LowerBounds.card_binaryWords
#print axioms LowerBounds.mem_binaryWords_iff
#print axioms LowerBounds.card_binaryExtensions
#print axioms LowerBounds.mem_binaryExtensions_iff
#print axioms LowerBounds.binaryExtensions_disjoint_of_incomparable
#print axioms LowerBounds.exists_binaryWord_avoiding_prefixes

example (S : Finset (List Bool)) (n : ℕ)
    (hf : ∀ a ∈ S, ∀ b ∈ S, a <+: b → a = b)
    (hl : ∀ w ∈ S, w.length ≤ n)
    (hk : (∑ w ∈ S, (1 / 2 : ℝ) ^ w.length) < 1) :
    ∃ v : List Bool, v.length = n ∧ v ∉ S ∧
      ∀ a ∈ insert v S, ∀ b ∈ insert v S, a <+: b → a = b :=
  exists_prefixFree_insert_of_kraft_lt_one S n hf hl hk

#print axioms LowerBounds.binary_level_mul_kraft_weight
#print axioms LowerBounds.exists_binaryWord_of_kraft_lt_one
#print axioms LowerBounds.exists_prefixFree_insert_of_kraft_lt_one

end BanditRLProof.TextbookPartIVChapter14PrefixConstructionCanary
