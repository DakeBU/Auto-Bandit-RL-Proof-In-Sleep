import BanditRLProof

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

example {α : Type*} [Fintype α] [DecidableEq α] (p : α → ℝ)
    (hp : ∀ i, 0 ≤ p i) (hs : ∑ i, p i = 1) :
    ∃ code : BinaryPrefixCode α,
      discreteEntropyBaseTwo Finset.univ p ≤ expectedCodeLength p code ∧
      expectedCodeLength p code ≤ discreteEntropyBaseTwo Finset.univ p + 1 :=
  exists_binaryPrefixCode_entropy_sandwich p hp hs

-- Zero-probability symbols are retained in the code's domain.
example : ∃ code : BinaryPrefixCode Bool,
    expectedCodeLength (fun b : Bool => if b then 1 else 0) code ≤
      discreteEntropyBaseTwo Finset.univ (fun b : Bool => if b then 1 else 0) + 1 := by
  obtain ⟨c, _, hc⟩ := exists_binaryPrefixCode_entropy_sandwich
    (fun b : Bool => if b then (1 : ℝ) else 0)
    (by intro b; cases b <;> norm_num) (by simp)
  exact ⟨c, hc⟩

#print axioms LowerBounds.exists_prefix_encoding_of_kraft_lt_one
#print axioms LowerBounds.exists_binaryPrefixCode_of_kraft_lt_one
#print axioms LowerBounds.exists_binaryPrefixCode_entropy_sandwich

end BanditRLProof.TextbookPartIVChapter14PrefixConstructionCanary
