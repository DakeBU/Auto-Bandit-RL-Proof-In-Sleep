import BanditRLProof.LowerBounds.ShannonLengths

namespace BanditRLProof.TextbookPartIVChapter14ShannonCanary

open LowerBounds

example {α : Type*} [Fintype α] (p : α → ℝ)
    (hp : ∀ i, 0 ≤ p i) (hs : ∑ i, p i = 1) :
    (∑ i, p i * shannonLength (p i)) ≤ discreteEntropyBaseTwo Finset.univ p + 1 :=
  sum_weighted_shannonLength_le_entropy_add_one p hp hs

example {p : ℝ} (hp : 0 < p) : (1 / 2 : ℝ) ^ shannonLength p < p :=
  shannonLength_kraft_weight_lt hp

example : shannonLength 1 = 1 := by simp [shannonLength]

#print axioms LowerBounds.shannonLength_kraft_weight_lt
#print axioms LowerBounds.weighted_shannonLength_le
#print axioms LowerBounds.sum_weighted_shannonLength_le_entropy_add_one

example {α : Type*} [Fintype α] (p : α → ℝ)
    (hp : ∀ i, 0 ≤ p i) (hs : ∑ i, p i = 1) :
    ∃ l : α → ℕ, (∀ i, 0 < l i) ∧ (∑ i, (1 / 2 : ℝ) ^ l i) < 1 ∧
      (∑ i, p i * l i) ≤ discreteEntropyBaseTwo Finset.univ p + 1 :=
  exists_lengths_kraft_lt_one_entropy_bound p hp hs

#print axioms LowerBounds.sum_positive_shannon_weights_lt_one
#print axioms LowerBounds.exists_lengths_kraft_lt_one_entropy_bound

end BanditRLProof.TextbookPartIVChapter14ShannonCanary
