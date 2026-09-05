import BanditRLProof

namespace BanditRLProof.TextbookPartIVChapter14ExchangeCanary

open LowerBounds

example {α : Type*} [Fintype α] [DecidableEq α] (p : α → ℝ) (c : BinaryPrefixCode α)
    (a b : α) (hab : a ≠ b) (hp : p a ≤ p b)
    (hl : (c.encode a).length ≤ (c.encode b).length) :
    expectedCodeLength p (c.relabel (Equiv.swap a b)) ≤ expectedCodeLength p c :=
  expectedCodeLength_swap_le p c a b hab hp hl

example {α : Type*} [Fintype α] [DecidableEq α] (p : α → ℝ) (c : BinaryPrefixCode α)
    (ho : IsOptimalPrefixCode p c) (a b : α) (hp : p a < p b) :
    (c.encode b).length ≤ (c.encode a).length := ho.length_antitone a b hp

#print axioms LowerBounds.expectedCodeLength_swap
#print axioms LowerBounds.expectedCodeLength_swap_le
#print axioms LowerBounds.IsOptimalPrefixCode.length_antitone
#print axioms LowerBounds.IsOptimalPrefixCode.entropy_sandwich

example : IsOptimalPrefixCode (fun _ : Unit => (1 : ℝ)) (singletonPrefixCode Unit) :=
  singletonPrefixCode_optimal _ (by simp) (by simp)

#print axioms LowerBounds.one_le_expectedCodeLength
#print axioms LowerBounds.singletonPrefixCode_optimal

end BanditRLProof.TextbookPartIVChapter14ExchangeCanary
