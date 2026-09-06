import BanditRLProof.LowerBounds.HuffmanStep

namespace BanditRLProof.TextbookPartIVChapter14HuffmanStepCanary

open LowerBounds

example {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α]
    (p : α → ℝ) (q r : ℝ) (hp : ∀ i, 0 ≤ p i) (hq : 0 ≤ q)
    (hqr : q ≤ r) (hr : ∀ i, r ≤ p i)
    (code : BinaryPrefixCode (Option α))
    (hopt : IsOptimalPrefixCode (fun a => a.elim (q + r) p) code) :
    IsOptimalPrefixCode (Sum.elim p (fun b => if b then r else q)) code.expandSibling :=
  hopt.expand_least_weights p q r hp hq hqr hr code

#print axioms LowerBounds.exists_oriented_sibling_code
#print axioms LowerBounds.IsOptimalPrefixCode.expand_least_weights

end BanditRLProof.TextbookPartIVChapter14HuffmanStepCanary
