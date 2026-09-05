import BanditRLProof.LowerBounds.ArithmeticBlockCoding

namespace BanditRLProof.TextbookPartIVChapter14ArithmeticBlockCanary

open LowerBounds

example {k : ℕ} (p : Fin k → ℝ) (hp : ∀ i, 0 ≤ p i) (hs : ∑ i, p i = 1) :
    Filter.Tendsto (fun n : ℕ => expectedCodeLength (sourceBlockMass p (n + 1))
      (arithmeticBlockCode p hp hs (n + 1)) / (n + 1))
      Filter.atTop (nhds (discreteEntropyBaseTwo Finset.univ p)) :=
  arithmeticBlockCode_rate_tendsto_entropy p hp hs

#print axioms LowerBounds.sourceBlockList_injective
example {k : ℕ} (p : Fin k → ℝ) (hp : ∀ i, 0 ≤ p i) (hs : ∑ i, p i = 1)
    (n : ℕ) (x : SourceBlock.{0,0} (Fin k) n) (hx : 0 < sourceBlockMass p n x) :
    (arithmeticInterval p (sourceBlockList n x)).1 ≤
      dyadicAddressLower ((arithmeticBlockCode p hp hs n).encode x).tail ∧
    dyadicAddressUpper ((arithmeticBlockCode p hp hs n).encode x).tail <
      (arithmeticInterval p (sourceBlockList n x)).2 :=
  arithmeticBlockCode_payload_interval p hp hs n x hx

#print axioms LowerBounds.arithmeticBlockCode_payload_interval
#print axioms LowerBounds.arithmeticBlockCode_expected_length_le
#print axioms LowerBounds.arithmeticBlockCode_rate_sandwich
#print axioms LowerBounds.arithmeticBlockCode_rate_tendsto_entropy

end BanditRLProof.TextbookPartIVChapter14ArithmeticBlockCanary
