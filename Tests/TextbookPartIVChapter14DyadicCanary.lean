import BanditRLProof.LowerBounds.DyadicAddresses

namespace BanditRLProof.TextbookPartIVChapter14DyadicCanary

open LowerBounds

example (L U : ℝ) (n : ℕ) (hL : 0 ≤ L) (hU : U ≤ 1)
    (hwidth : 2 * (1 / (2 : ℝ) ^ n) ≤ U - L) :
    ∃ w : List Bool, w.length = n ∧ L ≤ dyadicAddressLower w ∧ dyadicAddressUpper w < U :=
  exists_dyadicAddress_inside L U n hL hU hwidth

#print axioms LowerBounds.exists_binaryAddress
#print axioms LowerBounds.dyadicAddress_prefix_contained
#print axioms LowerBounds.exists_dyadicAddress_inside

end BanditRLProof.TextbookPartIVChapter14DyadicCanary
