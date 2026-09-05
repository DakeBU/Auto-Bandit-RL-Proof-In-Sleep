import BanditRLProof.LowerBounds.ArithmeticPrefixCode

namespace BanditRLProof.TextbookPartIVChapter14ArithmeticPrefixCanary

open LowerBounds

example {mass : ℝ} (hm : 0 < mass) (hm1 : mass ≤ 1) :
    (arithmeticLength mass : ℝ) ≤ Real.log mass⁻¹ / Real.log 2 + 2 :=
  arithmeticLength_le_information_add_two hm hm1

#print axioms LowerBounds.arithmeticAddress_prefix_forces_eq
#print axioms LowerBounds.exists_arithmeticPrefixCode
#print axioms LowerBounds.arithmeticLength_width_budget
#print axioms LowerBounds.arithmeticLength_le_information_add_two

end BanditRLProof.TextbookPartIVChapter14ArithmeticPrefixCanary
