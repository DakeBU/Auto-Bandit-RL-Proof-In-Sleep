import BanditRLProof.LowerBounds.UniformCoding

namespace BanditRLProof.TextbookPartIVChapter14UniformCodeCanary

open LowerBounds

example (code : BinaryPrefixCode (Fin 3)) (hlen : ∀ a, (code.encode a).length = 2) :
    ¬ IsOptimalPrefixCode (fun _ : Fin 3 => (1 / 3 : ℝ)) code :=
  uniform_three_fixedLength_not_optimal code hlen

#print axioms LowerBounds.uniformPowerTwo_entropy
#print axioms LowerBounds.fixedLength_uniformPowerTwo_optimal
#print axioms LowerBounds.ternaryPrefixCode_uniform_length
#print axioms LowerBounds.uniform_three_fixedLength_not_optimal

end BanditRLProof.TextbookPartIVChapter14UniformCodeCanary
