import BanditRLProof.CurvatureNoiseGapGeometry

namespace BanditRLProof.Tests

open CurvatureNoiseGap

#check CurvatureNoiseGap.tangentPairing_add_const_of_isSimplexTangent
#check CurvatureNoiseGap.weightedShiftEnergy_decomposition
#check CurvatureNoiseGap.weightedShiftEnergy_center_le
#check CurvatureNoiseGap.weightedShiftEnergy_eq_center_iff
#check CurvatureNoiseGap.weightedShiftEnergy_add_decomposition
#check CurvatureNoiseGap.weightedShiftEnergy_add_le_two

#print axioms CurvatureNoiseGap.tangentPairing_add_const_of_isSimplexTangent
#print axioms CurvatureNoiseGap.sum_weight_mul_sub_weightedCenter_eq_zero
#print axioms CurvatureNoiseGap.weightedShiftEnergy_decomposition_of_centered
#print axioms CurvatureNoiseGap.weightedShiftEnergy_decomposition
#print axioms CurvatureNoiseGap.weightedShiftEnergy_center_le
#print axioms CurvatureNoiseGap.weightedShiftEnergy_eq_center_iff
#print axioms CurvatureNoiseGap.weightedShiftEnergy_add_decomposition
#print axioms CurvatureNoiseGap.weightedShiftEnergy_add_le_two

example (signal direction : Fin 3 -> Real) (shift : Real)
    (hdirection : IsSimplexTangent Finset.univ direction) :
    tangentPairing Finset.univ (fun i => signal i + shift) direction =
      tangentPairing Finset.univ signal direction :=
  tangentPairing_add_const_of_isSimplexTangent
    Finset.univ signal direction shift hdirection

end BanditRLProof.Tests
