import BanditRLProof.Algorithms.StochasticGradientBanditTheoremFourContractAudit

/-!
# SGB Theorem-4 source-contract audit canary

This canary pins only the finite Appendix-E source-contract leaves.  It does
not promote Theorem 4 or the missing generated-process probability producers.
-/

namespace BanditRLProof
namespace StochasticGradientBandit

open scoped BigOperators

#check theoremFourStepOneMargin
#check theoremFourStepFourSurvivalLowerBound
#check theoremFourStepOneMargin_pos
#check theoremFourStepFourSurvivalLowerBound_pos
#check theoremFourStepFour_survivalMass_ge
#check theoremFourStepFour_survivalMass_pos
#check theoremFourFiniteGeometricPhaseMass_le_inv
#check theoremFourFiniteTransientMass_le_inv

example : theoremFourStepFourSurvivalLowerBound (1 / 4) (1 / 4) = 1 / 8 := by
  norm_num [theoremFourStepFourSurvivalLowerBound]

example : 0 < theoremFourStepFourSurvivalLowerBound (1 / 4) (1 / 4) := by
  exact theoremFourStepFourSurvivalLowerBound_pos (1 / 4) (1 / 4)
    (by norm_num) (by norm_num)

example (phaseCount : Nat) :
    (Finset.range phaseCount).sum (fun phase => ((1 : Real) / 2) ^ phase) <= 2 := by
  convert theoremFourFiniteGeometricPhaseMass_le_inv (1 / 2)
    (by norm_num) (by norm_num) phaseCount using 1 <;> norm_num

#print axioms theoremFourStepOneMargin_pos
#print axioms theoremFourStepFour_survivalMass_ge
#print axioms theoremFourFiniteTransientMass_le_inv

end StochasticGradientBandit
end BanditRLProof
