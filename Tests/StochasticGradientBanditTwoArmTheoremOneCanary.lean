import BanditRLProof.Algorithms.StochasticGradientBanditTwoArmTheoremOne

/-!
# Two-arm SGB Theorem-1 endpoint canary

This canary pins the dependency-closed, source-faithful Theorem 1 endpoint
from Baudry--Johnson--Vary--Pike-Burke--Rebeschini (NeurIPS 2025).
`tailHorizon + 1` is the paper horizon `T`: trace coordinate zero is the
uniform source round `t = 1`, while Lean tail index `n` is source round
`t = n + 2`.
-/

namespace BanditRLProof
namespace StochasticGradientBandit

open MeasureTheory ProbabilityTheory
open scoped BigOperators ProbabilityTheory

#check twoArmTrajectorySourceIncrement
#check measurable_twoArmTrajectorySourceIncrement
#check integrable_twoArmTrajectorySourceIncrement
#check twoArmTrajectorySourceIncrement_condExp_ae_eq_integral_condDistrib
#check twoArmTrajectorySourceIncrement_condExp_ae_eq_successFailure
#check twoArmTrajectoryParameterZero_succ
#check integrable_twoArmTrajectoryParameterZero
#check integral_twoArmTrajectorySourceIncrement_eq_successFailure
#check integral_twoArmTrajectoryParameterZero_succ
#check twoArmInitialSourceIncrement
#check measurable_twoArmInitialSourceIncrement
#check integral_twoArmInitialSourceIncrement_eq_quarter_gap
#check integral_twoArmTrajectoryParameterZero_zero
#check integral_twoArmTrajectoryParameterZero_eq_successFailureSum
#check measurable_twoArmSuccessFailureMass
#check integrable_twoArmSuccessFailureMass
#check integral_twoArmFailureMass_eq_successFailure_add_sq
#check twoArmGeneratedExpectedPseudoRegret
#check twoArmGeneratedExpectedPseudoRegret_eq_parameter_add_failureSq
#check integral_twoArmTrajectoryParameterZero_le_half_log_forwardPotential
#check integral_twoArmSuccessProbability_sq_le_one
#check integral_twoArmForwardPotential_le_source_bound
#check integral_twoArmTrajectoryParameterZero_le_source_log_bound
#check twoArmActionGap
#check measurable_twoArmActionGap
#check integral_twoArmInitialActionGap_eq_half
#check integral_twoArmSuccessorActionGap_eq_failureMass
#check twoArmSampledPseudoRegret
#check integral_twoArmSampledPseudoRegret_eq_generated
#check twoArmGeneratedExpectedPseudoRegret_le_sourceTheoremOne
#check integral_twoArmSampledPseudoRegret_le_sourceTheoremOne
#check twoArmFixedIIDDirac_theoremOne

example
    (armLaw : Fin 2 -> Measure Real)
    (hprob : forall arm, IsProbabilityMeasure (armLaw arm))
    (mean : Fin 2 -> Real)
    (hbound : forall arm, ∀ᵐ reward ∂armLaw arm, |reward| <= 1)
    (hmean : forall arm, integral (armLaw arm) id = mean arm)
    (eta Delta : Real) (heta : 0 < eta)
    (hDelta : 0 < Delta) (hDelta_lt_one : Delta < 1)
    (hgap : mean 0 - mean 1 = Delta)
    (hmargin : eta * sourceC eta < Delta)
    (tailHorizon : Nat) :
    integral
        (twoArmTrajectoryMeasure (Measure.dirac ()) eta
          (twoArmFixedIIDEnvironment armLaw hprob))
        (twoArmSampledPseudoRegret (Env := Unit) Delta
          (tailHorizon + 1)) <=
      Real.log
          (1 + 4 * eta * Delta * ((tailHorizon + 1 : Nat) : Real)) /
          (2 * eta) +
        Delta / (2 * eta * (Delta - eta * sourceC eta)) :=
  twoArmFixedIIDDirac_theoremOne armLaw hprob mean hbound hmean eta Delta
    heta hDelta hDelta_lt_one hgap hmargin tailHorizon

#print axioms integral_twoArmTrajectoryParameterZero_eq_successFailureSum
#print axioms integral_twoArmSampledPseudoRegret_eq_generated
#print axioms twoArmGeneratedExpectedPseudoRegret_le_sourceTheoremOne
#print axioms twoArmFixedIIDDirac_theoremOne

end StochasticGradientBandit
end BanditRLProof
