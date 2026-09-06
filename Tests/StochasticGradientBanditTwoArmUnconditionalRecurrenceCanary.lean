import BanditRLProof.Algorithms.StochasticGradientBanditTwoArmUnconditionalRecurrence

/-!
# Two-arm SGB unconditional-recurrence API canary

This canary pins the source-time fence and the complete public API of the
unconditional recurrence leaf.  An inclusive Lean prefix index `n` denotes
source time `n + 2`; `tailHorizon` covers source rounds
`t = 2, ..., tailHorizon + 1`, while `twoArmFullFailureMassSqSum_le` adds the
normalized source-round-1 failure square `1 / 4`.

The canary deliberately stops before Equation (7), the terminal logarithmic
consumer, and the assembled paper Theorem 1.
-/

namespace BanditRLProof
namespace StochasticGradientBandit

open MeasureTheory ProbabilityTheory
open scoped BigOperators ProbabilityTheory

#check twoArmTrajectoryParameterZero
#check twoArmForwardPotential
#check twoArmInversePotential
#check twoArmSuccessProbability
#check twoArmFailureMass

#check measurable_twoArmTrajectoryParameterZero
#check measurable_twoArmForwardPotential
#check measurable_twoArmInversePotential
#check measurable_twoArmSuccessProbability
#check measurable_twoArmFailureMass
#check integrable_twoArmForwardPotential
#check integrable_twoArmInversePotential
#check integrable_twoArmSuccessProbability_sq
#check integrable_twoArmFailureMass_sq

#check twoArmForwardSuccessor_eq_nextPotential
#check twoArmInverseSuccessor_eq_nextPotential
#check integrable_twoArmForwardRecurrenceBound
#check integrable_twoArmInverseRecurrenceBound
#check twoArmForwardUnconditionalRecurrence
#check twoArmInverseUnconditionalRecurrence

#check twoArmScalarForwardIterate
#check twoArmScalarInverseTelescope
#check twoArmForwardFiniteIteration
#check twoArmInverseFailureMassSqTelescope
#check twoArmInverseFailureMassSqSum_le_initial_div

#check twoArmInitialForwardPotential
#check twoArmInitialInversePotential
#check measurable_twoArmInitialForwardPotential
#check measurable_twoArmInitialInversePotential
#check twoArmForwardPotential_zero_eq_initial
#check twoArmInversePotential_zero_eq_initial
#check integral_twoArmForwardPotential_zero_kernel_eq_initial
#check integral_twoArmInversePotential_zero_kernel_eq_initial
#check twoArmForwardInitialUnconditionalRecurrence
#check twoArmInverseInitialUnconditionalRecurrence
#check twoArmForwardFiniteIteration_from_source_initial
#check twoArmFullFailureMassSqSum_le

/-! Typed source-time and theorem-contract fences. -/

/-- Lean prefix `n` has consumed trace coordinates `0, ..., n`, so it is the
source parameter `theta_{1,n+2}`, represented by adapter time `n + 1`. -/
example {Env : Type*} [MeasurableSpace Env]
    (eta : Real) (n : Nat)
    (sample : Env × ((k : Nat) -> Fin 2 × Real)) :
    twoArmTrajectoryParameterZero eta n sample =
      twoArmParameterAt eta sample.2 (n + 1) 0 := by
  rfl

example {Env : Type*} [MeasurableSpace Env]
    (eta : Real) (n : Nat)
    (sample : Env × ((k : Nat) -> Fin 2 × Real)) :
    twoArmFailureMass eta n sample =
      1 - twoArmSuccessProbability eta n sample := by
  rfl

example {Env : Type*} [MeasurableSpace Env] [StandardBorelSpace Env]
    (prior : Measure Env) [IsFiniteMeasure prior]
    (eta Delta : Real) (heta : 0 <= eta)
    (environment : Thompson.MeasurableHistoryEnvironment Env (Fin 2) Real)
    (mean : Fin 2 -> Real)
    (contract : TwoArmBoundedFixedMeanEnvironmentContract environment mean)
    (hgap : mean 0 - mean 1 = Delta) (n : Nat) :
    integral (twoArmTrajectoryMeasure prior eta environment)
        (twoArmForwardPotential (Env := Env) eta (n + 1)) <=
      integral (twoArmTrajectoryMeasure prior eta environment)
        (twoArmForwardPotential (Env := Env) eta n) +
      2 * integral (twoArmTrajectoryMeasure prior eta environment)
          (fun sample => twoArmSuccessProbability
            (Env := Env) eta n sample ^ 2) *
        (eta * Delta + eta ^ 2 * sourceC eta) :=
  twoArmForwardUnconditionalRecurrence
    prior eta Delta heta environment mean contract hgap n

example {Env : Type*} [MeasurableSpace Env] [StandardBorelSpace Env]
    (prior : Measure Env) [IsProbabilityMeasure prior]
    (eta Delta : Real) (heta : 0 < eta)
    (environment : Thompson.MeasurableHistoryEnvironment Env (Fin 2) Real)
    (mean : Fin 2 -> Real)
    (contract : TwoArmBoundedFixedMeanEnvironmentContract environment mean)
    (hgap : mean 0 - mean 1 = Delta)
    (hmargin : eta * sourceC eta < Delta) (tailHorizon : Nat) :
    (1 : Real) / 4 +
        (Finset.range tailHorizon).sum (fun n =>
          integral (twoArmTrajectoryMeasure prior eta environment)
            (fun sample => twoArmFailureMass
              (Env := Env) eta n sample ^ 2)) <=
      1 / (2 * eta * (Delta - eta * sourceC eta)) :=
  twoArmFullFailureMassSqSum_le
    prior eta Delta heta environment mean contract hgap hmargin tailHorizon

#print axioms twoArmForwardUnconditionalRecurrence
#print axioms twoArmInverseUnconditionalRecurrence
#print axioms twoArmForwardFiniteIteration
#print axioms twoArmInverseFailureMassSqTelescope
#print axioms twoArmInverseFailureMassSqSum_le_initial_div
#print axioms twoArmForwardInitialUnconditionalRecurrence
#print axioms twoArmInverseInitialUnconditionalRecurrence
#print axioms twoArmForwardFiniteIteration_from_source_initial
#print axioms twoArmFullFailureMassSqSum_le

end StochasticGradientBandit
end BanditRLProof
