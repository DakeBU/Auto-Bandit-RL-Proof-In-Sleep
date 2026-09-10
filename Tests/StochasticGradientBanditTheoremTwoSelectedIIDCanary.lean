import BanditRLProof.Algorithms.StochasticGradientBanditTheoremTwoSelectedIID

namespace BanditRLProof
namespace StochasticGradientBandit

open MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory

#check twoArmOptimalPullTimeRewardBlock
#check measurable_twoArmOptimalPullTimeRewardBlock
#check twoArmLatentMaskedOptimalPullBlock
#check measurable_twoArmLatentMaskedOptimalPullBlock
#check twoArmOptimalPullTimeRewardBlock_eq_latentMasked_ae
#check twoArmNativeOptimalPullTimeRewardBlock_map_eq_latentMasked
#check twoArmFixedIIDTrajectoryMeasure_map_snd_eq_nativeStationary
#check twoArmFixedIIDLatentTrajectoryMeasure_map_visible_eq_generated
#check twoArmFixedIIDTrajectoryMeasure_map_optimalPullTimeRewardBlock_eq_latentMasked
#check twoArmAppendixCPhaseOnePrefixSum
#check measurable_twoArmAppendixCPhaseOnePrefixSum
#check twoArmAppendixCRewardPhaseEvent
#check measurableSet_twoArmAppendixCRewardPhaseEvent
#check twoArmAppendixCAllPullsPresent
#check measurableSet_twoArmAppendixCAllPullsPresent
#check twoArmAppendixCObservedPhaseEvent
#check measurableSet_twoArmAppendixCObservedPhaseEvent
#check twoArmAppendixCLatentPhaseEvent
#check measurableSet_twoArmAppendixCLatentPhaseEvent
#check twoArmLatentMaskedOptimalPullBlock_preimage_appendixCObservedPhaseEvent
#check twoArmAppendixCGeneratedPhaseEvent
#check measurableSet_twoArmAppendixCGeneratedPhaseEvent
#check twoArmFixedIIDTrajectoryMeasure_appendixCGeneratedPhaseEvent_eq_latent
#check twoArmAppendixCPureLatentRewardEvent
#check measurableSet_twoArmAppendixCPureLatentRewardEvent
#check twoArmAppendixCMissingPullLatentPhaseEvent
#check measurableSet_twoArmAppendixCMissingPullLatentPhaseEvent
#check mem_twoArmAppendixCMissingPullLatentPhaseEvent_iff
#check twoArmAppendixCMissingPullLatentPhaseEvent_subset_terminalCountBelow
#check twoArmFixedIIDMissingPullLatentPhase_probability_le_countBelow
#check twoArmFixedIIDMissingPullLatentPhase_charge_mul_probability_le_integral
#check twoArmAppendixCPureLatentRewardEvent_eq_union_phase_missing
#check disjoint_twoArmAppendixCLatentPhaseEvent_missing
#check twoArmFixedIIDLatentTrajectoryMeasure_purePhaseEvent_eq_pi
#check twoArmFixedIIDLatentTrajectoryMeasure_purePhaseEvent_eq_phase_add_missing
#check twoArmAppendixCRewardPhaseProbability_eq_generated_add_missing
#check softmaxProbability_zero_le_one_div_two_mul_nat_of_exp_two_mul_le
#check twoArmSuccessProbability_le_one_div_two_mul_nat_of_exp_parameter_le
#check twoArmNthOptimalPullSuccessProbability_le_one_div_two_mul_nat_of_time_eq
#check twoArmSuccessProbability_le_exp_two_mul_parameter
#check twoArmSuccessProbability_le_one_div_two_mul_horizon_of_parameter
#check twoArmAppendixCGeneratedPhaseEvent_exists_lastPullTime

/-- The source-facing theorem retains the missing-pull time coordinate and
does not replace its masked right-hand side by the unmasked product law. -/
example
    (armLaw : Fin 2 -> Measure Real)
    (hprob : forall arm, IsProbabilityMeasure (armLaw arm))
    (eta : Real) :
    Measure.map (twoArmOptimalPullTimeRewardBlock (Env := Unit) 3)
        (twoArmTrajectoryMeasure (Measure.dirac ()) eta
          (twoArmFixedIIDEnvironment armLaw hprob)) =
      Measure.map (twoArmLatentMaskedOptimalPullBlock 3)
        (twoArmFixedIIDLatentTrajectoryMeasure armLaw hprob eta) := by
  exact
    twoArmFixedIIDTrajectoryMeasure_map_optimalPullTimeRewardBlock_eq_latentMasked
      armLaw hprob eta 3

/-- A concrete block-size/horizon canary pins the finite-horizon missing-mass
consumer without asserting that the missing branch has positive mass. -/
example
    (armLaw : Fin 2 -> Measure Real)
    (hprob : forall arm, IsProbabilityMeasure (armLaw arm))
    (eta Delta phaseOneTotal : Real) (hDelta : 0 ≤ Delta) :
    Delta * ((7 - (1 + 2) : Nat) : Real) *
        (twoArmFixedIIDLatentTrajectoryMeasure armLaw hprob eta).real
          (twoArmAppendixCMissingPullLatentPhaseEvent
            1 2 phaseOneTotal) ≤
      integral
        (twoArmTrajectoryMeasure (Measure.dirac ()) eta
          (twoArmFixedIIDEnvironment armLaw hprob))
        (twoArmSampledPseudoRegret (Env := Unit) Delta 7) := by
  exact
    twoArmFixedIIDMissingPullLatentPhase_charge_mul_probability_le_integral
      armLaw hprob eta Delta hDelta 1 2 phaseOneTotal 7

/-- The exact odds threshold retains the smallest allowed horizon. -/
example (theta : Fin 2 -> Real) (hsum : ∑ coordinate, theta coordinate = 0)
    (hodds : Real.exp (2 * theta 0) <= 1 / (2 * (1 : Real) - 1)) :
    softmaxProbability theta 0 <= 1 / (2 * (1 : Real)) := by
  simpa using softmaxProbability_zero_le_one_div_two_mul_nat_of_exp_two_mul_le
    theta 1 (by omega) hsum (by simpa using hodds)

/-- A missing pull is not silently replaced by a finite time: the witness
is an explicit premise even in this concrete specialization. -/
example (eta : Real) (sample : Unit × ((t : Nat) -> Fin 2 × Real))
    (htime : twoArmNthOptimalPullTime 2 sample = (5 : WithTop Nat))
    (hodds : Real.exp (2 * twoArmTrajectoryParameterZero eta 5 sample) <=
      1 / (2 * (7 : Real) - 1)) :
    twoArmNthOptimalPullSuccessProbability eta 2 sample <=
      1 / (2 * (7 : Real)) := by
  exact twoArmNthOptimalPullSuccessProbability_le_one_div_two_mul_nat_of_time_eq
    eta 2 5 7 (by omega) sample htime hodds

/-- A positive all-present phase exposes the third requested optimal pull. -/
example (phaseOneTotal : Real)
    (sample : Unit × ((t : Nat) -> Fin 2 × Real))
    (hphase : sample ∈ twoArmAppendixCGeneratedPhaseEvent 1 2 phaseOneTotal) :
    ∃ cutoff : Nat,
      twoArmNthOptimalPullTime 2 sample = (cutoff : WithTop Nat) ∧
        twoArmOptimalPullCount cutoff sample = 2 ∧
        twoArmGeneratedAction sample cutoff = 0 ∧
        twoArmOptimalPullCount (cutoff + 1) sample = 3 := by
  simpa using twoArmAppendixCGeneratedPhaseEvent_exists_lastPullTime
    1 2 phaseOneTotal (by omega) sample hphase

/-- The logarithmic parameter producer remains a supplied hypothesis. -/
example (eta : Real) (sample : Unit × ((t : Nat) -> Fin 2 × Real))
    (hparameter : 2 * twoArmTrajectoryParameterZero eta 5 sample <=
      -Real.log (2 * (7 : Real))) :
    twoArmSuccessProbability eta 5 sample <= 1 / (2 * (7 : Real)) := by
  exact twoArmSuccessProbability_le_one_div_two_mul_horizon_of_parameter
    eta 5 7 sample (by omega) hparameter

#print axioms softmaxProbability_zero_le_one_div_two_mul_nat_of_exp_two_mul_le
#print axioms twoArmSuccessProbability_le_one_div_two_mul_nat_of_exp_parameter_le
#print axioms twoArmNthOptimalPullSuccessProbability_le_one_div_two_mul_nat_of_time_eq
#print axioms twoArmSuccessProbability_le_exp_two_mul_parameter
#print axioms twoArmSuccessProbability_le_one_div_two_mul_horizon_of_parameter
#print axioms twoArmAppendixCGeneratedPhaseEvent_exists_lastPullTime
#print axioms twoArmOptimalPullTimeRewardBlock_eq_latentMasked_ae
#print axioms twoArmNativeOptimalPullTimeRewardBlock_map_eq_latentMasked
#print axioms twoArmFixedIIDTrajectoryMeasure_map_snd_eq_nativeStationary
#print axioms twoArmFixedIIDLatentTrajectoryMeasure_map_visible_eq_generated
#print axioms twoArmFixedIIDTrajectoryMeasure_map_optimalPullTimeRewardBlock_eq_latentMasked
#print axioms twoArmFixedIIDTrajectoryMeasure_appendixCGeneratedPhaseEvent_eq_latent
#print axioms twoArmAppendixCMissingPullLatentPhaseEvent_subset_terminalCountBelow
#print axioms twoArmFixedIIDMissingPullLatentPhase_probability_le_countBelow
#print axioms twoArmFixedIIDMissingPullLatentPhase_charge_mul_probability_le_integral
#print axioms twoArmAppendixCRewardPhaseProbability_eq_generated_add_missing

end StochasticGradientBandit
end BanditRLProof
