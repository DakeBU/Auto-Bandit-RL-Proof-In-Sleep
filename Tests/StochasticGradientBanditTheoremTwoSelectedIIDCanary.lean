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
