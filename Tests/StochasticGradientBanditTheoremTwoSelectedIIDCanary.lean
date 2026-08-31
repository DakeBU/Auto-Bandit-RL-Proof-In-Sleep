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

#print axioms twoArmOptimalPullTimeRewardBlock_eq_latentMasked_ae
#print axioms twoArmNativeOptimalPullTimeRewardBlock_map_eq_latentMasked
#print axioms twoArmFixedIIDTrajectoryMeasure_map_snd_eq_nativeStationary
#print axioms twoArmFixedIIDTrajectoryMeasure_map_optimalPullTimeRewardBlock_eq_latentMasked
#print axioms twoArmFixedIIDTrajectoryMeasure_appendixCGeneratedPhaseEvent_eq_latent

end StochasticGradientBandit
end BanditRLProof
