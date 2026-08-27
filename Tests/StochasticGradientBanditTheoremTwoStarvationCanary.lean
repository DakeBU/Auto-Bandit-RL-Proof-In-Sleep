import BanditRLProof.Algorithms.StochasticGradientBanditTheoremTwoStarvation

namespace BanditRLProof
namespace StochasticGradientBandit

open MeasureTheory ProbabilityTheory

#check twoArmGeneratedAction
#check twoArmOptimalPullCount
#check twoArmStepOneTriggerEvent
#check twoArmStepOneStarvationEvent
#check measurableSet_twoArmStepOneStarvationEvent
#check twoArmSampledPseudoRegret_eq_gap_mul_suboptimalPullCount
#check mem_twoArmStepOneStarvationEvent_of_lowProbability_noFurtherOptimalPull
#check twoArmStepOneStarvationEvent_sampledPseudoRegret_eq
#check twoArmStepOneStarvationEvent_charge_mul_probability_le_integral
#check twoArmFixedIIDStepOneStarvationEvent_charge_mul_probability_le_integral

/-- The Step-1 expectation consumer is stated on the actual fixed-IID
generated trajectory measure, not on an externally supplied action schedule. -/
example
    (armLaw : Fin 2 -> Measure Real)
    (hprob : forall arm, IsProbabilityMeasure (armLaw arm))
    (eta Delta : Real) (hDelta : 0 <= Delta)
    (cutoff n horizon : Nat) :
    Delta * ((horizon - n : Nat) : Real) *
        (twoArmTrajectoryMeasure (Measure.dirac ()) eta
          (twoArmFixedIIDEnvironment armLaw hprob)).real
          (twoArmStepOneStarvationEvent
            (Env := Unit) eta cutoff n horizon) <=
      integral
        (twoArmTrajectoryMeasure (Measure.dirac ()) eta
          (twoArmFixedIIDEnvironment armLaw hprob))
        (twoArmSampledPseudoRegret (Env := Unit) Delta horizon) := by
  exact
    twoArmFixedIIDStepOneStarvationEvent_charge_mul_probability_le_integral
      armLaw hprob eta Delta hDelta cutoff n horizon

/-- A chronological no-return path enters the exact measurable starvation
event without identifying chronological time with the optimal-arm pull count. -/
example
    (eta : Real) (cutoff n horizon : Nat)
    (sample : Unit × ((k : Nat) -> Fin 2 × Real))
    (hcutoff : cutoff + 1 <= horizon)
    (hlow : twoArmSuccessProbability eta cutoff sample <=
      twoArmStepOneThreshold horizon)
    (hcount : twoArmOptimalPullCount (cutoff + 1) sample = n)
    (hnoFurther : forall t, cutoff + 1 <= t -> t < horizon ->
      twoArmGeneratedAction sample t ≠ 0) :
    sample ∈
      twoArmStepOneStarvationEvent
        (Env := Unit) eta cutoff n horizon := by
  exact
    mem_twoArmStepOneStarvationEvent_of_lowProbability_noFurtherOptimalPull
      eta cutoff n horizon sample hcutoff hlow hcount hnoFurther

#print axioms twoArmSampledPseudoRegret_eq_gap_mul_suboptimalPullCount
#print axioms mem_twoArmStepOneStarvationEvent_of_lowProbability_noFurtherOptimalPull
#print axioms twoArmStepOneStarvationEvent_charge_mul_probability_le_integral
#print axioms twoArmFixedIIDStepOneStarvationEvent_charge_mul_probability_le_integral

end StochasticGradientBandit
end BanditRLProof
