import BanditRLProof.Algorithms.UCBFixedPolicyTelescopingAnytimeRegret

namespace BanditRLProof
namespace UCB

open MeasureTheory

#check selectedPolicySuccessorTelescopingRadiusAt
#check selectedPolicySuccessorTelescopingRadiusAt_nonneg
#check measurable_selectedPolicySuccessorTelescopingHistoryIndex
#check selectedPolicySuccessorTelescopingHistoryPolicy
#check selectedPolicySuccessorTelescopingGeneratedUCBAction
#check selectedPolicySuccessorTelescopingPairHistory_eq_finitePairHistoryOfTrace
#check selectedPolicySuccessorTelescopingHistoryIndex_finitePairHistoryOfTrace
#check selectedPolicySuccessorTelescoping_allHorizonPullCount_of_not_badEvent
#check measure_selectedPolicySuccessorTelescoping_allTimeBadEvent_le_trajMeasure
#check measure_selectedPolicySuccessorTelescoping_pullCount_gt_threshold_le_trajMeasure
#check lintegral_ofReal_pseudoRegret_selectedPolicySuccessorTelescoping_le_trajMeasure

noncomputable section TypedTerminal

variable {Context : Type} {K : Nat} [MeasurableSpace Context]
variable (model : FiniteBanditModel K)
variable (mu0 : Measure (Prod (Fin K) Rat)) [IsProbabilityMeasure mu0]
variable (rewardKernel : RewardKernel.MarkovRewardKernel (Prod Context (Fin K)) Rat)
variable (context : (n : Nat) -> ((j : Finset.Iic n) -> Rat) -> Context)
variable (mean : Context -> Fin K -> Rat)
variable (varianceProxy : Context -> Fin K -> NNReal)
variable (defaultAction : Fin K) (sigma2 : NNReal) (delta : Real)
variable (hcontext : forall n : Nat, Measurable (context n))
variable (hmean : Measurable (fun pair : Prod Context (Fin K) =>
  mean pair.1 pair.2))
variable (law : RewardKernel.CenteredRewardKernelLaw rewardKernel mean varianceProxy)
variable (hvariance : forall i : Nat,
  forall history : ((j : Finset.Iic i) -> Rat),
    varianceProxy (context i history)
        ((selectedPolicySuccessorTelescopingHistoryPolicy
          model.hK sigma2 delta defaultAction i).action
          (selectedPolicySuccessorTelescopingHistoryState
            model.hK sigma2 delta defaultAction i history)) <= sigma2)
variable (harmMean : forall i : Nat,
  forall history : ((j : Finset.Iic i) -> Rat),
    forall arm : Fin K, mean (context i history) arm = model.mean arm)
variable (hsigma2 : 0 < (((sigma2 : NNReal) : Real)))
variable (hdelta : 0 < delta)

/-- The policy type visibly has no terminal horizon parameter. -/
example (t : Nat) :
    Policy.MeasurablePolicy
      (SelectedPolicySuccessorFiniteHistoryState K) (Fin K) :=
  selectedPolicySuccessorTelescopingHistoryPolicy
    model.hK sigma2 delta defaultAction t

/-- Conclusion-typed terminal application: one fixed policy/measure and an
arbitrary consumer horizon `T`. -/
example (T : Nat) :
    let mu := selectedPolicySuccessorTelescopingActionRewardTrajMeasure
      model.hK mu0 rewardKernel context hcontext sigma2 delta defaultAction
    let reward : (Nat -> Prod (Fin K) Rat) -> RewardTrace Rat :=
      fun trajectory t => (trajectory t).2
    let action := selectedPolicySuccessorTelescopingGeneratedUCBRegretAction
      model.hK sigma2 delta defaultAction reward
    ∫⁻ trajectory,
        ENNReal.ofReal
          (((pseudoRegret model (action trajectory) T : Rat) : Real)) ∂mu <=
      (Finset.univ : Finset (Fin K)).sum (fun arm =>
        ENNReal.ofReal (((model.gap arm : Rat) : Real)) *
          ((selectedPolicySuccessorTelescopingPullThreshold
              K sigma2 T delta (((model.gap arm : Rat) : Real)) : Nat) :
                ENNReal) +
            ENNReal.ofReal (((model.gap arm : Rat) : Real)) *
              ((T : ENNReal) * ENNReal.ofReal delta)) := by
  exact
    lintegral_ofReal_pseudoRegret_selectedPolicySuccessorTelescoping_le_trajMeasure
      model mu0 rewardKernel context mean varianceProxy defaultAction
      sigma2 delta T hcontext hmean law hvariance harmMean hsigma2 hdelta

end TypedTerminal

#print axioms selectedPolicySuccessorTelescopingHistoryPolicy
#print axioms selectedPolicySuccessorTelescopingPairHistory_eq_finitePairHistoryOfTrace
#print axioms selectedPolicySuccessorTelescoping_allHorizonPullCount_of_not_badEvent
#print axioms measure_selectedPolicySuccessorTelescoping_allTimeBadEvent_le_trajMeasure
#print axioms lintegral_ofReal_pseudoRegret_selectedPolicySuccessorTelescoping_le_trajMeasure

end UCB
end BanditRLProof
