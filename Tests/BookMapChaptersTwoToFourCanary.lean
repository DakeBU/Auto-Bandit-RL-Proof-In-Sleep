import BanditRLProof.ConditionalRewardPartialTrajectoryGeometricAllTime
import BanditRLProof.ConditionalRewardPartialTrajectoryTelescopingAllTime
import BanditRLProof.Algorithms.ETCFiniteArmRewardLaw
import BanditRLProof.Algorithms.UCBFiniteArmSubGaussianSampledAsymptotics

/-!
# Book Map Chapters 2--4 public route canary

This external module checks the exact local declarations used by the scoped
completion contracts for the Probability, ETC, and ordinary-UCB chapters.
It deliberately does not turn the pinned LML cards, KL-UCB, self-normalized
concentration, or RL-specific confidence routes into local proof evidence.
-/

namespace BanditRLProof.BookMapChaptersTwoToFourCanary

open MeasureTheory ProbabilityTheory Filter

section ProbabilityRouteSurface

#check RewardKernel.historyStepKernelFamily
#check ConditionalExpectationReward.historyStepKernelFamily_generatedActionPartialTrajectoryPairLawSource_trajMeasure
#check ConditionalExpectationReward.historyStepKernelFamily_centeredReward_succ_hasCondSubgaussianMGF_trajMeasure
#check ConditionalExpectationReward.actionRewardHistoryStepKernelFamily_successorArmEmpiricalMean_simultaneous_finiteArmTime_abs_tail_ennreal_delta_trajMeasure
#check Concentration.measure_iUnion_iUnion_fintype_le_delta_of_geometricConfidenceShare
#check Concentration.measure_iUnion_iUnion_fintype_le_delta_of_telescopingConfidenceShare
#check ConditionalExpectationReward.actionRewardHistoryStepKernelFamily_successorArmEmpiricalMean_simultaneous_fintype_telescopingAllTime_abs_tail_ennreal_delta_trajMeasure
#check ConditionalExpectationReward.actionRewardHistoryStepKernelFamily_successorArmEmpiricalMean_simultaneous_fintype_geometricAllTime_abs_tail_ennreal_delta_trajMeasure

end ProbabilityRouteSurface

section ETCCanonicalRoute

#check ETC.explorationArgmaxHistoryPolicy
#check ETC.explorationArgmaxGeneratedActionPartialTrajectoryPairLawSource_trajMeasure
#check ETC.explorationArgmaxGeneratedAction_eq_explorationArgmaxAction
#check ETC.explorationArgmaxGeneratedAction_eq_actionWithCommit_of_lt
#check ETC.argmaxCommitOracle_argmax_finRange
#check ETC.argmaxCommitOracle_encode_le_of_score_le
#check ETC.explorationArgmaxHistory_prob_wrongCommit_le_pairwiseTailSum_of_boundedArmLaws
#check ETC.real_measure_explorationArgmaxCommit_eq_arm_le_canonicalSubGaussianArmPairwiseTailReal
#check ETC.integral_real_pseudoRegret_explorationArgmaxGeneratedAction_le_canonicalBoundedArmPerArmIntegralRegretBoundReal
#check ETC.integral_real_pseudoRegret_explorationArgmaxGeneratedAction_le_canonicalSubGaussianArmPerArmIntegralRegretBoundReal

example {K : Nat} (hK : 0 < K) (scores : Fin K -> Rat) (a : Fin K)
    (hscore :
      scores ((ETC.argmaxCommitOracle hK).choose scores) <= scores a) :
    Encodable.encode ((ETC.argmaxCommitOracle hK).choose scores) <=
      Encodable.encode a := by
  exact ETC.argmaxCommitOracle_encode_le_of_score_le hK scores a hscore

end ETCCanonicalRoute

section UCBCanonicalRoute

#check ConditionalExpectationReward.successorArmEmpiricalMeanFiniteArmTimeBadEvent
#check ConditionalExpectationReward.actionRewardHistoryStepKernelFamily_successorArmEmpiricalMean_simultaneous_finiteArmTime_abs_tail_ennreal_delta_trajMeasure
#check UCB.selectedPolicySuccessorGeneratedUCBInitializedScoreMaxSource
#check UCB.measure_selectedPolicySuccessorLargeGapEvent_generatedUCB_le_ennreal_delta_actionRewardTrajMeasure_centeredKernel
#check UCB.measure_successorArmPullCount_selectedPolicySuccessorGeneratedUCBAction_gt_explicitPullThreshold_le_ennreal_delta_actionRewardTrajMeasure_centeredKernel
#check UCB.lintegral_successorArmPullCount_selectedPolicySuccessorGeneratedUCBAction_le_explicitPullThreshold_add_horizon_mul_delta_actionRewardTrajMeasure_centeredKernel
#check UCB.integral_real_pseudoRegret_selectedPolicySuccessorGeneratedUCBRegretAction_le_textbookGapSum_actionRewardTrajMeasure_centeredKernel
#check UCB.selectedPolicySuccessorFiniteArmSubgaussianExpectedPseudoRegret_nonneg_and_le
#check UCB.selectedPolicySuccessorFiniteArmSubgaussianExpectedAveragePseudoRegret_tendsto_zero

example {K : Nat}
    (model : FiniteBanditModel K)
    (armLaw : Fin K -> Measure Rat)
    (hprob : forall arm, IsProbabilityMeasure (armLaw arm))
    (varianceProxy : Fin K -> NNReal)
    (hmean : forall arm,
      integral (armLaw arm) (fun reward : Rat => (reward : Real)) =
        (model.mean arm : Real))
    (hsubG : forall arm,
      HasSubgaussianMGF
        (fun reward : Rat => ((reward - model.mean arm : Rat) : Real))
        (varianceProxy arm) (armLaw arm))
    (defaultAction : Fin K) :
    Tendsto
      (UCB.selectedPolicySuccessorFiniteArmSubgaussianExpectedAveragePseudoRegret
        model armLaw hprob varianceProxy defaultAction)
      atTop (nhds 0) := by
  exact
    UCB.selectedPolicySuccessorFiniteArmSubgaussianExpectedAveragePseudoRegret_tendsto_zero
      model armLaw hprob varianceProxy hmean hsubG defaultAction

end UCBCanonicalRoute

#print axioms ETC.argmaxCommitOracle_encode_le_of_score_le
#print axioms ETC.explorationArgmaxHistory_prob_wrongCommit_le_pairwiseTailSum_of_boundedArmLaws
#print axioms ETC.integral_real_pseudoRegret_explorationArgmaxGeneratedAction_le_canonicalSubGaussianArmPerArmIntegralRegretBoundReal
#print axioms ConditionalExpectationReward.actionRewardHistoryStepKernelFamily_successorArmEmpiricalMean_simultaneous_finiteArmTime_abs_tail_ennreal_delta_trajMeasure
#print axioms UCB.selectedPolicySuccessorFiniteArmSubgaussianExpectedAveragePseudoRegret_tendsto_zero

end BanditRLProof.BookMapChaptersTwoToFourCanary
