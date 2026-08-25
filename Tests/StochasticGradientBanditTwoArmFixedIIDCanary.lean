import BanditRLProof.Algorithms.StochasticGradientBanditTwoArmFixedIID

open MeasureTheory ProbabilityTheory

#check BanditRLProof.StochasticGradientBandit.twoArmFixedIIDRewardKernel
#check BanditRLProof.StochasticGradientBandit.twoArmFixedIIDRewardKernel_apply
#check BanditRLProof.StochasticGradientBandit.twoArmFixedIIDRewardKernel_isMarkov
#check BanditRLProof.StochasticGradientBandit.twoArmFixedIIDEnvironment
#check BanditRLProof.StochasticGradientBandit.twoArmFixedIIDEnvironment_initialFeedback_apply
#check BanditRLProof.StochasticGradientBandit.twoArmFixedIIDEnvironment_feedback_apply
#check BanditRLProof.StochasticGradientBandit.twoArmFixedIIDReward_aestronglyMeasurable
#check BanditRLProof.StochasticGradientBandit.twoArmFixedIIDEnvironment_contract

example
    (armLaw : Fin 2 -> Measure Real)
    (hprob : forall arm, IsProbabilityMeasure (armLaw arm))
    (mean : Fin 2 -> Real)
    (hbound : forall arm, ∀ᵐ reward ∂armLaw arm, |reward| <= 1)
    (hmean : forall arm, integral (armLaw arm) id = mean arm) :
    BanditRLProof.StochasticGradientBandit.TwoArmBoundedFixedMeanEnvironmentContract
      (BanditRLProof.StochasticGradientBandit.twoArmFixedIIDEnvironment
        armLaw hprob) mean :=
  BanditRLProof.StochasticGradientBandit.twoArmFixedIIDEnvironment_contract
    armLaw hprob mean hbound hmean

#print axioms BanditRLProof.StochasticGradientBandit.twoArmFixedIIDEnvironment_contract
