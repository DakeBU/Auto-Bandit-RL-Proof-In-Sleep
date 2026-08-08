import BanditRLProof.Algorithms.UCBConditionalRewardLawCenteredKernelReal
import BanditRLProof.FiniteArmRewardKernelLaw

/-!
# Canonical UCB expected regret for bounded finite-arm reward laws

This module instantiates the centered-kernel canonical Real theorem with
stationary action-indexed reward laws. It supports both one common interval
and arm-dependent nondegenerate intervals.
-/

open scoped BigOperators ENNReal NNReal

open MeasureTheory ProbabilityTheory

namespace BanditRLProof
namespace UCB

/--
Canonical Real expected pseudo-regret bound for finite-arm stationary reward
laws supported almost surely on one nondegenerate interval.

The initial reward is sampled from the default arm law. Successor rewards use
the context-independent action law kernel, while the context is `Unit`.
-/
theorem integral_real_pseudoRegret_selectedPolicySuccessorGeneratedUCBRegretAction_le_textbookGapSum_boundedFiniteArmLaws
    {K : Nat}
    (model : FiniteBanditModel K)
    (armLaw : Fin K -> Measure Rat)
    (hprob : forall arm, IsProbabilityMeasure (armLaw arm))
    (lo hi : Real) (hlohi : lo < hi)
    (hmeas : forall arm,
      AEMeasurable (fun reward : Rat => ((reward : Rat) : Real))
        (armLaw arm))
    (hbound : forall arm,
      Filter.Eventually
        (fun reward : Rat => Set.Icc lo hi ((reward : Rat) : Real))
        (ae (armLaw arm)))
    (hmean : forall arm,
      integral (armLaw arm) (fun reward : Rat => ((reward : Rat) : Real)) =
        ((model.mean arm : Rat) : Real))
    (defaultAction : Fin K)
    (T : Nat) (hT : 0 < T)
    (delta : Real) (hdelta : 0 < delta) :
    let sigma2 := Concentration.intervalVarianceProxy lo hi
    let rewardKernel := RewardKernel.contextIndependentOfActionLaws
      (Context := Unit) armLaw hprob
    let context : (n : Nat) -> History.FiniteRewardHistory Rat n -> Unit :=
      fun _ _ => ()
    MeasureTheory.integral
        (selectedPolicySuccessorRewardTrajMeasure model.hK
          (armLaw defaultAction) rewardKernel context
          (fun _ => measurable_const) sigma2 T delta defaultAction)
        (fun trajectory : RewardTrace Rat =>
          ((pseudoRegret model
            (selectedPolicySuccessorGeneratedUCBRegretAction
              model.hK sigma2 T delta defaultAction
              (fun y : RewardTrace Rat => y) trajectory)
            T : Rat) : Real)) <=
      ((Finset.univ : Finset (Fin K)).filter (fun arm =>
        0 < (((model.gap arm : Rat) : Real)))).sum (fun arm =>
          selectedPolicySuccessorTextbookGapBudget K sigma2 T delta
              (((model.gap arm : Rat) : Real)) +
            (((model.gap arm : Rat) : Real)) * ((T : Real) * delta)) := by
  let sigma2 := Concentration.intervalVarianceProxy lo hi
  let rewardKernel := RewardKernel.contextIndependentOfActionLaws
    (Context := Unit) armLaw hprob
  let context : (n : Nat) -> History.FiniteRewardHistory Rat n -> Unit :=
    fun _ _ => ()
  have hcontext : forall n : Nat, Measurable (context n) := by
    intro n
    exact measurable_const
  have hmeanMeas :
      Measurable (fun pair : Unit × Fin K => model.mean pair.2) :=
    (measurable_of_countable model.mean).comp measurable_snd
  have hkernel :
      RewardKernel.CenteredRewardKernelLaw rewardKernel
        (fun _ arm => model.mean arm) (fun _ _ => sigma2) := by
    simpa [rewardKernel, sigma2] using
      (RewardKernel.contextIndependentBoundedCenteredRewardKernelLaw
        (Context := Unit)
        armLaw hprob model.mean lo hi hmeas hbound hmean)
  have hsigma2 : 0 < ((sigma2 : NNReal) : Real) := by
    simpa [sigma2] using
      (Concentration.intervalVarianceProxy_pos_of_lt hlohi)
  letI : IsProbabilityMeasure (armLaw defaultAction) := hprob defaultAction
  simpa [sigma2, rewardKernel, context] using
    (integral_real_pseudoRegret_selectedPolicySuccessorGeneratedUCBRegretAction_le_textbookGapSum_trajMeasure_centeredKernel
      (model := model)
      (mu0 := armLaw defaultAction)
      (rewardKernel := rewardKernel)
      (context := context)
      (mean := fun _ arm => model.mean arm)
      (varianceProxy := fun _ _ => sigma2)
      (defaultAction := defaultAction)
      (sigma2 := sigma2)
      (hcontext := hcontext)
      (hmean := hmeanMeas)
      (hkernel := hkernel)
      (T := T)
      (hT := hT)
      (hsigma2 := hsigma2)
      (delta := delta)
      (hdelta := hdelta)
      (hvariance := fun _ _ => le_rfl)
      (harmMean := fun _ _ _ => rfl))

/--
Canonical Real expected pseudo-regret bound for finite-arm stationary reward
laws with arm-dependent nondegenerate support intervals.

The UCB variance parameter is the maximum of the armwise Hoeffding proxies,
computed internally with `Finset.sup` over all arms.
-/
theorem integral_real_pseudoRegret_selectedPolicySuccessorGeneratedUCBRegretAction_le_textbookGapSum_armwiseBoundedFiniteArmLaws
    {K : Nat}
    (model : FiniteBanditModel K)
    (armLaw : Fin K -> Measure Rat)
    (hprob : forall arm, IsProbabilityMeasure (armLaw arm))
    (lo hi : Fin K -> Real)
    (hlohi : forall arm, lo arm < hi arm)
    (hmeas : forall arm,
      AEMeasurable (fun reward : Rat => ((reward : Rat) : Real))
        (armLaw arm))
    (hbound : forall arm,
      Filter.Eventually
        (fun reward : Rat => Set.Icc (lo arm) (hi arm)
          ((reward : Rat) : Real))
        (ae (armLaw arm)))
    (hmean : forall arm,
      integral (armLaw arm) (fun reward : Rat => ((reward : Rat) : Real)) =
        ((model.mean arm : Rat) : Real))
    (defaultAction : Fin K)
    (T : Nat) (hT : 0 < T)
    (delta : Real) (hdelta : 0 < delta) :
    let sigma2 := Concentration.finiteArmIntervalVarianceProxy lo hi
    let rewardKernel := RewardKernel.contextIndependentOfActionLaws
      (Context := Unit) armLaw hprob
    let context : (n : Nat) -> History.FiniteRewardHistory Rat n -> Unit :=
      fun _ _ => ()
    MeasureTheory.integral
        (selectedPolicySuccessorRewardTrajMeasure model.hK
          (armLaw defaultAction) rewardKernel context
          (fun _ => measurable_const) sigma2 T delta defaultAction)
        (fun trajectory : RewardTrace Rat =>
          ((pseudoRegret model
            (selectedPolicySuccessorGeneratedUCBRegretAction
              model.hK sigma2 T delta defaultAction
              (fun y : RewardTrace Rat => y) trajectory)
            T : Rat) : Real)) <=
      ((Finset.univ : Finset (Fin K)).filter (fun arm =>
        0 < (((model.gap arm : Rat) : Real)))).sum (fun arm =>
          selectedPolicySuccessorTextbookGapBudget K sigma2 T delta
              (((model.gap arm : Rat) : Real)) +
            (((model.gap arm : Rat) : Real)) * ((T : Real) * delta)) := by
  let sigma2 := Concentration.finiteArmIntervalVarianceProxy lo hi
  let rewardKernel := RewardKernel.contextIndependentOfActionLaws
    (Context := Unit) armLaw hprob
  let context : (n : Nat) -> History.FiniteRewardHistory Rat n -> Unit :=
    fun _ _ => ()
  have hcontext : forall n : Nat, Measurable (context n) := by
    intro n
    exact measurable_const
  have hmeanMeas :
      Measurable (fun pair : Unit × Fin K => model.mean pair.2) :=
    (measurable_of_countable model.mean).comp measurable_snd
  have hkernel :
      RewardKernel.CenteredRewardKernelLaw rewardKernel
        (fun _ arm => model.mean arm)
        (fun _ arm => Concentration.intervalVarianceProxy
          (lo arm) (hi arm)) := by
    simpa [rewardKernel] using
      (RewardKernel.contextIndependentArmwiseBoundedCenteredRewardKernelLaw
        (Context := Unit)
        armLaw hprob model.mean lo hi hmeas hbound hmean)
  have hsigma2 : 0 < ((sigma2 : NNReal) : Real) := by
    simpa [sigma2] using
      (Concentration.finiteArmIntervalVarianceProxy_pos
        model.hK lo hi hlohi)
  letI : IsProbabilityMeasure (armLaw defaultAction) := hprob defaultAction
  simpa [sigma2, rewardKernel, context] using
    (integral_real_pseudoRegret_selectedPolicySuccessorGeneratedUCBRegretAction_le_textbookGapSum_trajMeasure_centeredKernel
      (model := model)
      (mu0 := armLaw defaultAction)
      (rewardKernel := rewardKernel)
      (context := context)
      (mean := fun _ arm => model.mean arm)
      (varianceProxy := fun _ arm =>
        Concentration.intervalVarianceProxy (lo arm) (hi arm))
      (defaultAction := defaultAction)
      (sigma2 := sigma2)
      (hcontext := hcontext)
      (hmean := hmeanMeas)
      (hkernel := hkernel)
      (T := T)
      (hT := hT)
      (hsigma2 := hsigma2)
      (delta := delta)
      (hdelta := hdelta)
      (hvariance := fun _ _ =>
        Concentration.intervalVarianceProxy_le_finiteArmIntervalVarianceProxy
          lo hi _)
      (harmMean := fun _ _ _ => rfl))

end UCB
end BanditRLProof
