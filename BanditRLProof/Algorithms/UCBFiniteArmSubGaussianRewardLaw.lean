import BanditRLProof.Algorithms.UCBConditionalRewardLawCenteredKernelReal
import BanditRLProof.FiniteArmRewardKernelLaw

/-!
# Canonical UCB expected regret for sub-Gaussian finite-arm reward laws

This module instantiates the centered-kernel canonical Real theorem directly
from stationary action-indexed sub-Gaussian reward laws, without bounded-support
assumptions.
-/

open scoped BigOperators ENNReal NNReal

open MeasureTheory ProbabilityTheory

namespace BanditRLProof
namespace UCB

/--
Canonical Real expected pseudo-regret bound for stationary finite-arm reward
laws with direct centered sub-Gaussian MGF witnesses.

The UCB variance parameter is the maximum of the armwise proxies. At least one
proxy must be positive because the existing canonical UCB route requires a
strictly positive common proxy; zero proxies for other arms are allowed.
-/
theorem integral_real_pseudoRegret_selectedPolicySuccessorGeneratedUCBRegretAction_le_textbookGapSum_finiteArmSubgaussianLaws
    {K : Nat}
    (model : FiniteBanditModel K)
    (armLaw : Fin K -> Measure Rat)
    (hprob : forall arm, IsProbabilityMeasure (armLaw arm))
    (varianceProxy : Fin K -> NNReal)
    (hvariancePositive : exists arm,
      0 < ((varianceProxy arm : NNReal) : Real))
    (hmean : forall arm,
      integral (armLaw arm) (fun reward : Rat => ((reward : Rat) : Real)) =
        ((model.mean arm : Rat) : Real))
    (hsubG : forall arm,
      HasSubgaussianMGF
        (fun reward : Rat =>
          (((reward - model.mean arm : Rat) : Real)))
        (varianceProxy arm) (armLaw arm))
    (defaultAction : Fin K)
    (T : Nat) (hT : 0 < T)
    (delta : Real) (hdelta : 0 < delta) :
    let sigma2 := Concentration.finiteArmVarianceProxy varianceProxy
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
  let sigma2 := Concentration.finiteArmVarianceProxy varianceProxy
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
        (fun _ arm => varianceProxy arm) := by
    simpa [rewardKernel] using
      (RewardKernel.contextIndependentCenteredRewardKernelLaw_of_hasSubgaussianMGF
        (Context := Unit)
        armLaw hprob model.mean varianceProxy hmean hsubG)
  have hsigma2 : 0 < ((sigma2 : NNReal) : Real) := by
    simpa [sigma2] using
      (Concentration.finiteArmVarianceProxy_pos_of_exists
        varianceProxy hvariancePositive)
  letI : IsProbabilityMeasure (armLaw defaultAction) := hprob defaultAction
  simpa [sigma2, rewardKernel, context] using
    (integral_real_pseudoRegret_selectedPolicySuccessorGeneratedUCBRegretAction_le_textbookGapSum_trajMeasure_centeredKernel
      (model := model)
      (mu0 := armLaw defaultAction)
      (rewardKernel := rewardKernel)
      (context := context)
      (mean := fun _ arm => model.mean arm)
      (varianceProxy := fun _ arm => varianceProxy arm)
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
        Concentration.varianceProxy_le_finiteArmVarianceProxy
          varianceProxy _)
      (harmMean := fun _ _ _ => rfl))

/--
Canonical Real expected pseudo-regret bound for stationary finite-arm reward
laws with direct centered sub-Gaussian MGF witnesses, including an all-zero
proxy family. The common UCB tuning proxy is the finite maximum padded by one,
so callers provide neither a positivity witness nor a separate ceiling.
-/
theorem integral_real_pseudoRegret_selectedPolicySuccessorGeneratedUCBRegretAction_le_textbookGapSum_finiteArmSubgaussianLaws_without_proxy_positivity
    {K : Nat}
    (model : FiniteBanditModel K)
    (armLaw : Fin K -> Measure Rat)
    (hprob : forall arm, IsProbabilityMeasure (armLaw arm))
    (varianceProxy : Fin K -> NNReal)
    (hmean : forall arm,
      integral (armLaw arm) (fun reward : Rat => ((reward : Rat) : Real)) =
        ((model.mean arm : Rat) : Real))
    (hsubG : forall arm,
      HasSubgaussianMGF
        (fun reward : Rat =>
          (((reward - model.mean arm : Rat) : Real)))
        (varianceProxy arm) (armLaw arm))
    (defaultAction : Fin K)
    (T : Nat) (hT : 0 < T)
    (delta : Real) (hdelta : 0 < delta) :
    let sigma2 := Concentration.finiteArmPositiveVarianceProxy varianceProxy
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
  let sigma2 := Concentration.finiteArmPositiveVarianceProxy varianceProxy
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
        (fun _ arm => varianceProxy arm) := by
    simpa [rewardKernel] using
      (RewardKernel.contextIndependentCenteredRewardKernelLaw_of_hasSubgaussianMGF
        (Context := Unit)
        armLaw hprob model.mean varianceProxy hmean hsubG)
  have hsigma2 : 0 < ((sigma2 : NNReal) : Real) := by
    simpa [sigma2] using
      (Concentration.finiteArmPositiveVarianceProxy_pos varianceProxy)
  letI : IsProbabilityMeasure (armLaw defaultAction) := hprob defaultAction
  simpa [sigma2, rewardKernel, context] using
    (integral_real_pseudoRegret_selectedPolicySuccessorGeneratedUCBRegretAction_le_textbookGapSum_trajMeasure_centeredKernel
      (model := model)
      (mu0 := armLaw defaultAction)
      (rewardKernel := rewardKernel)
      (context := context)
      (mean := fun _ arm => model.mean arm)
      (varianceProxy := fun _ arm => varianceProxy arm)
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
        Concentration.varianceProxy_le_finiteArmPositiveVarianceProxy
          varianceProxy _)
      (harmMean := fun _ _ _ => rfl))

end UCB
end BanditRLProof
