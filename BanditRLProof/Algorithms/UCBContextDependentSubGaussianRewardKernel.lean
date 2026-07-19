import BanditRLProof.Algorithms.UCBConditionalRewardLawCenteredKernelReal
import BanditRLProof.BoundedRewardKernelLaw

/-!
# Canonical UCB expected regret for context-dependent sub-Gaussian reward kernels

The reward distribution and its pointwise sub-Gaussian proxy may vary with
context and action. Arm means remain stationary, and a positive uniform proxy
ceiling is supplied for the UCB confidence width.
-/

open scoped BigOperators ENNReal NNReal

open MeasureTheory ProbabilityTheory

namespace BanditRLProof
namespace UCB

/--
Canonical Real expected pseudo-regret bound for a context-dependent Markov
reward kernel with stationary arm means and direct centered sub-Gaussian MGF
witnesses.

The centered kernel law, selected reward law, trajectory law, and finite-horizon
integrability are constructed internally. The caller supplies a positive common
ceiling because an arbitrary measurable context space has no finite maximum
operation for the pointwise variance proxies.
-/
theorem integral_real_pseudoRegret_selectedPolicySuccessorGeneratedUCBRegretAction_le_textbookGapSum_trajMeasure_contextDependentSubgaussianRewardKernel
    {Context : Type} [MeasurableSpace Context]
    {K : Nat}
    (model : FiniteBanditModel K)
    (mu0 : Measure Rat) [IsProbabilityMeasure mu0]
    (rewardKernel : RewardKernel.MarkovRewardKernel
      (Context × Fin K) Rat)
    (context : (n : Nat) -> History.FiniteRewardHistory Rat n -> Context)
    (hcontext : forall n, Measurable (context n))
    (varianceProxy : Context -> Fin K -> NNReal)
    (sigma2 : NNReal)
    (hsigma2 : 0 < ((sigma2 : NNReal) : Real))
    (hvariance : forall ctx arm, varianceProxy ctx arm <= sigma2)
    (hmean : forall ctx arm,
      integral (RewardKernel.selectedMeasure rewardKernel ctx arm)
          (fun reward : Rat => ((reward : Rat) : Real)) =
        ((model.mean arm : Rat) : Real))
    (hsubG : forall ctx arm,
      HasSubgaussianMGF
        (fun reward : Rat =>
          (((reward - model.mean arm : Rat) : Real)))
        (varianceProxy ctx arm)
        (RewardKernel.selectedMeasure rewardKernel ctx arm))
    (defaultAction : Fin K)
    (T : Nat) (hT : 0 < T)
    (delta : Real) (hdelta : 0 < delta) :
    MeasureTheory.integral
        (selectedPolicySuccessorRewardTrajMeasure model.hK
          mu0 rewardKernel context hcontext sigma2 T delta defaultAction)
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
  have hmeanMeas :
      Measurable (fun pair : Context × Fin K => model.mean pair.2) :=
    (measurable_of_countable model.mean).comp measurable_snd
  have hkernel :
      RewardKernel.CenteredRewardKernelLaw rewardKernel
        (fun _ arm => model.mean arm) varianceProxy := by
    exact RewardKernel.centeredRewardKernelLaw_of_hasSubgaussianMGF
      rewardKernel (fun _ arm => model.mean arm) varianceProxy hmean hsubG
  exact
    integral_real_pseudoRegret_selectedPolicySuccessorGeneratedUCBRegretAction_le_textbookGapSum_trajMeasure_centeredKernel
      (model := model)
      (mu0 := mu0)
      (rewardKernel := rewardKernel)
      (context := context)
      (mean := fun _ arm => model.mean arm)
      (varianceProxy := varianceProxy)
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
      (hvariance := fun i history => hvariance _ _)
      (harmMean := fun _ _ _ => rfl)

end UCB
end BanditRLProof
