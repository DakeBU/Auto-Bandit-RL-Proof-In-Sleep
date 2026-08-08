import BanditRLProof.Algorithms.UCBConditionalRewardLawCenteredKernelReal
import BanditRLProof.BoundedRewardKernelLaw

/-!
# Canonical UCB expected regret for bounded context-dependent reward kernels

The reward distribution may vary with context and action. Arm means remain
stationary and all selected one-step laws share one nondegenerate interval.
-/

open scoped BigOperators ENNReal NNReal

open MeasureTheory ProbabilityTheory

namespace BanditRLProof
namespace UCB

/--
Canonical Real expected pseudo-regret bound for a context-dependent Markov
reward kernel with stationary arm means and common bounded support.

The centered kernel law, constant Hoeffding proxy, selected reward law,
trajectory law, and finite-horizon integrability are constructed internally.
-/
theorem integral_real_pseudoRegret_selectedPolicySuccessorGeneratedUCBRegretAction_le_textbookGapSum_trajMeasure_contextDependentBoundedRewardKernel
    {Context : Type} [MeasurableSpace Context]
    {K : Nat}
    (model : FiniteBanditModel K)
    (mu0 : Measure Rat) [IsProbabilityMeasure mu0]
    (rewardKernel : RewardKernel.MarkovRewardKernel
      (Context × Fin K) Rat)
    (context : (n : Nat) -> History.FiniteRewardHistory Rat n -> Context)
    (hcontext : forall n, Measurable (context n))
    (lo hi : Real) (hlohi : lo < hi)
    (hmeas : forall ctx arm,
      AEMeasurable (fun reward : Rat => ((reward : Rat) : Real))
        (RewardKernel.selectedMeasure rewardKernel ctx arm))
    (hbound : forall ctx arm,
      Filter.Eventually
        (fun reward : Rat => Set.Icc lo hi ((reward : Rat) : Real))
        (ae (RewardKernel.selectedMeasure rewardKernel ctx arm)))
    (hmean : forall ctx arm,
      integral (RewardKernel.selectedMeasure rewardKernel ctx arm)
          (fun reward : Rat => ((reward : Rat) : Real)) =
        ((model.mean arm : Rat) : Real))
    (defaultAction : Fin K)
    (T : Nat) (hT : 0 < T)
    (delta : Real) (hdelta : 0 < delta) :
    let sigma2 := Concentration.intervalVarianceProxy lo hi
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
  let sigma2 := Concentration.intervalVarianceProxy lo hi
  have hmeanMeas :
      Measurable (fun pair : Context × Fin K => model.mean pair.2) :=
    (measurable_of_countable model.mean).comp measurable_snd
  have hkernel :
      RewardKernel.CenteredRewardKernelLaw rewardKernel
        (fun _ arm => model.mean arm) (fun _ _ => sigma2) := by
    simpa [sigma2] using
      (RewardKernel.boundedCenteredRewardKernelLaw
        rewardKernel (fun _ arm => model.mean arm)
        lo hi hmeas hbound hmean)
  have hsigma2 : 0 < ((sigma2 : NNReal) : Real) := by
    simpa [sigma2] using
      (Concentration.intervalVarianceProxy_pos_of_lt hlohi)
  simpa [sigma2] using
    (integral_real_pseudoRegret_selectedPolicySuccessorGeneratedUCBRegretAction_le_textbookGapSum_trajMeasure_centeredKernel
      (model := model)
      (mu0 := mu0)
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

end UCB
end BanditRLProof
