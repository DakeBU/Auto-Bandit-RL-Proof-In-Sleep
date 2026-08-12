import BanditRLProof

namespace BanditRLProof
namespace ConditionalExpectationReward

open MeasureTheory ProbabilityTheory

universe v w x

#check successorArmEmpiricalMeanFintypeGeometricAllTimeBadEvent
#check actionRewardHistoryStepKernelFamily_successorArmEmpiricalMean_simultaneous_fintype_geometricAllTime_abs_tail_ennreal_delta_trajMeasure

section TypedApplication

variable {Context : Type v} {State : Type w} {Action : Type x}
variable [MeasurableSpace Context] [MeasurableSpace State]
variable [MeasurableSpace Action] [StandardBorelSpace Action]
variable [MeasurableSingletonClass Action] [Fintype Action] [Nonempty Action]
variable [DecidableEq Action]
variable (mu0 : Measure (Prod Action Rat)) [IsProbabilityMeasure mu0]
variable (rewardKernel : RewardKernel.MarkovRewardKernel (Prod Context Action) Rat)
variable (policy : Nat -> Policy.MeasurablePolicy State Action)
variable (context : (n : Nat) -> ((j : Finset.Iic n) -> Rat) -> Context)
variable (state : (n : Nat) -> ((j : Finset.Iic n) -> Rat) -> State)
variable (hcontext : forall n : Nat, Measurable (context n))
variable (hstate : forall n : Nat, Measurable (state n))
variable (mean : Context -> Action -> Rat)
variable (varianceProxy : Context -> Action -> NNReal)
variable (law : RewardKernel.CenteredRewardKernelLaw rewardKernel mean varianceProxy)
variable (hmean : Measurable (fun pair : Prod Context Action => mean pair.1 pair.2))
variable (armMean : Action -> Rat) (sigma2 : NNReal)
variable (hvariance : forall i : Nat,
  forall history : ((j : Finset.Iic i) -> Rat),
    varianceProxy (context i history)
      ((policy i).action (state i history)) <= sigma2)
variable (harmMean : forall i : Nat,
  forall history : ((j : Finset.Iic i) -> Rat),
    forall arm : Action, mean (context i history) arm = armMean arm)
variable (hsigma2 : 0 < (((sigma2 : NNReal) : Real)))
variable (delta : Real) (hdelta : 0 < delta)

example :
    let pairContext :
        (i : Nat) -> ((j : Finset.Iic i) -> Prod Action Rat) -> Context :=
      fun i history =>
        context i (History.pairHistoryRewardProjection history)
    let pairState :
        (i : Nat) -> ((j : Finset.Iic i) -> Prod Action Rat) -> State :=
      fun i history =>
        state i (History.pairHistoryRewardProjection history)
    let hpairContext : forall i : Nat, Measurable (pairContext i) := fun i =>
      (hcontext i).comp
        (History.measurable_pairHistoryRewardProjection
          (Action := Action) (Reward := Rat) i)
    let hpairState : forall i : Nat, Measurable (pairState i) := fun i =>
      (hstate i).comp
        (History.measurable_pairHistoryRewardProjection
          (Action := Action) (Reward := Rat) i)
    let stepKernel :=
      RewardKernel.actionRewardHistoryStepKernelFamily rewardKernel policy
        pairContext pairState hpairContext hpairState
    let mu :=
      ProbabilityTheory.Kernel.trajMeasure
        (X := fun _ : Nat => Prod Action Rat) mu0 stepKernel
    let action : (Nat -> Prod Action Rat) -> ActionTrace Action :=
      fun trajectory t => (trajectory t).1
    let reward : (Nat -> Prod Action Rat) -> RewardTrace Rat :=
      fun trajectory t => (trajectory t).2
    mu (successorArmEmpiricalMeanFintypeGeometricAllTimeBadEvent
      action reward armMean sigma2 delta) <= ENNReal.ofReal delta := by
  exact
    actionRewardHistoryStepKernelFamily_successorArmEmpiricalMean_simultaneous_fintype_geometricAllTime_abs_tail_ennreal_delta_trajMeasure
      (mu0 := mu0)
      (rewardKernel := rewardKernel)
      (policy := policy)
      (context := context)
      (state := state)
      (hcontext := hcontext)
      (hstate := hstate)
      (mean := mean)
      (varianceProxy := varianceProxy)
      (law := law)
      (hmean := hmean)
      (armMean := armMean)
      (sigma2 := sigma2)
      (hvariance := hvariance)
      (harmMean := harmMean)
      hsigma2 delta hdelta

end TypedApplication

#print axioms successorArmEmpiricalMeanFintypeGeometricAllTimeBadEvent
#print axioms actionRewardHistoryStepKernelFamily_successorArmEmpiricalMean_simultaneous_fintype_geometricAllTime_abs_tail_ennreal_delta_trajMeasure

end ConditionalExpectationReward
end BanditRLProof
