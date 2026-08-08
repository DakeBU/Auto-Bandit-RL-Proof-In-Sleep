import BanditRLProof.Algorithms.UCBConditionalRewardPairTrajectoryReal

open scoped BigOperators ENNReal NNReal

open MeasureTheory ProbabilityTheory

namespace BanditRLProof
namespace UCB

/-- Shift sampled pair-trajectory actions at coordinates `1, 2, ...` to times `0, 1, ...`. -/
def actionRewardTrajectorySuccessorAction
    {Action Reward : Type} (trajectory : Nat -> Prod Action Reward) :
    ActionTrace Action :=
  fun t => (trajectory (t + 1)).1

/-
The shifted UCB action reconstructed from reward coordinates agrees almost
everywhere with the sampled successor action trace on its canonical pair
trajectory measure.
-/
theorem selectedPolicySuccessorGeneratedUCBRegretAction_ae_eq_actionRewardTrajectorySuccessorAction_trajMeasure
    {Context : Type u} {K : Nat} [MeasurableSpace Context]
    (hK : 0 < K)
    (mu0 : Measure (Prod (Fin K) Rat)) [IsProbabilityMeasure mu0]
    (rewardKernel : RewardKernel.MarkovRewardKernel (Prod Context (Fin K)) Rat)
    (context : (n : Nat) -> ((j : Finset.Iic n) -> Rat) -> Context)
    (defaultAction : Fin K) (sigma2 : NNReal) (T : Nat) (delta : Real)
    (hcontext : forall n : Nat, Measurable (context n)) :
    let policy := selectedPolicySuccessorHistoryPolicy
      hK sigma2 T delta defaultAction
    let state := selectedPolicySuccessorHistoryState
      hK sigma2 T delta defaultAction
    let pairContext :
        (i : Nat) -> ((j : Finset.Iic i) -> Prod (Fin K) Rat) -> Context :=
      fun i history =>
        context i (History.pairHistoryRewardProjection history)
    let pairState :
        (i : Nat) -> ((j : Finset.Iic i) -> Prod (Fin K) Rat) ->
          SelectedPolicySuccessorFiniteHistoryState K :=
      fun i history =>
        state i (History.pairHistoryRewardProjection history)
    let hpairContext : forall i : Nat, Measurable (pairContext i) := fun i =>
      (hcontext i).comp
        (History.measurable_pairHistoryRewardProjection
          (Action := Fin K) (Reward := Rat) i)
    let hpairState : forall i : Nat, Measurable (pairState i) := fun i =>
      (measurable_selectedPolicySuccessorHistoryState
        hK sigma2 T delta defaultAction i).comp
        (History.measurable_pairHistoryRewardProjection
          (Action := Fin K) (Reward := Rat) i)
    let stepKernel :=
      RewardKernel.actionRewardHistoryStepKernelFamily rewardKernel policy
        pairContext pairState hpairContext hpairState
    let mu :=
      ProbabilityTheory.Kernel.trajMeasure
        (X := fun _ : Nat => Prod (Fin K) Rat) mu0 stepKernel
    let reward : (Nat -> Prod (Fin K) Rat) -> RewardTrace Rat :=
      fun trajectory t => (trajectory t).2
    Filter.EventuallyEq (ae mu)
      (selectedPolicySuccessorGeneratedUCBRegretAction
        hK sigma2 T delta defaultAction reward)
      (fun trajectory => actionRewardTrajectorySuccessorAction trajectory) := by
  let policy := selectedPolicySuccessorHistoryPolicy
    hK sigma2 T delta defaultAction
  let state := selectedPolicySuccessorHistoryState
    hK sigma2 T delta defaultAction
  let pairContext :
      (i : Nat) -> ((j : Finset.Iic i) -> Prod (Fin K) Rat) -> Context :=
    fun i history =>
      context i (History.pairHistoryRewardProjection history)
  let pairState :
      (i : Nat) -> ((j : Finset.Iic i) -> Prod (Fin K) Rat) ->
        SelectedPolicySuccessorFiniteHistoryState K :=
    fun i history =>
      state i (History.pairHistoryRewardProjection history)
  let hpairContext : forall i : Nat, Measurable (pairContext i) := fun i =>
    (hcontext i).comp
      (History.measurable_pairHistoryRewardProjection
        (Action := Fin K) (Reward := Rat) i)
  let hpairState : forall i : Nat, Measurable (pairState i) := fun i =>
    (measurable_selectedPolicySuccessorHistoryState
      hK sigma2 T delta defaultAction i).comp
      (History.measurable_pairHistoryRewardProjection
        (Action := Fin K) (Reward := Rat) i)
  let stepKernel :=
    RewardKernel.actionRewardHistoryStepKernelFamily rewardKernel policy
      pairContext pairState hpairContext hpairState
  let mu :=
    ProbabilityTheory.Kernel.trajMeasure
      (X := fun _ : Nat => Prod (Fin K) Rat) mu0 stepKernel
  let sampledAction : (Nat -> Prod (Fin K) Rat) -> ActionTrace (Fin K) :=
    fun trajectory t => (trajectory t).1
  let reward : (Nat -> Prod (Fin K) Rat) -> RewardTrace Rat :=
    fun trajectory t => (trajectory t).2
  let generatedAction := selectedPolicySuccessorGeneratedUCBAction
    hK sigma2 T delta defaultAction reward
  let regretAction := selectedPolicySuccessorGeneratedUCBRegretAction
    hK sigma2 T delta defaultAction reward
  let successorAction : (Nat -> Prod (Fin K) Rat) -> ActionTrace (Fin K) :=
    fun trajectory => actionRewardTrajectorySuccessorAction trajectory
  change Filter.EventuallyEq (ae mu) regretAction successorAction
  have hcoord : forall i : Nat,
      Filter.EventuallyEq (ae mu)
        (fun trajectory => regretAction trajectory i)
        (fun trajectory => successorAction trajectory i) := by
    intro i
    have hcanonical :=
      ConditionalExpectationReward.actionRewardHistoryStepKernelFamily_action_succ_ae_eq_policy_trajMeasure
        mu0 rewardKernel policy pairContext pairState hpairContext hpairState i
    have hsampled_generated :
        Filter.EventuallyEq (ae mu)
          (fun trajectory => sampledAction trajectory (i + 1))
          (fun trajectory => generatedAction trajectory (i + 1)) := by
      simpa [mu, stepKernel, sampledAction, generatedAction,
        selectedPolicySuccessorGeneratedUCBAction,
        ConditionalExpectationReward.generatedActionFromRewardHistory,
        Policy.generatedActionTraceSucc, policy, state, pairState, reward,
        History.pairHistoryRewardProjection,
        History.finiteRewardHistoryOfTrace,
        Preorder.frestrictLe_apply] using hcanonical
    simpa [regretAction, successorAction,
      selectedPolicySuccessorGeneratedUCBRegretAction,
      actionRewardTrajectorySuccessorAction, generatedAction, sampledAction] using
        hsampled_generated.symm
  have hall : ∀ᵐ trajectory ∂mu, forall i : Nat,
      regretAction trajectory i = successorAction trajectory i :=
    ae_all_iff.2 hcoord
  filter_upwards [hall] with trajectory htrajectory
  funext i
  exact htrajectory i

/-
Canonical pair-trajectory Real textbook pseudo-regret bound stated directly
on the sampled successor action coordinates.
-/
theorem integral_real_pseudoRegret_actionRewardTrajectorySuccessorAction_le_textbookGapSum_actionRewardTrajMeasure_centeredKernel
    {Context : Type u} {K : Nat} [MeasurableSpace Context]
    (model : FiniteBanditModel K)
    (mu0 : Measure (Prod (Fin K) Rat)) [IsProbabilityMeasure mu0]
    (rewardKernel : RewardKernel.MarkovRewardKernel (Prod Context (Fin K)) Rat)
    (context : (n : Nat) -> ((j : Finset.Iic n) -> Rat) -> Context)
    (mean : Context -> Fin K -> Rat)
    (varianceProxy : Context -> Fin K -> NNReal)
    (defaultAction : Fin K) (sigma2 : NNReal) (T : Nat) (delta : Real)
    (hcontext : forall n : Nat, Measurable (context n))
    (hmean : Measurable (fun pair : Prod Context (Fin K) =>
      mean pair.1 pair.2))
    (law : RewardKernel.CenteredRewardKernelLaw rewardKernel mean varianceProxy)
    (hvariance : forall i : Nat, i < T - 1 ->
      forall history : ((j : Finset.Iic i) -> Rat),
        varianceProxy (context i history)
            ((selectedPolicySuccessorHistoryPolicy
              model.hK sigma2 T delta defaultAction i).action
              (selectedPolicySuccessorHistoryState
                model.hK sigma2 T delta defaultAction i history)) <=
          sigma2)
    (harmMean : forall i : Nat,
      forall history : ((j : Finset.Iic i) -> Rat),
        forall arm : Fin K,
          mean (context i history) arm = model.mean arm)
    (hT : 0 < T) (hsigma2 : 0 < (((sigma2 : NNReal) : Real)))
    (hdelta : 0 < delta) :
    let policy := selectedPolicySuccessorHistoryPolicy
      model.hK sigma2 T delta defaultAction
    let state := selectedPolicySuccessorHistoryState
      model.hK sigma2 T delta defaultAction
    let pairContext :
        (i : Nat) -> ((j : Finset.Iic i) -> Prod (Fin K) Rat) -> Context :=
      fun i history =>
        context i (History.pairHistoryRewardProjection history)
    let pairState :
        (i : Nat) -> ((j : Finset.Iic i) -> Prod (Fin K) Rat) ->
          SelectedPolicySuccessorFiniteHistoryState K :=
      fun i history =>
        state i (History.pairHistoryRewardProjection history)
    let hpairContext : forall i : Nat, Measurable (pairContext i) := fun i =>
      (hcontext i).comp
        (History.measurable_pairHistoryRewardProjection
          (Action := Fin K) (Reward := Rat) i)
    let hpairState : forall i : Nat, Measurable (pairState i) := fun i =>
      (measurable_selectedPolicySuccessorHistoryState
        model.hK sigma2 T delta defaultAction i).comp
        (History.measurable_pairHistoryRewardProjection
          (Action := Fin K) (Reward := Rat) i)
    let stepKernel :=
      RewardKernel.actionRewardHistoryStepKernelFamily rewardKernel policy
        pairContext pairState hpairContext hpairState
    let mu :=
      ProbabilityTheory.Kernel.trajMeasure
        (X := fun _ : Nat => Prod (Fin K) Rat) mu0 stepKernel
    MeasureTheory.integral mu (fun trajectory =>
        (((pseudoRegret model
          (actionRewardTrajectorySuccessorAction trajectory) T : Rat) : Real))) <=
      ((Finset.univ : Finset (Fin K)).filter (fun arm =>
        0 < (((model.gap arm : Rat) : Real)))).sum (fun arm =>
          selectedPolicySuccessorTextbookGapBudget K sigma2 T delta
              (((model.gap arm : Rat) : Real)) +
            (((model.gap arm : Rat) : Real)) * ((T : Real) * delta)) := by
  let policy := selectedPolicySuccessorHistoryPolicy
    model.hK sigma2 T delta defaultAction
  let state := selectedPolicySuccessorHistoryState
    model.hK sigma2 T delta defaultAction
  let pairContext :
      (i : Nat) -> ((j : Finset.Iic i) -> Prod (Fin K) Rat) -> Context :=
    fun i history =>
      context i (History.pairHistoryRewardProjection history)
  let pairState :
      (i : Nat) -> ((j : Finset.Iic i) -> Prod (Fin K) Rat) ->
        SelectedPolicySuccessorFiniteHistoryState K :=
    fun i history =>
      state i (History.pairHistoryRewardProjection history)
  let hpairContext : forall i : Nat, Measurable (pairContext i) := fun i =>
    (hcontext i).comp
      (History.measurable_pairHistoryRewardProjection
        (Action := Fin K) (Reward := Rat) i)
  let hpairState : forall i : Nat, Measurable (pairState i) := fun i =>
    (measurable_selectedPolicySuccessorHistoryState
      model.hK sigma2 T delta defaultAction i).comp
      (History.measurable_pairHistoryRewardProjection
        (Action := Fin K) (Reward := Rat) i)
  let stepKernel :=
    RewardKernel.actionRewardHistoryStepKernelFamily rewardKernel policy
      pairContext pairState hpairContext hpairState
  let mu :=
    ProbabilityTheory.Kernel.trajMeasure
      (X := fun _ : Nat => Prod (Fin K) Rat) mu0 stepKernel
  let reward : (Nat -> Prod (Fin K) Rat) -> RewardTrace Rat :=
    fun trajectory t => (trajectory t).2
  let generatedAction := selectedPolicySuccessorGeneratedUCBRegretAction
    model.hK sigma2 T delta defaultAction reward
  let sampledAction : (Nat -> Prod (Fin K) Rat) -> ActionTrace (Fin K) :=
    fun trajectory => actionRewardTrajectorySuccessorAction trajectory
  let generatedRegret : (Nat -> Prod (Fin K) Rat) -> Real := fun trajectory =>
    (((pseudoRegret model (generatedAction trajectory) T : Rat) : Real))
  let sampledRegret : (Nat -> Prod (Fin K) Rat) -> Real := fun trajectory =>
    (((pseudoRegret model (sampledAction trajectory) T : Rat) : Real))
  let rhs : Real :=
    ((Finset.univ : Finset (Fin K)).filter (fun arm =>
      0 < (((model.gap arm : Rat) : Real)))).sum (fun arm =>
        selectedPolicySuccessorTextbookGapBudget K sigma2 T delta
            (((model.gap arm : Rat) : Real)) +
          (((model.gap arm : Rat) : Real)) * ((T : Real) * delta))
  change MeasureTheory.integral mu sampledRegret <= rhs
  have haction : Filter.EventuallyEq (ae mu) generatedAction sampledAction := by
    simpa [policy, state, pairContext, pairState, hpairContext, hpairState,
      stepKernel, mu, reward, generatedAction, sampledAction] using
      (selectedPolicySuccessorGeneratedUCBRegretAction_ae_eq_actionRewardTrajectorySuccessorAction_trajMeasure
        (hK := model.hK)
        (mu0 := mu0)
        (rewardKernel := rewardKernel)
        (context := context)
        (defaultAction := defaultAction)
        (sigma2 := sigma2)
        (T := T)
        (delta := delta)
        (hcontext := hcontext))
  have hintegral :
      MeasureTheory.integral mu sampledRegret =
        MeasureTheory.integral mu generatedRegret := by
    apply integral_congr_ae
    filter_upwards [haction] with trajectory htrajectory
    exact congrArg
      (fun action : ActionTrace (Fin K) =>
        (((pseudoRegret model action T : Rat) : Real))) htrajectory.symm
  rw [hintegral]
  simpa [policy, state, pairContext, pairState, hpairContext, hpairState,
    stepKernel, mu, reward, generatedAction, generatedRegret, rhs] using
    (integral_real_pseudoRegret_selectedPolicySuccessorGeneratedUCBRegretAction_le_textbookGapSum_actionRewardTrajMeasure_centeredKernel
      (model := model)
      (mu0 := mu0)
      (rewardKernel := rewardKernel)
      (context := context)
      (mean := mean)
      (varianceProxy := varianceProxy)
      (defaultAction := defaultAction)
      (sigma2 := sigma2)
      (T := T)
      (delta := delta)
      (hcontext := hcontext)
      (hmean := hmean)
      (law := law)
      (hvariance := hvariance)
      (harmMean := harmMean)
      (hT := hT)
      (hsigma2 := hsigma2)
      (hdelta := hdelta))

end UCB
end BanditRLProof
