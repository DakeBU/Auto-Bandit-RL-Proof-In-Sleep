import BanditRLProof.ConditionalRewardPartialTrajectoryMaskedLaw
import BanditRLProof.ConcentrationFintypeTelescopingAllTime

/-!
# Generated finite-arm empirical-mean telescoping all-time confidence

This module instantiates the canonical action/reward trajectory's fixed-arm,
fixed-successor-horizon random-pull-count empirical-mean tail at the
telescoping confidence share `delta / ((n+1)(n+2))` per time, divided equally
across arms.  The resulting countable event has outer measure at most `delta`
on one generated trajectory measure.

The polynomial reciprocal schedule is suitable infrastructure for a later
horizon-free UCB score.  This result is not itself a UCB policy, pull-count or
regret theorem, maximal inequality, optional-stopping theorem, or
self-normalized bound.
-/

universe u v w x

namespace BanditRLProof
namespace ConditionalExpectationReward

open MeasureTheory ProbabilityTheory

/-- The union, over every positive successor horizon and finite arm, of the
canonical positive-random-count empirical-mean failures at equal per-arm
telescoping confidence shares. -/
noncomputable def successorArmEmpiricalMeanFintypeTelescopingAllTimeBadEvent
    {Omega : Type u} {Action : Type x}
    [Fintype Action] [DecidableEq Action]
    (action : Omega -> ActionTrace Action)
    (reward : Omega -> RewardTrace Rat)
    (armMean : Action -> Rat) (sigma2 : NNReal) (delta : Real) : Set Omega :=
  ⋃ n : Nat, ⋃ arm : Action,
    {omega |
      0 < successorArmPullCount (action omega) arm (n + 1) ∧
        successorArmEmpiricalMeanPeelingRadius sigma2
            (successorArmPullCount (action omega) arm (n + 1)) (n + 1)
            (Concentration.telescopingConfidenceShare delta n /
              (Fintype.card Action : Real)) <=
          |successorArmEmpiricalMean (action omega) (reward omega) arm (n + 1) -
            (armMean arm : Real)|}

/-- On one canonical generated action/reward trajectory, every positive
successor horizon and every arm satisfies the random-count empirical-mean
radius outside one telescoping-schedule event of outer measure at most
`ENNReal.ofReal delta`. -/
theorem actionRewardHistoryStepKernelFamily_successorArmEmpiricalMean_simultaneous_fintype_telescopingAllTime_abs_tail_ennreal_delta_trajMeasure
    {Context : Type v} {State : Type w} {Action : Type x}
    [MeasurableSpace Context] [MeasurableSpace State]
    [MeasurableSpace Action] [StandardBorelSpace Action]
    [MeasurableSingletonClass Action] [Fintype Action] [Nonempty Action]
    [DecidableEq Action]
    (mu0 : Measure (Prod Action Rat)) [IsProbabilityMeasure mu0]
    (rewardKernel : RewardKernel.MarkovRewardKernel (Prod Context Action) Rat)
    (policy : Nat -> Policy.MeasurablePolicy State Action)
    (context : (n : Nat) -> ((j : Finset.Iic n) -> Rat) -> Context)
    (state : (n : Nat) -> ((j : Finset.Iic n) -> Rat) -> State)
    (hcontext : forall n : Nat, Measurable (context n))
    (hstate : forall n : Nat, Measurable (state n))
    (mean : Context -> Action -> Rat)
    (varianceProxy : Context -> Action -> NNReal)
    (law : RewardKernel.CenteredRewardKernelLaw rewardKernel mean varianceProxy)
    (hmean : Measurable (fun pair : Prod Context Action => mean pair.1 pair.2))
    (armMean : Action -> Rat) (sigma2 : NNReal)
    (hvariance : forall i : Nat,
      forall history : ((j : Finset.Iic i) -> Rat),
        varianceProxy (context i history)
          ((policy i).action (state i history)) <= sigma2)
    (harmMean : forall i : Nat,
      forall history : ((j : Finset.Iic i) -> Rat),
        forall arm : Action, mean (context i history) arm = armMean arm)
    (hsigma2 : 0 < (((sigma2 : NNReal) : Real)))
    (delta : Real) (hdelta : 0 < delta) :
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
    mu (successorArmEmpiricalMeanFintypeTelescopingAllTimeBadEvent
      action reward armMean sigma2 delta) <= ENNReal.ofReal delta := by
  classical
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
  let bad : Nat -> Action -> Set (Nat -> Prod Action Rat) := fun n arm =>
    {trajectory |
      0 < successorArmPullCount (action trajectory) arm (n + 1) ∧
        successorArmEmpiricalMeanPeelingRadius sigma2
            (successorArmPullCount (action trajectory) arm (n + 1)) (n + 1)
            (Concentration.telescopingConfidenceShare delta n /
              (Fintype.card Action : Real)) <=
          |successorArmEmpiricalMean (action trajectory) (reward trajectory)
              arm (n + 1) -
            (armMean arm : Real)|}
  have hcard : 0 < (Fintype.card Action : Real) := by
    exact_mod_cast Fintype.card_pos
  have htail : forall n arm,
      mu (bad n arm) <=
        ENNReal.ofReal
          (Concentration.telescopingConfidenceShare delta n /
            (Fintype.card Action : Real)) := by
    intro n arm
    have hshare :
        0 < Concentration.telescopingConfidenceShare delta n /
          (Fintype.card Action : Real) :=
      div_pos (Concentration.telescopingConfidenceShare_pos hdelta n) hcard
    simpa [pairContext, pairState, hpairContext, hpairState, stepKernel, mu,
      action, reward, bad] using
      (actionRewardHistoryStepKernelFamily_successorArmEmpiricalMean_abs_tail_random_pullCount_ennreal_delta_trajMeasure_on_horizon
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
        (arm := arm)
        (armMean := armMean arm)
        (sigma2 := sigma2)
        (n := n + 1)
        (hvariance := fun i _hi history => hvariance i history)
        (harmMean := fun i history => harmMean i history arm)
        (Nat.succ_pos n) hsigma2
        (Concentration.telescopingConfidenceShare delta n /
          (Fintype.card Action : Real)) hshare)
  simpa [pairContext, pairState, hpairContext, hpairState, stepKernel, mu,
    action, reward, bad,
    successorArmEmpiricalMeanFintypeTelescopingAllTimeBadEvent] using
    (Concentration.measure_iUnion_iUnion_fintype_le_delta_of_telescopingConfidenceShare
      mu bad delta hdelta.le htail)

end ConditionalExpectationReward
end BanditRLProof
