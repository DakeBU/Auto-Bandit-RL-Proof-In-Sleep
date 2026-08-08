import BanditRLProof.ConditionalRewardLawSource

/-!
# Canonical conditional reward foundation

This module closes the canonical `COND-EXPECT-REWARD` route for reward-only
`trajMeasure` processes.  A centered reward-kernel law and deterministic
historywise proxy ceilings yield, on the generated history filtration:

* conditional expectation zero for every successor centered reward;
* a conditional sub-Gaussian MGF witness at the selected proxy ceiling;
* the finite-sum Azuma-Hoeffding upper tail.
-/

universe v w x

namespace BanditRLProof
namespace ConditionalExpectationReward

open MeasureTheory

/--
Canonical successor conditional mean-zero with no caller integrability
premise.  The canonical conditional MGF theorem supplies exponential
integrability, and `HasCondSubgaussianMGF.integrable` lowers it to the ordinary
integrability needed by `condExp`.
-/
theorem
    historyStepKernelFamily_centeredReward_succ_condExp_eq_zero_trajMeasure_of_condSubgaussian
    {Context : Type v} {State : Type w} {Action : Type x}
    [MeasurableSpace Context] [MeasurableSpace State]
    [MeasurableSpace Action] [MeasurableSingletonClass Action]
    [Countable Action]
    (mu0 : Measure Rat) [IsProbabilityMeasure mu0]
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
    (defaultAction : Action)
    (i : Nat) (c : NNReal)
    (hvariance :
      forall history : ((j : Finset.Iic i) -> Rat),
        varianceProxy (context i history)
          ((policy i).action (state i history)) <= c) :
    let stepKernel :=
      RewardKernel.historyStepKernelFamily rewardKernel policy context state
        hcontext hstate
    let trajMeasure :=
      ProbabilityTheory.Kernel.trajMeasure
        (X := fun _ : Nat => Rat) mu0 stepKernel
    let reward : RewardTrace Rat -> RewardTrace Rat := fun trajectory => trajectory
    let hreward : forall t : Nat,
        Measurable (fun trajectory : RewardTrace Rat => reward trajectory t) :=
      fun t => measurable_pi_apply t
    let action :=
      generatedActionFromRewardHistory policy state defaultAction reward
    let haction :=
      generatedActionFromRewardHistory_measurable
        (policy := policy) (state := state)
        (defaultAction := defaultAction) (reward := reward)
        hreward hstate
    let F := History.historyFiltrationSucc action reward haction hreward
    let Y : RewardTrace Rat -> Real := fun trajectory =>
      (((reward trajectory (i + 1) -
        mean
          (context i
            (History.finiteRewardHistoryOfTrace (reward trajectory) i))
          ((policy i).action
            (state i
              (History.finiteRewardHistoryOfTrace
                (reward trajectory) i))) : Rat) : Real))
    Filter.EventuallyEq (ae trajMeasure)
      (@condExp (RewardTrace Rat) Real (F i) inferInstance _ _ _
        trajMeasure Y)
      0 := by
  dsimp only
  let stepKernel :=
    RewardKernel.historyStepKernelFamily rewardKernel policy context state
      hcontext hstate
  let trajMeasure :=
    ProbabilityTheory.Kernel.trajMeasure
      (X := fun _ : Nat => Rat) mu0 stepKernel
  let reward : RewardTrace Rat -> RewardTrace Rat := fun trajectory => trajectory
  have hreward : forall t : Nat,
      Measurable (fun trajectory : RewardTrace Rat => reward trajectory t) :=
    fun t => measurable_pi_apply t
  let action :=
    generatedActionFromRewardHistory policy state defaultAction reward
  have haction : forall t : Nat,
      Measurable (fun trajectory : RewardTrace Rat => action trajectory t) :=
    generatedActionFromRewardHistory_measurable
      (policy := policy) (state := state)
      (defaultAction := defaultAction) (reward := reward)
      hreward hstate
  let F := History.historyFiltrationSucc action reward haction hreward
  let Y : RewardTrace Rat -> Real := fun trajectory =>
    (((reward trajectory (i + 1) -
      mean
        (context i
          (History.finiteRewardHistoryOfTrace (reward trajectory) i))
        ((policy i).action
          (state i
            (History.finiteRewardHistoryOfTrace
              (reward trajectory) i))) : Rat) : Real))
  have hmgf :
      ProbabilityTheory.HasCondSubgaussianMGF
        (F i) (F.le i) Y c trajMeasure := by
    have h :=
      historyStepKernelFamily_centeredReward_succ_hasCondSubgaussianMGF_trajMeasure
        mu0 rewardKernel policy context state hcontext hstate mean
        varianceProxy law hmean defaultAction i c hvariance
    simpa [stepKernel, trajMeasure, reward, action, F, Y] using h
  have h_integrable : Integrable Y trajMeasure :=
    ProbabilityTheory.HasCondSubgaussianMGF.integrable (F.le i) hmgf
  have hzero :=
    historyStepKernelFamily_centeredReward_succ_condExp_eq_zero_trajMeasure
      mu0 rewardKernel policy context state hcontext hstate mean
      varianceProxy law defaultAction i
      (by simpa [stepKernel, trajMeasure, reward, Y] using h_integrable)
  simpa [stepKernel, trajMeasure, reward, action, F, Y] using hzero

/--
The canonical conditional reward foundation as one theorem-facing endpoint.

For every successor time it exposes both conditional mean zero and the
conditional MGF witness.  The same assumptions also yield the finite-sum
Azuma-Hoeffding upper tail for the zero-initialized centered process.  Thus
`Finset.range n` contains the deterministic slot `Y 0 = 0` and successor
rewards `Y 1, ..., Y (n - 1)`.  When the cumulative proxy is zero, Lean's
totalized division makes the displayed exponential bound equal to `1`; this
endpoint does not claim a sharper degenerate-variance bound.
-/
theorem historyStepKernelFamily_conditionalRewardFoundation_trajMeasure
    {Context : Type v} {State : Type w} {Action : Type x}
    [MeasurableSpace Context] [MeasurableSpace State]
    [MeasurableSpace Action] [MeasurableSingletonClass Action]
    [Countable Action]
    (mu0 : Measure Rat) [IsProbabilityMeasure mu0]
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
    (defaultAction : Action)
    (varianceCeiling : Nat -> NNReal)
    (hvariance :
      forall i : Nat, forall history : ((j : Finset.Iic i) -> Rat),
        varianceProxy (context i history)
          ((policy i).action (state i history)) <= varianceCeiling i) :
    let stepKernel :=
      RewardKernel.historyStepKernelFamily rewardKernel policy context state
        hcontext hstate
    let trajMeasure :=
      ProbabilityTheory.Kernel.trajMeasure
        (X := fun _ : Nat => Rat) mu0 stepKernel
    let reward : RewardTrace Rat -> RewardTrace Rat := fun trajectory => trajectory
    let hreward : forall t : Nat,
        Measurable (fun trajectory : RewardTrace Rat => reward trajectory t) :=
      fun t => measurable_pi_apply t
    let action :=
      generatedActionFromRewardHistory policy state defaultAction reward
    let haction :=
      generatedActionFromRewardHistory_measurable
        (policy := policy) (state := state)
        (defaultAction := defaultAction) (reward := reward)
        hreward hstate
    let F := History.historyFiltrationSucc action reward haction hreward
    let Y : Nat -> RewardTrace Rat -> Real := fun t trajectory =>
      match t with
      | 0 => 0
      | i + 1 =>
          (((reward trajectory (i + 1) -
            mean
              (context i
                (History.finiteRewardHistoryOfTrace (reward trajectory) i))
              ((policy i).action
                (state i
                  (History.finiteRewardHistoryOfTrace
                    (reward trajectory) i))) : Rat) : Real))
    let cY : Nat -> NNReal := fun t =>
      match t with
      | 0 => 0
      | i + 1 => varianceCeiling i
    (forall i : Nat,
      Filter.EventuallyEq (ae trajMeasure)
        (@condExp (RewardTrace Rat) Real (F i) inferInstance _ _ _
          trajMeasure (Y (i + 1)))
        0) /\
    (forall i : Nat,
      ProbabilityTheory.HasCondSubgaussianMGF
        (F i) (F.le i) (Y (i + 1)) (cY (i + 1)) trajMeasure) /\
    (forall n : Nat, forall eps : Real, 0 <= eps ->
      trajMeasure
          {trajectory |
            eps <= (Finset.range n).sum (fun t => Y t trajectory)} <=
        ENNReal.ofReal
          (Real.exp
            (-eps ^ 2 /
              (2 * (((Finset.range n).sum cY : NNReal) : Real))))) := by
  dsimp only
  let stepKernel :=
    RewardKernel.historyStepKernelFamily rewardKernel policy context state
      hcontext hstate
  let trajMeasure :=
    ProbabilityTheory.Kernel.trajMeasure
      (X := fun _ : Nat => Rat) mu0 stepKernel
  let reward : RewardTrace Rat -> RewardTrace Rat := fun trajectory => trajectory
  have hreward : forall t : Nat,
      Measurable (fun trajectory : RewardTrace Rat => reward trajectory t) :=
    fun t => measurable_pi_apply t
  let action :=
    generatedActionFromRewardHistory policy state defaultAction reward
  have haction : forall t : Nat,
      Measurable (fun trajectory : RewardTrace Rat => action trajectory t) :=
    generatedActionFromRewardHistory_measurable
      (policy := policy) (state := state)
      (defaultAction := defaultAction) (reward := reward)
      hreward hstate
  let F := History.historyFiltrationSucc action reward haction hreward
  let Y : Nat -> RewardTrace Rat -> Real := fun t trajectory =>
    match t with
    | 0 => 0
    | i + 1 =>
        (((reward trajectory (i + 1) -
          mean
            (context i
              (History.finiteRewardHistoryOfTrace (reward trajectory) i))
            ((policy i).action
              (state i
                (History.finiteRewardHistoryOfTrace
                  (reward trajectory) i))) : Rat) : Real))
  let cY : Nat -> NNReal := fun t =>
    match t with
    | 0 => 0
    | i + 1 => varianceCeiling i
  refine ⟨?_, ?_, ?_⟩
  · intro i
    have hzero :=
      historyStepKernelFamily_centeredReward_succ_condExp_eq_zero_trajMeasure_of_condSubgaussian
        mu0 rewardKernel policy context state hcontext hstate mean
        varianceProxy law hmean defaultAction i (varianceCeiling i)
        (hvariance i)
    simpa [stepKernel, trajMeasure, reward, action, F, Y] using hzero
  · intro i
    have hmgf :=
      historyStepKernelFamily_centeredReward_succ_hasCondSubgaussianMGF_trajMeasure
        mu0 rewardKernel policy context state hcontext hstate mean
        varianceProxy law hmean defaultAction i (varianceCeiling i)
        (hvariance i)
    simpa [stepKernel, trajMeasure, reward, action, F, Y, cY] using hmgf
  · intro n eps heps
    have htail :=
      historyStepKernelFamily_centeredRewardSuccProcess_sum_tail_ennreal_trajMeasure
        mu0 rewardKernel policy context state hcontext hstate mean
        varianceProxy law hmean defaultAction varianceCeiling hvariance n heps
    simpa [stepKernel, trajMeasure, reward, action, F, Y, cY] using htail

end ConditionalExpectationReward
end BanditRLProof
