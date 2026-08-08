import BanditRLProof.ConditionalRewardPartialTrajectoryLaw

/-!
# Canonical pair-trajectory masked conditional reward tails

This module specializes the canonical action/reward trajectory law to one
history-policy-selected arm and the generic predictable-variance concentration
interface.  It identifies the policy mask with the sampled successor action
almost everywhere on the canonical trajectory and rewrites the masked constant
proxy as an actual successor pull count.  It also normalizes positive exact
count fibers into empirical means, performs fixed-horizon count peeling, and
closes the finite arm/time union on the canonical trajectory.  It does not
prove uniform-time confidence, UCB, or regret.
-/

universe v w x

namespace BanditRLProof
namespace ConditionalExpectationReward

open MeasureTheory ProbabilityTheory

/--
On the canonical action/reward trajectory, every sampled successor action is
almost surely the action selected by the policy from the frozen pair prefix.

This is an ambient trajectory statement, not merely an a.e. statement inside
the regular conditional kernel.
-/
theorem actionRewardHistoryStepKernelFamily_action_succ_ae_eq_policy_trajMeasure
    {Context : Type v} {State : Type w} {Action : Type x} {Reward : Type*}
    [MeasurableSpace Context] [MeasurableSpace State]
    [MeasurableSpace Action] [MeasurableSpace Reward]
    [MeasurableSingletonClass Action] [Countable Action]
    (mu0 : Measure (Prod Action Reward)) [IsProbabilityMeasure mu0]
    (rewardKernel : RewardKernel.MarkovRewardKernel (Prod Context Action) Reward)
    (policy : Nat -> Policy.MeasurablePolicy State Action)
    (context :
      (n : Nat) -> ((i : Finset.Iic n) -> Prod Action Reward) -> Context)
    (state :
      (n : Nat) -> ((i : Finset.Iic n) -> Prod Action Reward) -> State)
    (hcontext : forall n : Nat, Measurable (context n))
    (hstate : forall n : Nat, Measurable (state n))
    (n : Nat) :
    let stepKernel :=
      RewardKernel.actionRewardHistoryStepKernelFamily rewardKernel policy
        context state hcontext hstate
    let mu :=
      ProbabilityTheory.Kernel.trajMeasure
        (X := fun _ : Nat => Prod Action Reward) mu0 stepKernel
    Filter.EventuallyEq (ae mu)
      (fun trajectory : Nat -> Prod Action Reward => (trajectory (n + 1)).1)
      (fun trajectory : Nat -> Prod Action Reward =>
        (policy n).action (state n (Preorder.frestrictLe n trajectory))) := by
  let stepKernel :=
    RewardKernel.actionRewardHistoryStepKernelFamily rewardKernel policy
      context state hcontext hstate
  let mu :=
    ProbabilityTheory.Kernel.trajMeasure
      (X := fun _ : Nat => Prod Action Reward) mu0 stepKernel
  let joinPrefixNext := fun trajectory : Nat -> Prod Action Reward =>
    (Preorder.frestrictLe n trajectory, trajectory (n + 1))
  have hp : MeasurableSet
      {sample : (((i : Finset.Iic n) -> Prod Action Reward) ×
          Prod Action Reward) |
        sample.2.1 = (policy n).action (state n sample.1)} :=
    measurableSet_eq_fun (measurable_fst.comp measurable_snd)
      ((policy n).measurable_action.comp ((hstate n).comp measurable_fst))
  have hjoint : ∀ᵐ sample ∂
      mu.map (Preorder.frestrictLe n) ⊗ₘ stepKernel n,
      sample.2.1 = (policy n).action (state n sample.1) := by
    apply Measure.ae_compProd_of_ae_ae hp
    filter_upwards [] with history
    exact
      eventuallyEq_const_of_map_eq_dirac
        (stepKernel n history) Prod.fst
        ((policy n).action (state n history)) measurable_fst
        (by
          simpa [stepKernel] using
            (RewardKernel.actionRewardHistoryStepKernelFamily_action_map
              rewardKernel policy context state hcontext hstate n history))
  have hkernel :
      mu.map joinPrefixNext =
        mu.map (Preorder.frestrictLe n) ⊗ₘ stepKernel n := by
    have hbase :
        (ProbabilityTheory.Kernel.trajMeasure
            (X := fun _ : Nat => Prod Action Reward) mu0 stepKernel).map
              (Preorder.frestrictLe n) ⊗ₘ stepKernel n =
          (ProbabilityTheory.Kernel.trajMeasure
            (X := fun _ : Nat => Prod Action Reward) mu0 stepKernel).map
              (fun trajectory : Nat -> Prod Action Reward =>
                (Preorder.frestrictLe n trajectory, trajectory (n + 1))) :=
      ProbabilityTheory.Kernel.map_frestrictLe_trajMeasure_compProd_eq_map_trajMeasure
        (X := fun _ : Nat => Prod Action Reward)
        (μ₀ := mu0) (κ := stepKernel) (a := n)
    simpa only [mu, joinPrefixNext] using hbase.symm
  rw [← hkernel] at hjoint
  have hsource :=
    (ae_map_iff
      ((Preorder.measurable_frestrictLe n).prodMk
        (measurable_pi_apply (n + 1))).aemeasurable hp).mp hjoint
  simpa [joinPrefixNext, mu] using hsource

/--
Canonical action/reward `trajMeasure` two-sided tail for one policy-selected
arm under a random cumulative predictable-variance budget.

The mask uses the action selected from the observed reward history, so it is
measurable at filtration level `i`.  Identifying this mask with the sampled
next-action coordinate is intentionally left to a separate transport theorem.
-/
theorem actionRewardHistoryStepKernelFamily_policyArmMaskedCenteredRewardSuccProcess_sum_abs_tail_predictableVariance_ennreal_delta_trajMeasure_on_horizon
    {Context : Type v} {State : Type w} {Action : Type x}
    [MeasurableSpace Context] [MeasurableSpace State]
    [MeasurableSpace Action] [StandardBorelSpace Action]
    [MeasurableSingletonClass Action] [Countable Action] [Nonempty Action]
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
    (arm : Action) (sigma2 : NNReal) (n : Nat)
    (hvariance : forall i : Nat, i < n - 1 ->
      forall history : ((j : Finset.Iic i) -> Rat),
        varianceProxy (context i history)
          ((policy i).action (state i history)) <= sigma2)
    (varianceBudget delta : Real)
    (hvarianceBudget : 0 < varianceBudget) (hdelta : 0 < delta) :
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
    let reward : (Nat -> Prod Action Rat) -> RewardTrace Rat :=
      fun trajectory t => (trajectory t).2
    let X : Nat -> (Nat -> Prod Action Rat) -> Real := fun i trajectory =>
      (((reward trajectory (i + 1) -
        mean
          (context i
            (History.finiteRewardHistoryOfTrace (reward trajectory) i))
          ((policy i).action
            (state i
              (History.finiteRewardHistoryOfTrace
                (reward trajectory) i))) : Rat) : Real))
    let s : Nat -> Set (Nat -> Prod Action Rat) := fun i =>
      {trajectory |
        (policy i).action
          (state i
            (History.finiteRewardHistoryOfTrace (reward trajectory) i)) = arm}
    let Y : Nat -> (Nat -> Prod Action Rat) -> Real := fun t trajectory =>
      match t with
      | 0 => 0
      | i + 1 => (s i).indicator (X i) trajectory
    let V : Nat -> (Nat -> Prod Action Rat) -> Real := fun t trajectory =>
      match t with
      | 0 => 0
      | i + 1 =>
          (s i).indicator (fun _ => (((sigma2 : NNReal) : Real))) trajectory
    mu {trajectory |
        Concentration.subGaussianPredictableVarianceRadius
            varianceBudget delta <=
          |(Finset.range n).sum (fun t => Y t trajectory)| ∧
        (Finset.range n).sum (fun t => V t trajectory) <= varianceBudget} <=
      ENNReal.ofReal delta := by
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
  have haction : forall t : Nat,
      Measurable (fun trajectory : Nat -> Prod Action Rat =>
        action trajectory t) := fun t =>
    measurable_fst.comp (measurable_pi_apply t)
  have hreward : forall t : Nat,
      Measurable (fun trajectory : Nat -> Prod Action Rat =>
        reward trajectory t) := fun t =>
    measurable_snd.comp (measurable_pi_apply t)
  let F := History.historyFiltrationSucc action reward haction hreward
  let X : Nat -> (Nat -> Prod Action Rat) -> Real := fun i trajectory =>
    (((reward trajectory (i + 1) -
      mean
        (context i
          (History.finiteRewardHistoryOfTrace (reward trajectory) i))
        ((policy i).action
          (state i
            (History.finiteRewardHistoryOfTrace (reward trajectory) i))) :
      Rat) : Real))
  let c : Nat -> NNReal := fun _ => sigma2
  let s : Nat -> Set (Nat -> Prod Action Rat) := fun i =>
    {trajectory |
      (policy i).action
        (state i
          (History.finiteRewardHistoryOfTrace (reward trajectory) i)) = arm}
  let Y : Nat -> (Nat -> Prod Action Rat) -> Real := fun t trajectory =>
    match t with
    | 0 => 0
    | i + 1 => (s i).indicator (X i) trajectory
  let V : Nat -> (Nat -> Prod Action Rat) -> Real := fun t trajectory =>
    match t with
    | 0 => 0
    | i + 1 =>
        (s i).indicator (fun _ => (((sigma2 : NNReal) : Real))) trajectory
  have hs : forall i, @MeasurableSet (Nat -> Prod Action Rat) (F i) (s i) := by
    intro i
    have hhistory :
        @Measurable (Nat -> Prod Action Rat)
          ((j : Finset.Iic i) -> Rat) (F i) inferInstance
          (fun trajectory =>
            History.finiteRewardHistoryOfTrace (reward trajectory) i) := by
      have hpair :=
        History.measurable_finitePairHistoryOfTrace_mem_historyFiltration_of_lt
          action reward haction hreward (Nat.lt_succ_self i)
      have hprojection :=
        (History.measurable_pairHistoryRewardProjection
          (Action := Action) (Reward := Rat) i).comp hpair
      simpa [F, History.historyFiltrationSucc_apply] using hprojection
    have hselected :
        @Measurable (Nat -> Prod Action Rat) Action (F i) inferInstance
          (fun trajectory =>
            (policy i).action
              (state i
                (History.finiteRewardHistoryOfTrace
                  (reward trajectory) i))) :=
      (policy i).measurable_action.comp ((hstate i).comp hhistory)
    simpa [s, Set.preimage] using hselected (MeasurableSet.singleton arm)
  have hcentered : StronglyAdapted F (fun t trajectory =>
      match t with
      | 0 => 0
      | i + 1 => X i trajectory) := by
    simpa [F, X] using
      (centeredRewardSuccProcess_stronglyAdapted_historyFiltrationSucc
        action policy context state hcontext hstate mean hmean reward haction
        hreward)
  have hY : StronglyAdapted F Y := by
    intro t
    cases t with
    | zero => exact stronglyMeasurable_const
    | succ i =>
        have hsi : @MeasurableSet (Nat -> Prod Action Rat) (F (i + 1)) (s i) :=
          (F.mono (Nat.le_succ i)) _ (hs i)
        simpa [Y] using (hcentered (i + 1)).indicator hsi
  have hV : StronglyAdapted F V := by
    intro t
    cases t with
    | zero => exact stronglyMeasurable_const
    | succ i =>
        have hsi : @MeasurableSet (Nat -> Prod Action Rat) (F (i + 1)) (s i) :=
          (F.mono (Nat.le_succ i)) _ (hs i)
        simpa [V] using
          (MeasureTheory.stronglyMeasurable_const.indicator hsi)
  have hsubG : forall i, i < n - 1 ->
      ProbabilityTheory.HasCondSubgaussianMGF
        (F i) (F.le i) (X i) (c i) mu := by
    intro i hi
    have hcanonical :=
      RewardKernel.actionRewardHistoryStepKernelFamily_condDistrib_trajMeasure
        mu0 rewardKernel policy pairContext pairState hpairContext hpairState i
    have hvariance' :
        Filter.Eventually
          (fun trajectory : Nat -> Prod Action Rat =>
            varianceProxy
                (context i
                  (History.finiteRewardHistoryOfTrace
                    (reward trajectory) i))
                ((policy i).action
                  (state i
                    (History.finiteRewardHistoryOfTrace
                      (reward trajectory) i))) <= sigma2)
          (ae (mu.trim (F.le i))) :=
      Filter.Eventually.of_forall (fun trajectory =>
        hvariance i hi
          (History.finiteRewardHistoryOfTrace (reward trajectory) i))
    have hmgf :=
      centeredReward_succ_hasCondSubgaussianMGF_of_pair_condDistrib_of_ae_variance
        mu action rewardKernel policy context state hcontext hstate mean
        varianceProxy law hmean reward haction hreward i sigma2 hvariance'
        (by
          simpa [mu, stepKernel, action, reward, pairContext, pairState,
            hpairContext, hpairState, History.finitePairHistoryOfTrace] using
              hcanonical)
    simpa [F, X, c] using hmgf
  have htail :=
    Concentration.condSubGaussian_indicator_sum_abs_tail_predictableVariance_delta
      F X c s hY hV hs n hsubG varianceBudget delta
        hvarianceBudget hdelta
  simpa [mu, action, reward, F, X, c, s, Y, V, pairContext, pairState,
    hpairContext, hpairState, stepKernel] using htail

/--
Canonical sampled-arm masked centered-reward tail with the random predictable
proxy written as `sigma2` times the actual successor pull count.

The proof transports the history-policy mask through the canonical ambient
a.e. successor-action law.  It remains a fixed-horizon joint event, before
exact-count peeling or empirical-mean normalization.
-/
theorem actionRewardHistoryStepKernelFamily_sampledArmMaskedCenteredRewardSuccProcess_sum_abs_tail_successorPullCount_ennreal_delta_trajMeasure_on_horizon
    {Context : Type v} {State : Type w} {Action : Type x}
    [MeasurableSpace Context] [MeasurableSpace State]
    [MeasurableSpace Action] [StandardBorelSpace Action]
    [MeasurableSingletonClass Action] [Countable Action] [Nonempty Action]
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
    (arm : Action) (sigma2 : NNReal) (n : Nat)
    (hvariance : forall i : Nat, i < n - 1 ->
      forall history : ((j : Finset.Iic i) -> Rat),
        varianceProxy (context i history)
          ((policy i).action (state i history)) <= sigma2)
    (varianceBudget delta : Real)
    (hvarianceBudget : 0 < varianceBudget) (hdelta : 0 < delta) :
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
    let X : Nat -> (Nat -> Prod Action Rat) -> Real := fun i trajectory =>
      (((reward trajectory (i + 1) -
        mean
          (context i
            (History.finiteRewardHistoryOfTrace (reward trajectory) i))
          ((policy i).action
            (state i
              (History.finiteRewardHistoryOfTrace
                (reward trajectory) i))) : Rat) : Real))
    let Y : Nat -> (Nat -> Prod Action Rat) -> Real := fun t trajectory =>
      match t with
      | 0 => 0
      | i + 1 =>
          if action trajectory (i + 1) = arm then X i trajectory else 0
    mu {trajectory |
        Concentration.subGaussianPredictableVarianceRadius
            varianceBudget delta <=
          |(Finset.range n).sum (fun t => Y t trajectory)| ∧
        (((sigma2 : NNReal) : Real)) *
            (successorArmPullCount (action trajectory) arm n : Real) <=
          varianceBudget} <=
      ENNReal.ofReal delta := by
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
  let X : Nat -> (Nat -> Prod Action Rat) -> Real := fun i trajectory =>
    (((reward trajectory (i + 1) -
      mean
        (context i
          (History.finiteRewardHistoryOfTrace (reward trajectory) i))
        ((policy i).action
          (state i
            (History.finiteRewardHistoryOfTrace (reward trajectory) i))) :
      Rat) : Real))
  let sPolicy : Nat -> Set (Nat -> Prod Action Rat) := fun i =>
    {trajectory |
      (policy i).action
        (state i
          (History.finiteRewardHistoryOfTrace (reward trajectory) i)) = arm}
  let YPolicy : Nat -> (Nat -> Prod Action Rat) -> Real := fun t trajectory =>
    match t with
    | 0 => 0
    | i + 1 => (sPolicy i).indicator (X i) trajectory
  let VPolicy : Nat -> (Nat -> Prod Action Rat) -> Real := fun t trajectory =>
    match t with
    | 0 => 0
    | i + 1 =>
        (sPolicy i).indicator
          (fun _ => (((sigma2 : NNReal) : Real))) trajectory
  let YSampled : Nat -> (Nat -> Prod Action Rat) -> Real := fun t trajectory =>
    match t with
    | 0 => 0
    | i + 1 =>
        if action trajectory (i + 1) = arm then X i trajectory else 0
  have htail :
      mu {trajectory |
          Concentration.subGaussianPredictableVarianceRadius
              varianceBudget delta <=
            |(Finset.range n).sum (fun t => YPolicy t trajectory)| ∧
          (Finset.range n).sum (fun t => VPolicy t trajectory) <=
            varianceBudget} <=
        ENNReal.ofReal delta := by
    simpa [pairContext, pairState, hpairContext, hpairState, stepKernel, mu,
      reward, X, sPolicy, YPolicy, VPolicy] using
        (actionRewardHistoryStepKernelFamily_policyArmMaskedCenteredRewardSuccProcess_sum_abs_tail_predictableVariance_ennreal_delta_trajMeasure_on_horizon
          mu0 rewardKernel policy context state hcontext hstate mean
            varianceProxy law hmean arm sigma2 n hvariance varianceBudget delta
            hvarianceBudget hdelta)
  have hactionEq : forall i : Nat,
      Filter.EventuallyEq (ae mu)
        (fun trajectory : Nat -> Prod Action Rat => action trajectory (i + 1))
        (fun trajectory : Nat -> Prod Action Rat =>
          (policy i).action
            (state i
              (History.finiteRewardHistoryOfTrace
                (reward trajectory) i))) := by
    intro i
    have hcanonical :=
      actionRewardHistoryStepKernelFamily_action_succ_ae_eq_policy_trajMeasure
        mu0 rewardKernel policy pairContext pairState hpairContext hpairState i
    simpa [mu, stepKernel, action, reward, pairState,
      History.pairHistoryRewardProjection, History.finiteRewardHistoryOfTrace,
      Preorder.frestrictLe_apply] using hcanonical
  have hactionAll : ∀ᵐ trajectory ∂mu, forall i : Nat,
      action trajectory (i + 1) =
        (policy i).action
          (state i
            (History.finiteRewardHistoryOfTrace (reward trajectory) i)) :=
    ae_all_iff.2 hactionEq
  have hevents : ∀ᵐ trajectory ∂mu,
      (Concentration.subGaussianPredictableVarianceRadius
            varianceBudget delta <=
          |(Finset.range n).sum (fun t => YSampled t trajectory)| ∧
        (((sigma2 : NNReal) : Real)) *
            (successorArmPullCount (action trajectory) arm n : Real) <=
          varianceBudget) ↔
      (Concentration.subGaussianPredictableVarianceRadius
            varianceBudget delta <=
          |(Finset.range n).sum (fun t => YPolicy t trajectory)| ∧
        (Finset.range n).sum (fun t => VPolicy t trajectory) <=
          varianceBudget) := by
    filter_upwards [hactionAll] with trajectory htrajectory
    have hsum :
        (Finset.range n).sum (fun t => YSampled t trajectory) =
          (Finset.range n).sum (fun t => YPolicy t trajectory) := by
      apply Finset.sum_congr rfl
      intro t _ht
      cases t with
      | zero => simp [YSampled, YPolicy]
      | succ i =>
          by_cases hselected :
              (policy i).action
                (state i
                  (History.finiteRewardHistoryOfTrace
                    (reward trajectory) i)) = arm
          · simp [YSampled, YPolicy, sPolicy, htrajectory i, hselected]
          · simp [YSampled, YPolicy, sPolicy, htrajectory i, hselected]
    have hproxy :
        (Finset.range n).sum (fun t => VPolicy t trajectory) =
          (((sigma2 : NNReal) : Real)) *
            (successorArmPullCount (action trajectory) arm n : Real) := by
      calc
        (Finset.range n).sum (fun t => VPolicy t trajectory) =
            (Finset.range n).sum (fun t =>
              match t with
              | 0 => 0
              | i + 1 =>
                  if action trajectory (i + 1) = arm then
                    (((sigma2 : NNReal) : Real)) else 0) := by
              apply Finset.sum_congr rfl
              intro t _ht
              cases t with
              | zero => simp [VPolicy]
              | succ i =>
                  by_cases hselected :
                      (policy i).action
                        (state i
                          (History.finiteRewardHistoryOfTrace
                            (reward trajectory) i)) = arm
                  · simp [VPolicy, sPolicy, htrajectory i, hselected]
                  · simp [VPolicy, sPolicy, htrajectory i, hselected]
        _ = (((sigma2 : NNReal) : Real)) *
              (successorArmPullCount (action trajectory) arm n : Real) :=
          armMaskedVarianceSuccProcess_sum_eq_mul_successorArmPullCount
            (action trajectory) arm sigma2 n
    rw [hsum, hproxy]
  calc
    mu {trajectory |
        Concentration.subGaussianPredictableVarianceRadius
            varianceBudget delta <=
          |(Finset.range n).sum (fun t => YSampled t trajectory)| ∧
        (((sigma2 : NNReal) : Real)) *
            (successorArmPullCount (action trajectory) arm n : Real) <=
          varianceBudget} =
      mu {trajectory |
        Concentration.subGaussianPredictableVarianceRadius
            varianceBudget delta <=
          |(Finset.range n).sum (fun t => YPolicy t trajectory)| ∧
        (Finset.range n).sum (fun t => VPolicy t trajectory) <=
          varianceBudget} :=
      measure_congr (hevents.mono fun _ h => propext h)
    _ <= ENNReal.ofReal delta := htail

/--
Canonical fixed-arm empirical-mean confidence on one exact positive successor
pull-count fiber.  The canonical sampled-arm tail is instantiated with budget
`sigma2 * k`, and the centered sum is divided by the positive count `k`.
-/
theorem actionRewardHistoryStepKernelFamily_successorArmEmpiricalMean_abs_tail_exact_pullCount_ennreal_delta_trajMeasure_on_horizon
    {Context : Type v} {State : Type w} {Action : Type x}
    [MeasurableSpace Context] [MeasurableSpace State]
    [MeasurableSpace Action] [StandardBorelSpace Action]
    [MeasurableSingletonClass Action] [Countable Action] [Nonempty Action]
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
    (arm : Action) (armMean : Rat) (sigma2 : NNReal) (n k : Nat)
    (hvariance : forall i : Nat, i < n - 1 ->
      forall history : ((j : Finset.Iic i) -> Rat),
        varianceProxy (context i history)
          ((policy i).action (state i history)) <= sigma2)
    (harmMean : forall i : Nat,
      forall history : ((j : Finset.Iic i) -> Rat),
        mean (context i history) arm = armMean)
    (hk : 0 < k) (hsigma2 : 0 < (((sigma2 : NNReal) : Real)))
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
    let count : (Nat -> Prod Action Rat) -> Nat := fun trajectory =>
      successorArmPullCount (action trajectory) arm n
    mu {trajectory |
        count trajectory = k ∧
          successorArmEmpiricalMeanExactCountRadius sigma2 k delta <=
            |successorArmEmpiricalMean
                (action trajectory) (reward trajectory) arm n -
              (armMean : Real)|} <=
      ENNReal.ofReal delta := by
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
  let X : Nat -> (Nat -> Prod Action Rat) -> Real := fun i trajectory =>
    (((reward trajectory (i + 1) -
      mean
        (context i
          (History.finiteRewardHistoryOfTrace (reward trajectory) i))
        ((policy i).action
          (state i
            (History.finiteRewardHistoryOfTrace
              (reward trajectory) i))) : Rat) : Real))
  let Y : Nat -> (Nat -> Prod Action Rat) -> Real := fun t trajectory =>
    match t with
    | 0 => 0
    | i + 1 =>
        if action trajectory (i + 1) = arm then X i trajectory else 0
  let count : (Nat -> Prod Action Rat) -> Nat := fun trajectory =>
    successorArmPullCount (action trajectory) arm n
  let varianceBudget : Real := (((sigma2 : NNReal) : Real)) * (k : Real)
  have hvarianceBudget : 0 < varianceBudget := by
    exact mul_pos hsigma2 (by exact_mod_cast hk)
  have htail :
      mu {trajectory |
          Concentration.subGaussianPredictableVarianceRadius
              varianceBudget delta <=
            |(Finset.range n).sum (fun t => Y t trajectory)| ∧
          (((sigma2 : NNReal) : Real)) * (count trajectory : Real) <=
            varianceBudget} <=
        ENNReal.ofReal delta := by
    simpa [pairContext, pairState, hpairContext, hpairState, stepKernel, mu,
      action, reward, X, Y, count, varianceBudget] using
        (actionRewardHistoryStepKernelFamily_sampledArmMaskedCenteredRewardSuccProcess_sum_abs_tail_successorPullCount_ennreal_delta_trajMeasure_on_horizon
          mu0 rewardKernel policy context state hcontext hstate mean
            varianceProxy law hmean arm sigma2 n hvariance varianceBudget delta
            hvarianceBudget hdelta)
  have hactionEq : forall i : Nat,
      Filter.EventuallyEq (ae mu)
        (fun trajectory : Nat -> Prod Action Rat => action trajectory (i + 1))
        (fun trajectory : Nat -> Prod Action Rat =>
          (policy i).action
            (state i
              (History.finiteRewardHistoryOfTrace
                (reward trajectory) i))) := by
    intro i
    have hcanonical :=
      actionRewardHistoryStepKernelFamily_action_succ_ae_eq_policy_trajMeasure
        mu0 rewardKernel policy pairContext pairState hpairContext hpairState i
    simpa [mu, stepKernel, action, reward, pairState,
      History.pairHistoryRewardProjection, History.finiteRewardHistoryOfTrace,
      Preorder.frestrictLe_apply] using hcanonical
  have hactionAll : ∀ᵐ trajectory ∂mu, forall i : Nat,
      action trajectory (i + 1) =
        (policy i).action
          (state i
            (History.finiteRewardHistoryOfTrace (reward trajectory) i)) :=
    ae_all_iff.2 hactionEq
  have hsubset : ∀ᵐ trajectory ∂mu,
      trajectory ∈ {trajectory |
          count trajectory = k ∧
            successorArmEmpiricalMeanExactCountRadius sigma2 k delta <=
              |successorArmEmpiricalMean
                  (action trajectory) (reward trajectory) arm n -
                (armMean : Real)|} ->
        trajectory ∈ {trajectory |
          Concentration.subGaussianPredictableVarianceRadius
              varianceBudget delta <=
            |(Finset.range n).sum (fun t => Y t trajectory)| ∧
          (((sigma2 : NNReal) : Real)) * (count trajectory : Real) <=
            varianceBudget} := by
    filter_upwards [hactionAll] with trajectory htrajectory
    intro homega
    rcases homega with ⟨hcount, hbad⟩
    have hkReal : 0 < (k : Real) := by exact_mod_cast hk
    have hkNe : (k : Real) ≠ 0 := ne_of_gt hkReal
    have hcenter : forall i : Nat,
        action trajectory (i + 1) = arm ->
          mean
            (context i
              (History.finiteRewardHistoryOfTrace (reward trajectory) i))
            ((policy i).action
              (state i
                (History.finiteRewardHistoryOfTrace
                  (reward trajectory) i))) = armMean := by
      intro i hselected
      have hselectedPolicy :
          (policy i).action
            (state i
              (History.finiteRewardHistoryOfTrace (reward trajectory) i)) =
            arm := by
        calc
          (policy i).action
              (state i
                (History.finiteRewardHistoryOfTrace (reward trajectory) i)) =
              action trajectory (i + 1) := (htrajectory i).symm
          _ = arm := hselected
      simpa [hselectedPolicy] using
        (harmMean i
          (History.finiteRewardHistoryOfTrace (reward trajectory) i))
    have hsum :
        (Finset.range n).sum (fun t => Y t trajectory) =
          successorArmRewardSum
              (action trajectory) (reward trajectory) arm n -
            (count trajectory : Real) * (armMean : Real) := by
      simpa [Y, X, count] using
        (armMaskedCenteredRewardSuccProcess_sum_eq_successorArmRewardSum_sub_pullCount_mul
          (action trajectory) (reward trajectory)
          (fun i =>
            mean
              (context i
                (History.finiteRewardHistoryOfTrace (reward trajectory) i))
              ((policy i).action
                (state i
                  (History.finiteRewardHistoryOfTrace
                    (reward trajectory) i))))
          arm armMean hcenter n)
    have haverage :
        (Finset.range n).sum (fun t => Y t trajectory) / (k : Real) =
          successorArmEmpiricalMean
              (action trajectory) (reward trajectory) arm n -
            (armMean : Real) := by
      rw [hsum, hcount]
      simp only [successorArmEmpiricalMean]
      rw [show successorArmPullCount (action trajectory) arm n = k by
        simpa [count] using hcount]
      field_simp [hkNe]
    have hsumBad :
        Concentration.subGaussianPredictableVarianceRadius
            varianceBudget delta <=
          |(Finset.range n).sum (fun t => Y t trajectory)| := by
      change
        Concentration.subGaussianPredictableVarianceRadius
              varianceBudget delta / (k : Real) <=
          |successorArmEmpiricalMean
              (action trajectory) (reward trajectory) arm n -
            (armMean : Real)| at hbad
      rw [← haverage, abs_div, abs_of_pos hkReal] at hbad
      exact (div_le_div_iff_of_pos_right hkReal).mp hbad
    have hvarianceBound :
        (((sigma2 : NNReal) : Real)) * (count trajectory : Real) <=
          varianceBudget := by
      rw [hcount]
    exact ⟨hsumBad, hvarianceBound⟩
  exact (measure_mono_ae hsubset).trans htail

/--
Canonical positive random-pull-count empirical-mean confidence obtained by
peeling the exact-count theorem over the at most `n` successor count fibers.
This is fixed-horizon confidence, not an anytime confidence sequence.
-/
theorem actionRewardHistoryStepKernelFamily_successorArmEmpiricalMean_abs_tail_random_pullCount_ennreal_delta_trajMeasure_on_horizon
    {Context : Type v} {State : Type w} {Action : Type x}
    [MeasurableSpace Context] [MeasurableSpace State]
    [MeasurableSpace Action] [StandardBorelSpace Action]
    [MeasurableSingletonClass Action] [Countable Action] [Nonempty Action]
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
    (arm : Action) (armMean : Rat) (sigma2 : NNReal) (n : Nat)
    (hvariance : forall i : Nat, i < n - 1 ->
      forall history : ((j : Finset.Iic i) -> Rat),
        varianceProxy (context i history)
          ((policy i).action (state i history)) <= sigma2)
    (harmMean : forall i : Nat,
      forall history : ((j : Finset.Iic i) -> Rat),
        mean (context i history) arm = armMean)
    (hn : 0 < n) (hsigma2 : 0 < (((sigma2 : NNReal) : Real)))
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
    let count : (Nat -> Prod Action Rat) -> Nat := fun trajectory =>
      successorArmPullCount (action trajectory) arm n
    mu {trajectory |
        0 < count trajectory ∧
          successorArmEmpiricalMeanPeelingRadius
              sigma2 (count trajectory) n delta <=
            |successorArmEmpiricalMean
                (action trajectory) (reward trajectory) arm n -
              (armMean : Real)|} <=
      ENNReal.ofReal delta := by
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
  let count : (Nat -> Prod Action Rat) -> Nat := fun trajectory =>
    successorArmPullCount (action trajectory) arm n
  let bad : Nat -> Set (Nat -> Prod Action Rat) := fun k =>
    {trajectory |
      successorArmEmpiricalMeanPeelingRadius sigma2 k n delta <=
        |successorArmEmpiricalMean
            (action trajectory) (reward trajectory) arm n -
          (armMean : Real)|}
  have hnReal : 0 < (n : Real) := Nat.cast_pos.mpr hn
  have hdeltaShare : 0 < delta / (n : Real) := div_pos hdelta hnReal
  have hcount_le : forall trajectory, count trajectory <= n := by
    intro trajectory
    exact successorArmPullCount_le_horizon (action trajectory) arm n
  have hfiber : forall k, 0 < k -> k <= n ->
      mu {trajectory | count trajectory = k ∧ trajectory ∈ bad k} <=
        ENNReal.ofReal (delta / (n : Real)) := by
    intro k hk _hk_le
    simpa [pairContext, pairState, hpairContext, hpairState, stepKernel, mu,
      action, reward, count, bad, successorArmEmpiricalMeanPeelingRadius] using
        (actionRewardHistoryStepKernelFamily_successorArmEmpiricalMean_abs_tail_exact_pullCount_ennreal_delta_trajMeasure_on_horizon
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
          (armMean := armMean)
          (sigma2 := sigma2)
          (n := n)
          (k := k)
          (hvariance := hvariance)
          (harmMean := harmMean)
          hk hsigma2 (delta / (n : Real)) hdeltaShare)
  simpa [pairContext, pairState, hpairContext, hpairState, stepKernel, mu,
    action, reward, count, bad] using
      (Concentration.measure_positive_randomCount_event_le_of_exactCount_uniform
        mu count n bad hcount_le hn delta hdelta hfiber)

/-
Finite-arm, finite-time empirical-mean confidence on the canonical
action/reward trajectory.  The variance premise is needed only through the
largest predecessor index used before time `T`; this is a fixed finite union,
not an anytime confidence sequence.
-/
theorem actionRewardHistoryStepKernelFamily_successorArmEmpiricalMean_simultaneous_finiteArmTime_abs_tail_ennreal_delta_trajMeasure
    {Context : Type v} {State : Type w} {Action : Type x}
    [MeasurableSpace Context] [MeasurableSpace State]
    [MeasurableSpace Action] [StandardBorelSpace Action]
    [MeasurableSingletonClass Action] [Countable Action] [Nonempty Action]
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
    (arms : Finset Action) (harms : arms.Nonempty)
    (armMean : Action -> Rat) (sigma2 : NNReal) (T : Nat)
    (hvariance : forall i : Nat, i < T - 1 ->
      forall history : ((j : Finset.Iic i) -> Rat),
        varianceProxy (context i history)
          ((policy i).action (state i history)) <= sigma2)
    (harmMean : forall i : Nat,
      forall history : ((j : Finset.Iic i) -> Rat),
        forall arm, arm ∈ arms ->
          mean (context i history) arm = armMean arm)
    (hT : 0 < T) (hsigma2 : 0 < (((sigma2 : NNReal) : Real)))
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
    mu (successorArmEmpiricalMeanFiniteArmTimeBadEvent action reward arms
      armMean sigma2 T delta) <= ENNReal.ofReal delta := by
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
  let family := arms.product (Finset.range T)
  let deltaShare :=
    successorArmEmpiricalMeanFiniteArmTimeConfidenceShare arms T delta
  let bad : Prod Action Nat -> Set (Nat -> Prod Action Rat) := fun pair =>
    {trajectory |
      0 < successorArmPullCount (action trajectory) pair.1 (pair.2 + 1) ∧
        successorArmEmpiricalMeanFiniteArmTimePeelingRadius sigma2
            (successorArmPullCount (action trajectory) pair.1 (pair.2 + 1))
            (pair.2 + 1) arms T delta <=
          |successorArmEmpiricalMean (action trajectory) (reward trajectory)
              pair.1 (pair.2 + 1) - (armMean pair.1 : Real)|}
  have hfamily : family.Nonempty := by
    rcases harms with ⟨arm, harm⟩
    refine ⟨(arm, 0), ?_⟩
    exact Finset.mem_product.mpr
      ⟨harm, Finset.mem_range.mpr hT⟩
  have hfamilyCard : 0 < family.card := Finset.card_pos.mpr hfamily
  have hfamilyCardReal : 0 < (family.card : Real) :=
    Nat.cast_pos.mpr hfamilyCard
  have hdeltaShare : 0 < deltaShare := by
    simpa [deltaShare,
      successorArmEmpiricalMeanFiniteArmTimeConfidenceShare, family] using
      (div_pos hdelta hfamilyCardReal)
  have htail : forall pair, pair ∈ family ->
      mu (bad pair) <= ENNReal.ofReal (delta / (family.card : Real)) := by
    intro pair hpair
    have hpairMem := Finset.mem_product.mp hpair
    have hvariancePair : forall i : Nat, i < (pair.2 + 1) - 1 ->
        forall history : ((j : Finset.Iic i) -> Rat),
          varianceProxy (context i history)
            ((policy i).action (state i history)) <= sigma2 := by
      intro i hi history
      apply hvariance i
      have htime : pair.2 < T := Finset.mem_range.mp hpairMem.2
      omega
    have hsingle :=
      actionRewardHistoryStepKernelFamily_successorArmEmpiricalMean_abs_tail_random_pullCount_ennreal_delta_trajMeasure_on_horizon
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
        (arm := pair.1)
        (armMean := armMean pair.1)
        (sigma2 := sigma2)
        (n := pair.2 + 1)
        (hvariance := hvariancePair)
        (harmMean := fun i history =>
          harmMean i history pair.1 hpairMem.1)
        (Nat.succ_pos pair.2) hsigma2 deltaShare hdeltaShare
    simpa [pairContext, pairState, hpairContext, hpairState, stepKernel, mu,
      action, reward, bad, family, deltaShare,
      successorArmEmpiricalMeanFiniteArmTimePeelingRadius,
      successorArmEmpiricalMeanFiniteArmTimeConfidenceShare] using hsingle
  simpa [pairContext, pairState, hpairContext, hpairState, stepKernel, mu,
    action, reward, family, bad,
    successorArmEmpiricalMeanFiniteArmTimeBadEvent] using
      (ProbabilityUnionBound.measure_biUnion_finset_le_of_uniform
        mu family hfamily delta bad htail)

end ConditionalExpectationReward
end BanditRLProof
