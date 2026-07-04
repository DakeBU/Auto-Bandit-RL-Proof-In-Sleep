import BanditRLProof

namespace BanditRLProof

def constantZeroAction : Nat → Nat := fun _ => 0

example : pullCount constantZeroAction 0 3 = 3 := by
  native_decide

def alternatingAction : Nat → Fin 2 :=
  fun n => if n % 2 = 0 then 0 else 1

example : pullCount alternatingAction 0 5 = 3 := by
  native_decide

example :
    pullCount alternatingAction 0 5 =
      ((List.range 5).filter
        (fun s : Nat => decide (alternatingAction s = 0))).length := by
  exact pullCount_eq_list_filter_length alternatingAction 0 5

example :
    pullCount alternatingAction 0 5 =
      ((Finset.range 5).filter
        (fun s : Nat => alternatingAction s = 0)).card := by
  exact pullCount_eq_finset_filter_card alternatingAction 0 5

example (s : Finset Nat) (gap : Nat -> Real) (count : Nat -> Nat)
    (hgap : forall i : Nat, i ∈ s -> 0 <= gap i) :
    ENNReal.ofReal
      (s.sum (fun i : Nat => gap i * ((count i : Nat) : Real)))
      =
    s.sum
      (fun i : Nat =>
        ENNReal.ofReal (gap i) * ((count i : Nat) : ENNReal)) := by
  exact ENNReal.ofReal_finset_sum_mul_natCast_of_nonneg
    s gap count hgap

example {K : Nat}
    (model : FiniteBanditModel K)
    (action : ActionTrace (Fin K))
    (hgap : forall a : Fin K,
      0 <= (((model.gap a : Rat) : Real)))
    (n : Nat) :
    ENNReal.ofReal (((pseudoRegret model action n : Rat) : Real))
      =
    (Finset.univ : Finset (Fin K)).sum
      (fun a : Fin K =>
        ENNReal.ofReal (((model.gap a : Rat) : Real)) *
          ((pullCount action a n : Nat) : ENNReal)) := by
  exact
    ENNReal.ofReal_pseudoRegret_eq_univ_sum_model_gap_ofReal_mul_natCast_pullCount_of_nonneg
      model action hgap n

example : pullCount alternatingAction 0 1 = 1 := by
  rw [pullCount_one]
  native_decide

example : pullCount alternatingAction 0 (2 + 1) =
    pullCount alternatingAction 0 2 + 1 := by
  apply pullCount_succ_of_eq
  native_decide

example : pullCount alternatingAction 0 (1 + 1) =
    pullCount alternatingAction 0 1 := by
  apply pullCount_succ_of_ne
  native_decide

example (t : Nat) :
    pullCount alternatingAction 0 t ≤ pullCount alternatingAction 0 (t + 1) :=
  pullCount_le_succ alternatingAction 0 t

example (s t : Nat) (h : s ≤ t) :
    pullCount alternatingAction 0 s ≤ pullCount alternatingAction 0 t :=
  pullCount_mono alternatingAction 0 h

example (t : Nat) :
    pullCount alternatingAction 0 t ≤ t :=
  pullCount_le_time alternatingAction 0 t

example (t : Nat) :
    (Finset.univ : Finset (Fin 2)).sum
      (fun a : Fin 2 => pullCount alternatingAction a t) = t := by
  exact finset_sum_pullCount_eq_time alternatingAction t

example {K : Nat}
    (spec : ETC.Spec K) (commitArm a : Fin K)
    (hexplorationPulls_pos : 0 < spec.explorationPulls) :
    0 < pullCount (ETC.actionWithCommit spec commitArm) a
      (spec.explorationPulls * K) := by
  exact ETC.pullCount_actionWithCommit_explorationPulls_mul_K_pos
    spec commitArm a hexplorationPulls_pos

example {K : Nat}
    (spec : ETC.Spec K) (commitArm a : Fin K)
    (hexplorationPulls_pos : 0 < spec.explorationPulls) :
    (0 : Rat) < (pullCount (ETC.actionWithCommit spec commitArm) a
      (spec.explorationPulls * K) : Rat) := by
  exact ETC.ratCast_pullCount_actionWithCommit_explorationPulls_mul_K_pos
    spec commitArm a hexplorationPulls_pos

example {K : Nat}
    (spec : ETC.Spec K) (commitArm a : Fin K)
    (hexplorationPulls_pos : 0 < spec.explorationPulls) :
    Not ((pullCount (ETC.actionWithCommit spec commitArm) a
      (spec.explorationPulls * K) : Rat) = 0) := by
  exact ETC.ratCast_pullCount_actionWithCommit_explorationPulls_mul_K_ne_zero
    spec commitArm a hexplorationPulls_pos

example {K : Nat}
    (spec : ETC.Spec K) (commitArm a : Fin K)
    (reward : RewardTrace Rat) :
    ETC.empMeanAtExploration spec commitArm reward a =
      sumRewards (ETC.actionWithCommit spec commitArm) reward a
          (spec.explorationPulls * K) /
        ((spec.explorationPulls : Nat) : Rat) := by
  exact ETC.empMeanAtExploration_eq_sumRewards_div_explorationPulls
    spec commitArm reward a

example {K : Nat}
    (spec : ETC.Spec K) (commitArm a b : Fin K)
    (reward : RewardTrace Rat)
    (hexplorationPulls_pos : 0 < spec.explorationPulls) :
    ETC.empMeanAtExploration spec commitArm reward b <=
      ETC.empMeanAtExploration spec commitArm reward a ↔
    sumRewards (ETC.actionWithCommit spec commitArm) reward b
        (spec.explorationPulls * K) <=
      sumRewards (ETC.actionWithCommit spec commitArm) reward a
        (spec.explorationPulls * K) := by
  exact ETC.empMeanAtExploration_le_iff_sumRewards_le_of_explorationPulls_pos
    spec commitArm reward a b hexplorationPulls_pos

noncomputable example {Omega : Type} {K : Nat}
    (spec : ETC.Spec K)
    (model : FiniteBanditModel K)
    (commitArm : Fin K)
    (reward : Omega -> RewardTrace Rat)
    (a : Fin K)
    (hexplorationPulls_pos : 0 < spec.explorationPulls)
    {Idx : Type}
    (idx : Finset Idx)
    (X : Idx -> Omega -> Real)
    (eps : Real)
    (himp :
      forall omega : Omega,
        sumRewards (ETC.actionWithCommit spec commitArm) (reward omega)
            model.bestArm (spec.explorationPulls * K) <=
          sumRewards (ETC.actionWithCommit spec commitArm) (reward omega)
            a (spec.explorationPulls * K) ->
        eps <= idx.sum (fun i => X i omega)) :
    Set.Subset
      {omega : Omega |
        ETC.empMeanAtExploration spec commitArm (reward omega) a >=
          ETC.empMeanAtExploration spec commitArm (reward omega)
            model.bestArm}
      {omega : Omega | eps <= idx.sum (fun i => X i omega)} := by
  exact
    ETC.empMeanAtExploration_ge_best_event_subset_sumRewards_tail_event_of_imp
      spec model commitArm reward a hexplorationPulls_pos idx X eps himp

example {Action : Type} [DecidableEq Action]
    (action : ActionTrace Action) (reward : RewardTrace Rat)
    (a b : Action) (n m : Nat) (muA muB : Rat)
    (hcount_a : pullCount action a n = m)
    (hcount_b : pullCount action b n = m)
    (hraw :
      sumRewards action reward b n <= sumRewards action reward a n) :
    (m : Rat) * (muB - muA) <=
      (Finset.range n).sum (fun t : Nat =>
        (if action t = a then reward t - muA else 0) +
        (if action t = b then muB - reward t else 0)) := by
  exact ETC.sumRewards_le_imp_centered_pairwise_sum_ge
    action reward a b n m muA muB hcount_a hcount_b hraw

noncomputable example {Omega : Type} {K : Nat}
    (spec : ETC.Spec K)
    (model : FiniteBanditModel K)
    (commitArm : Fin K)
    (reward : Omega -> RewardTrace Rat)
    (a : Fin K)
    (hexplorationPulls_pos : 0 < spec.explorationPulls) :
    Set.Subset
      {omega : Omega |
        ETC.empMeanAtExploration spec commitArm (reward omega) a >=
          ETC.empMeanAtExploration spec commitArm (reward omega)
            model.bestArm}
      {omega : Omega |
        (((spec.explorationPulls : Rat) *
            (model.mean model.bestArm - model.mean a) : Rat) : Real) <=
          (Finset.range (spec.explorationPulls * K)).sum (fun t : Nat =>
            (((if ETC.actionWithCommit spec commitArm t = a then
                reward omega t - model.mean a else 0) +
              (if ETC.actionWithCommit spec commitArm t = model.bestArm then
                model.mean model.bestArm - reward omega t else 0) :
              Rat) : Real))} := by
  exact
    ETC.empMeanAtExploration_ge_best_event_subset_centered_pairwise_sum_event
      spec model commitArm reward a hexplorationPulls_pos

example {Omega : Type} {K : Nat}
    [MeasurableSpace Omega]
    [MeasurableSpace (Fin K)] [MeasurableSingletonClass (Fin K)]
    [MeasurableSpace Rat] [MeasurableAdd₂ Rat]
    (spec : ETC.Spec K) (commitArm a : Fin K)
    (reward : Omega -> RewardTrace Rat)
    (hreward : forall t : Nat,
      Measurable (fun omega : Omega => reward omega t)) :
    Measurable (fun omega : Omega =>
      sumRewards (ETC.actionWithCommit spec commitArm) (reward omega) a
        (spec.explorationPulls * K)) := by
  exact ETC.measurable_sumRewards_actionWithCommit_exploration
    spec commitArm a reward hreward

example {Omega : Type} {K : Nat}
    [MeasurableSpace Omega]
    [MeasurableSpace (Fin K)] [MeasurableSingletonClass (Fin K)]
    [MeasurableSpace Rat] [MeasurableAdd₂ Rat]
    (spec : ETC.Spec K) (commitArm a : Fin K)
    (reward : Omega -> RewardTrace Rat)
    (hreward : forall t : Nat,
      Measurable (fun omega : Omega => reward omega t))
    (hdiv_const : forall c : Rat, Measurable (fun x : Rat => x / c)) :
    Measurable (fun omega : Omega =>
      ETC.empMeanAtExploration spec commitArm (reward omega) a) := by
  exact ETC.measurable_empMeanAtExploration_of_measurable_div_const
    spec commitArm a reward hreward hdiv_const

example [MeasurableSpace Rat] [MeasurableSingletonClass Rat] (c : Rat) :
    Measurable (fun x : Rat => x / c) := by
  exact measurable_rat_div_const c

example {Omega : Type} {K : Nat}
    [MeasurableSpace Omega]
    [MeasurableSpace (Fin K)] [MeasurableSingletonClass (Fin K)]
    [MeasurableSpace Rat] [MeasurableSingletonClass Rat] [MeasurableAdd₂ Rat]
    (spec : ETC.Spec K) (commitArm a : Fin K)
    (reward : Omega -> RewardTrace Rat)
    (hreward : forall t : Nat,
      Measurable (fun omega : Omega => reward omega t)) :
    Measurable (fun omega : Omega =>
      ETC.empMeanAtExploration spec commitArm (reward omega) a) := by
  exact ETC.measurable_empMeanAtExploration
    spec commitArm a reward hreward

example {Omega : Type} {K : Nat}
    [MeasurableSpace Omega]
    [MeasurableSpace (Fin K)] [MeasurableSingletonClass (Fin K)]
    [MeasurableSpace Rat] [MeasurableSingletonClass Rat] [MeasurableAdd₂ Rat]
    (spec : ETC.Spec K) (commitArm : Fin K)
    (reward : Omega -> RewardTrace Rat)
    (hreward : forall t : Nat,
      Measurable (fun omega : Omega => reward omega t)) :
    forall a : Fin K,
      Measurable (fun omega : Omega =>
        (fun b : Fin K =>
          ETC.empMeanAtExploration spec commitArm (reward omega) b) a) := by
  exact ETC.measurable_empMeanAtExploration_coordinates
    spec commitArm reward hreward

example {Omega : Type} {K : Nat}
    [MeasurableSpace Omega]
    [MeasurableSpace Rat]
    (empMean : Omega -> Fin K -> Rat)
    (hmeas_coord :
      forall a : Fin K, Measurable (fun omega : Omega => empMean omega a)) :
    Measurable (fun omega : Omega => (empMean omega : Fin K -> Rat)) := by
  exact ETC.measurable_empMeanVector_of_forall_measurable
    empMean hmeas_coord

example {Omega : Type} {Action : Type}
    [MeasurableSpace Omega] [MeasurableSpace Action]
    [MeasurableSingletonClass Action]
    (action : Omega -> ActionTrace Action)
    (hmeas : forall t : Nat, Measurable (fun omega : Omega => action omega t))
    (a : Action) (t : Nat) :
    MeasurableSet {omega : Omega | action omega t = a} := by
  exact measurableSet_actionTrace_eval_eq action hmeas a t

example {Action : Type}
    [MeasurableSpace Action]
    (t : Nat) (i : Finset.Iic t) :
    Measurable
      (fun history : History.FiniteActionHistory Action t => history i) := by
  exact History.measurable_finiteActionHistory_eval t i

example {Action Reward : Type}
    [MeasurableSpace Action] [MeasurableSpace Reward]
    (t : Nat) (i : Finset.Iic t) :
    Measurable
      (fun history : History.FiniteHistory Action Reward t => history.2 i) := by
  exact History.measurable_finiteHistory_reward_eval t i

example {Action Reward : Type}
    [MeasurableSpace Action] [MeasurableSpace Reward]
    (t : Nat) :
    Measurable
      (fun history : (i : Finset.Iic t) -> Prod Action Reward =>
        History.pairHistoryRewardProjection history) := by
  exact History.measurable_pairHistoryRewardProjection t

example {Omega : Type} {Action : Type}
    [MeasurableSpace Omega] [MeasurableSpace Action]
    (action : Omega -> ActionTrace Action)
    (haction : forall t : Nat,
      Measurable (fun omega : Omega => action omega t))
    (t : Nat) :
    Measurable
      (fun omega : Omega =>
        History.finiteActionHistoryOfTrace (action omega) t) := by
  exact History.measurable_finiteActionHistoryOfTrace action haction t

example {Omega : Type} {Action : Type} {Reward : Type}
    [MeasurableSpace Omega]
    [MeasurableSpace Action] [MeasurableSpace Reward]
    (action : Omega -> ActionTrace Action)
    (reward : Omega -> RewardTrace Reward)
    (haction : forall t : Nat,
      Measurable (fun omega : Omega => action omega t))
    (hreward : forall t : Nat,
      Measurable (fun omega : Omega => reward omega t))
    (t : Nat) :
    Measurable
      (fun omega : Omega =>
        History.finiteHistoryOfTrace (action omega) (reward omega) t) := by
  exact History.measurable_finiteHistoryOfTrace
    action reward haction hreward t

example {Omega : Type} {Action : Type} {Reward : Type}
    [MeasurableSpace Omega]
    [MeasurableSpace Action] [MeasurableSpace Reward]
    (action : Omega -> ActionTrace Action)
    (reward : Omega -> RewardTrace Reward)
    (haction : forall t : Nat,
      Measurable (fun omega : Omega => action omega t))
    (hreward : forall t : Nat,
      Measurable (fun omega : Omega => reward omega t))
    (t : Nat) :
    Measurable
      (fun omega : Omega =>
        History.finitePairHistoryOfTrace (action omega) (reward omega) t) := by
  exact History.measurable_finitePairHistoryOfTrace
    action reward haction hreward t

example {Action : Type} {Reward : Type}
    (action : ActionTrace Action)
    (reward : RewardTrace Reward)
    (t : Nat) :
    History.finitePairHistoryOfTrace action reward (t + 1) =
      History.extendPairHistorySucc
        (History.finitePairHistoryOfTrace action reward t)
        (action (t + 1), reward (t + 1)) := by
  exact History.finitePairHistoryOfTrace_succ action reward t

example {Action : Type} {Reward : Type}
    [MeasurableSpace Action] [MeasurableSpace Reward]
    (t : Nat) :
    Measurable
      (fun input :
          Prod (History.FinitePairHistory Action Reward t) (Prod Action Reward) =>
        History.extendPairHistorySucc input.1 input.2) := by
  exact History.measurable_extendPairHistorySucc

example {Omega : Type} {Action : Type} {Reward : Type}
    [mOmega : MeasurableSpace Omega]
    [MeasurableSpace Action] [MeasurableSingletonClass Action]
    [Countable Action]
    [MeasurableSpace Reward] [MeasurableSingletonClass Reward]
    (action : Omega -> ActionTrace Action)
    (reward : Omega -> RewardTrace Reward)
    (haction : forall t : Nat,
      Measurable (fun omega : Omega => action omega t))
    (hreward : forall t : Nat,
      Measurable (fun omega : Omega => reward omega t)) :
    MeasureTheory.Filtration Nat mOmega := by
  exact History.historyFiltration action reward haction hreward

example {Omega : Type} {Action : Type} {Reward : Type}
    [mOmega : MeasurableSpace Omega]
    [MeasurableSpace Action] [MeasurableSingletonClass Action]
    [MeasurableSpace Reward] [MeasurableSingletonClass Reward]
    (action : Omega -> ActionTrace Action)
    (reward : Omega -> RewardTrace Reward)
    (haction : forall t : Nat,
      Measurable (fun omega : Omega => action omega t))
    (hreward : forall t : Nat,
      Measurable (fun omega : Omega => reward omega t))
    {i t : Nat} (hit : i < t) (a : Action) :
    @MeasurableSet Omega
      (History.historyFiltration action reward haction hreward t)
      (Set.preimage (fun omega => action omega i) (Set.singleton a)) := by
  exact History.measurableSet_action_mem_historyFiltration
    action reward haction hreward hit a

example {Omega : Type} {Action : Type} {Reward : Type}
    [mOmega : MeasurableSpace Omega]
    [MeasurableSpace Action] [MeasurableSingletonClass Action]
    [Countable Action]
    [MeasurableSpace Reward] [MeasurableSingletonClass Reward]
    (action : Omega -> ActionTrace Action)
    (reward : Omega -> RewardTrace Reward)
    (haction : forall t : Nat,
      Measurable (fun omega : Omega => action omega t))
    (hreward : forall t : Nat,
      Measurable (fun omega : Omega => reward omega t))
    {i t : Nat} (hit : i < t) :
    @Measurable Omega Action
      (History.historyFiltration action reward haction hreward t)
      inferInstance
      (fun omega => action omega i) := by
  exact History.measurable_action_mem_historyFiltration_of_lt
    action reward haction hreward hit

example {Omega : Type} {Action : Type} {Reward : Type}
    [mOmega : MeasurableSpace Omega]
    [MeasurableSpace Action] [MeasurableSingletonClass Action]
    [MeasurableSpace Reward] [MeasurableSingletonClass Reward]
    [Countable Reward]
    (action : Omega -> ActionTrace Action)
    (reward : Omega -> RewardTrace Reward)
    (haction : forall t : Nat,
      Measurable (fun omega : Omega => action omega t))
    (hreward : forall t : Nat,
      Measurable (fun omega : Omega => reward omega t))
    {i t : Nat} (hit : i < t) (r : Reward) :
    @MeasurableSet Omega
      (History.historyFiltration action reward haction hreward t)
      (Set.preimage (fun omega => reward omega i) (Set.singleton r)) := by
  exact History.measurableSet_reward_mem_historyFiltration
    action reward haction hreward hit r

example {Omega : Type} {Action : Type} {Reward : Type}
    [mOmega : MeasurableSpace Omega]
    [MeasurableSpace Action] [MeasurableSingletonClass Action]
    [MeasurableSpace Reward] [MeasurableSingletonClass Reward]
    [Countable Reward]
    (action : Omega -> ActionTrace Action)
    (reward : Omega -> RewardTrace Reward)
    (haction : forall t : Nat,
      Measurable (fun omega : Omega => action omega t))
    (hreward : forall t : Nat,
      Measurable (fun omega : Omega => reward omega t))
    {i t : Nat} (hit : i < t) :
    @Measurable Omega Reward
      (History.historyFiltration action reward haction hreward t)
      inferInstance
      (fun omega => reward omega i) := by
  exact History.measurable_reward_mem_historyFiltration_of_lt
    action reward haction hreward hit

example {Omega State Action : Type}
    [MeasurableSpace Omega] [MeasurableSpace State] [MeasurableSpace Action]
    (policy : Policy.MeasurablePolicy State Action)
    (state : Omega -> State)
    (hstate : Measurable state) :
    Measurable (fun omega : Omega => policy.action (state omega)) := by
  exact Policy.measurable_action_of_measurable_state policy state hstate

example {Omega State Action : Type}
    [mOmega : MeasurableSpace Omega]
    [MeasurableSpace State] [MeasurableSpace Action]
    (F : MeasureTheory.Filtration Nat mOmega)
    (policy : Policy.MeasurablePolicy State Action)
    (state : Omega -> State)
    (t : Nat)
    (hstate :
      @Measurable Omega State
        (F t) inferInstance state) :
    @Measurable Omega Action
      (F t) inferInstance
      (fun omega : Omega => policy.action (state omega)) := by
  exact
    Policy.measurable_action_mem_filtration_of_measurable_state
      F policy state t hstate

example {Omega TraceAction Reward State PolicyAction : Type}
    [mOmega : MeasurableSpace Omega]
    [MeasurableSpace TraceAction] [MeasurableSingletonClass TraceAction]
    [MeasurableSpace Reward] [MeasurableSingletonClass Reward]
    [MeasurableSpace State] [MeasurableSpace PolicyAction]
    (traceAction : Omega -> ActionTrace TraceAction)
    (reward : Omega -> RewardTrace Reward)
    (haction : forall t : Nat,
      Measurable (fun omega : Omega => traceAction omega t))
    (hreward : forall t : Nat,
      Measurable (fun omega : Omega => reward omega t))
    (policy : Policy.MeasurablePolicy State PolicyAction)
    (state : Omega -> State)
    (t : Nat)
    (hstate :
      @Measurable Omega State
        (History.historyFiltration traceAction reward haction hreward t)
        inferInstance
        state) :
    @Measurable Omega PolicyAction
      (History.historyFiltration traceAction reward haction hreward t)
      inferInstance
      (fun omega : Omega => policy.action (state omega)) := by
  exact
    Policy.measurable_action_mem_historyFiltration_of_measurable_state
      traceAction reward haction hreward policy state t hstate

example {Omega State Action : Type}
    [MeasurableSpace Omega] [MeasurableSpace State] [MeasurableSpace Action]
    (policy : Policy.MeasurablePolicy State Action)
    (state : Nat -> Omega -> State)
    (hstate : forall t : Nat, Measurable (state t))
    (t : Nat) :
    Measurable
      (fun omega : Omega =>
        (Policy.generatedActionTrace policy state omega) t) := by
  exact
    Policy.measurable_generatedActionTrace_eval_of_measurable_state
      policy state hstate t

example {Omega State Action : Type}
    [MeasurableSpace State] [MeasurableSpace Action]
    (policy : Nat -> Policy.MeasurablePolicy State Action)
    (state : Nat -> Omega -> State)
    (defaultAction : Action)
    (t : Nat) :
    (fun omega : Omega =>
      (Policy.generatedActionTraceSucc policy state defaultAction omega)
        (t + 1)) =
    (fun omega : Omega => (policy t).action (state t omega)) := by
  exact Policy.generatedActionTraceSucc_succ_eq policy state defaultAction t

example {Omega State Action : Type}
    [MeasurableSpace Omega] [MeasurableSpace State] [MeasurableSpace Action]
    (policy : Nat -> Policy.MeasurablePolicy State Action)
    (state : Nat -> Omega -> State)
    (defaultAction : Action)
    (hstate : forall t : Nat, Measurable (state t))
    (t : Nat) :
    Measurable
      (fun omega : Omega =>
        (Policy.generatedActionTraceSucc policy state defaultAction omega) t) := by
  exact
    Policy.measurable_generatedActionTraceSucc_eval_of_measurable_state
      policy state defaultAction hstate t

example {Omega State Action : Type}
    [mOmega : MeasurableSpace Omega]
    [MeasurableSpace State] [MeasurableSpace Action]
    (F : MeasureTheory.Filtration Nat mOmega)
    (policy : Nat -> Policy.MeasurablePolicy State Action)
    (state : Nat -> Omega -> State)
    (defaultAction : Action)
    (hstate :
      forall t : Nat,
        @Measurable Omega State
          (F t) inferInstance (state t))
    (t : Nat) :
    @Measurable Omega Action
      (F t) inferInstance
      (fun omega : Omega =>
        (Policy.generatedActionTraceSucc policy state defaultAction omega)
          (t + 1)) := by
  exact
    Policy.measurable_generatedActionTraceSucc_succ_mem_filtration_of_measurable_state
      F policy state defaultAction hstate t

example {Omega State Action : Type}
    [mOmega : MeasurableSpace Omega]
    [MeasurableSpace State] [MeasurableSpace Action]
    (F : MeasureTheory.Filtration Nat mOmega)
    (policy : Policy.MeasurablePolicy State Action)
    (state : Nat -> Omega -> State)
    (hstate :
      forall t : Nat,
        @Measurable Omega State
          (F t) inferInstance (state t))
    (t : Nat) :
    @Measurable Omega Action
      (F t) inferInstance
      (fun omega : Omega =>
        (Policy.generatedActionTrace policy state omega) t) := by
  exact
    Policy.measurable_generatedActionTrace_eval_mem_filtration_of_measurable_state
      F policy state hstate t

example {Omega TraceAction Reward State PolicyAction : Type}
    [mOmega : MeasurableSpace Omega]
    [MeasurableSpace TraceAction] [MeasurableSingletonClass TraceAction]
    [MeasurableSpace Reward] [MeasurableSingletonClass Reward]
    [MeasurableSpace State] [MeasurableSpace PolicyAction]
    (traceAction : Omega -> ActionTrace TraceAction)
    (reward : Omega -> RewardTrace Reward)
    (haction : forall t : Nat,
      Measurable (fun omega : Omega => traceAction omega t))
    (hreward : forall t : Nat,
      Measurable (fun omega : Omega => reward omega t))
    (policy : Policy.MeasurablePolicy State PolicyAction)
    (state : Nat -> Omega -> State)
    (hstate :
      forall t : Nat,
        @Measurable Omega State
          (History.historyFiltration traceAction reward haction hreward t)
          inferInstance
          (state t))
    (t : Nat) :
    @Measurable Omega PolicyAction
      (History.historyFiltration traceAction reward haction hreward t)
      inferInstance
      (fun omega : Omega =>
        (Policy.generatedActionTrace policy state omega) t) := by
  exact
    Policy.measurable_generatedActionTrace_eval_mem_historyFiltration_of_measurable_state
      traceAction reward haction hreward policy state hstate t

example {Index Reward : Type}
    [MeasurableSpace Index] [MeasurableSpace Reward]
    (rewardKernel : RewardKernel.MarkovRewardKernel Index Reward)
    (index : Index) :
    MeasureTheory.IsProbabilityMeasure (rewardKernel.kernel index) := by
  exact RewardKernel.isProbabilityMeasure_apply rewardKernel index

example {Omega Index Reward : Type}
    [MeasurableSpace Omega] [MeasurableSpace Index] [MeasurableSpace Reward]
    (rewardKernel : RewardKernel.MarkovRewardKernel Index Reward)
    (index : Omega -> Index)
    (hindex : Measurable index)
    {event : Set Reward}
    (hevent : MeasurableSet event) :
    Measurable
      (fun omega : Omega => rewardKernel.kernel (index omega) event) := by
  exact
    RewardKernel.measurable_eventProbability_of_measurable_index
      rewardKernel index hindex hevent

example {Omega Context Action Reward : Type}
    [MeasurableSpace Omega]
    [MeasurableSpace Context] [MeasurableSpace Action]
    [MeasurableSpace Reward]
    (rewardKernel : RewardKernel.MarkovRewardKernel (Context × Action) Reward)
    (context : Omega -> Context)
    (action : Omega -> Action)
    (hcontext : Measurable context)
    (haction : Measurable action) :
    Measurable
      (fun omega : Omega =>
        RewardKernel.selectedMeasure rewardKernel
          (context omega) (action omega)) := by
  exact
    RewardKernel.measurable_selectedMeasure_of_measurable
      rewardKernel context action hcontext haction

example {Omega Context State Action Reward : Type}
    [MeasurableSpace Omega]
    [MeasurableSpace Context] [MeasurableSpace State]
    [MeasurableSpace Action] [MeasurableSpace Reward]
    (rewardKernel : RewardKernel.MarkovRewardKernel (Context × Action) Reward)
    (policy : Policy.MeasurablePolicy State Action)
    (context : Omega -> Context)
    (state : Omega -> State)
    (hcontext : Measurable context)
    (hstate : Measurable state)
    {event : Set Reward}
    (hevent : MeasurableSet event) :
    Measurable
      (fun omega : Omega =>
        RewardKernel.selectedMeasure rewardKernel
          (context omega) (policy.action (state omega)) event) := by
  exact
    RewardKernel.measurable_selectedEventProbability_of_policy_state
      rewardKernel policy context state hcontext hstate hevent

example {Context State Action : Type}
    [MeasurableSpace Context] [MeasurableSpace State]
    [MeasurableSpace Action]
    (policy : Policy.MeasurablePolicy State Action) :
    Measurable
      (RewardKernel.policyContextStateIndex
        (Context := Context) policy) := by
  exact RewardKernel.measurable_policyContextStateIndex policy

example {Context State Action Reward : Type}
    [MeasurableSpace Context] [MeasurableSpace State]
    [MeasurableSpace Action] [MeasurableSpace Reward]
    (rewardKernel : RewardKernel.MarkovRewardKernel (Context × Action) Reward)
    (policy : Policy.MeasurablePolicy State Action) :
    ProbabilityTheory.IsMarkovKernel
      (RewardKernel.composePolicy rewardKernel policy).kernel := by
  exact RewardKernel.isMarkovKernel_composePolicy rewardKernel policy

example {Context State Action Reward : Type}
    [MeasurableSpace Context] [MeasurableSpace State]
    [MeasurableSpace Action] [MeasurableSpace Reward]
    (rewardKernel : RewardKernel.MarkovRewardKernel (Context × Action) Reward)
    (policy : Policy.MeasurablePolicy State Action)
    (pair : Context × State) :
    (RewardKernel.composePolicy rewardKernel policy).kernel pair =
      RewardKernel.selectedMeasure rewardKernel pair.1
        (policy.action pair.2) := by
  exact RewardKernel.composePolicy_kernel_apply rewardKernel policy pair

example {Context State Action Reward : Type}
    [MeasurableSpace Context] [MeasurableSpace State]
    [MeasurableSpace Action] [MeasurableSpace Reward]
    (rewardKernel : RewardKernel.MarkovRewardKernel (Context × Action) Reward)
    (policy : Policy.MeasurablePolicy State Action)
    {event : Set Reward}
    (hevent : MeasurableSet event) :
    Measurable
      (fun pair : Context × State =>
        (RewardKernel.composePolicy rewardKernel policy).kernel pair event) := by
  exact
    RewardKernel.measurable_composePolicy_eventProbability
      rewardKernel policy hevent

example {Context State Action Reward : Type}
    [MeasurableSpace Context] [MeasurableSpace State]
    [MeasurableSpace Action] [MeasurableSpace Reward]
    (rewardKernel : RewardKernel.MarkovRewardKernel (Context × Action) Reward)
    (policy : Nat -> Policy.MeasurablePolicy State Action)
    (context : (n : Nat) -> ((i : Finset.Iic n) -> Reward) -> Context)
    (state : (n : Nat) -> ((i : Finset.Iic n) -> Reward) -> State)
    (hcontext : forall n : Nat, Measurable (context n))
    (hstate : forall n : Nat, Measurable (state n))
    (n : Nat) :
    ProbabilityTheory.IsMarkovKernel
      (RewardKernel.historyStepKernelFamily rewardKernel policy context state
        hcontext hstate n) := by
  exact
    RewardKernel.isMarkovKernel_historyStepKernelFamily
      rewardKernel policy context state hcontext hstate n

example {Context State Action Reward : Type}
    [MeasurableSpace Context] [MeasurableSpace State]
    [MeasurableSpace Action] [MeasurableSpace Reward]
    (rewardKernel : RewardKernel.MarkovRewardKernel (Context × Action) Reward)
    (policy : Nat -> Policy.MeasurablePolicy State Action)
    (context : (n : Nat) -> ((i : Finset.Iic n) -> Reward) -> Context)
    (state : (n : Nat) -> ((i : Finset.Iic n) -> Reward) -> State)
    (hcontext : forall n : Nat, Measurable (context n))
    (hstate : forall n : Nat, Measurable (state n))
    (n : Nat) (history : (i : Finset.Iic n) -> Reward) :
    RewardKernel.historyStepKernelFamily rewardKernel policy context state
        hcontext hstate n history =
      RewardKernel.selectedMeasure rewardKernel (context n history)
        ((policy n).action (state n history)) := by
  exact
    RewardKernel.historyStepKernelFamily_apply
      rewardKernel policy context state hcontext hstate n history

example {Context State Action Reward : Type}
    [MeasurableSpace Context] [MeasurableSpace State]
    [MeasurableSpace Action] [MeasurableSpace Reward]
    (rewardKernel : RewardKernel.MarkovRewardKernel (Context × Action) Reward)
    (policy : Nat -> Policy.MeasurablePolicy State Action)
    (context : (n : Nat) -> ((i : Finset.Iic n) -> Reward) -> Context)
    (state : (n : Nat) -> ((i : Finset.Iic n) -> Reward) -> State)
    (hcontext : forall n : Nat, Measurable (context n))
    (hstate : forall n : Nat, Measurable (state n))
    (n : Nat)
    {event : Set Reward}
    (hevent : MeasurableSet event) :
    Measurable
      (fun history : (i : Finset.Iic n) -> Reward =>
        RewardKernel.historyStepKernelFamily rewardKernel policy context state
          hcontext hstate n history event) := by
  exact
    RewardKernel.measurable_historyStepKernelFamily_eventProbability
      rewardKernel policy context state hcontext hstate n hevent

example {Context State Action : Type}
    [MeasurableSpace Context] [MeasurableSpace State]
    [MeasurableSpace Action]
    (rewardKernel : RewardKernel.MarkovRewardKernel (Context × Action) Rat)
    (policy : Policy.MeasurablePolicy State Action)
    (mean : Context -> Action -> Rat)
    (varianceProxy : Context -> Action -> NNReal)
    (law :
      RewardKernel.CenteredRewardKernelLaw
        rewardKernel mean varianceProxy)
    (pair : Context × State) :
    MeasureTheory.integral
      ((RewardKernel.composePolicy rewardKernel policy).kernel pair)
      (fun reward : Rat =>
        (((reward - mean pair.1 (policy.action pair.2) : Rat) : Real))) = 0 := by
  exact
    RewardKernel.composePolicy_centeredReward_integral_eq_zero
      rewardKernel policy mean varianceProxy law pair

example {Context State Action : Type}
    [MeasurableSpace Context] [MeasurableSpace State]
    [MeasurableSpace Action]
    (rewardKernel : RewardKernel.MarkovRewardKernel (Context × Action) Rat)
    (policy : Policy.MeasurablePolicy State Action)
    (mean : Context -> Action -> Rat)
    (varianceProxy : Context -> Action -> NNReal)
    (law :
      RewardKernel.CenteredRewardKernelLaw
        rewardKernel mean varianceProxy)
    (pair : Context × State) :
    ProbabilityTheory.HasSubgaussianMGF
      (fun reward : Rat =>
        (((reward - mean pair.1 (policy.action pair.2) : Rat) : Real)))
      (varianceProxy pair.1 (policy.action pair.2))
      ((RewardKernel.composePolicy rewardKernel policy).kernel pair) := by
  exact
    RewardKernel.composePolicy_centeredReward_hasSubgaussianMGF
      rewardKernel policy mean varianceProxy law pair

example {Context State Action : Type}
    [MeasurableSpace Context] [MeasurableSpace State]
    [MeasurableSpace Action]
    (rewardKernel : RewardKernel.MarkovRewardKernel (Context × Action) Rat)
    (policy : Nat -> Policy.MeasurablePolicy State Action)
    (context : (n : Nat) -> ((i : Finset.Iic n) -> Rat) -> Context)
    (state : (n : Nat) -> ((i : Finset.Iic n) -> Rat) -> State)
    (hcontext : forall n : Nat, Measurable (context n))
    (hstate : forall n : Nat, Measurable (state n))
    (mean : Context -> Action -> Rat)
    (varianceProxy : Context -> Action -> NNReal)
    (law :
      RewardKernel.CenteredRewardKernelLaw
        rewardKernel mean varianceProxy)
    (n : Nat) (history : (i : Finset.Iic n) -> Rat) :
    ProbabilityTheory.HasSubgaussianMGF
      (fun reward : Rat =>
        (((reward -
          mean (context n history) ((policy n).action (state n history)) :
            Rat) : Real)))
      (varianceProxy
        (context n history) ((policy n).action (state n history)))
      (RewardKernel.historyStepKernelFamily rewardKernel policy context state
        hcontext hstate n history) := by
  exact
    RewardKernel.historyStepKernelFamily_centeredReward_hasSubgaussianMGF
      rewardKernel policy context state hcontext hstate mean varianceProxy law
      n history

example {Context State Action Reward : Type}
    [MeasurableSpace Context] [MeasurableSpace State]
    [MeasurableSpace Action] [MeasurableSpace Reward]
    (rewardKernel : RewardKernel.MarkovRewardKernel (Context × Action) Reward)
    (policy : Nat -> Policy.MeasurablePolicy State Action)
    (context : (n : Nat) -> ((i : Finset.Iic n) -> Reward) -> Context)
    (state : (n : Nat) -> ((i : Finset.Iic n) -> Reward) -> State)
    (hcontext : forall n : Nat, Measurable (context n))
    (hstate : forall n : Nat, Measurable (state n))
    (a b : Nat) :
    ProbabilityTheory.IsMarkovKernel
      (RewardKernel.partialTrajectoryKernel rewardKernel policy context state
        hcontext hstate a b) := by
  exact
    RewardKernel.isMarkovKernel_partialTrajectoryKernel
      rewardKernel policy context state hcontext hstate a b

example {Context State Action Reward : Type}
    [MeasurableSpace Context] [MeasurableSpace State]
    [MeasurableSpace Action] [MeasurableSpace Reward]
    (rewardKernel : RewardKernel.MarkovRewardKernel (Context × Action) Reward)
    (policy : Nat -> Policy.MeasurablePolicy State Action)
    (context : (n : Nat) -> ((i : Finset.Iic n) -> Reward) -> Context)
    (state : (n : Nat) -> ((i : Finset.Iic n) -> Reward) -> State)
    (hcontext : forall n : Nat, Measurable (context n))
    (hstate : forall n : Nat, Measurable (state n))
    (a b : Nat)
    {event : Set ((i : Finset.Iic b) -> Reward)}
    (hevent : MeasurableSet event) :
    Measurable
      (fun history : (i : Finset.Iic a) -> Reward =>
        RewardKernel.partialTrajectoryKernel rewardKernel policy context state
          hcontext hstate a b history event) := by
  exact
    RewardKernel.measurable_partialTrajectoryKernel_eventProbability
      rewardKernel policy context state hcontext hstate a b hevent

example {Context State Action Reward : Type}
    [MeasurableSpace Context] [MeasurableSpace State]
    [MeasurableSpace Action] [MeasurableSpace Reward]
    (rewardKernel : RewardKernel.MarkovRewardKernel (Context × Action) Reward)
    (policy : Nat -> Policy.MeasurablePolicy State Action)
    (context : (n : Nat) -> ((i : Finset.Iic n) -> Reward) -> Context)
    (state : (n : Nat) -> ((i : Finset.Iic n) -> Reward) -> State)
    (hcontext : forall n : Nat, Measurable (context n))
    (hstate : forall n : Nat, Measurable (state n))
    (n : Nat) :
    (RewardKernel.partialTrajectoryKernel rewardKernel policy context state
        hcontext hstate n (n + 1)).map
      (fun history : (i : Finset.Iic (n + 1)) -> Reward =>
        history ⟨n + 1, Finset.mem_Iic.mpr le_rfl⟩) =
      RewardKernel.historyStepKernelFamily rewardKernel policy context state
        hcontext hstate n := by
  exact
    RewardKernel.partialTrajectoryKernel_succ_next_map
      rewardKernel policy context state hcontext hstate n

example {Context State Action Reward : Type}
    [MeasurableSpace Context] [MeasurableSpace State]
    [MeasurableSpace Action] [MeasurableSpace Reward]
    (rewardKernel : RewardKernel.MarkovRewardKernel (Context × Action) Reward)
    (policy : Nat -> Policy.MeasurablePolicy State Action)
    (context : (n : Nat) -> ((i : Finset.Iic n) -> Reward) -> Context)
    (state : (n : Nat) -> ((i : Finset.Iic n) -> Reward) -> State)
    (hcontext : forall n : Nat, Measurable (context n))
    (hstate : forall n : Nat, Measurable (state n))
    (n : Nat) (history : (i : Finset.Iic n) -> Reward) :
    MeasureTheory.Measure.map
        (fun extended : (i : Finset.Iic (n + 1)) -> Reward =>
          extended ⟨n + 1, Finset.mem_Iic.mpr le_rfl⟩)
        (RewardKernel.partialTrajectoryKernel rewardKernel policy context state
          hcontext hstate n (n + 1) history) =
      RewardKernel.historyStepKernelFamily rewardKernel policy context state
        hcontext hstate n history := by
  exact
    RewardKernel.partialTrajectoryKernel_succ_next_map_apply
      rewardKernel policy context state hcontext hstate n history

example {Context State Action : Type}
    [MeasurableSpace Context] [MeasurableSpace State]
    [MeasurableSpace Action]
    (policy : Policy.MeasurablePolicy State Action) :
    ProbabilityTheory.IsMarkovKernel
      (RewardKernel.policyActionKernel (Context := Context) policy) := by
  exact RewardKernel.isMarkovKernel_policyActionKernel policy

example {Context State Action Reward : Type}
    [MeasurableSpace Context] [MeasurableSpace State]
    [MeasurableSpace Action] [MeasurableSpace Reward]
    (rewardKernel : RewardKernel.MarkovRewardKernel (Context × Action) Reward)
    (policy : Policy.MeasurablePolicy State Action) :
    ProbabilityTheory.IsMarkovKernel
      (RewardKernel.composePolicyActionReward rewardKernel policy).kernel := by
  exact RewardKernel.isMarkovKernel_composePolicyActionReward rewardKernel policy

example {Context State Action Reward : Type}
    [MeasurableSpace Context] [MeasurableSpace State]
    [MeasurableSpace Action] [MeasurableSpace Reward]
    (rewardKernel : RewardKernel.MarkovRewardKernel (Context × Action) Reward)
    (policy : Policy.MeasurablePolicy State Action)
    {event : Set (Action × Reward)}
    (hevent : MeasurableSet event) :
    Measurable
      (fun pair : Context × State =>
        (RewardKernel.composePolicyActionReward rewardKernel policy).kernel
          pair event) := by
  exact
    RewardKernel.measurable_composePolicyActionReward_eventProbability
      rewardKernel policy hevent

example {Context State Action Reward : Type}
    [MeasurableSpace Context] [MeasurableSpace State]
    [MeasurableSpace Action] [MeasurableSpace Reward]
    (rewardKernel : RewardKernel.MarkovRewardKernel (Context × Action) Reward)
    (policy : Policy.MeasurablePolicy State Action)
    (pair : Context × State)
    {event : Set Reward}
    (hevent : MeasurableSet event) :
    (RewardKernel.composePolicyActionReward rewardKernel policy).kernel pair
        (Prod.snd ⁻¹' event) =
      RewardKernel.selectedMeasure rewardKernel pair.1
        (policy.action pair.2) event := by
  exact
    RewardKernel.composePolicyActionReward_reward_event
      rewardKernel policy pair hevent

example {Context State Action Reward : Type}
    [MeasurableSpace Context] [MeasurableSpace State]
    [MeasurableSpace Action] [MeasurableSpace Reward]
    (rewardKernel : RewardKernel.MarkovRewardKernel (Context × Action) Reward)
    (policy : Policy.MeasurablePolicy State Action)
    (pair : Context × State) :
    MeasureTheory.Measure.map Prod.snd
        ((RewardKernel.composePolicyActionReward rewardKernel policy).kernel
          pair) =
      RewardKernel.selectedMeasure rewardKernel pair.1
        (policy.action pair.2) := by
  exact
    RewardKernel.composePolicyActionReward_reward_map
      rewardKernel policy pair

example {Context State Action Reward : Type}
    [MeasurableSpace Context] [MeasurableSpace State]
    [MeasurableSpace Action] [MeasurableSpace Reward]
    (rewardKernel : RewardKernel.MarkovRewardKernel (Context × Action) Reward)
    (policy : Nat -> Policy.MeasurablePolicy State Action)
    (context :
      (n : Nat) -> ((i : Finset.Iic n) -> Action × Reward) -> Context)
    (state :
      (n : Nat) -> ((i : Finset.Iic n) -> Action × Reward) -> State)
    (hcontext : forall n : Nat, Measurable (context n))
    (hstate : forall n : Nat, Measurable (state n))
    (n : Nat) :
    ProbabilityTheory.IsMarkovKernel
      (RewardKernel.actionRewardHistoryStepKernelFamily rewardKernel policy
        context state hcontext hstate n) := by
  exact
    RewardKernel.isMarkovKernel_actionRewardHistoryStepKernelFamily
      rewardKernel policy context state hcontext hstate n

example {Context State Action Reward : Type}
    [MeasurableSpace Context] [MeasurableSpace State]
    [MeasurableSpace Action] [MeasurableSpace Reward]
    (rewardKernel : RewardKernel.MarkovRewardKernel (Context × Action) Reward)
    (policy : Nat -> Policy.MeasurablePolicy State Action)
    (context :
      (n : Nat) -> ((i : Finset.Iic n) -> Action × Reward) -> Context)
    (state :
      (n : Nat) -> ((i : Finset.Iic n) -> Action × Reward) -> State)
    (hcontext : forall n : Nat, Measurable (context n))
    (hstate : forall n : Nat, Measurable (state n))
    (n : Nat) (history : (i : Finset.Iic n) -> Action × Reward) :
    RewardKernel.actionRewardHistoryStepKernelFamily rewardKernel policy
        context state hcontext hstate n history =
      (RewardKernel.composePolicyActionReward rewardKernel (policy n)).kernel
        (context n history, state n history) := by
  exact
    RewardKernel.actionRewardHistoryStepKernelFamily_apply
      rewardKernel policy context state hcontext hstate n history

example {Context State Action Reward : Type}
    [MeasurableSpace Context] [MeasurableSpace State]
    [MeasurableSpace Action] [MeasurableSpace Reward]
    (rewardKernel : RewardKernel.MarkovRewardKernel (Context × Action) Reward)
    (policy : Nat -> Policy.MeasurablePolicy State Action)
    (context :
      (n : Nat) -> ((i : Finset.Iic n) -> Action × Reward) -> Context)
    (state :
      (n : Nat) -> ((i : Finset.Iic n) -> Action × Reward) -> State)
    (hcontext : forall n : Nat, Measurable (context n))
    (hstate : forall n : Nat, Measurable (state n))
    (n : Nat)
    {event : Set (Action × Reward)}
    (hevent : MeasurableSet event) :
    Measurable
      (fun history : (i : Finset.Iic n) -> Action × Reward =>
        RewardKernel.actionRewardHistoryStepKernelFamily rewardKernel policy
          context state hcontext hstate n history event) := by
  exact
    RewardKernel.measurable_actionRewardHistoryStepKernelFamily_eventProbability
      rewardKernel policy context state hcontext hstate n hevent

example {Context State Action Reward : Type}
    [MeasurableSpace Context] [MeasurableSpace State]
    [MeasurableSpace Action] [MeasurableSpace Reward]
    (rewardKernel : RewardKernel.MarkovRewardKernel (Context × Action) Reward)
    (policy : Nat -> Policy.MeasurablePolicy State Action)
    (context :
      (n : Nat) -> ((i : Finset.Iic n) -> Action × Reward) -> Context)
    (state :
      (n : Nat) -> ((i : Finset.Iic n) -> Action × Reward) -> State)
    (hcontext : forall n : Nat, Measurable (context n))
    (hstate : forall n : Nat, Measurable (state n))
    (n : Nat) (history : (i : Finset.Iic n) -> Action × Reward)
    {event : Set Reward}
    (hevent : MeasurableSet event) :
    RewardKernel.actionRewardHistoryStepKernelFamily rewardKernel policy
        context state hcontext hstate n history (Prod.snd ⁻¹' event) =
      RewardKernel.selectedMeasure rewardKernel
        (context n history) ((policy n).action (state n history)) event := by
  exact
    RewardKernel.actionRewardHistoryStepKernelFamily_reward_event
      rewardKernel policy context state hcontext hstate n history hevent

example {Context State Action Reward : Type}
    [MeasurableSpace Context] [MeasurableSpace State]
    [MeasurableSpace Action] [MeasurableSpace Reward]
    (rewardKernel : RewardKernel.MarkovRewardKernel (Context × Action) Reward)
    (policy : Nat -> Policy.MeasurablePolicy State Action)
    (context :
      (n : Nat) -> ((i : Finset.Iic n) -> Action × Reward) -> Context)
    (state :
      (n : Nat) -> ((i : Finset.Iic n) -> Action × Reward) -> State)
    (hcontext : forall n : Nat, Measurable (context n))
    (hstate : forall n : Nat, Measurable (state n))
    (n : Nat) (history : (i : Finset.Iic n) -> Action × Reward) :
    MeasureTheory.Measure.map Prod.snd
        (RewardKernel.actionRewardHistoryStepKernelFamily rewardKernel policy
          context state hcontext hstate n history) =
      RewardKernel.selectedMeasure rewardKernel
        (context n history) ((policy n).action (state n history)) := by
  exact
    RewardKernel.actionRewardHistoryStepKernelFamily_reward_map
      rewardKernel policy context state hcontext hstate n history

example {Context State Action Reward : Type}
    [MeasurableSpace Context] [MeasurableSpace State]
    [MeasurableSpace Action] [MeasurableSpace Reward]
    (rewardKernel : RewardKernel.MarkovRewardKernel (Context × Action) Reward)
    (policy : Nat -> Policy.MeasurablePolicy State Action)
    (context :
      (n : Nat) -> ((i : Finset.Iic n) -> Action × Reward) -> Context)
    (state :
      (n : Nat) -> ((i : Finset.Iic n) -> Action × Reward) -> State)
    (hcontext : forall n : Nat, Measurable (context n))
    (hstate : forall n : Nat, Measurable (state n))
    (n : Nat) (history : (i : Finset.Iic n) -> Action × Reward) :
    RewardKernel.actionRewardHistoryStepKernelFamily rewardKernel policy
        context state hcontext hstate n history =
      MeasureTheory.Measure.map
        (Prod.mk ((policy n).action (state n history)))
        (RewardKernel.selectedMeasure rewardKernel
          (context n history) ((policy n).action (state n history))) := by
  exact
    RewardKernel.actionRewardHistoryStepKernelFamily_apply_eq_map_prod_mk
      rewardKernel policy context state hcontext hstate n history

example {Context State Action Reward : Type}
    [MeasurableSpace Context] [MeasurableSpace State]
    [MeasurableSpace Action] [MeasurableSpace Reward]
    (rewardKernel : RewardKernel.MarkovRewardKernel (Context × Action) Reward)
    (policy : Nat -> Policy.MeasurablePolicy State Action)
    (context :
      (n : Nat) -> ((i : Finset.Iic n) -> Action × Reward) -> Context)
    (state :
      (n : Nat) -> ((i : Finset.Iic n) -> Action × Reward) -> State)
    (hcontext : forall n : Nat, Measurable (context n))
    (hstate : forall n : Nat, Measurable (state n))
    (a b : Nat) :
    ProbabilityTheory.IsMarkovKernel
      (RewardKernel.actionRewardPartialTrajectoryKernel rewardKernel policy
        context state hcontext hstate a b) := by
  exact
    RewardKernel.isMarkovKernel_actionRewardPartialTrajectoryKernel
      rewardKernel policy context state hcontext hstate a b

example {Context State Action Reward : Type}
    [MeasurableSpace Context] [MeasurableSpace State]
    [MeasurableSpace Action] [MeasurableSpace Reward]
    (rewardKernel : RewardKernel.MarkovRewardKernel (Context × Action) Reward)
    (policy : Nat -> Policy.MeasurablePolicy State Action)
    (context :
      (n : Nat) -> ((i : Finset.Iic n) -> Action × Reward) -> Context)
    (state :
      (n : Nat) -> ((i : Finset.Iic n) -> Action × Reward) -> State)
    (hcontext : forall n : Nat, Measurable (context n))
    (hstate : forall n : Nat, Measurable (state n))
    (a b : Nat)
    {event : Set ((i : Finset.Iic b) -> Action × Reward)}
    (hevent : MeasurableSet event) :
    Measurable
      (fun history : (i : Finset.Iic a) -> Action × Reward =>
        RewardKernel.actionRewardPartialTrajectoryKernel rewardKernel policy
          context state hcontext hstate a b history event) := by
  exact
    RewardKernel.measurable_actionRewardPartialTrajectoryKernel_eventProbability
      rewardKernel policy context state hcontext hstate a b hevent

example {Context State Action Reward : Type}
    [MeasurableSpace Context] [MeasurableSpace State]
    [MeasurableSpace Action] [MeasurableSpace Reward]
    (rewardKernel : RewardKernel.MarkovRewardKernel (Context × Action) Reward)
    (policy : Nat -> Policy.MeasurablePolicy State Action)
    (context :
      (n : Nat) -> ((i : Finset.Iic n) -> Action × Reward) -> Context)
    (state :
      (n : Nat) -> ((i : Finset.Iic n) -> Action × Reward) -> State)
    (hcontext : forall n : Nat, Measurable (context n))
    (hstate : forall n : Nat, Measurable (state n))
    (n : Nat) :
    (RewardKernel.actionRewardPartialTrajectoryKernel rewardKernel policy
        context state hcontext hstate n (n + 1)).map
      (fun history : (i : Finset.Iic (n + 1)) -> Action × Reward =>
        history ⟨n + 1, Finset.mem_Iic.mpr le_rfl⟩) =
      RewardKernel.actionRewardHistoryStepKernelFamily rewardKernel policy
        context state hcontext hstate n := by
  exact
    RewardKernel.actionRewardPartialTrajectoryKernel_succ_next_map
      rewardKernel policy context state hcontext hstate n

example {Context State Action Reward : Type}
    [MeasurableSpace Context] [MeasurableSpace State]
    [MeasurableSpace Action] [MeasurableSpace Reward]
    (rewardKernel : RewardKernel.MarkovRewardKernel (Context × Action) Reward)
    (policy : Nat -> Policy.MeasurablePolicy State Action)
    (context :
      (n : Nat) -> ((i : Finset.Iic n) -> Action × Reward) -> Context)
    (state :
      (n : Nat) -> ((i : Finset.Iic n) -> Action × Reward) -> State)
    (hcontext : forall n : Nat, Measurable (context n))
    (hstate : forall n : Nat, Measurable (state n))
    (n : Nat) (history : (i : Finset.Iic n) -> Action × Reward) :
    MeasureTheory.Measure.map
        (fun extended : (i : Finset.Iic (n + 1)) -> Action × Reward =>
          extended ⟨n + 1, Finset.mem_Iic.mpr le_rfl⟩)
        (RewardKernel.actionRewardPartialTrajectoryKernel rewardKernel policy
          context state hcontext hstate n (n + 1) history) =
      RewardKernel.actionRewardHistoryStepKernelFamily rewardKernel policy
        context state hcontext hstate n history := by
  exact
    RewardKernel.actionRewardPartialTrajectoryKernel_succ_next_map_apply
      rewardKernel policy context state hcontext hstate n history

example {Context State Action Reward : Type}
    [MeasurableSpace Context] [MeasurableSpace State]
    [MeasurableSpace Action] [MeasurableSpace Reward]
    (rewardKernel : RewardKernel.MarkovRewardKernel (Context × Action) Reward)
    (policy : Nat -> Policy.MeasurablePolicy State Action)
    (context :
      (n : Nat) -> ((i : Finset.Iic n) -> Action × Reward) -> Context)
    (state :
      (n : Nat) -> ((i : Finset.Iic n) -> Action × Reward) -> State)
    (hcontext : forall n : Nat, Measurable (context n))
    (hstate : forall n : Nat, Measurable (state n))
    (n : Nat) (history : (i : Finset.Iic n) -> Action × Reward) :
    RewardKernel.actionRewardPartialTrajectoryKernel rewardKernel policy
        context state hcontext hstate n (n + 1) history =
      MeasureTheory.Measure.map
        (fun next : Action × Reward =>
          History.extendPairHistorySucc history next)
        (RewardKernel.actionRewardHistoryStepKernelFamily rewardKernel policy
          context state hcontext hstate n history) := by
  exact
    RewardKernel.actionRewardPartialTrajectoryKernel_succ_extend_map_apply
      rewardKernel policy context state hcontext hstate n history

example {Omega : Type} {K : Nat}
    [MeasurableSpace Omega]
    [MeasurableSpace (Fin K)] [MeasurableSingletonClass (Fin K)]
    (model : FiniteBanditModel K)
    (commitArm : Omega -> Fin K)
    (hmeas_commit : Measurable commitArm) :
    MeasurableSet {omega : Omega | commitArm omega = model.bestArm -> False} := by
  exact ETC.measurableSet_commitArm_ne_bestArm model commitArm hmeas_commit

example {Omega : Type} {K : Nat}
    [MeasurableSpace Omega]
    [MeasurableSpace (Fin K)]
    [MeasurableSpace (Fin K -> Rat)]
    [MeasurableSingletonClass (Fin K -> Rat)]
    [Countable (Fin K -> Rat)]
    (oracle : ETC.CommitOracle K)
    (empMean : Omega -> Fin K -> Rat)
    (hmeas_emp :
      Measurable (fun omega : Omega => (empMean omega : Fin K -> Rat))) :
    Measurable (fun omega : Omega => oracle.choose (empMean omega)) := by
  exact ETC.measurable_commitOracle_choose_of_measurable_empMeanVector
    oracle empMean hmeas_emp

example {Omega : Type} {K : Nat}
    [MeasurableSpace Omega]
    [MeasurableSpace Rat]
    [MeasurableSpace (Fin K)]
    [MeasurableSingletonClass (Fin K -> Rat)]
    [Countable (Fin K -> Rat)]
    (oracle : ETC.CommitOracle K)
    (empMean : Omega -> Fin K -> Rat)
    (hmeas_coord :
      forall a : Fin K, Measurable (fun omega : Omega => empMean omega a)) :
    Measurable (fun omega : Omega => oracle.choose (empMean omega)) := by
  exact ETC.measurable_commitOracle_choose_of_forall_measurable_empMean
    oracle empMean hmeas_coord

example {Omega : Type} {K : Nat}
    [MeasurableSpace Omega]
    [MeasurableSpace (Fin K)] [MeasurableSingletonClass (Fin K)]
    (model : FiniteBanditModel K)
    (oracle : ETC.CommitOracle K)
    (empMean : Omega -> Fin K -> Rat)
    (hmeas_choose :
      Measurable (fun omega : Omega => oracle.choose (empMean omega))) :
    MeasurableSet
      {omega : Omega |
        oracle.choose (empMean omega) = model.bestArm -> False} := by
  exact ETC.measurableSet_commitOracle_ne_bestArm
    model oracle empMean hmeas_choose

example {Omega : Type} {K : Nat}
    [MeasurableSpace Omega]
    [MeasurableSpace Rat]
    [MeasurableSpace (Fin K)]
    [MeasurableSingletonClass (Fin K)]
    [MeasurableSingletonClass (Fin K -> Rat)]
    [Countable (Fin K -> Rat)]
    (model : FiniteBanditModel K)
    (oracle : ETC.CommitOracle K)
    (empMean : Omega -> Fin K -> Rat)
    (hmeas_coord :
      forall a : Fin K, Measurable (fun omega : Omega => empMean omega a)) :
    MeasurableSet
      {omega : Omega |
        oracle.choose (empMean omega) = model.bestArm -> False} := by
  exact ETC.measurableSet_commitOracle_ne_bestArm_of_forall_measurable_empMean
    model oracle empMean hmeas_coord

example {Omega : Type} {K : Nat}
    [MeasurableSpace Omega]
    (empMean : Omega -> Fin K -> Rat)
    (hmeas_empMean :
      forall a : Fin K, Measurable (fun omega : Omega => empMean omega a))
    (a b : Fin K) :
    MeasurableSet {omega : Omega | empMean omega a >= empMean omega b} := by
  exact ETC.measurableSet_empMean_ge_empMean
    empMean hmeas_empMean a b

example {Omega : Type} {K : Nat}
    [MeasurableSpace Omega]
    (model : FiniteBanditModel K)
    (empMean : Omega -> Fin K -> Rat)
    (hmeas_empMean :
      forall a : Fin K, Measurable (fun omega : Omega => empMean omega a)) :
    MeasurableSet {omega : Omega |
      exists a : Fin K, (a = model.bestArm -> False) /\
        empMean omega a >= empMean omega model.bestArm} := by
  exact ETC.measurableSet_exists_ne_bestArm_empMean_ge_bestArm
    model empMean hmeas_empMean

example {Omega : Type} {K : Nat}
    (model : FiniteBanditModel K)
    (commitArm : Omega -> Fin K)
    (empMean : Omega -> Fin K -> Rat)
    (hcommit_argmax :
      forall omega : Omega, forall a : Fin K,
        empMean omega a <= empMean omega (commitArm omega)) :
    Set.Subset
      {omega : Omega | commitArm omega = model.bestArm -> False}
      {omega : Omega |
        exists a : Fin K, (a = model.bestArm -> False) /\
          empMean omega a >= empMean omega model.bestArm} := by
  exact ETC.wrong_commit_subset_exists_empMean_ge_bestArm
    model commitArm empMean hcommit_argmax

example {Omega : Type} {K : Nat}
    (model : FiniteBanditModel K)
    (oracle : ETC.CommitOracle K)
    (empMean : Omega -> Fin K -> Rat)
    (hchoose_argmax :
      forall scores : Fin K -> Rat, forall a : Fin K,
        scores a <= scores (oracle.choose scores)) :
    Set.Subset
      {omega : Omega |
        oracle.choose (empMean omega) = model.bestArm -> False}
      {omega : Omega |
        exists a : Fin K, (a = model.bestArm -> False) /\
          empMean omega a >= empMean omega model.bestArm} := by
  exact ETC.wrong_commit_subset_exists_empMean_ge_bestArm_of_commitOracle
    model oracle empMean hchoose_argmax

example {K : Nat}
    (hK : 0 < K)
    (scores : Fin K -> Rat)
    (a : Fin K) :
    scores a <= scores ((ETC.argmaxCommitOracle hK).choose scores) := by
  exact ETC.argmaxCommitOracle_choose_spec hK scores a

example {Omega : Type} {K : Nat}
    (hK : 0 < K)
    (model : FiniteBanditModel K)
    (empMean : Omega -> Fin K -> Rat) :
    Set.Subset
      {omega : Omega |
        (ETC.argmaxCommitOracle hK).choose (empMean omega) =
          model.bestArm -> False}
      {omega : Omega |
        exists a : Fin K, (a = model.bestArm -> False) /\
          empMean omega a >= empMean omega model.bestArm} := by
  exact ETC.wrong_commit_subset_exists_empMean_ge_bestArm_of_argmaxOracle
    hK model empMean

example {Omega : Type} {K : Nat}
    [MeasurableSpace Omega]
    (hK : 0 < K)
    (mu : MeasureTheory.Measure Omega)
    (model : FiniteBanditModel K)
    (empMean : Omega -> Fin K -> Rat)
    (tail : Fin K -> ENNReal)
    (hpair_tail :
      forall a : Fin K, (a = model.bestArm -> False) ->
        mu {omega : Omega |
          empMean omega a >= empMean omega model.bestArm} <= tail a) :
    mu {omega : Omega |
        (ETC.argmaxCommitOracle hK).choose (empMean omega) =
          model.bestArm -> False} <=
    ((Finset.univ : Finset (Fin K)).filter
      (fun a : Fin K => a = model.bestArm -> False)).sum tail := by
  exact ETC.prob_argmaxCommitOracle_ne_bestArm_le_filtered_sum_pairwise_tail
    hK mu model empMean tail hpair_tail

example {Omega : Type} {K : Nat}
    [MeasurableSpace Omega]
    (hK : 0 < K)
    (mu : MeasureTheory.Measure Omega)
    (spec : ETC.Spec K)
    (model : FiniteBanditModel K)
    (commitArm : Fin K)
    (reward : Omega -> RewardTrace Rat)
    (tail : Fin K -> ENNReal)
    (hcontract :
      ETC.PairwiseEmpMeanTailContract
        mu spec model commitArm reward tail) :
    mu {omega : Omega |
        (ETC.argmaxCommitOracle hK).choose
          (fun a : Fin K =>
            ETC.empMeanAtExploration spec commitArm (reward omega) a) =
          model.bestArm -> False} <=
    ((Finset.univ : Finset (Fin K)).filter
      (fun a : Fin K => a = model.bestArm -> False)).sum tail := by
  exact
    ETC.prob_argmaxCommitOracle_ne_bestArm_le_filtered_sum_pairwise_tail_of_contract
      hK mu spec model commitArm reward tail hcontract

example {Omega : Type} {K : Nat}
    [MeasurableSpace Omega]
    (mu : MeasureTheory.Measure Omega)
    (model : FiniteBanditModel K)
    (commitArm : Omega -> Fin K)
    (empMean : Omega -> Fin K -> Rat)
    (hcommit_argmax :
      forall omega : Omega, forall a : Fin K,
        empMean omega a <= empMean omega (commitArm omega)) :
    mu {omega : Omega | commitArm omega = model.bestArm -> False} <=
    mu {omega : Omega |
      exists a : Fin K, (a = model.bestArm -> False) /\
        empMean omega a >= empMean omega model.bestArm} := by
  exact ETC.prob_commitArm_ne_bestArm_le_wrong_mean_events_of_subset
    mu model commitArm empMean hcommit_argmax

example {Omega : Type} {K : Nat}
    [MeasurableSpace Omega]
    (mu : MeasureTheory.Measure Omega)
    (model : FiniteBanditModel K)
    (empMean : Omega -> Fin K -> Rat) :
    mu {omega : Omega |
      exists a : Fin K, (a = model.bestArm -> False) /\
        empMean omega a >= empMean omega model.bestArm} <=
    (Finset.univ : Finset (Fin K)).sum
      (fun a : Fin K =>
        mu {omega : Omega | (a = model.bestArm -> False) /\
          empMean omega a >= empMean omega model.bestArm}) := by
  exact ETC.prob_exists_ne_bestArm_empMean_ge_bestArm_le_sum
    mu model empMean

example {Omega : Type u}
    [MeasurableSpace Omega]
    {Idx : Type v}
    (mu : MeasureTheory.Measure Omega)
    (s : Finset Idx)
    (E : Idx -> Set Omega) :
    mu (⋃ i ∈ s, E i) <=
      s.sum (fun i => mu (E i)) := by
  exact ProbabilityUnionBound.measure_biUnion_finset_le
    mu s E

example {Omega : Type u}
    [MeasurableSpace Omega]
    {Idx : Type v} [Fintype Idx]
    (mu : MeasureTheory.Measure Omega)
    (E : Idx -> Set Omega) :
    mu (⋃ i, E i) <=
      (Finset.univ : Finset Idx).sum (fun i => mu (E i)) := by
  exact ProbabilityUnionBound.measure_iUnion_fintype_le_sum
    mu E

example {Omega : Type u}
    [MeasurableSpace Omega]
    {Arm : Type v} [Fintype Arm]
    (mu : MeasureTheory.Measure Omega)
    (bad : Arm -> Nat -> Set Omega)
    (T : Nat) :
    mu (UCBSummability.finiteHorizonBadEvent bad T) <=
      (Finset.univ : Finset Arm).sum
        (fun a => (Finset.range T).sum (fun t => mu (bad a t))) := by
  exact UCBSummability.measure_finiteHorizonBadEvent_le_sum
    mu bad T

example {Omega : Type u}
    [MeasurableSpace Omega]
    {Arm : Type v} [Fintype Arm]
    (mu : MeasureTheory.Measure Omega)
    (bad : Arm -> Nat -> Set Omega)
    (tail : Arm -> Nat -> ENNReal)
    (T : Nat)
    (htail : forall a t, t < T -> mu (bad a t) <= tail a t) :
    mu (UCBSummability.finiteHorizonBadEvent bad T) <=
      (Finset.univ : Finset Arm).sum
        (fun a => (Finset.range T).sum (fun t => tail a t)) := by
  exact UCBSummability.measure_finiteHorizonBadEvent_le_tail_sum
    mu bad tail T htail

example {History : Type u} {Env : Type v}
    [MeasurableSpace History] [MeasurableSpace Env]
    (posteriorKernel : ProbabilityTheory.Kernel History Env)
    (hposteriorKernel :
      ProbabilityTheory.IsMarkovKernel posteriorKernel) :
    ProbabilityTheory.IsMarkovKernel
      (PosteriorKernel.ofKernel posteriorKernel hposteriorKernel).kernel := by
  infer_instance

example {History : Type u} {Env : Type v}
    [MeasurableSpace History] [MeasurableSpace Env]
    [Countable History] [MeasurableSingletonClass History]
    (posterior : History -> MeasureTheory.Measure Env)
    (hprob : forall history,
      MeasureTheory.IsProbabilityMeasure (posterior history))
    (history : History) :
    (PosteriorKernel.ofCountableHistorySelector posterior hprob).kernel
        history =
      posterior history := by
  simp

example {Omega : Type u} {History : Type u} {Env : Type v}
    [MeasurableSpace Omega]
    [MeasurableSpace History] [MeasurableSpace Env]
    (posterior : PosteriorKernel.MarkovPosteriorKernel History Env)
    (history : Omega -> History)
    (hhistory : Measurable history)
    {event : Set Env}
    (hevent : MeasurableSet event) :
    Measurable
      (fun omega : Omega => posterior.kernel (history omega) event) := by
  exact PosteriorKernel.measurable_eventProbability_of_measurable_history
    posterior history hhistory hevent

example {Omega : Type u}
    [MeasurableSpace Omega]
    {Idx : Type v}
    (mu : MeasureTheory.Measure Omega)
    (s : Finset Idx)
    (X : Idx -> Omega -> Real)
    (hX : forall i, i ∈ s -> MeasureTheory.Integrable (X i) mu) :
    MeasureTheory.Integrable
      (fun omega : Omega => s.sum (fun i => X i omega)) mu := by
  exact IntegrabilitySums.integrable_finset_sum
    mu s X hX

example {Omega : Type u}
    [MeasurableSpace Omega]
    {Idx : Type v} [Fintype Idx]
    (mu : MeasureTheory.Measure Omega)
    (X : Idx -> Omega -> Real)
    (hX : forall i : Idx, MeasureTheory.Integrable (X i) mu) :
    MeasureTheory.Integrable
      (fun omega : Omega =>
        (Finset.univ : Finset Idx).sum (fun i => X i omega))
      mu := by
  exact IntegrabilitySums.integrable_univ_sum
    mu X hX

example {Omega : Type u}
    [MeasurableSpace Omega]
    {Idx : Type v}
    (mu : MeasureTheory.Measure Omega)
    (s : Finset Idx)
    (X : Idx -> Omega -> Real)
    (hX : forall i, i ∈ s -> MeasureTheory.Integrable (X i) mu) :
    MeasureTheory.integral mu
      (fun omega : Omega => s.sum (fun i => X i omega)) =
    s.sum (fun i => MeasureTheory.integral mu (X i)) := by
  exact ExpectationBochnerSums.integral_finset_sum
    mu s X hX

example {Omega : Type u}
    [MeasurableSpace Omega]
    {Idx : Type v} [Fintype Idx]
    (mu : MeasureTheory.Measure Omega)
    (X : Idx -> Omega -> Real)
    (hX : forall i : Idx, MeasureTheory.Integrable (X i) mu) :
    MeasureTheory.integral mu
      (fun omega : Omega =>
        (Finset.univ : Finset Idx).sum (fun i => X i omega)) =
    (Finset.univ : Finset Idx).sum
      (fun i => MeasureTheory.integral mu (X i)) := by
  exact ExpectationBochnerSums.integral_univ_sum
    mu X hX

example {Omega : Type} {K : Nat}
    [MeasurableSpace Omega]
    (mu : MeasureTheory.Measure Omega)
    (model : FiniteBanditModel K)
    (action : Omega -> ActionTrace (Fin K))
    (n : Nat)
    (hcount : forall a : Fin K,
      MeasureTheory.Integrable
        (fun omega : Omega =>
          ((pullCount (action omega) a n : Nat) : Real)) mu) :
    MeasureTheory.Integrable
      (fun omega : Omega =>
        ((pseudoRegret model (action omega) n : Rat) : Real)) mu := by
  exact
    integrable_real_pseudoRegret_of_integrable_pullCount
      mu model action n hcount

example {Omega : Type} {K : Nat}
    [MeasurableSpace Omega]
    (mu : MeasureTheory.Measure Omega)
    (model : FiniteBanditModel K)
    (action : Omega -> ActionTrace (Fin K))
    (n : Nat)
    (hcount : forall a : Fin K,
      MeasureTheory.Integrable
        (fun omega : Omega =>
          ((pullCount (action omega) a n : Nat) : Real)) mu) :
    MeasureTheory.integral mu
      (fun omega : Omega =>
        ((pseudoRegret model (action omega) n : Rat) : Real))
      =
    (Finset.univ : Finset (Fin K)).sum
      (fun a : Fin K =>
        ((model.gap a : Rat) : Real) *
          MeasureTheory.integral mu
            (fun omega : Omega =>
              ((pullCount (action omega) a n : Nat) : Real))) := by
  exact
    integral_real_pseudoRegret_eq_sum_gap_mul_integral_pullCount
      mu model action n hcount

example {Omega : Type} {K : Nat}
    [MeasurableSpace Omega]
    (mu : MeasureTheory.Measure Omega)
    (model : FiniteBanditModel K)
    (commitArm : Omega -> Fin K)
    (empMean : Omega -> Fin K -> Rat)
    (hcommit_argmax :
      forall omega : Omega, forall a : Fin K,
        empMean omega a <= empMean omega (commitArm omega)) :
    mu {omega : Omega | commitArm omega = model.bestArm -> False} <=
    (Finset.univ : Finset (Fin K)).sum
      (fun a : Fin K =>
        mu {omega : Omega | (a = model.bestArm -> False) /\
          empMean omega a >= empMean omega model.bestArm}) := by
  exact ETC.prob_commitArm_ne_bestArm_le_sum_wrong_mean_events
    mu model commitArm empMean hcommit_argmax

example {Omega : Type} {K : Nat}
    [MeasurableSpace Omega]
    (mu : MeasureTheory.Measure Omega)
    (model : FiniteBanditModel K)
    (commitArm : Omega -> Fin K)
    (empMean : Omega -> Fin K -> Rat)
    (tail : Fin K -> ENNReal)
    (hcommit_argmax :
      forall omega : Omega, forall a : Fin K,
        empMean omega a <= empMean omega (commitArm omega))
    (hpair_tail :
      forall a : Fin K, (a = model.bestArm -> False) ->
        mu {omega : Omega |
          empMean omega a >= empMean omega model.bestArm} <= tail a) :
    mu {omega : Omega | commitArm omega = model.bestArm -> False} <=
    (Finset.univ : Finset (Fin K)).sum tail := by
  exact ETC.prob_commitArm_ne_bestArm_le_sum_pairwise_tail
    mu model commitArm empMean tail hcommit_argmax hpair_tail

example {Omega : Type} {K : Nat}
    [MeasurableSpace Omega]
    (mu : MeasureTheory.Measure Omega)
    (model : FiniteBanditModel K)
    (oracle : ETC.CommitOracle K)
    (empMean : Omega -> Fin K -> Rat)
    (tail : Fin K -> ENNReal)
    (hchoose_argmax :
      forall scores : Fin K -> Rat, forall a : Fin K,
        scores a <= scores (oracle.choose scores))
    (hpair_tail :
      forall a : Fin K, (a = model.bestArm -> False) ->
        mu {omega : Omega |
          empMean omega a >= empMean omega model.bestArm} <= tail a) :
    mu {omega : Omega |
        oracle.choose (empMean omega) = model.bestArm -> False} <=
    (Finset.univ : Finset (Fin K)).sum tail := by
  exact ETC.prob_commitOracle_ne_bestArm_le_sum_pairwise_tail
    mu model oracle empMean tail hchoose_argmax hpair_tail

example {Omega : Type} {K : Nat}
    [MeasurableSpace Omega]
    (mu : MeasureTheory.Measure Omega)
    (model : FiniteBanditModel K)
    (commitArm : Omega -> Fin K)
    (empMean : Omega -> Fin K -> Rat)
    (tail : Fin K -> ENNReal)
    (hcommit_argmax :
      forall omega : Omega, forall a : Fin K,
        empMean omega a <= empMean omega (commitArm omega))
    (hpair_tail :
      forall a : Fin K, (a = model.bestArm -> False) ->
        mu {omega : Omega |
          empMean omega a >= empMean omega model.bestArm} <= tail a) :
    mu {omega : Omega | commitArm omega = model.bestArm -> False} <=
    (Finset.univ : Finset (Fin K)).sum
      (fun a : Fin K => if a = model.bestArm then 0 else tail a) := by
  exact ETC.prob_commitArm_ne_bestArm_le_sum_nonbest_pairwise_tail
    mu model commitArm empMean tail hcommit_argmax hpair_tail

example {Omega : Type} {K : Nat}
    [MeasurableSpace Omega]
    (mu : MeasureTheory.Measure Omega)
    (model : FiniteBanditModel K)
    (commitArm : Omega -> Fin K)
    (empMean : Omega -> Fin K -> Rat)
    (tail : Fin K -> ENNReal)
    (hcommit_argmax :
      forall omega : Omega, forall a : Fin K,
        empMean omega a <= empMean omega (commitArm omega))
    (hpair_tail :
      forall a : Fin K, (a = model.bestArm -> False) ->
        mu {omega : Omega |
          empMean omega a >= empMean omega model.bestArm} <= tail a) :
    mu {omega : Omega | commitArm omega = model.bestArm -> False} <=
    ((Finset.univ : Finset (Fin K)).filter
      (fun a : Fin K => a = model.bestArm -> False)).sum tail := by
  exact ETC.prob_commitArm_ne_bestArm_le_filtered_sum_pairwise_tail
    mu model commitArm empMean tail hcommit_argmax hpair_tail

example {Omega : Type} {K : Nat}
    [MeasurableSpace Omega]
    (mu : MeasureTheory.Measure Omega)
    (model : FiniteBanditModel K)
    (oracle : ETC.CommitOracle K)
    (empMean : Omega -> Fin K -> Rat)
    (tail : Fin K -> ENNReal)
    (hchoose_argmax :
      forall scores : Fin K -> Rat, forall a : Fin K,
        scores a <= scores (oracle.choose scores))
    (hpair_tail :
      forall a : Fin K, (a = model.bestArm -> False) ->
        mu {omega : Omega |
          empMean omega a >= empMean omega model.bestArm} <= tail a) :
    mu {omega : Omega |
        oracle.choose (empMean omega) = model.bestArm -> False} <=
    ((Finset.univ : Finset (Fin K)).filter
      (fun a : Fin K => a = model.bestArm -> False)).sum tail := by
  exact ETC.prob_commitOracle_ne_bestArm_le_filtered_sum_pairwise_tail
    mu model oracle empMean tail hchoose_argmax hpair_tail

example {Omega : Type} {K : Nat}
    [MeasurableSpace Omega]
    (mu : MeasureTheory.Measure Omega)
    (model : FiniteBanditModel K)
    (oracle : ETC.CommitOracle K)
    (empMean : Omega -> Fin K -> Rat)
    (tail : Fin K -> ENNReal)
    (hchoose_argmax :
      forall scores : Fin K -> Rat, forall a : Fin K,
        scores a <= scores (oracle.choose scores))
    (hpair_tail :
      forall a : Fin K, (a = model.bestArm -> False) ->
        mu {omega : Omega |
          empMean omega a >= empMean omega model.bestArm} <= tail a) :
    mu {omega : Omega |
        oracle.choose (empMean omega) = model.bestArm -> False} <=
    (Finset.univ : Finset (Fin K)).sum
      (fun a : Fin K => if a = model.bestArm then 0 else tail a) := by
  exact ETC.prob_commitOracle_ne_bestArm_le_sum_nonbest_pairwise_tail
    mu model oracle empMean tail hchoose_argmax hpair_tail

example {Omega : Type} {Action : Type} {Beta : Type}
    [MeasurableSpace Omega] [MeasurableSpace Action]
    [MeasurableSingletonClass Action]
    [MeasurableSpace Beta] [Zero Beta]
    (action : Omega -> ActionTrace Action)
    (hmeas : forall t : Nat, Measurable (fun omega : Omega => action omega t))
    (a : Action) (t : Nat) (c : Beta) :
    Measurable
      (({omega : Omega | action omega t = a} : Set Omega).indicator
        (fun _ : Omega => c)) := by
  exact measurable_actionTrace_eval_eq_indicator_const action hmeas a t c

example {Omega : Type} {Action : Type} {Reward : Type}
    [MeasurableSpace Omega] [MeasurableSpace Action]
    [MeasurableSingletonClass Action]
    [MeasurableSpace Reward] [Zero Reward]
    (action : Omega -> ActionTrace Action)
    (reward : Omega -> RewardTrace Reward)
    (haction : forall t : Nat, Measurable (fun omega : Omega => action omega t))
    (hreward : forall t : Nat, Measurable (fun omega : Omega => reward omega t))
    (a : Action) (t : Nat) :
    Measurable
      (({omega : Omega | action omega t = a} : Set Omega).indicator
        (fun omega : Omega => reward omega t)) := by
  exact measurable_actionTrace_eval_eq_indicator_reward
    action reward haction hreward a t

example {Omega : Type} {Action : Type} {Reward : Type}
    [MeasurableSpace Omega] [MeasurableSpace Action]
    [MeasurableSingletonClass Action]
    [MeasurableSpace Reward] [AddCommMonoid Reward] [MeasurableAdd₂ Reward]
    (action : Omega -> ActionTrace Action)
    (reward : Omega -> RewardTrace Reward)
    (haction : forall t : Nat, Measurable (fun omega : Omega => action omega t))
    (hreward : forall t : Nat, Measurable (fun omega : Omega => reward omega t))
    (a : Action) (s : Finset Nat) :
    Measurable
      (fun omega : Omega =>
        s.sum
          (fun t : Nat =>
            (({omega' : Omega | action omega' t = a} : Set Omega).indicator
              (fun omega' : Omega => reward omega' t)) omega)) := by
  exact measurable_finset_sum_indicator_reward
    action reward haction hreward a s

example {Omega : Type} {Action : Type} {Reward : Type}
    [MeasurableSpace Omega] [MeasurableSpace Action]
    [MeasurableSingletonClass Action]
    [MeasurableSpace Reward] [AddCommMonoid Reward] [MeasurableAdd₂ Reward]
    [DecidableEq Action]
    (action : Omega -> ActionTrace Action)
    (reward : Omega -> RewardTrace Reward)
    (haction : forall t : Nat, Measurable (fun omega : Omega => action omega t))
    (hreward : forall t : Nat, Measurable (fun omega : Omega => reward omega t))
    (a : Action) (n : Nat) :
    Measurable
      (fun omega : Omega => sumRewards (action omega) (reward omega) a n) := by
  exact measurable_sumRewards action reward haction hreward a n

example {Omega : Type}
    [MeasurableSpace Omega]
    [MeasurableSpace (Fin K)] [MeasurableSingletonClass (Fin K)]
    [MeasurableSpace Rat] [MeasurableAdd₂ Rat]
    (model : FiniteBanditModel K)
    (action : Omega -> ActionTrace (Fin K))
    (haction : forall t : Nat,
      Measurable (fun omega : Omega => action omega t))
    (n : Nat) :
    Measurable
      (fun omega : Omega => pseudoRegret model (action omega) n) := by
  exact measurable_pseudoRegret model action haction n

example {Omega : Type} {Action : Type}
    [MeasurableSpace Omega] [MeasurableSpace Action]
    [MeasurableSingletonClass Action]
    [MeasurableSpace Nat] [MeasurableAdd₂ Nat]
    [DecidableEq Action]
    (action : Omega -> ActionTrace Action)
    (haction : forall t : Nat,
      Measurable (fun omega : Omega => action omega t))
    (a : Action) (n : Nat) :
    Measurable
      (fun omega : Omega => pullCount (action omega) a n) := by
  exact measurable_pullCount action haction a n

example {Omega : Type} {Action : Type} {Beta : Type}
    [MeasurableSpace Omega] [MeasurableSpace Action]
    [MeasurableSingletonClass Action]
    [MeasurableSpace Beta] [AddCommMonoidWithOne Beta] [MeasurableAdd₂ Beta]
    [DecidableEq Action]
    (action : Omega -> ActionTrace Action)
    (haction : forall t : Nat,
      Measurable (fun omega : Omega => action omega t))
    (a : Action) (n : Nat) :
    Measurable
      (fun omega : Omega =>
        ((pullCount (action omega) a n : Nat) : Beta)) := by
  exact measurable_natCast_pullCount action haction a n

example {Omega : Type} {Action : Type}
    [MeasurableSpace Omega] [MeasurableSpace Action]
    [MeasurableSingletonClass Action]
    (mu : MeasureTheory.Measure Omega)
    (action : Omega -> ActionTrace Action)
    (haction : forall t : Nat,
      Measurable (fun omega : Omega => action omega t))
    (a : Action) (t : Nat) :
    MeasureTheory.lintegral mu
      (fun omega : Omega =>
        (({omega' : Omega | action omega' t = a} : Set Omega).indicator
          (1 : Omega -> ENNReal)) omega)
      =
    mu {omega : Omega | action omega t = a} := by
  exact lintegral_actionTrace_eval_eq_indicator_one mu action haction a t

example {Omega : Type} {Action : Type}
    [MeasurableSpace Omega] [MeasurableSpace Action]
    [MeasurableSingletonClass Action]
    (mu : MeasureTheory.Measure Omega)
    (action : Omega -> ActionTrace Action)
    (haction : forall t : Nat,
      Measurable (fun omega : Omega => action omega t))
    (a : Action) (s : Finset Nat) :
    MeasureTheory.lintegral mu
      (fun omega : Omega =>
        s.sum
          (fun t : Nat =>
            (({omega' : Omega | action omega' t = a} : Set Omega).indicator
              (1 : Omega -> ENNReal)) omega))
      =
    s.sum
      (fun t : Nat =>
        mu {omega : Omega | action omega t = a}) := by
  exact lintegral_finset_sum_actionTrace_eval_eq_indicator_one
    mu action haction a s

example {Omega : Type} {Action : Type}
    [MeasurableSpace Omega] [MeasurableSpace Action]
    [MeasurableSingletonClass Action] [DecidableEq Action]
    (mu : MeasureTheory.Measure Omega)
    (action : Omega -> ActionTrace Action)
    (haction : forall t : Nat,
      Measurable (fun omega : Omega => action omega t))
    (a : Action) (n : Nat) :
    MeasureTheory.lintegral mu
      (fun omega : Omega =>
        ((pullCount (action omega) a n : Nat) : ENNReal))
      =
    (Finset.range n).sum
      (fun t : Nat =>
        mu {omega : Omega | action omega t = a}) := by
  exact lintegral_natCast_pullCount_eq_sum_measure_actionTrace_eval_eq
    mu action haction a n

example {Omega : Type} {Action : Type}
    [MeasurableSpace Omega] [MeasurableSpace Action]
    [MeasurableSingletonClass Action] [DecidableEq Action]
    (mu : MeasureTheory.Measure Omega)
    (action : Omega -> ActionTrace Action)
    (haction : forall t : Nat,
      Measurable (fun omega : Omega => action omega t))
    (gap : Action -> ENNReal) (arms : Finset Action) (n : Nat) :
    MeasureTheory.lintegral mu
      (fun omega : Omega =>
        arms.sum
          (fun a : Action =>
            gap a *
              ((pullCount (action omega) a n : Nat) : ENNReal)))
      =
    arms.sum
      (fun a : Action =>
        gap a *
          (Finset.range n).sum
            (fun t : Nat =>
              mu {omega : Omega | action omega t = a})) := by
  exact lintegral_finset_sum_gap_mul_natCast_pullCount_eq
    mu action haction gap arms n

example {Omega : Type} {Action : Type}
    [MeasurableSpace Omega] [MeasurableSpace Action]
    [MeasurableSingletonClass Action] [DecidableEq Action]
    (mu : MeasureTheory.Measure Omega)
    [MeasureTheory.IsProbabilityMeasure mu]
    (action : Omega -> ActionTrace Action)
    (haction : forall t : Nat,
      Measurable (fun omega : Omega => action omega t))
    (a : Action) (n : Nat) :
    MeasureTheory.lintegral mu
      (fun omega : Omega =>
        ((pullCount (action omega) a n : Nat) : ENNReal))
      <= (n : ENNReal) := by
  exact lintegral_natCast_pullCount_le_time
    mu action haction a n

example {Omega : Type} {Action : Type}
    [MeasurableSpace Omega] [MeasurableSpace Action]
    [MeasurableSingletonClass Action] [DecidableEq Action]
    (mu : MeasureTheory.Measure Omega)
    [MeasureTheory.IsProbabilityMeasure mu]
    (action : Omega -> ActionTrace Action)
    (haction : forall t : Nat,
      Measurable (fun omega : Omega => action omega t))
    (gap : Action -> ENNReal) (arms : Finset Action) (n : Nat) :
    MeasureTheory.lintegral mu
      (fun omega : Omega =>
        arms.sum
          (fun a : Action =>
            gap a *
              ((pullCount (action omega) a n : Nat) : ENNReal)))
      <=
    arms.sum
      (fun a : Action =>
        gap a * (n : ENNReal)) := by
  exact
    lintegral_finset_sum_gap_mul_natCast_pullCount_le_sum_gap_mul_time
      mu action haction gap arms n

example {Omega : Type} {K : Nat}
    [MeasurableSpace Omega]
    [MeasurableSpace (Fin K)] [MeasurableSingletonClass (Fin K)]
    (mu : MeasureTheory.Measure Omega)
    [MeasureTheory.IsProbabilityMeasure mu]
    (action : Omega -> ActionTrace (Fin K))
    (haction : forall t : Nat,
      Measurable (fun omega : Omega => action omega t))
    (gap : Fin K -> ENNReal) (n : Nat) :
    MeasureTheory.lintegral mu
      (fun omega : Omega =>
        (Finset.univ : Finset (Fin K)).sum
          (fun a : Fin K =>
            gap a *
              ((pullCount (action omega) a n : Nat) : ENNReal)))
      <=
    (Finset.univ : Finset (Fin K)).sum
      (fun a : Fin K =>
        gap a * (n : ENNReal)) := by
  exact
    lintegral_univ_sum_gap_mul_natCast_pullCount_le_sum_gap_mul_time
      mu action haction gap n

example {Omega : Type} {K : Nat}
    [MeasurableSpace Omega]
    [MeasurableSpace (Fin K)] [MeasurableSingletonClass (Fin K)]
    (mu : MeasureTheory.Measure Omega)
    [MeasureTheory.IsProbabilityMeasure mu]
    (model : FiniteBanditModel K)
    (action : Omega -> ActionTrace (Fin K))
    (haction : forall t : Nat,
      Measurable (fun omega : Omega => action omega t))
    (n : Nat) :
    MeasureTheory.lintegral mu
      (fun omega : Omega =>
        (Finset.univ : Finset (Fin K)).sum
          (fun a : Fin K =>
            ENNReal.ofReal (((model.gap a : Rat) : Real)) *
              ((pullCount (action omega) a n : Nat) : ENNReal)))
      <=
    (Finset.univ : Finset (Fin K)).sum
      (fun a : Fin K =>
        ENNReal.ofReal (((model.gap a : Rat) : Real)) *
          (n : ENNReal)) := by
  exact
    lintegral_univ_sum_model_gap_ofReal_mul_natCast_pullCount_le_sum_model_gap_ofReal_mul_time
      mu model action haction n

example {Omega : Type} {K : Nat}
    [MeasurableSpace Omega]
    [MeasurableSpace (Fin K)] [MeasurableSingletonClass (Fin K)]
    (mu : MeasureTheory.Measure Omega)
    [MeasureTheory.IsProbabilityMeasure mu]
    (model : FiniteBanditModel K)
    (action : Omega -> ActionTrace (Fin K))
    (haction : forall t : Nat,
      Measurable (fun omega : Omega => action omega t))
    (hgap : forall a : Fin K,
      0 <= (((model.gap a : Rat) : Real)))
    (n : Nat) :
    MeasureTheory.lintegral mu
      (fun omega : Omega =>
        ENNReal.ofReal
          (((pseudoRegret model (action omega) n : Rat) : Real)))
      <=
    (Finset.univ : Finset (Fin K)).sum
      (fun a : Fin K =>
        ENNReal.ofReal (((model.gap a : Rat) : Real)) *
          (n : ENNReal)) := by
  exact
    lintegral_ofReal_pseudoRegret_le_sum_model_gap_ofReal_mul_time_of_nonneg
      mu model action haction hgap n

example {Omega : Type} {K : Nat}
    [MeasurableSpace Omega]
    [MeasurableSpace (Fin K)] [MeasurableSingletonClass (Fin K)]
    (mu : MeasureTheory.Measure Omega)
    [MeasureTheory.IsProbabilityMeasure mu]
    (model : FiniteBanditModel K)
    (action : Omega -> ActionTrace (Fin K))
    (haction : forall t : Nat,
      Measurable (fun omega : Omega => action omega t))
    (hgap : forall a : Fin K,
      (0 : Rat) <= model.gap a)
    (n : Nat) :
    MeasureTheory.lintegral mu
      (fun omega : Omega =>
        ENNReal.ofReal
          (((pseudoRegret model (action omega) n : Rat) : Real)))
      <=
    (Finset.univ : Finset (Fin K)).sum
      (fun a : Fin K =>
        ENNReal.ofReal (((model.gap a : Rat) : Real)) *
          (n : ENNReal)) := by
  exact
    lintegral_ofReal_pseudoRegret_le_sum_model_gap_ofReal_mul_time_of_rat_gap_nonneg
      mu model action haction hgap n

example {Omega : Type} {K : Nat}
    [MeasurableSpace Omega]
    [MeasurableSpace (Fin K)] [MeasurableSingletonClass (Fin K)]
    (mu : MeasureTheory.Measure Omega)
    [MeasureTheory.IsProbabilityMeasure mu]
    (model : FiniteBanditModel K)
    (action : Omega -> ActionTrace (Fin K))
    (haction : forall t : Nat,
      Measurable (fun omega : Omega => action omega t))
    (n : Nat) :
    MeasureTheory.lintegral mu
      (fun omega : Omega =>
        ENNReal.ofReal
          (((pseudoRegret model (action omega) n : Rat) : Real)))
      <=
    (Finset.univ : Finset (Fin K)).sum
      (fun a : Fin K =>
        ENNReal.ofReal (((model.gap a : Rat) : Real)) *
          (n : ENNReal)) := by
  exact
    lintegral_ofReal_pseudoRegret_le_sum_model_gap_ofReal_mul_time
      mu model action haction n

example {Omega : Type} [MeasurableSpace Omega]
    (mu : MeasureTheory.Measure Omega) [MeasureTheory.IsProbabilityMeasure mu]
    {X : Omega -> Real} {lo hi mean : Real}
    (hmeas : AEMeasurable X mu)
    (hbound : Filter.Eventually
      (fun omega : Omega => Set.Icc lo hi (X omega)) (MeasureTheory.ae mu))
    (hmean : MeasureTheory.integral mu X = mean) :
    ProbabilityTheory.HasSubgaussianMGF
      (fun omega : Omega => X omega - mean)
      (Concentration.intervalVarianceProxy lo hi) mu := by
  exact
    Concentration.boundedCentered_hasSubgaussianMGF_of_mem_Icc_integral_eq
      mu hmeas hbound hmean

example
    {Idx : Type} {Omega : Idx -> Type} {Target : Idx -> Type}
    [forall i, MeasurableSpace (Omega i)]
    [forall i, MeasurableSpace (Target i)]
    (coordLaw : forall i, MeasureTheory.Measure (Omega i))
    [forall i, MeasureTheory.IsProbabilityMeasure (coordLaw i)]
    (X : forall i, Omega i -> Target i)
    (hX : forall i, Measurable (X i)) :
    ProbabilityTheory.iIndepFun
      (fun i omega => X i (omega i))
      (MeasureTheory.Measure.infinitePi coordLaw) := by
  exact
    IndependenceFoundation.iIndepFun_infinitePi_coord
      coordLaw X hX

example {Reward : Type} [MeasurableSpace Reward]
    (coordLaw : Nat -> MeasureTheory.Measure Reward)
    [forall t : Nat, MeasureTheory.IsProbabilityMeasure (coordLaw t)] :
    ProbabilityTheory.iIndepFun
      (fun t (omega : RewardTrace Reward) => omega t)
      (MeasureTheory.Measure.infinitePi coordLaw) := by
  exact
    IndependenceFoundation.iIndepFun_rewardTrace_infinitePi coordLaw

example {Omega : Type} [MeasurableSpace Omega]
    (mu : MeasureTheory.Measure Omega) [MeasureTheory.IsFiniteMeasure mu]
    {X : Omega -> Real}
    (hX : MeasureTheory.MemLp X 2 mu)
    {eps : Real} (heps : 0 < eps) :
    mu {omega | eps <= |X omega - MeasureTheory.integral mu X|} <=
      ENNReal.ofReal (ProbabilityTheory.variance X mu / eps ^ 2) := by
  exact Concentration.variance_chebyshev_tail mu hX heps

example {Omega : Type} [MeasurableSpace Omega]
    (mu : MeasureTheory.Measure Omega) [MeasureTheory.IsFiniteMeasure mu]
    {Idx : Type} {X : Idx -> Omega -> Real} {s : Finset Idx}
    (h_mem :
      forall i : Idx, Membership.mem s i -> MeasureTheory.MemLp (X i) 2 mu)
    (h_pairwise :
      Set.Pairwise ((s : Finset Idx) : Set Idx)
        (fun i j => ProbabilityTheory.IndepFun (X i) (X j) mu)) :
    ProbabilityTheory.variance (Finset.sum s X) mu =
      Finset.sum s (fun i => ProbabilityTheory.variance (X i) mu) := by
  exact Concentration.variance_sum_of_pairwise_indep
    mu h_mem h_pairwise

example {Omega : Type} [mOmega : MeasurableSpace Omega]
    {F : MeasureTheory.Filtration Nat mOmega}
    {spent : Nat -> Omega -> Nat}
    (budget : Nat)
    (hspent : MeasureTheory.Adapted F spent) :
    MeasureTheory.IsStoppingTime F
      (Budget.budgetExhaustionTime spent budget) := by
  exact Budget.isStoppingTime_budgetExhaustionTime_of_adapted
    budget hspent

example {Omega : Type} [mOmega : MeasurableSpace Omega]
    {F : MeasureTheory.Filtration Nat mOmega}
    {spent : Nat -> Omega -> Nat}
    (budget n : Nat)
    (hspent : MeasureTheory.Adapted F spent) :
    @MeasurableSet Omega (F n)
      {omega | Budget.budgetExhaustionTime spent budget omega <= n} := by
  exact Budget.measurableSet_budgetExhaustionTime_le_of_adapted
    budget n hspent

example {Omega : Type} [MeasurableSpace Omega]
    (mu : MeasureTheory.Measure Omega)
    {Idx : Type} {X : Idx -> Omega -> Real}
    (h_indep : ProbabilityTheory.iIndepFun X mu)
    {c : Idx -> NNReal} {s : Finset Idx}
    (h_subG :
      forall i, i ∈ s ->
        ProbabilityTheory.HasSubgaussianMGF (X i) (c i) mu)
    {eps : Real} (heps : 0 <= eps) :
    mu.real {omega | eps <= s.sum (fun i => X i omega)} <=
      Real.exp (-eps ^ 2 / (2 * ((s.sum c : NNReal) : Real))) := by
  exact Concentration.subGaussian_sum_tail_of_iIndepFun
    mu h_indep h_subG heps

example {Omega : Type} [MeasurableSpace Omega]
    (mu : MeasureTheory.Measure Omega) [MeasureTheory.IsFiniteMeasure mu]
    {Idx : Type} {X : Idx -> Omega -> Real}
    (h_indep : ProbabilityTheory.iIndepFun X mu)
    {c : Idx -> NNReal} {s : Finset Idx}
    (h_subG :
      forall i, i ∈ s ->
        ProbabilityTheory.HasSubgaussianMGF (X i) (c i) mu)
    {eps : Real} (heps : 0 <= eps) :
    mu {omega | eps <= s.sum (fun i => X i omega)} <=
      ENNReal.ofReal
        (Real.exp (-eps ^ 2 / (2 * ((s.sum c : NNReal) : Real)))) := by
  exact Concentration.subGaussian_sum_tail_ennreal_of_iIndepFun
    mu h_indep h_subG heps

example {Omega : Type} [mOmega : MeasurableSpace Omega]
    [StandardBorelSpace Omega]
    {mu : MeasureTheory.Measure Omega}
    [MeasureTheory.IsZeroOrProbabilityMeasure mu]
    {Y : Nat -> Omega -> Real} {cY : Nat -> NNReal}
    {F : MeasureTheory.Filtration Nat mOmega}
    (h_adapted : MeasureTheory.StronglyAdapted F Y)
    (h0 : ProbabilityTheory.HasSubgaussianMGF (Y 0) (cY 0) mu)
    (n : Nat)
    (h_subG :
      forall i, i < n - 1 ->
        ProbabilityTheory.HasCondSubgaussianMGF
          (F i) (F.le i) (Y (i + 1)) (cY (i + 1)) mu)
    {eps : Real} (heps : 0 <= eps) :
    mu.real {omega | eps <= (Finset.range n).sum (fun i => Y i omega)} <=
      Real.exp (-eps ^ 2 / (2 * (((Finset.range n).sum cY : NNReal) : Real))) := by
  exact Concentration.condSubGaussian_sum_tail_of_stronglyAdapted
    h_adapted h0 n h_subG heps

example {Omega : Type} [mOmega : MeasurableSpace Omega]
    [StandardBorelSpace Omega]
    {mu : MeasureTheory.Measure Omega}
    [MeasureTheory.IsFiniteMeasure mu] [MeasureTheory.IsZeroOrProbabilityMeasure mu]
    {Y : Nat -> Omega -> Real} {cY : Nat -> NNReal}
    {F : MeasureTheory.Filtration Nat mOmega}
    (h_adapted : MeasureTheory.StronglyAdapted F Y)
    (h0 : ProbabilityTheory.HasSubgaussianMGF (Y 0) (cY 0) mu)
    (n : Nat)
    (h_subG :
      forall i, i < n - 1 ->
        ProbabilityTheory.HasCondSubgaussianMGF
          (F i) (F.le i) (Y (i + 1)) (cY (i + 1)) mu)
    {eps : Real} (heps : 0 <= eps) :
    mu {omega | eps <= (Finset.range n).sum (fun i => Y i omega)} <=
      ENNReal.ofReal
        (Real.exp (-eps ^ 2 / (2 * (((Finset.range n).sum cY : NNReal) : Real)))) := by
  exact Concentration.condSubGaussian_sum_tail_ennreal_of_stronglyAdapted
    h_adapted h0 n h_subG heps

example {Omega : Type} {K : Nat}
    [MeasurableSpace Omega]
    (mu : MeasureTheory.Measure Omega) [MeasureTheory.IsFiniteMeasure mu]
    (spec : ETC.Spec K)
    (model : FiniteBanditModel K)
    (commitArm : Fin K)
    (reward : Omega -> RewardTrace Rat)
    (tail : Fin K -> ENNReal)
    {Idx : Type}
    (idx : Finset Idx)
    (X : Fin K -> Idx -> Omega -> Real)
    (c : Fin K -> Idx -> NNReal)
    (eps : Fin K -> Real)
    (h_indep :
      forall a : Fin K, (a = model.bestArm -> False) ->
        ProbabilityTheory.iIndepFun (X a) mu)
    (h_subG :
      forall a : Fin K, (a = model.bestArm -> False) ->
        forall i, i ∈ idx ->
          ProbabilityTheory.HasSubgaussianMGF ((X a) i) ((c a) i) mu)
    (heps :
      forall a : Fin K, (a = model.bestArm -> False) ->
        0 <= eps a)
    (hsubset :
      forall a : Fin K, (a = model.bestArm -> False) ->
        Set.Subset
          {omega : Omega |
            ETC.empMeanAtExploration spec commitArm (reward omega) a >=
              ETC.empMeanAtExploration spec commitArm
                (reward omega) model.bestArm}
          {omega : Omega | eps a <= idx.sum (fun i => X a i omega)})
    (htail :
      forall a : Fin K, (a = model.bestArm -> False) ->
        ENNReal.ofReal
          (Real.exp
            (-(eps a) ^ 2 /
              (2 * ((idx.sum (c a) : NNReal) : Real)))) <= tail a) :
    ETC.PairwiseEmpMeanTailContract
      mu spec model commitArm reward tail := by
  exact ETC.pairwiseEmpMeanTailContract_of_subGaussian_event_bounds
    mu spec model commitArm reward tail idx X c eps
    h_indep h_subG heps hsubset htail

example {Omega : Type} {K : Nat}
    [MeasurableSpace Omega]
    (mu : MeasureTheory.Measure Omega) [MeasureTheory.IsFiniteMeasure mu]
    (spec : ETC.Spec K)
    (model : FiniteBanditModel K)
    (commitArm : Fin K)
    (reward : Omega -> RewardTrace Rat)
    (tail : Fin K -> ENNReal)
    (c : Fin K -> Nat -> NNReal)
    (hexplorationPulls_pos : 0 < spec.explorationPulls)
    (h_indep :
      forall a : Fin K, (a = model.bestArm -> False) ->
        ProbabilityTheory.iIndepFun
          (fun t omega =>
            ETC.centeredPairwiseRewardDiff
              spec model commitArm reward a t omega)
          mu)
    (h_subG :
      forall a : Fin K, (a = model.bestArm -> False) ->
        forall t, t ∈ Finset.range (spec.explorationPulls * K) ->
          ProbabilityTheory.HasSubgaussianMGF
            (fun omega =>
              ETC.centeredPairwiseRewardDiff
                spec model commitArm reward a t omega)
            (c a t) mu)
    (htail :
      forall a : Fin K, (a = model.bestArm -> False) ->
        ENNReal.ofReal
          (Real.exp
            (-(ETC.centeredPairwiseGapThreshold spec model a) ^ 2 /
              (2 *
                (((Finset.range (spec.explorationPulls * K)).sum
                  (fun t => c a t) : NNReal) : Real)))) <= tail a) :
    ETC.PairwiseEmpMeanTailContract
      mu spec model commitArm reward tail := by
  exact
    ETC.pairwiseEmpMeanTailContract_of_centered_subGaussian_event_bounds
      mu spec model commitArm reward tail c hexplorationPulls_pos
      h_indep h_subG htail

example {Omega : Type} {K : Nat}
    [MeasurableSpace Omega]
    (mu : MeasureTheory.Measure Omega) [MeasureTheory.IsFiniteMeasure mu]
    (spec : ETC.Spec K)
    (model : FiniteBanditModel K)
    (commitArm : Fin K)
    (reward : Omega -> RewardTrace Rat)
    (tail : Fin K -> ENNReal)
    (hexplorationPulls_pos : 0 < spec.explorationPulls)
    (w :
      ETC.CenteredDiffSubGaussianWitnesses
        mu spec model commitArm reward tail) :
    ETC.PairwiseEmpMeanTailContract
      mu spec model commitArm reward tail := by
  exact
    ETC.pairwiseEmpMeanTailContract_of_centeredDiffSubGaussianWitnesses
      mu spec model commitArm reward tail hexplorationPulls_pos w

example {Omega : Type} {K : Nat}
    [mOmega : MeasurableSpace Omega] [StandardBorelSpace Omega]
    (mu : MeasureTheory.Measure Omega)
    [MeasureTheory.IsFiniteMeasure mu]
    [MeasureTheory.IsZeroOrProbabilityMeasure mu]
    (spec : ETC.Spec K)
    (model : FiniteBanditModel K)
    (commitArm : Fin K)
    (reward : Omega -> RewardTrace Rat)
    (tail : Fin K -> ENNReal)
    (hexplorationPulls_pos : 0 < spec.explorationPulls)
    (w :
      ETC.CenteredDiffCondSubGaussianWitnesses
        mu spec model commitArm reward tail) :
    ETC.PairwiseEmpMeanTailContract
      mu spec model commitArm reward tail := by
  exact
    ETC.pairwiseEmpMeanTailContract_of_centeredDiffCondSubGaussianWitnesses
      mu spec model commitArm reward tail hexplorationPulls_pos w

example {Omega : Type} {K : Nat}
    [mOmega : MeasurableSpace Omega]
    (spec : ETC.Spec K)
    (model : FiniteBanditModel K)
    (commitArm : Fin K)
    (reward : Omega -> RewardTrace Rat)
    (hreward : forall t : Nat,
      Measurable (fun omega : Omega => reward omega t))
    (a : Fin K) (t : Nat) :
    @Measurable Omega Real
      (History.historyFiltrationSucc
        (fun _omega : Omega => ETC.actionWithCommit spec commitArm)
        reward
        (fun _t : Nat => measurable_const)
        hreward t)
      inferInstance
      (fun omega =>
        ETC.centeredPairwiseRewardDiff
          spec model commitArm reward a t omega) := by
  exact
    ETC.measurable_centeredPairwiseRewardDiff_historyFiltrationSucc
      spec model commitArm reward hreward a t

example {Omega : Type} {K : Nat}
    [mOmega : MeasurableSpace Omega]
    (spec : ETC.Spec K)
    (model : FiniteBanditModel K)
    (commitArm : Fin K)
    (reward : Omega -> RewardTrace Rat)
    (hreward : forall t : Nat,
      Measurable (fun omega : Omega => reward omega t))
    (a : Fin K) :
    MeasureTheory.StronglyAdapted
      (History.historyFiltrationSucc
        (fun _omega : Omega => ETC.actionWithCommit spec commitArm)
        reward
        (fun _t : Nat => measurable_const)
        hreward)
      (fun t omega =>
        ETC.centeredPairwiseRewardDiff
          spec model commitArm reward a t omega) := by
  exact
    ETC.stronglyAdapted_centeredPairwiseRewardDiff_historyFiltrationSucc
      spec model commitArm reward hreward a

example {Omega : Type} {K : Nat}
    [MeasurableSpace Omega]
    (mu : MeasureTheory.Measure Omega)
    [MeasureTheory.IsZeroOrProbabilityMeasure mu]
    (spec : ETC.Spec K)
    (model : FiniteBanditModel K)
    (commitArm : Fin K)
    (reward : Omega -> RewardTrace Rat)
    (a : Fin K) (t : Nat)
    (h_ne_a : ETC.actionWithCommit spec commitArm t ≠ a)
    (h_ne_best :
      ETC.actionWithCommit spec commitArm t ≠ model.bestArm) :
    ProbabilityTheory.HasSubgaussianMGF
      (fun omega =>
        ETC.centeredPairwiseRewardDiff
          spec model commitArm reward a t omega)
      0 mu := by
  exact
    ETC.centeredPairwiseRewardDiff_hasSubgaussianMGF_of_action_miss
      mu spec model commitArm reward a t h_ne_a h_ne_best

example {Omega : Type} {K : Nat}
    [mOmega : MeasurableSpace Omega] [StandardBorelSpace Omega]
    (mu : MeasureTheory.Measure Omega)
    [MeasureTheory.IsFiniteMeasure mu]
    (m : MeasurableSpace Omega) (hm : m ≤ mOmega)
    (spec : ETC.Spec K)
    (model : FiniteBanditModel K)
    (commitArm : Fin K)
    (reward : Omega -> RewardTrace Rat)
    (a : Fin K) (t : Nat)
    (h_ne_a : ETC.actionWithCommit spec commitArm t ≠ a)
    (h_ne_best :
      ETC.actionWithCommit spec commitArm t ≠ model.bestArm) :
    ProbabilityTheory.HasCondSubgaussianMGF
      m hm
      (fun omega =>
        ETC.centeredPairwiseRewardDiff
          spec model commitArm reward a t omega)
      0 mu := by
  exact
    ETC.centeredPairwiseRewardDiff_hasCondSubgaussianMGF_of_action_miss
      (mOmega := mOmega) (mu := mu) (m := m) (hm := hm)
      spec model commitArm reward a t h_ne_a h_ne_best

example {Omega : Type} {K : Nat}
    [mOmega : MeasurableSpace Omega] [StandardBorelSpace Omega]
    (mu : MeasureTheory.Measure Omega)
    [MeasureTheory.IsFiniteMeasure mu]
    (spec : ETC.Spec K)
    (model : FiniteBanditModel K)
    (commitArm : Fin K)
    (reward : Omega -> RewardTrace Rat)
    (hreward : forall t : Nat,
      Measurable (fun omega : Omega => reward omega t))
    (a : Fin K) (t : Nat)
    (h_ne_a : ETC.actionWithCommit spec commitArm t ≠ a)
    (h_ne_best :
      ETC.actionWithCommit spec commitArm t ≠ model.bestArm) :
    ProbabilityTheory.HasCondSubgaussianMGF
      (History.historyFiltrationSucc
        (fun _omega : Omega => ETC.actionWithCommit spec commitArm)
        reward
        (fun _t : Nat => measurable_const)
        hreward t)
      ((History.historyFiltrationSucc
        (fun _omega : Omega => ETC.actionWithCommit spec commitArm)
        reward
        (fun _t : Nat => measurable_const)
        hreward).le t)
      (fun omega =>
        ETC.centeredPairwiseRewardDiff
          spec model commitArm reward a t omega)
      0 mu := by
  exact
    ETC.centeredPairwiseRewardDiff_hasCondSubgaussianMGF_historyFiltrationSucc_of_action_miss
      mu spec model commitArm reward hreward a t h_ne_a h_ne_best

example {Omega : Type} {K : Nat}
    [mOmega : MeasurableSpace Omega] [StandardBorelSpace Omega]
    (mu : MeasureTheory.Measure Omega)
    [MeasureTheory.IsFiniteMeasure mu]
    (m : MeasurableSpace Omega) (hm : m ≤ mOmega)
    (spec : ETC.Spec K)
    (model : FiniteBanditModel K)
    (commitArm : Fin K)
    (reward : Omega -> RewardTrace Rat)
    (a : Fin K) (t : Nat) (c : NNReal)
    (hne : a = model.bestArm -> False)
    (h_action : ETC.actionWithCommit spec commitArm t = a)
    (h_subG :
      ProbabilityTheory.HasCondSubgaussianMGF
        m hm
        (fun omega : Omega =>
          (((reward omega t - model.mean a : Rat) : Real)))
        c mu) :
    ProbabilityTheory.HasCondSubgaussianMGF
      m hm
      (fun omega =>
        ETC.centeredPairwiseRewardDiff
          spec model commitArm reward a t omega)
      c mu := by
  exact
    ETC.centeredPairwiseRewardDiff_hasCondSubgaussianMGF_of_action_eq_arm
      (mOmega := mOmega) (mu := mu) (m := m) (hm := hm)
      spec model commitArm reward a t c hne h_action h_subG

example {Omega : Type} {K : Nat}
    [mOmega : MeasurableSpace Omega] [StandardBorelSpace Omega]
    (mu : MeasureTheory.Measure Omega)
    [MeasureTheory.IsFiniteMeasure mu]
    (m : MeasurableSpace Omega) (hm : m ≤ mOmega)
    (spec : ETC.Spec K)
    (model : FiniteBanditModel K)
    (commitArm : Fin K)
    (reward : Omega -> RewardTrace Rat)
    (a : Fin K) (t : Nat) (c : NNReal)
    (hne : a = model.bestArm -> False)
    (h_action :
      ETC.actionWithCommit spec commitArm t = model.bestArm)
    (h_subG :
      ProbabilityTheory.HasCondSubgaussianMGF
        m hm
        (fun omega : Omega =>
          (((model.mean model.bestArm - reward omega t : Rat) : Real)))
        c mu) :
    ProbabilityTheory.HasCondSubgaussianMGF
      m hm
      (fun omega =>
        ETC.centeredPairwiseRewardDiff
          spec model commitArm reward a t omega)
      c mu := by
  exact
    ETC.centeredPairwiseRewardDiff_hasCondSubgaussianMGF_of_action_eq_bestArm
      (mOmega := mOmega) (mu := mu) (m := m) (hm := hm)
      spec model commitArm reward a t c hne h_action h_subG

example {Omega : Type} {K : Nat}
    [mOmega : MeasurableSpace Omega] [StandardBorelSpace Omega]
    (mu : MeasureTheory.Measure Omega)
    [MeasureTheory.IsFiniteMeasure mu]
    (spec : ETC.Spec K)
    (model : FiniteBanditModel K)
    (commitArm : Fin K)
    (reward : Omega -> RewardTrace Rat)
    (hreward : forall t : Nat,
      Measurable (fun omega : Omega => reward omega t))
    (a : Fin K) (t : Nat) (c : NNReal)
    (hne : a = model.bestArm -> False)
    (h_action : ETC.actionWithCommit spec commitArm t = a)
    (h_subG :
      ProbabilityTheory.HasCondSubgaussianMGF
        (History.historyFiltrationSucc
          (fun _omega : Omega => ETC.actionWithCommit spec commitArm)
          reward
          (fun _t : Nat => measurable_const)
          hreward t)
        ((History.historyFiltrationSucc
          (fun _omega : Omega => ETC.actionWithCommit spec commitArm)
          reward
          (fun _t : Nat => measurable_const)
          hreward).le t)
        (fun omega : Omega =>
          (((reward omega t - model.mean a : Rat) : Real)))
        c mu) :
    ProbabilityTheory.HasCondSubgaussianMGF
      (History.historyFiltrationSucc
        (fun _omega : Omega => ETC.actionWithCommit spec commitArm)
        reward
        (fun _t : Nat => measurable_const)
        hreward t)
      ((History.historyFiltrationSucc
        (fun _omega : Omega => ETC.actionWithCommit spec commitArm)
        reward
        (fun _t : Nat => measurable_const)
        hreward).le t)
      (fun omega =>
        ETC.centeredPairwiseRewardDiff
          spec model commitArm reward a t omega)
      c mu := by
  exact
    ETC.centeredPairwiseRewardDiff_hasCondSubgaussianMGF_historyFiltrationSucc_of_action_eq_arm
      mu spec model commitArm reward hreward a t c hne h_action h_subG

example {Omega : Type} {K : Nat}
    [mOmega : MeasurableSpace Omega] [StandardBorelSpace Omega]
    (mu : MeasureTheory.Measure Omega)
    [MeasureTheory.IsFiniteMeasure mu]
    (spec : ETC.Spec K)
    (model : FiniteBanditModel K)
    (commitArm : Fin K)
    (reward : Omega -> RewardTrace Rat)
    (hreward : forall t : Nat,
      Measurable (fun omega : Omega => reward omega t))
    (a : Fin K) (t : Nat) (c : NNReal)
    (hne : a = model.bestArm -> False)
    (h_action :
      ETC.actionWithCommit spec commitArm t = model.bestArm)
    (h_subG :
      ProbabilityTheory.HasCondSubgaussianMGF
        (History.historyFiltrationSucc
          (fun _omega : Omega => ETC.actionWithCommit spec commitArm)
          reward
          (fun _t : Nat => measurable_const)
          hreward t)
        ((History.historyFiltrationSucc
          (fun _omega : Omega => ETC.actionWithCommit spec commitArm)
          reward
          (fun _t : Nat => measurable_const)
          hreward).le t)
        (fun omega : Omega =>
          (((model.mean model.bestArm - reward omega t : Rat) : Real)))
        c mu) :
    ProbabilityTheory.HasCondSubgaussianMGF
      (History.historyFiltrationSucc
        (fun _omega : Omega => ETC.actionWithCommit spec commitArm)
        reward
        (fun _t : Nat => measurable_const)
        hreward t)
      ((History.historyFiltrationSucc
        (fun _omega : Omega => ETC.actionWithCommit spec commitArm)
        reward
        (fun _t : Nat => measurable_const)
        hreward).le t)
      (fun omega =>
        ETC.centeredPairwiseRewardDiff
          spec model commitArm reward a t omega)
      c mu := by
  exact
    ETC.centeredPairwiseRewardDiff_hasCondSubgaussianMGF_historyFiltrationSucc_of_action_eq_bestArm
      mu spec model commitArm reward hreward a t c hne h_action h_subG

noncomputable example {Omega : Type} {K : Nat}
    [mOmega : MeasurableSpace Omega] [StandardBorelSpace Omega]
    (mu : MeasureTheory.Measure Omega)
    [MeasureTheory.IsFiniteMeasure mu]
    (m : MeasurableSpace Omega) (hm : m <= mOmega)
    (spec : ETC.Spec K)
    (model : FiniteBanditModel K)
    (commitArm : Fin K)
    (reward : Omega -> RewardTrace Rat)
    (cReward : Fin K -> Nat -> NNReal)
    (a : Fin K) (t : Nat)
    (hne : a = model.bestArm -> False)
    (h_subG :
      forall b : Fin K, ETC.actionWithCommit spec commitArm t = b ->
        ProbabilityTheory.HasCondSubgaussianMGF
          m hm
          (fun omega : Omega =>
            (((reward omega t - model.mean b : Rat) : Real)))
          (cReward b t) mu) :
    ProbabilityTheory.HasCondSubgaussianMGF
      m hm
      (fun omega =>
        ETC.centeredPairwiseRewardDiff
          spec model commitArm reward a t omega)
      (ETC.centeredPairwiseRewardDiffVarianceProxy
        spec model commitArm cReward a t)
      mu := by
  exact
    ETC.centeredPairwiseRewardDiff_hasCondSubgaussianMGF_of_centeredReward
      (mOmega := mOmega) (mu := mu) (m := m) (hm := hm)
      spec model commitArm reward cReward a t hne h_subG

noncomputable example {Omega : Type} {K : Nat}
    [mOmega : MeasurableSpace Omega] [StandardBorelSpace Omega]
    (mu : MeasureTheory.Measure Omega)
    [MeasureTheory.IsFiniteMeasure mu]
    (spec : ETC.Spec K)
    (model : FiniteBanditModel K)
    (commitArm : Fin K)
    (reward : Omega -> RewardTrace Rat)
    (hreward : forall t : Nat,
      Measurable (fun omega : Omega => reward omega t))
    (cReward : Fin K -> Nat -> NNReal)
    (a : Fin K) (t : Nat)
    (hne : a = model.bestArm -> False)
    (h_subG :
      forall b : Fin K, ETC.actionWithCommit spec commitArm t = b ->
        ProbabilityTheory.HasCondSubgaussianMGF
          (History.historyFiltrationSucc
            (fun _omega : Omega => ETC.actionWithCommit spec commitArm)
            reward
            (fun _t : Nat => measurable_const)
            hreward t)
          ((History.historyFiltrationSucc
            (fun _omega : Omega => ETC.actionWithCommit spec commitArm)
            reward
            (fun _t : Nat => measurable_const)
            hreward).le t)
          (fun omega : Omega =>
            (((reward omega t - model.mean b : Rat) : Real)))
          (cReward b t) mu) :
    ProbabilityTheory.HasCondSubgaussianMGF
      (History.historyFiltrationSucc
        (fun _omega : Omega => ETC.actionWithCommit spec commitArm)
        reward
        (fun _t : Nat => measurable_const)
        hreward t)
      ((History.historyFiltrationSucc
        (fun _omega : Omega => ETC.actionWithCommit spec commitArm)
        reward
        (fun _t : Nat => measurable_const)
        hreward).le t)
      (fun omega =>
        ETC.centeredPairwiseRewardDiff
          spec model commitArm reward a t omega)
      (ETC.centeredPairwiseRewardDiffVarianceProxy
        spec model commitArm cReward a t)
      mu := by
  exact
    ETC.centeredPairwiseRewardDiff_hasCondSubgaussianMGF_historyFiltrationSucc_of_centeredReward
      mu spec model commitArm reward hreward cReward a t hne h_subG

noncomputable example {Omega : Type} {K : Nat}
    [mOmega : MeasurableSpace Omega] [StandardBorelSpace Omega]
    (mu : MeasureTheory.Measure Omega)
    [MeasureTheory.IsFiniteMeasure mu]
    [MeasureTheory.IsZeroOrProbabilityMeasure mu]
    (spec : ETC.Spec K)
    (model : FiniteBanditModel K)
    (commitArm : Fin K)
    (reward : Omega -> RewardTrace Rat)
    (tail : Fin K -> ENNReal)
    (w :
      ETC.CenteredRewardCondSubGaussianWitnesses
        mu spec model commitArm reward tail) :
    ETC.CenteredDiffCondSubGaussianWitnesses
      mu spec model commitArm reward tail := by
  exact
    ETC.centeredDiffCondSubGaussianWitnesses_of_centeredRewardCondSubGaussianWitnesses
      mu spec model commitArm reward tail w

noncomputable example {Omega : Type} {K : Nat}
    [mOmega : MeasurableSpace Omega] [StandardBorelSpace Omega]
    (mu : MeasureTheory.Measure Omega)
    [MeasureTheory.IsFiniteMeasure mu]
    [MeasureTheory.IsZeroOrProbabilityMeasure mu]
    (spec : ETC.Spec K)
    (model : FiniteBanditModel K)
    (commitArm : Fin K)
    (reward : Omega -> RewardTrace Rat)
    (tail : Fin K -> ENNReal)
    (hexplorationPulls_pos : 0 < spec.explorationPulls)
    (w :
      ETC.CenteredRewardCondSubGaussianWitnesses
        mu spec model commitArm reward tail) :
    ETC.PairwiseEmpMeanTailContract
      mu spec model commitArm reward tail := by
  exact
    ETC.pairwiseEmpMeanTailContract_of_centeredDiffCondSubGaussianWitnesses
      mu spec model commitArm reward tail hexplorationPulls_pos
      (ETC.centeredDiffCondSubGaussianWitnesses_of_centeredRewardCondSubGaussianWitnesses
        mu spec model commitArm reward tail w)

example {Omega : Type} {K : Nat}
    [mOmega : MeasurableSpace Omega]
    (mu : MeasureTheory.Measure Omega)
    [MeasureTheory.IsFiniteMeasure mu]
    (mcond : MeasurableSpace Omega) (hm : mcond <= mOmega)
    (model : FiniteBanditModel K)
    (reward : Omega -> RewardTrace Rat)
    (b : Fin K) (t : Nat)
    (hmeas : @Measurable Omega Real mOmega inferInstance
      (fun omega : Omega =>
        (((reward omega t - model.mean b : Rat) : Real))))
    (h_indep :
      ProbabilityTheory.Indep
        (MeasurableSpace.comap
          (fun omega : Omega =>
            (((reward omega t - model.mean b : Rat) : Real)))
          inferInstance)
        mcond mu)
    (h_integral :
      MeasureTheory.integral mu
        (fun omega : Omega =>
          (((reward omega t - model.mean b : Rat) : Real))) = 0) :
    Filter.EventuallyEq (MeasureTheory.ae mu)
      (MeasureTheory.condExp mcond mu
        (fun omega : Omega =>
          (((reward omega t - model.mean b : Rat) : Real))))
      (fun _omega : Omega => (0 : Real)) := by
  exact
    ETC.centeredReward_condExp_eq_zero_of_indep
      (mOmega := mOmega)
      mu mcond hm model reward b t hmeas h_indep h_integral

example {Omega : Type}
    [mOmega : MeasurableSpace Omega] [StandardBorelSpace Omega]
    (mu : MeasureTheory.Measure Omega)
    [MeasureTheory.IsFiniteMeasure mu]
    (mcond : MeasurableSpace Omega) (hm : mcond <= mOmega)
    (X : Omega -> Real)
    (h_integrable : MeasureTheory.Integrable X mu)
    (h_kernel_zero :
      Filter.Eventually
        (fun omega : Omega =>
          MeasureTheory.integral
            (ProbabilityTheory.condExpKernel
              (Ω := Omega) (mΩ := mOmega) mu mcond omega)
            X = 0)
        (MeasureTheory.ae (mu.trim hm))) :
    Filter.EventuallyEq (MeasureTheory.ae mu)
      (@MeasureTheory.condExp Omega Real mcond mOmega _ _ _ mu X)
      (fun _omega : Omega => (0 : Real)) := by
  exact
    ConditionalExpectationReward.condExp_eq_zero_of_condExpKernel_integral_eq_zero
      (mOmega := mOmega)
      mu mcond hm X h_integrable h_kernel_zero

example {Omega : Type} {K : Nat}
    [mOmega : MeasurableSpace Omega] [StandardBorelSpace Omega]
    (mu : MeasureTheory.Measure Omega)
    [MeasureTheory.IsFiniteMeasure mu]
    (F : MeasureTheory.Filtration Nat mOmega)
    (model : FiniteBanditModel K)
    (reward : Omega -> RewardTrace Rat)
    (b : Fin K) (i : Nat)
    (h_integrable :
      MeasureTheory.Integrable
        (fun omega : Omega =>
          (((reward omega (i + 1) - model.mean b : Rat) : Real))) mu)
    (h_kernel_zero :
      Filter.Eventually
        (fun omega : Omega =>
          MeasureTheory.integral
            (ProbabilityTheory.condExpKernel
              (Ω := Omega) (mΩ := mOmega) mu (F i) omega)
            (fun y : Omega =>
              (((reward y (i + 1) - model.mean b : Rat) : Real))) = 0)
        (MeasureTheory.ae (mu.trim (F.le i)))) :
    Filter.EventuallyEq (MeasureTheory.ae mu)
      (@MeasureTheory.condExp Omega Real (F i) mOmega _ _ _ mu
        (fun omega : Omega =>
          (((reward omega (i + 1) - model.mean b : Rat) : Real))))
      (fun _omega : Omega => (0 : Real)) := by
  exact
    ConditionalExpectationReward.centeredReward_succ_condExp_eq_zero_of_condExpKernel_integral_eq_zero
      (mOmega := mOmega)
      mu F model reward b i h_integrable h_kernel_zero

example {Omega Context State Action : Type}
    [mOmega : MeasurableSpace Omega] [StandardBorelSpace Omega]
    [MeasurableSpace Context] [MeasurableSpace State]
    [MeasurableSpace Action]
    (mu : MeasureTheory.Measure Omega)
    [MeasureTheory.IsFiniteMeasure mu]
    (mcond : MeasurableSpace Omega) (hm : mcond <= mOmega)
    (rewardKernel :
      RewardKernel.MarkovRewardKernel (Context × Action) Rat)
    (policy : Nat -> Policy.MeasurablePolicy State Action)
    (context : (n : Nat) -> ((j : Finset.Iic n) -> Rat) -> Context)
    (state : (n : Nat) -> ((j : Finset.Iic n) -> Rat) -> State)
    (hcontext : forall n : Nat, Measurable (context n))
    (hstate : forall n : Nat, Measurable (state n))
    (mean : Context -> Action -> Rat)
    (varianceProxy : Context -> Action -> NNReal)
    (law :
      RewardKernel.CenteredRewardKernelLaw rewardKernel mean varianceProxy)
    (n : Nat)
    (history : Omega -> ((j : Finset.Iic n) -> Rat))
    (X : Omega -> Real)
    (h_integrable : MeasureTheory.Integrable X mu)
    (h_kernel_eq :
      Filter.Eventually
        (fun omega : Omega =>
          MeasureTheory.integral
            (ProbabilityTheory.condExpKernel
              (Ω := Omega) (mΩ := mOmega) mu mcond omega)
            X =
          MeasureTheory.integral
            (RewardKernel.historyStepKernelFamily rewardKernel policy context
              state hcontext hstate n (history omega))
            (fun reward : Rat =>
              (((reward -
                mean (context n (history omega))
                  ((policy n).action (state n (history omega))) :
                    Rat) : Real))))
        (MeasureTheory.ae (mu.trim hm))) :
    Filter.EventuallyEq (MeasureTheory.ae mu)
      (@MeasureTheory.condExp Omega Real mcond mOmega _ _ _ mu X)
      (fun _omega : Omega => (0 : Real)) := by
  exact
    ConditionalExpectationReward.condExp_eq_zero_of_condExpKernel_integral_eq_historyStepKernel_centeredReward
      (mOmega := mOmega)
      mu mcond hm rewardKernel policy context state hcontext hstate mean
      varianceProxy law n history X h_integrable h_kernel_eq

example {Omega Context State Action : Type}
    [mOmega : MeasurableSpace Omega] [StandardBorelSpace Omega]
    [MeasurableSpace Context] [MeasurableSpace State]
    [MeasurableSpace Action]
    (mu : MeasureTheory.Measure Omega)
    [MeasureTheory.IsFiniteMeasure mu]
    (F : MeasureTheory.Filtration Nat mOmega)
    (rewardKernel :
      RewardKernel.MarkovRewardKernel (Context × Action) Rat)
    (policy : Nat -> Policy.MeasurablePolicy State Action)
    (context : (n : Nat) -> ((j : Finset.Iic n) -> Rat) -> Context)
    (state : (n : Nat) -> ((j : Finset.Iic n) -> Rat) -> State)
    (hcontext : forall n : Nat, Measurable (context n))
    (hstate : forall n : Nat, Measurable (state n))
    (mean : Context -> Action -> Rat)
    (varianceProxy : Context -> Action -> NNReal)
    (law :
      RewardKernel.CenteredRewardKernelLaw rewardKernel mean varianceProxy)
    (reward : Omega -> RewardTrace Rat)
    (i : Nat)
    (history : Omega -> ((j : Finset.Iic i) -> Rat))
    (h_integrable :
      MeasureTheory.Integrable
        (fun omega : Omega =>
          (((reward omega (i + 1) -
            mean (context i (history omega))
              ((policy i).action (state i (history omega))) : Rat) :
                Real))) mu)
    (h_kernel_eq :
      Filter.Eventually
        (fun omega : Omega =>
          MeasureTheory.integral
            (ProbabilityTheory.condExpKernel
              (Ω := Omega) (mΩ := mOmega) mu (F i) omega)
            (fun y : Omega =>
              (((reward y (i + 1) -
                mean (context i (history y))
                  ((policy i).action (state i (history y))) : Rat) :
                    Real))) =
          MeasureTheory.integral
            (RewardKernel.historyStepKernelFamily rewardKernel policy context
              state hcontext hstate i (history omega))
            (fun reward : Rat =>
              (((reward -
                mean (context i (history omega))
                  ((policy i).action (state i (history omega))) :
                    Rat) : Real))))
        (MeasureTheory.ae (mu.trim (F.le i)))) :
    Filter.EventuallyEq (MeasureTheory.ae mu)
      (@MeasureTheory.condExp Omega Real (F i) mOmega _ _ _ mu
        (fun omega : Omega =>
          (((reward omega (i + 1) -
            mean (context i (history omega))
              ((policy i).action (state i (history omega))) : Rat) :
                Real))))
      (fun _omega : Omega => (0 : Real)) := by
  exact
    ConditionalExpectationReward.centeredReward_succ_condExp_eq_zero_of_historyStepKernelFamily_condExpKernel_integral_eq
      (mOmega := mOmega)
      mu F rewardKernel policy context state hcontext hstate mean varianceProxy
      law reward i history h_integrable h_kernel_eq

example {Omega Context State Action : Type}
    [mOmega : MeasurableSpace Omega] [StandardBorelSpace Omega]
    [MeasurableSpace Context] [MeasurableSpace State]
    [MeasurableSpace Action]
    (mu : MeasureTheory.Measure Omega)
    [MeasureTheory.IsFiniteMeasure mu]
    (mcond : MeasurableSpace Omega) (hm : mcond <= mOmega)
    (rewardKernel :
      RewardKernel.MarkovRewardKernel (Context × Action) Rat)
    (policy : Nat -> Policy.MeasurablePolicy State Action)
    (context : (n : Nat) -> ((j : Finset.Iic n) -> Rat) -> Context)
    (state : (n : Nat) -> ((j : Finset.Iic n) -> Rat) -> State)
    (hcontext : forall n : Nat, Measurable (context n))
    (hstate : forall n : Nat, Measurable (state n))
    (mean : Context -> Action -> Rat)
    (varianceProxy : Context -> Action -> NNReal)
    (law :
      RewardKernel.CenteredRewardKernelLaw rewardKernel mean varianceProxy)
    (n : Nat)
    (history : Omega -> ((j : Finset.Iic n) -> Rat))
    (nextReward : Omega -> Rat)
    (X : Omega -> Real)
    (h_nextReward :
      @Measurable Omega Rat mOmega inferInstance nextReward)
    (h_integrable : MeasureTheory.Integrable X mu)
    (h_kernel_map_eq :
      Filter.Eventually
        (fun omega : Omega =>
          @MeasureTheory.Measure.map Omega Rat mOmega inferInstance nextReward
            (ProbabilityTheory.condExpKernel
              (Ω := Omega) (mΩ := mOmega) mu mcond omega) =
          RewardKernel.historyStepKernelFamily rewardKernel policy context state
            hcontext hstate n (history omega))
        (MeasureTheory.ae (mu.trim hm)))
    (h_kernel_X_eq :
      Filter.Eventually
        (fun omega : Omega =>
          X =ᵐ[
            ProbabilityTheory.condExpKernel
              (Ω := Omega) (mΩ := mOmega) mu mcond omega]
            (fun y : Omega =>
              (((nextReward y -
                mean (context n (history omega))
                  ((policy n).action (state n (history omega))) :
                    Rat) : Real))))
        (MeasureTheory.ae (mu.trim hm))) :
    Filter.EventuallyEq (MeasureTheory.ae mu)
      (@MeasureTheory.condExp Omega Real mcond mOmega _ _ _ mu X)
      (fun _omega : Omega => (0 : Real)) := by
  exact
    ConditionalExpectationReward.condExp_eq_zero_of_condExpKernel_map_eq_historyStepKernel_centeredReward
      (mOmega := mOmega)
      mu mcond hm rewardKernel policy context state hcontext hstate mean
      varianceProxy law n history nextReward X h_nextReward h_integrable
      h_kernel_map_eq h_kernel_X_eq

example {Omega : Type} [MeasurableSpace Omega]
    {mu : MeasureTheory.Measure Omega}
    {X : Omega -> Real} {c d : NNReal}
    (hcd : c <= d)
    (h_subG : ProbabilityTheory.HasSubgaussianMGF X c mu) :
    ProbabilityTheory.HasSubgaussianMGF X d mu := by
  exact
    ConditionalExpectationReward.hasSubgaussianMGF_mono_varianceProxy
      hcd h_subG

example {Omega : Type}
    [mOmega : MeasurableSpace Omega] [StandardBorelSpace Omega]
    (mu : MeasureTheory.Measure Omega)
    [MeasureTheory.IsFiniteMeasure mu]
    (mcond : MeasurableSpace Omega) (hm : mcond <= mOmega)
    (X : Omega -> Real) (c : NNReal)
    (hX : @Measurable Omega Real mOmega inferInstance X)
    (target : Omega -> MeasureTheory.Measure Real)
    (h_integrable_exp :
      forall t : Real,
        MeasureTheory.Integrable
          (fun omega : Omega => Real.exp (t * X omega)) mu)
    (h_kernel_map_eq :
      Filter.Eventually
        (fun omega : Omega =>
          @MeasureTheory.Measure.map Omega Real mOmega inferInstance X
            (@ProbabilityTheory.condExpKernel Omega mOmega _ mu _ mcond
              omega) =
          target omega)
        (MeasureTheory.ae (mu.trim hm)))
    (h_target_subG :
      Filter.Eventually
        (fun omega : Omega =>
          ProbabilityTheory.HasSubgaussianMGF
            (fun z : Real => z) c (target omega))
        (MeasureTheory.ae (mu.trim hm))) :
    ProbabilityTheory.HasCondSubgaussianMGF mcond hm X c mu := by
  exact
    ConditionalExpectationReward.hasCondSubgaussianMGF_of_condExpKernel_map_eq
      (mOmega := mOmega)
      mu mcond hm X c hX target h_integrable_exp h_kernel_map_eq
      h_target_subG

example {Omega Context State Action : Type}
    [mOmega : MeasurableSpace Omega] [StandardBorelSpace Omega]
    [MeasurableSpace Context] [MeasurableSpace State]
    [MeasurableSpace Action]
    (mu : MeasureTheory.Measure Omega)
    [MeasureTheory.IsFiniteMeasure mu]
    (mcond : MeasurableSpace Omega) (hm : mcond <= mOmega)
    (rewardKernel :
      RewardKernel.MarkovRewardKernel (Prod Context Action) Rat)
    (policy : Nat -> Policy.MeasurablePolicy State Action)
    (context : (n : Nat) -> ((j : Finset.Iic n) -> Rat) -> Context)
    (state : (n : Nat) -> ((j : Finset.Iic n) -> Rat) -> State)
    (hcontext : forall n : Nat, Measurable (context n))
    (hstate : forall n : Nat, Measurable (state n))
    (mean : Context -> Action -> Rat)
    (varianceProxy : Context -> Action -> NNReal)
    (law :
      RewardKernel.CenteredRewardKernelLaw rewardKernel mean varianceProxy)
    (n : Nat)
    (history : Omega -> ((j : Finset.Iic n) -> Rat))
    (nextReward : Omega -> Rat)
    (X : Omega -> Real)
    (c : NNReal)
    (h_nextReward :
      @Measurable Omega Rat mOmega inferInstance nextReward)
    (hX : @Measurable Omega Real mOmega inferInstance X)
    (h_integrable_exp :
      forall t : Real,
        MeasureTheory.Integrable
          (fun omega : Omega => Real.exp (t * X omega)) mu)
    (h_kernel_map_eq :
      Filter.Eventually
        (fun omega : Omega =>
          @MeasureTheory.Measure.map Omega Rat mOmega inferInstance nextReward
            (@ProbabilityTheory.condExpKernel Omega mOmega _ mu _ mcond
              omega) =
          RewardKernel.historyStepKernelFamily rewardKernel policy context state
            hcontext hstate n (history omega))
        (MeasureTheory.ae (mu.trim hm)))
    (h_kernel_X_eq :
      Filter.Eventually
        (fun omega : Omega =>
          Filter.EventuallyEq
            (MeasureTheory.ae
              (@ProbabilityTheory.condExpKernel Omega mOmega _ mu _ mcond
                omega))
            X
            (fun y : Omega =>
              (((nextReward y - mean (context n (history omega))
                ((policy n).action (state n (history omega))) : Rat) :
                Real))))
        (MeasureTheory.ae (mu.trim hm)))
    (h_variance_le :
      Filter.Eventually
        (fun omega : Omega =>
          varianceProxy (context n (history omega))
            ((policy n).action (state n (history omega))) <= c)
        (MeasureTheory.ae (mu.trim hm))) :
    ProbabilityTheory.HasCondSubgaussianMGF mcond hm X c mu := by
  exact
    ConditionalExpectationReward.hasCondSubgaussianMGF_of_condExpKernel_map_eq_historyStepKernel_centeredReward
      (mOmega := mOmega)
      mu mcond hm rewardKernel policy context state hcontext hstate mean
      varianceProxy law n history nextReward X c h_nextReward hX
      h_integrable_exp h_kernel_map_eq h_kernel_X_eq h_variance_le

example {Omega : Type}
    [mOmega : MeasurableSpace Omega] [StandardBorelSpace Omega]
    (mu : MeasureTheory.Measure Omega)
    [MeasureTheory.IsFiniteMeasure mu]
    (mcond : MeasurableSpace Omega) (hm : mcond <= mOmega)
    (s : Set Omega) (hs : @MeasurableSet Omega mcond s) :
    Filter.Eventually
      (fun omega : Omega =>
        (@ProbabilityTheory.condExpKernel Omega mOmega _ mu _ mcond omega).real s =
        Set.indicator s (fun _omega : Omega => (1 : Real)) omega)
      (MeasureTheory.ae (mu.trim hm)) := by
  exact
    ConditionalExpectationReward.condExpKernel_event_real_eq_indicator_of_measurableSet
      (mOmega := mOmega) mu mcond hm s hs

example {Omega A : Type}
    [mOmega : MeasurableSpace Omega] [StandardBorelSpace Omega]
    [MeasurableSpace A] [MeasurableSingletonClass A] [Countable A]
    (mu : MeasureTheory.Measure Omega)
    [MeasureTheory.IsFiniteMeasure mu]
    (mcond : MeasurableSpace Omega) (hm : mcond <= mOmega)
    (Y : Omega -> A)
    (hY : @Measurable Omega A mcond inferInstance Y) :
    Filter.Eventually
      (fun omega : Omega =>
        Filter.EventuallyEq
          (MeasureTheory.ae
            (@ProbabilityTheory.condExpKernel Omega mOmega _ mu _ mcond omega))
          Y
          (fun _y : Omega => Y omega))
      (MeasureTheory.ae (mu.trim hm)) := by
  exact
    ConditionalExpectationReward.condExpKernel_ae_eq_const_of_countable_measurable
      (mOmega := mOmega) mu mcond hm Y hY

example {Omega : Type}
    [mOmega : MeasurableSpace Omega] [StandardBorelSpace Omega]
    (mu : MeasureTheory.Measure Omega)
    [MeasureTheory.IsFiniteMeasure mu]
    (F : MeasureTheory.Filtration Nat mOmega)
    (i : Nat)
    (history : Omega -> ((j : Finset.Iic i) -> Rat))
    (hhistory :
      @Measurable Omega ((j : Finset.Iic i) -> Rat)
        (F i) inferInstance history) :
    Filter.Eventually
      (fun omega : Omega =>
        history =ᵐ[
          ProbabilityTheory.condExpKernel
            (Ω := Omega) (mΩ := mOmega) mu (F i) omega]
          (fun _y : Omega => history omega))
      (MeasureTheory.ae (mu.trim (F.le i))) := by
  exact
    ConditionalExpectationReward.finiteRewardHistory_condExpKernel_frozen_of_measurable
      (mOmega := mOmega) mu F i history hhistory

example {Omega : Type}
    [mOmega : MeasurableSpace Omega] [StandardBorelSpace Omega]
    (mu : MeasureTheory.Measure Omega)
    [MeasureTheory.IsFiniteMeasure mu]
    (F : MeasureTheory.Filtration Nat mOmega)
    (reward : Omega -> RewardTrace Rat)
    (i : Nat)
    (hreward :
      forall j : Finset.Iic i,
        @Measurable Omega Rat (F i) inferInstance
          (fun omega : Omega => reward omega j.1)) :
    Filter.Eventually
      (fun omega : Omega =>
        Filter.EventuallyEq
          (MeasureTheory.ae
            (@ProbabilityTheory.condExpKernel Omega mOmega _ mu _ (F i) omega))
          (fun y : Omega =>
            History.finiteRewardHistoryOfTrace (reward y) i)
          (fun _y : Omega =>
            History.finiteRewardHistoryOfTrace (reward omega) i))
      (MeasureTheory.ae (mu.trim (F.le i))) := by
  exact
    ConditionalExpectationReward.finiteRewardHistory_condExpKernel_frozen_of_coordinate_measurable
      (mOmega := mOmega) mu F reward i hreward

example {Omega Action : Type}
    [mOmega : MeasurableSpace Omega] [StandardBorelSpace Omega]
    [MeasurableSpace Action] [MeasurableSingletonClass Action]
    (mu : MeasureTheory.Measure Omega)
    [MeasureTheory.IsFiniteMeasure mu]
    (action : Omega -> ActionTrace Action)
    (reward : Omega -> RewardTrace Rat)
    (haction : forall t : Nat,
      Measurable (fun omega : Omega => action omega t))
    (hreward : forall t : Nat,
      Measurable (fun omega : Omega => reward omega t))
    (i : Nat) :
    Filter.Eventually
      (fun omega : Omega =>
        Filter.EventuallyEq
          (MeasureTheory.ae
            (@ProbabilityTheory.condExpKernel Omega mOmega _ mu _
              ((History.historyFiltrationSucc action reward haction hreward) i)
              omega))
          (fun y : Omega =>
            History.finiteRewardHistoryOfTrace (reward y) i)
          (fun _y : Omega =>
            History.finiteRewardHistoryOfTrace (reward omega) i))
      (MeasureTheory.ae
        (mu.trim
          ((History.historyFiltrationSucc action reward haction hreward).le
            i))) := by
  exact
    ConditionalExpectationReward.finiteRewardHistory_condExpKernel_frozen_historyFiltrationSucc
      (mOmega := mOmega) mu action reward haction hreward i

example {Omega Action : Type}
    [mOmega : MeasurableSpace Omega] [StandardBorelSpace Omega]
    [MeasurableSpace Action] [MeasurableSingletonClass Action]
    [Countable Action]
    (mu : MeasureTheory.Measure Omega)
    [MeasureTheory.IsFiniteMeasure mu]
    (F : MeasureTheory.Filtration Nat mOmega)
    (i : Nat)
    (history : Omega -> ((j : Finset.Iic i) -> Prod Action Rat))
    (hhistory :
      @Measurable Omega ((j : Finset.Iic i) -> Prod Action Rat)
        (F i) inferInstance history) :
    Filter.Eventually
      (fun omega : Omega =>
        Filter.EventuallyEq
          (MeasureTheory.ae
            (@ProbabilityTheory.condExpKernel Omega mOmega _ mu _ (F i) omega))
          history
          (fun _y : Omega => history omega))
      (MeasureTheory.ae (mu.trim (F.le i))) := by
  exact
    ConditionalExpectationReward.finitePairHistory_condExpKernel_frozen_of_measurable
      (mOmega := mOmega) mu F i history hhistory

example {Omega Action : Type}
    [mOmega : MeasurableSpace Omega] [StandardBorelSpace Omega]
    [MeasurableSpace Action] [MeasurableSingletonClass Action]
    [Countable Action]
    (mu : MeasureTheory.Measure Omega)
    [MeasureTheory.IsFiniteMeasure mu]
    (F : MeasureTheory.Filtration Nat mOmega)
    (action : Omega -> ActionTrace Action)
    (reward : Omega -> RewardTrace Rat)
    (i : Nat)
    (haction :
      forall j : Finset.Iic i,
        @Measurable Omega Action (F i) inferInstance
          (fun omega : Omega => action omega j.1))
    (hreward :
      forall j : Finset.Iic i,
        @Measurable Omega Rat (F i) inferInstance
          (fun omega : Omega => reward omega j.1)) :
    Filter.Eventually
      (fun omega : Omega =>
        Filter.EventuallyEq
          (MeasureTheory.ae
            (@ProbabilityTheory.condExpKernel Omega mOmega _ mu _ (F i) omega))
          (fun y : Omega =>
            History.finitePairHistoryOfTrace (action y) (reward y) i)
          (fun _y : Omega =>
            History.finitePairHistoryOfTrace (action omega) (reward omega) i))
      (MeasureTheory.ae (mu.trim (F.le i))) := by
  exact
    ConditionalExpectationReward.finitePairHistory_condExpKernel_frozen_of_coordinate_measurable
      (mOmega := mOmega) mu F action reward i haction hreward

example {Omega Action : Type}
    [mOmega : MeasurableSpace Omega] [StandardBorelSpace Omega]
    [MeasurableSpace Action] [MeasurableSingletonClass Action]
    [Countable Action]
    (mu : MeasureTheory.Measure Omega)
    [MeasureTheory.IsFiniteMeasure mu]
    (action : Omega -> ActionTrace Action)
    (reward : Omega -> RewardTrace Rat)
    (haction : forall t : Nat,
      Measurable (fun omega : Omega => action omega t))
    (hreward : forall t : Nat,
      Measurable (fun omega : Omega => reward omega t))
    (i : Nat) :
    Filter.Eventually
      (fun omega : Omega =>
        Filter.EventuallyEq
          (MeasureTheory.ae
            (@ProbabilityTheory.condExpKernel Omega mOmega _ mu _
              ((History.historyFiltrationSucc action reward haction hreward) i)
              omega))
          (fun y : Omega =>
            History.finitePairHistoryOfTrace (action y) (reward y) i)
          (fun _y : Omega =>
            History.finitePairHistoryOfTrace (action omega) (reward omega) i))
      (MeasureTheory.ae
        (mu.trim
          ((History.historyFiltrationSucc action reward haction hreward).le
            i))) := by
  exact
    ConditionalExpectationReward.finitePairHistory_condExpKernel_frozen_historyFiltrationSucc
      (mOmega := mOmega) mu action reward haction hreward i

example {Omega Action : Type}
    [mOmega : MeasurableSpace Omega]
    (nu : MeasureTheory.Measure Omega)
    (action : Omega -> ActionTrace Action)
    (reward : Omega -> RewardTrace Rat)
    (i : Nat) (omega : Omega)
    (h_pair_history_frozen :
      Filter.EventuallyEq (MeasureTheory.ae nu)
        (fun y : Omega =>
          History.finitePairHistoryOfTrace (action y) (reward y) i)
        (fun _y : Omega =>
          History.finitePairHistoryOfTrace (action omega) (reward omega) i)) :
    Filter.EventuallyEq (MeasureTheory.ae nu)
      (fun y : Omega =>
        History.finitePairHistoryOfTrace (action y) (reward y) (i + 1))
      (fun y : Omega =>
        History.extendPairHistorySucc
          (History.finitePairHistoryOfTrace (action omega) (reward omega) i)
          (action y (i + 1), reward y (i + 1))) := by
  exact
    ConditionalExpectationReward.finitePairHistory_succ_ae_eq_extend_of_pairHistory_frozen
      (mOmega := mOmega) nu action reward i omega h_pair_history_frozen

example {Omega Action : Type}
    [mOmega : MeasurableSpace Omega] [StandardBorelSpace Omega]
    [MeasurableSpace Action] [MeasurableSingletonClass Action]
    [Countable Action]
    (mu : MeasureTheory.Measure Omega)
    [MeasureTheory.IsFiniteMeasure mu]
    (action : Omega -> ActionTrace Action)
    (reward : Omega -> RewardTrace Rat)
    (haction : forall t : Nat,
      Measurable (fun omega : Omega => action omega t))
    (hreward : forall t : Nat,
      Measurable (fun omega : Omega => reward omega t))
    (i : Nat) :
    Filter.Eventually
      (fun omega : Omega =>
        Filter.EventuallyEq
          (MeasureTheory.ae
            (@ProbabilityTheory.condExpKernel Omega mOmega _ mu _
              ((History.historyFiltrationSucc action reward haction hreward) i)
              omega))
          (fun y : Omega =>
            History.finitePairHistoryOfTrace (action y) (reward y) (i + 1))
          (fun y : Omega =>
            History.extendPairHistorySucc
              (History.finitePairHistoryOfTrace
                (action omega) (reward omega) i)
              (action y (i + 1), reward y (i + 1))))
      (MeasureTheory.ae
        (mu.trim
          ((History.historyFiltrationSucc action reward haction hreward).le
            i))) := by
  exact
    ConditionalExpectationReward.finitePairHistory_succ_condExpKernel_ae_eq_extend_historyFiltrationSucc
      (mOmega := mOmega) mu action reward haction hreward i

example {Omega Action : Type}
    [mOmega : MeasurableSpace Omega] [StandardBorelSpace Omega]
    [MeasurableSpace Action] [MeasurableSingletonClass Action]
    [Countable Action]
    (mu : MeasureTheory.Measure Omega)
    [MeasureTheory.IsFiniteMeasure mu]
    (action : Omega -> ActionTrace Action)
    (reward : Omega -> RewardTrace Rat)
    (haction : forall t : Nat,
      Measurable (fun omega : Omega => action omega t))
    (hreward : forall t : Nat,
      Measurable (fun omega : Omega => reward omega t))
    (i : Nat) :
    Filter.Eventually
      (fun omega : Omega =>
        @MeasureTheory.Measure.map Omega
          ((j : Finset.Iic (i + 1)) -> Prod Action Rat) mOmega
          inferInstance
          (fun y : Omega =>
            History.finitePairHistoryOfTrace (action y) (reward y) (i + 1))
          (@ProbabilityTheory.condExpKernel Omega mOmega _ mu _
            ((History.historyFiltrationSucc action reward haction hreward) i)
            omega) =
        @MeasureTheory.Measure.map Omega
          ((j : Finset.Iic (i + 1)) -> Prod Action Rat) mOmega
          inferInstance
          (fun y : Omega =>
            History.extendPairHistorySucc
              (History.finitePairHistoryOfTrace
                (action omega) (reward omega) i)
              (action y (i + 1), reward y (i + 1)))
          (@ProbabilityTheory.condExpKernel Omega mOmega _ mu _
            ((History.historyFiltrationSucc action reward haction hreward) i)
            omega))
      (MeasureTheory.ae
        (mu.trim
          ((History.historyFiltrationSucc action reward haction hreward).le
            i))) := by
  exact
    ConditionalExpectationReward.finitePairHistory_succ_condExpKernel_map_eq_extend_historyFiltrationSucc
      (mOmega := mOmega) mu action reward haction hreward i

example {Omega Context State Action : Type}
    [mOmega : MeasurableSpace Omega] [StandardBorelSpace Omega]
    [MeasurableSpace Context] [MeasurableSpace State]
    [MeasurableSpace Action]
    (mu : MeasureTheory.Measure Omega)
    [MeasureTheory.IsFiniteMeasure mu]
    (F : MeasureTheory.Filtration Nat mOmega)
    (policy : Nat -> Policy.MeasurablePolicy State Action)
    (context : (n : Nat) -> ((j : Finset.Iic n) -> Rat) -> Context)
    (state : (n : Nat) -> ((j : Finset.Iic n) -> Rat) -> State)
    (mean : Context -> Action -> Rat)
    (reward : Omega -> RewardTrace Rat)
    (i : Nat)
    (history : Omega -> ((j : Finset.Iic i) -> Rat))
    (h_history_frozen :
      Filter.Eventually
        (fun omega : Omega =>
          history =ᵐ[
            ProbabilityTheory.condExpKernel
              (Ω := Omega) (mΩ := mOmega) mu (F i) omega]
            (fun _y : Omega => history omega))
        (MeasureTheory.ae (mu.trim (F.le i)))) :
    Filter.Eventually
      (fun omega : Omega =>
        (fun y : Omega =>
          (((reward y (i + 1) -
            mean (context i (history y))
              ((policy i).action (state i (history y))) : Rat) :
                Real))) =ᵐ[
          ProbabilityTheory.condExpKernel
            (Ω := Omega) (mΩ := mOmega) mu (F i) omega]
        (fun y : Omega =>
          (((reward y (i + 1) -
            mean (context i (history omega))
              ((policy i).action (state i (history omega))) : Rat) :
                Real))))
      (MeasureTheory.ae (mu.trim (F.le i))) := by
  exact
    ConditionalExpectationReward.centeredReward_succ_frozenPast_ae_of_history_frozen
      (mOmega := mOmega)
      mu F policy context state mean reward i history h_history_frozen

example {Omega Context State Action : Type}
    [mOmega : MeasurableSpace Omega] [StandardBorelSpace Omega]
    [MeasurableSpace Context] [MeasurableSpace State]
    [MeasurableSpace Action]
    (mu : MeasureTheory.Measure Omega)
    [MeasureTheory.IsFiniteMeasure mu]
    (F : MeasureTheory.Filtration Nat mOmega)
    (rewardKernel :
      RewardKernel.MarkovRewardKernel (Context × Action) Rat)
    (policy : Nat -> Policy.MeasurablePolicy State Action)
    (context : (n : Nat) -> ((j : Finset.Iic n) -> Rat) -> Context)
    (state : (n : Nat) -> ((j : Finset.Iic n) -> Rat) -> State)
    (hcontext : forall n : Nat, Measurable (context n))
    (hstate : forall n : Nat, Measurable (state n))
    (mean : Context -> Action -> Rat)
    (varianceProxy : Context -> Action -> NNReal)
    (law :
      RewardKernel.CenteredRewardKernelLaw rewardKernel mean varianceProxy)
    (reward : Omega -> RewardTrace Rat)
    (i : Nat)
    (history : Omega -> ((j : Finset.Iic i) -> Rat))
    (h_reward :
      @Measurable Omega Rat mOmega inferInstance
        (fun omega : Omega => reward omega (i + 1)))
    (h_integrable :
      MeasureTheory.Integrable
        (fun omega : Omega =>
          (((reward omega (i + 1) -
            mean (context i (history omega))
              ((policy i).action (state i (history omega))) : Rat) :
                Real))) mu)
    (h_kernel_map_eq :
      Filter.Eventually
        (fun omega : Omega =>
          @MeasureTheory.Measure.map Omega Rat mOmega inferInstance
            (fun y : Omega => reward y (i + 1))
            (ProbabilityTheory.condExpKernel
              (Ω := Omega) (mΩ := mOmega) mu (F i) omega) =
          RewardKernel.historyStepKernelFamily rewardKernel policy context state
            hcontext hstate i (history omega))
        (MeasureTheory.ae (mu.trim (F.le i))))
    (h_kernel_X_eq :
      Filter.Eventually
        (fun omega : Omega =>
          (fun y : Omega =>
            (((reward y (i + 1) -
              mean (context i (history y))
                ((policy i).action (state i (history y))) : Rat) :
                  Real))) =ᵐ[
            ProbabilityTheory.condExpKernel
              (Ω := Omega) (mΩ := mOmega) mu (F i) omega]
            (fun y : Omega =>
              (((reward y (i + 1) -
                mean (context i (history omega))
                  ((policy i).action (state i (history omega))) : Rat) :
                    Real))))
        (MeasureTheory.ae (mu.trim (F.le i)))) :
    Filter.EventuallyEq (MeasureTheory.ae mu)
      (@MeasureTheory.condExp Omega Real (F i) mOmega _ _ _ mu
        (fun omega : Omega =>
          (((reward omega (i + 1) -
            mean (context i (history omega))
              ((policy i).action (state i (history omega))) : Rat) :
                Real))))
      (fun _omega : Omega => (0 : Real)) := by
  exact
    ConditionalExpectationReward.centeredReward_succ_condExp_eq_zero_of_historyStepKernelFamily_condExpKernel_map_eq
      (mOmega := mOmega)
      mu F rewardKernel policy context state hcontext hstate mean varianceProxy
      law reward i history h_reward h_integrable h_kernel_map_eq h_kernel_X_eq

example {Omega Context State Action : Type}
    [mOmega : MeasurableSpace Omega] [StandardBorelSpace Omega]
    [MeasurableSpace Context] [MeasurableSpace State]
    [MeasurableSpace Action]
    (mu : MeasureTheory.Measure Omega)
    [MeasureTheory.IsFiniteMeasure mu]
    (F : MeasureTheory.Filtration Nat mOmega)
    (rewardKernel :
      RewardKernel.MarkovRewardKernel (Prod Context Action) Rat)
    (policy : Nat -> Policy.MeasurablePolicy State Action)
    (context : (n : Nat) -> ((j : Finset.Iic n) -> Rat) -> Context)
    (state : (n : Nat) -> ((j : Finset.Iic n) -> Rat) -> State)
    (hcontext : forall n : Nat, Measurable (context n))
    (hstate : forall n : Nat, Measurable (state n))
    (mean : Context -> Action -> Rat)
    (varianceProxy : Context -> Action -> NNReal)
    (law :
      RewardKernel.CenteredRewardKernelLaw rewardKernel mean varianceProxy)
    (reward : Omega -> RewardTrace Rat)
    (i : Nat)
    (history : Omega -> ((j : Finset.Iic i) -> Rat))
    (c : NNReal)
    (h_reward :
      @Measurable Omega Rat mOmega inferInstance
        (fun omega : Omega => reward omega (i + 1)))
    (h_centered_meas :
      @Measurable Omega Real mOmega inferInstance
        (fun omega : Omega =>
          (((reward omega (i + 1) -
            mean (context i (history omega))
              ((policy i).action (state i (history omega))) : Rat) :
                Real))))
    (h_integrable_exp :
      forall t : Real,
        MeasureTheory.Integrable
          (fun omega : Omega =>
            Real.exp (t *
              (((reward omega (i + 1) -
                mean (context i (history omega))
                  ((policy i).action (state i (history omega))) : Rat) :
                    Real)))) mu)
    (h_kernel_map_eq :
      Filter.Eventually
        (fun omega : Omega =>
          @MeasureTheory.Measure.map Omega Rat mOmega inferInstance
            (fun y : Omega => reward y (i + 1))
            (ProbabilityTheory.condExpKernel
              (Ω := Omega) (mΩ := mOmega) mu (F i) omega) =
          RewardKernel.historyStepKernelFamily rewardKernel policy context state
            hcontext hstate i (history omega))
        (MeasureTheory.ae (mu.trim (F.le i))))
    (h_kernel_X_eq :
      Filter.Eventually
        (fun omega : Omega =>
          Filter.EventuallyEq
            (MeasureTheory.ae
              (ProbabilityTheory.condExpKernel
                (Ω := Omega) (mΩ := mOmega) mu (F i) omega))
            (fun y : Omega =>
              (((reward y (i + 1) -
                mean (context i (history y))
                  ((policy i).action (state i (history y))) : Rat) :
                    Real)))
            (fun y : Omega =>
              (((reward y (i + 1) -
                mean (context i (history omega))
                  ((policy i).action (state i (history omega))) : Rat) :
                    Real))))
        (MeasureTheory.ae (mu.trim (F.le i))))
    (h_variance_le :
      Filter.Eventually
        (fun omega : Omega =>
          varianceProxy (context i (history omega))
            ((policy i).action (state i (history omega))) <= c)
        (MeasureTheory.ae (mu.trim (F.le i)))) :
    ProbabilityTheory.HasCondSubgaussianMGF (F i) (F.le i)
      (fun omega : Omega =>
        (((reward omega (i + 1) -
          mean (context i (history omega))
            ((policy i).action (state i (history omega))) : Rat) : Real)))
      c mu := by
  exact
    ConditionalExpectationReward.centeredReward_succ_hasCondSubgaussianMGF_of_historyStepKernelFamily_condExpKernel_map_eq
      (mOmega := mOmega)
      mu F rewardKernel policy context state hcontext hstate mean varianceProxy
      law reward i history c h_reward h_centered_meas h_integrable_exp
      h_kernel_map_eq h_kernel_X_eq h_variance_le

example {Omega Context State Action : Type}
    [mOmega : MeasurableSpace Omega] [StandardBorelSpace Omega]
    [MeasurableSpace Context] [MeasurableSpace State]
    [MeasurableSpace Action]
    (mu : MeasureTheory.Measure Omega)
    [MeasureTheory.IsFiniteMeasure mu]
    (F : MeasureTheory.Filtration Nat mOmega)
    (rewardKernel :
      RewardKernel.MarkovRewardKernel (Prod Context Action) Rat)
    (policy : Nat -> Policy.MeasurablePolicy State Action)
    (context : (n : Nat) -> ((j : Finset.Iic n) -> Rat) -> Context)
    (state : (n : Nat) -> ((j : Finset.Iic n) -> Rat) -> State)
    (hcontext : forall n : Nat, Measurable (context n))
    (hstate : forall n : Nat, Measurable (state n))
    (mean : Context -> Action -> Rat)
    (varianceProxy : Context -> Action -> NNReal)
    (law :
      RewardKernel.CenteredRewardKernelLaw rewardKernel mean varianceProxy)
    (reward : Omega -> RewardTrace Rat)
    (i : Nat)
    (h_reward :
      @Measurable Omega Rat mOmega inferInstance
        (fun omega : Omega => reward omega (i + 1)))
    (h_prefix_meas :
      forall j : Finset.Iic i,
        @Measurable Omega Rat (F i) inferInstance
          (fun omega : Omega => reward omega j.1))
    (h_integrable :
      MeasureTheory.Integrable
        (fun omega : Omega =>
          (((reward omega (i + 1) -
            mean
              (context i
                (History.finiteRewardHistoryOfTrace (reward omega) i))
              ((policy i).action
                (state i
                  (History.finiteRewardHistoryOfTrace (reward omega) i))) :
                Rat) : Real))) mu)
    (h_kernel_map_eq :
      Filter.Eventually
        (fun omega : Omega =>
          @MeasureTheory.Measure.map Omega Rat mOmega inferInstance
            (fun y : Omega => reward y (i + 1))
            (@ProbabilityTheory.condExpKernel Omega mOmega _ mu _ (F i)
              omega) =
          RewardKernel.historyStepKernelFamily rewardKernel policy context state
            hcontext hstate i
            (History.finiteRewardHistoryOfTrace (reward omega) i))
        (MeasureTheory.ae (mu.trim (F.le i)))) :
    Filter.EventuallyEq (MeasureTheory.ae mu)
      (@MeasureTheory.condExp Omega Real (F i) mOmega _ _ _ mu
        (fun omega : Omega =>
          (((reward omega (i + 1) -
            mean
              (context i
                (History.finiteRewardHistoryOfTrace (reward omega) i))
              ((policy i).action
                (state i
                  (History.finiteRewardHistoryOfTrace (reward omega) i))) :
                Rat) : Real))))
      (fun _omega : Omega => (0 : Real)) := by
  exact
    ConditionalExpectationReward.centeredReward_succ_condExp_eq_zero_of_historyStepKernelFamily_condExpKernel_map_eq_of_coordinate_measurable
      (mOmega := mOmega)
      mu F rewardKernel policy context state hcontext hstate mean varianceProxy
      law reward i h_reward h_prefix_meas h_integrable h_kernel_map_eq

example {Omega Context State Action : Type}
    [mOmega : MeasurableSpace Omega] [StandardBorelSpace Omega]
    [MeasurableSpace Context] [MeasurableSpace State]
    [MeasurableSpace Action]
    (mu : MeasureTheory.Measure Omega)
    [MeasureTheory.IsFiniteMeasure mu]
    (F : MeasureTheory.Filtration Nat mOmega)
    (rewardKernel :
      RewardKernel.MarkovRewardKernel (Prod Context Action) Rat)
    (policy : Nat -> Policy.MeasurablePolicy State Action)
    (context : (n : Nat) -> ((j : Finset.Iic n) -> Rat) -> Context)
    (state : (n : Nat) -> ((j : Finset.Iic n) -> Rat) -> State)
    (hcontext : forall n : Nat, Measurable (context n))
    (hstate : forall n : Nat, Measurable (state n))
    (mean : Context -> Action -> Rat)
    (varianceProxy : Context -> Action -> NNReal)
    (law :
      RewardKernel.CenteredRewardKernelLaw rewardKernel mean varianceProxy)
    (reward : Omega -> RewardTrace Rat)
    (i : Nat)
    (c : NNReal)
    (h_reward :
      @Measurable Omega Rat mOmega inferInstance
        (fun omega : Omega => reward omega (i + 1)))
    (h_prefix_meas :
      forall j : Finset.Iic i,
        @Measurable Omega Rat (F i) inferInstance
          (fun omega : Omega => reward omega j.1))
    (h_centered_meas :
      @Measurable Omega Real mOmega inferInstance
        (fun omega : Omega =>
          (((reward omega (i + 1) -
            mean
              (context i
                (History.finiteRewardHistoryOfTrace (reward omega) i))
              ((policy i).action
                (state i
                  (History.finiteRewardHistoryOfTrace (reward omega) i))) :
                Rat) : Real))))
    (h_integrable_exp :
      forall t : Real,
        MeasureTheory.Integrable
          (fun omega : Omega =>
            Real.exp (t *
              (((reward omega (i + 1) -
                mean
                  (context i
                    (History.finiteRewardHistoryOfTrace (reward omega) i))
                  ((policy i).action
                    (state i
                      (History.finiteRewardHistoryOfTrace (reward omega) i))) :
                    Rat) : Real)))) mu)
    (h_kernel_map_eq :
      Filter.Eventually
        (fun omega : Omega =>
          @MeasureTheory.Measure.map Omega Rat mOmega inferInstance
            (fun y : Omega => reward y (i + 1))
            (@ProbabilityTheory.condExpKernel Omega mOmega _ mu _ (F i)
              omega) =
          RewardKernel.historyStepKernelFamily rewardKernel policy context state
            hcontext hstate i
            (History.finiteRewardHistoryOfTrace (reward omega) i))
        (MeasureTheory.ae (mu.trim (F.le i))))
    (h_variance_le :
      Filter.Eventually
        (fun omega : Omega =>
          varianceProxy
              (context i
                (History.finiteRewardHistoryOfTrace (reward omega) i))
              ((policy i).action
                (state i
                  (History.finiteRewardHistoryOfTrace (reward omega) i))) <=
            c)
        (MeasureTheory.ae (mu.trim (F.le i)))) :
    ProbabilityTheory.HasCondSubgaussianMGF (F i) (F.le i)
      (fun omega : Omega =>
        (((reward omega (i + 1) -
          mean
            (context i
              (History.finiteRewardHistoryOfTrace (reward omega) i))
            ((policy i).action
              (state i
                (History.finiteRewardHistoryOfTrace (reward omega) i))) :
            Rat) : Real)))
      c mu := by
  exact
    ConditionalExpectationReward.centeredReward_succ_hasCondSubgaussianMGF_of_historyStepKernelFamily_condExpKernel_map_eq_of_coordinate_measurable
      (mOmega := mOmega)
      mu F rewardKernel policy context state hcontext hstate mean varianceProxy
      law reward i c h_reward h_prefix_meas h_centered_meas
      h_integrable_exp h_kernel_map_eq h_variance_le

example {Omega Context State Action : Type}
    [mOmega : MeasurableSpace Omega] [StandardBorelSpace Omega]
    [MeasurableSpace Context] [MeasurableSpace State]
    [MeasurableSpace Action]
    (mu : MeasureTheory.Measure Omega)
    [MeasureTheory.IsFiniteMeasure mu]
    (F : MeasureTheory.Filtration Nat mOmega)
    (rewardKernel :
      RewardKernel.MarkovRewardKernel (Prod Context Action) Rat)
    (policy : Nat -> Policy.MeasurablePolicy State Action)
    (context : (n : Nat) -> ((j : Finset.Iic n) -> Rat) -> Context)
    (state : (n : Nat) -> ((j : Finset.Iic n) -> Rat) -> State)
    (hcontext : forall n : Nat, Measurable (context n))
    (hstate : forall n : Nat, Measurable (state n))
    (mean : Context -> Action -> Rat)
    (varianceProxy : Context -> Action -> NNReal)
    (hmean :
      Measurable (fun pair : Prod Context Action => mean pair.1 pair.2))
    (hkernel :
      RewardKernel.CenteredRewardKernelLaw rewardKernel mean varianceProxy)
    (reward : Omega -> RewardTrace Rat)
    (hreward : forall t : Nat,
      @Measurable Omega Rat mOmega inferInstance
        (fun omega : Omega => reward omega t))
    (rewardLo rewardHi meanLo meanHi : Nat -> Real)
    (hraw :
      forall i : Nat, forall omega : Omega,
        Set.Icc (rewardLo i) (rewardHi i)
          (((reward omega (i + 1) : Rat) : Real)))
    (hmean_range :
      forall i : Nat, forall context : Context, forall action : Action,
        Set.Icc (meanLo i) (meanHi i)
          (((mean context action : Rat) : Real)))
    (i : Nat)
    (h_prefix_meas :
      forall j : Finset.Iic i,
        @Measurable Omega Rat (F i) inferInstance
          (fun omega : Omega => reward omega j.1))
    (h_kernel_map_eq :
      Filter.Eventually
        (fun omega : Omega =>
          @MeasureTheory.Measure.map Omega Rat mOmega inferInstance
            (fun y : Omega => reward y (i + 1))
            (@ProbabilityTheory.condExpKernel Omega mOmega _ mu _ (F i)
              omega) =
          RewardKernel.historyStepKernelFamily rewardKernel policy context state
            hcontext hstate i
            (History.finiteRewardHistoryOfTrace (reward omega) i))
        (MeasureTheory.ae (mu.trim (F.le i)))) :
    Filter.EventuallyEq (MeasureTheory.ae mu)
      (@MeasureTheory.condExp Omega Real (F i) mOmega _ _ _ mu
        (fun omega : Omega =>
          (((reward omega (i + 1) -
            mean
              (context i
                (History.finiteRewardHistoryOfTrace (reward omega) i))
              ((policy i).action
                (state i
                  (History.finiteRewardHistoryOfTrace (reward omega) i))) :
            Rat) : Real))))
      (fun _omega : Omega => (0 : Real)) := by
  exact
    ConditionalExpectationReward.centeredReward_succ_condExp_eq_zero_of_historyStepKernelFamily_condExpKernel_map_eq_of_coordinate_measurable_rawRangeMeasurableMeanRangeBounded
      (mOmega := mOmega)
      mu F rewardKernel policy context state hcontext hstate mean
      varianceProxy hmean hkernel reward hreward rewardLo rewardHi meanLo
      meanHi hraw hmean_range i h_prefix_meas h_kernel_map_eq

example {Omega Context State Action : Type}
    [mOmega : MeasurableSpace Omega] [StandardBorelSpace Omega]
    [MeasurableSpace Context] [MeasurableSpace State]
    [MeasurableSpace Action] [MeasurableSingletonClass Action]
    (mu : MeasureTheory.Measure Omega)
    [MeasureTheory.IsFiniteMeasure mu]
    (action : Omega -> ActionTrace Action)
    (rewardKernel :
      RewardKernel.MarkovRewardKernel (Prod Context Action) Rat)
    (policy : Nat -> Policy.MeasurablePolicy State Action)
    (context : (n : Nat) -> ((j : Finset.Iic n) -> Rat) -> Context)
    (state : (n : Nat) -> ((j : Finset.Iic n) -> Rat) -> State)
    (hcontext : forall n : Nat, Measurable (context n))
    (hstate : forall n : Nat, Measurable (state n))
    (mean : Context -> Action -> Rat)
    (varianceProxy : Context -> Action -> NNReal)
    (law :
      RewardKernel.CenteredRewardKernelLaw rewardKernel mean varianceProxy)
    (reward : Omega -> RewardTrace Rat)
    (haction : forall t : Nat,
      Measurable (fun omega : Omega => action omega t))
    (hreward : forall t : Nat,
      Measurable (fun omega : Omega => reward omega t))
    (i : Nat)
    (h_integrable :
      MeasureTheory.Integrable
        (fun omega : Omega =>
          (((reward omega (i + 1) -
            mean
              (context i
                (History.finiteRewardHistoryOfTrace (reward omega) i))
              ((policy i).action
                (state i
                  (History.finiteRewardHistoryOfTrace (reward omega) i))) :
                Rat) : Real))) mu)
    (h_kernel_map_eq :
      Filter.Eventually
        (fun omega : Omega =>
          @MeasureTheory.Measure.map Omega Rat mOmega inferInstance
            (fun y : Omega => reward y (i + 1))
            (@ProbabilityTheory.condExpKernel Omega mOmega _ mu _
              ((History.historyFiltrationSucc action reward haction hreward) i)
              omega) =
          RewardKernel.historyStepKernelFamily rewardKernel policy context state
            hcontext hstate i
            (History.finiteRewardHistoryOfTrace (reward omega) i))
        (MeasureTheory.ae
          (mu.trim
            ((History.historyFiltrationSucc action reward haction hreward).le
              i)))) :
    Filter.EventuallyEq (MeasureTheory.ae mu)
      (@MeasureTheory.condExp Omega Real
        ((History.historyFiltrationSucc action reward haction hreward) i)
        mOmega _ _ _ mu
        (fun omega : Omega =>
          (((reward omega (i + 1) -
            mean
              (context i
                (History.finiteRewardHistoryOfTrace (reward omega) i))
              ((policy i).action
                (state i
                  (History.finiteRewardHistoryOfTrace (reward omega) i))) :
                Rat) : Real))))
      (fun _omega : Omega => (0 : Real)) := by
  exact
    ConditionalExpectationReward.centeredReward_succ_condExp_eq_zero_of_historyStepKernelFamily_condExpKernel_map_eq_historyFiltrationSucc
      (mOmega := mOmega)
      mu action rewardKernel policy context state hcontext hstate mean
      varianceProxy law reward haction hreward i h_integrable h_kernel_map_eq

example {Omega Context State Action : Type}
    [mOmega : MeasurableSpace Omega] [StandardBorelSpace Omega]
    [MeasurableSpace Context] [MeasurableSpace State]
    [MeasurableSpace Action] [MeasurableSingletonClass Action]
    (mu : MeasureTheory.Measure Omega)
    [MeasureTheory.IsFiniteMeasure mu]
    (action : Omega -> ActionTrace Action)
    (rewardKernel :
      RewardKernel.MarkovRewardKernel (Prod Context Action) Rat)
    (policy : Nat -> Policy.MeasurablePolicy State Action)
    (context : (n : Nat) -> ((j : Finset.Iic n) -> Rat) -> Context)
    (state : (n : Nat) -> ((j : Finset.Iic n) -> Rat) -> State)
    (hcontext : forall n : Nat, Measurable (context n))
    (hstate : forall n : Nat, Measurable (state n))
    (mean : Context -> Action -> Rat)
    (varianceProxy : Context -> Action -> NNReal)
    (law :
      RewardKernel.CenteredRewardKernelLaw rewardKernel mean varianceProxy)
    (reward : Omega -> RewardTrace Rat)
    (haction : forall t : Nat,
      Measurable (fun omega : Omega => action omega t))
    (hreward : forall t : Nat,
      Measurable (fun omega : Omega => reward omega t))
    (i : Nat)
    (c : NNReal)
    (h_centered_meas :
      @Measurable Omega Real mOmega inferInstance
        (fun omega : Omega =>
          (((reward omega (i + 1) -
            mean
              (context i
                (History.finiteRewardHistoryOfTrace (reward omega) i))
              ((policy i).action
                (state i
                  (History.finiteRewardHistoryOfTrace (reward omega) i))) :
                Rat) : Real))))
    (h_integrable_exp :
      forall t : Real,
        MeasureTheory.Integrable
          (fun omega : Omega =>
            Real.exp (t *
              (((reward omega (i + 1) -
                mean
                  (context i
                    (History.finiteRewardHistoryOfTrace (reward omega) i))
                  ((policy i).action
                    (state i
                      (History.finiteRewardHistoryOfTrace (reward omega) i))) :
                    Rat) : Real)))) mu)
    (h_kernel_map_eq :
      Filter.Eventually
        (fun omega : Omega =>
          @MeasureTheory.Measure.map Omega Rat mOmega inferInstance
            (fun y : Omega => reward y (i + 1))
            (@ProbabilityTheory.condExpKernel Omega mOmega _ mu _
              ((History.historyFiltrationSucc action reward haction hreward) i)
              omega) =
          RewardKernel.historyStepKernelFamily rewardKernel policy context state
            hcontext hstate i
            (History.finiteRewardHistoryOfTrace (reward omega) i))
        (MeasureTheory.ae
          (mu.trim
            ((History.historyFiltrationSucc action reward haction hreward).le
              i))))
    (h_variance_le :
      Filter.Eventually
        (fun omega : Omega =>
          varianceProxy
              (context i
                (History.finiteRewardHistoryOfTrace (reward omega) i))
              ((policy i).action
                (state i
                  (History.finiteRewardHistoryOfTrace (reward omega) i))) <=
            c)
        (MeasureTheory.ae
          (mu.trim
            ((History.historyFiltrationSucc action reward haction hreward).le
              i)))) :
    ProbabilityTheory.HasCondSubgaussianMGF
      ((History.historyFiltrationSucc action reward haction hreward) i)
      ((History.historyFiltrationSucc action reward haction hreward).le i)
      (fun omega : Omega =>
        (((reward omega (i + 1) -
          mean
            (context i
              (History.finiteRewardHistoryOfTrace (reward omega) i))
            ((policy i).action
              (state i
                (History.finiteRewardHistoryOfTrace (reward omega) i))) :
            Rat) : Real)))
      c mu := by
  exact
    ConditionalExpectationReward.centeredReward_succ_hasCondSubgaussianMGF_of_historyStepKernelFamily_condExpKernel_map_eq_historyFiltrationSucc
      (mOmega := mOmega)
      mu action rewardKernel policy context state hcontext hstate mean
      varianceProxy law reward haction hreward i c h_centered_meas
      h_integrable_exp h_kernel_map_eq h_variance_le

example {Omega Context State Action : Type}
    [mOmega : MeasurableSpace Omega] [StandardBorelSpace Omega]
    [MeasurableSpace Context] [MeasurableSpace State]
    [MeasurableSpace Action] [MeasurableSingletonClass Action]
    (mu : MeasureTheory.Measure Omega)
    [MeasureTheory.IsFiniteMeasure mu]
    (action : Omega -> ActionTrace Action)
    (rewardKernel :
      RewardKernel.MarkovRewardKernel (Prod Context Action) Rat)
    (policy : Nat -> Policy.MeasurablePolicy State Action)
    (context : (n : Nat) -> ((j : Finset.Iic n) -> Rat) -> Context)
    (state : (n : Nat) -> ((j : Finset.Iic n) -> Rat) -> State)
    (hcontext : forall n : Nat, Measurable (context n))
    (hstate : forall n : Nat, Measurable (state n))
    (mean : Context -> Action -> Rat)
    (varianceProxy : Context -> Action -> NNReal)
    (hmean :
      Measurable (fun pair : Prod Context Action => mean pair.1 pair.2))
    (hkernel :
      RewardKernel.CenteredRewardKernelLaw rewardKernel mean varianceProxy)
    (reward : Omega -> RewardTrace Rat)
    (haction : forall t : Nat,
      Measurable (fun omega : Omega => action omega t))
    (hreward : forall t : Nat,
      Measurable (fun omega : Omega => reward omega t))
    (rewardLo rewardHi meanLo meanHi : Nat -> Real)
    (hraw :
      forall i : Nat, forall omega : Omega,
        Set.Icc (rewardLo i) (rewardHi i)
          (((reward omega (i + 1) : Rat) : Real)))
    (hmean_range :
      forall i : Nat, forall context : Context, forall action : Action,
        Set.Icc (meanLo i) (meanHi i)
          (((mean context action : Rat) : Real)))
    (i : Nat)
    (h_kernel_map_eq :
      Filter.Eventually
        (fun omega : Omega =>
          @MeasureTheory.Measure.map Omega Rat mOmega inferInstance
            (fun y : Omega => reward y (i + 1))
            (@ProbabilityTheory.condExpKernel Omega mOmega _ mu _
              ((History.historyFiltrationSucc action reward haction hreward) i)
              omega) =
          RewardKernel.historyStepKernelFamily rewardKernel policy context state
            hcontext hstate i
            (History.finiteRewardHistoryOfTrace (reward omega) i))
        (MeasureTheory.ae
          (mu.trim
            ((History.historyFiltrationSucc action reward haction hreward).le
              i)))) :
    Filter.EventuallyEq (MeasureTheory.ae mu)
      (@MeasureTheory.condExp Omega Real
        ((History.historyFiltrationSucc action reward haction hreward) i)
        mOmega _ _ _ mu
        (fun omega : Omega =>
          (((reward omega (i + 1) -
            mean
              (context i
                (History.finiteRewardHistoryOfTrace (reward omega) i))
              ((policy i).action
                (state i
                  (History.finiteRewardHistoryOfTrace (reward omega) i))) :
            Rat) : Real))))
      (fun _omega : Omega => (0 : Real)) := by
  exact
    ConditionalExpectationReward.centeredReward_succ_condExp_eq_zero_of_historyStepKernelFamily_condExpKernel_map_eq_historyFiltrationSucc_rawRangeMeasurableMeanRangeBounded
      (mOmega := mOmega)
      mu action rewardKernel policy context state hcontext hstate mean
      varianceProxy hmean hkernel reward haction hreward rewardLo rewardHi
      meanLo meanHi hraw hmean_range i h_kernel_map_eq

example {Omega Context State Action : Type}
    [mOmega : MeasurableSpace Omega] [StandardBorelSpace Omega]
    [MeasurableSpace Context] [MeasurableSpace State]
    [MeasurableSpace Action]
    (mu : MeasureTheory.Measure Omega)
    [MeasureTheory.IsFiniteMeasure mu]
    (F : MeasureTheory.Filtration Nat mOmega)
    (rewardKernel :
      RewardKernel.MarkovRewardKernel (Prod Context Action) Rat)
    (policy : Nat -> Policy.MeasurablePolicy State Action)
    (context : (n : Nat) -> ((j : Finset.Iic n) -> Rat) -> Context)
    (state : (n : Nat) -> ((j : Finset.Iic n) -> Rat) -> State)
    (hcontext : forall n : Nat, Measurable (context n))
    (hstate : forall n : Nat, Measurable (state n))
    (pairContext :
      (n : Nat) -> ((j : Finset.Iic n) -> Prod Action Rat) -> Context)
    (pairState :
      (n : Nat) -> ((j : Finset.Iic n) -> Prod Action Rat) -> State)
    (hpairContext : forall n : Nat, Measurable (pairContext n))
    (hpairState : forall n : Nat, Measurable (pairState n))
    (mean : Context -> Action -> Rat)
    (varianceProxy : Context -> Action -> NNReal)
    (law :
      RewardKernel.CenteredRewardKernelLaw rewardKernel mean varianceProxy)
    (action : Omega -> ActionTrace Action)
    (reward : Omega -> RewardTrace Rat)
    (i : Nat)
    (pairHistory : Omega -> ((j : Finset.Iic i) -> Prod Action Rat))
    (h_action_next :
      @Measurable Omega Action mOmega inferInstance
        (fun omega : Omega => action omega (i + 1)))
    (h_reward_next :
      @Measurable Omega Rat mOmega inferInstance
        (fun omega : Omega => reward omega (i + 1)))
    (h_prefix_meas :
      forall j : Finset.Iic i,
        @Measurable Omega Rat (F i) inferInstance
          (fun omega : Omega => reward omega j.1))
    (h_pair_context_eq :
      forall omega : Omega,
        pairContext i (pairHistory omega) =
          context i (History.finiteRewardHistoryOfTrace (reward omega) i))
    (h_pair_state_eq :
      forall omega : Omega,
        pairState i (pairHistory omega) =
          state i (History.finiteRewardHistoryOfTrace (reward omega) i))
    (h_integrable :
      MeasureTheory.Integrable
        (fun omega : Omega =>
          (((reward omega (i + 1) -
            mean
              (context i
                (History.finiteRewardHistoryOfTrace (reward omega) i))
              ((policy i).action
                (state i
                  (History.finiteRewardHistoryOfTrace (reward omega) i))) :
                Rat) : Real))) mu)
    (h_kernel_pair_map_eq :
      Filter.Eventually
        (fun omega : Omega =>
          @MeasureTheory.Measure.map Omega (Prod Action Rat) mOmega
            inferInstance
            (fun y : Omega => (action y (i + 1), reward y (i + 1)))
            (@ProbabilityTheory.condExpKernel Omega mOmega _ mu _ (F i)
              omega) =
          RewardKernel.actionRewardHistoryStepKernelFamily rewardKernel policy
            pairContext pairState hpairContext hpairState i
            (pairHistory omega))
        (MeasureTheory.ae (mu.trim (F.le i)))) :
    Filter.EventuallyEq (MeasureTheory.ae mu)
      (@MeasureTheory.condExp Omega Real (F i) mOmega _ _ _ mu
        (fun omega : Omega =>
          (((reward omega (i + 1) -
            mean
              (context i
                (History.finiteRewardHistoryOfTrace (reward omega) i))
              ((policy i).action
                (state i
                  (History.finiteRewardHistoryOfTrace (reward omega) i))) :
                Rat) : Real))))
      (fun _omega : Omega => (0 : Real)) := by
  exact
    ConditionalExpectationReward.centeredReward_succ_condExp_eq_zero_of_actionRewardHistoryStepKernelFamily_pair_map_eq_of_coordinate_measurable
      (mOmega := mOmega)
      mu F rewardKernel policy context state hcontext hstate pairContext
      pairState hpairContext hpairState mean varianceProxy law action reward i
      pairHistory h_action_next h_reward_next h_prefix_meas h_pair_context_eq
      h_pair_state_eq h_integrable h_kernel_pair_map_eq

example {Omega Context State Action : Type}
    [mOmega : MeasurableSpace Omega] [StandardBorelSpace Omega]
    [MeasurableSpace Context] [MeasurableSpace State]
    [MeasurableSpace Action]
    (mu : MeasureTheory.Measure Omega)
    [MeasureTheory.IsFiniteMeasure mu]
    (F : MeasureTheory.Filtration Nat mOmega)
    (rewardKernel :
      RewardKernel.MarkovRewardKernel (Prod Context Action) Rat)
    (policy : Nat -> Policy.MeasurablePolicy State Action)
    (context : (n : Nat) -> ((j : Finset.Iic n) -> Rat) -> Context)
    (state : (n : Nat) -> ((j : Finset.Iic n) -> Rat) -> State)
    (hcontext : forall n : Nat, Measurable (context n))
    (hstate : forall n : Nat, Measurable (state n))
    (pairContext :
      (n : Nat) -> ((j : Finset.Iic n) -> Prod Action Rat) -> Context)
    (pairState :
      (n : Nat) -> ((j : Finset.Iic n) -> Prod Action Rat) -> State)
    (hpairContext : forall n : Nat, Measurable (pairContext n))
    (hpairState : forall n : Nat, Measurable (pairState n))
    (mean : Context -> Action -> Rat)
    (varianceProxy : Context -> Action -> NNReal)
    (hmean :
      Measurable (fun pair : Prod Context Action => mean pair.1 pair.2))
    (hkernel :
      RewardKernel.CenteredRewardKernelLaw rewardKernel mean varianceProxy)
    (action : Omega -> ActionTrace Action)
    (reward : Omega -> RewardTrace Rat)
    (hreward : forall t : Nat,
      @Measurable Omega Rat mOmega inferInstance
        (fun omega : Omega => reward omega t))
    (rewardLo rewardHi meanLo meanHi : Nat -> Real)
    (hraw :
      forall i : Nat, forall omega : Omega,
        Set.Icc (rewardLo i) (rewardHi i)
          (((reward omega (i + 1) : Rat) : Real)))
    (hmean_range :
      forall i : Nat, forall context : Context, forall action : Action,
        Set.Icc (meanLo i) (meanHi i)
          (((mean context action : Rat) : Real)))
    (i : Nat)
    (pairHistory : Omega -> ((j : Finset.Iic i) -> Prod Action Rat))
    (h_action_next :
      @Measurable Omega Action mOmega inferInstance
        (fun omega : Omega => action omega (i + 1)))
    (h_prefix_meas :
      forall j : Finset.Iic i,
        @Measurable Omega Rat (F i) inferInstance
          (fun omega : Omega => reward omega j.1))
    (h_pair_context_eq :
      forall omega : Omega,
        pairContext i (pairHistory omega) =
          context i (History.finiteRewardHistoryOfTrace (reward omega) i))
    (h_pair_state_eq :
      forall omega : Omega,
        pairState i (pairHistory omega) =
          state i (History.finiteRewardHistoryOfTrace (reward omega) i))
    (h_kernel_pair_map_eq :
      Filter.Eventually
        (fun omega : Omega =>
          @MeasureTheory.Measure.map Omega (Prod Action Rat) mOmega
            inferInstance
            (fun y : Omega => (action y (i + 1), reward y (i + 1)))
            (@ProbabilityTheory.condExpKernel Omega mOmega _ mu _ (F i)
              omega) =
          RewardKernel.actionRewardHistoryStepKernelFamily rewardKernel policy
            pairContext pairState hpairContext hpairState i
            (pairHistory omega))
        (MeasureTheory.ae (mu.trim (F.le i)))) :
    Filter.EventuallyEq (MeasureTheory.ae mu)
      (@MeasureTheory.condExp Omega Real (F i) mOmega _ _ _ mu
        (fun omega : Omega =>
          (((reward omega (i + 1) -
            mean
              (context i
                (History.finiteRewardHistoryOfTrace (reward omega) i))
              ((policy i).action
                (state i
                  (History.finiteRewardHistoryOfTrace (reward omega) i))) :
            Rat) : Real))))
      (fun _omega : Omega => (0 : Real)) := by
  exact
    ConditionalExpectationReward.centeredReward_succ_condExp_eq_zero_of_actionRewardHistoryStepKernelFamily_pair_map_eq_of_coordinate_measurable_rawRangeMeasurableMeanRangeBounded
      (mOmega := mOmega)
      mu F rewardKernel policy context state hcontext hstate pairContext
      pairState hpairContext hpairState mean varianceProxy hmean hkernel action
      reward hreward rewardLo rewardHi meanLo meanHi hraw hmean_range i
      pairHistory h_action_next h_prefix_meas h_pair_context_eq
      h_pair_state_eq h_kernel_pair_map_eq

example {Omega Context State Action : Type}
    [mOmega : MeasurableSpace Omega] [StandardBorelSpace Omega]
    [MeasurableSpace Context] [MeasurableSpace State]
    [MeasurableSpace Action] [MeasurableSingletonClass Action]
    (mu : MeasureTheory.Measure Omega)
    [MeasureTheory.IsFiniteMeasure mu]
    (rewardKernel :
      RewardKernel.MarkovRewardKernel (Prod Context Action) Rat)
    (policy : Nat -> Policy.MeasurablePolicy State Action)
    (context : (n : Nat) -> ((j : Finset.Iic n) -> Rat) -> Context)
    (state : (n : Nat) -> ((j : Finset.Iic n) -> Rat) -> State)
    (hcontext : forall n : Nat, Measurable (context n))
    (hstate : forall n : Nat, Measurable (state n))
    (pairContext :
      (n : Nat) -> ((j : Finset.Iic n) -> Prod Action Rat) -> Context)
    (pairState :
      (n : Nat) -> ((j : Finset.Iic n) -> Prod Action Rat) -> State)
    (hpairContext : forall n : Nat, Measurable (pairContext n))
    (hpairState : forall n : Nat, Measurable (pairState n))
    (mean : Context -> Action -> Rat)
    (varianceProxy : Context -> Action -> NNReal)
    (law :
      RewardKernel.CenteredRewardKernelLaw rewardKernel mean varianceProxy)
    (action : Omega -> ActionTrace Action)
    (reward : Omega -> RewardTrace Rat)
    (haction : forall t : Nat,
      @Measurable Omega Action mOmega inferInstance
        (fun omega : Omega => action omega t))
    (hreward : forall t : Nat,
      @Measurable Omega Rat mOmega inferInstance
        (fun omega : Omega => reward omega t))
    (i : Nat)
    (pairHistory : Omega -> ((j : Finset.Iic i) -> Prod Action Rat))
    (h_pair_context_eq :
      forall omega : Omega,
        pairContext i (pairHistory omega) =
          context i (History.finiteRewardHistoryOfTrace (reward omega) i))
    (h_pair_state_eq :
      forall omega : Omega,
        pairState i (pairHistory omega) =
          state i (History.finiteRewardHistoryOfTrace (reward omega) i))
    (h_integrable :
      MeasureTheory.Integrable
        (fun omega : Omega =>
          (((reward omega (i + 1) -
            mean
              (context i
                (History.finiteRewardHistoryOfTrace (reward omega) i))
              ((policy i).action
                (state i
                  (History.finiteRewardHistoryOfTrace (reward omega) i))) :
                Rat) : Real))) mu)
    (h_kernel_pair_map_eq :
      Filter.Eventually
        (fun omega : Omega =>
          @MeasureTheory.Measure.map Omega (Prod Action Rat) mOmega
            inferInstance
            (fun y : Omega => (action y (i + 1), reward y (i + 1)))
            (@ProbabilityTheory.condExpKernel Omega mOmega _ mu _
              ((History.historyFiltrationSucc action reward haction hreward) i)
              omega) =
          RewardKernel.actionRewardHistoryStepKernelFamily rewardKernel policy
            pairContext pairState hpairContext hpairState i
            (pairHistory omega))
        (MeasureTheory.ae
          (mu.trim
            ((History.historyFiltrationSucc action reward haction hreward).le
              i)))) :
    Filter.EventuallyEq (MeasureTheory.ae mu)
      (@MeasureTheory.condExp Omega Real
        ((History.historyFiltrationSucc action reward haction hreward) i)
        mOmega _ _ _ mu
        (fun omega : Omega =>
          (((reward omega (i + 1) -
            mean
              (context i
                (History.finiteRewardHistoryOfTrace (reward omega) i))
              ((policy i).action
                (state i
                  (History.finiteRewardHistoryOfTrace (reward omega) i))) :
                Rat) : Real))))
      (fun _omega : Omega => (0 : Real)) := by
  exact
    ConditionalExpectationReward.centeredReward_succ_condExp_eq_zero_of_actionRewardHistoryStepKernelFamily_pair_map_eq_historyFiltrationSucc
      (mOmega := mOmega)
      mu action rewardKernel policy context state hcontext hstate pairContext
      pairState hpairContext hpairState mean varianceProxy law reward haction
      hreward i pairHistory h_pair_context_eq h_pair_state_eq h_integrable
      h_kernel_pair_map_eq

example {Omega Context State Action : Type}
    [mOmega : MeasurableSpace Omega] [StandardBorelSpace Omega]
    [MeasurableSpace Context] [MeasurableSpace State]
    [MeasurableSpace Action] [MeasurableSingletonClass Action]
    (mu : MeasureTheory.Measure Omega)
    [MeasureTheory.IsFiniteMeasure mu]
    (rewardKernel :
      RewardKernel.MarkovRewardKernel (Prod Context Action) Rat)
    (policy : Nat -> Policy.MeasurablePolicy State Action)
    (context : (n : Nat) -> ((j : Finset.Iic n) -> Rat) -> Context)
    (state : (n : Nat) -> ((j : Finset.Iic n) -> Rat) -> State)
    (hcontext : forall n : Nat, Measurable (context n))
    (hstate : forall n : Nat, Measurable (state n))
    (pairContext :
      (n : Nat) -> ((j : Finset.Iic n) -> Prod Action Rat) -> Context)
    (pairState :
      (n : Nat) -> ((j : Finset.Iic n) -> Prod Action Rat) -> State)
    (hpairContext : forall n : Nat, Measurable (pairContext n))
    (hpairState : forall n : Nat, Measurable (pairState n))
    (mean : Context -> Action -> Rat)
    (varianceProxy : Context -> Action -> NNReal)
    (hmean :
      Measurable (fun pair : Prod Context Action => mean pair.1 pair.2))
    (hkernel :
      RewardKernel.CenteredRewardKernelLaw rewardKernel mean varianceProxy)
    (action : Omega -> ActionTrace Action)
    (reward : Omega -> RewardTrace Rat)
    (haction : forall t : Nat,
      @Measurable Omega Action mOmega inferInstance
        (fun omega : Omega => action omega t))
    (hreward : forall t : Nat,
      @Measurable Omega Rat mOmega inferInstance
        (fun omega : Omega => reward omega t))
    (rewardLo rewardHi meanLo meanHi : Nat -> Real)
    (hraw :
      forall i : Nat, forall omega : Omega,
        Set.Icc (rewardLo i) (rewardHi i)
          (((reward omega (i + 1) : Rat) : Real)))
    (hmean_range :
      forall i : Nat, forall context : Context, forall action : Action,
        Set.Icc (meanLo i) (meanHi i)
          (((mean context action : Rat) : Real)))
    (i : Nat)
    (pairHistory : Omega -> ((j : Finset.Iic i) -> Prod Action Rat))
    (h_pair_context_eq :
      forall omega : Omega,
        pairContext i (pairHistory omega) =
          context i (History.finiteRewardHistoryOfTrace (reward omega) i))
    (h_pair_state_eq :
      forall omega : Omega,
        pairState i (pairHistory omega) =
          state i (History.finiteRewardHistoryOfTrace (reward omega) i))
    (h_kernel_pair_map_eq :
      Filter.Eventually
        (fun omega : Omega =>
          @MeasureTheory.Measure.map Omega (Prod Action Rat) mOmega
            inferInstance
            (fun y : Omega => (action y (i + 1), reward y (i + 1)))
            (@ProbabilityTheory.condExpKernel Omega mOmega _ mu _
              ((History.historyFiltrationSucc action reward haction hreward) i)
              omega) =
          RewardKernel.actionRewardHistoryStepKernelFamily rewardKernel policy
            pairContext pairState hpairContext hpairState i
            (pairHistory omega))
        (MeasureTheory.ae
          (mu.trim
            ((History.historyFiltrationSucc action reward haction hreward).le
              i)))) :
    Filter.EventuallyEq (MeasureTheory.ae mu)
      (@MeasureTheory.condExp Omega Real
        ((History.historyFiltrationSucc action reward haction hreward) i)
        mOmega _ _ _ mu
        (fun omega : Omega =>
          (((reward omega (i + 1) -
            mean
              (context i
                (History.finiteRewardHistoryOfTrace (reward omega) i))
              ((policy i).action
                (state i
                  (History.finiteRewardHistoryOfTrace (reward omega) i))) :
                Rat) : Real))))
      (fun _omega : Omega => (0 : Real)) := by
  exact
    ConditionalExpectationReward.centeredReward_succ_condExp_eq_zero_of_actionRewardHistoryStepKernelFamily_pair_map_eq_historyFiltrationSucc_rawRangeMeasurableMeanRangeBounded
      (mOmega := mOmega)
      mu action rewardKernel policy context state hcontext hstate pairContext
      pairState hpairContext hpairState mean varianceProxy hmean hkernel reward
      haction hreward rewardLo rewardHi meanLo meanHi hraw hmean_range i
      pairHistory h_pair_context_eq h_pair_state_eq h_kernel_pair_map_eq

example {Omega Context State Action : Type}
    [mOmega : MeasurableSpace Omega] [StandardBorelSpace Omega]
    [MeasurableSpace Context] [MeasurableSpace State]
    [MeasurableSpace Action] [MeasurableSingletonClass Action]
    (mu : MeasureTheory.Measure Omega)
    [MeasureTheory.IsFiniteMeasure mu]
    (rewardKernel :
      RewardKernel.MarkovRewardKernel (Prod Context Action) Rat)
    (policy : Nat -> Policy.MeasurablePolicy State Action)
    (context : (n : Nat) -> ((j : Finset.Iic n) -> Rat) -> Context)
    (state : (n : Nat) -> ((j : Finset.Iic n) -> Rat) -> State)
    (hcontext : forall n : Nat, Measurable (context n))
    (hstate : forall n : Nat, Measurable (state n))
    (hpairContext :
      forall n : Nat,
        Measurable
          (fun history : (j : Finset.Iic n) -> Prod Action Rat =>
            context n (fun j : Finset.Iic n => (history j).2)))
    (hpairState :
      forall n : Nat,
        Measurable
          (fun history : (j : Finset.Iic n) -> Prod Action Rat =>
            state n (fun j : Finset.Iic n => (history j).2)))
    (mean : Context -> Action -> Rat)
    (varianceProxy : Context -> Action -> NNReal)
    (law :
      RewardKernel.CenteredRewardKernelLaw rewardKernel mean varianceProxy)
    (action : Omega -> ActionTrace Action)
    (reward : Omega -> RewardTrace Rat)
    (haction : forall t : Nat,
      @Measurable Omega Action mOmega inferInstance
        (fun omega : Omega => action omega t))
    (hreward : forall t : Nat,
      @Measurable Omega Rat mOmega inferInstance
        (fun omega : Omega => reward omega t))
    (i : Nat)
    (h_integrable :
      MeasureTheory.Integrable
        (fun omega : Omega =>
          (((reward omega (i + 1) -
            mean
              (context i
                (History.finiteRewardHistoryOfTrace (reward omega) i))
              ((policy i).action
                (state i
                  (History.finiteRewardHistoryOfTrace (reward omega) i))) :
                Rat) : Real))) mu)
    (h_kernel_pair_map_eq :
      Filter.Eventually
        (fun omega : Omega =>
          @MeasureTheory.Measure.map Omega (Prod Action Rat) mOmega
            inferInstance
            (fun y : Omega => (action y (i + 1), reward y (i + 1)))
            (@ProbabilityTheory.condExpKernel Omega mOmega _ mu _
              ((History.historyFiltrationSucc action reward haction hreward) i)
              omega) =
          RewardKernel.actionRewardHistoryStepKernelFamily rewardKernel policy
            (fun n history =>
              context n (fun j : Finset.Iic n => (history j).2))
            (fun n history =>
              state n (fun j : Finset.Iic n => (history j).2))
            hpairContext hpairState i
            (fun j : Finset.Iic i =>
              (action omega j.1, reward omega j.1)))
        (MeasureTheory.ae
          (mu.trim
            ((History.historyFiltrationSucc action reward haction hreward).le
              i)))) :
    Filter.EventuallyEq (MeasureTheory.ae mu)
      (@MeasureTheory.condExp Omega Real
        ((History.historyFiltrationSucc action reward haction hreward) i)
        mOmega _ _ _ mu
        (fun omega : Omega =>
          (((reward omega (i + 1) -
            mean
              (context i
                (History.finiteRewardHistoryOfTrace (reward omega) i))
              ((policy i).action
                (state i
                  (History.finiteRewardHistoryOfTrace (reward omega) i))) :
                Rat) : Real))))
      (fun _omega : Omega => (0 : Real)) := by
  exact
    ConditionalExpectationReward.centeredReward_succ_condExp_eq_zero_of_actionRewardHistoryStepKernelFamily_pair_map_eq_historyFiltrationSucc_projected
      (mOmega := mOmega)
      mu action rewardKernel policy context state hcontext hstate hpairContext
      hpairState mean varianceProxy law reward haction hreward i h_integrable
      h_kernel_pair_map_eq

example {Omega Context State Action : Type}
    [mOmega : MeasurableSpace Omega] [StandardBorelSpace Omega]
    [MeasurableSpace Context] [MeasurableSpace State]
    [MeasurableSpace Action] [MeasurableSingletonClass Action]
    (mu : MeasureTheory.Measure Omega)
    [MeasureTheory.IsFiniteMeasure mu]
    (rewardKernel :
      RewardKernel.MarkovRewardKernel (Prod Context Action) Rat)
    (policy : Nat -> Policy.MeasurablePolicy State Action)
    (context : (n : Nat) -> ((j : Finset.Iic n) -> Rat) -> Context)
    (state : (n : Nat) -> ((j : Finset.Iic n) -> Rat) -> State)
    (hcontext : forall n : Nat, Measurable (context n))
    (hstate : forall n : Nat, Measurable (state n))
    (hpairContext :
      forall n : Nat,
        Measurable
          (fun history : (j : Finset.Iic n) -> Prod Action Rat =>
            context n (fun j : Finset.Iic n => (history j).2)))
    (hpairState :
      forall n : Nat,
        Measurable
          (fun history : (j : Finset.Iic n) -> Prod Action Rat =>
            state n (fun j : Finset.Iic n => (history j).2)))
    (mean : Context -> Action -> Rat)
    (varianceProxy : Context -> Action -> NNReal)
    (hmean :
      Measurable (fun pair : Prod Context Action => mean pair.1 pair.2))
    (hkernel :
      RewardKernel.CenteredRewardKernelLaw rewardKernel mean varianceProxy)
    (action : Omega -> ActionTrace Action)
    (reward : Omega -> RewardTrace Rat)
    (haction : forall t : Nat,
      @Measurable Omega Action mOmega inferInstance
        (fun omega : Omega => action omega t))
    (hreward : forall t : Nat,
      @Measurable Omega Rat mOmega inferInstance
        (fun omega : Omega => reward omega t))
    (rewardLo rewardHi meanLo meanHi : Nat -> Real)
    (hraw :
      forall i : Nat, forall omega : Omega,
        Set.Icc (rewardLo i) (rewardHi i)
          (((reward omega (i + 1) : Rat) : Real)))
    (hmean_range :
      forall i : Nat, forall context : Context, forall action : Action,
        Set.Icc (meanLo i) (meanHi i)
          (((mean context action : Rat) : Real)))
    (i : Nat)
    (h_kernel_pair_map_eq :
      Filter.Eventually
        (fun omega : Omega =>
          @MeasureTheory.Measure.map Omega (Prod Action Rat) mOmega
            inferInstance
            (fun y : Omega => (action y (i + 1), reward y (i + 1)))
            (@ProbabilityTheory.condExpKernel Omega mOmega _ mu _
              ((History.historyFiltrationSucc action reward haction hreward) i)
              omega) =
          RewardKernel.actionRewardHistoryStepKernelFamily rewardKernel policy
            (fun n history =>
              context n (fun j : Finset.Iic n => (history j).2))
            (fun n history =>
              state n (fun j : Finset.Iic n => (history j).2))
            hpairContext hpairState i
            (fun j : Finset.Iic i =>
              (action omega j.1, reward omega j.1)))
        (MeasureTheory.ae
          (mu.trim
            ((History.historyFiltrationSucc action reward haction hreward).le
              i)))) :
    Filter.EventuallyEq (MeasureTheory.ae mu)
      (@MeasureTheory.condExp Omega Real
        ((History.historyFiltrationSucc action reward haction hreward) i)
        mOmega _ _ _ mu
        (fun omega : Omega =>
          (((reward omega (i + 1) -
            mean
              (context i
                (History.finiteRewardHistoryOfTrace (reward omega) i))
              ((policy i).action
                (state i
                  (History.finiteRewardHistoryOfTrace (reward omega) i))) :
                Rat) : Real))))
      (fun _omega : Omega => (0 : Real)) := by
  exact
    ConditionalExpectationReward.centeredReward_succ_condExp_eq_zero_of_actionRewardHistoryStepKernelFamily_pair_map_eq_historyFiltrationSucc_projected_rawRangeMeasurableMeanRangeBounded
      (mOmega := mOmega)
      mu action rewardKernel policy context state hcontext hstate hpairContext
      hpairState mean varianceProxy hmean hkernel reward haction hreward
      rewardLo rewardHi meanLo meanHi hraw hmean_range i
      h_kernel_pair_map_eq

example {Omega Context State Action : Type}
    [mOmega : MeasurableSpace Omega] [StandardBorelSpace Omega]
    [MeasurableSpace Context] [MeasurableSpace State]
    [MeasurableSpace Action] [MeasurableSingletonClass Action]
    (mu : MeasureTheory.Measure Omega)
    [MeasureTheory.IsFiniteMeasure mu]
    (rewardKernel :
      RewardKernel.MarkovRewardKernel (Prod Context Action) Rat)
    (policy : Nat -> Policy.MeasurablePolicy State Action)
    (context : (n : Nat) -> ((j : Finset.Iic n) -> Rat) -> Context)
    (state : (n : Nat) -> ((j : Finset.Iic n) -> Rat) -> State)
    (hcontext : forall n : Nat, Measurable (context n))
    (hstate : forall n : Nat, Measurable (state n))
    (mean : Context -> Action -> Rat)
    (varianceProxy : Context -> Action -> NNReal)
    (law :
      RewardKernel.CenteredRewardKernelLaw rewardKernel mean varianceProxy)
    (action : Omega -> ActionTrace Action)
    (reward : Omega -> RewardTrace Rat)
    (haction : forall t : Nat,
      @Measurable Omega Action mOmega inferInstance
        (fun omega : Omega => action omega t))
    (hreward : forall t : Nat,
      @Measurable Omega Rat mOmega inferInstance
        (fun omega : Omega => reward omega t))
    (i : Nat)
    (h_integrable :
      MeasureTheory.Integrable
        (fun omega : Omega =>
          (((reward omega (i + 1) -
            mean
              (context i
                (History.finiteRewardHistoryOfTrace (reward omega) i))
              ((policy i).action
                (state i
                  (History.finiteRewardHistoryOfTrace (reward omega) i))) :
                Rat) : Real))) mu)
    (h_kernel_pair_map_eq :
      Filter.Eventually
        (fun omega : Omega =>
          @MeasureTheory.Measure.map Omega (Prod Action Rat) mOmega
            inferInstance
            (fun y : Omega => (action y (i + 1), reward y (i + 1)))
            (@ProbabilityTheory.condExpKernel Omega mOmega _ mu _
              ((History.historyFiltrationSucc action reward haction hreward) i)
              omega) =
          RewardKernel.actionRewardHistoryStepKernelFamily rewardKernel policy
            (fun n history =>
              context n (History.pairHistoryRewardProjection history))
            (fun n history =>
              state n (History.pairHistoryRewardProjection history))
            (fun n : Nat =>
              (hcontext n).comp
                (History.measurable_pairHistoryRewardProjection
                  (Action := Action) (Reward := Rat) n))
            (fun n : Nat =>
              (hstate n).comp
                (History.measurable_pairHistoryRewardProjection
                  (Action := Action) (Reward := Rat) n))
            i
            (fun j : Finset.Iic i =>
              (action omega j.1, reward omega j.1)))
        (MeasureTheory.ae
          (mu.trim
            ((History.historyFiltrationSucc action reward haction hreward).le
              i)))) :
    Filter.EventuallyEq (MeasureTheory.ae mu)
      (@MeasureTheory.condExp Omega Real
        ((History.historyFiltrationSucc action reward haction hreward) i)
        mOmega _ _ _ mu
        (fun omega : Omega =>
          (((reward omega (i + 1) -
            mean
              (context i
                (History.finiteRewardHistoryOfTrace (reward omega) i))
              ((policy i).action
                (state i
                  (History.finiteRewardHistoryOfTrace (reward omega) i))) :
                Rat) : Real))))
      (fun _omega : Omega => (0 : Real)) := by
  exact
    ConditionalExpectationReward.centeredReward_succ_condExp_eq_zero_of_actionRewardHistoryStepKernelFamily_pair_map_eq_historyFiltrationSucc_projected_of_context_state_measurable
      (mOmega := mOmega)
      mu action rewardKernel policy context state hcontext hstate mean
      varianceProxy law reward haction hreward i h_integrable
      h_kernel_pair_map_eq

example {Omega Context State Action : Type}
    [mOmega : MeasurableSpace Omega] [StandardBorelSpace Omega]
    [MeasurableSpace Context] [MeasurableSpace State]
    [MeasurableSpace Action] [MeasurableSingletonClass Action]
    (mu : MeasureTheory.Measure Omega)
    [MeasureTheory.IsFiniteMeasure mu]
    (rewardKernel :
      RewardKernel.MarkovRewardKernel (Prod Context Action) Rat)
    (policy : Nat -> Policy.MeasurablePolicy State Action)
    (context : (n : Nat) -> ((j : Finset.Iic n) -> Rat) -> Context)
    (state : (n : Nat) -> ((j : Finset.Iic n) -> Rat) -> State)
    (hcontext : forall n : Nat, Measurable (context n))
    (hstate : forall n : Nat, Measurable (state n))
    (mean : Context -> Action -> Rat)
    (varianceProxy : Context -> Action -> NNReal)
    (hmean :
      Measurable (fun pair : Prod Context Action => mean pair.1 pair.2))
    (hkernel :
      RewardKernel.CenteredRewardKernelLaw rewardKernel mean varianceProxy)
    (action : Omega -> ActionTrace Action)
    (reward : Omega -> RewardTrace Rat)
    (haction : forall t : Nat,
      @Measurable Omega Action mOmega inferInstance
        (fun omega : Omega => action omega t))
    (hreward : forall t : Nat,
      @Measurable Omega Rat mOmega inferInstance
        (fun omega : Omega => reward omega t))
    (rewardLo rewardHi meanLo meanHi : Nat -> Real)
    (hraw :
      forall i : Nat, forall omega : Omega,
        Set.Icc (rewardLo i) (rewardHi i)
          (((reward omega (i + 1) : Rat) : Real)))
    (hmean_range :
      forall i : Nat, forall context : Context, forall action : Action,
        Set.Icc (meanLo i) (meanHi i)
          (((mean context action : Rat) : Real)))
    (i : Nat)
    (h_kernel_pair_map_eq :
      Filter.Eventually
        (fun omega : Omega =>
          @MeasureTheory.Measure.map Omega (Prod Action Rat) mOmega
            inferInstance
            (fun y : Omega => (action y (i + 1), reward y (i + 1)))
            (@ProbabilityTheory.condExpKernel Omega mOmega _ mu _
              ((History.historyFiltrationSucc action reward haction hreward) i)
              omega) =
          RewardKernel.actionRewardHistoryStepKernelFamily rewardKernel policy
            (fun n history =>
              context n (History.pairHistoryRewardProjection history))
            (fun n history =>
              state n (History.pairHistoryRewardProjection history))
            (fun n : Nat =>
              (hcontext n).comp
                (History.measurable_pairHistoryRewardProjection
                  (Action := Action) (Reward := Rat) n))
            (fun n : Nat =>
              (hstate n).comp
                (History.measurable_pairHistoryRewardProjection
                  (Action := Action) (Reward := Rat) n))
            i
            (fun j : Finset.Iic i =>
              (action omega j.1, reward omega j.1)))
        (MeasureTheory.ae
          (mu.trim
            ((History.historyFiltrationSucc action reward haction hreward).le
              i)))) :
    Filter.EventuallyEq (MeasureTheory.ae mu)
      (@MeasureTheory.condExp Omega Real
        ((History.historyFiltrationSucc action reward haction hreward) i)
        mOmega _ _ _ mu
        (fun omega : Omega =>
          (((reward omega (i + 1) -
            mean
              (context i
                (History.finiteRewardHistoryOfTrace (reward omega) i))
              ((policy i).action
                (state i
                  (History.finiteRewardHistoryOfTrace (reward omega) i))) :
                Rat) : Real))))
      (fun _omega : Omega => (0 : Real)) := by
  exact
    ConditionalExpectationReward.centeredReward_succ_condExp_eq_zero_of_actionRewardHistoryStepKernelFamily_pair_map_eq_historyFiltrationSucc_projected_of_context_state_measurable_rawRangeMeasurableMeanRangeBounded
      (mOmega := mOmega)
      mu action rewardKernel policy context state hcontext hstate mean
      varianceProxy hmean hkernel reward haction hreward rewardLo rewardHi
      meanLo meanHi hraw hmean_range i h_kernel_pair_map_eq

example {Omega Context State Action : Type}
    [mOmega : MeasurableSpace Omega] [StandardBorelSpace Omega]
    [MeasurableSpace Context] [MeasurableSpace State]
    [MeasurableSpace Action] [MeasurableSingletonClass Action]
    (mu : MeasureTheory.Measure Omega)
    [MeasureTheory.IsFiniteMeasure mu]
    (rewardKernel :
      RewardKernel.MarkovRewardKernel (Prod Context Action) Rat)
    (policy : Nat -> Policy.MeasurablePolicy State Action)
    (context : (n : Nat) -> ((j : Finset.Iic n) -> Rat) -> Context)
    (state : (n : Nat) -> ((j : Finset.Iic n) -> Rat) -> State)
    (hcontext : forall n : Nat, Measurable (context n))
    (hstate : forall n : Nat, Measurable (state n))
    (action : Omega -> ActionTrace Action)
    (reward : Omega -> RewardTrace Rat)
    (haction : forall t : Nat,
      @Measurable Omega Action mOmega inferInstance
        (fun omega : Omega => action omega t))
    (hreward : forall t : Nat,
      @Measurable Omega Rat mOmega inferInstance
        (fun omega : Omega => reward omega t))
    (i : Nat)
    (h_kernel_partialtraj_map_eq :
      Filter.Eventually
        (fun omega : Omega =>
          @MeasureTheory.Measure.map Omega
            ((j : Finset.Iic (i + 1)) -> Prod Action Rat) mOmega
            inferInstance
            (fun y : Omega =>
              History.finitePairHistoryOfTrace
                (action y) (reward y) (i + 1))
            (@ProbabilityTheory.condExpKernel Omega mOmega _ mu _
              ((History.historyFiltrationSucc action reward haction hreward) i)
              omega) =
          RewardKernel.actionRewardPartialTrajectoryKernel rewardKernel policy
            (fun n history =>
              context n (History.pairHistoryRewardProjection history))
            (fun n history =>
              state n (History.pairHistoryRewardProjection history))
            (fun n : Nat =>
              (hcontext n).comp
                (History.measurable_pairHistoryRewardProjection
                  (Action := Action) (Reward := Rat) n))
            (fun n : Nat =>
              (hstate n).comp
                (History.measurable_pairHistoryRewardProjection
                  (Action := Action) (Reward := Rat) n))
            i (i + 1)
            (History.finitePairHistoryOfTrace
              (action omega) (reward omega) i))
        (MeasureTheory.ae
          (mu.trim
            ((History.historyFiltrationSucc action reward haction hreward).le
              i)))) :
    Filter.Eventually
      (fun omega : Omega =>
        @MeasureTheory.Measure.map Omega (Prod Action Rat) mOmega
          inferInstance
          (fun y : Omega => (action y (i + 1), reward y (i + 1)))
          (@ProbabilityTheory.condExpKernel Omega mOmega _ mu _
            ((History.historyFiltrationSucc action reward haction hreward) i)
            omega) =
        RewardKernel.actionRewardHistoryStepKernelFamily rewardKernel policy
          (fun n history =>
            context n (History.pairHistoryRewardProjection history))
          (fun n history =>
            state n (History.pairHistoryRewardProjection history))
          (fun n : Nat =>
            (hcontext n).comp
              (History.measurable_pairHistoryRewardProjection
                (Action := Action) (Reward := Rat) n))
          (fun n : Nat =>
            (hstate n).comp
              (History.measurable_pairHistoryRewardProjection
                (Action := Action) (Reward := Rat) n))
          i
          (History.finitePairHistoryOfTrace
            (action omega) (reward omega) i))
      (MeasureTheory.ae
        (mu.trim
          ((History.historyFiltrationSucc action reward haction hreward).le
            i))) := by
  exact
    ConditionalExpectationReward.actionRewardHistoryStepKernelFamily_pair_map_eq_of_actionRewardPartialTrajectoryKernel_map_eq_historyFiltrationSucc_finitePairHistoryOfTrace
      (mOmega := mOmega)
      mu action rewardKernel policy context state hcontext hstate reward
      haction hreward i h_kernel_partialtraj_map_eq

example {Omega Context State Action : Type}
    [mOmega : MeasurableSpace Omega] [StandardBorelSpace Omega]
    [MeasurableSpace Context] [MeasurableSpace State]
    [MeasurableSpace Action] [MeasurableSingletonClass Action]
    (mu : MeasureTheory.Measure Omega)
    [MeasureTheory.IsFiniteMeasure mu]
    (action : Omega -> ActionTrace Action)
    (rewardKernel :
      RewardKernel.MarkovRewardKernel (Prod Context Action) Rat)
    (policy : Nat -> Policy.MeasurablePolicy State Action)
    (context : (n : Nat) -> ((j : Finset.Iic n) -> Rat) -> Context)
    (state : (n : Nat) -> ((j : Finset.Iic n) -> Rat) -> State)
    (hcontext : forall n : Nat, Measurable (context n))
    (hstate : forall n : Nat, Measurable (state n))
    (defaultAction : Action)
    (reward : Omega -> RewardTrace Rat)
    (haction : forall t : Nat,
      @Measurable Omega Action mOmega inferInstance
        (fun omega : Omega => action omega t))
    (hreward : forall t : Nat,
      @Measurable Omega Rat mOmega inferInstance
        (fun omega : Omega => reward omega t))
    (i : Nat)
    (h_action_generated :
      action =
        Policy.generatedActionTraceSucc policy
          (fun n omega =>
            state n (History.finiteRewardHistoryOfTrace (reward omega) n))
          defaultAction)
    (h_kernel_partialtraj_map_eq :
      Filter.Eventually
        (fun omega : Omega =>
          @MeasureTheory.Measure.map Omega
            ((j : Finset.Iic (i + 1)) -> Prod Action Rat) mOmega
            inferInstance
            (fun y : Omega =>
              History.finitePairHistoryOfTrace
                (action y) (reward y) (i + 1))
            (@ProbabilityTheory.condExpKernel Omega mOmega _ mu _
              ((History.historyFiltrationSucc action reward haction hreward) i)
              omega) =
          RewardKernel.actionRewardPartialTrajectoryKernel rewardKernel policy
            (fun n history =>
              context n (History.pairHistoryRewardProjection history))
            (fun n history =>
              state n (History.pairHistoryRewardProjection history))
            (fun n : Nat =>
              (hcontext n).comp
                (History.measurable_pairHistoryRewardProjection
                  (Action := Action) (Reward := Rat) n))
            (fun n : Nat =>
              (hstate n).comp
                (History.measurable_pairHistoryRewardProjection
                  (Action := Action) (Reward := Rat) n))
            i (i + 1)
            (History.finitePairHistoryOfTrace
              (action omega) (reward omega) i))
        (MeasureTheory.ae
          (mu.trim
            ((History.historyFiltrationSucc action reward haction hreward).le
              i)))) :
    Filter.Eventually
      (fun omega : Omega =>
        @MeasureTheory.Measure.map Omega Rat mOmega inferInstance
          (fun y : Omega => reward y (i + 1))
          (@ProbabilityTheory.condExpKernel Omega mOmega _ mu _
            ((History.historyFiltrationSucc action reward haction hreward) i)
            omega) =
        RewardKernel.selectedMeasure rewardKernel
          (context i (History.finiteRewardHistoryOfTrace (reward omega) i))
          (action omega (i + 1)))
      (MeasureTheory.ae
        (mu.trim
          ((History.historyFiltrationSucc action reward haction hreward).le
            i))) := by
  exact
    ConditionalExpectationReward.reward_condExpKernel_map_eq_selected_actual_action_of_generatedActionTraceSucc_actionRewardPartialTrajectoryKernel_map_eq_historyFiltrationSucc_finitePairHistoryOfTrace
      (mOmega := mOmega)
      mu action rewardKernel policy context state hcontext hstate defaultAction
      reward haction hreward i h_action_generated h_kernel_partialtraj_map_eq

example {Omega Context State Action : Type}
    [mOmega : MeasurableSpace Omega] [StandardBorelSpace Omega]
    [MeasurableSpace Context] [MeasurableSpace State]
    [MeasurableSpace Action] [MeasurableSingletonClass Action]
    (mu : MeasureTheory.Measure Omega)
    [MeasureTheory.IsFiniteMeasure mu]
    (rewardKernel :
      RewardKernel.MarkovRewardKernel (Prod Context Action) Rat)
    (policy : Nat -> Policy.MeasurablePolicy State Action)
    (context : (n : Nat) -> ((j : Finset.Iic n) -> Rat) -> Context)
    (state : (n : Nat) -> ((j : Finset.Iic n) -> Rat) -> State)
    (hcontext : forall n : Nat, Measurable (context n))
    (hstate : forall n : Nat, Measurable (state n))
    (mean : Context -> Action -> Rat)
    (varianceProxy : Context -> Action -> NNReal)
    (law :
      RewardKernel.CenteredRewardKernelLaw rewardKernel mean varianceProxy)
    (action : Omega -> ActionTrace Action)
    (reward : Omega -> RewardTrace Rat)
    (haction : forall t : Nat,
      @Measurable Omega Action mOmega inferInstance
        (fun omega : Omega => action omega t))
    (hreward : forall t : Nat,
      @Measurable Omega Rat mOmega inferInstance
        (fun omega : Omega => reward omega t))
    (i : Nat)
    (h_integrable :
      MeasureTheory.Integrable
        (fun omega : Omega =>
          (((reward omega (i + 1) -
            mean
              (context i
                (History.finiteRewardHistoryOfTrace (reward omega) i))
              ((policy i).action
                (state i
                  (History.finiteRewardHistoryOfTrace (reward omega) i))) :
                Rat) : Real))) mu)
    (h_kernel_pair_map_eq :
      Filter.Eventually
        (fun omega : Omega =>
          @MeasureTheory.Measure.map Omega (Prod Action Rat) mOmega
            inferInstance
            (fun y : Omega => (action y (i + 1), reward y (i + 1)))
            (@ProbabilityTheory.condExpKernel Omega mOmega _ mu _
              ((History.historyFiltrationSucc action reward haction hreward) i)
              omega) =
          RewardKernel.actionRewardHistoryStepKernelFamily rewardKernel policy
            (fun n history =>
              context n (History.pairHistoryRewardProjection history))
            (fun n history =>
              state n (History.pairHistoryRewardProjection history))
            (fun n : Nat =>
              (hcontext n).comp
                (History.measurable_pairHistoryRewardProjection
                  (Action := Action) (Reward := Rat) n))
            (fun n : Nat =>
              (hstate n).comp
                (History.measurable_pairHistoryRewardProjection
                  (Action := Action) (Reward := Rat) n))
            i
            (History.finitePairHistoryOfTrace
              (action omega) (reward omega) i))
        (MeasureTheory.ae
          (mu.trim
            ((History.historyFiltrationSucc action reward haction hreward).le
              i)))) :
    Filter.EventuallyEq (MeasureTheory.ae mu)
      (@MeasureTheory.condExp Omega Real
        ((History.historyFiltrationSucc action reward haction hreward) i)
        mOmega _ _ _ mu
        (fun omega : Omega =>
          (((reward omega (i + 1) -
            mean
              (context i
                (History.finiteRewardHistoryOfTrace (reward omega) i))
              ((policy i).action
                (state i
                  (History.finiteRewardHistoryOfTrace (reward omega) i))) :
                Rat) : Real))))
      (fun _omega : Omega => (0 : Real)) := by
  exact
    ConditionalExpectationReward.centeredReward_succ_condExp_eq_zero_of_actionRewardHistoryStepKernelFamily_pair_map_eq_historyFiltrationSucc_finitePairHistoryOfTrace
      (mOmega := mOmega)
      mu action rewardKernel policy context state hcontext hstate mean
      varianceProxy law reward haction hreward i h_integrable
      h_kernel_pair_map_eq

example {Omega Context State Action : Type}
    [mOmega : MeasurableSpace Omega] [StandardBorelSpace Omega]
    [MeasurableSpace Context] [MeasurableSpace State]
    [MeasurableSpace Action] [MeasurableSingletonClass Action]
    (mu : MeasureTheory.Measure Omega)
    [MeasureTheory.IsFiniteMeasure mu]
    (rewardKernel :
      RewardKernel.MarkovRewardKernel (Prod Context Action) Rat)
    (policy : Nat -> Policy.MeasurablePolicy State Action)
    (context : (n : Nat) -> ((j : Finset.Iic n) -> Rat) -> Context)
    (state : (n : Nat) -> ((j : Finset.Iic n) -> Rat) -> State)
    (hcontext : forall n : Nat, Measurable (context n))
    (hstate : forall n : Nat, Measurable (state n))
    (mean : Context -> Action -> Rat)
    (varianceProxy : Context -> Action -> NNReal)
    (hmean :
      Measurable (fun pair : Prod Context Action => mean pair.1 pair.2))
    (hkernel :
      RewardKernel.CenteredRewardKernelLaw rewardKernel mean varianceProxy)
    (action : Omega -> ActionTrace Action)
    (reward : Omega -> RewardTrace Rat)
    (haction : forall t : Nat,
      @Measurable Omega Action mOmega inferInstance
        (fun omega : Omega => action omega t))
    (hreward : forall t : Nat,
      @Measurable Omega Rat mOmega inferInstance
        (fun omega : Omega => reward omega t))
    (rewardLo rewardHi meanLo meanHi : Nat -> Real)
    (hraw :
      forall i : Nat, forall omega : Omega,
        Set.Icc (rewardLo i) (rewardHi i)
          (((reward omega (i + 1) : Rat) : Real)))
    (hmean_range :
      forall i : Nat, forall context : Context, forall action : Action,
        Set.Icc (meanLo i) (meanHi i)
          (((mean context action : Rat) : Real)))
    (i : Nat)
    (h_kernel_pair_map_eq :
      Filter.Eventually
        (fun omega : Omega =>
          @MeasureTheory.Measure.map Omega (Prod Action Rat) mOmega
            inferInstance
            (fun y : Omega => (action y (i + 1), reward y (i + 1)))
            (@ProbabilityTheory.condExpKernel Omega mOmega _ mu _
              ((History.historyFiltrationSucc action reward haction hreward) i)
              omega) =
          RewardKernel.actionRewardHistoryStepKernelFamily rewardKernel policy
            (fun n history =>
              context n (History.pairHistoryRewardProjection history))
            (fun n history =>
              state n (History.pairHistoryRewardProjection history))
            (fun n : Nat =>
              (hcontext n).comp
                (History.measurable_pairHistoryRewardProjection
                  (Action := Action) (Reward := Rat) n))
            (fun n : Nat =>
              (hstate n).comp
                (History.measurable_pairHistoryRewardProjection
                  (Action := Action) (Reward := Rat) n))
            i
            (History.finitePairHistoryOfTrace
              (action omega) (reward omega) i))
        (MeasureTheory.ae
          (mu.trim
            ((History.historyFiltrationSucc action reward haction hreward).le
              i)))) :
    Filter.EventuallyEq (MeasureTheory.ae mu)
      (@MeasureTheory.condExp Omega Real
        ((History.historyFiltrationSucc action reward haction hreward) i)
        mOmega _ _ _ mu
        (fun omega : Omega =>
          (((reward omega (i + 1) -
            mean
              (context i
                (History.finiteRewardHistoryOfTrace (reward omega) i))
              ((policy i).action
                (state i
                  (History.finiteRewardHistoryOfTrace (reward omega) i))) :
            Rat) : Real))))
      (fun _omega : Omega => (0 : Real)) := by
  exact
    ConditionalExpectationReward.centeredReward_succ_condExp_eq_zero_of_actionRewardHistoryStepKernelFamily_pair_map_eq_historyFiltrationSucc_finitePairHistoryOfTrace_rawRangeMeasurableMeanRangeBounded
      (mOmega := mOmega)
      mu action rewardKernel policy context state hcontext hstate mean
      varianceProxy hmean hkernel reward haction hreward rewardLo rewardHi
      meanLo meanHi hraw hmean_range i h_kernel_pair_map_eq

example {Omega Context State Action : Type}
    [mOmega : MeasurableSpace Omega] [StandardBorelSpace Omega]
    [MeasurableSpace Context] [MeasurableSpace State]
    [MeasurableSpace Action] [MeasurableSingletonClass Action]
    (mu : MeasureTheory.Measure Omega)
    [MeasureTheory.IsFiniteMeasure mu]
    (rewardKernel :
      RewardKernel.MarkovRewardKernel (Prod Context Action) Rat)
    (policy : Nat -> Policy.MeasurablePolicy State Action)
    (context : (n : Nat) -> ((j : Finset.Iic n) -> Rat) -> Context)
    (state : (n : Nat) -> ((j : Finset.Iic n) -> Rat) -> State)
    (hcontext : forall n : Nat, Measurable (context n))
    (hstate : forall n : Nat, Measurable (state n))
    (mean : Context -> Action -> Rat)
    (varianceProxy : Context -> Action -> NNReal)
    (hmean :
      Measurable (fun pair : Prod Context Action => mean pair.1 pair.2))
    (hkernel :
      RewardKernel.CenteredRewardKernelLaw rewardKernel mean varianceProxy)
    (defaultAction : Action)
    (action : Omega -> ActionTrace Action)
    (reward : Omega -> RewardTrace Rat)
    (haction : forall t : Nat,
      @Measurable Omega Action mOmega inferInstance
        (fun omega : Omega => action omega t))
    (hreward : forall t : Nat,
      @Measurable Omega Rat mOmega inferInstance
        (fun omega : Omega => reward omega t))
    (rewardLo rewardHi meanLo meanHi : Nat -> Real)
    (hraw :
      forall i : Nat, forall omega : Omega,
        Set.Icc (rewardLo i) (rewardHi i)
          (((reward omega (i + 1) : Rat) : Real)))
    (hmean_range :
      forall i : Nat, forall context : Context, forall action : Action,
        Set.Icc (meanLo i) (meanHi i)
          (((mean context action : Rat) : Real)))
    (i : Nat)
    (h_action_generated :
      action =
        Policy.generatedActionTraceSucc policy
          (fun n omega =>
            state n (History.finiteRewardHistoryOfTrace (reward omega) n))
          defaultAction)
    (h_kernel_pair_map_eq :
      Filter.Eventually
        (fun omega : Omega =>
          @MeasureTheory.Measure.map Omega (Prod Action Rat) mOmega
            inferInstance
            (fun y : Omega => (action y (i + 1), reward y (i + 1)))
            (@ProbabilityTheory.condExpKernel Omega mOmega _ mu _
              ((History.historyFiltrationSucc action reward haction hreward) i)
              omega) =
          RewardKernel.actionRewardHistoryStepKernelFamily rewardKernel policy
            (fun n history =>
              context n (History.pairHistoryRewardProjection history))
            (fun n history =>
              state n (History.pairHistoryRewardProjection history))
            (fun n : Nat =>
              (hcontext n).comp
                (History.measurable_pairHistoryRewardProjection
                  (Action := Action) (Reward := Rat) n))
            (fun n : Nat =>
              (hstate n).comp
                (History.measurable_pairHistoryRewardProjection
                  (Action := Action) (Reward := Rat) n))
            i
            (History.finitePairHistoryOfTrace
              (action omega) (reward omega) i))
        (MeasureTheory.ae
          (mu.trim
            ((History.historyFiltrationSucc action reward haction hreward).le
              i)))) :
    Filter.EventuallyEq (MeasureTheory.ae mu)
      (@MeasureTheory.condExp Omega Real
        ((History.historyFiltrationSucc action reward haction hreward) i)
        mOmega _ _ _ mu
        (fun omega : Omega =>
          (((reward omega (i + 1) -
            mean
              (context i
                (History.finiteRewardHistoryOfTrace (reward omega) i))
              ((policy i).action
                (state i
                  (History.finiteRewardHistoryOfTrace (reward omega) i))) :
            Rat) : Real))))
      (fun _omega : Omega => (0 : Real)) := by
  exact
    ConditionalExpectationReward.centeredReward_succ_condExp_eq_zero_of_generatedActionTraceSucc_actionRewardHistoryStepKernelFamily_pair_map_eq_historyFiltrationSucc_finitePairHistoryOfTrace_rawRangeMeasurableMeanRangeBounded
      (mOmega := mOmega)
      mu action rewardKernel policy context state hcontext hstate mean
      varianceProxy hmean hkernel defaultAction reward haction hreward
      rewardLo rewardHi meanLo meanHi hraw hmean_range i
      h_action_generated h_kernel_pair_map_eq

example {Omega Context State Action : Type}
    [mOmega : MeasurableSpace Omega] [StandardBorelSpace Omega]
    [MeasurableSpace Context] [MeasurableSpace State]
    [MeasurableSpace Action] [MeasurableSingletonClass Action]
    (mu : MeasureTheory.Measure Omega)
    [MeasureTheory.IsFiniteMeasure mu]
    (rewardKernel :
      RewardKernel.MarkovRewardKernel (Prod Context Action) Rat)
    (policy : Nat -> Policy.MeasurablePolicy State Action)
    (context : (n : Nat) -> ((j : Finset.Iic n) -> Rat) -> Context)
    (state : (n : Nat) -> ((j : Finset.Iic n) -> Rat) -> State)
    (hcontext : forall n : Nat, Measurable (context n))
    (hstate : forall n : Nat, Measurable (state n))
    (mean : Context -> Action -> Rat)
    (varianceProxy : Context -> Action -> NNReal)
    (hmean :
      Measurable (fun pair : Prod Context Action => mean pair.1 pair.2))
    (hkernel :
      RewardKernel.CenteredRewardKernelLaw rewardKernel mean varianceProxy)
    (action : Omega -> ActionTrace Action)
    (reward : Omega -> RewardTrace Rat)
    (haction : forall t : Nat,
      @Measurable Omega Action mOmega inferInstance
        (fun omega : Omega => action omega t))
    (hreward : forall t : Nat,
      @Measurable Omega Rat mOmega inferInstance
        (fun omega : Omega => reward omega t))
    (rewardLo rewardHi meanLo meanHi : Nat -> Real)
    (hraw :
      forall i : Nat, forall omega : Omega,
        Set.Icc (rewardLo i) (rewardHi i)
          (((reward omega (i + 1) : Rat) : Real)))
    (hmean_range :
      forall i : Nat, forall context : Context, forall action : Action,
        Set.Icc (meanLo i) (meanHi i)
          (((mean context action : Rat) : Real)))
    (i : Nat)
    (h_action_ae_eq_policy :
      Filter.Eventually
        (fun omega : Omega =>
          Filter.EventuallyEq
            (MeasureTheory.ae
              (@ProbabilityTheory.condExpKernel Omega mOmega _ mu _
                ((History.historyFiltrationSucc action reward haction hreward) i)
                omega))
            (fun y : Omega => action y (i + 1))
            (fun _y : Omega =>
              (policy i).action
                (state i
                  (History.finiteRewardHistoryOfTrace (reward omega) i))))
        (MeasureTheory.ae
          (mu.trim
            ((History.historyFiltrationSucc action reward haction hreward).le
              i))))
    (h_reward_map_eq :
      Filter.Eventually
        (fun omega : Omega =>
          @MeasureTheory.Measure.map Omega Rat mOmega inferInstance
            (fun y : Omega => reward y (i + 1))
            (@ProbabilityTheory.condExpKernel Omega mOmega _ mu _
              ((History.historyFiltrationSucc action reward haction hreward) i)
              omega) =
          RewardKernel.selectedMeasure rewardKernel
            (context i
              (History.finiteRewardHistoryOfTrace (reward omega) i))
            ((policy i).action
              (state i
                (History.finiteRewardHistoryOfTrace (reward omega) i))))
        (MeasureTheory.ae
          (mu.trim
            ((History.historyFiltrationSucc action reward haction hreward).le
              i)))) :
    Filter.EventuallyEq (MeasureTheory.ae mu)
      (@MeasureTheory.condExp Omega Real
        ((History.historyFiltrationSucc action reward haction hreward) i)
        mOmega _ _ _ mu
        (fun omega : Omega =>
          (((reward omega (i + 1) -
            mean
              (context i
                (History.finiteRewardHistoryOfTrace (reward omega) i))
              ((policy i).action
                (state i
                  (History.finiteRewardHistoryOfTrace (reward omega) i))) :
            Rat) : Real))))
      (fun _omega : Omega => (0 : Real)) := by
  exact
    ConditionalExpectationReward.centeredReward_succ_condExp_eq_zero_of_action_ae_eq_policy_reward_map_eq_historyFiltrationSucc_finitePairHistoryOfTrace_rawRangeMeasurableMeanRangeBounded
      (mOmega := mOmega)
      mu action rewardKernel policy context state hcontext hstate mean
      varianceProxy hmean hkernel reward haction hreward rewardLo rewardHi
      meanLo meanHi hraw hmean_range i h_action_ae_eq_policy
      h_reward_map_eq

example {Omega Context State Action : Type}
    [mOmega : MeasurableSpace Omega] [StandardBorelSpace Omega]
    [MeasurableSpace Context] [MeasurableSpace State]
    [MeasurableSpace Action] [MeasurableSingletonClass Action]
    [Countable Action]
    (mu : MeasureTheory.Measure Omega)
    [MeasureTheory.IsFiniteMeasure mu]
    (rewardKernel :
      RewardKernel.MarkovRewardKernel (Prod Context Action) Rat)
    (policy : Nat -> Policy.MeasurablePolicy State Action)
    (context : (n : Nat) -> ((j : Finset.Iic n) -> Rat) -> Context)
    (state : (n : Nat) -> ((j : Finset.Iic n) -> Rat) -> State)
    (hcontext : forall n : Nat, Measurable (context n))
    (hstate : forall n : Nat, Measurable (state n))
    (mean : Context -> Action -> Rat)
    (varianceProxy : Context -> Action -> NNReal)
    (hmean :
      Measurable (fun pair : Prod Context Action => mean pair.1 pair.2))
    (hkernel :
      RewardKernel.CenteredRewardKernelLaw rewardKernel mean varianceProxy)
    (defaultAction : Action)
    (action : Omega -> ActionTrace Action)
    (reward : Omega -> RewardTrace Rat)
    (haction : forall t : Nat,
      @Measurable Omega Action mOmega inferInstance
        (fun omega : Omega => action omega t))
    (hreward : forall t : Nat,
      @Measurable Omega Rat mOmega inferInstance
        (fun omega : Omega => reward omega t))
    (rewardLo rewardHi meanLo meanHi : Nat -> Real)
    (hraw :
      forall i : Nat, forall omega : Omega,
        Set.Icc (rewardLo i) (rewardHi i)
          (((reward omega (i + 1) : Rat) : Real)))
    (hmean_range :
      forall i : Nat, forall context : Context, forall action : Action,
        Set.Icc (meanLo i) (meanHi i)
          (((mean context action : Rat) : Real)))
    (i : Nat)
    (h_action_generated :
      action =
        Policy.generatedActionTraceSucc policy
          (fun n omega =>
            state n (History.finiteRewardHistoryOfTrace (reward omega) n))
          defaultAction)
    (h_reward_map_eq_policy :
      Filter.Eventually
        (fun omega : Omega =>
          @MeasureTheory.Measure.map Omega Rat mOmega inferInstance
            (fun y : Omega => reward y (i + 1))
            (@ProbabilityTheory.condExpKernel Omega mOmega _ mu _
              ((History.historyFiltrationSucc action reward haction hreward) i)
              omega) =
          RewardKernel.selectedMeasure rewardKernel
            (context i
              (History.finiteRewardHistoryOfTrace (reward omega) i))
            ((policy i).action
              (state i
                (History.finiteRewardHistoryOfTrace (reward omega) i))))
        (MeasureTheory.ae
          (mu.trim
            ((History.historyFiltrationSucc action reward haction hreward).le
              i)))) :
    Filter.EventuallyEq (MeasureTheory.ae mu)
      (@MeasureTheory.condExp Omega Real
        ((History.historyFiltrationSucc action reward haction hreward) i)
        mOmega _ _ _ mu
        (fun omega : Omega =>
          (((reward omega (i + 1) -
            mean
              (context i
                (History.finiteRewardHistoryOfTrace (reward omega) i))
              ((policy i).action
                (state i
                  (History.finiteRewardHistoryOfTrace (reward omega) i))) :
            Rat) : Real))))
      (fun _omega : Omega => (0 : Real)) := by
  exact
    ConditionalExpectationReward.centeredReward_succ_condExp_eq_zero_of_generatedActionTraceSucc_reward_map_eq_selected_policy_rawRangeMeasurableMeanRangeBounded
      (mOmega := mOmega)
      mu action rewardKernel policy context state hcontext hstate mean
      varianceProxy hmean hkernel defaultAction reward haction hreward
      rewardLo rewardHi meanLo meanHi hraw hmean_range i
      h_action_generated h_reward_map_eq_policy

example {Omega Context State Action : Type}
    [mOmega : MeasurableSpace Omega] [StandardBorelSpace Omega]
    [MeasurableSpace Context] [MeasurableSpace State]
    [MeasurableSpace Action] [MeasurableSingletonClass Action]
    (mu : MeasureTheory.Measure Omega)
    [MeasureTheory.IsFiniteMeasure mu]
    (rewardKernel :
      RewardKernel.MarkovRewardKernel (Prod Context Action) Rat)
    (policy : Nat -> Policy.MeasurablePolicy State Action)
    (context : (n : Nat) -> ((j : Finset.Iic n) -> Rat) -> Context)
    (state : (n : Nat) -> ((j : Finset.Iic n) -> Rat) -> State)
    (hcontext : forall n : Nat, Measurable (context n))
    (hstate : forall n : Nat, Measurable (state n))
    (mean : Context -> Action -> Rat)
    (varianceProxy : Context -> Action -> NNReal)
    (law :
      RewardKernel.CenteredRewardKernelLaw rewardKernel mean varianceProxy)
    (action : Omega -> ActionTrace Action)
    (reward : Omega -> RewardTrace Rat)
    (haction : forall t : Nat,
      @Measurable Omega Action mOmega inferInstance
        (fun omega : Omega => action omega t))
    (hreward : forall t : Nat,
      @Measurable Omega Rat mOmega inferInstance
        (fun omega : Omega => reward omega t))
    (i : Nat)
    (h_integrable :
      MeasureTheory.Integrable
        (fun omega : Omega =>
          (((reward omega (i + 1) -
            mean
              (context i
                (History.finiteRewardHistoryOfTrace (reward omega) i))
              ((policy i).action
                (state i
                  (History.finiteRewardHistoryOfTrace (reward omega) i))) :
                Rat) : Real))) mu)
    (h_kernel_partialtraj_map_eq :
      Filter.Eventually
        (fun omega : Omega =>
          @MeasureTheory.Measure.map Omega
            ((j : Finset.Iic (i + 1)) -> Prod Action Rat) mOmega
            inferInstance
            (fun y : Omega =>
              History.finitePairHistoryOfTrace
                (action y) (reward y) (i + 1))
            (@ProbabilityTheory.condExpKernel Omega mOmega _ mu _
              ((History.historyFiltrationSucc action reward haction hreward) i)
              omega) =
          RewardKernel.actionRewardPartialTrajectoryKernel rewardKernel policy
            (fun n history =>
              context n (History.pairHistoryRewardProjection history))
            (fun n history =>
              state n (History.pairHistoryRewardProjection history))
            (fun n : Nat =>
              (hcontext n).comp
                (History.measurable_pairHistoryRewardProjection
                  (Action := Action) (Reward := Rat) n))
            (fun n : Nat =>
              (hstate n).comp
                (History.measurable_pairHistoryRewardProjection
                  (Action := Action) (Reward := Rat) n))
            i (i + 1)
            (History.finitePairHistoryOfTrace
              (action omega) (reward omega) i))
        (MeasureTheory.ae
          (mu.trim
            ((History.historyFiltrationSucc action reward haction hreward).le
              i)))) :
    Filter.EventuallyEq (MeasureTheory.ae mu)
      (@MeasureTheory.condExp Omega Real
        ((History.historyFiltrationSucc action reward haction hreward) i)
        mOmega _ _ _ mu
        (fun omega : Omega =>
          (((reward omega (i + 1) -
            mean
              (context i
                (History.finiteRewardHistoryOfTrace (reward omega) i))
              ((policy i).action
                (state i
                  (History.finiteRewardHistoryOfTrace (reward omega) i))) :
                Rat) : Real))))
      (fun _omega : Omega => (0 : Real)) := by
  exact
    ConditionalExpectationReward.centeredReward_succ_condExp_eq_zero_of_actionRewardPartialTrajectoryKernel_map_eq_historyFiltrationSucc_finitePairHistoryOfTrace
      (mOmega := mOmega)
      mu action rewardKernel policy context state hcontext hstate mean
      varianceProxy law reward haction hreward i h_integrable
      h_kernel_partialtraj_map_eq

example {Omega Context State Action : Type}
    [mOmega : MeasurableSpace Omega] [StandardBorelSpace Omega]
    [MeasurableSpace Context] [MeasurableSpace State]
    [MeasurableSpace Action] [MeasurableSingletonClass Action]
    (mu : MeasureTheory.Measure Omega)
    [MeasureTheory.IsFiniteMeasure mu]
    (rewardKernel :
      RewardKernel.MarkovRewardKernel (Prod Context Action) Rat)
    (policy : Nat -> Policy.MeasurablePolicy State Action)
    (context : (n : Nat) -> ((j : Finset.Iic n) -> Rat) -> Context)
    (state : (n : Nat) -> ((j : Finset.Iic n) -> Rat) -> State)
    (hcontext : forall n : Nat, Measurable (context n))
    (hstate : forall n : Nat, Measurable (state n))
    (mean : Context -> Action -> Rat)
    (varianceProxy : Context -> Action -> NNReal)
    (hmean :
      Measurable (fun pair : Prod Context Action => mean pair.1 pair.2))
    (hkernel :
      RewardKernel.CenteredRewardKernelLaw rewardKernel mean varianceProxy)
    (action : Omega -> ActionTrace Action)
    (reward : Omega -> RewardTrace Rat)
    (haction : forall t : Nat,
      @Measurable Omega Action mOmega inferInstance
        (fun omega : Omega => action omega t))
    (hreward : forall t : Nat,
      @Measurable Omega Rat mOmega inferInstance
        (fun omega : Omega => reward omega t))
    (rewardLo rewardHi meanLo meanHi : Nat -> Real)
    (hraw :
      forall i : Nat, forall omega : Omega,
        Set.Icc (rewardLo i) (rewardHi i)
          (((reward omega (i + 1) : Rat) : Real)))
    (hmean_range :
      forall i : Nat, forall context : Context, forall action : Action,
        Set.Icc (meanLo i) (meanHi i)
          (((mean context action : Rat) : Real)))
    (i : Nat)
    (h_kernel_partialtraj_map_eq :
      Filter.Eventually
        (fun omega : Omega =>
          @MeasureTheory.Measure.map Omega
            ((j : Finset.Iic (i + 1)) -> Prod Action Rat) mOmega
            inferInstance
            (fun y : Omega =>
              History.finitePairHistoryOfTrace
                (action y) (reward y) (i + 1))
            (@ProbabilityTheory.condExpKernel Omega mOmega _ mu _
              ((History.historyFiltrationSucc action reward haction hreward) i)
              omega) =
          RewardKernel.actionRewardPartialTrajectoryKernel rewardKernel policy
            (fun n history =>
              context n (History.pairHistoryRewardProjection history))
            (fun n history =>
              state n (History.pairHistoryRewardProjection history))
            (fun n : Nat =>
              (hcontext n).comp
                (History.measurable_pairHistoryRewardProjection
                  (Action := Action) (Reward := Rat) n))
            (fun n : Nat =>
              (hstate n).comp
                (History.measurable_pairHistoryRewardProjection
                  (Action := Action) (Reward := Rat) n))
            i (i + 1)
            (History.finitePairHistoryOfTrace
              (action omega) (reward omega) i))
        (MeasureTheory.ae
          (mu.trim
            ((History.historyFiltrationSucc action reward haction hreward).le
              i)))) :
    Filter.EventuallyEq (MeasureTheory.ae mu)
      (@MeasureTheory.condExp Omega Real
        ((History.historyFiltrationSucc action reward haction hreward) i)
        mOmega _ _ _ mu
        (fun omega : Omega =>
          (((reward omega (i + 1) -
            mean
              (context i
                (History.finiteRewardHistoryOfTrace (reward omega) i))
              ((policy i).action
                (state i
                  (History.finiteRewardHistoryOfTrace (reward omega) i))) :
            Rat) : Real))))
      (fun _omega : Omega => (0 : Real)) := by
  exact
    ConditionalExpectationReward.centeredReward_succ_condExp_eq_zero_of_actionRewardPartialTrajectoryKernel_map_eq_historyFiltrationSucc_finitePairHistoryOfTrace_rawRangeMeasurableMeanRangeBounded
      (mOmega := mOmega)
      mu action rewardKernel policy context state hcontext hstate mean
      varianceProxy hmean hkernel reward haction hreward rewardLo rewardHi
      meanLo meanHi hraw hmean_range i h_kernel_partialtraj_map_eq

example {Omega State Action : Type}
    [mOmega : MeasurableSpace Omega] [StandardBorelSpace Omega]
    [MeasurableSpace State] [MeasurableSpace Action]
    [MeasurableSingletonClass Action] [Countable Action]
    (mu : MeasureTheory.Measure Omega)
    [MeasureTheory.IsFiniteMeasure mu]
    (F : MeasureTheory.Filtration Nat mOmega)
    (policy : Nat -> Policy.MeasurablePolicy State Action)
    (pairState :
      (n : Nat) -> ((j : Finset.Iic n) -> Prod Action Rat) -> State)
    (action : Omega -> ActionTrace Action)
    (i : Nat)
    (pairHistory : Omega -> ((j : Finset.Iic i) -> Prod Action Rat))
    (h_action_next_meas :
      @Measurable Omega Action (F i) inferInstance
        (fun omega : Omega => action omega (i + 1)))
    (h_action_policy_eq :
      Filter.Eventually
        (fun omega : Omega =>
          action omega (i + 1) =
            (policy i).action (pairState i (pairHistory omega)))
        (MeasureTheory.ae (mu.trim (F.le i)))) :
    Filter.Eventually
      (fun omega : Omega =>
        Filter.EventuallyEq
          (MeasureTheory.ae
            (@ProbabilityTheory.condExpKernel Omega mOmega _ mu _ (F i)
              omega))
          (fun y : Omega => action y (i + 1))
          (fun _y : Omega =>
            (policy i).action (pairState i (pairHistory omega))))
      (MeasureTheory.ae (mu.trim (F.le i))) := by
  exact
    ConditionalExpectationReward.action_condExpKernel_ae_eq_policy_of_measurable_of_policy_eq
      (mOmega := mOmega)
      mu F policy pairState action i pairHistory h_action_next_meas
      h_action_policy_eq

example {Omega State Action : Type}
    [mOmega : MeasurableSpace Omega] [StandardBorelSpace Omega]
    [MeasurableSpace State] [MeasurableSpace Action]
    [MeasurableSingletonClass Action] [Countable Action]
    (mu : MeasureTheory.Measure Omega)
    [MeasureTheory.IsFiniteMeasure mu]
    (F : MeasureTheory.Filtration Nat mOmega)
    (policy : Nat -> Policy.MeasurablePolicy State Action)
    (pairState :
      (n : Nat) -> ((j : Finset.Iic n) -> Prod Action Rat) -> State)
    (hpairState : forall n : Nat, Measurable (pairState n))
    (action : Omega -> ActionTrace Action)
    (i : Nat)
    (pairHistory : Omega -> ((j : Finset.Iic i) -> Prod Action Rat))
    (h_pairHistory_meas :
      @Measurable Omega ((j : Finset.Iic i) -> Prod Action Rat)
        (F i) inferInstance pairHistory)
    (h_action_eq :
      (fun omega : Omega => action omega (i + 1)) =
        (fun omega : Omega =>
          (policy i).action (pairState i (pairHistory omega)))) :
    Filter.Eventually
      (fun omega : Omega =>
        Filter.EventuallyEq
          (MeasureTheory.ae
            (@ProbabilityTheory.condExpKernel Omega mOmega _ mu _ (F i)
              omega))
          (fun y : Omega => action y (i + 1))
          (fun _y : Omega =>
            (policy i).action (pairState i (pairHistory omega))))
      (MeasureTheory.ae (mu.trim (F.le i))) := by
  exact
    ConditionalExpectationReward.action_condExpKernel_ae_eq_policy_of_pairHistory_measurable_of_action_eq
      (mOmega := mOmega)
      mu F policy pairState hpairState action i pairHistory
      h_pairHistory_meas h_action_eq

example {Omega State Action : Type}
    [mOmega : MeasurableSpace Omega] [StandardBorelSpace Omega]
    [MeasurableSpace State]
    [MeasurableSpace Action] [MeasurableSingletonClass Action]
    [Countable Action]
    (mu : MeasureTheory.Measure Omega)
    [MeasureTheory.IsFiniteMeasure mu]
    (policy : Nat -> Policy.MeasurablePolicy State Action)
    (pairState :
      (n : Nat) -> ((j : Finset.Iic n) -> Prod Action Rat) -> State)
    (hpairState : forall n : Nat, Measurable (pairState n))
    (action : Omega -> ActionTrace Action)
    (reward : Omega -> RewardTrace Rat)
    (haction : forall t : Nat,
      Measurable (fun omega : Omega => action omega t))
    (hreward : forall t : Nat,
      Measurable (fun omega : Omega => reward omega t))
    (i : Nat)
    (h_action_eq :
      (fun omega : Omega => action omega (i + 1)) =
        (fun omega : Omega =>
          (policy i).action
            (pairState i
              (History.finitePairHistoryOfTrace
                (action omega) (reward omega) i)))) :
    Filter.Eventually
      (fun omega : Omega =>
        Filter.EventuallyEq
          (MeasureTheory.ae
            (@ProbabilityTheory.condExpKernel Omega mOmega _ mu _
              ((History.historyFiltrationSucc action reward haction hreward) i)
              omega))
          (fun y : Omega => action y (i + 1))
          (fun _y : Omega =>
            (policy i).action
              (pairState i
                (History.finitePairHistoryOfTrace
                  (action omega) (reward omega) i))))
      (MeasureTheory.ae
        (mu.trim
          ((History.historyFiltrationSucc action reward haction hreward).le
            i))) := by
  exact
    ConditionalExpectationReward.action_condExpKernel_ae_eq_policy_historyFiltrationSucc_finitePairHistoryOfTrace_of_action_eq
      (mOmega := mOmega)
      mu policy pairState hpairState action reward haction hreward i
      h_action_eq

example {Omega State Action : Type}
    [mOmega : MeasurableSpace Omega] [StandardBorelSpace Omega]
    [MeasurableSpace State]
    [MeasurableSpace Action] [MeasurableSingletonClass Action]
    [Countable Action]
    (mu : MeasureTheory.Measure Omega)
    [MeasureTheory.IsFiniteMeasure mu]
    (policy : Nat -> Policy.MeasurablePolicy State Action)
    (pairState :
      (n : Nat) -> ((j : Finset.Iic n) -> Prod Action Rat) -> State)
    (hpairState : forall n : Nat, Measurable (pairState n))
    (defaultAction : Action)
    (action : Omega -> ActionTrace Action)
    (reward : Omega -> RewardTrace Rat)
    (haction : forall t : Nat,
      Measurable (fun omega : Omega => action omega t))
    (hreward : forall t : Nat,
      Measurable (fun omega : Omega => reward omega t))
    (i : Nat)
    (h_action_generated :
      action =
        Policy.generatedActionTraceSucc policy
          (fun n omega =>
            pairState n
              (History.finitePairHistoryOfTrace
                (action omega) (reward omega) n))
          defaultAction) :
    Filter.Eventually
      (fun omega : Omega =>
        Filter.EventuallyEq
          (MeasureTheory.ae
            (@ProbabilityTheory.condExpKernel Omega mOmega _ mu _
              ((History.historyFiltrationSucc action reward haction hreward) i)
              omega))
          (fun y : Omega => action y (i + 1))
          (fun _y : Omega =>
            (policy i).action
              (pairState i
                (History.finitePairHistoryOfTrace
                  (action omega) (reward omega) i))))
      (MeasureTheory.ae
        (mu.trim
          ((History.historyFiltrationSucc action reward haction hreward).le
            i))) := by
  exact
    ConditionalExpectationReward.action_condExpKernel_ae_eq_policy_historyFiltrationSucc_finitePairHistoryOfTrace_of_generatedActionTraceSucc
      (mOmega := mOmega)
      mu policy pairState hpairState defaultAction action reward haction hreward
      i h_action_generated

example {Omega Context State Action : Type}
    [mOmega : MeasurableSpace Omega] [StandardBorelSpace Omega]
    [MeasurableSpace Context] [MeasurableSpace State]
    [MeasurableSpace Action]
    (mu : MeasureTheory.Measure Omega)
    [MeasureTheory.IsFiniteMeasure mu]
    (F : MeasureTheory.Filtration Nat mOmega)
    (rewardKernel :
      RewardKernel.MarkovRewardKernel (Prod Context Action) Rat)
    (policy : Nat -> Policy.MeasurablePolicy State Action)
    (pairContext :
      (n : Nat) -> ((j : Finset.Iic n) -> Prod Action Rat) -> Context)
    (pairState :
      (n : Nat) -> ((j : Finset.Iic n) -> Prod Action Rat) -> State)
    (action : Omega -> ActionTrace Action)
    (reward : Omega -> RewardTrace Rat)
    (i : Nat)
    (pairHistory : Omega -> ((j : Finset.Iic i) -> Prod Action Rat))
    (h_action_policy_eq :
      Filter.Eventually
        (fun omega : Omega =>
          action omega (i + 1) =
            (policy i).action (pairState i (pairHistory omega)))
        (MeasureTheory.ae (mu.trim (F.le i))))
    (h_reward_map_eq_actual_action :
      Filter.Eventually
        (fun omega : Omega =>
          @MeasureTheory.Measure.map Omega Rat mOmega inferInstance
            (fun y : Omega => reward y (i + 1))
            (@ProbabilityTheory.condExpKernel Omega mOmega _ mu _ (F i)
              omega) =
          RewardKernel.selectedMeasure rewardKernel
            (pairContext i (pairHistory omega))
            (action omega (i + 1)))
        (MeasureTheory.ae (mu.trim (F.le i)))) :
    Filter.Eventually
      (fun omega : Omega =>
        @MeasureTheory.Measure.map Omega Rat mOmega inferInstance
          (fun y : Omega => reward y (i + 1))
          (@ProbabilityTheory.condExpKernel Omega mOmega _ mu _ (F i)
            omega) =
        RewardKernel.selectedMeasure rewardKernel
          (pairContext i (pairHistory omega))
          ((policy i).action (pairState i (pairHistory omega))))
      (MeasureTheory.ae (mu.trim (F.le i))) := by
  exact
    ConditionalExpectationReward.reward_condExpKernel_map_eq_selected_policy_of_action_eq
      (mOmega := mOmega)
      mu F rewardKernel policy pairContext pairState action reward i
      pairHistory h_action_policy_eq h_reward_map_eq_actual_action

example {Omega Context Action : Type}
    [mOmega : MeasurableSpace Omega] [StandardBorelSpace Omega]
    [MeasurableSpace Context] [MeasurableSpace Action]
    (mu : MeasureTheory.Measure Omega)
    [MeasureTheory.IsFiniteMeasure mu]
    (F : MeasureTheory.Filtration Nat mOmega)
    (rewardKernel :
      RewardKernel.MarkovRewardKernel (Prod Context Action) Rat)
    (pairContext :
      (n : Nat) -> ((j : Finset.Iic n) -> Prod Action Rat) -> Context)
    (action : Omega -> ActionTrace Action)
    (reward : Omega -> RewardTrace Rat)
    (i : Nat)
    (pairHistory : Omega -> ((j : Finset.Iic i) -> Prod Action Rat))
    (h_reward_next :
      @Measurable Omega Rat mOmega inferInstance
        (fun omega : Omega => reward omega (i + 1)))
    (h_pair_map_eq_actual_action :
      Filter.Eventually
        (fun omega : Omega =>
          @MeasureTheory.Measure.map Omega (Prod Action Rat) mOmega
            inferInstance
            (fun y : Omega => (action omega (i + 1), reward y (i + 1)))
            (@ProbabilityTheory.condExpKernel Omega mOmega _ mu _ (F i)
              omega) =
          MeasureTheory.Measure.map
            (Prod.mk (action omega (i + 1)))
            (RewardKernel.selectedMeasure rewardKernel
              (pairContext i (pairHistory omega))
              (action omega (i + 1))))
        (MeasureTheory.ae (mu.trim (F.le i)))) :
    Filter.Eventually
      (fun omega : Omega =>
        @MeasureTheory.Measure.map Omega Rat mOmega inferInstance
          (fun y : Omega => reward y (i + 1))
          (@ProbabilityTheory.condExpKernel Omega mOmega _ mu _ (F i)
            omega) =
        RewardKernel.selectedMeasure rewardKernel
          (pairContext i (pairHistory omega))
          (action omega (i + 1)))
      (MeasureTheory.ae (mu.trim (F.le i))) := by
  exact
    ConditionalExpectationReward.reward_condExpKernel_map_eq_selected_actual_action_of_pair_map_eq
      (mOmega := mOmega)
      mu F rewardKernel pairContext action reward i pairHistory
      h_reward_next h_pair_map_eq_actual_action

example {Omega Context State Action : Type}
    [mOmega : MeasurableSpace Omega] [StandardBorelSpace Omega]
    [MeasurableSpace Context] [MeasurableSpace State]
    [MeasurableSpace Action] [MeasurableSingletonClass Action]
    [Countable Action]
    (mu : MeasureTheory.Measure Omega)
    [MeasureTheory.IsFiniteMeasure mu]
    (rewardKernel :
      RewardKernel.MarkovRewardKernel (Prod Context Action) Rat)
    (policy : Nat -> Policy.MeasurablePolicy State Action)
    (pairContext :
      (n : Nat) -> ((j : Finset.Iic n) -> Prod Action Rat) -> Context)
    (pairState :
      (n : Nat) -> ((j : Finset.Iic n) -> Prod Action Rat) -> State)
    (hpairState : forall n : Nat, Measurable (pairState n))
    (defaultAction : Action)
    (action : Omega -> ActionTrace Action)
    (reward : Omega -> RewardTrace Rat)
    (haction : forall t : Nat,
      @Measurable Omega Action mOmega inferInstance
        (fun omega : Omega => action omega t))
    (hreward : forall t : Nat,
      @Measurable Omega Rat mOmega inferInstance
        (fun omega : Omega => reward omega t))
    (i : Nat)
    (h_action_generated :
      action =
        Policy.generatedActionTraceSucc policy
          (fun n omega =>
            pairState n
              (History.finitePairHistoryOfTrace
                (action omega) (reward omega) n))
          defaultAction)
    (h_random_pair_map_eq_actual_action :
      Filter.Eventually
        (fun omega : Omega =>
          @MeasureTheory.Measure.map Omega (Prod Action Rat) mOmega
            inferInstance
            (fun y : Omega => (action y (i + 1), reward y (i + 1)))
            (@ProbabilityTheory.condExpKernel Omega mOmega _ mu _
              ((History.historyFiltrationSucc action reward haction hreward) i)
              omega) =
          MeasureTheory.Measure.map
            (Prod.mk (action omega (i + 1)))
            (RewardKernel.selectedMeasure rewardKernel
              (pairContext i
                (History.finitePairHistoryOfTrace
                  (action omega) (reward omega) i))
              (action omega (i + 1))))
        (MeasureTheory.ae
          (mu.trim
            ((History.historyFiltrationSucc action reward haction hreward).le
              i)))) :
    Filter.Eventually
      (fun omega : Omega =>
        @MeasureTheory.Measure.map Omega (Prod Action Rat) mOmega
          inferInstance
          (fun y : Omega => (action omega (i + 1), reward y (i + 1)))
          (@ProbabilityTheory.condExpKernel Omega mOmega _ mu _
            ((History.historyFiltrationSucc action reward haction hreward) i)
            omega) =
        MeasureTheory.Measure.map
          (Prod.mk (action omega (i + 1)))
          (RewardKernel.selectedMeasure rewardKernel
            (pairContext i
              (History.finitePairHistoryOfTrace
                (action omega) (reward omega) i))
            (action omega (i + 1))))
      (MeasureTheory.ae
        (mu.trim
          ((History.historyFiltrationSucc action reward haction hreward).le
            i))) := by
  exact
    ConditionalExpectationReward.pair_condExpKernel_map_eq_frozen_actual_action_of_generatedActionTraceSucc_random_pair_map_eq
      (mOmega := mOmega)
      mu rewardKernel policy pairContext pairState hpairState defaultAction
      action reward haction hreward i h_action_generated
      h_random_pair_map_eq_actual_action

example {Omega Context State Action : Type}
    [mOmega : MeasurableSpace Omega] [StandardBorelSpace Omega]
    [MeasurableSpace Context] [MeasurableSpace State]
    [MeasurableSpace Action]
    (mu : MeasureTheory.Measure Omega)
    [MeasureTheory.IsFiniteMeasure mu]
    (F : MeasureTheory.Filtration Nat mOmega)
    (rewardKernel :
      RewardKernel.MarkovRewardKernel (Prod Context Action) Rat)
    (policy : Nat -> Policy.MeasurablePolicy State Action)
    (pairContext :
      (n : Nat) -> ((j : Finset.Iic n) -> Prod Action Rat) -> Context)
    (pairState :
      (n : Nat) -> ((j : Finset.Iic n) -> Prod Action Rat) -> State)
    (hpairContext : forall n : Nat, Measurable (pairContext n))
    (hpairState : forall n : Nat, Measurable (pairState n))
    (action : Omega -> ActionTrace Action)
    (reward : Omega -> RewardTrace Rat)
    (i : Nat)
    (pairHistory : Omega -> ((j : Finset.Iic i) -> Prod Action Rat))
    (h_action_next :
      @Measurable Omega Action mOmega inferInstance
        (fun omega : Omega => action omega (i + 1)))
    (h_reward_next :
      @Measurable Omega Rat mOmega inferInstance
        (fun omega : Omega => reward omega (i + 1)))
    (h_action_ae_eq_policy :
      Filter.Eventually
        (fun omega : Omega =>
          Filter.EventuallyEq
            (MeasureTheory.ae
              (@ProbabilityTheory.condExpKernel Omega mOmega _ mu _ (F i)
                omega))
            (fun y : Omega => action y (i + 1))
            (fun _y : Omega =>
              (policy i).action (pairState i (pairHistory omega))))
        (MeasureTheory.ae (mu.trim (F.le i))))
    (h_reward_map_eq :
      Filter.Eventually
        (fun omega : Omega =>
          @MeasureTheory.Measure.map Omega Rat mOmega inferInstance
            (fun y : Omega => reward y (i + 1))
            (@ProbabilityTheory.condExpKernel Omega mOmega _ mu _ (F i)
              omega) =
          RewardKernel.selectedMeasure rewardKernel
            (pairContext i (pairHistory omega))
            ((policy i).action (pairState i (pairHistory omega))))
        (MeasureTheory.ae (mu.trim (F.le i)))) :
    Filter.Eventually
      (fun omega : Omega =>
        @MeasureTheory.Measure.map Omega (Prod Action Rat) mOmega inferInstance
          (fun y : Omega => (action y (i + 1), reward y (i + 1)))
          (@ProbabilityTheory.condExpKernel Omega mOmega _ mu _ (F i)
            omega) =
        RewardKernel.actionRewardHistoryStepKernelFamily rewardKernel policy
          pairContext pairState hpairContext hpairState i
          (pairHistory omega))
      (MeasureTheory.ae (mu.trim (F.le i))) := by
  exact
    ConditionalExpectationReward.actionRewardHistoryStepKernelFamily_pair_map_eq_of_action_ae_eq_policy_reward_map_eq
      (mOmega := mOmega)
      mu F rewardKernel policy pairContext pairState hpairContext hpairState
      action reward i pairHistory h_action_next h_reward_next
      h_action_ae_eq_policy h_reward_map_eq

example {Omega Context State Action : Type}
    [mOmega : MeasurableSpace Omega] [StandardBorelSpace Omega]
    [MeasurableSpace Context] [MeasurableSpace State]
    [MeasurableSpace Action] [MeasurableSingletonClass Action]
    [Countable Action]
    (mu : MeasureTheory.Measure Omega)
    [MeasureTheory.IsFiniteMeasure mu]
    (rewardKernel :
      RewardKernel.MarkovRewardKernel (Prod Context Action) Rat)
    (policy : Nat -> Policy.MeasurablePolicy State Action)
    (pairContext :
      (n : Nat) -> ((j : Finset.Iic n) -> Prod Action Rat) -> Context)
    (pairState :
      (n : Nat) -> ((j : Finset.Iic n) -> Prod Action Rat) -> State)
    (hpairContext : forall n : Nat, Measurable (pairContext n))
    (hpairState : forall n : Nat, Measurable (pairState n))
    (defaultAction : Action)
    (action : Omega -> ActionTrace Action)
    (reward : Omega -> RewardTrace Rat)
    (haction : forall t : Nat,
      Measurable (fun omega : Omega => action omega t))
    (hreward : forall t : Nat,
      Measurable (fun omega : Omega => reward omega t))
    (i : Nat)
    (h_action_generated :
      action =
        Policy.generatedActionTraceSucc policy
          (fun n omega =>
            pairState n
              (History.finitePairHistoryOfTrace
                (action omega) (reward omega) n))
          defaultAction)
    (h_reward_map_eq_actual_action :
      Filter.Eventually
        (fun omega : Omega =>
          @MeasureTheory.Measure.map Omega Rat mOmega inferInstance
            (fun y : Omega => reward y (i + 1))
            (@ProbabilityTheory.condExpKernel Omega mOmega _ mu _
              ((History.historyFiltrationSucc action reward haction hreward) i)
              omega) =
          RewardKernel.selectedMeasure rewardKernel
            (pairContext i
              (History.finitePairHistoryOfTrace
                (action omega) (reward omega) i))
            (action omega (i + 1)))
        (MeasureTheory.ae
          (mu.trim
            ((History.historyFiltrationSucc action reward haction hreward).le
              i)))) :
    Filter.Eventually
      (fun omega : Omega =>
        @MeasureTheory.Measure.map Omega (Prod Action Rat) mOmega inferInstance
          (fun y : Omega => (action y (i + 1), reward y (i + 1)))
          (@ProbabilityTheory.condExpKernel Omega mOmega _ mu _
            ((History.historyFiltrationSucc action reward haction hreward) i)
            omega) =
        RewardKernel.actionRewardHistoryStepKernelFamily rewardKernel policy
          pairContext pairState hpairContext hpairState i
          (History.finitePairHistoryOfTrace
            (action omega) (reward omega) i))
      (MeasureTheory.ae
        (mu.trim
          ((History.historyFiltrationSucc action reward haction hreward).le
            i))) := by
  exact
    ConditionalExpectationReward.actionRewardHistoryStepKernelFamily_pair_map_eq_historyFiltrationSucc_finitePairHistoryOfTrace_of_generatedActionTraceSucc_reward_map_eq_actual_action
      (mOmega := mOmega)
      mu rewardKernel policy pairContext pairState hpairContext hpairState
      defaultAction action reward haction hreward i h_action_generated
      h_reward_map_eq_actual_action

example {Omega Context State Action : Type}
    [mOmega : MeasurableSpace Omega] [StandardBorelSpace Omega]
    [MeasurableSpace Context] [MeasurableSpace State]
    [MeasurableSpace Action] [MeasurableSingletonClass Action]
    [Countable Action]
    (mu : MeasureTheory.Measure Omega)
    [MeasureTheory.IsFiniteMeasure mu]
    (rewardKernel :
      RewardKernel.MarkovRewardKernel (Prod Context Action) Rat)
    (policy : Nat -> Policy.MeasurablePolicy State Action)
    (pairContext :
      (n : Nat) -> ((j : Finset.Iic n) -> Prod Action Rat) -> Context)
    (pairState :
      (n : Nat) -> ((j : Finset.Iic n) -> Prod Action Rat) -> State)
    (hpairContext : forall n : Nat, Measurable (pairContext n))
    (hpairState : forall n : Nat, Measurable (pairState n))
    (defaultAction : Action)
    (action : Omega -> ActionTrace Action)
    (reward : Omega -> RewardTrace Rat)
    (haction : forall t : Nat,
      Measurable (fun omega : Omega => action omega t))
    (hreward : forall t : Nat,
      Measurable (fun omega : Omega => reward omega t))
    (i : Nat)
    (h_action_generated :
      action =
        Policy.generatedActionTraceSucc policy
          (fun n omega =>
            pairState n
              (History.finitePairHistoryOfTrace
                (action omega) (reward omega) n))
          defaultAction)
    (h_random_pair_map_eq_actual_action :
      Filter.Eventually
        (fun omega : Omega =>
          @MeasureTheory.Measure.map Omega (Prod Action Rat) mOmega
            inferInstance
            (fun y : Omega => (action y (i + 1), reward y (i + 1)))
            (@ProbabilityTheory.condExpKernel Omega mOmega _ mu _
              ((History.historyFiltrationSucc action reward haction hreward) i)
              omega) =
          MeasureTheory.Measure.map
            (Prod.mk (action omega (i + 1)))
            (RewardKernel.selectedMeasure rewardKernel
              (pairContext i
                (History.finitePairHistoryOfTrace
                  (action omega) (reward omega) i))
              (action omega (i + 1))))
        (MeasureTheory.ae
          (mu.trim
            ((History.historyFiltrationSucc action reward haction hreward).le
              i)))) :
    Filter.Eventually
      (fun omega : Omega =>
        @MeasureTheory.Measure.map Omega (Prod Action Rat) mOmega inferInstance
          (fun y : Omega => (action y (i + 1), reward y (i + 1)))
          (@ProbabilityTheory.condExpKernel Omega mOmega _ mu _
            ((History.historyFiltrationSucc action reward haction hreward) i)
            omega) =
        RewardKernel.actionRewardHistoryStepKernelFamily rewardKernel policy
          pairContext pairState hpairContext hpairState i
          (History.finitePairHistoryOfTrace
            (action omega) (reward omega) i))
      (MeasureTheory.ae
        (mu.trim
          ((History.historyFiltrationSucc action reward haction hreward).le
            i))) := by
  exact
    ConditionalExpectationReward.actionRewardHistoryStepKernelFamily_pair_map_eq_historyFiltrationSucc_finitePairHistoryOfTrace_of_generatedActionTraceSucc_random_pair_map_eq_actual_action
      (mOmega := mOmega)
      mu rewardKernel policy pairContext pairState hpairContext hpairState
      defaultAction action reward haction hreward i h_action_generated
      h_random_pair_map_eq_actual_action

example {Omega Context State Action : Type}
    [mOmega : MeasurableSpace Omega] [StandardBorelSpace Omega]
    [MeasurableSpace Context] [MeasurableSpace State]
    [MeasurableSpace Action] [MeasurableSingletonClass Action]
    [Countable Action]
    (mu : MeasureTheory.Measure Omega)
    [MeasureTheory.IsFiniteMeasure mu]
    (rewardKernel :
      RewardKernel.MarkovRewardKernel (Prod Context Action) Rat)
    (policy : Nat -> Policy.MeasurablePolicy State Action)
    (context : (n : Nat) -> ((j : Finset.Iic n) -> Rat) -> Context)
    (state : (n : Nat) -> ((j : Finset.Iic n) -> Rat) -> State)
    (hcontext : forall n : Nat, Measurable (context n))
    (hstate : forall n : Nat, Measurable (state n))
    (defaultAction : Action)
    (action : Omega -> ActionTrace Action)
    (reward : Omega -> RewardTrace Rat)
    (haction : forall t : Nat,
      @Measurable Omega Action mOmega inferInstance
        (fun omega : Omega => action omega t))
    (hreward : forall t : Nat,
      @Measurable Omega Rat mOmega inferInstance
        (fun omega : Omega => reward omega t))
    (i : Nat)
    (h_action_generated :
      action =
        Policy.generatedActionTraceSucc policy
          (fun n omega =>
            state n (History.finiteRewardHistoryOfTrace (reward omega) n))
          defaultAction)
    (h_reward_map_eq_actual_action :
      Filter.Eventually
        (fun omega : Omega =>
          @MeasureTheory.Measure.map Omega Rat mOmega inferInstance
            (fun y : Omega => reward y (i + 1))
            (@ProbabilityTheory.condExpKernel Omega mOmega _ mu _
              ((History.historyFiltrationSucc action reward haction hreward) i)
              omega) =
          RewardKernel.selectedMeasure rewardKernel
            (context i
              (History.finiteRewardHistoryOfTrace (reward omega) i))
            (action omega (i + 1)))
        (MeasureTheory.ae
          (mu.trim
            ((History.historyFiltrationSucc action reward haction hreward).le
              i)))) :
    Filter.Eventually
      (fun omega : Omega =>
        @MeasureTheory.Measure.map Omega
          ((j : Finset.Iic (i + 1)) -> Prod Action Rat) mOmega
          inferInstance
          (fun y : Omega =>
            History.extendPairHistorySucc
              (History.finitePairHistoryOfTrace
                (action omega) (reward omega) i)
              (action y (i + 1), reward y (i + 1)))
          (@ProbabilityTheory.condExpKernel Omega mOmega _ mu _
            ((History.historyFiltrationSucc action reward haction hreward) i)
            omega) =
        RewardKernel.actionRewardPartialTrajectoryKernel rewardKernel policy
          (fun n history =>
            context n (History.pairHistoryRewardProjection history))
          (fun n history =>
            state n (History.pairHistoryRewardProjection history))
          (fun n : Nat =>
            (hcontext n).comp
              (History.measurable_pairHistoryRewardProjection
                (Action := Action) (Reward := Rat) n))
          (fun n : Nat =>
            (hstate n).comp
              (History.measurable_pairHistoryRewardProjection
                (Action := Action) (Reward := Rat) n))
          i (i + 1)
          (History.finitePairHistoryOfTrace
            (action omega) (reward omega) i))
      (MeasureTheory.ae
        (mu.trim
          ((History.historyFiltrationSucc action reward haction hreward).le
            i))) := by
  exact
    ConditionalExpectationReward.actionRewardPartialTrajectoryKernel_extend_map_eq_historyFiltrationSucc_finitePairHistoryOfTrace_of_generatedActionTraceSucc_reward_map_eq_actual_action
      (mOmega := mOmega)
      mu action rewardKernel policy context state hcontext hstate defaultAction
      reward haction hreward i h_action_generated
      h_reward_map_eq_actual_action

example {Omega Context State Action : Type}
    [mOmega : MeasurableSpace Omega] [StandardBorelSpace Omega]
    [MeasurableSpace Context] [MeasurableSpace State]
    [MeasurableSpace Action] [MeasurableSingletonClass Action]
    [Countable Action]
    (mu : MeasureTheory.Measure Omega)
    [MeasureTheory.IsFiniteMeasure mu]
    (rewardKernel :
      RewardKernel.MarkovRewardKernel (Prod Context Action) Rat)
    (policy : Nat -> Policy.MeasurablePolicy State Action)
    (context : (n : Nat) -> ((j : Finset.Iic n) -> Rat) -> Context)
    (state : (n : Nat) -> ((j : Finset.Iic n) -> Rat) -> State)
    (hcontext : forall n : Nat, Measurable (context n))
    (hstate : forall n : Nat, Measurable (state n))
    (defaultAction : Action)
    (action : Omega -> ActionTrace Action)
    (reward : Omega -> RewardTrace Rat)
    (haction : forall t : Nat,
      @Measurable Omega Action mOmega inferInstance
        (fun omega : Omega => action omega t))
    (hreward : forall t : Nat,
      @Measurable Omega Rat mOmega inferInstance
        (fun omega : Omega => reward omega t))
    (i : Nat)
    (h_action_generated :
      action =
        Policy.generatedActionTraceSucc policy
          (fun n omega =>
            state n (History.finiteRewardHistoryOfTrace (reward omega) n))
          defaultAction)
    (h_reward_map_eq_actual_action :
      Filter.Eventually
        (fun omega : Omega =>
          @MeasureTheory.Measure.map Omega Rat mOmega inferInstance
            (fun y : Omega => reward y (i + 1))
            (@ProbabilityTheory.condExpKernel Omega mOmega _ mu _
              ((History.historyFiltrationSucc action reward haction hreward) i)
              omega) =
          RewardKernel.selectedMeasure rewardKernel
            (context i
              (History.finiteRewardHistoryOfTrace (reward omega) i))
            (action omega (i + 1)))
        (MeasureTheory.ae
          (mu.trim
            ((History.historyFiltrationSucc action reward haction hreward).le
              i)))) :
    Filter.Eventually
      (fun omega : Omega =>
        @MeasureTheory.Measure.map Omega
          ((j : Finset.Iic (i + 1)) -> Prod Action Rat) mOmega
          inferInstance
          (fun y : Omega =>
            History.finitePairHistoryOfTrace
              (action y) (reward y) (i + 1))
          (@ProbabilityTheory.condExpKernel Omega mOmega _ mu _
            ((History.historyFiltrationSucc action reward haction hreward) i)
            omega) =
        RewardKernel.actionRewardPartialTrajectoryKernel rewardKernel policy
          (fun n history =>
            context n (History.pairHistoryRewardProjection history))
          (fun n history =>
            state n (History.pairHistoryRewardProjection history))
          (fun n : Nat =>
            (hcontext n).comp
              (History.measurable_pairHistoryRewardProjection
                (Action := Action) (Reward := Rat) n))
          (fun n : Nat =>
            (hstate n).comp
              (History.measurable_pairHistoryRewardProjection
                (Action := Action) (Reward := Rat) n))
          i (i + 1)
          (History.finitePairHistoryOfTrace
            (action omega) (reward omega) i))
      (MeasureTheory.ae
        (mu.trim
          ((History.historyFiltrationSucc action reward haction hreward).le
            i))) := by
  exact
    ConditionalExpectationReward.actionRewardPartialTrajectoryKernel_map_eq_historyFiltrationSucc_finitePairHistoryOfTrace_of_generatedActionTraceSucc_reward_map_eq_actual_action
      (mOmega := mOmega)
      mu action rewardKernel policy context state hcontext hstate defaultAction
      reward haction hreward i h_action_generated
      h_reward_map_eq_actual_action

example {Omega Context State Action : Type}
    [mOmega : MeasurableSpace Omega] [StandardBorelSpace Omega]
    [MeasurableSpace Context] [MeasurableSpace State]
    [MeasurableSpace Action] [MeasurableSingletonClass Action]
    [Countable Action]
    (mu : MeasureTheory.Measure Omega)
    [MeasureTheory.IsFiniteMeasure mu]
    (rewardKernel :
      RewardKernel.MarkovRewardKernel (Prod Context Action) Rat)
    (policy : Nat -> Policy.MeasurablePolicy State Action)
    (context : (n : Nat) -> ((j : Finset.Iic n) -> Rat) -> Context)
    (state : (n : Nat) -> ((j : Finset.Iic n) -> Rat) -> State)
    (hcontext : forall n : Nat, Measurable (context n))
    (hstate : forall n : Nat, Measurable (state n))
    (action : Omega -> ActionTrace Action)
    (reward : Omega -> RewardTrace Rat)
    (haction : forall t : Nat,
      @Measurable Omega Action mOmega inferInstance
        (fun omega : Omega => action omega t))
    (hreward : forall t : Nat,
      @Measurable Omega Rat mOmega inferInstance
        (fun omega : Omega => reward omega t))
    (i : Nat)
    (h_kernel_extend_map_eq :
      Filter.Eventually
        (fun omega : Omega =>
          @MeasureTheory.Measure.map Omega
            ((j : Finset.Iic (i + 1)) -> Prod Action Rat) mOmega
            inferInstance
            (fun y : Omega =>
              History.extendPairHistorySucc
                (History.finitePairHistoryOfTrace
                  (action omega) (reward omega) i)
                (action y (i + 1), reward y (i + 1)))
            (@ProbabilityTheory.condExpKernel Omega mOmega _ mu _
              ((History.historyFiltrationSucc action reward haction hreward) i)
              omega) =
          RewardKernel.actionRewardPartialTrajectoryKernel rewardKernel policy
            (fun n history =>
              context n (History.pairHistoryRewardProjection history))
            (fun n history =>
              state n (History.pairHistoryRewardProjection history))
            (fun n : Nat =>
              (hcontext n).comp
                (History.measurable_pairHistoryRewardProjection
                  (Action := Action) (Reward := Rat) n))
            (fun n : Nat =>
              (hstate n).comp
                (History.measurable_pairHistoryRewardProjection
                  (Action := Action) (Reward := Rat) n))
            i (i + 1)
            (History.finitePairHistoryOfTrace
              (action omega) (reward omega) i))
        (MeasureTheory.ae
          (mu.trim
            ((History.historyFiltrationSucc action reward haction hreward).le
              i)))) :
    Filter.Eventually
      (fun omega : Omega =>
        @MeasureTheory.Measure.map Omega
          ((j : Finset.Iic (i + 1)) -> Prod Action Rat) mOmega
          inferInstance
          (fun y : Omega =>
            History.finitePairHistoryOfTrace
              (action y) (reward y) (i + 1))
          (@ProbabilityTheory.condExpKernel Omega mOmega _ mu _
            ((History.historyFiltrationSucc action reward haction hreward) i)
            omega) =
        RewardKernel.actionRewardPartialTrajectoryKernel rewardKernel policy
          (fun n history =>
            context n (History.pairHistoryRewardProjection history))
          (fun n history =>
            state n (History.pairHistoryRewardProjection history))
          (fun n : Nat =>
            (hcontext n).comp
              (History.measurable_pairHistoryRewardProjection
                (Action := Action) (Reward := Rat) n))
          (fun n : Nat =>
            (hstate n).comp
              (History.measurable_pairHistoryRewardProjection
                (Action := Action) (Reward := Rat) n))
          i (i + 1)
          (History.finitePairHistoryOfTrace
            (action omega) (reward omega) i))
      (MeasureTheory.ae
        (mu.trim
          ((History.historyFiltrationSucc action reward haction hreward).le
            i))) := by
  exact
    ConditionalExpectationReward.actionRewardPartialTrajectoryKernel_map_eq_of_extend_map_eq_historyFiltrationSucc_finitePairHistoryOfTrace
      (mOmega := mOmega)
      mu action rewardKernel policy context state hcontext hstate reward
      haction hreward i h_kernel_extend_map_eq

example {Omega Context State Action : Type}
    [mOmega : MeasurableSpace Omega] [StandardBorelSpace Omega]
    [MeasurableSpace Context] [MeasurableSpace State]
    [MeasurableSpace Action] [MeasurableSingletonClass Action]
    [Countable Action]
    (mu : MeasureTheory.Measure Omega)
    [MeasureTheory.IsFiniteMeasure mu]
    (action : Omega -> ActionTrace Action)
    (rewardKernel :
      RewardKernel.MarkovRewardKernel (Prod Context Action) Rat)
    (policy : Nat -> Policy.MeasurablePolicy State Action)
    (context : (n : Nat) -> ((j : Finset.Iic n) -> Rat) -> Context)
    (state : (n : Nat) -> ((j : Finset.Iic n) -> Rat) -> State)
    (hcontext : forall n : Nat, Measurable (context n))
    (hstate : forall n : Nat, Measurable (state n))
    (defaultAction : Action)
    (reward : Omega -> RewardTrace Rat)
    (haction : forall t : Nat,
      @Measurable Omega Action mOmega inferInstance
        (fun omega : Omega => action omega t))
    (hreward : forall t : Nat,
      @Measurable Omega Rat mOmega inferInstance
        (fun omega : Omega => reward omega t))
    (i : Nat)
    (h_action_generated :
      action =
        Policy.generatedActionTraceSucc policy
          (fun n omega =>
            state n (History.finiteRewardHistoryOfTrace (reward omega) n))
          defaultAction)
    (h_kernel_extend_map_eq :
      Filter.Eventually
        (fun omega : Omega =>
          @MeasureTheory.Measure.map Omega
            ((j : Finset.Iic (i + 1)) -> Prod Action Rat) mOmega
            inferInstance
            (fun y : Omega =>
              History.extendPairHistorySucc
                (History.finitePairHistoryOfTrace
                  (action omega) (reward omega) i)
                (action y (i + 1), reward y (i + 1)))
            (@ProbabilityTheory.condExpKernel Omega mOmega _ mu _
              ((History.historyFiltrationSucc action reward haction hreward) i)
              omega) =
          RewardKernel.actionRewardPartialTrajectoryKernel rewardKernel policy
            (fun n history =>
              context n (History.pairHistoryRewardProjection history))
            (fun n history =>
              state n (History.pairHistoryRewardProjection history))
            (fun n : Nat =>
              (hcontext n).comp
                (History.measurable_pairHistoryRewardProjection
                  (Action := Action) (Reward := Rat) n))
            (fun n : Nat =>
              (hstate n).comp
                (History.measurable_pairHistoryRewardProjection
                  (Action := Action) (Reward := Rat) n))
            i (i + 1)
            (History.finitePairHistoryOfTrace
              (action omega) (reward omega) i))
        (MeasureTheory.ae
          (mu.trim
            ((History.historyFiltrationSucc action reward haction hreward).le
              i)))) :
    Filter.Eventually
      (fun omega : Omega =>
        @MeasureTheory.Measure.map Omega Rat mOmega inferInstance
          (fun y : Omega => reward y (i + 1))
          (@ProbabilityTheory.condExpKernel Omega mOmega _ mu _
            ((History.historyFiltrationSucc action reward haction hreward) i)
            omega) =
        RewardKernel.selectedMeasure rewardKernel
          (context i (History.finiteRewardHistoryOfTrace (reward omega) i))
          (action omega (i + 1)))
      (MeasureTheory.ae
        (mu.trim
          ((History.historyFiltrationSucc action reward haction hreward).le
            i))) := by
  exact
    ConditionalExpectationReward.reward_condExpKernel_map_eq_selected_actual_action_of_generatedActionTraceSucc_actionRewardPartialTrajectoryKernel_extend_map_eq_historyFiltrationSucc_finitePairHistoryOfTrace
      (mOmega := mOmega)
      mu action rewardKernel policy context state hcontext hstate defaultAction
      reward haction hreward i h_action_generated h_kernel_extend_map_eq

example {Omega Context State Action : Type}
    [mOmega : MeasurableSpace Omega] [StandardBorelSpace Omega]
    [MeasurableSpace Context] [MeasurableSpace State]
    [MeasurableSpace Action] [MeasurableSingletonClass Action]
    (mu : MeasureTheory.Measure Omega)
    [MeasureTheory.IsFiniteMeasure mu]
    (action : Omega -> ActionTrace Action)
    (rewardKernel :
      RewardKernel.MarkovRewardKernel (Prod Context Action) Rat)
    (policy : Nat -> Policy.MeasurablePolicy State Action)
    (context : (n : Nat) -> ((j : Finset.Iic n) -> Rat) -> Context)
    (state : (n : Nat) -> ((j : Finset.Iic n) -> Rat) -> State)
    (hcontext : forall n : Nat, Measurable (context n))
    (hstate : forall n : Nat, Measurable (state n))
    (defaultAction : Action)
    (reward : Omega -> RewardTrace Rat)
    (haction : forall t : Nat,
      @Measurable Omega Action mOmega inferInstance
        (fun omega : Omega => action omega t))
    (hreward : forall t : Nat,
      @Measurable Omega Rat mOmega inferInstance
        (fun omega : Omega => reward omega t))
    (i : Nat)
    (h_action_generated :
      action =
        Policy.generatedActionTraceSucc policy
          (fun n omega =>
            state n (History.finiteRewardHistoryOfTrace (reward omega) n))
          defaultAction)
    (h_kernel_pair_map_eq :
      Filter.Eventually
        (fun omega : Omega =>
          @MeasureTheory.Measure.map Omega (Prod Action Rat) mOmega
            inferInstance
            (fun y : Omega => (action y (i + 1), reward y (i + 1)))
            (@ProbabilityTheory.condExpKernel Omega mOmega _ mu _
              ((History.historyFiltrationSucc action reward haction hreward) i)
              omega) =
          RewardKernel.actionRewardHistoryStepKernelFamily rewardKernel policy
            (fun n history =>
              context n (History.pairHistoryRewardProjection history))
            (fun n history =>
              state n (History.pairHistoryRewardProjection history))
            (fun n : Nat =>
              (hcontext n).comp
                (History.measurable_pairHistoryRewardProjection
                  (Action := Action) (Reward := Rat) n))
            (fun n : Nat =>
              (hstate n).comp
                (History.measurable_pairHistoryRewardProjection
                  (Action := Action) (Reward := Rat) n))
            i
            (History.finitePairHistoryOfTrace
              (action omega) (reward omega) i))
        (MeasureTheory.ae
          (mu.trim
            ((History.historyFiltrationSucc action reward haction hreward).le
              i)))) :
    Filter.Eventually
      (fun omega : Omega =>
        @MeasureTheory.Measure.map Omega Rat mOmega inferInstance
          (fun y : Omega => reward y (i + 1))
          (@ProbabilityTheory.condExpKernel Omega mOmega _ mu _
            ((History.historyFiltrationSucc action reward haction hreward) i)
            omega) =
        RewardKernel.selectedMeasure rewardKernel
          (context i (History.finiteRewardHistoryOfTrace (reward omega) i))
          (action omega (i + 1)))
      (MeasureTheory.ae
        (mu.trim
          ((History.historyFiltrationSucc action reward haction hreward).le
            i))) := by
  exact
    ConditionalExpectationReward.reward_condExpKernel_map_eq_selected_actual_action_of_generatedActionTraceSucc_actionRewardHistoryStepKernelFamily_pair_map_eq_historyFiltrationSucc_finitePairHistoryOfTrace
      (mOmega := mOmega)
      mu action rewardKernel policy context state hcontext hstate defaultAction
      reward haction hreward i h_action_generated h_kernel_pair_map_eq

example {Omega Context State Action : Type}
    [mOmega : MeasurableSpace Omega] [StandardBorelSpace Omega]
    [MeasurableSpace Context] [MeasurableSpace State]
    [MeasurableSpace Action] [MeasurableSingletonClass Action]
    (mu : MeasureTheory.Measure Omega)
    [MeasureTheory.IsFiniteMeasure mu]
    (rewardKernel :
      RewardKernel.MarkovRewardKernel (Prod Context Action) Rat)
    (policy : Nat -> Policy.MeasurablePolicy State Action)
    (context : (n : Nat) -> ((j : Finset.Iic n) -> Rat) -> Context)
    (state : (n : Nat) -> ((j : Finset.Iic n) -> Rat) -> State)
    (hcontext : forall n : Nat, Measurable (context n))
    (hstate : forall n : Nat, Measurable (state n))
    (action : Omega -> ActionTrace Action)
    (reward : Omega -> RewardTrace Rat)
    (haction : forall t : Nat,
      @Measurable Omega Action mOmega inferInstance
        (fun omega : Omega => action omega t))
    (hreward : forall t : Nat,
      @Measurable Omega Rat mOmega inferInstance
        (fun omega : Omega => reward omega t))
    (i : Nat)
    (h_kernel_pair_map_eq :
      Filter.Eventually
        (fun omega : Omega =>
          @MeasureTheory.Measure.map Omega (Prod Action Rat) mOmega
            inferInstance
            (fun y : Omega => (action y (i + 1), reward y (i + 1)))
            (@ProbabilityTheory.condExpKernel Omega mOmega _ mu _
              ((History.historyFiltrationSucc action reward haction hreward) i)
              omega) =
          RewardKernel.actionRewardHistoryStepKernelFamily rewardKernel policy
            (fun n history =>
              context n (History.pairHistoryRewardProjection history))
            (fun n history =>
              state n (History.pairHistoryRewardProjection history))
            (fun n : Nat =>
              (hcontext n).comp
                (History.measurable_pairHistoryRewardProjection
                  (Action := Action) (Reward := Rat) n))
            (fun n : Nat =>
              (hstate n).comp
                (History.measurable_pairHistoryRewardProjection
                  (Action := Action) (Reward := Rat) n))
            i
            (History.finitePairHistoryOfTrace
              (action omega) (reward omega) i))
        (MeasureTheory.ae
          (mu.trim
            ((History.historyFiltrationSucc action reward haction hreward).le
              i)))) :
    Filter.Eventually
      (fun omega : Omega =>
        @MeasureTheory.Measure.map Omega
          ((j : Finset.Iic (i + 1)) -> Prod Action Rat) mOmega
          inferInstance
          (fun y : Omega =>
            History.extendPairHistorySucc
              (History.finitePairHistoryOfTrace
                (action omega) (reward omega) i)
              (action y (i + 1), reward y (i + 1)))
          (@ProbabilityTheory.condExpKernel Omega mOmega _ mu _
            ((History.historyFiltrationSucc action reward haction hreward) i)
            omega) =
        RewardKernel.actionRewardPartialTrajectoryKernel rewardKernel policy
          (fun n history =>
            context n (History.pairHistoryRewardProjection history))
          (fun n history =>
            state n (History.pairHistoryRewardProjection history))
          (fun n : Nat =>
            (hcontext n).comp
              (History.measurable_pairHistoryRewardProjection
                (Action := Action) (Reward := Rat) n))
          (fun n : Nat =>
            (hstate n).comp
              (History.measurable_pairHistoryRewardProjection
                (Action := Action) (Reward := Rat) n))
          i (i + 1)
          (History.finitePairHistoryOfTrace
            (action omega) (reward omega) i))
      (MeasureTheory.ae
        (mu.trim
          ((History.historyFiltrationSucc action reward haction hreward).le
            i))) := by
  exact
    ConditionalExpectationReward.actionRewardPartialTrajectoryKernel_extend_map_eq_of_actionRewardHistoryStepKernelFamily_pair_map_eq_historyFiltrationSucc_finitePairHistoryOfTrace
      (mOmega := mOmega)
      mu action rewardKernel policy context state hcontext hstate reward
      haction hreward i h_kernel_pair_map_eq

example {Omega Context State Action : Type}
    [mOmega : MeasurableSpace Omega] [StandardBorelSpace Omega]
    [MeasurableSpace Context] [MeasurableSpace State]
    [MeasurableSpace Action] [MeasurableSingletonClass Action]
    [Countable Action]
    (mu : MeasureTheory.Measure Omega)
    [MeasureTheory.IsFiniteMeasure mu]
    (rewardKernel :
      RewardKernel.MarkovRewardKernel (Prod Context Action) Rat)
    (policy : Nat -> Policy.MeasurablePolicy State Action)
    (context : (n : Nat) -> ((j : Finset.Iic n) -> Rat) -> Context)
    (state : (n : Nat) -> ((j : Finset.Iic n) -> Rat) -> State)
    (hcontext : forall n : Nat, Measurable (context n))
    (hstate : forall n : Nat, Measurable (state n))
    (mean : Context -> Action -> Rat)
    (varianceProxy : Context -> Action -> NNReal)
    (law :
      RewardKernel.CenteredRewardKernelLaw rewardKernel mean varianceProxy)
    (action : Omega -> ActionTrace Action)
    (reward : Omega -> RewardTrace Rat)
    (haction : forall t : Nat,
      @Measurable Omega Action mOmega inferInstance
        (fun omega : Omega => action omega t))
    (hreward : forall t : Nat,
      @Measurable Omega Rat mOmega inferInstance
        (fun omega : Omega => reward omega t))
    (i : Nat)
    (h_integrable :
      MeasureTheory.Integrable
        (fun omega : Omega =>
          (((reward omega (i + 1) -
            mean
              (context i
                (History.finiteRewardHistoryOfTrace (reward omega) i))
              ((policy i).action
                (state i
                  (History.finiteRewardHistoryOfTrace (reward omega) i))) :
                Rat) : Real))) mu)
    (h_kernel_extend_map_eq :
      Filter.Eventually
        (fun omega : Omega =>
          @MeasureTheory.Measure.map Omega
            ((j : Finset.Iic (i + 1)) -> Prod Action Rat) mOmega
            inferInstance
            (fun y : Omega =>
              History.extendPairHistorySucc
                (History.finitePairHistoryOfTrace
                  (action omega) (reward omega) i)
                (action y (i + 1), reward y (i + 1)))
            (@ProbabilityTheory.condExpKernel Omega mOmega _ mu _
              ((History.historyFiltrationSucc action reward haction hreward) i)
              omega) =
          RewardKernel.actionRewardPartialTrajectoryKernel rewardKernel policy
            (fun n history =>
              context n (History.pairHistoryRewardProjection history))
            (fun n history =>
              state n (History.pairHistoryRewardProjection history))
            (fun n : Nat =>
              (hcontext n).comp
                (History.measurable_pairHistoryRewardProjection
                  (Action := Action) (Reward := Rat) n))
            (fun n : Nat =>
              (hstate n).comp
                (History.measurable_pairHistoryRewardProjection
                  (Action := Action) (Reward := Rat) n))
            i (i + 1)
            (History.finitePairHistoryOfTrace
              (action omega) (reward omega) i))
        (MeasureTheory.ae
          (mu.trim
            ((History.historyFiltrationSucc action reward haction hreward).le
              i)))) :
    Filter.EventuallyEq (MeasureTheory.ae mu)
      (@MeasureTheory.condExp Omega Real
        ((History.historyFiltrationSucc action reward haction hreward) i)
        mOmega _ _ _ mu
        (fun omega : Omega =>
          (((reward omega (i + 1) -
            mean
              (context i
                (History.finiteRewardHistoryOfTrace (reward omega) i))
              ((policy i).action
                (state i
                  (History.finiteRewardHistoryOfTrace (reward omega) i))) :
                Rat) : Real))))
      (fun _omega : Omega => (0 : Real)) := by
  exact
    ConditionalExpectationReward.centeredReward_succ_condExp_eq_zero_of_actionRewardPartialTrajectoryKernel_extend_map_eq_historyFiltrationSucc_finitePairHistoryOfTrace
      (mOmega := mOmega)
      mu action rewardKernel policy context state hcontext hstate mean
      varianceProxy law reward haction hreward i h_integrable
      h_kernel_extend_map_eq

example {Omega Context State Action : Type}
    [mOmega : MeasurableSpace Omega] [StandardBorelSpace Omega]
    [MeasurableSpace Context] [MeasurableSpace State]
    [MeasurableSpace Action] [MeasurableSingletonClass Action]
    [Countable Action]
    (mu : MeasureTheory.Measure Omega)
    [MeasureTheory.IsFiniteMeasure mu]
    (rewardKernel :
      RewardKernel.MarkovRewardKernel (Prod Context Action) Rat)
    (policy : Nat -> Policy.MeasurablePolicy State Action)
    (context : (n : Nat) -> ((j : Finset.Iic n) -> Rat) -> Context)
    (state : (n : Nat) -> ((j : Finset.Iic n) -> Rat) -> State)
    (hcontext : forall n : Nat, Measurable (context n))
    (hstate : forall n : Nat, Measurable (state n))
    (mean : Context -> Action -> Rat)
    (varianceProxy : Context -> Action -> NNReal)
    (hmean :
      Measurable (fun pair : Prod Context Action => mean pair.1 pair.2))
    (hkernel :
      RewardKernel.CenteredRewardKernelLaw rewardKernel mean varianceProxy)
    (action : Omega -> ActionTrace Action)
    (reward : Omega -> RewardTrace Rat)
    (haction : forall t : Nat,
      @Measurable Omega Action mOmega inferInstance
        (fun omega : Omega => action omega t))
    (hreward : forall t : Nat,
      @Measurable Omega Rat mOmega inferInstance
        (fun omega : Omega => reward omega t))
    (rewardLo rewardHi meanLo meanHi : Nat -> Real)
    (hraw :
      forall i : Nat, forall omega : Omega,
        Set.Icc (rewardLo i) (rewardHi i)
          (((reward omega (i + 1) : Rat) : Real)))
    (hmean_range :
      forall i : Nat, forall context : Context, forall action : Action,
        Set.Icc (meanLo i) (meanHi i)
          (((mean context action : Rat) : Real)))
    (i : Nat)
    (h_kernel_extend_map_eq :
      Filter.Eventually
        (fun omega : Omega =>
          @MeasureTheory.Measure.map Omega
            ((j : Finset.Iic (i + 1)) -> Prod Action Rat) mOmega
            inferInstance
            (fun y : Omega =>
              History.extendPairHistorySucc
                (History.finitePairHistoryOfTrace
                  (action omega) (reward omega) i)
                (action y (i + 1), reward y (i + 1)))
            (@ProbabilityTheory.condExpKernel Omega mOmega _ mu _
              ((History.historyFiltrationSucc action reward haction hreward) i)
              omega) =
          RewardKernel.actionRewardPartialTrajectoryKernel rewardKernel policy
            (fun n history =>
              context n (History.pairHistoryRewardProjection history))
            (fun n history =>
              state n (History.pairHistoryRewardProjection history))
            (fun n : Nat =>
              (hcontext n).comp
                (History.measurable_pairHistoryRewardProjection
                  (Action := Action) (Reward := Rat) n))
            (fun n : Nat =>
              (hstate n).comp
                (History.measurable_pairHistoryRewardProjection
                  (Action := Action) (Reward := Rat) n))
            i (i + 1)
            (History.finitePairHistoryOfTrace
              (action omega) (reward omega) i))
        (MeasureTheory.ae
          (mu.trim
            ((History.historyFiltrationSucc action reward haction hreward).le
              i)))) :
    Filter.EventuallyEq (MeasureTheory.ae mu)
      (@MeasureTheory.condExp Omega Real
        ((History.historyFiltrationSucc action reward haction hreward) i)
        mOmega _ _ _ mu
        (fun omega : Omega =>
          (((reward omega (i + 1) -
            mean
              (context i
                (History.finiteRewardHistoryOfTrace (reward omega) i))
              ((policy i).action
                (state i
                  (History.finiteRewardHistoryOfTrace (reward omega) i))) :
            Rat) : Real))))
      (fun _omega : Omega => (0 : Real)) := by
  exact
    ConditionalExpectationReward.centeredReward_succ_condExp_eq_zero_of_actionRewardPartialTrajectoryKernel_extend_map_eq_historyFiltrationSucc_finitePairHistoryOfTrace_rawRangeMeasurableMeanRangeBounded
      (mOmega := mOmega)
      mu action rewardKernel policy context state hcontext hstate mean
      varianceProxy hmean hkernel reward haction hreward rewardLo rewardHi
      meanLo meanHi hraw hmean_range i h_kernel_extend_map_eq

example {Omega Context State Action : Type}
    [mOmega : MeasurableSpace Omega] [StandardBorelSpace Omega]
    [MeasurableSpace Context] [MeasurableSpace State]
    [MeasurableSpace Action] [MeasurableSingletonClass Action]
    [Countable Action]
    (mu : MeasureTheory.Measure Omega)
    [MeasureTheory.IsFiniteMeasure mu]
    (rewardKernel :
      RewardKernel.MarkovRewardKernel (Prod Context Action) Rat)
    (policy : Nat -> Policy.MeasurablePolicy State Action)
    (context : (n : Nat) -> ((j : Finset.Iic n) -> Rat) -> Context)
    (state : (n : Nat) -> ((j : Finset.Iic n) -> Rat) -> State)
    (hcontext : forall n : Nat, Measurable (context n))
    (hstate : forall n : Nat, Measurable (state n))
    (mean : Context -> Action -> Rat)
    (varianceProxy : Context -> Action -> NNReal)
    (law :
      RewardKernel.CenteredRewardKernelLaw rewardKernel mean varianceProxy)
    (defaultAction : Action)
    (action : Omega -> ActionTrace Action)
    (reward : Omega -> RewardTrace Rat)
    (haction : forall t : Nat,
      @Measurable Omega Action mOmega inferInstance
        (fun omega : Omega => action omega t))
    (hreward : forall t : Nat,
      @Measurable Omega Rat mOmega inferInstance
        (fun omega : Omega => reward omega t))
    (i : Nat)
    (h_action_generated :
      action =
        Policy.generatedActionTraceSucc policy
          (fun n omega =>
            state n (History.finiteRewardHistoryOfTrace (reward omega) n))
          defaultAction)
    (h_integrable :
      MeasureTheory.Integrable
        (fun omega : Omega =>
          (((reward omega (i + 1) -
            mean
              (context i
                (History.finiteRewardHistoryOfTrace (reward omega) i))
              ((policy i).action
                (state i
                  (History.finiteRewardHistoryOfTrace (reward omega) i))) :
                Rat) : Real))) mu)
    (h_reward_map_eq_actual_action :
      Filter.Eventually
        (fun omega : Omega =>
          @MeasureTheory.Measure.map Omega Rat mOmega inferInstance
            (fun y : Omega => reward y (i + 1))
            (@ProbabilityTheory.condExpKernel Omega mOmega _ mu _
              ((History.historyFiltrationSucc action reward haction hreward) i)
              omega) =
          RewardKernel.selectedMeasure rewardKernel
            (context i
              (History.finiteRewardHistoryOfTrace (reward omega) i))
            (action omega (i + 1)))
        (MeasureTheory.ae
          (mu.trim
            ((History.historyFiltrationSucc action reward haction hreward).le
              i)))) :
    Filter.EventuallyEq (MeasureTheory.ae mu)
      (@MeasureTheory.condExp Omega Real
        ((History.historyFiltrationSucc action reward haction hreward) i)
        mOmega _ _ _ mu
        (fun omega : Omega =>
          (((reward omega (i + 1) -
            mean
              (context i
                (History.finiteRewardHistoryOfTrace (reward omega) i))
              ((policy i).action
                (state i
                  (History.finiteRewardHistoryOfTrace (reward omega) i))) :
                Rat) : Real))))
      (fun _omega : Omega => (0 : Real)) := by
  exact
    ConditionalExpectationReward.centeredReward_succ_condExp_eq_zero_of_generatedActionTraceSucc_reward_map_eq_actual_action
      (mOmega := mOmega)
      mu action rewardKernel policy context state hcontext hstate mean
      varianceProxy law defaultAction reward haction hreward i
      h_action_generated h_integrable h_reward_map_eq_actual_action

example {Omega Context State Action : Type}
    [mOmega : MeasurableSpace Omega] [StandardBorelSpace Omega]
    [MeasurableSpace Context] [MeasurableSpace State]
    [MeasurableSpace Action] [MeasurableSingletonClass Action]
    [Countable Action]
    (mu : MeasureTheory.Measure Omega)
    [MeasureTheory.IsFiniteMeasure mu]
    (rewardKernel :
      RewardKernel.MarkovRewardKernel (Prod Context Action) Rat)
    (policy : Nat -> Policy.MeasurablePolicy State Action)
    (context : (n : Nat) -> ((j : Finset.Iic n) -> Rat) -> Context)
    (state : (n : Nat) -> ((j : Finset.Iic n) -> Rat) -> State)
    (hcontext : forall n : Nat, Measurable (context n))
    (hstate : forall n : Nat, Measurable (state n))
    (mean : Context -> Action -> Rat)
    (varianceProxy : Context -> Action -> NNReal)
    (hmean :
      Measurable (fun pair : Prod Context Action => mean pair.1 pair.2))
    (hkernel :
      RewardKernel.CenteredRewardKernelLaw rewardKernel mean varianceProxy)
    (defaultAction : Action)
    (action : Omega -> ActionTrace Action)
    (reward : Omega -> RewardTrace Rat)
    (haction : forall t : Nat,
      @Measurable Omega Action mOmega inferInstance
        (fun omega : Omega => action omega t))
    (hreward : forall t : Nat,
      @Measurable Omega Rat mOmega inferInstance
        (fun omega : Omega => reward omega t))
    (rewardLo rewardHi meanLo meanHi : Nat -> Real)
    (hraw :
      forall i : Nat, forall omega : Omega,
        Set.Icc (rewardLo i) (rewardHi i)
          (((reward omega (i + 1) : Rat) : Real)))
    (hmean_range :
      forall i : Nat, forall context : Context, forall action : Action,
        Set.Icc (meanLo i) (meanHi i)
          (((mean context action : Rat) : Real)))
    (i : Nat)
    (h_action_generated :
      action =
        Policy.generatedActionTraceSucc policy
          (fun n omega =>
            state n (History.finiteRewardHistoryOfTrace (reward omega) n))
          defaultAction)
    (h_reward_map_eq_actual_action :
      Filter.Eventually
        (fun omega : Omega =>
          @MeasureTheory.Measure.map Omega Rat mOmega inferInstance
            (fun y : Omega => reward y (i + 1))
            (@ProbabilityTheory.condExpKernel Omega mOmega _ mu _
              ((History.historyFiltrationSucc action reward haction hreward) i)
              omega) =
          RewardKernel.selectedMeasure rewardKernel
            (context i
              (History.finiteRewardHistoryOfTrace (reward omega) i))
            (action omega (i + 1)))
        (MeasureTheory.ae
          (mu.trim
            ((History.historyFiltrationSucc action reward haction hreward).le
              i)))) :
    Filter.EventuallyEq (MeasureTheory.ae mu)
      (@MeasureTheory.condExp Omega Real
        ((History.historyFiltrationSucc action reward haction hreward) i)
        mOmega _ _ _ mu
        (fun omega : Omega =>
          (((reward omega (i + 1) -
            mean
              (context i
                (History.finiteRewardHistoryOfTrace (reward omega) i))
              ((policy i).action
                (state i
                  (History.finiteRewardHistoryOfTrace (reward omega) i))) :
              Rat) : Real))))
      (fun _omega : Omega => (0 : Real)) := by
  exact
    ConditionalExpectationReward.centeredReward_succ_condExp_eq_zero_of_generatedActionTraceSucc_reward_map_eq_actual_action_rawRangeMeasurableMeanRangeBounded
      (mOmega := mOmega)
      mu action rewardKernel policy context state hcontext hstate mean
      varianceProxy hmean hkernel defaultAction reward haction hreward
      rewardLo rewardHi meanLo meanHi hraw hmean_range i
      h_action_generated h_reward_map_eq_actual_action

example {Omega Context State Action : Type}
    [mOmega : MeasurableSpace Omega] [StandardBorelSpace Omega]
    [MeasurableSpace Context] [MeasurableSpace State]
    [MeasurableSpace Action] [MeasurableSingletonClass Action]
    [Countable Action]
    (mu : MeasureTheory.Measure Omega)
    [MeasureTheory.IsFiniteMeasure mu]
    (rewardKernel :
      RewardKernel.MarkovRewardKernel (Prod Context Action) Rat)
    (policy : Nat -> Policy.MeasurablePolicy State Action)
    (context : (n : Nat) -> ((j : Finset.Iic n) -> Rat) -> Context)
    (state : (n : Nat) -> ((j : Finset.Iic n) -> Rat) -> State)
    (hcontext : forall n : Nat, Measurable (context n))
    (hstate : forall n : Nat, Measurable (state n))
    (mean : Context -> Action -> Rat)
    (varianceProxy : Context -> Action -> NNReal)
    (hmean :
      Measurable (fun pair : Prod Context Action => mean pair.1 pair.2))
    (hkernel :
      RewardKernel.CenteredRewardKernelLaw rewardKernel mean varianceProxy)
    (defaultAction : Action)
    (action : Omega -> ActionTrace Action)
    (reward : Omega -> RewardTrace Rat)
    (haction : forall t : Nat,
      @Measurable Omega Action mOmega inferInstance
        (fun omega : Omega => action omega t))
    (hreward : forall t : Nat,
      @Measurable Omega Rat mOmega inferInstance
        (fun omega : Omega => reward omega t))
    (rewardLo rewardHi meanLo meanHi : Nat -> Real)
    (hraw :
      forall i : Nat, forall omega : Omega,
        Set.Icc (rewardLo i) (rewardHi i)
          (((reward omega (i + 1) : Rat) : Real)))
    (hmean_range :
      forall i : Nat, forall context : Context, forall action : Action,
        Set.Icc (meanLo i) (meanHi i)
          (((mean context action : Rat) : Real)))
    (i : Nat)
    (h_action_generated :
      action =
        Policy.generatedActionTraceSucc policy
          (fun n omega =>
            state n (History.finiteRewardHistoryOfTrace (reward omega) n))
          defaultAction)
    (h_kernel_partialtraj_map_eq :
      Filter.Eventually
        (fun omega : Omega =>
          @MeasureTheory.Measure.map Omega
            ((j : Finset.Iic (i + 1)) -> Prod Action Rat) mOmega
            inferInstance
            (fun y : Omega =>
              History.finitePairHistoryOfTrace
                (action y) (reward y) (i + 1))
            (@ProbabilityTheory.condExpKernel Omega mOmega _ mu _
              ((History.historyFiltrationSucc action reward haction hreward) i)
              omega) =
          RewardKernel.actionRewardPartialTrajectoryKernel rewardKernel policy
            (fun n history =>
              context n (History.pairHistoryRewardProjection history))
            (fun n history =>
              state n (History.pairHistoryRewardProjection history))
            (fun n : Nat =>
              (hcontext n).comp
                (History.measurable_pairHistoryRewardProjection
                  (Action := Action) (Reward := Rat) n))
            (fun n : Nat =>
              (hstate n).comp
                (History.measurable_pairHistoryRewardProjection
                  (Action := Action) (Reward := Rat) n))
            i (i + 1)
            (History.finitePairHistoryOfTrace
              (action omega) (reward omega) i))
        (MeasureTheory.ae
          (mu.trim
            ((History.historyFiltrationSucc action reward haction hreward).le
              i)))) :
    Filter.EventuallyEq (MeasureTheory.ae mu)
      (@MeasureTheory.condExp Omega Real
        ((History.historyFiltrationSucc action reward haction hreward) i)
        mOmega _ _ _ mu
        (fun omega : Omega =>
          (((reward omega (i + 1) -
            mean
              (context i
                (History.finiteRewardHistoryOfTrace (reward omega) i))
              ((policy i).action
                (state i
                  (History.finiteRewardHistoryOfTrace (reward omega) i))) :
              Rat) : Real))))
      (fun _omega : Omega => (0 : Real)) := by
  exact
    ConditionalExpectationReward.centeredReward_succ_condExp_eq_zero_of_generatedActionTraceSucc_actionRewardPartialTrajectoryKernel_map_eq_historyFiltrationSucc_finitePairHistoryOfTrace_rawRangeMeasurableMeanRangeBounded
      (mOmega := mOmega)
      mu action rewardKernel policy context state hcontext hstate mean
      varianceProxy hmean hkernel defaultAction reward haction hreward
      rewardLo rewardHi meanLo meanHi hraw hmean_range i
      h_action_generated h_kernel_partialtraj_map_eq

example {Omega Context State Action : Type}
    [mOmega : MeasurableSpace Omega] [StandardBorelSpace Omega]
    [MeasurableSpace Context] [MeasurableSpace State]
    [MeasurableSpace Action] [MeasurableSingletonClass Action]
    [Countable Action]
    (mu : MeasureTheory.Measure Omega)
    [MeasureTheory.IsFiniteMeasure mu]
    (rewardKernel :
      RewardKernel.MarkovRewardKernel (Prod Context Action) Rat)
    (policy : Nat -> Policy.MeasurablePolicy State Action)
    (context : (n : Nat) -> ((j : Finset.Iic n) -> Rat) -> Context)
    (state : (n : Nat) -> ((j : Finset.Iic n) -> Rat) -> State)
    (hcontext : forall n : Nat, Measurable (context n))
    (hstate : forall n : Nat, Measurable (state n))
    (mean : Context -> Action -> Rat)
    (varianceProxy : Context -> Action -> NNReal)
    (hmean :
      Measurable (fun pair : Prod Context Action => mean pair.1 pair.2))
    (hkernel :
      RewardKernel.CenteredRewardKernelLaw rewardKernel mean varianceProxy)
    (defaultAction : Action)
    (action : Omega -> ActionTrace Action)
    (reward : Omega -> RewardTrace Rat)
    (haction : forall t : Nat,
      @Measurable Omega Action mOmega inferInstance
        (fun omega : Omega => action omega t))
    (hreward : forall t : Nat,
      @Measurable Omega Rat mOmega inferInstance
        (fun omega : Omega => reward omega t))
    (rewardLo rewardHi meanLo meanHi : Nat -> Real)
    (hraw :
      forall i : Nat, forall omega : Omega,
        Set.Icc (rewardLo i) (rewardHi i)
          (((reward omega (i + 1) : Rat) : Real)))
    (hmean_range :
      forall i : Nat, forall context : Context, forall action : Action,
        Set.Icc (meanLo i) (meanHi i)
          (((mean context action : Rat) : Real)))
    (i : Nat)
    (h_action_generated :
      action =
        Policy.generatedActionTraceSucc policy
          (fun n omega =>
            state n (History.finiteRewardHistoryOfTrace (reward omega) n))
          defaultAction)
    (h_kernel_extend_map_eq :
      Filter.Eventually
        (fun omega : Omega =>
          @MeasureTheory.Measure.map Omega
            ((j : Finset.Iic (i + 1)) -> Prod Action Rat) mOmega
            inferInstance
            (fun y : Omega =>
              History.extendPairHistorySucc
                (History.finitePairHistoryOfTrace
                  (action omega) (reward omega) i)
                (action y (i + 1), reward y (i + 1)))
            (@ProbabilityTheory.condExpKernel Omega mOmega _ mu _
              ((History.historyFiltrationSucc action reward haction hreward) i)
              omega) =
          RewardKernel.actionRewardPartialTrajectoryKernel rewardKernel policy
            (fun n history =>
              context n (History.pairHistoryRewardProjection history))
            (fun n history =>
              state n (History.pairHistoryRewardProjection history))
            (fun n : Nat =>
              (hcontext n).comp
                (History.measurable_pairHistoryRewardProjection
                  (Action := Action) (Reward := Rat) n))
            (fun n : Nat =>
              (hstate n).comp
                (History.measurable_pairHistoryRewardProjection
                  (Action := Action) (Reward := Rat) n))
            i (i + 1)
            (History.finitePairHistoryOfTrace
              (action omega) (reward omega) i))
        (MeasureTheory.ae
          (mu.trim
            ((History.historyFiltrationSucc action reward haction hreward).le
              i)))) :
    Filter.EventuallyEq (MeasureTheory.ae mu)
      (@MeasureTheory.condExp Omega Real
        ((History.historyFiltrationSucc action reward haction hreward) i)
        mOmega _ _ _ mu
        (fun omega : Omega =>
          (((reward omega (i + 1) -
            mean
              (context i
                (History.finiteRewardHistoryOfTrace (reward omega) i))
              ((policy i).action
                (state i
                  (History.finiteRewardHistoryOfTrace (reward omega) i))) :
              Rat) : Real))))
      (fun _omega : Omega => (0 : Real)) := by
  exact
    ConditionalExpectationReward.centeredReward_succ_condExp_eq_zero_of_generatedActionTraceSucc_actionRewardPartialTrajectoryKernel_extend_map_eq_historyFiltrationSucc_finitePairHistoryOfTrace_rawRangeMeasurableMeanRangeBounded
      (mOmega := mOmega)
      mu action rewardKernel policy context state hcontext hstate mean
      varianceProxy hmean hkernel defaultAction reward haction hreward
      rewardLo rewardHi meanLo meanHi hraw hmean_range i
      h_action_generated h_kernel_extend_map_eq

example {Omega Context State Action : Type}
    [mOmega : MeasurableSpace Omega] [StandardBorelSpace Omega]
    [MeasurableSpace Context] [MeasurableSpace State]
    [MeasurableSpace Action] [MeasurableSingletonClass Action]
    [Countable Action]
    (mu : MeasureTheory.Measure Omega)
    [MeasureTheory.IsFiniteMeasure mu]
    (rewardKernel :
      RewardKernel.MarkovRewardKernel (Prod Context Action) Rat)
    (policy : Nat -> Policy.MeasurablePolicy State Action)
    (context : (n : Nat) -> ((j : Finset.Iic n) -> Rat) -> Context)
    (state : (n : Nat) -> ((j : Finset.Iic n) -> Rat) -> State)
    (hcontext : forall n : Nat, Measurable (context n))
    (hstate : forall n : Nat, Measurable (state n))
    (defaultAction : Action)
    (action : Omega -> ActionTrace Action)
    (reward : Omega -> RewardTrace Rat)
    (haction : forall t : Nat,
      @Measurable Omega Action mOmega inferInstance
        (fun omega : Omega => action omega t))
    (hreward : forall t : Nat,
      @Measurable Omega Rat mOmega inferInstance
        (fun omega : Omega => reward omega t))
    (i : Nat)
    (h_action_generated :
      action =
        Policy.generatedActionTraceSucc policy
          (fun n omega =>
            state n (History.finiteRewardHistoryOfTrace (reward omega) n))
          defaultAction)
    (h_pair_map_eq_actual_action :
      Filter.Eventually
        (fun omega : Omega =>
          @MeasureTheory.Measure.map Omega (Prod Action Rat) mOmega
            inferInstance
            (fun y : Omega => (action omega (i + 1), reward y (i + 1)))
            (@ProbabilityTheory.condExpKernel Omega mOmega _ mu _
              ((History.historyFiltrationSucc action reward haction hreward) i)
              omega) =
          MeasureTheory.Measure.map
            (Prod.mk (action omega (i + 1)))
            (RewardKernel.selectedMeasure rewardKernel
              (context i
                (History.finiteRewardHistoryOfTrace (reward omega) i))
              (action omega (i + 1))))
        (MeasureTheory.ae
          (mu.trim
            ((History.historyFiltrationSucc action reward haction hreward).le
              i)))) :
    Filter.Eventually
      (fun omega : Omega =>
        @MeasureTheory.Measure.map Omega
          ((j : Finset.Iic (i + 1)) -> Prod Action Rat) mOmega
          inferInstance
          (fun y : Omega =>
            History.finitePairHistoryOfTrace
              (action y) (reward y) (i + 1))
          (@ProbabilityTheory.condExpKernel Omega mOmega _ mu _
            ((History.historyFiltrationSucc action reward haction hreward) i)
            omega) =
        RewardKernel.actionRewardPartialTrajectoryKernel rewardKernel policy
          (fun n history =>
            context n (History.pairHistoryRewardProjection history))
          (fun n history =>
            state n (History.pairHistoryRewardProjection history))
          (fun n : Nat =>
            (hcontext n).comp
              (History.measurable_pairHistoryRewardProjection
                (Action := Action) (Reward := Rat) n))
          (fun n : Nat =>
            (hstate n).comp
              (History.measurable_pairHistoryRewardProjection
                (Action := Action) (Reward := Rat) n))
          i (i + 1)
          (History.finitePairHistoryOfTrace
            (action omega) (reward omega) i))
      (MeasureTheory.ae
        (mu.trim
          ((History.historyFiltrationSucc action reward haction hreward).le
            i))) := by
  exact
    ConditionalExpectationReward.actionRewardPartialTrajectoryKernel_map_eq_historyFiltrationSucc_finitePairHistoryOfTrace_of_generatedActionTraceSucc_pair_map_eq_actual_action
      (mOmega := mOmega)
      mu action rewardKernel policy context state hcontext hstate defaultAction
      reward haction hreward i h_action_generated h_pair_map_eq_actual_action

example {Omega Context State Action : Type}
    [mOmega : MeasurableSpace Omega] [StandardBorelSpace Omega]
    [MeasurableSpace Context] [MeasurableSpace State]
    [MeasurableSpace Action] [MeasurableSingletonClass Action]
    [Countable Action]
    (mu : MeasureTheory.Measure Omega)
    [MeasureTheory.IsFiniteMeasure mu]
    (rewardKernel :
      RewardKernel.MarkovRewardKernel (Prod Context Action) Rat)
    (policy : Nat -> Policy.MeasurablePolicy State Action)
    (context : (n : Nat) -> ((j : Finset.Iic n) -> Rat) -> Context)
    (state : (n : Nat) -> ((j : Finset.Iic n) -> Rat) -> State)
    (hcontext : forall n : Nat, Measurable (context n))
    (hstate : forall n : Nat, Measurable (state n))
    (defaultAction : Action)
    (action : Omega -> ActionTrace Action)
    (reward : Omega -> RewardTrace Rat)
    (haction : forall t : Nat,
      @Measurable Omega Action mOmega inferInstance
        (fun omega : Omega => action omega t))
    (hreward : forall t : Nat,
      @Measurable Omega Rat mOmega inferInstance
        (fun omega : Omega => reward omega t))
    (i : Nat)
    (h_action_generated :
      action =
        Policy.generatedActionTraceSucc policy
          (fun n omega =>
            state n (History.finiteRewardHistoryOfTrace (reward omega) n))
          defaultAction)
    (h_random_pair_map_eq_actual_action :
      Filter.Eventually
        (fun omega : Omega =>
          @MeasureTheory.Measure.map Omega (Prod Action Rat) mOmega
            inferInstance
            (fun y : Omega => (action y (i + 1), reward y (i + 1)))
            (@ProbabilityTheory.condExpKernel Omega mOmega _ mu _
              ((History.historyFiltrationSucc action reward haction hreward) i)
              omega) =
          MeasureTheory.Measure.map
            (Prod.mk (action omega (i + 1)))
            (RewardKernel.selectedMeasure rewardKernel
              (context i
                (History.finiteRewardHistoryOfTrace (reward omega) i))
              (action omega (i + 1))))
        (MeasureTheory.ae
          (mu.trim
            ((History.historyFiltrationSucc action reward haction hreward).le
              i)))) :
    Filter.Eventually
      (fun omega : Omega =>
        @MeasureTheory.Measure.map Omega
          ((j : Finset.Iic (i + 1)) -> Prod Action Rat) mOmega
          inferInstance
          (fun y : Omega =>
            History.finitePairHistoryOfTrace
              (action y) (reward y) (i + 1))
          (@ProbabilityTheory.condExpKernel Omega mOmega _ mu _
            ((History.historyFiltrationSucc action reward haction hreward) i)
            omega) =
        RewardKernel.actionRewardPartialTrajectoryKernel rewardKernel policy
          (fun n history =>
            context n (History.pairHistoryRewardProjection history))
          (fun n history =>
            state n (History.pairHistoryRewardProjection history))
          (fun n : Nat =>
            (hcontext n).comp
              (History.measurable_pairHistoryRewardProjection
                (Action := Action) (Reward := Rat) n))
          (fun n : Nat =>
            (hstate n).comp
              (History.measurable_pairHistoryRewardProjection
                (Action := Action) (Reward := Rat) n))
          i (i + 1)
          (History.finitePairHistoryOfTrace
            (action omega) (reward omega) i))
      (MeasureTheory.ae
        (mu.trim
          ((History.historyFiltrationSucc action reward haction hreward).le
            i))) := by
  exact
    ConditionalExpectationReward.actionRewardPartialTrajectoryKernel_map_eq_historyFiltrationSucc_finitePairHistoryOfTrace_of_generatedActionTraceSucc_random_pair_map_eq_actual_action
      (mOmega := mOmega)
      mu action rewardKernel policy context state hcontext hstate defaultAction
      reward haction hreward i h_action_generated
      h_random_pair_map_eq_actual_action

example {Omega Context State Action : Type}
    [mOmega : MeasurableSpace Omega] [StandardBorelSpace Omega]
    [MeasurableSpace Context] [MeasurableSpace State]
    [MeasurableSpace Action] [MeasurableSingletonClass Action]
    [Countable Action]
    (mu : MeasureTheory.Measure Omega)
    [MeasureTheory.IsFiniteMeasure mu]
    (rewardKernel :
      RewardKernel.MarkovRewardKernel (Prod Context Action) Rat)
    (policy : Nat -> Policy.MeasurablePolicy State Action)
    (context : (n : Nat) -> ((j : Finset.Iic n) -> Rat) -> Context)
    (state : (n : Nat) -> ((j : Finset.Iic n) -> Rat) -> State)
    (hcontext : forall n : Nat, Measurable (context n))
    (hstate : forall n : Nat, Measurable (state n))
    (mean : Context -> Action -> Rat)
    (varianceProxy : Context -> Action -> NNReal)
    (law :
      RewardKernel.CenteredRewardKernelLaw rewardKernel mean varianceProxy)
    (defaultAction : Action)
    (action : Omega -> ActionTrace Action)
    (reward : Omega -> RewardTrace Rat)
    (haction : forall t : Nat,
      @Measurable Omega Action mOmega inferInstance
        (fun omega : Omega => action omega t))
    (hreward : forall t : Nat,
      @Measurable Omega Rat mOmega inferInstance
        (fun omega : Omega => reward omega t))
    (i : Nat)
    (h_action_generated :
      action =
        Policy.generatedActionTraceSucc policy
          (fun n omega =>
            state n (History.finiteRewardHistoryOfTrace (reward omega) n))
          defaultAction)
    (h_integrable :
      MeasureTheory.Integrable
        (fun omega : Omega =>
          (((reward omega (i + 1) -
            mean
              (context i
                (History.finiteRewardHistoryOfTrace (reward omega) i))
              ((policy i).action
                (state i
                  (History.finiteRewardHistoryOfTrace (reward omega) i))) :
                Rat) : Real))) mu)
    (h_pair_map_eq_actual_action :
      Filter.Eventually
        (fun omega : Omega =>
          @MeasureTheory.Measure.map Omega (Prod Action Rat) mOmega
            inferInstance
            (fun y : Omega => (action omega (i + 1), reward y (i + 1)))
            (@ProbabilityTheory.condExpKernel Omega mOmega _ mu _
              ((History.historyFiltrationSucc action reward haction hreward) i)
              omega) =
          MeasureTheory.Measure.map
            (Prod.mk (action omega (i + 1)))
            (RewardKernel.selectedMeasure rewardKernel
              (context i
                (History.finiteRewardHistoryOfTrace (reward omega) i))
              (action omega (i + 1))))
        (MeasureTheory.ae
          (mu.trim
            ((History.historyFiltrationSucc action reward haction hreward).le
              i)))) :
    Filter.EventuallyEq (MeasureTheory.ae mu)
      (@MeasureTheory.condExp Omega Real
        ((History.historyFiltrationSucc action reward haction hreward) i)
        mOmega _ _ _ mu
        (fun omega : Omega =>
          (((reward omega (i + 1) -
            mean
              (context i
                (History.finiteRewardHistoryOfTrace (reward omega) i))
              ((policy i).action
                (state i
                  (History.finiteRewardHistoryOfTrace (reward omega) i))) :
                Rat) : Real))))
      (fun _omega : Omega => (0 : Real)) := by
  exact
    ConditionalExpectationReward.centeredReward_succ_condExp_eq_zero_of_generatedActionTraceSucc_pair_map_eq_actual_action
      (mOmega := mOmega)
      mu action rewardKernel policy context state hcontext hstate mean
      varianceProxy law defaultAction reward haction hreward i
      h_action_generated h_integrable h_pair_map_eq_actual_action

example {Omega Context State Action : Type}
    [mOmega : MeasurableSpace Omega] [StandardBorelSpace Omega]
    [MeasurableSpace Context] [MeasurableSpace State]
    [MeasurableSpace Action] [MeasurableSingletonClass Action]
    [Countable Action]
    (mu : MeasureTheory.Measure Omega)
    [MeasureTheory.IsFiniteMeasure mu]
    (action : Omega -> ActionTrace Action)
    (rewardKernel :
      RewardKernel.MarkovRewardKernel (Prod Context Action) Rat)
    (policy : Nat -> Policy.MeasurablePolicy State Action)
    (context : (n : Nat) -> ((j : Finset.Iic n) -> Rat) -> Context)
    (state : (n : Nat) -> ((j : Finset.Iic n) -> Rat) -> State)
    (hcontext : forall n : Nat, Measurable (context n))
    (hstate : forall n : Nat, Measurable (state n))
    (mean : Context -> Action -> Rat)
    (varianceProxy : Context -> Action -> NNReal)
    (hmean :
      Measurable (fun pair : Prod Context Action => mean pair.1 pair.2))
    (law :
      RewardKernel.CenteredRewardKernelLaw rewardKernel mean varianceProxy)
    (defaultAction : Action)
    (reward : Omega -> RewardTrace Rat)
    (haction : forall t : Nat,
      @Measurable Omega Action mOmega inferInstance
        (fun omega : Omega => action omega t))
    (hreward : forall t : Nat,
      @Measurable Omega Rat mOmega inferInstance
        (fun omega : Omega => reward omega t))
    (rewardLo rewardHi meanLo meanHi : Nat -> Real)
    (hraw :
      forall i : Nat, forall omega : Omega,
        Set.Icc (rewardLo i) (rewardHi i)
          (((reward omega (i + 1) : Rat) : Real)))
    (hmean_range :
      forall i : Nat, forall context : Context, forall action : Action,
        Set.Icc (meanLo i) (meanHi i)
          (((mean context action : Rat) : Real)))
    (i : Nat)
    (h_action_generated :
      action =
        Policy.generatedActionTraceSucc policy
          (fun n omega =>
            state n (History.finiteRewardHistoryOfTrace (reward omega) n))
          defaultAction)
    (h_pair_map_eq_actual_action :
      Filter.Eventually
        (fun omega : Omega =>
          @MeasureTheory.Measure.map Omega (Prod Action Rat) mOmega
            inferInstance
            (fun y : Omega => (action omega (i + 1), reward y (i + 1)))
            (@ProbabilityTheory.condExpKernel Omega mOmega _ mu _
              ((History.historyFiltrationSucc action reward haction hreward) i)
              omega) =
          MeasureTheory.Measure.map
            (Prod.mk (action omega (i + 1)))
            (RewardKernel.selectedMeasure rewardKernel
              (context i
                (History.finiteRewardHistoryOfTrace (reward omega) i))
              (action omega (i + 1))))
        (MeasureTheory.ae
          (mu.trim
            ((History.historyFiltrationSucc action reward haction hreward).le
              i)))) :
    Filter.EventuallyEq (MeasureTheory.ae mu)
      (@MeasureTheory.condExp Omega Real
        ((History.historyFiltrationSucc action reward haction hreward) i)
        mOmega _ _ _ mu
        (fun omega : Omega =>
          (((reward omega (i + 1) -
            mean
              (context i
                (History.finiteRewardHistoryOfTrace (reward omega) i))
              ((policy i).action
                (state i
                  (History.finiteRewardHistoryOfTrace (reward omega) i))) :
                Rat) : Real))))
      (fun _omega : Omega => (0 : Real)) := by
  exact
    ConditionalExpectationReward.centeredReward_succ_condExp_eq_zero_of_generatedActionTraceSucc_pair_map_eq_actual_action_rawRangeMeasurableMeanRangeBounded
      (mOmega := mOmega)
      mu action rewardKernel policy context state hcontext hstate mean
      varianceProxy hmean law defaultAction reward haction hreward
      rewardLo rewardHi meanLo meanHi hraw hmean_range i
      h_action_generated h_pair_map_eq_actual_action

example {Omega Context State Action : Type}
    [mOmega : MeasurableSpace Omega] [StandardBorelSpace Omega]
    [MeasurableSpace Context] [MeasurableSpace State]
    [MeasurableSpace Action] [MeasurableSingletonClass Action]
    [Countable Action]
    (mu : MeasureTheory.Measure Omega)
    [MeasureTheory.IsFiniteMeasure mu]
    (rewardKernel :
      RewardKernel.MarkovRewardKernel (Prod Context Action) Rat)
    (policy : Nat -> Policy.MeasurablePolicy State Action)
    (context : (n : Nat) -> ((j : Finset.Iic n) -> Rat) -> Context)
    (state : (n : Nat) -> ((j : Finset.Iic n) -> Rat) -> State)
    (hcontext : forall n : Nat, Measurable (context n))
    (hstate : forall n : Nat, Measurable (state n))
    (mean : Context -> Action -> Rat)
    (varianceProxy : Context -> Action -> NNReal)
    (law :
      RewardKernel.CenteredRewardKernelLaw rewardKernel mean varianceProxy)
    (defaultAction : Action)
    (action : Omega -> ActionTrace Action)
    (reward : Omega -> RewardTrace Rat)
    (haction : forall t : Nat,
      @Measurable Omega Action mOmega inferInstance
        (fun omega : Omega => action omega t))
    (hreward : forall t : Nat,
      @Measurable Omega Rat mOmega inferInstance
        (fun omega : Omega => reward omega t))
    (i : Nat)
    (h_action_generated :
      action =
        Policy.generatedActionTraceSucc policy
          (fun n omega =>
            state n (History.finiteRewardHistoryOfTrace (reward omega) n))
          defaultAction)
    (h_integrable :
      MeasureTheory.Integrable
        (fun omega : Omega =>
          (((reward omega (i + 1) -
            mean
              (context i
                (History.finiteRewardHistoryOfTrace (reward omega) i))
              ((policy i).action
                (state i
                  (History.finiteRewardHistoryOfTrace (reward omega) i))) :
                Rat) : Real))) mu)
    (h_random_pair_map_eq_actual_action :
      Filter.Eventually
        (fun omega : Omega =>
          @MeasureTheory.Measure.map Omega (Prod Action Rat) mOmega
            inferInstance
            (fun y : Omega => (action y (i + 1), reward y (i + 1)))
            (@ProbabilityTheory.condExpKernel Omega mOmega _ mu _
              ((History.historyFiltrationSucc action reward haction hreward) i)
              omega) =
          MeasureTheory.Measure.map
            (Prod.mk (action omega (i + 1)))
            (RewardKernel.selectedMeasure rewardKernel
              (context i
                (History.finiteRewardHistoryOfTrace (reward omega) i))
              (action omega (i + 1))))
        (MeasureTheory.ae
          (mu.trim
            ((History.historyFiltrationSucc action reward haction hreward).le
              i)))) :
    Filter.EventuallyEq (MeasureTheory.ae mu)
      (@MeasureTheory.condExp Omega Real
        ((History.historyFiltrationSucc action reward haction hreward) i)
        mOmega _ _ _ mu
        (fun omega : Omega =>
          (((reward omega (i + 1) -
            mean
              (context i
                (History.finiteRewardHistoryOfTrace (reward omega) i))
              ((policy i).action
                (state i
                  (History.finiteRewardHistoryOfTrace (reward omega) i))) :
                Rat) : Real))))
      (fun _omega : Omega => (0 : Real)) := by
  exact
    ConditionalExpectationReward.centeredReward_succ_condExp_eq_zero_of_generatedActionTraceSucc_random_pair_map_eq_actual_action
      (mOmega := mOmega)
      mu action rewardKernel policy context state hcontext hstate mean
      varianceProxy law defaultAction reward haction hreward i
      h_action_generated h_integrable h_random_pair_map_eq_actual_action

example {Omega Context State Action : Type}
    [mOmega : MeasurableSpace Omega] [StandardBorelSpace Omega]
    [MeasurableSpace Context] [MeasurableSpace State]
    [MeasurableSpace Action] [MeasurableSingletonClass Action]
    [Countable Action]
    (mu : MeasureTheory.Measure Omega)
    [MeasureTheory.IsFiniteMeasure mu]
    (action : Omega -> ActionTrace Action)
    (rewardKernel :
      RewardKernel.MarkovRewardKernel (Prod Context Action) Rat)
    (policy : Nat -> Policy.MeasurablePolicy State Action)
    (context : (n : Nat) -> ((j : Finset.Iic n) -> Rat) -> Context)
    (state : (n : Nat) -> ((j : Finset.Iic n) -> Rat) -> State)
    (hcontext : forall n : Nat, Measurable (context n))
    (hstate : forall n : Nat, Measurable (state n))
    (mean : Context -> Action -> Rat)
    (varianceProxy : Context -> Action -> NNReal)
    (hmean :
      Measurable (fun pair : Prod Context Action => mean pair.1 pair.2))
    (law :
      RewardKernel.CenteredRewardKernelLaw rewardKernel mean varianceProxy)
    (defaultAction : Action)
    (reward : Omega -> RewardTrace Rat)
    (haction : forall t : Nat,
      @Measurable Omega Action mOmega inferInstance
        (fun omega : Omega => action omega t))
    (hreward : forall t : Nat,
      @Measurable Omega Rat mOmega inferInstance
        (fun omega : Omega => reward omega t))
    (rewardLo rewardHi meanLo meanHi : Nat -> Real)
    (hraw :
      forall i : Nat, forall omega : Omega,
        Set.Icc (rewardLo i) (rewardHi i)
          (((reward omega (i + 1) : Rat) : Real)))
    (hmean_range :
      forall i : Nat, forall context : Context, forall action : Action,
        Set.Icc (meanLo i) (meanHi i)
          (((mean context action : Rat) : Real)))
    (i : Nat)
    (h_action_generated :
      action =
        Policy.generatedActionTraceSucc policy
          (fun n omega =>
            state n (History.finiteRewardHistoryOfTrace (reward omega) n))
          defaultAction)
    (h_random_pair_map_eq_actual_action :
      Filter.Eventually
        (fun omega : Omega =>
          @MeasureTheory.Measure.map Omega (Prod Action Rat) mOmega
            inferInstance
            (fun y : Omega => (action y (i + 1), reward y (i + 1)))
            (@ProbabilityTheory.condExpKernel Omega mOmega _ mu _
              ((History.historyFiltrationSucc action reward haction hreward) i)
              omega) =
          MeasureTheory.Measure.map
            (Prod.mk (action omega (i + 1)))
            (RewardKernel.selectedMeasure rewardKernel
              (context i
                (History.finiteRewardHistoryOfTrace (reward omega) i))
              (action omega (i + 1))))
        (MeasureTheory.ae
          (mu.trim
            ((History.historyFiltrationSucc action reward haction hreward).le
              i)))) :
    Filter.EventuallyEq (MeasureTheory.ae mu)
      (@MeasureTheory.condExp Omega Real
        ((History.historyFiltrationSucc action reward haction hreward) i)
        mOmega _ _ _ mu
        (fun omega : Omega =>
          (((reward omega (i + 1) -
            mean
              (context i
                (History.finiteRewardHistoryOfTrace (reward omega) i))
              ((policy i).action
                (state i
                  (History.finiteRewardHistoryOfTrace (reward omega) i))) :
                Rat) : Real))))
      (fun _omega : Omega => (0 : Real)) := by
  exact
    ConditionalExpectationReward.centeredReward_succ_condExp_eq_zero_of_generatedActionTraceSucc_random_pair_map_eq_actual_action_rawRangeMeasurableMeanRangeBounded
      (mOmega := mOmega)
      mu action rewardKernel policy context state hcontext hstate mean
      varianceProxy hmean law defaultAction reward haction hreward
      rewardLo rewardHi meanLo meanHi hraw hmean_range i
      h_action_generated h_random_pair_map_eq_actual_action

example {Omega Context State Action : Type}
    [mOmega : MeasurableSpace Omega] [StandardBorelSpace Omega]
    [MeasurableSpace Context] [MeasurableSpace State]
    [MeasurableSpace Action] [MeasurableSingletonClass Action]
    [Countable Action]
    (mu : MeasureTheory.Measure Omega) [MeasureTheory.IsFiniteMeasure mu]
    (action : Omega -> ActionTrace Action)
    (rewardKernel : RewardKernel.MarkovRewardKernel (Prod Context Action) Rat)
    (policy : Nat -> Policy.MeasurablePolicy State Action)
    (context : (n : Nat) -> ((j : Finset.Iic n) -> Rat) -> Context)
    (state : (n : Nat) -> ((j : Finset.Iic n) -> Rat) -> State)
    (hcontext : forall n : Nat, Measurable (context n))
    (hstate : forall n : Nat, Measurable (state n))
    (defaultAction : Action)
    (reward : Omega -> RewardTrace Rat)
    (haction : forall t : Nat,
      Measurable (fun omega : Omega => action omega t))
    (hreward : forall t : Nat,
      Measurable (fun omega : Omega => reward omega t))
    (source :
      ConditionalExpectationReward.GeneratedActionActualRewardMapSource
        mu action rewardKernel policy context state defaultAction reward
        haction hreward)
    (i : Nat) :
    Filter.Eventually
      (fun omega : Omega =>
        @MeasureTheory.Measure.map Omega (Prod Action Rat) mOmega inferInstance
          (fun y : Omega => (action y (i + 1), reward y (i + 1)))
          (@ProbabilityTheory.condExpKernel Omega mOmega _ mu _
            ((History.historyFiltrationSucc action reward haction hreward) i)
            omega) =
        RewardKernel.actionRewardHistoryStepKernelFamily rewardKernel policy
          (fun n history =>
            context n (History.pairHistoryRewardProjection history))
          (fun n history =>
            state n (History.pairHistoryRewardProjection history))
          (fun n : Nat =>
            (hcontext n).comp
              (History.measurable_pairHistoryRewardProjection
                (Action := Action) (Reward := Rat) n))
          (fun n : Nat =>
            (hstate n).comp
              (History.measurable_pairHistoryRewardProjection
                (Action := Action) (Reward := Rat) n))
          i
          (History.finitePairHistoryOfTrace
            (action omega) (reward omega) i))
      (MeasureTheory.ae
        (mu.trim
          ((History.historyFiltrationSucc action reward haction hreward).le
            i))) := by
  exact
    ConditionalExpectationReward.actionRewardHistoryStepKernelFamily_pair_map_eq_historyFiltrationSucc_finitePairHistoryOfTrace_of_generatedActionActualRewardMapSource
      (mOmega := mOmega)
      mu action rewardKernel policy context state hcontext hstate defaultAction
      reward haction hreward source i

example {Omega Context State Action : Type}
    [mOmega : MeasurableSpace Omega] [StandardBorelSpace Omega]
    [MeasurableSpace Context] [MeasurableSpace State]
    [MeasurableSpace Action] [MeasurableSingletonClass Action]
    [Countable Action]
    (mu : MeasureTheory.Measure Omega) [MeasureTheory.IsFiniteMeasure mu]
    (action : Omega -> ActionTrace Action)
    (rewardKernel : RewardKernel.MarkovRewardKernel (Prod Context Action) Rat)
    (policy : Nat -> Policy.MeasurablePolicy State Action)
    (context : (n : Nat) -> ((j : Finset.Iic n) -> Rat) -> Context)
    (state : (n : Nat) -> ((j : Finset.Iic n) -> Rat) -> State)
    (hcontext : forall n : Nat, Measurable (context n))
    (hstate : forall n : Nat, Measurable (state n))
    (defaultAction : Action)
    (reward : Omega -> RewardTrace Rat)
    (haction : forall t : Nat,
      Measurable (fun omega : Omega => action omega t))
    (hreward : forall t : Nat,
      Measurable (fun omega : Omega => reward omega t))
    (source :
      ConditionalExpectationReward.GeneratedActionActualRewardMapSource
        mu action rewardKernel policy context state defaultAction reward
        haction hreward)
    (i : Nat) :
    Filter.Eventually
      (fun omega : Omega =>
        @MeasureTheory.Measure.map Omega ((j : Finset.Iic (i + 1)) -> Prod Action Rat)
          mOmega inferInstance
          (fun y : Omega =>
            History.finitePairHistoryOfTrace (action y) (reward y) (i + 1))
          (@ProbabilityTheory.condExpKernel Omega mOmega _ mu _
            ((History.historyFiltrationSucc action reward haction hreward) i)
            omega) =
        RewardKernel.actionRewardPartialTrajectoryKernel rewardKernel policy
          (fun n history =>
            context n (History.pairHistoryRewardProjection history))
          (fun n history =>
            state n (History.pairHistoryRewardProjection history))
          (fun n : Nat =>
            (hcontext n).comp
              (History.measurable_pairHistoryRewardProjection
                (Action := Action) (Reward := Rat) n))
          (fun n : Nat =>
            (hstate n).comp
              (History.measurable_pairHistoryRewardProjection
                (Action := Action) (Reward := Rat) n))
          i (i + 1)
          (History.finitePairHistoryOfTrace
            (action omega) (reward omega) i))
      (MeasureTheory.ae
        (mu.trim
          ((History.historyFiltrationSucc action reward haction hreward).le
            i))) := by
  exact
    ConditionalExpectationReward.actionRewardPartialTrajectoryKernel_map_eq_historyFiltrationSucc_finitePairHistoryOfTrace_of_generatedActionActualRewardMapSource
      (mOmega := mOmega)
      mu action rewardKernel policy context state hcontext hstate defaultAction
      reward haction hreward source i

example {Omega Context State Action : Type}
    [mOmega : MeasurableSpace Omega] [StandardBorelSpace Omega]
    [MeasurableSpace Context] [MeasurableSpace State]
    [MeasurableSpace Action] [MeasurableSingletonClass Action]
    [Countable Action]
    (mu : MeasureTheory.Measure Omega) [MeasureTheory.IsFiniteMeasure mu]
    (action : Omega -> ActionTrace Action)
    (rewardKernel : RewardKernel.MarkovRewardKernel (Prod Context Action) Rat)
    (policy : Nat -> Policy.MeasurablePolicy State Action)
    (context : (n : Nat) -> ((j : Finset.Iic n) -> Rat) -> Context)
    (state : (n : Nat) -> ((j : Finset.Iic n) -> Rat) -> State)
    (hcontext : forall n : Nat, Measurable (context n))
    (hstate : forall n : Nat, Measurable (state n))
    (mean : Context -> Action -> Rat)
    (varianceProxy : Context -> Action -> NNReal)
    (law :
      RewardKernel.CenteredRewardKernelLaw rewardKernel mean varianceProxy)
    (defaultAction : Action)
    (reward : Omega -> RewardTrace Rat)
    (haction : forall t : Nat,
      Measurable (fun omega : Omega => action omega t))
    (hreward : forall t : Nat,
      Measurable (fun omega : Omega => reward omega t))
    (source :
      ConditionalExpectationReward.GeneratedActionActualRewardMapSource
        mu action rewardKernel policy context state defaultAction reward
        haction hreward)
    (i : Nat)
    (h_integrable :
      MeasureTheory.Integrable
        (fun omega : Omega =>
          (((reward omega (i + 1) -
            mean
              (context i
                (History.finiteRewardHistoryOfTrace (reward omega) i))
              ((policy i).action
                (state i
                  (History.finiteRewardHistoryOfTrace (reward omega) i))) :
                Rat) : Real))) mu) :
    Filter.EventuallyEq (MeasureTheory.ae mu)
      (@MeasureTheory.condExp Omega Real
        ((History.historyFiltrationSucc action reward haction hreward) i)
        mOmega _ _ _ mu
        (fun omega : Omega =>
          (((reward omega (i + 1) -
            mean
              (context i
                (History.finiteRewardHistoryOfTrace (reward omega) i))
              ((policy i).action
                (state i
                  (History.finiteRewardHistoryOfTrace (reward omega) i))) :
                Rat) : Real))))
      (fun _omega : Omega => (0 : Real)) := by
  exact
    ConditionalExpectationReward.centeredReward_succ_condExp_eq_zero_of_generatedActionActualRewardMapSource
      (mOmega := mOmega)
      mu action rewardKernel policy context state hcontext hstate mean
      varianceProxy law defaultAction reward haction hreward source i
      h_integrable

example {Omega Context State Action : Type}
    [mOmega : MeasurableSpace Omega] [StandardBorelSpace Omega]
    [MeasurableSpace Context] [MeasurableSpace State]
    [MeasurableSpace Action] [MeasurableSingletonClass Action]
    [Countable Action]
    (mu : MeasureTheory.Measure Omega) [MeasureTheory.IsFiniteMeasure mu]
    (action : Omega -> ActionTrace Action)
    (rewardKernel : RewardKernel.MarkovRewardKernel (Prod Context Action) Rat)
    (policy : Nat -> Policy.MeasurablePolicy State Action)
    (context : (n : Nat) -> ((j : Finset.Iic n) -> Rat) -> Context)
    (state : (n : Nat) -> ((j : Finset.Iic n) -> Rat) -> State)
    (hcontext : forall n : Nat, Measurable (context n))
    (hstate : forall n : Nat, Measurable (state n))
    (mean : Context -> Action -> Rat)
    (varianceProxy : Context -> Action -> NNReal)
    (hmean :
      Measurable (fun pair : Prod Context Action => mean pair.1 pair.2))
    (hkernel :
      RewardKernel.CenteredRewardKernelLaw rewardKernel mean varianceProxy)
    (defaultAction : Action)
    (reward : Omega -> RewardTrace Rat)
    (haction : forall t : Nat,
      Measurable (fun omega : Omega => action omega t))
    (hreward : forall t : Nat,
      Measurable (fun omega : Omega => reward omega t))
    (rewardLo rewardHi meanLo meanHi : Nat -> Real)
    (hraw :
      forall i : Nat, forall omega : Omega,
        Set.Icc (rewardLo i) (rewardHi i)
          (((reward omega (i + 1) : Rat) : Real)))
    (hmean_range :
      forall i : Nat, forall context : Context, forall action : Action,
        Set.Icc (meanLo i) (meanHi i)
          (((mean context action : Rat) : Real)))
    (source :
      ConditionalExpectationReward.GeneratedActionActualRewardMapSource
        mu action rewardKernel policy context state defaultAction reward
        haction hreward)
    (i : Nat) :
    Filter.EventuallyEq (MeasureTheory.ae mu)
      (@MeasureTheory.condExp Omega Real
        ((History.historyFiltrationSucc action reward haction hreward) i)
        mOmega _ _ _ mu
        (fun omega : Omega =>
          (((reward omega (i + 1) -
            mean
              (context i
                (History.finiteRewardHistoryOfTrace (reward omega) i))
              ((policy i).action
                (state i
                  (History.finiteRewardHistoryOfTrace (reward omega) i))) :
              Rat) : Real))))
      (fun _omega : Omega => (0 : Real)) := by
  exact
    ConditionalExpectationReward.centeredReward_succ_condExp_eq_zero_of_generatedActionActualRewardMapSource_rawRangeMeasurableMeanRangeBounded
      (mOmega := mOmega)
      mu action rewardKernel policy context state hcontext hstate mean
      varianceProxy hmean hkernel defaultAction reward haction hreward
      rewardLo rewardHi meanLo meanHi hraw hmean_range source i

example {Omega Context State Action : Type}
    [mOmega : MeasurableSpace Omega] [StandardBorelSpace Omega]
    [MeasurableSpace Context] [MeasurableSpace State]
    [MeasurableSpace Action] [MeasurableSingletonClass Action]
    [Countable Action]
    (mu : MeasureTheory.Measure Omega) [MeasureTheory.IsFiniteMeasure mu]
    (rewardKernel : RewardKernel.MarkovRewardKernel (Prod Context Action) Rat)
    (policy : Nat -> Policy.MeasurablePolicy State Action)
    (context : (n : Nat) -> ((j : Finset.Iic n) -> Rat) -> Context)
    (state : (n : Nat) -> ((j : Finset.Iic n) -> Rat) -> State)
    (defaultAction : Action)
    (reward : Omega -> RewardTrace Rat)
    (hreward : forall t : Nat,
      Measurable (fun omega : Omega => reward omega t))
    (source :
      ConditionalExpectationReward.GeneratedActionDefinitionalActualRewardMapSource
        mu rewardKernel policy context state defaultAction reward hreward) :
    ConditionalExpectationReward.GeneratedActionActualRewardMapSource mu
      (ConditionalExpectationReward.generatedActionFromRewardHistory
        policy state defaultAction reward)
      rewardKernel policy context state defaultAction reward
      (ConditionalExpectationReward.generatedActionFromRewardHistory_measurable
        (policy := policy) (state := state) (defaultAction := defaultAction)
        (reward := reward) hreward source.hstate)
      hreward := by
  exact
    ConditionalExpectationReward.generatedActionActualRewardMapSource_of_definitionalActualRewardMapSource
      (mOmega := mOmega)
      mu rewardKernel policy context state defaultAction reward hreward source

example {Omega Context State Action : Type}
    [mOmega : MeasurableSpace Omega] [StandardBorelSpace Omega]
    [MeasurableSpace Context] [MeasurableSpace State]
    [MeasurableSpace Action] [MeasurableSingletonClass Action]
    [Countable Action]
    (mu : MeasureTheory.Measure Omega) [MeasureTheory.IsFiniteMeasure mu]
    (action : Omega -> ActionTrace Action)
    (rewardKernel : RewardKernel.MarkovRewardKernel (Prod Context Action) Rat)
    (policy : Nat -> Policy.MeasurablePolicy State Action)
    (context : (n : Nat) -> ((j : Finset.Iic n) -> Rat) -> Context)
    (state : (n : Nat) -> ((j : Finset.Iic n) -> Rat) -> State)
    (hcontext : forall n : Nat, Measurable (context n))
    (hstate : forall n : Nat, Measurable (state n))
    (defaultAction : Action)
    (reward : Omega -> RewardTrace Rat)
    (haction : forall t : Nat,
      Measurable (fun omega : Omega => action omega t))
    (hreward : forall t : Nat,
      Measurable (fun omega : Omega => reward omega t))
    (h_action_generated :
      action =
        Policy.generatedActionTraceSucc policy
          (fun n omega =>
            state n (History.finiteRewardHistoryOfTrace (reward omega) n))
          defaultAction)
    (h_partialtraj_map_eq :
      forall i : Nat,
        Filter.Eventually
          (fun omega : Omega =>
            @MeasureTheory.Measure.map Omega
              ((j : Finset.Iic (i + 1)) -> Prod Action Rat)
              mOmega inferInstance
              (fun y : Omega =>
                History.finitePairHistoryOfTrace
                  (action y) (reward y) (i + 1))
              (@ProbabilityTheory.condExpKernel Omega mOmega _ mu _
                ((History.historyFiltrationSucc action reward haction hreward) i)
                omega) =
            RewardKernel.actionRewardPartialTrajectoryKernel rewardKernel policy
              (fun n history =>
                context n (History.pairHistoryRewardProjection history))
              (fun n history =>
                state n (History.pairHistoryRewardProjection history))
              (fun n : Nat =>
                (hcontext n).comp
                  (History.measurable_pairHistoryRewardProjection
                    (Action := Action) (Reward := Rat) n))
              (fun n : Nat =>
                (hstate n).comp
                  (History.measurable_pairHistoryRewardProjection
                    (Action := Action) (Reward := Rat) n))
              i (i + 1)
              (History.finitePairHistoryOfTrace
                (action omega) (reward omega) i))
          (MeasureTheory.ae
            (mu.trim
              ((History.historyFiltrationSucc action reward haction hreward).le
                i)))) :
    ConditionalExpectationReward.GeneratedActionActualRewardMapSource mu action
      rewardKernel policy context state defaultAction reward haction hreward := by
  exact
    ConditionalExpectationReward.generatedActionActualRewardMapSource_of_partialTrajectoryKernel_map_eq
      (mOmega := mOmega)
      mu action rewardKernel policy context state hcontext hstate defaultAction
      reward haction hreward h_action_generated h_partialtraj_map_eq

example {Omega Context State Action : Type}
    [mOmega : MeasurableSpace Omega] [StandardBorelSpace Omega]
    [MeasurableSpace Context] [MeasurableSpace State]
    [MeasurableSpace Action] [MeasurableSingletonClass Action]
    [Countable Action]
    (mu : MeasureTheory.Measure Omega) [MeasureTheory.IsFiniteMeasure mu]
    (action : Omega -> ActionTrace Action)
    (rewardKernel : RewardKernel.MarkovRewardKernel (Prod Context Action) Rat)
    (policy : Nat -> Policy.MeasurablePolicy State Action)
    (context : (n : Nat) -> ((j : Finset.Iic n) -> Rat) -> Context)
    (state : (n : Nat) -> ((j : Finset.Iic n) -> Rat) -> State)
    (hcontext : forall n : Nat, Measurable (context n))
    (hstate : forall n : Nat, Measurable (state n))
    (defaultAction : Action)
    (reward : Omega -> RewardTrace Rat)
    (haction : forall t : Nat,
      Measurable (fun omega : Omega => action omega t))
    (hreward : forall t : Nat,
      Measurable (fun omega : Omega => reward omega t))
    (h_action_generated :
      action =
        Policy.generatedActionTraceSucc policy
          (fun n omega =>
            state n (History.finiteRewardHistoryOfTrace (reward omega) n))
          defaultAction)
    (h_extend_map_eq :
      forall i : Nat,
        Filter.Eventually
          (fun omega : Omega =>
            @MeasureTheory.Measure.map Omega
              ((j : Finset.Iic (i + 1)) -> Prod Action Rat)
              mOmega inferInstance
              (fun y : Omega =>
                History.extendPairHistorySucc
                  (History.finitePairHistoryOfTrace
                    (action omega) (reward omega) i)
                  (action y (i + 1), reward y (i + 1)))
              (@ProbabilityTheory.condExpKernel Omega mOmega _ mu _
                ((History.historyFiltrationSucc action reward haction hreward) i)
                omega) =
            RewardKernel.actionRewardPartialTrajectoryKernel rewardKernel policy
              (fun n history =>
                context n (History.pairHistoryRewardProjection history))
              (fun n history =>
                state n (History.pairHistoryRewardProjection history))
              (fun n : Nat =>
                (hcontext n).comp
                  (History.measurable_pairHistoryRewardProjection
                    (Action := Action) (Reward := Rat) n))
              (fun n : Nat =>
                (hstate n).comp
                  (History.measurable_pairHistoryRewardProjection
                    (Action := Action) (Reward := Rat) n))
              i (i + 1)
              (History.finitePairHistoryOfTrace
                (action omega) (reward omega) i))
          (MeasureTheory.ae
            (mu.trim
              ((History.historyFiltrationSucc action reward haction hreward).le
                i)))) :
    ConditionalExpectationReward.GeneratedActionActualRewardMapSource mu action
      rewardKernel policy context state defaultAction reward haction hreward := by
  exact
    ConditionalExpectationReward.generatedActionActualRewardMapSource_of_partialTrajectoryKernel_extend_map_eq
      (mOmega := mOmega)
      mu action rewardKernel policy context state hcontext hstate defaultAction
      reward haction hreward h_action_generated h_extend_map_eq

example {Omega Context State Action : Type}
    [mOmega : MeasurableSpace Omega] [StandardBorelSpace Omega]
    [MeasurableSpace Context] [MeasurableSpace State]
    [MeasurableSpace Action] [MeasurableSingletonClass Action]
    [Countable Action]
    (mu : MeasureTheory.Measure Omega) [MeasureTheory.IsFiniteMeasure mu]
    (action : Omega -> ActionTrace Action)
    (rewardKernel : RewardKernel.MarkovRewardKernel (Prod Context Action) Rat)
    (policy : Nat -> Policy.MeasurablePolicy State Action)
    (context : (n : Nat) -> ((j : Finset.Iic n) -> Rat) -> Context)
    (state : (n : Nat) -> ((j : Finset.Iic n) -> Rat) -> State)
    (hcontext : forall n : Nat, Measurable (context n))
    (hstate : forall n : Nat, Measurable (state n))
    (defaultAction : Action)
    (reward : Omega -> RewardTrace Rat)
    (haction : forall t : Nat,
      Measurable (fun omega : Omega => action omega t))
    (hreward : forall t : Nat,
      Measurable (fun omega : Omega => reward omega t))
    (h_action_generated :
      action =
        Policy.generatedActionTraceSucc policy
          (fun n omega =>
            state n (History.finiteRewardHistoryOfTrace (reward omega) n))
          defaultAction)
    (h_pair_map_eq :
      forall i : Nat,
        Filter.Eventually
          (fun omega : Omega =>
            @MeasureTheory.Measure.map Omega (Prod Action Rat) mOmega
              inferInstance
              (fun y : Omega => (action y (i + 1), reward y (i + 1)))
              (@ProbabilityTheory.condExpKernel Omega mOmega _ mu _
                ((History.historyFiltrationSucc action reward haction hreward) i)
                omega) =
            RewardKernel.actionRewardHistoryStepKernelFamily rewardKernel policy
              (fun n history =>
                context n (History.pairHistoryRewardProjection history))
              (fun n history =>
                state n (History.pairHistoryRewardProjection history))
              (fun n : Nat =>
                (hcontext n).comp
                  (History.measurable_pairHistoryRewardProjection
                    (Action := Action) (Reward := Rat) n))
              (fun n : Nat =>
                (hstate n).comp
                  (History.measurable_pairHistoryRewardProjection
                    (Action := Action) (Reward := Rat) n))
              i
              (History.finitePairHistoryOfTrace
                (action omega) (reward omega) i))
          (MeasureTheory.ae
            (mu.trim
              ((History.historyFiltrationSucc action reward haction hreward).le
                i)))) :
    ConditionalExpectationReward.GeneratedActionActualRewardMapSource mu action
      rewardKernel policy context state defaultAction reward haction hreward := by
  exact
    ConditionalExpectationReward.generatedActionActualRewardMapSource_of_actionRewardHistoryStepKernelFamily_pair_map_eq
      (mOmega := mOmega)
      mu action rewardKernel policy context state hcontext hstate defaultAction
      reward haction hreward h_action_generated h_pair_map_eq

example {Omega Context State Action : Type}
    [mOmega : MeasurableSpace Omega] [StandardBorelSpace Omega]
    [MeasurableSpace Context] [MeasurableSpace State]
    [MeasurableSpace Action] [MeasurableSingletonClass Action]
    [Countable Action]
    (mu : MeasureTheory.Measure Omega) [MeasureTheory.IsFiniteMeasure mu]
    (rewardKernel : RewardKernel.MarkovRewardKernel (Prod Context Action) Rat)
    (policy : Nat -> Policy.MeasurablePolicy State Action)
    (context : (n : Nat) -> ((j : Finset.Iic n) -> Rat) -> Context)
    (state : (n : Nat) -> ((j : Finset.Iic n) -> Rat) -> State)
    (hstate : forall n : Nat, Measurable (state n))
    (defaultAction : Action)
    (reward : Omega -> RewardTrace Rat)
    (hreward : forall t : Nat,
      Measurable (fun omega : Omega => reward omega t))
    (h_reward_map_eq_policy :
      forall i : Nat,
        Filter.Eventually
          (fun omega : Omega =>
            @MeasureTheory.Measure.map Omega Rat mOmega inferInstance
              (fun y : Omega => reward y (i + 1))
              (@ProbabilityTheory.condExpKernel Omega mOmega _ mu _
                ((History.historyFiltrationSucc
                  (ConditionalExpectationReward.generatedActionFromRewardHistory
                    policy state defaultAction reward)
                  reward
                  (ConditionalExpectationReward.generatedActionFromRewardHistory_measurable
                    (policy := policy) (state := state)
                    (defaultAction := defaultAction) (reward := reward)
                    hreward hstate)
                  hreward) i)
                omega) =
            RewardKernel.selectedMeasure rewardKernel
              (context i
                (History.finiteRewardHistoryOfTrace (reward omega) i))
              ((policy i).action
                (state i
                  (History.finiteRewardHistoryOfTrace (reward omega) i))))
          (MeasureTheory.ae
            (mu.trim
              ((History.historyFiltrationSucc
                (ConditionalExpectationReward.generatedActionFromRewardHistory
                  policy state defaultAction reward)
                reward
                (ConditionalExpectationReward.generatedActionFromRewardHistory_measurable
                  (policy := policy) (state := state)
                  (defaultAction := defaultAction) (reward := reward)
                  hreward hstate)
                hreward).le i)))) :
    ConditionalExpectationReward.GeneratedActionDefinitionalActualRewardMapSource
      mu rewardKernel policy context state defaultAction reward hreward := by
  exact
    ConditionalExpectationReward.generatedActionDefinitionalActualRewardMapSource_of_reward_map_eq_selected_policy
      (mOmega := mOmega)
      mu rewardKernel policy context state hstate defaultAction reward hreward
      h_reward_map_eq_policy

example {Omega Context State Action : Type}
    [mOmega : MeasurableSpace Omega] [StandardBorelSpace Omega]
    [MeasurableSpace Context] [MeasurableSpace State]
    [MeasurableSpace Action] [MeasurableSingletonClass Action]
    [Countable Action]
    (mu : MeasureTheory.Measure Omega) [MeasureTheory.IsFiniteMeasure mu]
    (rewardKernel : RewardKernel.MarkovRewardKernel (Prod Context Action) Rat)
    (policy : Nat -> Policy.MeasurablePolicy State Action)
    (context : (n : Nat) -> ((j : Finset.Iic n) -> Rat) -> Context)
    (state : (n : Nat) -> ((j : Finset.Iic n) -> Rat) -> State)
    (hcontext : forall n : Nat, Measurable (context n))
    (hstate : forall n : Nat, Measurable (state n))
    (defaultAction : Action)
    (reward : Omega -> RewardTrace Rat)
    (hreward : forall t : Nat,
      Measurable (fun omega : Omega => reward omega t))
    (h_partialtraj_map_eq :
      forall i : Nat,
        Filter.Eventually
          (fun omega : Omega =>
            @MeasureTheory.Measure.map Omega
              ((j : Finset.Iic (i + 1)) -> Prod Action Rat)
              mOmega inferInstance
              (fun y : Omega =>
                History.finitePairHistoryOfTrace
                  (ConditionalExpectationReward.generatedActionFromRewardHistory
                    policy state defaultAction reward y)
                  (reward y) (i + 1))
              (@ProbabilityTheory.condExpKernel Omega mOmega _ mu _
                ((History.historyFiltrationSucc
                  (ConditionalExpectationReward.generatedActionFromRewardHistory
                    policy state defaultAction reward)
                  reward
                  (ConditionalExpectationReward.generatedActionFromRewardHistory_measurable
                    (policy := policy) (state := state)
                    (defaultAction := defaultAction) (reward := reward)
                    hreward hstate)
                  hreward) i)
                omega) =
            RewardKernel.actionRewardPartialTrajectoryKernel rewardKernel
              policy
              (fun n history =>
                context n (History.pairHistoryRewardProjection history))
              (fun n history =>
                state n (History.pairHistoryRewardProjection history))
              (fun n : Nat =>
                (hcontext n).comp
                  (History.measurable_pairHistoryRewardProjection
                    (Action := Action) (Reward := Rat) n))
              (fun n : Nat =>
                (hstate n).comp
                  (History.measurable_pairHistoryRewardProjection
                    (Action := Action) (Reward := Rat) n))
              i (i + 1)
              (History.finitePairHistoryOfTrace
                (ConditionalExpectationReward.generatedActionFromRewardHistory
                  policy state defaultAction reward omega)
                (reward omega) i))
          (MeasureTheory.ae
            (mu.trim
              ((History.historyFiltrationSucc
                (ConditionalExpectationReward.generatedActionFromRewardHistory
                  policy state defaultAction reward)
                reward
                (ConditionalExpectationReward.generatedActionFromRewardHistory_measurable
                  (policy := policy) (state := state)
                  (defaultAction := defaultAction) (reward := reward)
                  hreward hstate)
                hreward).le i)))) :
    ConditionalExpectationReward.GeneratedActionDefinitionalActualRewardMapSource
      mu rewardKernel policy context state defaultAction reward hreward := by
  exact
    ConditionalExpectationReward.generatedActionDefinitionalActualRewardMapSource_of_partialTrajectoryKernel_map_eq
      (mOmega := mOmega)
      mu rewardKernel policy context state hcontext hstate defaultAction reward
      hreward h_partialtraj_map_eq

example {Omega Context State Action : Type}
    [mOmega : MeasurableSpace Omega] [StandardBorelSpace Omega]
    [MeasurableSpace Context] [MeasurableSpace State]
    [MeasurableSpace Action] [MeasurableSingletonClass Action]
    [Countable Action]
    (mu : MeasureTheory.Measure Omega) [MeasureTheory.IsFiniteMeasure mu]
    (rewardKernel : RewardKernel.MarkovRewardKernel (Prod Context Action) Rat)
    (policy : Nat -> Policy.MeasurablePolicy State Action)
    (context : (n : Nat) -> ((j : Finset.Iic n) -> Rat) -> Context)
    (state : (n : Nat) -> ((j : Finset.Iic n) -> Rat) -> State)
    (hcontext : forall n : Nat, Measurable (context n))
    (hstate : forall n : Nat, Measurable (state n))
    (defaultAction : Action)
    (reward : Omega -> RewardTrace Rat)
    (hreward : forall t : Nat,
      Measurable (fun omega : Omega => reward omega t))
    (h_extend_map_eq :
      forall i : Nat,
        Filter.Eventually
          (fun omega : Omega =>
            @MeasureTheory.Measure.map Omega
              ((j : Finset.Iic (i + 1)) -> Prod Action Rat)
              mOmega inferInstance
              (fun y : Omega =>
                History.extendPairHistorySucc
                  (History.finitePairHistoryOfTrace
                    (ConditionalExpectationReward.generatedActionFromRewardHistory
                      policy state defaultAction reward omega)
                    (reward omega) i)
                  (ConditionalExpectationReward.generatedActionFromRewardHistory
                    policy state defaultAction reward y (i + 1),
                    reward y (i + 1)))
              (@ProbabilityTheory.condExpKernel Omega mOmega _ mu _
                ((History.historyFiltrationSucc
                  (ConditionalExpectationReward.generatedActionFromRewardHistory
                    policy state defaultAction reward)
                  reward
                  (ConditionalExpectationReward.generatedActionFromRewardHistory_measurable
                    (policy := policy) (state := state)
                    (defaultAction := defaultAction) (reward := reward)
                    hreward hstate)
                  hreward) i)
                omega) =
            RewardKernel.actionRewardPartialTrajectoryKernel rewardKernel
              policy
              (fun n history =>
                context n (History.pairHistoryRewardProjection history))
              (fun n history =>
                state n (History.pairHistoryRewardProjection history))
              (fun n : Nat =>
                (hcontext n).comp
                  (History.measurable_pairHistoryRewardProjection
                    (Action := Action) (Reward := Rat) n))
              (fun n : Nat =>
                (hstate n).comp
                  (History.measurable_pairHistoryRewardProjection
                    (Action := Action) (Reward := Rat) n))
              i (i + 1)
              (History.finitePairHistoryOfTrace
                (ConditionalExpectationReward.generatedActionFromRewardHistory
                  policy state defaultAction reward omega)
                (reward omega) i))
          (MeasureTheory.ae
            (mu.trim
              ((History.historyFiltrationSucc
                (ConditionalExpectationReward.generatedActionFromRewardHistory
                  policy state defaultAction reward)
                reward
                (ConditionalExpectationReward.generatedActionFromRewardHistory_measurable
                  (policy := policy) (state := state)
                  (defaultAction := defaultAction) (reward := reward)
                  hreward hstate)
                hreward).le i)))) :
    ConditionalExpectationReward.GeneratedActionDefinitionalActualRewardMapSource
      mu rewardKernel policy context state defaultAction reward hreward := by
  exact
    ConditionalExpectationReward.generatedActionDefinitionalActualRewardMapSource_of_partialTrajectoryKernel_extend_map_eq
      (mOmega := mOmega)
      mu rewardKernel policy context state hcontext hstate defaultAction reward
      hreward h_extend_map_eq

example {Omega Context State Action : Type}
    [mOmega : MeasurableSpace Omega] [StandardBorelSpace Omega]
    [MeasurableSpace Context] [MeasurableSpace State]
    [MeasurableSpace Action] [MeasurableSingletonClass Action]
    [Countable Action]
    (mu : MeasureTheory.Measure Omega) [MeasureTheory.IsFiniteMeasure mu]
    (rewardKernel : RewardKernel.MarkovRewardKernel (Prod Context Action) Rat)
    (policy : Nat -> Policy.MeasurablePolicy State Action)
    (context : (n : Nat) -> ((j : Finset.Iic n) -> Rat) -> Context)
    (state : (n : Nat) -> ((j : Finset.Iic n) -> Rat) -> State)
    (hcontext : forall n : Nat, Measurable (context n))
    (hstate : forall n : Nat, Measurable (state n))
    (defaultAction : Action)
    (reward : Omega -> RewardTrace Rat)
    (hreward : forall t : Nat,
      Measurable (fun omega : Omega => reward omega t))
    (h_pair_map_eq :
      forall i : Nat,
        Filter.Eventually
          (fun omega : Omega =>
            @MeasureTheory.Measure.map Omega (Prod Action Rat) mOmega
              inferInstance
              (fun y : Omega =>
                (ConditionalExpectationReward.generatedActionFromRewardHistory
                  policy state defaultAction reward y (i + 1),
                  reward y (i + 1)))
              (@ProbabilityTheory.condExpKernel Omega mOmega _ mu _
                ((History.historyFiltrationSucc
                  (ConditionalExpectationReward.generatedActionFromRewardHistory
                    policy state defaultAction reward)
                  reward
                  (ConditionalExpectationReward.generatedActionFromRewardHistory_measurable
                    (policy := policy) (state := state)
                    (defaultAction := defaultAction) (reward := reward)
                    hreward hstate)
                  hreward) i)
                omega) =
            RewardKernel.actionRewardHistoryStepKernelFamily rewardKernel
              policy
              (fun n history =>
                context n (History.pairHistoryRewardProjection history))
              (fun n history =>
                state n (History.pairHistoryRewardProjection history))
              (fun n : Nat =>
                (hcontext n).comp
                  (History.measurable_pairHistoryRewardProjection
                    (Action := Action) (Reward := Rat) n))
              (fun n : Nat =>
                (hstate n).comp
                  (History.measurable_pairHistoryRewardProjection
                    (Action := Action) (Reward := Rat) n))
              i
              (History.finitePairHistoryOfTrace
                (ConditionalExpectationReward.generatedActionFromRewardHistory
                  policy state defaultAction reward omega)
                (reward omega) i))
          (MeasureTheory.ae
            (mu.trim
              ((History.historyFiltrationSucc
                (ConditionalExpectationReward.generatedActionFromRewardHistory
                  policy state defaultAction reward)
                reward
                (ConditionalExpectationReward.generatedActionFromRewardHistory_measurable
                  (policy := policy) (state := state)
                  (defaultAction := defaultAction) (reward := reward)
                  hreward hstate)
                hreward).le i)))) :
    ConditionalExpectationReward.GeneratedActionDefinitionalActualRewardMapSource
      mu rewardKernel policy context state defaultAction reward hreward := by
  exact
    ConditionalExpectationReward.generatedActionDefinitionalActualRewardMapSource_of_actionRewardHistoryStepKernelFamily_pair_map_eq
      (mOmega := mOmega)
      mu rewardKernel policy context state hcontext hstate defaultAction reward
      hreward h_pair_map_eq

example {Omega Context State Action : Type}
    [mOmega : MeasurableSpace Omega] [StandardBorelSpace Omega]
    [MeasurableSpace Context] [MeasurableSpace State]
    [MeasurableSpace Action] [MeasurableSingletonClass Action]
    [Countable Action]
    (mu : MeasureTheory.Measure Omega) [MeasureTheory.IsFiniteMeasure mu]
    (rewardKernel : RewardKernel.MarkovRewardKernel (Prod Context Action) Rat)
    (policy : Nat -> Policy.MeasurablePolicy State Action)
    (context : (n : Nat) -> ((j : Finset.Iic n) -> Rat) -> Context)
    (state : (n : Nat) -> ((j : Finset.Iic n) -> Rat) -> State)
    (hcontext : forall n : Nat, Measurable (context n))
    (defaultAction : Action)
    (reward : Omega -> RewardTrace Rat)
    (hreward : forall t : Nat,
      Measurable (fun omega : Omega => reward omega t))
    (source :
      ConditionalExpectationReward.GeneratedActionDefinitionalActualRewardMapSource
        mu rewardKernel policy context state defaultAction reward hreward)
    (i : Nat) :
    Filter.Eventually
      (fun omega : Omega =>
        @MeasureTheory.Measure.map Omega (Prod Action Rat) mOmega inferInstance
          (fun y : Omega =>
            (ConditionalExpectationReward.generatedActionFromRewardHistory
              policy state defaultAction reward y (i + 1),
              reward y (i + 1)))
          (@ProbabilityTheory.condExpKernel Omega mOmega _ mu _
            ((History.historyFiltrationSucc
              (ConditionalExpectationReward.generatedActionFromRewardHistory
                policy state defaultAction reward)
              reward
              (ConditionalExpectationReward.generatedActionFromRewardHistory_measurable
                (policy := policy) (state := state)
                (defaultAction := defaultAction) (reward := reward)
                hreward source.hstate)
              hreward) i)
            omega) =
        RewardKernel.actionRewardHistoryStepKernelFamily rewardKernel policy
          (fun n history =>
            context n (History.pairHistoryRewardProjection history))
          (fun n history =>
            state n (History.pairHistoryRewardProjection history))
          (fun n : Nat =>
            (hcontext n).comp
              (History.measurable_pairHistoryRewardProjection
                (Action := Action) (Reward := Rat) n))
          (fun n : Nat =>
            (source.hstate n).comp
              (History.measurable_pairHistoryRewardProjection
                (Action := Action) (Reward := Rat) n))
          i
          (History.finitePairHistoryOfTrace
            (ConditionalExpectationReward.generatedActionFromRewardHistory
              policy state defaultAction reward omega)
            (reward omega) i))
      (MeasureTheory.ae
        (mu.trim
          ((History.historyFiltrationSucc
            (ConditionalExpectationReward.generatedActionFromRewardHistory
              policy state defaultAction reward)
            reward
            (ConditionalExpectationReward.generatedActionFromRewardHistory_measurable
              (policy := policy) (state := state)
              (defaultAction := defaultAction) (reward := reward)
              hreward source.hstate)
            hreward).le i))) := by
  exact
    ConditionalExpectationReward.actionRewardHistoryStepKernelFamily_pair_map_eq_historyFiltrationSucc_finitePairHistoryOfTrace_of_generatedActionDefinitionalActualRewardMapSource
      (mOmega := mOmega)
      mu rewardKernel policy context state hcontext defaultAction reward
      hreward source i

example {Omega Context State Action : Type}
    [mOmega : MeasurableSpace Omega] [StandardBorelSpace Omega]
    [MeasurableSpace Context] [MeasurableSpace State]
    [MeasurableSpace Action] [MeasurableSingletonClass Action]
    [Countable Action]
    (mu : MeasureTheory.Measure Omega) [MeasureTheory.IsFiniteMeasure mu]
    (rewardKernel : RewardKernel.MarkovRewardKernel (Prod Context Action) Rat)
    (policy : Nat -> Policy.MeasurablePolicy State Action)
    (context : (n : Nat) -> ((j : Finset.Iic n) -> Rat) -> Context)
    (state : (n : Nat) -> ((j : Finset.Iic n) -> Rat) -> State)
    (hcontext : forall n : Nat, Measurable (context n))
    (defaultAction : Action)
    (reward : Omega -> RewardTrace Rat)
    (hreward : forall t : Nat,
      Measurable (fun omega : Omega => reward omega t))
    (source :
      ConditionalExpectationReward.GeneratedActionDefinitionalActualRewardMapSource
        mu rewardKernel policy context state defaultAction reward hreward)
    (i : Nat) :
    Filter.Eventually
      (fun omega : Omega =>
        @MeasureTheory.Measure.map Omega ((j : Finset.Iic (i + 1)) -> Prod Action Rat)
          mOmega inferInstance
          (fun y : Omega =>
            History.finitePairHistoryOfTrace
              (ConditionalExpectationReward.generatedActionFromRewardHistory
                policy state defaultAction reward y)
              (reward y) (i + 1))
          (@ProbabilityTheory.condExpKernel Omega mOmega _ mu _
            ((History.historyFiltrationSucc
              (ConditionalExpectationReward.generatedActionFromRewardHistory
                policy state defaultAction reward)
              reward
              (ConditionalExpectationReward.generatedActionFromRewardHistory_measurable
                (policy := policy) (state := state)
                (defaultAction := defaultAction) (reward := reward)
                hreward source.hstate)
              hreward) i)
            omega) =
        RewardKernel.actionRewardPartialTrajectoryKernel rewardKernel policy
          (fun n history =>
            context n (History.pairHistoryRewardProjection history))
          (fun n history =>
            state n (History.pairHistoryRewardProjection history))
          (fun n : Nat =>
            (hcontext n).comp
              (History.measurable_pairHistoryRewardProjection
                (Action := Action) (Reward := Rat) n))
          (fun n : Nat =>
            (source.hstate n).comp
              (History.measurable_pairHistoryRewardProjection
                (Action := Action) (Reward := Rat) n))
          i (i + 1)
          (History.finitePairHistoryOfTrace
            (ConditionalExpectationReward.generatedActionFromRewardHistory
              policy state defaultAction reward omega)
            (reward omega) i))
      (MeasureTheory.ae
        (mu.trim
          ((History.historyFiltrationSucc
            (ConditionalExpectationReward.generatedActionFromRewardHistory
              policy state defaultAction reward)
            reward
            (ConditionalExpectationReward.generatedActionFromRewardHistory_measurable
              (policy := policy) (state := state)
              (defaultAction := defaultAction) (reward := reward)
              hreward source.hstate)
            hreward).le i))) := by
  exact
    ConditionalExpectationReward.actionRewardPartialTrajectoryKernel_map_eq_historyFiltrationSucc_finitePairHistoryOfTrace_of_generatedActionDefinitionalActualRewardMapSource
      (mOmega := mOmega)
      mu rewardKernel policy context state hcontext defaultAction reward
      hreward source i

example {Omega Context State Action : Type}
    [mOmega : MeasurableSpace Omega] [StandardBorelSpace Omega]
    [MeasurableSpace Context] [MeasurableSpace State]
    [MeasurableSpace Action] [MeasurableSingletonClass Action]
    [Countable Action]
    (mu : MeasureTheory.Measure Omega) [MeasureTheory.IsFiniteMeasure mu]
    (rewardKernel : RewardKernel.MarkovRewardKernel (Prod Context Action) Rat)
    (policy : Nat -> Policy.MeasurablePolicy State Action)
    (context : (n : Nat) -> ((j : Finset.Iic n) -> Rat) -> Context)
    (state : (n : Nat) -> ((j : Finset.Iic n) -> Rat) -> State)
    (hcontext : forall n : Nat, Measurable (context n))
    (mean : Context -> Action -> Rat)
    (varianceProxy : Context -> Action -> NNReal)
    (law :
      RewardKernel.CenteredRewardKernelLaw rewardKernel mean varianceProxy)
    (defaultAction : Action)
    (reward : Omega -> RewardTrace Rat)
    (hreward : forall t : Nat,
      Measurable (fun omega : Omega => reward omega t))
    (source :
      ConditionalExpectationReward.GeneratedActionDefinitionalActualRewardMapSource
        mu rewardKernel policy context state defaultAction reward hreward)
    (i : Nat)
    (h_integrable :
      MeasureTheory.Integrable
        (fun omega : Omega =>
          (((reward omega (i + 1) -
            mean
              (context i
                (History.finiteRewardHistoryOfTrace (reward omega) i))
              ((policy i).action
                (state i
                  (History.finiteRewardHistoryOfTrace (reward omega) i))) :
                Rat) : Real))) mu) :
    Filter.EventuallyEq (MeasureTheory.ae mu)
      (@MeasureTheory.condExp Omega Real
        ((History.historyFiltrationSucc
          (ConditionalExpectationReward.generatedActionFromRewardHistory
            policy state defaultAction reward)
          reward
          (ConditionalExpectationReward.generatedActionFromRewardHistory_measurable
            (policy := policy) (state := state)
            (defaultAction := defaultAction) (reward := reward)
            hreward source.hstate)
          hreward) i)
        mOmega _ _ _ mu
        (fun omega : Omega =>
          (((reward omega (i + 1) -
            mean
              (context i
                (History.finiteRewardHistoryOfTrace (reward omega) i))
              ((policy i).action
                (state i
                  (History.finiteRewardHistoryOfTrace (reward omega) i))) :
                Rat) : Real))))
      (fun _omega : Omega => (0 : Real)) := by
  exact
    ConditionalExpectationReward.centeredReward_succ_condExp_eq_zero_of_generatedActionDefinitionalActualRewardMapSource
      (mOmega := mOmega)
      mu rewardKernel policy context state hcontext mean varianceProxy law
      defaultAction reward hreward source i h_integrable

example {Omega Context State Action : Type}
    [mOmega : MeasurableSpace Omega] [StandardBorelSpace Omega]
    [MeasurableSpace Context] [MeasurableSpace State]
    [MeasurableSpace Action] [MeasurableSingletonClass Action]
    [Countable Action]
    (mu : MeasureTheory.Measure Omega) [MeasureTheory.IsFiniteMeasure mu]
    (action : Omega -> ActionTrace Action)
    (rewardKernel : RewardKernel.MarkovRewardKernel (Prod Context Action) Rat)
    (policy : Nat -> Policy.MeasurablePolicy State Action)
    (context : (n : Nat) -> ((j : Finset.Iic n) -> Rat) -> Context)
    (state : (n : Nat) -> ((j : Finset.Iic n) -> Rat) -> State)
    (hstate : forall n : Nat, Measurable (state n))
    (defaultAction : Action)
    (reward : Omega -> RewardTrace Rat)
    (haction : forall t : Nat,
      Measurable (fun omega : Omega => action omega t))
    (hreward : forall t : Nat,
      Measurable (fun omega : Omega => reward omega t))
    (source :
      ConditionalExpectationReward.GeneratedActionRandomPairMapSource
        mu action rewardKernel policy context state defaultAction reward
        haction hreward)
    :
    ConditionalExpectationReward.GeneratedActionActualRewardMapSource
      mu action rewardKernel policy context state defaultAction reward
      haction hreward := by
  exact
    ConditionalExpectationReward.generatedActionActualRewardMapSource_of_randomPairMapSource
      (mOmega := mOmega)
      mu action rewardKernel policy context state hstate defaultAction reward
      haction hreward source

example {Omega Context State Action : Type}
    [mOmega : MeasurableSpace Omega] [StandardBorelSpace Omega]
    [MeasurableSpace Context] [MeasurableSpace State]
    [MeasurableSpace Action] [MeasurableSingletonClass Action]
    [Countable Action]
    (mu : MeasureTheory.Measure Omega) [MeasureTheory.IsFiniteMeasure mu]
    (action : Omega -> ActionTrace Action)
    (rewardKernel : RewardKernel.MarkovRewardKernel (Prod Context Action) Rat)
    (policy : Nat -> Policy.MeasurablePolicy State Action)
    (context : (n : Nat) -> ((j : Finset.Iic n) -> Rat) -> Context)
    (state : (n : Nat) -> ((j : Finset.Iic n) -> Rat) -> State)
    (hcontext : forall n : Nat, Measurable (context n))
    (hstate : forall n : Nat, Measurable (state n))
    (defaultAction : Action)
    (reward : Omega -> RewardTrace Rat)
    (haction : forall t : Nat,
      Measurable (fun omega : Omega => action omega t))
    (hreward : forall t : Nat,
      Measurable (fun omega : Omega => reward omega t))
    (h_action_generated :
      action =
        Policy.generatedActionTraceSucc policy
          (fun n omega =>
            state n (History.finiteRewardHistoryOfTrace (reward omega) n))
          defaultAction)
    (h_pair_map_eq :
      forall i : Nat,
        Filter.Eventually
          (fun omega : Omega =>
            @MeasureTheory.Measure.map Omega (Prod Action Rat) mOmega
              inferInstance
              (fun y : Omega => (action y (i + 1), reward y (i + 1)))
              (@ProbabilityTheory.condExpKernel Omega mOmega _ mu _
                ((History.historyFiltrationSucc action reward haction hreward) i)
                omega) =
            RewardKernel.actionRewardHistoryStepKernelFamily rewardKernel policy
              (fun n history =>
                context n (History.pairHistoryRewardProjection history))
              (fun n history =>
                state n (History.pairHistoryRewardProjection history))
              (fun n : Nat =>
                (hcontext n).comp
                  (History.measurable_pairHistoryRewardProjection
                    (Action := Action) (Reward := Rat) n))
              (fun n : Nat =>
                (hstate n).comp
                  (History.measurable_pairHistoryRewardProjection
                    (Action := Action) (Reward := Rat) n))
              i
              (History.finitePairHistoryOfTrace
                (action omega) (reward omega) i))
          (MeasureTheory.ae
            (mu.trim
              ((History.historyFiltrationSucc action reward haction hreward).le
                i)))) :
    ConditionalExpectationReward.GeneratedActionRandomPairMapSource mu action
      rewardKernel policy context state defaultAction reward haction hreward := by
  exact
    ConditionalExpectationReward.generatedActionRandomPairMapSource_of_actionRewardHistoryStepKernelFamily_pair_map_eq
      (mOmega := mOmega)
      mu action rewardKernel policy context state hcontext hstate defaultAction
      reward haction hreward h_action_generated h_pair_map_eq

example {Omega Context State Action : Type}
    [mOmega : MeasurableSpace Omega] [StandardBorelSpace Omega]
    [MeasurableSpace Context] [MeasurableSpace State]
    [MeasurableSpace Action] [MeasurableSingletonClass Action]
    [Countable Action]
    (mu : MeasureTheory.Measure Omega) [MeasureTheory.IsFiniteMeasure mu]
    (action : Omega -> ActionTrace Action)
    (rewardKernel : RewardKernel.MarkovRewardKernel (Prod Context Action) Rat)
    (policy : Nat -> Policy.MeasurablePolicy State Action)
    (context : (n : Nat) -> ((j : Finset.Iic n) -> Rat) -> Context)
    (state : (n : Nat) -> ((j : Finset.Iic n) -> Rat) -> State)
    (hcontext : forall n : Nat, Measurable (context n))
    (hstate : forall n : Nat, Measurable (state n))
    (defaultAction : Action)
    (reward : Omega -> RewardTrace Rat)
    (haction : forall t : Nat,
      Measurable (fun omega : Omega => action omega t))
    (hreward : forall t : Nat,
      Measurable (fun omega : Omega => reward omega t))
    (h_action_generated :
      action =
        Policy.generatedActionTraceSucc policy
          (fun n omega =>
            state n (History.finiteRewardHistoryOfTrace (reward omega) n))
          defaultAction)
    (h_partialtraj_map_eq :
      forall i : Nat,
        Filter.Eventually
          (fun omega : Omega =>
            @MeasureTheory.Measure.map Omega
              ((j : Finset.Iic (i + 1)) -> Prod Action Rat)
              mOmega inferInstance
              (fun y : Omega =>
                History.finitePairHistoryOfTrace
                  (action y) (reward y) (i + 1))
              (@ProbabilityTheory.condExpKernel Omega mOmega _ mu _
                ((History.historyFiltrationSucc action reward haction hreward) i)
                omega) =
            RewardKernel.actionRewardPartialTrajectoryKernel rewardKernel policy
              (fun n history =>
                context n (History.pairHistoryRewardProjection history))
              (fun n history =>
                state n (History.pairHistoryRewardProjection history))
              (fun n : Nat =>
                (hcontext n).comp
                  (History.measurable_pairHistoryRewardProjection
                    (Action := Action) (Reward := Rat) n))
              (fun n : Nat =>
                (hstate n).comp
                  (History.measurable_pairHistoryRewardProjection
                    (Action := Action) (Reward := Rat) n))
              i (i + 1)
              (History.finitePairHistoryOfTrace
                (action omega) (reward omega) i))
          (MeasureTheory.ae
            (mu.trim
              ((History.historyFiltrationSucc action reward haction hreward).le
                i)))) :
    ConditionalExpectationReward.GeneratedActionRandomPairMapSource mu action
      rewardKernel policy context state defaultAction reward haction hreward := by
  exact
    ConditionalExpectationReward.generatedActionRandomPairMapSource_of_actionRewardPartialTrajectoryKernel_map_eq
      (mOmega := mOmega)
      mu action rewardKernel policy context state hcontext hstate defaultAction
      reward haction hreward h_action_generated h_partialtraj_map_eq

example {Omega Context State Action : Type}
    [mOmega : MeasurableSpace Omega] [StandardBorelSpace Omega]
    [MeasurableSpace Context] [MeasurableSpace State]
    [MeasurableSpace Action] [MeasurableSingletonClass Action]
    [Countable Action]
    (mu : MeasureTheory.Measure Omega) [MeasureTheory.IsFiniteMeasure mu]
    (action : Omega -> ActionTrace Action)
    (rewardKernel : RewardKernel.MarkovRewardKernel (Prod Context Action) Rat)
    (policy : Nat -> Policy.MeasurablePolicy State Action)
    (context : (n : Nat) -> ((j : Finset.Iic n) -> Rat) -> Context)
    (state : (n : Nat) -> ((j : Finset.Iic n) -> Rat) -> State)
    (hcontext : forall n : Nat, Measurable (context n))
    (hstate : forall n : Nat, Measurable (state n))
    (defaultAction : Action)
    (reward : Omega -> RewardTrace Rat)
    (haction : forall t : Nat,
      Measurable (fun omega : Omega => action omega t))
    (hreward : forall t : Nat,
      Measurable (fun omega : Omega => reward omega t))
    (h_action_generated :
      action =
        Policy.generatedActionTraceSucc policy
          (fun n omega =>
            state n (History.finiteRewardHistoryOfTrace (reward omega) n))
          defaultAction)
    (h_extend_map_eq :
      forall i : Nat,
        Filter.Eventually
          (fun omega : Omega =>
            @MeasureTheory.Measure.map Omega
              ((j : Finset.Iic (i + 1)) -> Prod Action Rat)
              mOmega inferInstance
              (fun y : Omega =>
                History.extendPairHistorySucc
                  (History.finitePairHistoryOfTrace
                    (action omega) (reward omega) i)
                  (action y (i + 1), reward y (i + 1)))
              (@ProbabilityTheory.condExpKernel Omega mOmega _ mu _
                ((History.historyFiltrationSucc action reward haction hreward) i)
                omega) =
            RewardKernel.actionRewardPartialTrajectoryKernel rewardKernel policy
              (fun n history =>
                context n (History.pairHistoryRewardProjection history))
              (fun n history =>
                state n (History.pairHistoryRewardProjection history))
              (fun n : Nat =>
                (hcontext n).comp
                  (History.measurable_pairHistoryRewardProjection
                    (Action := Action) (Reward := Rat) n))
              (fun n : Nat =>
                (hstate n).comp
                  (History.measurable_pairHistoryRewardProjection
                    (Action := Action) (Reward := Rat) n))
              i (i + 1)
              (History.finitePairHistoryOfTrace
                (action omega) (reward omega) i))
          (MeasureTheory.ae
            (mu.trim
              ((History.historyFiltrationSucc action reward haction hreward).le
                i)))) :
    ConditionalExpectationReward.GeneratedActionRandomPairMapSource mu action
      rewardKernel policy context state defaultAction reward haction hreward := by
  exact
    ConditionalExpectationReward.generatedActionRandomPairMapSource_of_actionRewardPartialTrajectoryKernel_extend_map_eq
      (mOmega := mOmega)
      mu action rewardKernel policy context state hcontext hstate defaultAction
      reward haction hreward h_action_generated h_extend_map_eq

example {Omega Context State Action : Type}
    [mOmega : MeasurableSpace Omega] [StandardBorelSpace Omega]
    [MeasurableSpace Context] [MeasurableSpace State]
    [MeasurableSpace Action] [MeasurableSingletonClass Action]
    [Countable Action]
    (mu : MeasureTheory.Measure Omega) [MeasureTheory.IsFiniteMeasure mu]
    (action : Omega -> ActionTrace Action)
    (rewardKernel : RewardKernel.MarkovRewardKernel (Prod Context Action) Rat)
    (policy : Nat -> Policy.MeasurablePolicy State Action)
    (context : (n : Nat) -> ((j : Finset.Iic n) -> Rat) -> Context)
    (state : (n : Nat) -> ((j : Finset.Iic n) -> Rat) -> State)
    (hcontext : forall n : Nat, Measurable (context n))
    (hstate : forall n : Nat, Measurable (state n))
    (defaultAction : Action)
    (reward : Omega -> RewardTrace Rat)
    (haction : forall t : Nat,
      Measurable (fun omega : Omega => action omega t))
    (hreward : forall t : Nat,
      Measurable (fun omega : Omega => reward omega t))
    (source :
      ConditionalExpectationReward.GeneratedActionRandomPairMapSource
        mu action rewardKernel policy context state defaultAction reward
        haction hreward)
    (i : Nat) :
    Filter.Eventually
      (fun omega : Omega =>
        @MeasureTheory.Measure.map Omega (Prod Action Rat) mOmega inferInstance
          (fun y : Omega => (action y (i + 1), reward y (i + 1)))
          (@ProbabilityTheory.condExpKernel Omega mOmega _ mu _
            ((History.historyFiltrationSucc action reward haction hreward) i)
            omega) =
        RewardKernel.actionRewardHistoryStepKernelFamily rewardKernel policy
          (fun n history =>
            context n (History.pairHistoryRewardProjection history))
          (fun n history =>
            state n (History.pairHistoryRewardProjection history))
          (fun n : Nat =>
            (hcontext n).comp
              (History.measurable_pairHistoryRewardProjection
                (Action := Action) (Reward := Rat) n))
          (fun n : Nat =>
            (hstate n).comp
              (History.measurable_pairHistoryRewardProjection
                (Action := Action) (Reward := Rat) n))
          i
          (History.finitePairHistoryOfTrace
            (action omega) (reward omega) i))
      (MeasureTheory.ae
        (mu.trim
          ((History.historyFiltrationSucc action reward haction hreward).le
            i))) := by
  exact
    ConditionalExpectationReward.actionRewardHistoryStepKernelFamily_pair_map_eq_historyFiltrationSucc_finitePairHistoryOfTrace_of_generatedActionRandomPairMapSource
      (mOmega := mOmega)
      mu action rewardKernel policy context state hcontext hstate defaultAction
      reward haction hreward source i

example {Omega Context State Action : Type}
    [mOmega : MeasurableSpace Omega] [StandardBorelSpace Omega]
    [MeasurableSpace Context] [MeasurableSpace State]
    [MeasurableSpace Action] [MeasurableSingletonClass Action]
    [Countable Action]
    (mu : MeasureTheory.Measure Omega) [MeasureTheory.IsFiniteMeasure mu]
    (action : Omega -> ActionTrace Action)
    (rewardKernel : RewardKernel.MarkovRewardKernel (Prod Context Action) Rat)
    (policy : Nat -> Policy.MeasurablePolicy State Action)
    (context : (n : Nat) -> ((j : Finset.Iic n) -> Rat) -> Context)
    (state : (n : Nat) -> ((j : Finset.Iic n) -> Rat) -> State)
    (hcontext : forall n : Nat, Measurable (context n))
    (hstate : forall n : Nat, Measurable (state n))
    (defaultAction : Action)
    (reward : Omega -> RewardTrace Rat)
    (haction : forall t : Nat,
      Measurable (fun omega : Omega => action omega t))
    (hreward : forall t : Nat,
      Measurable (fun omega : Omega => reward omega t))
    (source :
      ConditionalExpectationReward.GeneratedActionRandomPairMapSource
        mu action rewardKernel policy context state defaultAction reward
        haction hreward)
    (i : Nat) :
    Filter.Eventually
      (fun omega : Omega =>
        @MeasureTheory.Measure.map Omega ((j : Finset.Iic (i + 1)) -> Prod Action Rat)
          mOmega inferInstance
          (fun y : Omega =>
            History.finitePairHistoryOfTrace (action y) (reward y) (i + 1))
          (@ProbabilityTheory.condExpKernel Omega mOmega _ mu _
            ((History.historyFiltrationSucc action reward haction hreward) i)
            omega) =
        RewardKernel.actionRewardPartialTrajectoryKernel rewardKernel policy
          (fun n history =>
            context n (History.pairHistoryRewardProjection history))
          (fun n history =>
            state n (History.pairHistoryRewardProjection history))
          (fun n : Nat =>
            (hcontext n).comp
              (History.measurable_pairHistoryRewardProjection
                (Action := Action) (Reward := Rat) n))
          (fun n : Nat =>
            (hstate n).comp
              (History.measurable_pairHistoryRewardProjection
                (Action := Action) (Reward := Rat) n))
          i (i + 1)
          (History.finitePairHistoryOfTrace
            (action omega) (reward omega) i))
      (MeasureTheory.ae
        (mu.trim
          ((History.historyFiltrationSucc action reward haction hreward).le
            i))) := by
  exact
    ConditionalExpectationReward.actionRewardPartialTrajectoryKernel_map_eq_historyFiltrationSucc_finitePairHistoryOfTrace_of_generatedActionRandomPairMapSource
      (mOmega := mOmega)
      mu action rewardKernel policy context state hcontext hstate defaultAction
      reward haction hreward source i

example {Omega Context State Action : Type}
    [mOmega : MeasurableSpace Omega] [StandardBorelSpace Omega]
    [MeasurableSpace Context] [MeasurableSpace State]
    [MeasurableSpace Action] [MeasurableSingletonClass Action]
    [Countable Action]
    (mu : MeasureTheory.Measure Omega) [MeasureTheory.IsFiniteMeasure mu]
    (action : Omega -> ActionTrace Action)
    (rewardKernel : RewardKernel.MarkovRewardKernel (Prod Context Action) Rat)
    (policy : Nat -> Policy.MeasurablePolicy State Action)
    (context : (n : Nat) -> ((j : Finset.Iic n) -> Rat) -> Context)
    (state : (n : Nat) -> ((j : Finset.Iic n) -> Rat) -> State)
    (hcontext : forall n : Nat, Measurable (context n))
    (hstate : forall n : Nat, Measurable (state n))
    (mean : Context -> Action -> Rat)
    (varianceProxy : Context -> Action -> NNReal)
    (law :
      RewardKernel.CenteredRewardKernelLaw rewardKernel mean varianceProxy)
    (defaultAction : Action)
    (reward : Omega -> RewardTrace Rat)
    (haction : forall t : Nat,
      Measurable (fun omega : Omega => action omega t))
    (hreward : forall t : Nat,
      Measurable (fun omega : Omega => reward omega t))
    (source :
      ConditionalExpectationReward.GeneratedActionRandomPairMapSource
        mu action rewardKernel policy context state defaultAction reward
        haction hreward)
    (i : Nat)
    (h_integrable :
      MeasureTheory.Integrable
        (fun omega : Omega =>
          (((reward omega (i + 1) -
            mean
              (context i
                (History.finiteRewardHistoryOfTrace (reward omega) i))
              ((policy i).action
                (state i
                  (History.finiteRewardHistoryOfTrace (reward omega) i))) :
                Rat) : Real))) mu) :
    Filter.EventuallyEq (MeasureTheory.ae mu)
      (@MeasureTheory.condExp Omega Real
        ((History.historyFiltrationSucc action reward haction hreward) i)
        mOmega _ _ _ mu
        (fun omega : Omega =>
          (((reward omega (i + 1) -
            mean
              (context i
                (History.finiteRewardHistoryOfTrace (reward omega) i))
              ((policy i).action
                (state i
                  (History.finiteRewardHistoryOfTrace (reward omega) i))) :
                Rat) : Real))))
      (fun _omega : Omega => (0 : Real)) := by
  exact
    ConditionalExpectationReward.centeredReward_succ_condExp_eq_zero_of_generatedActionRandomPairMapSource
      (mOmega := mOmega)
      mu action rewardKernel policy context state hcontext hstate mean
      varianceProxy law defaultAction reward haction hreward source i
      h_integrable

example {Omega Context State Action : Type}
    [mOmega : MeasurableSpace Omega] [StandardBorelSpace Omega]
    [MeasurableSpace Context] [MeasurableSpace State]
    [MeasurableSpace Action] [MeasurableSingletonClass Action]
    [Countable Action]
    (mu : MeasureTheory.Measure Omega) [MeasureTheory.IsFiniteMeasure mu]
    (action : Omega -> ActionTrace Action)
    (rewardKernel : RewardKernel.MarkovRewardKernel (Prod Context Action) Rat)
    (policy : Nat -> Policy.MeasurablePolicy State Action)
    (context : (n : Nat) -> ((j : Finset.Iic n) -> Rat) -> Context)
    (state : (n : Nat) -> ((j : Finset.Iic n) -> Rat) -> State)
    (hcontext : forall n : Nat, Measurable (context n))
    (hstate : forall n : Nat, Measurable (state n))
    (mean : Context -> Action -> Rat)
    (varianceProxy : Context -> Action -> NNReal)
    (hmean :
      Measurable (fun pair : Prod Context Action => mean pair.1 pair.2))
    (law :
      RewardKernel.CenteredRewardKernelLaw rewardKernel mean varianceProxy)
    (defaultAction : Action)
    (reward : Omega -> RewardTrace Rat)
    (haction : forall t : Nat,
      Measurable (fun omega : Omega => action omega t))
    (hreward : forall t : Nat,
      Measurable (fun omega : Omega => reward omega t))
    (rewardLo rewardHi meanLo meanHi : Nat -> Real)
    (hraw :
      forall i : Nat, forall omega : Omega,
        Set.Icc (rewardLo i) (rewardHi i)
          (((reward omega (i + 1) : Rat) : Real)))
    (hmean_range :
      forall i : Nat, forall context : Context, forall action : Action,
        Set.Icc (meanLo i) (meanHi i)
          (((mean context action : Rat) : Real)))
    (source :
      ConditionalExpectationReward.GeneratedActionRandomPairMapSource
        mu action rewardKernel policy context state defaultAction reward
        haction hreward)
    (i : Nat) :
    Filter.EventuallyEq (MeasureTheory.ae mu)
      (@MeasureTheory.condExp Omega Real
        ((History.historyFiltrationSucc action reward haction hreward) i)
        mOmega _ _ _ mu
        (fun omega : Omega =>
          (((reward omega (i + 1) -
            mean
              (context i
                (History.finiteRewardHistoryOfTrace (reward omega) i))
              ((policy i).action
                (state i
                  (History.finiteRewardHistoryOfTrace (reward omega) i))) :
                Rat) : Real))))
      (fun _omega : Omega => (0 : Real)) := by
  exact
    ConditionalExpectationReward.centeredReward_succ_condExp_eq_zero_of_generatedActionRandomPairMapSource_rawRangeMeasurableMeanRangeBounded
      (mOmega := mOmega)
      mu action rewardKernel policy context state hcontext hstate mean
      varianceProxy hmean law defaultAction reward haction hreward
      rewardLo rewardHi meanLo meanHi hraw hmean_range source i

example {Omega Context State Action : Type}
    [mOmega : MeasurableSpace Omega] [StandardBorelSpace Omega]
    [MeasurableSpace Context] [MeasurableSpace State]
    [MeasurableSpace Action] [MeasurableSingletonClass Action]
    [Countable Action]
    (mu : MeasureTheory.Measure Omega) [MeasureTheory.IsFiniteMeasure mu]
    (rewardKernel : RewardKernel.MarkovRewardKernel (Prod Context Action) Rat)
    (policy : Nat -> Policy.MeasurablePolicy State Action)
    (context : (n : Nat) -> ((j : Finset.Iic n) -> Rat) -> Context)
    (state : (n : Nat) -> ((j : Finset.Iic n) -> Rat) -> State)
    (defaultAction : Action)
    (reward : Omega -> RewardTrace Rat)
    (hreward : forall t : Nat,
      Measurable (fun omega : Omega => reward omega t))
    (source :
      ConditionalExpectationReward.GeneratedActionRandomPairDefinitionalMapSource
        mu rewardKernel policy context state defaultAction reward hreward) :
    ConditionalExpectationReward.GeneratedActionDefinitionalActualRewardMapSource
      mu rewardKernel policy context state defaultAction reward hreward := by
  exact
    ConditionalExpectationReward.generatedActionDefinitionalActualRewardMapSource_of_randomPairDefinitionalMapSource
      (mOmega := mOmega)
      mu rewardKernel policy context state defaultAction reward hreward source

example {Omega State Action : Type}
    [mOmega : MeasurableSpace Omega]
    [MeasurableSpace State] [MeasurableSpace Action]
    (policy : Nat -> Policy.MeasurablePolicy State Action)
    (state : (n : Nat) -> ((j : Finset.Iic n) -> Rat) -> State)
    (defaultAction : Action)
    (reward : Omega -> RewardTrace Rat)
    (hreward : forall t : Nat,
      Measurable (fun omega : Omega => reward omega t))
    (hstate : forall n : Nat, Measurable (state n))
    (t : Nat) :
    Measurable
      (fun omega : Omega =>
        ConditionalExpectationReward.generatedActionFromRewardHistory
          policy state defaultAction reward omega t) := by
  exact
    ConditionalExpectationReward.generatedActionFromRewardHistory_measurable
      (mOmega := mOmega) policy state defaultAction reward hreward hstate t

example {Omega Context State Action : Type}
    [mOmega : MeasurableSpace Omega] [StandardBorelSpace Omega]
    [MeasurableSpace Context] [MeasurableSpace State]
    [MeasurableSpace Action] [MeasurableSingletonClass Action]
    [Countable Action]
    (mu : MeasureTheory.Measure Omega) [MeasureTheory.IsFiniteMeasure mu]
    (rewardKernel : RewardKernel.MarkovRewardKernel (Prod Context Action) Rat)
    (policy : Nat -> Policy.MeasurablePolicy State Action)
    (context : (n : Nat) -> ((j : Finset.Iic n) -> Rat) -> Context)
    (state : (n : Nat) -> ((j : Finset.Iic n) -> Rat) -> State)
    (defaultAction : Action)
    (reward : Omega -> RewardTrace Rat)
    (hreward : forall t : Nat,
      Measurable (fun omega : Omega => reward omega t))
    (source :
      ConditionalExpectationReward.GeneratedActionRandomPairDefinitionalMapSource
        mu rewardKernel policy context state defaultAction reward hreward) :
    ConditionalExpectationReward.GeneratedActionRandomPairMapSource mu
      (ConditionalExpectationReward.generatedActionFromRewardHistory
        policy state defaultAction reward)
      rewardKernel policy context state defaultAction reward
      (ConditionalExpectationReward.generatedActionFromRewardHistory_measurable
        (policy := policy) (state := state) (defaultAction := defaultAction)
        (reward := reward) hreward source.hstate)
      hreward := by
  exact
    ConditionalExpectationReward.generatedActionRandomPairMapSource_of_definitionalMapSource
      (mOmega := mOmega)
      mu rewardKernel policy context state defaultAction reward hreward source

example {Omega Context State Action : Type}
    [mOmega : MeasurableSpace Omega] [StandardBorelSpace Omega]
    [MeasurableSpace Context] [MeasurableSpace State]
    [MeasurableSpace Action] [MeasurableSingletonClass Action]
    [Countable Action]
    (mu : MeasureTheory.Measure Omega) [MeasureTheory.IsFiniteMeasure mu]
    (rewardKernel : RewardKernel.MarkovRewardKernel (Prod Context Action) Rat)
    (policy : Nat -> Policy.MeasurablePolicy State Action)
    (context : (n : Nat) -> ((j : Finset.Iic n) -> Rat) -> Context)
    (state : (n : Nat) -> ((j : Finset.Iic n) -> Rat) -> State)
    (hcontext : forall n : Nat, Measurable (context n))
    (hstate : forall n : Nat, Measurable (state n))
    (defaultAction : Action)
    (reward : Omega -> RewardTrace Rat)
    (hreward : forall t : Nat,
      Measurable (fun omega : Omega => reward omega t))
    (h_kernel_extend_map_eq :
      forall i : Nat,
        Filter.Eventually
          (fun omega : Omega =>
            @MeasureTheory.Measure.map Omega
              ((j : Finset.Iic (i + 1)) -> Prod Action Rat)
              mOmega inferInstance
              (fun y : Omega =>
                History.extendPairHistorySucc
                  (History.finitePairHistoryOfTrace
                    (ConditionalExpectationReward.generatedActionFromRewardHistory
                      policy state defaultAction reward omega)
                    (reward omega) i)
                  (ConditionalExpectationReward.generatedActionFromRewardHistory
                    policy state defaultAction reward y (i + 1),
                    reward y (i + 1)))
              (@ProbabilityTheory.condExpKernel Omega mOmega _ mu _
                ((History.historyFiltrationSucc
                  (ConditionalExpectationReward.generatedActionFromRewardHistory
                    policy state defaultAction reward)
                  reward
                  (ConditionalExpectationReward.generatedActionFromRewardHistory_measurable
                    (policy := policy) (state := state)
                    (defaultAction := defaultAction) (reward := reward)
                    hreward hstate)
                  hreward) i)
                omega) =
            RewardKernel.actionRewardPartialTrajectoryKernel rewardKernel policy
              (fun n history =>
                context n (History.pairHistoryRewardProjection history))
              (fun n history =>
                state n (History.pairHistoryRewardProjection history))
              (fun n : Nat =>
                (hcontext n).comp
                  (History.measurable_pairHistoryRewardProjection
                    (Action := Action) (Reward := Rat) n))
              (fun n : Nat =>
                (hstate n).comp
                  (History.measurable_pairHistoryRewardProjection
                    (Action := Action) (Reward := Rat) n))
              i (i + 1)
              (History.finitePairHistoryOfTrace
                (ConditionalExpectationReward.generatedActionFromRewardHistory
                  policy state defaultAction reward omega)
                (reward omega) i))
          (MeasureTheory.ae
            (mu.trim
              ((History.historyFiltrationSucc
                (ConditionalExpectationReward.generatedActionFromRewardHistory
                  policy state defaultAction reward)
                reward
                (ConditionalExpectationReward.generatedActionFromRewardHistory_measurable
                  (policy := policy) (state := state)
                  (defaultAction := defaultAction) (reward := reward)
                  hreward hstate)
                hreward).le i)))) :
    ConditionalExpectationReward.GeneratedActionRandomPairDefinitionalMapSource
      mu rewardKernel policy context state defaultAction reward hreward := by
  exact
    ConditionalExpectationReward.generatedActionRandomPairDefinitionalMapSource_of_actionRewardPartialTrajectoryKernel_extend_map_eq
      (mOmega := mOmega)
      mu rewardKernel policy context state hcontext hstate defaultAction reward
      hreward h_kernel_extend_map_eq

example {Omega Context State Action : Type}
    [mOmega : MeasurableSpace Omega] [StandardBorelSpace Omega]
    [MeasurableSpace Context] [MeasurableSpace State]
    [MeasurableSpace Action] [MeasurableSingletonClass Action]
    [Countable Action]
    (mu : MeasureTheory.Measure Omega) [MeasureTheory.IsFiniteMeasure mu]
    (rewardKernel : RewardKernel.MarkovRewardKernel (Prod Context Action) Rat)
    (policy : Nat -> Policy.MeasurablePolicy State Action)
    (context : (n : Nat) -> ((j : Finset.Iic n) -> Rat) -> Context)
    (state : (n : Nat) -> ((j : Finset.Iic n) -> Rat) -> State)
    (mean : Context -> Action -> Rat)
    (varianceProxy : Context -> Action -> NNReal)
    (defaultAction : Action)
    (reward : Omega -> RewardTrace Rat)
    (hreward : forall t : Nat,
      Measurable (fun omega : Omega => reward omega t))
    (rewardLo rewardHi meanLo meanHi : Nat -> Real)
    (hcontext : forall n : Nat, Measurable (context n))
    (hstate : forall n : Nat, Measurable (state n))
    (hmean :
      Measurable (fun pair : Prod Context Action => mean pair.1 pair.2))
    (hkernel :
      RewardKernel.CenteredRewardKernelLaw rewardKernel mean varianceProxy)
    (hraw :
      forall i : Nat, forall omega : Omega,
        Set.Icc (rewardLo i) (rewardHi i)
          (((reward omega (i + 1) : Rat) : Real)))
    (hmean_range :
      forall i : Nat, forall context : Context, forall action : Action,
        Set.Icc (meanLo i) (meanHi i)
          (((mean context action : Rat) : Real)))
    (h_kernel_extend_map_eq :
      forall i : Nat,
        Filter.Eventually
          (fun omega : Omega =>
            @MeasureTheory.Measure.map Omega
              ((j : Finset.Iic (i + 1)) -> Prod Action Rat)
              mOmega inferInstance
              (fun y : Omega =>
                History.extendPairHistorySucc
                  (History.finitePairHistoryOfTrace
                    (ConditionalExpectationReward.generatedActionFromRewardHistory
                      policy state defaultAction reward omega)
                    (reward omega) i)
                  (ConditionalExpectationReward.generatedActionFromRewardHistory
                    policy state defaultAction reward y (i + 1),
                    reward y (i + 1)))
              (@ProbabilityTheory.condExpKernel Omega mOmega _ mu _
                ((History.historyFiltrationSucc
                  (ConditionalExpectationReward.generatedActionFromRewardHistory
                    policy state defaultAction reward)
                  reward
                  (ConditionalExpectationReward.generatedActionFromRewardHistory_measurable
                    (policy := policy) (state := state)
                    (defaultAction := defaultAction) (reward := reward)
                    hreward hstate)
                  hreward) i)
                omega) =
            RewardKernel.actionRewardPartialTrajectoryKernel rewardKernel policy
              (fun n history =>
                context n (History.pairHistoryRewardProjection history))
              (fun n history =>
                state n (History.pairHistoryRewardProjection history))
              (fun n : Nat =>
                (hcontext n).comp
                  (History.measurable_pairHistoryRewardProjection
                    (Action := Action) (Reward := Rat) n))
              (fun n : Nat =>
                (hstate n).comp
                  (History.measurable_pairHistoryRewardProjection
                    (Action := Action) (Reward := Rat) n))
              i (i + 1)
              (History.finitePairHistoryOfTrace
                (ConditionalExpectationReward.generatedActionFromRewardHistory
                  policy state defaultAction reward omega)
                (reward omega) i))
          (MeasureTheory.ae
            (mu.trim
              ((History.historyFiltrationSucc
                (ConditionalExpectationReward.generatedActionFromRewardHistory
                  policy state defaultAction reward)
                reward
                (ConditionalExpectationReward.generatedActionFromRewardHistory_measurable
                  (policy := policy) (state := state)
                  (defaultAction := defaultAction) (reward := reward)
                  hreward hstate)
                hreward).le i)))) :
    ConditionalExpectationReward.GeneratedActionRandomPairDefinitionalRawRangeMeasurableMeanRangeBoundedSource
      mu rewardKernel policy context state mean varianceProxy defaultAction
      reward hreward rewardLo rewardHi meanLo meanHi := by
  exact
    ConditionalExpectationReward.generatedActionRandomPairDefinitionalRawRangeMeasurableMeanRangeBoundedSource_of_actionRewardPartialTrajectoryKernel_extend_map_eq
      (mOmega := mOmega)
      mu rewardKernel policy context state mean varianceProxy defaultAction
      reward hreward rewardLo rewardHi meanLo meanHi hcontext hstate hmean
      hkernel hraw hmean_range h_kernel_extend_map_eq

example {Omega Context State Action : Type}
    [mOmega : MeasurableSpace Omega] [StandardBorelSpace Omega]
    [MeasurableSpace Context] [MeasurableSpace State]
    [MeasurableSpace Action] [MeasurableSingletonClass Action]
    [Countable Action]
    (mu : MeasureTheory.Measure Omega) [MeasureTheory.IsFiniteMeasure mu]
    (rewardKernel : RewardKernel.MarkovRewardKernel (Prod Context Action) Rat)
    (policy : Nat -> Policy.MeasurablePolicy State Action)
    (context : (n : Nat) -> ((j : Finset.Iic n) -> Rat) -> Context)
    (state : (n : Nat) -> ((j : Finset.Iic n) -> Rat) -> State)
    (mean : Context -> Action -> Rat)
    (varianceProxy : Context -> Action -> NNReal)
    (defaultAction : Action)
    (reward : Omega -> RewardTrace Rat)
    (hreward : forall t : Nat,
      Measurable (fun omega : Omega => reward omega t))
    (rewardLo rewardHi meanLo meanHi : Nat -> Real)
    (hcontext : forall n : Nat, Measurable (context n))
    (hstate : forall n : Nat, Measurable (state n))
    (hmean :
      Measurable (fun pair : Prod Context Action => mean pair.1 pair.2))
    (hkernel :
      RewardKernel.CenteredRewardKernelLaw rewardKernel mean varianceProxy)
    (hraw :
      forall i : Nat, forall omega : Omega,
        Set.Icc (rewardLo i) (rewardHi i)
          (((reward omega (i + 1) : Rat) : Real)))
    (hmean_range :
      forall i : Nat, forall context : Context, forall action : Action,
        Set.Icc (meanLo i) (meanHi i)
          (((mean context action : Rat) : Real)))
    (h_kernel_pair_map_eq :
      forall i : Nat,
        Filter.Eventually
          (fun omega : Omega =>
            @MeasureTheory.Measure.map Omega (Prod Action Rat) mOmega
              inferInstance
              (fun y : Omega =>
                (ConditionalExpectationReward.generatedActionFromRewardHistory
                  policy state defaultAction reward y (i + 1),
                  reward y (i + 1)))
              (@ProbabilityTheory.condExpKernel Omega mOmega _ mu _
                ((History.historyFiltrationSucc
                  (ConditionalExpectationReward.generatedActionFromRewardHistory
                    policy state defaultAction reward)
                  reward
                  (ConditionalExpectationReward.generatedActionFromRewardHistory_measurable
                    (policy := policy) (state := state)
                    (defaultAction := defaultAction) (reward := reward)
                    hreward hstate)
                  hreward) i)
                omega) =
            RewardKernel.actionRewardHistoryStepKernelFamily rewardKernel policy
              (fun n history =>
                context n (History.pairHistoryRewardProjection history))
              (fun n history =>
                state n (History.pairHistoryRewardProjection history))
              (fun n : Nat =>
                (hcontext n).comp
                  (History.measurable_pairHistoryRewardProjection
                    (Action := Action) (Reward := Rat) n))
              (fun n : Nat =>
                (hstate n).comp
                  (History.measurable_pairHistoryRewardProjection
                    (Action := Action) (Reward := Rat) n))
              i
              (History.finitePairHistoryOfTrace
                (ConditionalExpectationReward.generatedActionFromRewardHistory
                  policy state defaultAction reward omega)
                (reward omega) i))
          (MeasureTheory.ae
            (mu.trim
              ((History.historyFiltrationSucc
                (ConditionalExpectationReward.generatedActionFromRewardHistory
                  policy state defaultAction reward)
                reward
                (ConditionalExpectationReward.generatedActionFromRewardHistory_measurable
                  (policy := policy) (state := state)
                  (defaultAction := defaultAction) (reward := reward)
                  hreward hstate)
                hreward).le i)))) :
    ConditionalExpectationReward.GeneratedActionRandomPairDefinitionalRawRangeMeasurableMeanRangeBoundedSource
      mu rewardKernel policy context state mean varianceProxy defaultAction
      reward hreward rewardLo rewardHi meanLo meanHi := by
  exact
    ConditionalExpectationReward.generatedActionRandomPairDefinitionalRawRangeMeasurableMeanRangeBoundedSource_of_actionRewardHistoryStepKernelFamily_pair_map_eq
      (mOmega := mOmega)
      mu rewardKernel policy context state mean varianceProxy defaultAction
      reward hreward rewardLo rewardHi meanLo meanHi hcontext hstate hmean
      hkernel hraw hmean_range h_kernel_pair_map_eq

example {Omega Context State Action : Type}
    [mOmega : MeasurableSpace Omega] [StandardBorelSpace Omega]
    [MeasurableSpace Context] [MeasurableSpace State]
    [MeasurableSpace Action] [MeasurableSingletonClass Action]
    [Countable Action]
    (mu : MeasureTheory.Measure Omega) [MeasureTheory.IsFiniteMeasure mu]
    (rewardKernel : RewardKernel.MarkovRewardKernel (Prod Context Action) Rat)
    (policy : Nat -> Policy.MeasurablePolicy State Action)
    (context : (n : Nat) -> ((j : Finset.Iic n) -> Rat) -> Context)
    (state : (n : Nat) -> ((j : Finset.Iic n) -> Rat) -> State)
    (mean : Context -> Action -> Rat)
    (varianceProxy : Context -> Action -> NNReal)
    (defaultAction : Action)
    (reward : Omega -> RewardTrace Rat)
    (hreward : forall t : Nat,
      Measurable (fun omega : Omega => reward omega t))
    (rewardLo rewardHi meanLo meanHi : Nat -> Real)
    (hcontext : forall n : Nat, Measurable (context n))
    (hstate : forall n : Nat, Measurable (state n))
    (hmean :
      Measurable (fun pair : Prod Context Action => mean pair.1 pair.2))
    (hkernel :
      RewardKernel.CenteredRewardKernelLaw rewardKernel mean varianceProxy)
    (hraw :
      forall i : Nat, forall omega : Omega,
        Set.Icc (rewardLo i) (rewardHi i)
          (((reward omega (i + 1) : Rat) : Real)))
    (hmean_range :
      forall i : Nat, forall context : Context, forall action : Action,
        Set.Icc (meanLo i) (meanHi i)
          (((mean context action : Rat) : Real)))
    (h_kernel_partialtraj_map_eq :
      forall i : Nat,
        Filter.Eventually
          (fun omega : Omega =>
            @MeasureTheory.Measure.map Omega
              ((j : Finset.Iic (i + 1)) -> Prod Action Rat)
              mOmega inferInstance
              (fun y : Omega =>
                History.finitePairHistoryOfTrace
                  (ConditionalExpectationReward.generatedActionFromRewardHistory
                    policy state defaultAction reward y)
                  (reward y) (i + 1))
              (@ProbabilityTheory.condExpKernel Omega mOmega _ mu _
                ((History.historyFiltrationSucc
                  (ConditionalExpectationReward.generatedActionFromRewardHistory
                    policy state defaultAction reward)
                  reward
                  (ConditionalExpectationReward.generatedActionFromRewardHistory_measurable
                    (policy := policy) (state := state)
                    (defaultAction := defaultAction) (reward := reward)
                    hreward hstate)
                  hreward) i)
                omega) =
            RewardKernel.actionRewardPartialTrajectoryKernel rewardKernel policy
              (fun n history =>
                context n (History.pairHistoryRewardProjection history))
              (fun n history =>
                state n (History.pairHistoryRewardProjection history))
              (fun n : Nat =>
                (hcontext n).comp
                  (History.measurable_pairHistoryRewardProjection
                    (Action := Action) (Reward := Rat) n))
              (fun n : Nat =>
                (hstate n).comp
                  (History.measurable_pairHistoryRewardProjection
                    (Action := Action) (Reward := Rat) n))
              i (i + 1)
              (History.finitePairHistoryOfTrace
                (ConditionalExpectationReward.generatedActionFromRewardHistory
                  policy state defaultAction reward omega)
                (reward omega) i))
          (MeasureTheory.ae
            (mu.trim
              ((History.historyFiltrationSucc
                (ConditionalExpectationReward.generatedActionFromRewardHistory
                  policy state defaultAction reward)
                reward
                (ConditionalExpectationReward.generatedActionFromRewardHistory_measurable
                  (policy := policy) (state := state)
                  (defaultAction := defaultAction) (reward := reward)
                  hreward hstate)
                hreward).le i))))
    (i : Nat) :
    Filter.EventuallyEq (MeasureTheory.ae mu)
      (@MeasureTheory.condExp Omega Real
        ((History.historyFiltrationSucc
          (ConditionalExpectationReward.generatedActionFromRewardHistory
            policy state defaultAction reward)
          reward
          (ConditionalExpectationReward.generatedActionFromRewardHistory_measurable
            (policy := policy) (state := state)
            (defaultAction := defaultAction) (reward := reward)
            hreward hstate)
          hreward) i)
        mOmega _ _ _ mu
        (fun omega : Omega =>
          (((reward omega (i + 1) -
            mean
              (context i
                (History.finiteRewardHistoryOfTrace (reward omega) i))
              ((policy i).action
                (state i
                  (History.finiteRewardHistoryOfTrace (reward omega) i))) :
              Rat) : Real))))
      (fun _omega : Omega => (0 : Real)) := by
  exact
    ConditionalExpectationReward.centeredReward_succ_condExp_eq_zero_of_actionRewardPartialTrajectoryKernel_map_eq_definitionalRawRangeMeasurableMeanRangeBounded
      (mOmega := mOmega)
      mu rewardKernel policy context state mean varianceProxy defaultAction
      reward hreward rewardLo rewardHi meanLo meanHi hcontext hstate hmean
      hkernel hraw hmean_range h_kernel_partialtraj_map_eq i

example {Omega Context State Action : Type}
    [mOmega : MeasurableSpace Omega] [StandardBorelSpace Omega]
    [MeasurableSpace Context] [MeasurableSpace State]
    [MeasurableSpace Action] [MeasurableSingletonClass Action]
    [Countable Action]
    (mu : MeasureTheory.Measure Omega) [MeasureTheory.IsFiniteMeasure mu]
    (rewardKernel : RewardKernel.MarkovRewardKernel (Prod Context Action) Rat)
    (policy : Nat -> Policy.MeasurablePolicy State Action)
    (context : (n : Nat) -> ((j : Finset.Iic n) -> Rat) -> Context)
    (state : (n : Nat) -> ((j : Finset.Iic n) -> Rat) -> State)
    (mean : Context -> Action -> Rat)
    (varianceProxy : Context -> Action -> NNReal)
    (defaultAction : Action)
    (reward : Omega -> RewardTrace Rat)
    (hreward : forall t : Nat,
      Measurable (fun omega : Omega => reward omega t))
    (rewardLo rewardHi meanLo meanHi : Nat -> Real)
    (hcontext : forall n : Nat, Measurable (context n))
    (hstate : forall n : Nat, Measurable (state n))
    (hmean :
      Measurable (fun pair : Prod Context Action => mean pair.1 pair.2))
    (hkernel :
      RewardKernel.CenteredRewardKernelLaw rewardKernel mean varianceProxy)
    (hraw :
      forall i : Nat, forall omega : Omega,
        Set.Icc (rewardLo i) (rewardHi i)
          (((reward omega (i + 1) : Rat) : Real)))
    (hmean_range :
      forall i : Nat, forall context : Context, forall action : Action,
        Set.Icc (meanLo i) (meanHi i)
          (((mean context action : Rat) : Real)))
    (h_kernel_extend_map_eq :
      forall i : Nat,
        Filter.Eventually
          (fun omega : Omega =>
            @MeasureTheory.Measure.map Omega
              ((j : Finset.Iic (i + 1)) -> Prod Action Rat)
              mOmega inferInstance
              (fun y : Omega =>
                History.extendPairHistorySucc
                  (History.finitePairHistoryOfTrace
                    (ConditionalExpectationReward.generatedActionFromRewardHistory
                      policy state defaultAction reward omega)
                    (reward omega) i)
                  (ConditionalExpectationReward.generatedActionFromRewardHistory
                    policy state defaultAction reward y (i + 1),
                    reward y (i + 1)))
              (@ProbabilityTheory.condExpKernel Omega mOmega _ mu _
                ((History.historyFiltrationSucc
                  (ConditionalExpectationReward.generatedActionFromRewardHistory
                    policy state defaultAction reward)
                  reward
                  (ConditionalExpectationReward.generatedActionFromRewardHistory_measurable
                    (policy := policy) (state := state)
                    (defaultAction := defaultAction) (reward := reward)
                    hreward hstate)
                  hreward) i)
                omega) =
            RewardKernel.actionRewardPartialTrajectoryKernel rewardKernel policy
              (fun n history =>
                context n (History.pairHistoryRewardProjection history))
              (fun n history =>
                state n (History.pairHistoryRewardProjection history))
              (fun n : Nat =>
                (hcontext n).comp
                  (History.measurable_pairHistoryRewardProjection
                    (Action := Action) (Reward := Rat) n))
              (fun n : Nat =>
                (hstate n).comp
                  (History.measurable_pairHistoryRewardProjection
                    (Action := Action) (Reward := Rat) n))
              i (i + 1)
              (History.finitePairHistoryOfTrace
                (ConditionalExpectationReward.generatedActionFromRewardHistory
                  policy state defaultAction reward omega)
                (reward omega) i))
          (MeasureTheory.ae
            (mu.trim
              ((History.historyFiltrationSucc
                (ConditionalExpectationReward.generatedActionFromRewardHistory
                  policy state defaultAction reward)
                reward
                (ConditionalExpectationReward.generatedActionFromRewardHistory_measurable
                  (policy := policy) (state := state)
                  (defaultAction := defaultAction) (reward := reward)
                  hreward hstate)
                hreward).le i))))
    (i : Nat) :
    Filter.EventuallyEq (MeasureTheory.ae mu)
      (@MeasureTheory.condExp Omega Real
        ((History.historyFiltrationSucc
          (ConditionalExpectationReward.generatedActionFromRewardHistory
            policy state defaultAction reward)
          reward
          (ConditionalExpectationReward.generatedActionFromRewardHistory_measurable
            (policy := policy) (state := state)
            (defaultAction := defaultAction) (reward := reward)
            hreward hstate)
          hreward) i)
        mOmega _ _ _ mu
        (fun omega : Omega =>
          (((reward omega (i + 1) -
            mean
              (context i
                (History.finiteRewardHistoryOfTrace (reward omega) i))
              ((policy i).action
                (state i
                  (History.finiteRewardHistoryOfTrace (reward omega) i))) :
              Rat) : Real))))
      (fun _omega : Omega => (0 : Real)) := by
  exact
    ConditionalExpectationReward.centeredReward_succ_condExp_eq_zero_of_actionRewardPartialTrajectoryKernel_extend_map_eq_definitionalRawRangeMeasurableMeanRangeBounded
      (mOmega := mOmega)
      mu rewardKernel policy context state mean varianceProxy defaultAction
      reward hreward rewardLo rewardHi meanLo meanHi hcontext hstate hmean
      hkernel hraw hmean_range h_kernel_extend_map_eq i

example {Omega Context State Action : Type}
    [mOmega : MeasurableSpace Omega] [StandardBorelSpace Omega]
    [MeasurableSpace Context] [MeasurableSpace State]
    [MeasurableSpace Action] [MeasurableSingletonClass Action]
    [Countable Action]
    (mu : MeasureTheory.Measure Omega) [MeasureTheory.IsFiniteMeasure mu]
    (rewardKernel : RewardKernel.MarkovRewardKernel (Prod Context Action) Rat)
    (policy : Nat -> Policy.MeasurablePolicy State Action)
    (context : (n : Nat) -> ((j : Finset.Iic n) -> Rat) -> Context)
    (state : (n : Nat) -> ((j : Finset.Iic n) -> Rat) -> State)
    (mean : Context -> Action -> Rat)
    (varianceProxy : Context -> Action -> NNReal)
    (defaultAction : Action)
    (reward : Omega -> RewardTrace Rat)
    (hreward : forall t : Nat,
      Measurable (fun omega : Omega => reward omega t))
    (rewardLo rewardHi meanLo meanHi : Nat -> Real)
    (hcontext : forall n : Nat, Measurable (context n))
    (hstate : forall n : Nat, Measurable (state n))
    (hmean :
      Measurable (fun pair : Prod Context Action => mean pair.1 pair.2))
    (hkernel :
      RewardKernel.CenteredRewardKernelLaw rewardKernel mean varianceProxy)
    (hraw :
      forall i : Nat, forall omega : Omega,
        Set.Icc (rewardLo i) (rewardHi i)
          (((reward omega (i + 1) : Rat) : Real)))
    (hmean_range :
      forall i : Nat, forall context : Context, forall action : Action,
        Set.Icc (meanLo i) (meanHi i)
          (((mean context action : Rat) : Real)))
    (h_kernel_pair_map_eq :
      forall i : Nat,
        Filter.Eventually
          (fun omega : Omega =>
            @MeasureTheory.Measure.map Omega (Prod Action Rat) mOmega
              inferInstance
              (fun y : Omega =>
                (ConditionalExpectationReward.generatedActionFromRewardHistory
                  policy state defaultAction reward y (i + 1),
                  reward y (i + 1)))
              (@ProbabilityTheory.condExpKernel Omega mOmega _ mu _
                ((History.historyFiltrationSucc
                  (ConditionalExpectationReward.generatedActionFromRewardHistory
                    policy state defaultAction reward)
                  reward
                  (ConditionalExpectationReward.generatedActionFromRewardHistory_measurable
                    (policy := policy) (state := state)
                    (defaultAction := defaultAction) (reward := reward)
                    hreward hstate)
                  hreward) i)
                omega) =
            RewardKernel.actionRewardHistoryStepKernelFamily rewardKernel policy
              (fun n history =>
                context n (History.pairHistoryRewardProjection history))
              (fun n history =>
                state n (History.pairHistoryRewardProjection history))
              (fun n : Nat =>
                (hcontext n).comp
                  (History.measurable_pairHistoryRewardProjection
                    (Action := Action) (Reward := Rat) n))
              (fun n : Nat =>
                (hstate n).comp
                  (History.measurable_pairHistoryRewardProjection
                    (Action := Action) (Reward := Rat) n))
              i
              (History.finitePairHistoryOfTrace
                (ConditionalExpectationReward.generatedActionFromRewardHistory
                  policy state defaultAction reward omega)
                (reward omega) i))
          (MeasureTheory.ae
            (mu.trim
              ((History.historyFiltrationSucc
                (ConditionalExpectationReward.generatedActionFromRewardHistory
                  policy state defaultAction reward)
                reward
                (ConditionalExpectationReward.generatedActionFromRewardHistory_measurable
                  (policy := policy) (state := state)
                  (defaultAction := defaultAction) (reward := reward)
                  hreward hstate)
                hreward).le i))))
    (i : Nat) :
    Filter.EventuallyEq (MeasureTheory.ae mu)
      (@MeasureTheory.condExp Omega Real
        ((History.historyFiltrationSucc
          (ConditionalExpectationReward.generatedActionFromRewardHistory
            policy state defaultAction reward)
          reward
          (ConditionalExpectationReward.generatedActionFromRewardHistory_measurable
            (policy := policy) (state := state)
            (defaultAction := defaultAction) (reward := reward)
            hreward hstate)
          hreward) i)
        mOmega _ _ _ mu
        (fun omega : Omega =>
          (((reward omega (i + 1) -
            mean
              (context i
                (History.finiteRewardHistoryOfTrace (reward omega) i))
              ((policy i).action
                (state i
                  (History.finiteRewardHistoryOfTrace (reward omega) i))) :
              Rat) : Real))))
      (fun _omega : Omega => (0 : Real)) := by
  exact
    ConditionalExpectationReward.centeredReward_succ_condExp_eq_zero_of_actionRewardHistoryStepKernelFamily_pair_map_eq_definitionalRawRangeMeasurableMeanRangeBounded
      (mOmega := mOmega)
      mu rewardKernel policy context state mean varianceProxy defaultAction
      reward hreward rewardLo rewardHi meanLo meanHi hcontext hstate hmean
      hkernel hraw hmean_range h_kernel_pair_map_eq i

example {Omega Context State Action : Type}
    [mOmega : MeasurableSpace Omega] [StandardBorelSpace Omega]
    [MeasurableSpace Context] [MeasurableSpace State]
    [MeasurableSpace Action] [MeasurableSingletonClass Action]
    [Countable Action]
    (mu : MeasureTheory.Measure Omega) [MeasureTheory.IsFiniteMeasure mu]
    (rewardKernel : RewardKernel.MarkovRewardKernel (Prod Context Action) Rat)
    (policy : Nat -> Policy.MeasurablePolicy State Action)
    (context : (n : Nat) -> ((j : Finset.Iic n) -> Rat) -> Context)
    (state : (n : Nat) -> ((j : Finset.Iic n) -> Rat) -> State)
    (mean : Context -> Action -> Rat)
    (varianceProxy : Context -> Action -> NNReal)
    (defaultAction : Action)
    (reward : Omega -> RewardTrace Rat)
    (hreward : forall t : Nat,
      Measurable (fun omega : Omega => reward omega t))
    (rewardLo rewardHi meanLo meanHi : Nat -> Real)
    (hcontext : forall n : Nat, Measurable (context n))
    (hstate : forall n : Nat, Measurable (state n))
    (hmean :
      Measurable (fun pair : Prod Context Action => mean pair.1 pair.2))
    (hkernel :
      RewardKernel.CenteredRewardKernelLaw rewardKernel mean varianceProxy)
    (hraw :
      forall i : Nat, forall omega : Omega,
        Set.Icc (rewardLo i) (rewardHi i)
          (((reward omega (i + 1) : Rat) : Real)))
    (hmean_range :
      forall i : Nat, forall context : Context, forall action : Action,
        Set.Icc (meanLo i) (meanHi i)
          (((mean context action : Rat) : Real)))
    (h_reward_map_eq_actual_action :
      forall i : Nat,
        Filter.Eventually
          (fun omega : Omega =>
            @MeasureTheory.Measure.map Omega Rat mOmega inferInstance
              (fun y : Omega => reward y (i + 1))
              (@ProbabilityTheory.condExpKernel Omega mOmega _ mu _
                ((History.historyFiltrationSucc
                  (ConditionalExpectationReward.generatedActionFromRewardHistory
                    policy state defaultAction reward)
                  reward
                  (ConditionalExpectationReward.generatedActionFromRewardHistory_measurable
                    (policy := policy) (state := state)
                    (defaultAction := defaultAction) (reward := reward)
                    hreward hstate)
                  hreward) i)
                omega) =
            RewardKernel.selectedMeasure rewardKernel
              (context i
                (History.finiteRewardHistoryOfTrace (reward omega) i))
              (ConditionalExpectationReward.generatedActionFromRewardHistory
                policy state defaultAction reward omega (i + 1)))
          (MeasureTheory.ae
            (mu.trim
              ((History.historyFiltrationSucc
                (ConditionalExpectationReward.generatedActionFromRewardHistory
                  policy state defaultAction reward)
                reward
                (ConditionalExpectationReward.generatedActionFromRewardHistory_measurable
                  (policy := policy) (state := state)
                  (defaultAction := defaultAction) (reward := reward)
                  hreward hstate)
                hreward).le i))))
    (i : Nat) :
    Filter.EventuallyEq (MeasureTheory.ae mu)
      (@MeasureTheory.condExp Omega Real
        ((History.historyFiltrationSucc
          (ConditionalExpectationReward.generatedActionFromRewardHistory
            policy state defaultAction reward)
          reward
          (ConditionalExpectationReward.generatedActionFromRewardHistory_measurable
            (policy := policy) (state := state)
            (defaultAction := defaultAction) (reward := reward)
            hreward hstate)
          hreward) i)
        mOmega _ _ _ mu
        (fun omega : Omega =>
          (((reward omega (i + 1) -
            mean
              (context i
                (History.finiteRewardHistoryOfTrace (reward omega) i))
              ((policy i).action
                (state i
                  (History.finiteRewardHistoryOfTrace (reward omega) i))) :
              Rat) : Real))))
      (fun _omega : Omega => (0 : Real)) := by
  exact
    ConditionalExpectationReward.centeredReward_succ_condExp_eq_zero_of_reward_map_eq_actual_action_definitionalRawRangeMeasurableMeanRangeBounded
      (mOmega := mOmega)
      mu rewardKernel policy context state mean varianceProxy defaultAction
      reward hreward rewardLo rewardHi meanLo meanHi hcontext hstate hmean
      hkernel hraw hmean_range h_reward_map_eq_actual_action i

example {Omega Context State Action : Type}
    [mOmega : MeasurableSpace Omega] [StandardBorelSpace Omega]
    [MeasurableSpace Context] [MeasurableSpace State]
    [MeasurableSpace Action] [MeasurableSingletonClass Action]
    [Countable Action]
    (mu : MeasureTheory.Measure Omega) [MeasureTheory.IsFiniteMeasure mu]
    (rewardKernel : RewardKernel.MarkovRewardKernel (Prod Context Action) Rat)
    (policy : Nat -> Policy.MeasurablePolicy State Action)
    (context : (n : Nat) -> ((j : Finset.Iic n) -> Rat) -> Context)
    (state : (n : Nat) -> ((j : Finset.Iic n) -> Rat) -> State)
    (mean : Context -> Action -> Rat)
    (varianceProxy : Context -> Action -> NNReal)
    (defaultAction : Action)
    (reward : Omega -> RewardTrace Rat)
    (hreward : forall t : Nat,
      Measurable (fun omega : Omega => reward omega t))
    (rewardLo rewardHi meanLo meanHi : Nat -> Real)
    (hcontext : forall n : Nat, Measurable (context n))
    (hstate : forall n : Nat, Measurable (state n))
    (hmean :
      Measurable (fun pair : Prod Context Action => mean pair.1 pair.2))
    (hkernel :
      RewardKernel.CenteredRewardKernelLaw rewardKernel mean varianceProxy)
    (hraw :
      forall i : Nat, forall omega : Omega,
        Set.Icc (rewardLo i) (rewardHi i)
          (((reward omega (i + 1) : Rat) : Real)))
    (hmean_range :
      forall i : Nat, forall context : Context, forall action : Action,
        Set.Icc (meanLo i) (meanHi i)
          (((mean context action : Rat) : Real)))
    (h_reward_map_eq_policy :
      forall i : Nat,
        Filter.Eventually
          (fun omega : Omega =>
            @MeasureTheory.Measure.map Omega Rat mOmega inferInstance
              (fun y : Omega => reward y (i + 1))
              (@ProbabilityTheory.condExpKernel Omega mOmega _ mu _
                ((History.historyFiltrationSucc
                  (ConditionalExpectationReward.generatedActionFromRewardHistory
                    policy state defaultAction reward)
                  reward
                  (ConditionalExpectationReward.generatedActionFromRewardHistory_measurable
                    (policy := policy) (state := state)
                    (defaultAction := defaultAction) (reward := reward)
                    hreward hstate)
                  hreward) i)
                omega) =
            RewardKernel.selectedMeasure rewardKernel
              (context i
                (History.finiteRewardHistoryOfTrace (reward omega) i))
              ((policy i).action
                (state i
                  (History.finiteRewardHistoryOfTrace (reward omega) i))))
          (MeasureTheory.ae
            (mu.trim
              ((History.historyFiltrationSucc
                (ConditionalExpectationReward.generatedActionFromRewardHistory
                  policy state defaultAction reward)
                reward
                (ConditionalExpectationReward.generatedActionFromRewardHistory_measurable
                  (policy := policy) (state := state)
                  (defaultAction := defaultAction) (reward := reward)
                  hreward hstate)
                hreward).le i))))
    (i : Nat) :
    Filter.EventuallyEq (MeasureTheory.ae mu)
      (@MeasureTheory.condExp Omega Real
        ((History.historyFiltrationSucc
          (ConditionalExpectationReward.generatedActionFromRewardHistory
            policy state defaultAction reward)
          reward
          (ConditionalExpectationReward.generatedActionFromRewardHistory_measurable
            (policy := policy) (state := state)
            (defaultAction := defaultAction) (reward := reward)
            hreward hstate)
          hreward) i)
        mOmega _ _ _ mu
        (fun omega : Omega =>
          (((reward omega (i + 1) -
            mean
              (context i
                (History.finiteRewardHistoryOfTrace (reward omega) i))
              ((policy i).action
                (state i
                  (History.finiteRewardHistoryOfTrace (reward omega) i))) :
              Rat) : Real))))
      (fun _omega : Omega => (0 : Real)) := by
  exact
    ConditionalExpectationReward.centeredReward_succ_condExp_eq_zero_of_reward_map_eq_selected_policy_definitionalRawRangeMeasurableMeanRangeBounded
      (mOmega := mOmega)
      mu rewardKernel policy context state mean varianceProxy defaultAction
      reward hreward rewardLo rewardHi meanLo meanHi hcontext hstate hmean
      hkernel hraw hmean_range h_reward_map_eq_policy i

example {Omega Context State Action : Type}
    [mOmega : MeasurableSpace Omega] [StandardBorelSpace Omega]
    [MeasurableSpace Context] [MeasurableSpace State]
    [MeasurableSpace Action] [MeasurableSingletonClass Action]
    [Countable Action]
    (mu : MeasureTheory.Measure Omega) [MeasureTheory.IsFiniteMeasure mu]
    (rewardKernel : RewardKernel.MarkovRewardKernel (Prod Context Action) Rat)
    (policy : Nat -> Policy.MeasurablePolicy State Action)
    (context : (n : Nat) -> ((j : Finset.Iic n) -> Rat) -> Context)
    (state : (n : Nat) -> ((j : Finset.Iic n) -> Rat) -> State)
    (mean : Context -> Action -> Rat)
    (varianceProxy : Context -> Action -> NNReal)
    (defaultAction : Action)
    (reward : Omega -> RewardTrace Rat)
    (hreward : forall t : Nat,
      Measurable (fun omega : Omega => reward omega t))
    (rewardLo rewardHi meanLo meanHi : Nat -> Real)
    (hcontext : forall n : Nat, Measurable (context n))
    (hmean :
      Measurable (fun pair : Prod Context Action => mean pair.1 pair.2))
    (hkernel :
      RewardKernel.CenteredRewardKernelLaw rewardKernel mean varianceProxy)
    (hraw :
      forall i : Nat, forall omega : Omega,
        Set.Icc (rewardLo i) (rewardHi i)
          (((reward omega (i + 1) : Rat) : Real)))
    (hmean_range :
      forall i : Nat, forall context : Context, forall action : Action,
        Set.Icc (meanLo i) (meanHi i)
          (((mean context action : Rat) : Real)))
    (source :
      ConditionalExpectationReward.GeneratedActionDefinitionalActualRewardMapSource
        mu rewardKernel policy context state defaultAction reward hreward)
    (i : Nat) :
    Filter.EventuallyEq (MeasureTheory.ae mu)
      (@MeasureTheory.condExp Omega Real
        ((History.historyFiltrationSucc
          (ConditionalExpectationReward.generatedActionFromRewardHistory
            policy state defaultAction reward)
          reward
          (ConditionalExpectationReward.generatedActionFromRewardHistory_measurable
            (policy := policy) (state := state)
            (defaultAction := defaultAction) (reward := reward)
            hreward source.hstate)
          hreward) i)
        mOmega _ _ _ mu
        (fun omega : Omega =>
          (((reward omega (i + 1) -
            mean
              (context i
                (History.finiteRewardHistoryOfTrace (reward omega) i))
              ((policy i).action
                (state i
                  (History.finiteRewardHistoryOfTrace (reward omega) i))) :
              Rat) : Real))))
      (fun _omega : Omega => (0 : Real)) := by
  exact
    ConditionalExpectationReward.centeredReward_succ_condExp_eq_zero_of_generatedActionDefinitionalActualRewardMapSource_definitionalRawRangeMeasurableMeanRangeBounded
      (mOmega := mOmega)
      mu rewardKernel policy context state mean varianceProxy defaultAction
      reward hreward rewardLo rewardHi meanLo meanHi hcontext hmean hkernel
      hraw hmean_range source i

example {Omega Context State Action : Type}
    [mOmega : MeasurableSpace Omega] [StandardBorelSpace Omega]
    [MeasurableSpace Context] [MeasurableSpace State]
    [MeasurableSpace Action] [MeasurableSingletonClass Action]
    [Countable Action]
    (mu : MeasureTheory.Measure Omega) [MeasureTheory.IsFiniteMeasure mu]
    (rewardKernel : RewardKernel.MarkovRewardKernel (Prod Context Action) Rat)
    (policy : Nat -> Policy.MeasurablePolicy State Action)
    (context : (n : Nat) -> ((j : Finset.Iic n) -> Rat) -> Context)
    (state : (n : Nat) -> ((j : Finset.Iic n) -> Rat) -> State)
    (hcontext : forall n : Nat, Measurable (context n))
    (defaultAction : Action)
    (reward : Omega -> RewardTrace Rat)
    (hreward : forall t : Nat,
      Measurable (fun omega : Omega => reward omega t))
    (source :
      ConditionalExpectationReward.GeneratedActionRandomPairDefinitionalMapSource
        mu rewardKernel policy context state defaultAction reward hreward)
    (i : Nat) :
    Filter.Eventually
      (fun omega : Omega =>
        @MeasureTheory.Measure.map Omega (Prod Action Rat) mOmega inferInstance
          (fun y : Omega =>
            (ConditionalExpectationReward.generatedActionFromRewardHistory
              policy state defaultAction reward y (i + 1),
              reward y (i + 1)))
          (@ProbabilityTheory.condExpKernel Omega mOmega _ mu _
            ((History.historyFiltrationSucc
              (ConditionalExpectationReward.generatedActionFromRewardHistory
                policy state defaultAction reward)
              reward
              (ConditionalExpectationReward.generatedActionFromRewardHistory_measurable
                (policy := policy) (state := state)
                (defaultAction := defaultAction) (reward := reward)
                hreward source.hstate)
              hreward) i)
            omega) =
        RewardKernel.actionRewardHistoryStepKernelFamily rewardKernel policy
          (fun n history =>
            context n (History.pairHistoryRewardProjection history))
          (fun n history =>
            state n (History.pairHistoryRewardProjection history))
          (fun n : Nat =>
            (hcontext n).comp
              (History.measurable_pairHistoryRewardProjection
                (Action := Action) (Reward := Rat) n))
          (fun n : Nat =>
            (source.hstate n).comp
              (History.measurable_pairHistoryRewardProjection
                (Action := Action) (Reward := Rat) n))
          i
          (History.finitePairHistoryOfTrace
            (ConditionalExpectationReward.generatedActionFromRewardHistory
              policy state defaultAction reward omega)
            (reward omega) i))
      (MeasureTheory.ae
        (mu.trim
          ((History.historyFiltrationSucc
            (ConditionalExpectationReward.generatedActionFromRewardHistory
              policy state defaultAction reward)
            reward
            (ConditionalExpectationReward.generatedActionFromRewardHistory_measurable
              (policy := policy) (state := state)
              (defaultAction := defaultAction) (reward := reward)
              hreward source.hstate)
            hreward).le i))) := by
  exact
    ConditionalExpectationReward.actionRewardHistoryStepKernelFamily_pair_map_eq_historyFiltrationSucc_finitePairHistoryOfTrace_of_generatedActionRandomPairDefinitionalMapSource
      (mOmega := mOmega)
      mu rewardKernel policy context state hcontext defaultAction reward
      hreward source i

example {Omega Context State Action : Type}
    [mOmega : MeasurableSpace Omega] [StandardBorelSpace Omega]
    [MeasurableSpace Context] [MeasurableSpace State]
    [MeasurableSpace Action] [MeasurableSingletonClass Action]
    [Countable Action]
    (mu : MeasureTheory.Measure Omega) [MeasureTheory.IsFiniteMeasure mu]
    (rewardKernel : RewardKernel.MarkovRewardKernel (Prod Context Action) Rat)
    (policy : Nat -> Policy.MeasurablePolicy State Action)
    (context : (n : Nat) -> ((j : Finset.Iic n) -> Rat) -> Context)
    (state : (n : Nat) -> ((j : Finset.Iic n) -> Rat) -> State)
    (mean : Context -> Action -> Rat)
    (varianceProxy : Context -> Action -> NNReal)
    (defaultAction : Action)
    (reward : Omega -> RewardTrace Rat)
    (hreward : forall t : Nat,
      Measurable (fun omega : Omega => reward omega t))
    (source :
      ConditionalExpectationReward.GeneratedActionRandomPairDefinitionalCenteredSource
        mu rewardKernel policy context state mean varianceProxy defaultAction
        reward hreward)
    (i : Nat) :
    MeasureTheory.Integrable
      (fun omega : Omega =>
        (((reward omega (i + 1) -
          mean
            (context i
              (History.finiteRewardHistoryOfTrace (reward omega) i))
            ((policy i).action
              (state i
                (History.finiteRewardHistoryOfTrace (reward omega) i))) :
              Rat) : Real))) mu := by
  exact
    ConditionalExpectationReward.centeredReward_succ_integrable_of_generatedActionRandomPairDefinitionalCenteredSource
      (mOmega := mOmega)
      mu rewardKernel policy context state mean varianceProxy defaultAction
      reward hreward source i

example {Omega Context State Action : Type}
    [mOmega : MeasurableSpace Omega] [StandardBorelSpace Omega]
    [MeasurableSpace Context] [MeasurableSpace State]
    [MeasurableSpace Action] [MeasurableSingletonClass Action]
    [Countable Action]
    (mu : MeasureTheory.Measure Omega) [MeasureTheory.IsFiniteMeasure mu]
    (rewardKernel : RewardKernel.MarkovRewardKernel (Prod Context Action) Rat)
    (policy : Nat -> Policy.MeasurablePolicy State Action)
    (context : (n : Nat) -> ((j : Finset.Iic n) -> Rat) -> Context)
    (state : (n : Nat) -> ((j : Finset.Iic n) -> Rat) -> State)
    (mean : Context -> Action -> Rat)
    (varianceProxy : Context -> Action -> NNReal)
    (defaultAction : Action)
    (reward : Omega -> RewardTrace Rat)
    (hreward : forall t : Nat,
      Measurable (fun omega : Omega => reward omega t))
    (source :
      ConditionalExpectationReward.GeneratedActionRandomPairDefinitionalCenteredSource
        mu rewardKernel policy context state mean varianceProxy defaultAction
        reward hreward) :
    ConditionalExpectationReward.GeneratedActionRandomPairCenteredSource mu
      (ConditionalExpectationReward.generatedActionFromRewardHistory
        policy state defaultAction reward)
      rewardKernel policy context state mean varianceProxy defaultAction reward
      (ConditionalExpectationReward.generatedActionFromRewardHistory_measurable
        (policy := policy) (state := state) (defaultAction := defaultAction)
        (reward := reward) hreward source.definitional_map_source.hstate)
      hreward := by
  exact
    ConditionalExpectationReward.generatedActionRandomPairCenteredSource_of_definitionalCenteredSource
      (mOmega := mOmega)
      mu rewardKernel policy context state mean varianceProxy defaultAction
      reward hreward source

example {Omega Context State Action : Type}
    [mOmega : MeasurableSpace Omega] [StandardBorelSpace Omega]
    [MeasurableSpace Context] [MeasurableSpace State]
    [MeasurableSpace Action] [MeasurableSingletonClass Action]
    [Countable Action]
    (mu : MeasureTheory.Measure Omega) [MeasureTheory.IsFiniteMeasure mu]
    (rewardKernel : RewardKernel.MarkovRewardKernel (Prod Context Action) Rat)
    (policy : Nat -> Policy.MeasurablePolicy State Action)
    (context : (n : Nat) -> ((j : Finset.Iic n) -> Rat) -> Context)
    (state : (n : Nat) -> ((j : Finset.Iic n) -> Rat) -> State)
    (mean : Context -> Action -> Rat)
    (varianceProxy : Context -> Action -> NNReal)
    (defaultAction : Action)
    (reward : Omega -> RewardTrace Rat)
    (hreward : forall t : Nat,
      Measurable (fun omega : Omega => reward omega t))
    (source :
      ConditionalExpectationReward.GeneratedActionRandomPairDefinitionalCenteredSource
        mu rewardKernel policy context state mean varianceProxy defaultAction
        reward hreward) :
    ConditionalExpectationReward.GeneratedActionRandomPairMapSource mu
      (ConditionalExpectationReward.generatedActionFromRewardHistory
        policy state defaultAction reward)
      rewardKernel policy context state defaultAction reward
      (ConditionalExpectationReward.generatedActionFromRewardHistory_measurable
        (policy := policy) (state := state) (defaultAction := defaultAction)
        (reward := reward) hreward source.definitional_map_source.hstate)
      hreward := by
  exact
    ConditionalExpectationReward.generatedActionRandomPairMapSource_of_randomPairDefinitionalCenteredSource
      (mOmega := mOmega)
      mu rewardKernel policy context state mean varianceProxy defaultAction
      reward hreward source

example {Omega Context State Action : Type}
    [mOmega : MeasurableSpace Omega] [StandardBorelSpace Omega]
    [MeasurableSpace Context] [MeasurableSpace State]
    [MeasurableSpace Action] [MeasurableSingletonClass Action]
    [Countable Action]
    (mu : MeasureTheory.Measure Omega) [MeasureTheory.IsFiniteMeasure mu]
    (rewardKernel : RewardKernel.MarkovRewardKernel (Prod Context Action) Rat)
    (policy : Nat -> Policy.MeasurablePolicy State Action)
    (context : (n : Nat) -> ((j : Finset.Iic n) -> Rat) -> Context)
    (state : (n : Nat) -> ((j : Finset.Iic n) -> Rat) -> State)
    (mean : Context -> Action -> Rat)
    (varianceProxy : Context -> Action -> NNReal)
    (defaultAction : Action)
    (reward : Omega -> RewardTrace Rat)
    (hreward : forall t : Nat,
      Measurable (fun omega : Omega => reward omega t))
    (source :
      ConditionalExpectationReward.GeneratedActionRandomPairDefinitionalCenteredSource
        mu rewardKernel policy context state mean varianceProxy defaultAction
        reward hreward) :
    ConditionalExpectationReward.GeneratedActionDefinitionalActualRewardMapSource
      mu rewardKernel policy context state defaultAction reward hreward := by
  exact
    ConditionalExpectationReward.generatedActionDefinitionalActualRewardMapSource_of_randomPairDefinitionalCenteredSource
      (mOmega := mOmega)
      mu rewardKernel policy context state mean varianceProxy defaultAction
      reward hreward source

example {Omega Context State Action : Type}
    [mOmega : MeasurableSpace Omega] [StandardBorelSpace Omega]
    [MeasurableSpace Context] [MeasurableSpace State]
    [MeasurableSpace Action] [MeasurableSingletonClass Action]
    [Countable Action]
    (mu : MeasureTheory.Measure Omega) [MeasureTheory.IsFiniteMeasure mu]
    (rewardKernel : RewardKernel.MarkovRewardKernel (Prod Context Action) Rat)
    (policy : Nat -> Policy.MeasurablePolicy State Action)
    (context : (n : Nat) -> ((j : Finset.Iic n) -> Rat) -> Context)
    (state : (n : Nat) -> ((j : Finset.Iic n) -> Rat) -> State)
    (mean : Context -> Action -> Rat)
    (varianceProxy : Context -> Action -> NNReal)
    (defaultAction : Action)
    (reward : Omega -> RewardTrace Rat)
    (hreward : forall t : Nat,
      Measurable (fun omega : Omega => reward omega t))
    (source :
      ConditionalExpectationReward.GeneratedActionRandomPairDefinitionalCenteredSource
        mu rewardKernel policy context state mean varianceProxy defaultAction
        reward hreward) :
    ConditionalExpectationReward.GeneratedActionActualRewardMapSource mu
      (ConditionalExpectationReward.generatedActionFromRewardHistory
        policy state defaultAction reward)
      rewardKernel policy context state defaultAction reward
      (ConditionalExpectationReward.generatedActionFromRewardHistory_measurable
        (policy := policy) (state := state) (defaultAction := defaultAction)
        (reward := reward) hreward source.definitional_map_source.hstate)
      hreward := by
  exact
    ConditionalExpectationReward.generatedActionActualRewardMapSource_of_randomPairDefinitionalCenteredSource
      (mOmega := mOmega)
      mu rewardKernel policy context state mean varianceProxy defaultAction
      reward hreward source

example {Omega Context State Action : Type}
    [mOmega : MeasurableSpace Omega] [StandardBorelSpace Omega]
    [MeasurableSpace Context] [MeasurableSpace State]
    [MeasurableSpace Action] [MeasurableSingletonClass Action]
    [Countable Action]
    (mu : MeasureTheory.Measure Omega) [MeasureTheory.IsFiniteMeasure mu]
    (rewardKernel : RewardKernel.MarkovRewardKernel (Prod Context Action) Rat)
    (policy : Nat -> Policy.MeasurablePolicy State Action)
    (context : (n : Nat) -> ((j : Finset.Iic n) -> Rat) -> Context)
    (state : (n : Nat) -> ((j : Finset.Iic n) -> Rat) -> State)
    (mean : Context -> Action -> Rat)
    (varianceProxy : Context -> Action -> NNReal)
    (defaultAction : Action)
    (reward : Omega -> RewardTrace Rat)
    (hreward : forall t : Nat,
      Measurable (fun omega : Omega => reward omega t))
    (source :
      ConditionalExpectationReward.GeneratedActionRandomPairDefinitionalCenteredSource
        mu rewardKernel policy context state mean varianceProxy defaultAction
        reward hreward)
    (i : Nat) :
    Filter.Eventually
      (fun omega : Omega =>
        @MeasureTheory.Measure.map Omega (Prod Action Rat) mOmega inferInstance
          (fun y : Omega =>
            (ConditionalExpectationReward.generatedActionFromRewardHistory
              policy state defaultAction reward y (i + 1),
              reward y (i + 1)))
          (@ProbabilityTheory.condExpKernel Omega mOmega _ mu _
            ((History.historyFiltrationSucc
              (ConditionalExpectationReward.generatedActionFromRewardHistory
                policy state defaultAction reward)
              reward
              (ConditionalExpectationReward.generatedActionFromRewardHistory_measurable
                (policy := policy) (state := state)
                (defaultAction := defaultAction) (reward := reward)
                hreward source.definitional_map_source.hstate)
              hreward) i)
            omega) =
        RewardKernel.actionRewardHistoryStepKernelFamily rewardKernel policy
          (fun n history =>
            context n (History.pairHistoryRewardProjection history))
          (fun n history =>
            state n (History.pairHistoryRewardProjection history))
          (fun n : Nat =>
            (source.hcontext n).comp
              (History.measurable_pairHistoryRewardProjection
                (Action := Action) (Reward := Rat) n))
          (fun n : Nat =>
            (source.definitional_map_source.hstate n).comp
              (History.measurable_pairHistoryRewardProjection
                (Action := Action) (Reward := Rat) n))
          i
          (History.finitePairHistoryOfTrace
            (ConditionalExpectationReward.generatedActionFromRewardHistory
              policy state defaultAction reward omega)
            (reward omega) i))
      (MeasureTheory.ae
        (mu.trim
          ((History.historyFiltrationSucc
            (ConditionalExpectationReward.generatedActionFromRewardHistory
              policy state defaultAction reward)
            reward
            (ConditionalExpectationReward.generatedActionFromRewardHistory_measurable
              (policy := policy) (state := state)
              (defaultAction := defaultAction) (reward := reward)
              hreward source.definitional_map_source.hstate)
            hreward).le i))) := by
  exact
    ConditionalExpectationReward.actionRewardHistoryStepKernelFamily_pair_map_eq_historyFiltrationSucc_finitePairHistoryOfTrace_of_generatedActionRandomPairDefinitionalCenteredSource
      (mOmega := mOmega)
      mu rewardKernel policy context state mean varianceProxy defaultAction
      reward hreward source i

example {Omega Context State Action : Type}
    [mOmega : MeasurableSpace Omega] [StandardBorelSpace Omega]
    [MeasurableSpace Context] [MeasurableSpace State]
    [MeasurableSpace Action] [MeasurableSingletonClass Action]
    [Countable Action]
    (mu : MeasureTheory.Measure Omega) [MeasureTheory.IsFiniteMeasure mu]
    (rewardKernel : RewardKernel.MarkovRewardKernel (Prod Context Action) Rat)
    (policy : Nat -> Policy.MeasurablePolicy State Action)
    (context : (n : Nat) -> ((j : Finset.Iic n) -> Rat) -> Context)
    (state : (n : Nat) -> ((j : Finset.Iic n) -> Rat) -> State)
    (mean : Context -> Action -> Rat)
    (varianceProxy : Context -> Action -> NNReal)
    (defaultAction : Action)
    (reward : Omega -> RewardTrace Rat)
    (hreward : forall t : Nat,
      Measurable (fun omega : Omega => reward omega t))
    (source :
      ConditionalExpectationReward.GeneratedActionRandomPairDefinitionalCenteredSource
        mu rewardKernel policy context state mean varianceProxy defaultAction
        reward hreward)
    (i : Nat) :
    Filter.Eventually
      (fun omega : Omega =>
        @MeasureTheory.Measure.map Omega ((j : Finset.Iic (i + 1)) -> Prod Action Rat)
          mOmega inferInstance
          (fun y : Omega =>
            History.finitePairHistoryOfTrace
              (ConditionalExpectationReward.generatedActionFromRewardHistory
                policy state defaultAction reward y)
              (reward y) (i + 1))
          (@ProbabilityTheory.condExpKernel Omega mOmega _ mu _
            ((History.historyFiltrationSucc
              (ConditionalExpectationReward.generatedActionFromRewardHistory
                policy state defaultAction reward)
              reward
              (ConditionalExpectationReward.generatedActionFromRewardHistory_measurable
                (policy := policy) (state := state)
                (defaultAction := defaultAction) (reward := reward)
                hreward source.definitional_map_source.hstate)
              hreward) i)
            omega) =
        RewardKernel.actionRewardPartialTrajectoryKernel rewardKernel policy
          (fun n history =>
            context n (History.pairHistoryRewardProjection history))
          (fun n history =>
            state n (History.pairHistoryRewardProjection history))
          (fun n : Nat =>
            (source.hcontext n).comp
              (History.measurable_pairHistoryRewardProjection
                (Action := Action) (Reward := Rat) n))
          (fun n : Nat =>
            (source.definitional_map_source.hstate n).comp
              (History.measurable_pairHistoryRewardProjection
                (Action := Action) (Reward := Rat) n))
          i (i + 1)
          (History.finitePairHistoryOfTrace
            (ConditionalExpectationReward.generatedActionFromRewardHistory
              policy state defaultAction reward omega)
            (reward omega) i))
      (MeasureTheory.ae
        (mu.trim
          ((History.historyFiltrationSucc
            (ConditionalExpectationReward.generatedActionFromRewardHistory
              policy state defaultAction reward)
            reward
            (ConditionalExpectationReward.generatedActionFromRewardHistory_measurable
              (policy := policy) (state := state)
              (defaultAction := defaultAction) (reward := reward)
              hreward source.definitional_map_source.hstate)
            hreward).le i))) := by
  exact
    ConditionalExpectationReward.actionRewardPartialTrajectoryKernel_map_eq_historyFiltrationSucc_finitePairHistoryOfTrace_of_generatedActionRandomPairDefinitionalCenteredSource
      (mOmega := mOmega)
      mu rewardKernel policy context state mean varianceProxy defaultAction
      reward hreward source i

example {Omega Context State Action : Type}
    [mOmega : MeasurableSpace Omega] [StandardBorelSpace Omega]
    [MeasurableSpace Context] [MeasurableSpace State]
    [MeasurableSpace Action] [MeasurableSingletonClass Action]
    [Countable Action]
    (mu : MeasureTheory.Measure Omega) [MeasureTheory.IsFiniteMeasure mu]
    (rewardKernel : RewardKernel.MarkovRewardKernel (Prod Context Action) Rat)
    (policy : Nat -> Policy.MeasurablePolicy State Action)
    (context : (n : Nat) -> ((j : Finset.Iic n) -> Rat) -> Context)
    (state : (n : Nat) -> ((j : Finset.Iic n) -> Rat) -> State)
    (mean : Context -> Action -> Rat)
    (varianceProxy : Context -> Action -> NNReal)
    (defaultAction : Action)
    (reward : Omega -> RewardTrace Rat)
    (hreward : forall t : Nat,
      Measurable (fun omega : Omega => reward omega t))
    (source :
      ConditionalExpectationReward.GeneratedActionRandomPairDefinitionalCenteredSource
        mu rewardKernel policy context state mean varianceProxy defaultAction
        reward hreward)
    (i : Nat) :
    Filter.EventuallyEq (MeasureTheory.ae mu)
      (@MeasureTheory.condExp Omega Real
        ((History.historyFiltrationSucc
          (ConditionalExpectationReward.generatedActionFromRewardHistory
            policy state defaultAction reward)
          reward
          (ConditionalExpectationReward.generatedActionFromRewardHistory_measurable
            (policy := policy) (state := state) (defaultAction := defaultAction)
            (reward := reward) hreward source.definitional_map_source.hstate)
          hreward) i)
        mOmega _ _ _ mu
        (fun omega : Omega =>
          (((reward omega (i + 1) -
            mean
              (context i
                (History.finiteRewardHistoryOfTrace (reward omega) i))
              ((policy i).action
                (state i
                  (History.finiteRewardHistoryOfTrace (reward omega) i))) :
                Rat) : Real))))
      (fun _omega : Omega => (0 : Real)) := by
  exact
    ConditionalExpectationReward.centeredReward_succ_condExp_eq_zero_of_generatedActionRandomPairDefinitionalCenteredSource
      (mOmega := mOmega)
      mu rewardKernel policy context state mean varianceProxy defaultAction
      reward hreward source i

example {Omega Context State Action : Type}
    [mOmega : MeasurableSpace Omega] [StandardBorelSpace Omega]
    [MeasurableSpace Context] [MeasurableSpace State]
    [MeasurableSpace Action] [MeasurableSingletonClass Action]
    [Countable Action]
    (mu : MeasureTheory.Measure Omega) [MeasureTheory.IsFiniteMeasure mu]
    (rewardKernel : RewardKernel.MarkovRewardKernel (Prod Context Action) Rat)
    (policy : Nat -> Policy.MeasurablePolicy State Action)
    (context : (n : Nat) -> ((j : Finset.Iic n) -> Rat) -> Context)
    (state : (n : Nat) -> ((j : Finset.Iic n) -> Rat) -> State)
    (mean : Context -> Action -> Rat)
    (varianceProxy : Context -> Action -> NNReal)
    (defaultAction : Action)
    (reward : Omega -> RewardTrace Rat)
    (hreward : forall t : Nat,
      Measurable (fun omega : Omega => reward omega t))
    (source :
      ConditionalExpectationReward.GeneratedActionRandomPairDefinitionalCenteredSource
        mu rewardKernel policy context state mean varianceProxy defaultAction
        reward hreward)
    (i : Nat)
    (c : NNReal)
    (h_centered_meas :
      @Measurable Omega Real mOmega inferInstance
        (fun omega : Omega =>
          (((reward omega (i + 1) -
            mean
              (context i
                (History.finiteRewardHistoryOfTrace (reward omega) i))
              ((policy i).action
                (state i
                  (History.finiteRewardHistoryOfTrace (reward omega) i))) :
                Rat) : Real))))
    (h_integrable_exp :
      forall t : Real,
        MeasureTheory.Integrable
          (fun omega : Omega =>
            Real.exp (t *
              (((reward omega (i + 1) -
                mean
                  (context i
                    (History.finiteRewardHistoryOfTrace (reward omega) i))
                  ((policy i).action
                    (state i
                      (History.finiteRewardHistoryOfTrace (reward omega) i))) :
                    Rat) : Real)))) mu)
    (h_variance_le :
      Filter.Eventually
        (fun omega : Omega =>
          varianceProxy
              (context i
                (History.finiteRewardHistoryOfTrace (reward omega) i))
              ((policy i).action
                (state i
                  (History.finiteRewardHistoryOfTrace (reward omega) i))) <=
            c)
        (MeasureTheory.ae
          (mu.trim
            ((History.historyFiltrationSucc
              (ConditionalExpectationReward.generatedActionFromRewardHistory
                policy state defaultAction reward)
              reward
              (ConditionalExpectationReward.generatedActionFromRewardHistory_measurable
                (policy := policy) (state := state)
                (defaultAction := defaultAction) (reward := reward)
                hreward source.definitional_map_source.hstate)
              hreward).le i)))) :
    ProbabilityTheory.HasCondSubgaussianMGF
      ((History.historyFiltrationSucc
        (ConditionalExpectationReward.generatedActionFromRewardHistory
          policy state defaultAction reward)
        reward
        (ConditionalExpectationReward.generatedActionFromRewardHistory_measurable
          (policy := policy) (state := state) (defaultAction := defaultAction)
          (reward := reward) hreward source.definitional_map_source.hstate)
        hreward) i)
      ((History.historyFiltrationSucc
        (ConditionalExpectationReward.generatedActionFromRewardHistory
          policy state defaultAction reward)
        reward
        (ConditionalExpectationReward.generatedActionFromRewardHistory_measurable
          (policy := policy) (state := state) (defaultAction := defaultAction)
          (reward := reward) hreward source.definitional_map_source.hstate)
        hreward).le i)
      (fun omega : Omega =>
        (((reward omega (i + 1) -
          mean
            (context i
              (History.finiteRewardHistoryOfTrace (reward omega) i))
            ((policy i).action
              (state i
                (History.finiteRewardHistoryOfTrace (reward omega) i))) :
            Rat) : Real)))
      c mu := by
  exact
    ConditionalExpectationReward.centeredReward_succ_hasCondSubgaussianMGF_of_generatedActionRandomPairDefinitionalCenteredSource
      (mOmega := mOmega)
      mu rewardKernel policy context state mean varianceProxy defaultAction
      reward hreward source i c h_centered_meas h_integrable_exp
      h_variance_le

example {Omega Context State Action : Type}
    [mOmega : MeasurableSpace Omega] [StandardBorelSpace Omega]
    [MeasurableSpace Context] [MeasurableSpace State]
    [MeasurableSpace Action] [MeasurableSingletonClass Action]
    [Countable Action]
    (mu : MeasureTheory.Measure Omega) [MeasureTheory.IsFiniteMeasure mu]
    (rewardKernel : RewardKernel.MarkovRewardKernel (Prod Context Action) Rat)
    (policy : Nat -> Policy.MeasurablePolicy State Action)
    (context : (n : Nat) -> ((j : Finset.Iic n) -> Rat) -> Context)
    (state : (n : Nat) -> ((j : Finset.Iic n) -> Rat) -> State)
    (hcontext : forall n : Nat, Measurable (context n))
    (defaultAction : Action)
    (reward : Omega -> RewardTrace Rat)
    (hreward : forall t : Nat,
      Measurable (fun omega : Omega => reward omega t))
    (source :
      ConditionalExpectationReward.GeneratedActionRandomPairDefinitionalMapSource
        mu rewardKernel policy context state defaultAction reward hreward)
    (i : Nat) :
    Filter.Eventually
      (fun omega : Omega =>
        @MeasureTheory.Measure.map Omega ((j : Finset.Iic (i + 1)) -> Prod Action Rat)
          mOmega inferInstance
          (fun y : Omega =>
            History.finitePairHistoryOfTrace
              (ConditionalExpectationReward.generatedActionFromRewardHistory
                policy state defaultAction reward y)
              (reward y) (i + 1))
          (@ProbabilityTheory.condExpKernel Omega mOmega _ mu _
            ((History.historyFiltrationSucc
              (ConditionalExpectationReward.generatedActionFromRewardHistory
                policy state defaultAction reward)
              reward
              (ConditionalExpectationReward.generatedActionFromRewardHistory_measurable
                (policy := policy) (state := state)
                (defaultAction := defaultAction) (reward := reward)
                hreward source.hstate)
              hreward) i)
            omega) =
        RewardKernel.actionRewardPartialTrajectoryKernel rewardKernel policy
          (fun n history =>
            context n (History.pairHistoryRewardProjection history))
          (fun n history =>
            state n (History.pairHistoryRewardProjection history))
          (fun n : Nat =>
            (hcontext n).comp
              (History.measurable_pairHistoryRewardProjection
                (Action := Action) (Reward := Rat) n))
          (fun n : Nat =>
            (source.hstate n).comp
              (History.measurable_pairHistoryRewardProjection
                (Action := Action) (Reward := Rat) n))
          i (i + 1)
          (History.finitePairHistoryOfTrace
            (ConditionalExpectationReward.generatedActionFromRewardHistory
              policy state defaultAction reward omega)
            (reward omega) i))
      (MeasureTheory.ae
        (mu.trim
          ((History.historyFiltrationSucc
            (ConditionalExpectationReward.generatedActionFromRewardHistory
              policy state defaultAction reward)
            reward
            (ConditionalExpectationReward.generatedActionFromRewardHistory_measurable
              (policy := policy) (state := state)
              (defaultAction := defaultAction) (reward := reward)
              hreward source.hstate)
            hreward).le i))) := by
  exact
    ConditionalExpectationReward.actionRewardPartialTrajectoryKernel_map_eq_historyFiltrationSucc_finitePairHistoryOfTrace_of_generatedActionRandomPairDefinitionalMapSource
      (mOmega := mOmega)
      mu rewardKernel policy context state hcontext defaultAction reward
      hreward source i

example {Omega Context State Action : Type}
    [mOmega : MeasurableSpace Omega] [StandardBorelSpace Omega]
    [MeasurableSpace Context] [MeasurableSpace State]
    [MeasurableSpace Action] [MeasurableSingletonClass Action]
    [Countable Action]
    (mu : MeasureTheory.Measure Omega) [MeasureTheory.IsFiniteMeasure mu]
    (rewardKernel : RewardKernel.MarkovRewardKernel (Prod Context Action) Rat)
    (policy : Nat -> Policy.MeasurablePolicy State Action)
    (context : (n : Nat) -> ((j : Finset.Iic n) -> Rat) -> Context)
    (state : (n : Nat) -> ((j : Finset.Iic n) -> Rat) -> State)
    (hcontext : forall n : Nat, Measurable (context n))
    (mean : Context -> Action -> Rat)
    (varianceProxy : Context -> Action -> NNReal)
    (law :
      RewardKernel.CenteredRewardKernelLaw rewardKernel mean varianceProxy)
    (defaultAction : Action)
    (reward : Omega -> RewardTrace Rat)
    (hreward : forall t : Nat,
      Measurable (fun omega : Omega => reward omega t))
    (source :
      ConditionalExpectationReward.GeneratedActionRandomPairDefinitionalMapSource
        mu rewardKernel policy context state defaultAction reward hreward)
    (i : Nat)
    (h_integrable :
      MeasureTheory.Integrable
        (fun omega : Omega =>
          (((reward omega (i + 1) -
            mean
              (context i
                (History.finiteRewardHistoryOfTrace (reward omega) i))
              ((policy i).action
                (state i
                  (History.finiteRewardHistoryOfTrace (reward omega) i))) :
                Rat) : Real))) mu) :
    Filter.EventuallyEq (MeasureTheory.ae mu)
      (@MeasureTheory.condExp Omega Real
        ((History.historyFiltrationSucc
          (ConditionalExpectationReward.generatedActionFromRewardHistory
            policy state defaultAction reward)
          reward
          (ConditionalExpectationReward.generatedActionFromRewardHistory_measurable
            (policy := policy) (state := state) (defaultAction := defaultAction)
            (reward := reward) hreward source.hstate)
          hreward) i)
        mOmega _ _ _ mu
        (fun omega : Omega =>
          (((reward omega (i + 1) -
            mean
              (context i
                (History.finiteRewardHistoryOfTrace (reward omega) i))
              ((policy i).action
                (state i
                  (History.finiteRewardHistoryOfTrace (reward omega) i))) :
                Rat) : Real))))
      (fun _omega : Omega => (0 : Real)) := by
  exact
    ConditionalExpectationReward.centeredReward_succ_condExp_eq_zero_of_generatedActionRandomPairDefinitionalMapSource
      (mOmega := mOmega)
      mu rewardKernel policy context state hcontext mean varianceProxy law
      defaultAction reward hreward source i h_integrable

example {Omega Context State Action : Type}
    [mOmega : MeasurableSpace Omega] [StandardBorelSpace Omega]
    [MeasurableSpace Context] [MeasurableSpace State]
    [MeasurableSpace Action] [MeasurableSingletonClass Action]
    [Countable Action]
    (mu : MeasureTheory.Measure Omega) [MeasureTheory.IsFiniteMeasure mu]
    (rewardKernel : RewardKernel.MarkovRewardKernel (Prod Context Action) Rat)
    (policy : Nat -> Policy.MeasurablePolicy State Action)
    (context : (n : Nat) -> ((j : Finset.Iic n) -> Rat) -> Context)
    (state : (n : Nat) -> ((j : Finset.Iic n) -> Rat) -> State)
    (hcontext : forall n : Nat, Measurable (context n))
    (mean : Context -> Action -> Rat)
    (varianceProxy : Context -> Action -> NNReal)
    (hmean :
      Measurable (fun pair : Prod Context Action => mean pair.1 pair.2))
    (law :
      RewardKernel.CenteredRewardKernelLaw rewardKernel mean varianceProxy)
    (defaultAction : Action)
    (reward : Omega -> RewardTrace Rat)
    (hreward : forall t : Nat,
      Measurable (fun omega : Omega => reward omega t))
    (rewardLo rewardHi meanLo meanHi : Nat -> Real)
    (hraw :
      forall i : Nat, forall omega : Omega,
        Set.Icc (rewardLo i) (rewardHi i)
          (((reward omega (i + 1) : Rat) : Real)))
    (hmean_range :
      forall i : Nat, forall context : Context, forall action : Action,
        Set.Icc (meanLo i) (meanHi i)
          (((mean context action : Rat) : Real)))
    (source :
      ConditionalExpectationReward.GeneratedActionRandomPairDefinitionalMapSource
        mu rewardKernel policy context state defaultAction reward hreward)
    (i : Nat) :
    Filter.EventuallyEq (MeasureTheory.ae mu)
      (@MeasureTheory.condExp Omega Real
        ((History.historyFiltrationSucc
          (ConditionalExpectationReward.generatedActionFromRewardHistory
            policy state defaultAction reward)
          reward
          (ConditionalExpectationReward.generatedActionFromRewardHistory_measurable
            (policy := policy) (state := state) (defaultAction := defaultAction)
            (reward := reward) hreward source.hstate)
          hreward) i)
        mOmega _ _ _ mu
        (fun omega : Omega =>
          (((reward omega (i + 1) -
            mean
              (context i
                (History.finiteRewardHistoryOfTrace (reward omega) i))
              ((policy i).action
                (state i
                  (History.finiteRewardHistoryOfTrace (reward omega) i))) :
                Rat) : Real))))
      (fun _omega : Omega => (0 : Real)) := by
  exact
    ConditionalExpectationReward.centeredReward_succ_condExp_eq_zero_of_generatedActionRandomPairDefinitionalMapSource_rawRangeMeasurableMeanRangeBounded
      (mOmega := mOmega)
      mu rewardKernel policy context state hcontext mean varianceProxy hmean
      law defaultAction reward hreward rewardLo rewardHi meanLo meanHi hraw
      hmean_range source i

example {Omega Context State Action : Type}
    [mOmega : MeasurableSpace Omega] [StandardBorelSpace Omega]
    [MeasurableSpace Context] [MeasurableSpace State]
    [MeasurableSpace Action] [MeasurableSingletonClass Action]
    [Countable Action]
    (mu : MeasureTheory.Measure Omega) [MeasureTheory.IsFiniteMeasure mu]
    (rewardKernel : RewardKernel.MarkovRewardKernel (Prod Context Action) Rat)
    (policy : Nat -> Policy.MeasurablePolicy State Action)
    (context : (n : Nat) -> ((j : Finset.Iic n) -> Rat) -> Context)
    (state : (n : Nat) -> ((j : Finset.Iic n) -> Rat) -> State)
    (mean : Context -> Action -> Rat)
    (varianceProxy : Context -> Action -> NNReal)
    (defaultAction : Action)
    (reward : Omega -> RewardTrace Rat)
    (hreward : forall t : Nat,
      Measurable (fun omega : Omega => reward omega t))
    (rewardLo rewardHi meanLo meanHi : Nat -> Real)
    (source :
      ConditionalExpectationReward.GeneratedActionRandomPairDefinitionalRawRangeMeasurableMeanRangeBoundedSource
        mu rewardKernel policy context state mean varianceProxy defaultAction
        reward hreward rewardLo rewardHi meanLo meanHi) :
    ConditionalExpectationReward.GeneratedActionRandomPairRawRangeMeasurableMeanRangeBoundedSource
      mu
      (ConditionalExpectationReward.generatedActionFromRewardHistory
        policy state defaultAction reward)
      rewardKernel policy context state mean varianceProxy defaultAction reward
      (ConditionalExpectationReward.generatedActionFromRewardHistory_measurable
        (policy := policy) (state := state) (defaultAction := defaultAction)
        (reward := reward) hreward source.definitional_map_source.hstate)
      hreward rewardLo rewardHi meanLo meanHi := by
  exact
    ConditionalExpectationReward.generatedActionRandomPairRawRangeMeasurableMeanRangeBoundedSource_of_definitionalRawRangeMeasurableMeanRangeBoundedSource
      (mOmega := mOmega)
      mu rewardKernel policy context state mean varianceProxy defaultAction
      reward hreward rewardLo rewardHi meanLo meanHi source

example {Omega Context State Action : Type}
    [mOmega : MeasurableSpace Omega] [StandardBorelSpace Omega]
    [MeasurableSpace Context] [MeasurableSpace State]
    [MeasurableSpace Action] [MeasurableSingletonClass Action]
    [Countable Action]
    (mu : MeasureTheory.Measure Omega) [MeasureTheory.IsFiniteMeasure mu]
    (rewardKernel : RewardKernel.MarkovRewardKernel (Prod Context Action) Rat)
    (policy : Nat -> Policy.MeasurablePolicy State Action)
    (context : (n : Nat) -> ((j : Finset.Iic n) -> Rat) -> Context)
    (state : (n : Nat) -> ((j : Finset.Iic n) -> Rat) -> State)
    (mean : Context -> Action -> Rat)
    (varianceProxy : Context -> Action -> NNReal)
    (defaultAction : Action)
    (reward : Omega -> RewardTrace Rat)
    (hreward : forall t : Nat,
      Measurable (fun omega : Omega => reward omega t))
    (rewardLo rewardHi meanLo meanHi : Nat -> Real)
    (source :
      ConditionalExpectationReward.GeneratedActionRandomPairDefinitionalRawRangeMeasurableMeanRangeBoundedSource
        mu rewardKernel policy context state mean varianceProxy defaultAction
        reward hreward rewardLo rewardHi meanLo meanHi)
    (i : Nat) :
    Filter.Eventually
      (fun omega : Omega =>
        @MeasureTheory.Measure.map Omega (Prod Action Rat) mOmega inferInstance
          (fun y : Omega =>
            (ConditionalExpectationReward.generatedActionFromRewardHistory
              policy state defaultAction reward y (i + 1),
              reward y (i + 1)))
          (@ProbabilityTheory.condExpKernel Omega mOmega _ mu _
            ((History.historyFiltrationSucc
              (ConditionalExpectationReward.generatedActionFromRewardHistory
                policy state defaultAction reward)
              reward
              (ConditionalExpectationReward.generatedActionFromRewardHistory_measurable
                (policy := policy) (state := state)
                (defaultAction := defaultAction) (reward := reward)
                hreward source.definitional_map_source.hstate)
              hreward) i)
            omega) =
        RewardKernel.actionRewardHistoryStepKernelFamily rewardKernel policy
          (fun n history =>
            context n (History.pairHistoryRewardProjection history))
          (fun n history =>
            state n (History.pairHistoryRewardProjection history))
          (fun n : Nat =>
            (source.hcontext n).comp
              (History.measurable_pairHistoryRewardProjection
                (Action := Action) (Reward := Rat) n))
          (fun n : Nat =>
            (source.definitional_map_source.hstate n).comp
              (History.measurable_pairHistoryRewardProjection
                (Action := Action) (Reward := Rat) n))
          i
          (History.finitePairHistoryOfTrace
            (ConditionalExpectationReward.generatedActionFromRewardHistory
              policy state defaultAction reward omega)
            (reward omega) i))
      (MeasureTheory.ae
        (mu.trim
          ((History.historyFiltrationSucc
            (ConditionalExpectationReward.generatedActionFromRewardHistory
              policy state defaultAction reward)
            reward
            (ConditionalExpectationReward.generatedActionFromRewardHistory_measurable
              (policy := policy) (state := state)
              (defaultAction := defaultAction) (reward := reward)
              hreward source.definitional_map_source.hstate)
            hreward).le i))) := by
  exact
    ConditionalExpectationReward.actionRewardHistoryStepKernelFamily_pair_map_eq_historyFiltrationSucc_finitePairHistoryOfTrace_of_generatedActionRandomPairDefinitionalRawRangeMeasurableMeanRangeBoundedSource
      (mOmega := mOmega)
      mu rewardKernel policy context state mean varianceProxy defaultAction
      reward hreward rewardLo rewardHi meanLo meanHi source i

example {Omega Context State Action : Type}
    [mOmega : MeasurableSpace Omega] [StandardBorelSpace Omega]
    [MeasurableSpace Context] [MeasurableSpace State]
    [MeasurableSpace Action] [MeasurableSingletonClass Action]
    [Countable Action]
    (mu : MeasureTheory.Measure Omega) [MeasureTheory.IsFiniteMeasure mu]
    (rewardKernel : RewardKernel.MarkovRewardKernel (Prod Context Action) Rat)
    (policy : Nat -> Policy.MeasurablePolicy State Action)
    (context : (n : Nat) -> ((j : Finset.Iic n) -> Rat) -> Context)
    (state : (n : Nat) -> ((j : Finset.Iic n) -> Rat) -> State)
    (mean : Context -> Action -> Rat)
    (varianceProxy : Context -> Action -> NNReal)
    (defaultAction : Action)
    (reward : Omega -> RewardTrace Rat)
    (hreward : forall t : Nat, Measurable (fun omega : Omega => reward omega t))
    (rewardLo rewardHi meanLo meanHi : Nat -> Real)
    (source :
      ConditionalExpectationReward.GeneratedActionRandomPairDefinitionalRawRangeMeasurableMeanRangeBoundedSource
        mu rewardKernel policy context state mean varianceProxy defaultAction
        reward hreward rewardLo rewardHi meanLo meanHi)
    (i : Nat) :
    Filter.Eventually
      (fun omega : Omega =>
        @MeasureTheory.Measure.map Omega ((j : Finset.Iic (i + 1)) -> Prod Action Rat)
          mOmega inferInstance
          (fun y : Omega =>
            History.finitePairHistoryOfTrace
              (ConditionalExpectationReward.generatedActionFromRewardHistory
                policy state defaultAction reward y)
              (reward y) (i + 1))
          (@ProbabilityTheory.condExpKernel Omega mOmega _ mu _
            ((History.historyFiltrationSucc
              (ConditionalExpectationReward.generatedActionFromRewardHistory
                policy state defaultAction reward)
              reward
              (ConditionalExpectationReward.generatedActionFromRewardHistory_measurable
                (policy := policy) (state := state)
                (defaultAction := defaultAction) (reward := reward)
                hreward source.definitional_map_source.hstate)
              hreward) i)
            omega) =
        RewardKernel.actionRewardPartialTrajectoryKernel rewardKernel policy
          (fun n history => context n (History.pairHistoryRewardProjection history))
          (fun n history => state n (History.pairHistoryRewardProjection history))
          (fun n : Nat =>
            (source.hcontext n).comp
              (History.measurable_pairHistoryRewardProjection
                (Action := Action) (Reward := Rat) n))
          (fun n : Nat =>
            (source.definitional_map_source.hstate n).comp
              (History.measurable_pairHistoryRewardProjection
                (Action := Action) (Reward := Rat) n))
          i (i + 1)
          (History.finitePairHistoryOfTrace
            (ConditionalExpectationReward.generatedActionFromRewardHistory
              policy state defaultAction reward omega)
            (reward omega) i))
      (MeasureTheory.ae
        (mu.trim
          ((History.historyFiltrationSucc
            (ConditionalExpectationReward.generatedActionFromRewardHistory
              policy state defaultAction reward)
            reward
            (ConditionalExpectationReward.generatedActionFromRewardHistory_measurable
              (policy := policy) (state := state)
              (defaultAction := defaultAction) (reward := reward)
              hreward source.definitional_map_source.hstate)
            hreward).le i))) := by
  exact
    ConditionalExpectationReward.actionRewardPartialTrajectoryKernel_map_eq_historyFiltrationSucc_finitePairHistoryOfTrace_of_generatedActionRandomPairDefinitionalRawRangeMeasurableMeanRangeBoundedSource
      (mOmega := mOmega)
      mu rewardKernel policy context state mean varianceProxy defaultAction
      reward hreward rewardLo rewardHi meanLo meanHi source i

example {Omega Context State Action : Type}
    [mOmega : MeasurableSpace Omega] [StandardBorelSpace Omega]
    [MeasurableSpace Context] [MeasurableSpace State]
    [MeasurableSpace Action] [MeasurableSingletonClass Action]
    [Countable Action]
    (mu : MeasureTheory.Measure Omega) [MeasureTheory.IsFiniteMeasure mu]
    (rewardKernel : RewardKernel.MarkovRewardKernel (Prod Context Action) Rat)
    (policy : Nat -> Policy.MeasurablePolicy State Action)
    (context : (n : Nat) -> ((j : Finset.Iic n) -> Rat) -> Context)
    (state : (n : Nat) -> ((j : Finset.Iic n) -> Rat) -> State)
    (mean : Context -> Action -> Rat)
    (varianceProxy : Context -> Action -> NNReal)
    (defaultAction : Action)
    (reward : Omega -> RewardTrace Rat)
    (hreward : forall t : Nat,
      Measurable (fun omega : Omega => reward omega t))
    (rewardLo rewardHi meanLo meanHi : Nat -> Real)
    (source :
      ConditionalExpectationReward.GeneratedActionRandomPairDefinitionalRawRangeMeasurableMeanRangeBoundedSource
        mu rewardKernel policy context state mean varianceProxy defaultAction
        reward hreward rewardLo rewardHi meanLo meanHi) :
    ConditionalExpectationReward.GeneratedActionRandomPairMapSource mu
      (ConditionalExpectationReward.generatedActionFromRewardHistory
        policy state defaultAction reward)
      rewardKernel policy context state defaultAction reward
      (ConditionalExpectationReward.generatedActionFromRewardHistory_measurable
        (policy := policy) (state := state) (defaultAction := defaultAction)
        (reward := reward) hreward source.definitional_map_source.hstate)
      hreward := by
  exact
    ConditionalExpectationReward.generatedActionRandomPairMapSource_of_definitionalRawRangeMeasurableMeanRangeBoundedSource
      (mOmega := mOmega)
      mu rewardKernel policy context state mean varianceProxy defaultAction
      reward hreward rewardLo rewardHi meanLo meanHi source

example {Omega Context State Action : Type}
    [mOmega : MeasurableSpace Omega] [StandardBorelSpace Omega]
    [MeasurableSpace Context] [MeasurableSpace State]
    [MeasurableSpace Action] [MeasurableSingletonClass Action]
    [Countable Action]
    (mu : MeasureTheory.Measure Omega) [MeasureTheory.IsFiniteMeasure mu]
    (rewardKernel : RewardKernel.MarkovRewardKernel (Prod Context Action) Rat)
    (policy : Nat -> Policy.MeasurablePolicy State Action)
    (context : (n : Nat) -> ((j : Finset.Iic n) -> Rat) -> Context)
    (state : (n : Nat) -> ((j : Finset.Iic n) -> Rat) -> State)
    (mean : Context -> Action -> Rat)
    (varianceProxy : Context -> Action -> NNReal)
    (defaultAction : Action)
    (reward : Omega -> RewardTrace Rat)
    (hreward : forall t : Nat,
      Measurable (fun omega : Omega => reward omega t))
    (rewardLo rewardHi meanLo meanHi : Nat -> Real)
    (source :
      ConditionalExpectationReward.GeneratedActionRandomPairDefinitionalRawRangeMeasurableMeanRangeBoundedSource
        mu rewardKernel policy context state mean varianceProxy defaultAction
        reward hreward rewardLo rewardHi meanLo meanHi) :
    ConditionalExpectationReward.GeneratedActionRandomPairDefinitionalCenteredSource
      mu rewardKernel policy context state mean varianceProxy defaultAction
      reward hreward := by
  exact
    ConditionalExpectationReward.generatedActionRandomPairDefinitionalCenteredSource_of_definitionalRawRangeMeasurableMeanRangeBoundedSource
      (mOmega := mOmega)
      mu rewardKernel policy context state mean varianceProxy defaultAction
      reward hreward rewardLo rewardHi meanLo meanHi source

example {Omega Context State Action : Type}
    [mOmega : MeasurableSpace Omega] [StandardBorelSpace Omega]
    [MeasurableSpace Context] [MeasurableSpace State]
    [MeasurableSpace Action] [MeasurableSingletonClass Action]
    [Countable Action]
    (mu : MeasureTheory.Measure Omega) [MeasureTheory.IsFiniteMeasure mu]
    (rewardKernel : RewardKernel.MarkovRewardKernel (Prod Context Action) Rat)
    (policy : Nat -> Policy.MeasurablePolicy State Action)
    (context : (n : Nat) -> ((j : Finset.Iic n) -> Rat) -> Context)
    (state : (n : Nat) -> ((j : Finset.Iic n) -> Rat) -> State)
    (mean : Context -> Action -> Rat)
    (varianceProxy : Context -> Action -> NNReal)
    (defaultAction : Action)
    (reward : Omega -> RewardTrace Rat)
    (hreward : forall t : Nat,
      Measurable (fun omega : Omega => reward omega t))
    (rewardLo rewardHi meanLo meanHi : Nat -> Real)
    (source :
      ConditionalExpectationReward.GeneratedActionRandomPairDefinitionalRawRangeMeasurableMeanRangeBoundedSource
        mu rewardKernel policy context state mean varianceProxy defaultAction
        reward hreward rewardLo rewardHi meanLo meanHi) :
    ConditionalExpectationReward.GeneratedActionDefinitionalActualRewardMapSource
      mu rewardKernel policy context state defaultAction reward hreward := by
  exact
    ConditionalExpectationReward.generatedActionDefinitionalActualRewardMapSource_of_randomPairDefinitionalRawRangeMeasurableMeanRangeBoundedSource
      (mOmega := mOmega)
      mu rewardKernel policy context state mean varianceProxy defaultAction
      reward hreward rewardLo rewardHi meanLo meanHi source

example {Omega Context State Action : Type}
    [mOmega : MeasurableSpace Omega] [StandardBorelSpace Omega]
    [MeasurableSpace Context] [MeasurableSpace State]
    [MeasurableSpace Action] [MeasurableSingletonClass Action]
    [Countable Action]
    (mu : MeasureTheory.Measure Omega) [MeasureTheory.IsFiniteMeasure mu]
    (rewardKernel : RewardKernel.MarkovRewardKernel (Prod Context Action) Rat)
    (policy : Nat -> Policy.MeasurablePolicy State Action)
    (context : (n : Nat) -> ((j : Finset.Iic n) -> Rat) -> Context)
    (state : (n : Nat) -> ((j : Finset.Iic n) -> Rat) -> State)
    (mean : Context -> Action -> Rat)
    (varianceProxy : Context -> Action -> NNReal)
    (defaultAction : Action)
    (reward : Omega -> RewardTrace Rat)
    (hreward : forall t : Nat,
      Measurable (fun omega : Omega => reward omega t))
    (rewardLo rewardHi meanLo meanHi : Nat -> Real)
    (source :
      ConditionalExpectationReward.GeneratedActionRandomPairDefinitionalRawRangeMeasurableMeanRangeBoundedSource
        mu rewardKernel policy context state mean varianceProxy defaultAction
        reward hreward rewardLo rewardHi meanLo meanHi) :
    ConditionalExpectationReward.GeneratedActionActualRewardMapSource mu
      (ConditionalExpectationReward.generatedActionFromRewardHistory
        policy state defaultAction reward)
      rewardKernel policy context state defaultAction reward
      (ConditionalExpectationReward.generatedActionFromRewardHistory_measurable
        (policy := policy) (state := state) (defaultAction := defaultAction)
        (reward := reward) hreward source.definitional_map_source.hstate)
      hreward := by
  exact
    ConditionalExpectationReward.generatedActionActualRewardMapSource_of_randomPairDefinitionalRawRangeMeasurableMeanRangeBoundedSource
      (mOmega := mOmega)
      mu rewardKernel policy context state mean varianceProxy defaultAction
      reward hreward rewardLo rewardHi meanLo meanHi source

example {Omega Context State Action : Type}
    [mOmega : MeasurableSpace Omega] [StandardBorelSpace Omega]
    [MeasurableSpace Context] [MeasurableSpace State]
    [MeasurableSpace Action] [MeasurableSingletonClass Action]
    [Countable Action]
    (mu : MeasureTheory.Measure Omega) [MeasureTheory.IsFiniteMeasure mu]
    (rewardKernel : RewardKernel.MarkovRewardKernel (Prod Context Action) Rat)
    (policy : Nat -> Policy.MeasurablePolicy State Action)
    (context : (n : Nat) -> ((j : Finset.Iic n) -> Rat) -> Context)
    (state : (n : Nat) -> ((j : Finset.Iic n) -> Rat) -> State)
    (mean : Context -> Action -> Rat)
    (varianceProxy : Context -> Action -> NNReal)
    (defaultAction : Action)
    (reward : Omega -> RewardTrace Rat)
    (hreward : forall t : Nat,
      Measurable (fun omega : Omega => reward omega t))
    (rewardLo rewardHi meanLo meanHi : Nat -> Real)
    (source :
      ConditionalExpectationReward.GeneratedActionRandomPairDefinitionalRawRangeMeasurableMeanRangeBoundedSource
        mu rewardKernel policy context state mean varianceProxy defaultAction
        reward hreward rewardLo rewardHi meanLo meanHi)
    (i : Nat) :
    AEMeasurable
      (fun omega : Omega =>
        (((reward omega (i + 1) -
          mean
            (context i
              (History.finiteRewardHistoryOfTrace (reward omega) i))
            ((policy i).action
              (state i
                (History.finiteRewardHistoryOfTrace (reward omega) i))) :
            Rat) : Real))) mu := by
  exact
    ConditionalExpectationReward.centeredReward_succ_aemeasurable_of_generatedActionRandomPairDefinitionalRawRangeMeasurableMeanRangeBoundedSource
      (mOmega := mOmega)
      mu rewardKernel policy context state mean varianceProxy defaultAction
      reward hreward rewardLo rewardHi meanLo meanHi source i

example {Omega Context State Action : Type}
    [mOmega : MeasurableSpace Omega] [StandardBorelSpace Omega]
    [MeasurableSpace Context] [MeasurableSpace State]
    [MeasurableSpace Action] [MeasurableSingletonClass Action]
    [Countable Action]
    (mu : MeasureTheory.Measure Omega) [MeasureTheory.IsFiniteMeasure mu]
    (rewardKernel : RewardKernel.MarkovRewardKernel (Prod Context Action) Rat)
    (policy : Nat -> Policy.MeasurablePolicy State Action)
    (context : (n : Nat) -> ((j : Finset.Iic n) -> Rat) -> Context)
    (state : (n : Nat) -> ((j : Finset.Iic n) -> Rat) -> State)
    (mean : Context -> Action -> Rat)
    (varianceProxy : Context -> Action -> NNReal)
    (defaultAction : Action)
    (reward : Omega -> RewardTrace Rat)
    (hreward : forall t : Nat,
      Measurable (fun omega : Omega => reward omega t))
    (rewardLo rewardHi meanLo meanHi : Nat -> Real)
    (source :
      ConditionalExpectationReward.GeneratedActionRandomPairDefinitionalRawRangeMeasurableMeanRangeBoundedSource
        mu rewardKernel policy context state mean varianceProxy defaultAction
        reward hreward rewardLo rewardHi meanLo meanHi)
    (i : Nat) :
    Filter.Eventually
      (fun omega : Omega =>
        Set.Icc (rewardLo i - meanHi i) (rewardHi i - meanLo i)
          (((reward omega (i + 1) -
            mean
              (context i
                (History.finiteRewardHistoryOfTrace (reward omega) i))
              ((policy i).action
                (state i
                  (History.finiteRewardHistoryOfTrace (reward omega) i))) :
              Rat) : Real)))
      (MeasureTheory.ae mu) := by
  exact
    ConditionalExpectationReward.centeredReward_succ_bound_of_generatedActionRandomPairDefinitionalRawRangeMeasurableMeanRangeBoundedSource
      (mOmega := mOmega)
      mu rewardKernel policy context state mean varianceProxy defaultAction
      reward hreward rewardLo rewardHi meanLo meanHi source i

example {Omega Context State Action : Type}
    [mOmega : MeasurableSpace Omega] [StandardBorelSpace Omega]
    [MeasurableSpace Context] [MeasurableSpace State]
    [MeasurableSpace Action] [MeasurableSingletonClass Action]
    [Countable Action]
    (mu : MeasureTheory.Measure Omega) [MeasureTheory.IsFiniteMeasure mu]
    (rewardKernel : RewardKernel.MarkovRewardKernel (Prod Context Action) Rat)
    (policy : Nat -> Policy.MeasurablePolicy State Action)
    (context : (n : Nat) -> ((j : Finset.Iic n) -> Rat) -> Context)
    (state : (n : Nat) -> ((j : Finset.Iic n) -> Rat) -> State)
    (mean : Context -> Action -> Rat)
    (varianceProxy : Context -> Action -> NNReal)
    (defaultAction : Action)
    (reward : Omega -> RewardTrace Rat)
    (hreward : forall t : Nat, Measurable (fun omega : Omega => reward omega t))
    (rewardLo rewardHi meanLo meanHi : Nat -> Real)
    (source :
      ConditionalExpectationReward.GeneratedActionRandomPairDefinitionalRawRangeMeasurableMeanRangeBoundedSource
        mu rewardKernel policy context state mean varianceProxy defaultAction
        reward hreward rewardLo rewardHi meanLo meanHi)
    (i : Nat) :
    MeasureTheory.Integrable
      (fun omega : Omega =>
        (((reward omega (i + 1) -
          mean
            (context i
              (History.finiteRewardHistoryOfTrace (reward omega) i))
            ((policy i).action
              (state i
                (History.finiteRewardHistoryOfTrace (reward omega) i))) :
              Rat) : Real))) mu := by
  exact
    ConditionalExpectationReward.centeredReward_succ_integrable_of_generatedActionRandomPairDefinitionalRawRangeMeasurableMeanRangeBoundedSource
      (mOmega := mOmega)
      mu rewardKernel policy context state mean varianceProxy defaultAction
      reward hreward rewardLo rewardHi meanLo meanHi source i

example {Omega Context State Action : Type}
    [mOmega : MeasurableSpace Omega] [StandardBorelSpace Omega]
    [MeasurableSpace Context] [MeasurableSpace State]
    [MeasurableSpace Action] [MeasurableSingletonClass Action]
    [Countable Action]
    (mu : MeasureTheory.Measure Omega) [MeasureTheory.IsFiniteMeasure mu]
    (rewardKernel : RewardKernel.MarkovRewardKernel (Prod Context Action) Rat)
    (policy : Nat -> Policy.MeasurablePolicy State Action)
    (context : (n : Nat) -> ((j : Finset.Iic n) -> Rat) -> Context)
    (state : (n : Nat) -> ((j : Finset.Iic n) -> Rat) -> State)
    (mean : Context -> Action -> Rat)
    (varianceProxy : Context -> Action -> NNReal)
    (defaultAction : Action)
    (reward : Omega -> RewardTrace Rat)
    (hreward : forall t : Nat,
      Measurable (fun omega : Omega => reward omega t))
    (rewardLo rewardHi meanLo meanHi : Nat -> Real)
    (source :
      ConditionalExpectationReward.GeneratedActionRandomPairDefinitionalRawRangeMeasurableMeanRangeBoundedSource
        mu rewardKernel policy context state mean varianceProxy defaultAction
        reward hreward rewardLo rewardHi meanLo meanHi) :
    ConditionalExpectationReward.GeneratedActionRandomPairBoundedCenteredSource
      mu
      (ConditionalExpectationReward.generatedActionFromRewardHistory
        policy state defaultAction reward)
      rewardKernel policy context state mean varianceProxy defaultAction reward
      (ConditionalExpectationReward.generatedActionFromRewardHistory_measurable
        (policy := policy) (state := state) (defaultAction := defaultAction)
        (reward := reward) hreward source.definitional_map_source.hstate)
      hreward
      (fun i => rewardLo i - meanHi i)
      (fun i => rewardHi i - meanLo i) := by
  exact
    ConditionalExpectationReward.generatedActionRandomPairBoundedCenteredSource_of_definitionalRawRangeMeasurableMeanRangeBoundedSource
      (mOmega := mOmega)
      mu rewardKernel policy context state mean varianceProxy defaultAction
      reward hreward rewardLo rewardHi meanLo meanHi source

example {Omega Context State Action : Type}
    [mOmega : MeasurableSpace Omega] [StandardBorelSpace Omega]
    [MeasurableSpace Context] [MeasurableSpace State]
    [MeasurableSpace Action] [MeasurableSingletonClass Action]
    [Countable Action]
    (mu : MeasureTheory.Measure Omega) [MeasureTheory.IsFiniteMeasure mu]
    (rewardKernel : RewardKernel.MarkovRewardKernel (Prod Context Action) Rat)
    (policy : Nat -> Policy.MeasurablePolicy State Action)
    (context : (n : Nat) -> ((j : Finset.Iic n) -> Rat) -> Context)
    (state : (n : Nat) -> ((j : Finset.Iic n) -> Rat) -> State)
    (mean : Context -> Action -> Rat)
    (varianceProxy : Context -> Action -> NNReal)
    (defaultAction : Action)
    (reward : Omega -> RewardTrace Rat)
    (hreward : forall t : Nat,
      Measurable (fun omega : Omega => reward omega t))
    (rewardLo rewardHi meanLo meanHi : Nat -> Real)
    (source :
      ConditionalExpectationReward.GeneratedActionRandomPairDefinitionalRawRangeMeasurableMeanRangeBoundedSource
        mu rewardKernel policy context state mean varianceProxy defaultAction
        reward hreward rewardLo rewardHi meanLo meanHi) :
    ConditionalExpectationReward.GeneratedActionRandomPairCenteredSource
      mu
      (ConditionalExpectationReward.generatedActionFromRewardHistory
        policy state defaultAction reward)
      rewardKernel policy context state mean varianceProxy defaultAction reward
      (ConditionalExpectationReward.generatedActionFromRewardHistory_measurable
        (policy := policy) (state := state) (defaultAction := defaultAction)
        (reward := reward) hreward source.definitional_map_source.hstate)
      hreward := by
  exact
    ConditionalExpectationReward.generatedActionRandomPairCenteredSource_of_definitionalRawRangeMeasurableMeanRangeBoundedSource
      (mOmega := mOmega)
      mu rewardKernel policy context state mean varianceProxy defaultAction
      reward hreward rewardLo rewardHi meanLo meanHi source

example {Omega Context State Action : Type}
    [mOmega : MeasurableSpace Omega] [StandardBorelSpace Omega]
    [MeasurableSpace Context] [MeasurableSpace State]
    [MeasurableSpace Action] [MeasurableSingletonClass Action]
    [Countable Action]
    (mu : MeasureTheory.Measure Omega) [MeasureTheory.IsFiniteMeasure mu]
    (rewardKernel : RewardKernel.MarkovRewardKernel (Prod Context Action) Rat)
    (policy : Nat -> Policy.MeasurablePolicy State Action)
    (context : (n : Nat) -> ((j : Finset.Iic n) -> Rat) -> Context)
    (state : (n : Nat) -> ((j : Finset.Iic n) -> Rat) -> State)
    (mean : Context -> Action -> Rat)
    (varianceProxy : Context -> Action -> NNReal)
    (defaultAction : Action)
    (reward : Omega -> RewardTrace Rat)
    (hreward : forall t : Nat,
      Measurable (fun omega : Omega => reward omega t))
    (rewardLo rewardHi meanLo meanHi : Nat -> Real)
    (source :
      ConditionalExpectationReward.GeneratedActionRandomPairDefinitionalRawRangeMeasurableMeanRangeBoundedSource
        mu rewardKernel policy context state mean varianceProxy defaultAction
        reward hreward rewardLo rewardHi meanLo meanHi)
    (i : Nat) :
    Filter.EventuallyEq (MeasureTheory.ae mu)
      (@MeasureTheory.condExp Omega Real
        ((History.historyFiltrationSucc
          (ConditionalExpectationReward.generatedActionFromRewardHistory
            policy state defaultAction reward)
          reward
          (ConditionalExpectationReward.generatedActionFromRewardHistory_measurable
            (policy := policy) (state := state)
            (defaultAction := defaultAction) (reward := reward)
            hreward source.definitional_map_source.hstate)
          hreward) i)
        mOmega _ _ _ mu
        (fun omega : Omega =>
          (((reward omega (i + 1) -
            mean
              (context i
                (History.finiteRewardHistoryOfTrace (reward omega) i))
              ((policy i).action
                (state i
                  (History.finiteRewardHistoryOfTrace (reward omega) i))) :
                Rat) : Real))))
      (fun _omega : Omega => (0 : Real)) := by
  exact
    ConditionalExpectationReward.centeredReward_succ_condExp_eq_zero_of_generatedActionRandomPairDefinitionalRawRangeMeasurableMeanRangeBoundedSource
      (mOmega := mOmega)
      mu rewardKernel policy context state mean varianceProxy defaultAction
      reward hreward rewardLo rewardHi meanLo meanHi source i

example {Omega Context State Action : Type}
    [mOmega : MeasurableSpace Omega] [StandardBorelSpace Omega]
    [MeasurableSpace Context] [MeasurableSpace State]
    [MeasurableSpace Action] [MeasurableSingletonClass Action]
    [Countable Action]
    (mu : MeasureTheory.Measure Omega) [MeasureTheory.IsFiniteMeasure mu]
    (rewardKernel : RewardKernel.MarkovRewardKernel (Prod Context Action) Rat)
    (policy : Nat -> Policy.MeasurablePolicy State Action)
    (context : (n : Nat) -> ((j : Finset.Iic n) -> Rat) -> Context)
    (state : (n : Nat) -> ((j : Finset.Iic n) -> Rat) -> State)
    (mean : Context -> Action -> Rat)
    (varianceProxy : Context -> Action -> NNReal)
    (defaultAction : Action)
    (reward : Omega -> RewardTrace Rat)
    (hreward : forall t : Nat,
      Measurable (fun omega : Omega => reward omega t))
    (rewardLo rewardHi meanLo meanHi : Nat -> Real)
    (source :
      ConditionalExpectationReward.GeneratedActionRandomPairDefinitionalRawRangeMeasurableMeanRangeBoundedSource
        mu rewardKernel policy context state mean varianceProxy defaultAction
        reward hreward rewardLo rewardHi meanLo meanHi)
    (i : Nat)
    (c : NNReal)
    (h_centered_meas :
      @Measurable Omega Real mOmega inferInstance
        (fun omega : Omega =>
          (((reward omega (i + 1) -
            mean
              (context i
                (History.finiteRewardHistoryOfTrace (reward omega) i))
              ((policy i).action
                (state i
                  (History.finiteRewardHistoryOfTrace (reward omega) i))) :
                Rat) : Real))))
    (h_integrable_exp :
      forall t : Real,
        MeasureTheory.Integrable
          (fun omega : Omega =>
            Real.exp (t *
              (((reward omega (i + 1) -
                mean
                  (context i
                    (History.finiteRewardHistoryOfTrace (reward omega) i))
                  ((policy i).action
                    (state i
                      (History.finiteRewardHistoryOfTrace (reward omega) i))) :
                    Rat) : Real)))) mu)
    (h_variance_le :
      Filter.Eventually
        (fun omega : Omega =>
          varianceProxy
              (context i
                (History.finiteRewardHistoryOfTrace (reward omega) i))
              ((policy i).action
                (state i
                  (History.finiteRewardHistoryOfTrace (reward omega) i))) <=
            c)
        (MeasureTheory.ae
          (mu.trim
            ((History.historyFiltrationSucc
              (ConditionalExpectationReward.generatedActionFromRewardHistory
                policy state defaultAction reward)
              reward
              (ConditionalExpectationReward.generatedActionFromRewardHistory_measurable
                (policy := policy) (state := state)
                (defaultAction := defaultAction) (reward := reward)
                hreward source.definitional_map_source.hstate)
              hreward).le i)))) :
    ProbabilityTheory.HasCondSubgaussianMGF
      ((History.historyFiltrationSucc
        (ConditionalExpectationReward.generatedActionFromRewardHistory
          policy state defaultAction reward)
        reward
        (ConditionalExpectationReward.generatedActionFromRewardHistory_measurable
          (policy := policy) (state := state) (defaultAction := defaultAction)
          (reward := reward) hreward source.definitional_map_source.hstate)
        hreward) i)
      ((History.historyFiltrationSucc
        (ConditionalExpectationReward.generatedActionFromRewardHistory
          policy state defaultAction reward)
        reward
        (ConditionalExpectationReward.generatedActionFromRewardHistory_measurable
          (policy := policy) (state := state) (defaultAction := defaultAction)
          (reward := reward) hreward source.definitional_map_source.hstate)
        hreward).le i)
      (fun omega : Omega =>
        (((reward omega (i + 1) -
          mean
            (context i
              (History.finiteRewardHistoryOfTrace (reward omega) i))
            ((policy i).action
              (state i
                (History.finiteRewardHistoryOfTrace (reward omega) i))) :
            Rat) : Real)))
      c mu := by
  exact
    ConditionalExpectationReward.centeredReward_succ_hasCondSubgaussianMGF_of_generatedActionRandomPairDefinitionalRawRangeMeasurableMeanRangeBoundedSource
      (mOmega := mOmega)
      mu rewardKernel policy context state mean varianceProxy defaultAction
      reward hreward rewardLo rewardHi meanLo meanHi source i c
      h_centered_meas h_integrable_exp h_variance_le

example {Omega Context State Action : Type}
    [mOmega : MeasurableSpace Omega] [StandardBorelSpace Omega]
    [MeasurableSpace Context] [MeasurableSpace State]
    [MeasurableSpace Action] [MeasurableSingletonClass Action]
    [Countable Action]
    (mu : MeasureTheory.Measure Omega) [MeasureTheory.IsFiniteMeasure mu]
    (action : Omega -> ActionTrace Action)
    (rewardKernel : RewardKernel.MarkovRewardKernel (Prod Context Action) Rat)
    (policy : Nat -> Policy.MeasurablePolicy State Action)
    (context : (n : Nat) -> ((j : Finset.Iic n) -> Rat) -> Context)
    (state : (n : Nat) -> ((j : Finset.Iic n) -> Rat) -> State)
    (mean : Context -> Action -> Rat)
    (varianceProxy : Context -> Action -> NNReal)
    (defaultAction : Action)
    (reward : Omega -> RewardTrace Rat)
    (haction : forall t : Nat,
      Measurable (fun omega : Omega => action omega t))
    (hreward : forall t : Nat,
      Measurable (fun omega : Omega => reward omega t))
    (source :
      ConditionalExpectationReward.GeneratedActionRandomPairCenteredSource
        mu action rewardKernel policy context state mean varianceProxy
        defaultAction reward haction hreward) :
    ConditionalExpectationReward.GeneratedActionActualRewardMapSource
      mu action rewardKernel policy context state defaultAction reward
      haction hreward := by
  exact
    ConditionalExpectationReward.generatedActionActualRewardMapSource_of_randomPairCenteredSource
      (mOmega := mOmega)
      mu action rewardKernel policy context state mean varianceProxy
      defaultAction reward haction hreward source

example {Omega Context State Action : Type}
    [mOmega : MeasurableSpace Omega] [StandardBorelSpace Omega]
    [MeasurableSpace Context] [MeasurableSpace State]
    [MeasurableSpace Action] [MeasurableSingletonClass Action]
    [Countable Action]
    (mu : MeasureTheory.Measure Omega) [MeasureTheory.IsFiniteMeasure mu]
    (action : Omega -> ActionTrace Action)
    (rewardKernel : RewardKernel.MarkovRewardKernel (Prod Context Action) Rat)
    (policy : Nat -> Policy.MeasurablePolicy State Action)
    (context : (n : Nat) -> ((j : Finset.Iic n) -> Rat) -> Context)
    (state : (n : Nat) -> ((j : Finset.Iic n) -> Rat) -> State)
    (mean : Context -> Action -> Rat)
    (varianceProxy : Context -> Action -> NNReal)
    (defaultAction : Action)
    (reward : Omega -> RewardTrace Rat)
    (haction : forall t : Nat,
      Measurable (fun omega : Omega => action omega t))
    (hreward : forall t : Nat,
      Measurable (fun omega : Omega => reward omega t))
    (source :
      ConditionalExpectationReward.GeneratedActionRandomPairCenteredSource
        mu action rewardKernel policy context state mean varianceProxy
        defaultAction reward haction hreward)
    (i : Nat) :
    Filter.Eventually
      (fun omega : Omega =>
        @MeasureTheory.Measure.map Omega (Prod Action Rat) mOmega inferInstance
          (fun y : Omega => (action y (i + 1), reward y (i + 1)))
          (@ProbabilityTheory.condExpKernel Omega mOmega _ mu _
            ((History.historyFiltrationSucc action reward haction hreward) i)
            omega) =
        RewardKernel.actionRewardHistoryStepKernelFamily rewardKernel policy
          (fun n history =>
            context n (History.pairHistoryRewardProjection history))
          (fun n history =>
            state n (History.pairHistoryRewardProjection history))
          (fun n : Nat =>
            (source.hcontext n).comp
              (History.measurable_pairHistoryRewardProjection
                (Action := Action) (Reward := Rat) n))
          (fun n : Nat =>
            (source.hstate n).comp
              (History.measurable_pairHistoryRewardProjection
                (Action := Action) (Reward := Rat) n))
          i
          (History.finitePairHistoryOfTrace
            (action omega) (reward omega) i))
      (MeasureTheory.ae
        (mu.trim
          ((History.historyFiltrationSucc action reward haction hreward).le
            i))) := by
  exact
    ConditionalExpectationReward.actionRewardHistoryStepKernelFamily_pair_map_eq_historyFiltrationSucc_finitePairHistoryOfTrace_of_generatedActionRandomPairCenteredSource
      (mOmega := mOmega)
      mu action rewardKernel policy context state mean varianceProxy
      defaultAction reward haction hreward source i

example {Omega Context State Action : Type}
    [mOmega : MeasurableSpace Omega] [StandardBorelSpace Omega]
    [MeasurableSpace Context] [MeasurableSpace State]
    [MeasurableSpace Action] [MeasurableSingletonClass Action]
    [Countable Action]
    (mu : MeasureTheory.Measure Omega) [MeasureTheory.IsFiniteMeasure mu]
    (action : Omega -> ActionTrace Action)
    (rewardKernel : RewardKernel.MarkovRewardKernel (Prod Context Action) Rat)
    (policy : Nat -> Policy.MeasurablePolicy State Action)
    (context : (n : Nat) -> ((j : Finset.Iic n) -> Rat) -> Context)
    (state : (n : Nat) -> ((j : Finset.Iic n) -> Rat) -> State)
    (mean : Context -> Action -> Rat)
    (varianceProxy : Context -> Action -> NNReal)
    (defaultAction : Action)
    (reward : Omega -> RewardTrace Rat)
    (haction : forall t : Nat,
      Measurable (fun omega : Omega => action omega t))
    (hreward : forall t : Nat,
      Measurable (fun omega : Omega => reward omega t))
    (lo hi : Nat -> Real)
    (source :
      ConditionalExpectationReward.GeneratedActionRandomPairBoundedCenteredSource
        mu action rewardKernel policy context state mean varianceProxy
        defaultAction reward haction hreward lo hi)
    (i : Nat) :
    Filter.Eventually
      (fun omega : Omega =>
        @MeasureTheory.Measure.map Omega (Prod Action Rat) mOmega inferInstance
          (fun y : Omega => (action y (i + 1), reward y (i + 1)))
          (@ProbabilityTheory.condExpKernel Omega mOmega _ mu _
            ((History.historyFiltrationSucc action reward haction hreward) i)
            omega) =
        RewardKernel.actionRewardHistoryStepKernelFamily rewardKernel policy
          (fun n history =>
            context n (History.pairHistoryRewardProjection history))
          (fun n history =>
            state n (History.pairHistoryRewardProjection history))
          (fun n : Nat =>
            (source.hcontext n).comp
              (History.measurable_pairHistoryRewardProjection
                (Action := Action) (Reward := Rat) n))
          (fun n : Nat =>
            (source.hstate n).comp
              (History.measurable_pairHistoryRewardProjection
                (Action := Action) (Reward := Rat) n))
          i
          (History.finitePairHistoryOfTrace
            (action omega) (reward omega) i))
      (MeasureTheory.ae
        (mu.trim
          ((History.historyFiltrationSucc action reward haction hreward).le
            i))) := by
  exact
    ConditionalExpectationReward.actionRewardHistoryStepKernelFamily_pair_map_eq_historyFiltrationSucc_finitePairHistoryOfTrace_of_generatedActionRandomPairBoundedCenteredSource
      (mOmega := mOmega)
      mu action rewardKernel policy context state mean varianceProxy
      defaultAction reward haction hreward lo hi source i

example {Omega Context State Action : Type}
    [mOmega : MeasurableSpace Omega] [StandardBorelSpace Omega]
    [MeasurableSpace Context] [MeasurableSpace State]
    [MeasurableSpace Action] [MeasurableSingletonClass Action]
    [Countable Action]
    (mu : MeasureTheory.Measure Omega) [MeasureTheory.IsFiniteMeasure mu]
    (action : Omega -> ActionTrace Action)
    (rewardKernel : RewardKernel.MarkovRewardKernel (Prod Context Action) Rat)
    (policy : Nat -> Policy.MeasurablePolicy State Action)
    (context : (n : Nat) -> ((j : Finset.Iic n) -> Rat) -> Context)
    (state : (n : Nat) -> ((j : Finset.Iic n) -> Rat) -> State)
    (mean : Context -> Action -> Rat)
    (varianceProxy : Context -> Action -> NNReal)
    (defaultAction : Action)
    (reward : Omega -> RewardTrace Rat)
    (haction : forall t : Nat,
      Measurable (fun omega : Omega => action omega t))
    (hreward : forall t : Nat,
      Measurable (fun omega : Omega => reward omega t))
    (source :
      ConditionalExpectationReward.GeneratedActionRandomPairCenteredSource
        mu action rewardKernel policy context state mean varianceProxy
        defaultAction reward haction hreward)
    (i : Nat) :
    Filter.Eventually
      (fun omega : Omega =>
        @MeasureTheory.Measure.map Omega ((j : Finset.Iic (i + 1)) -> Prod Action Rat)
          mOmega inferInstance
          (fun y : Omega =>
            History.finitePairHistoryOfTrace (action y) (reward y) (i + 1))
          (@ProbabilityTheory.condExpKernel Omega mOmega _ mu _
            ((History.historyFiltrationSucc action reward haction hreward) i)
            omega) =
        RewardKernel.actionRewardPartialTrajectoryKernel rewardKernel policy
          (fun n history =>
            context n (History.pairHistoryRewardProjection history))
          (fun n history =>
            state n (History.pairHistoryRewardProjection history))
          (fun n : Nat =>
            (source.hcontext n).comp
              (History.measurable_pairHistoryRewardProjection
                (Action := Action) (Reward := Rat) n))
          (fun n : Nat =>
            (source.hstate n).comp
              (History.measurable_pairHistoryRewardProjection
                (Action := Action) (Reward := Rat) n))
          i (i + 1)
          (History.finitePairHistoryOfTrace
            (action omega) (reward omega) i))
      (MeasureTheory.ae
        (mu.trim
          ((History.historyFiltrationSucc action reward haction hreward).le
            i))) := by
  exact
    ConditionalExpectationReward.actionRewardPartialTrajectoryKernel_map_eq_historyFiltrationSucc_finitePairHistoryOfTrace_of_generatedActionRandomPairCenteredSource
      (mOmega := mOmega)
      mu action rewardKernel policy context state mean varianceProxy
      defaultAction reward haction hreward source i

example {Omega Context State Action : Type}
    [mOmega : MeasurableSpace Omega] [StandardBorelSpace Omega]
    [MeasurableSpace Context] [MeasurableSpace State]
    [MeasurableSpace Action] [MeasurableSingletonClass Action]
    [Countable Action]
    (mu : MeasureTheory.Measure Omega) [MeasureTheory.IsFiniteMeasure mu]
    (action : Omega -> ActionTrace Action)
    (rewardKernel : RewardKernel.MarkovRewardKernel (Prod Context Action) Rat)
    (policy : Nat -> Policy.MeasurablePolicy State Action)
    (context : (n : Nat) -> ((j : Finset.Iic n) -> Rat) -> Context)
    (state : (n : Nat) -> ((j : Finset.Iic n) -> Rat) -> State)
    (mean : Context -> Action -> Rat)
    (varianceProxy : Context -> Action -> NNReal)
    (defaultAction : Action)
    (reward : Omega -> RewardTrace Rat)
    (haction : forall t : Nat,
      Measurable (fun omega : Omega => action omega t))
    (hreward : forall t : Nat,
      Measurable (fun omega : Omega => reward omega t))
    (source :
      ConditionalExpectationReward.GeneratedActionRandomPairCenteredSource
        mu action rewardKernel policy context state mean varianceProxy
        defaultAction reward haction hreward)
    (i : Nat) :
    Filter.EventuallyEq (MeasureTheory.ae mu)
      (@MeasureTheory.condExp Omega Real
        ((History.historyFiltrationSucc action reward haction hreward) i)
        mOmega _ _ _ mu
        (fun omega : Omega =>
          (((reward omega (i + 1) -
            mean
              (context i
                (History.finiteRewardHistoryOfTrace (reward omega) i))
              ((policy i).action
                (state i
                  (History.finiteRewardHistoryOfTrace (reward omega) i))) :
                Rat) : Real))))
      (fun _omega : Omega => (0 : Real)) := by
  exact
    ConditionalExpectationReward.centeredReward_succ_condExp_eq_zero_of_generatedActionRandomPairCenteredSource
      (mOmega := mOmega)
      mu action rewardKernel policy context state mean varianceProxy
      defaultAction reward haction hreward source i

example {Omega Context State Action : Type}
    [mOmega : MeasurableSpace Omega] [StandardBorelSpace Omega]
    [MeasurableSpace Context] [MeasurableSpace State]
    [MeasurableSpace Action] [MeasurableSingletonClass Action]
    [Countable Action]
    (mu : MeasureTheory.Measure Omega) [MeasureTheory.IsFiniteMeasure mu]
    (action : Omega -> ActionTrace Action)
    (rewardKernel : RewardKernel.MarkovRewardKernel (Prod Context Action) Rat)
    (policy : Nat -> Policy.MeasurablePolicy State Action)
    (context : (n : Nat) -> ((j : Finset.Iic n) -> Rat) -> Context)
    (state : (n : Nat) -> ((j : Finset.Iic n) -> Rat) -> State)
    (mean : Context -> Action -> Rat)
    (varianceProxy : Context -> Action -> NNReal)
    (defaultAction : Action)
    (reward : Omega -> RewardTrace Rat)
    (haction : forall t : Nat,
      Measurable (fun omega : Omega => action omega t))
    (hreward : forall t : Nat,
      Measurable (fun omega : Omega => reward omega t))
    (source :
      ConditionalExpectationReward.GeneratedActionRandomPairCenteredSource
        mu action rewardKernel policy context state mean varianceProxy
        defaultAction reward haction hreward)
    (i : Nat)
    (c : NNReal)
    (h_centered_meas :
      @Measurable Omega Real mOmega inferInstance
        (fun omega : Omega =>
          (((reward omega (i + 1) -
            mean
              (context i
                (History.finiteRewardHistoryOfTrace (reward omega) i))
              ((policy i).action
                (state i
                  (History.finiteRewardHistoryOfTrace (reward omega) i))) :
                Rat) : Real))))
    (h_integrable_exp :
      forall t : Real,
        MeasureTheory.Integrable
          (fun omega : Omega =>
            Real.exp (t *
              (((reward omega (i + 1) -
                mean
                  (context i
                    (History.finiteRewardHistoryOfTrace (reward omega) i))
                  ((policy i).action
                    (state i
                      (History.finiteRewardHistoryOfTrace (reward omega) i))) :
                    Rat) : Real)))) mu)
    (h_variance_le :
      Filter.Eventually
        (fun omega : Omega =>
          varianceProxy
              (context i
                (History.finiteRewardHistoryOfTrace (reward omega) i))
              ((policy i).action
                (state i
                  (History.finiteRewardHistoryOfTrace (reward omega) i))) <=
            c)
        (MeasureTheory.ae
          (mu.trim
            ((History.historyFiltrationSucc action reward haction hreward).le
              i)))) :
    ProbabilityTheory.HasCondSubgaussianMGF
      ((History.historyFiltrationSucc action reward haction hreward) i)
      ((History.historyFiltrationSucc action reward haction hreward).le i)
      (fun omega : Omega =>
        (((reward omega (i + 1) -
          mean
            (context i
              (History.finiteRewardHistoryOfTrace (reward omega) i))
            ((policy i).action
              (state i
                (History.finiteRewardHistoryOfTrace (reward omega) i))) :
            Rat) : Real)))
      c mu := by
  exact
    ConditionalExpectationReward.centeredReward_succ_hasCondSubgaussianMGF_of_generatedActionRandomPairCenteredSource
      (mOmega := mOmega)
      mu action rewardKernel policy context state mean varianceProxy
      defaultAction reward haction hreward source i c h_centered_meas
      h_integrable_exp h_variance_le

example {Omega Context State Action : Type}
    [mOmega : MeasurableSpace Omega] [StandardBorelSpace Omega]
    [MeasurableSpace Context] [MeasurableSpace State]
    [MeasurableSpace Action] [MeasurableSingletonClass Action]
    [Countable Action]
    (mu : MeasureTheory.Measure Omega) [MeasureTheory.IsFiniteMeasure mu]
    (action : Omega -> ActionTrace Action)
    (rewardKernel : RewardKernel.MarkovRewardKernel (Prod Context Action) Rat)
    (policy : Nat -> Policy.MeasurablePolicy State Action)
    (context : (n : Nat) -> ((j : Finset.Iic n) -> Rat) -> Context)
    (state : (n : Nat) -> ((j : Finset.Iic n) -> Rat) -> State)
    (mean : Context -> Action -> Rat)
    (varianceProxy : Context -> Action -> NNReal)
    (defaultAction : Action)
    (reward : Omega -> RewardTrace Rat)
    (haction : forall t : Nat,
      Measurable (fun omega : Omega => action omega t))
    (hreward : forall t : Nat,
      Measurable (fun omega : Omega => reward omega t))
    (lo hi : Nat -> Real)
    (source :
      ConditionalExpectationReward.GeneratedActionRandomPairBoundedCenteredSource
        mu action rewardKernel policy context state mean varianceProxy
        defaultAction reward haction hreward lo hi)
    (i : Nat)
    (c : NNReal)
    (h_centered_meas :
      @Measurable Omega Real mOmega inferInstance
        (fun omega : Omega =>
          (((reward omega (i + 1) -
            mean
              (context i
                (History.finiteRewardHistoryOfTrace (reward omega) i))
              ((policy i).action
                (state i
                  (History.finiteRewardHistoryOfTrace (reward omega) i))) :
                Rat) : Real))))
    (h_integrable_exp :
      forall t : Real,
        MeasureTheory.Integrable
          (fun omega : Omega =>
            Real.exp (t *
              (((reward omega (i + 1) -
                mean
                  (context i
                    (History.finiteRewardHistoryOfTrace (reward omega) i))
                  ((policy i).action
                    (state i
                      (History.finiteRewardHistoryOfTrace (reward omega) i))) :
                    Rat) : Real)))) mu)
    (h_variance_le :
      Filter.Eventually
        (fun omega : Omega =>
          varianceProxy
              (context i
                (History.finiteRewardHistoryOfTrace (reward omega) i))
              ((policy i).action
                (state i
                  (History.finiteRewardHistoryOfTrace (reward omega) i))) <=
            c)
        (MeasureTheory.ae
          (mu.trim
            ((History.historyFiltrationSucc action reward haction hreward).le
              i)))) :
    ProbabilityTheory.HasCondSubgaussianMGF
      ((History.historyFiltrationSucc action reward haction hreward) i)
      ((History.historyFiltrationSucc action reward haction hreward).le i)
      (fun omega : Omega =>
        (((reward omega (i + 1) -
          mean
            (context i
              (History.finiteRewardHistoryOfTrace (reward omega) i))
            ((policy i).action
              (state i
                (History.finiteRewardHistoryOfTrace (reward omega) i))) :
            Rat) : Real)))
      c mu := by
  exact
    ConditionalExpectationReward.centeredReward_succ_hasCondSubgaussianMGF_of_generatedActionRandomPairBoundedCenteredSource
      (mOmega := mOmega)
      mu action rewardKernel policy context state mean varianceProxy
      defaultAction reward haction hreward lo hi source i c h_centered_meas
      h_integrable_exp h_variance_le

example {Omega Context State Action : Type}
    [mOmega : MeasurableSpace Omega] [StandardBorelSpace Omega]
    [MeasurableSpace Context] [MeasurableSpace State]
    [MeasurableSpace Action] [MeasurableSingletonClass Action]
    [Countable Action]
    (mu : MeasureTheory.Measure Omega) [MeasureTheory.IsFiniteMeasure mu]
    (action : Omega -> ActionTrace Action)
    (rewardKernel : RewardKernel.MarkovRewardKernel (Prod Context Action) Rat)
    (policy : Nat -> Policy.MeasurablePolicy State Action)
    (context : (n : Nat) -> ((j : Finset.Iic n) -> Rat) -> Context)
    (state : (n : Nat) -> ((j : Finset.Iic n) -> Rat) -> State)
    (mean : Context -> Action -> Rat)
    (varianceProxy : Context -> Action -> NNReal)
    (defaultAction : Action)
    (reward : Omega -> RewardTrace Rat)
    (haction : forall t : Nat,
      Measurable (fun omega : Omega => action omega t))
    (hreward : forall t : Nat,
      Measurable (fun omega : Omega => reward omega t))
    (lo hi : Nat -> Real)
    (source :
      ConditionalExpectationReward.GeneratedActionRandomPairBoundedCenteredSource
        mu action rewardKernel policy context state mean varianceProxy
        defaultAction reward haction hreward lo hi)
    (i : Nat) :
    MeasureTheory.Integrable
      (fun omega : Omega =>
        (((reward omega (i + 1) -
          mean
            (context i
              (History.finiteRewardHistoryOfTrace (reward omega) i))
            ((policy i).action
              (state i
                (History.finiteRewardHistoryOfTrace (reward omega) i))) :
              Rat) : Real))) mu := by
  exact
    ConditionalExpectationReward.centeredReward_succ_integrable_of_generatedActionRandomPairBoundedCenteredSource
      (mOmega := mOmega)
      mu action rewardKernel policy context state mean varianceProxy
      defaultAction reward haction hreward lo hi source i

example {Omega Context State Action : Type}
    [mOmega : MeasurableSpace Omega] [StandardBorelSpace Omega]
    [MeasurableSpace Context] [MeasurableSpace State]
    [MeasurableSpace Action] [MeasurableSingletonClass Action]
    [Countable Action]
    (mu : MeasureTheory.Measure Omega) [MeasureTheory.IsFiniteMeasure mu]
    (action : Omega -> ActionTrace Action)
    (rewardKernel : RewardKernel.MarkovRewardKernel (Prod Context Action) Rat)
    (policy : Nat -> Policy.MeasurablePolicy State Action)
    (context : (n : Nat) -> ((j : Finset.Iic n) -> Rat) -> Context)
    (state : (n : Nat) -> ((j : Finset.Iic n) -> Rat) -> State)
    (mean : Context -> Action -> Rat)
    (varianceProxy : Context -> Action -> NNReal)
    (defaultAction : Action)
    (reward : Omega -> RewardTrace Rat)
    (haction : forall t : Nat,
      Measurable (fun omega : Omega => action omega t))
    (hreward : forall t : Nat,
      Measurable (fun omega : Omega => reward omega t))
    (lo hi : Nat -> Real)
    (source :
      ConditionalExpectationReward.GeneratedActionRandomPairBoundedCenteredSource
        mu action rewardKernel policy context state mean varianceProxy
        defaultAction reward haction hreward lo hi) :
    ConditionalExpectationReward.GeneratedActionRandomPairCenteredSource
      mu action rewardKernel policy context state mean varianceProxy
      defaultAction reward haction hreward := by
  exact
    ConditionalExpectationReward.generatedActionRandomPairCenteredSource_of_boundedCenteredSource
      (mOmega := mOmega)
      mu action rewardKernel policy context state mean varianceProxy
      defaultAction reward haction hreward lo hi source

example {Omega Context State Action : Type}
    [mOmega : MeasurableSpace Omega] [StandardBorelSpace Omega]
    [MeasurableSpace Context] [MeasurableSpace State]
    [MeasurableSpace Action] [MeasurableSingletonClass Action]
    [Countable Action]
    (mu : MeasureTheory.Measure Omega) [MeasureTheory.IsFiniteMeasure mu]
    (action : Omega -> ActionTrace Action)
    (rewardKernel : RewardKernel.MarkovRewardKernel (Prod Context Action) Rat)
    (policy : Nat -> Policy.MeasurablePolicy State Action)
    (context : (n : Nat) -> ((j : Finset.Iic n) -> Rat) -> Context)
    (state : (n : Nat) -> ((j : Finset.Iic n) -> Rat) -> State)
    (mean : Context -> Action -> Rat)
    (varianceProxy : Context -> Action -> NNReal)
    (defaultAction : Action)
    (reward : Omega -> RewardTrace Rat)
    (haction : forall t : Nat,
      Measurable (fun omega : Omega => action omega t))
    (hreward : forall t : Nat,
      Measurable (fun omega : Omega => reward omega t))
    (lo hi : Nat -> Real)
    (source :
      ConditionalExpectationReward.GeneratedActionRandomPairBoundedCenteredSource
        mu action rewardKernel policy context state mean varianceProxy
        defaultAction reward haction hreward lo hi) :
    ConditionalExpectationReward.GeneratedActionActualRewardMapSource
      mu action rewardKernel policy context state defaultAction reward
      haction hreward := by
  exact
    ConditionalExpectationReward.generatedActionActualRewardMapSource_of_randomPairBoundedCenteredSource
      (mOmega := mOmega)
      mu action rewardKernel policy context state mean varianceProxy
      defaultAction reward haction hreward lo hi source

example {Omega Context State Action : Type}
    [mOmega : MeasurableSpace Omega] [StandardBorelSpace Omega]
    [MeasurableSpace Context] [MeasurableSpace State]
    [MeasurableSpace Action] [MeasurableSingletonClass Action]
    [Countable Action]
    (mu : MeasureTheory.Measure Omega) [MeasureTheory.IsFiniteMeasure mu]
    (action : Omega -> ActionTrace Action)
    (rewardKernel : RewardKernel.MarkovRewardKernel (Prod Context Action) Rat)
    (policy : Nat -> Policy.MeasurablePolicy State Action)
    (context : (n : Nat) -> ((j : Finset.Iic n) -> Rat) -> Context)
    (state : (n : Nat) -> ((j : Finset.Iic n) -> Rat) -> State)
    (mean : Context -> Action -> Rat)
    (varianceProxy : Context -> Action -> NNReal)
    (defaultAction : Action)
    (reward : Omega -> RewardTrace Rat)
    (haction : forall t : Nat,
      Measurable (fun omega : Omega => action omega t))
    (hreward : forall t : Nat,
      Measurable (fun omega : Omega => reward omega t))
    (lo hi : Nat -> Real)
    (source :
      ConditionalExpectationReward.GeneratedActionRandomPairBoundedCenteredSource
        mu action rewardKernel policy context state mean varianceProxy
        defaultAction reward haction hreward lo hi)
    (i : Nat) :
    Filter.Eventually
      (fun omega : Omega =>
        @MeasureTheory.Measure.map Omega ((j : Finset.Iic (i + 1)) -> Prod Action Rat)
          mOmega inferInstance
          (fun y : Omega =>
            History.finitePairHistoryOfTrace (action y) (reward y) (i + 1))
          (@ProbabilityTheory.condExpKernel Omega mOmega _ mu _
            ((History.historyFiltrationSucc action reward haction hreward) i)
            omega) =
        RewardKernel.actionRewardPartialTrajectoryKernel rewardKernel policy
          (fun n history =>
            context n (History.pairHistoryRewardProjection history))
          (fun n history =>
            state n (History.pairHistoryRewardProjection history))
          (fun n : Nat =>
            (source.hcontext n).comp
              (History.measurable_pairHistoryRewardProjection
                (Action := Action) (Reward := Rat) n))
          (fun n : Nat =>
            (source.hstate n).comp
              (History.measurable_pairHistoryRewardProjection
                (Action := Action) (Reward := Rat) n))
          i (i + 1)
          (History.finitePairHistoryOfTrace
            (action omega) (reward omega) i))
      (MeasureTheory.ae
        (mu.trim
          ((History.historyFiltrationSucc action reward haction hreward).le
            i))) := by
  exact
    ConditionalExpectationReward.actionRewardPartialTrajectoryKernel_map_eq_historyFiltrationSucc_finitePairHistoryOfTrace_of_generatedActionRandomPairBoundedCenteredSource
      (mOmega := mOmega)
      mu action rewardKernel policy context state mean varianceProxy
      defaultAction reward haction hreward lo hi source i

example {Omega Context State Action : Type}
    [mOmega : MeasurableSpace Omega] [StandardBorelSpace Omega]
    [MeasurableSpace Context] [MeasurableSpace State]
    [MeasurableSpace Action] [MeasurableSingletonClass Action]
    [Countable Action]
    (mu : MeasureTheory.Measure Omega) [MeasureTheory.IsFiniteMeasure mu]
    (action : Omega -> ActionTrace Action)
    (rewardKernel : RewardKernel.MarkovRewardKernel (Prod Context Action) Rat)
    (policy : Nat -> Policy.MeasurablePolicy State Action)
    (context : (n : Nat) -> ((j : Finset.Iic n) -> Rat) -> Context)
    (state : (n : Nat) -> ((j : Finset.Iic n) -> Rat) -> State)
    (mean : Context -> Action -> Rat)
    (varianceProxy : Context -> Action -> NNReal)
    (defaultAction : Action)
    (reward : Omega -> RewardTrace Rat)
    (haction : forall t : Nat,
      Measurable (fun omega : Omega => action omega t))
    (hreward : forall t : Nat,
      Measurable (fun omega : Omega => reward omega t))
    (lo hi : Nat -> Real)
    (source :
      ConditionalExpectationReward.GeneratedActionRandomPairBoundedCenteredSource
        mu action rewardKernel policy context state mean varianceProxy
        defaultAction reward haction hreward lo hi)
    (i : Nat) :
    Filter.EventuallyEq (MeasureTheory.ae mu)
      (@MeasureTheory.condExp Omega Real
        ((History.historyFiltrationSucc action reward haction hreward) i)
        mOmega _ _ _ mu
        (fun omega : Omega =>
          (((reward omega (i + 1) -
            mean
              (context i
                (History.finiteRewardHistoryOfTrace (reward omega) i))
              ((policy i).action
                (state i
                  (History.finiteRewardHistoryOfTrace (reward omega) i))) :
                Rat) : Real))))
      (fun _omega : Omega => (0 : Real)) := by
  exact
    ConditionalExpectationReward.centeredReward_succ_condExp_eq_zero_of_generatedActionRandomPairBoundedCenteredSource
      (mOmega := mOmega)
      mu action rewardKernel policy context state mean varianceProxy
      defaultAction reward haction hreward lo hi source i

example {Omega : Type}
    [mOmega : MeasurableSpace Omega]
    (mu : MeasureTheory.Measure Omega)
    (reward : Omega -> RewardTrace Rat)
    (hreward : forall t : Nat,
      Measurable (fun omega : Omega => reward omega t))
    (i : Nat) :
    AEMeasurable
      (fun omega : Omega => (((reward omega (i + 1) : Rat) : Real))) mu := by
  exact
    ConditionalExpectationReward.rawReward_succ_aemeasurable_of_measurable_reward
      (mOmega := mOmega) mu reward hreward i

example {Omega Context State Action : Type}
    [mOmega : MeasurableSpace Omega] [StandardBorelSpace Omega]
    [MeasurableSpace Context] [MeasurableSpace State]
    [MeasurableSpace Action] [MeasurableSingletonClass Action]
    [Countable Action]
    (mu : MeasureTheory.Measure Omega) [MeasureTheory.IsFiniteMeasure mu]
    (action : Omega -> ActionTrace Action)
    (rewardKernel : RewardKernel.MarkovRewardKernel (Prod Context Action) Rat)
    (policy : Nat -> Policy.MeasurablePolicy State Action)
    (context : (n : Nat) -> ((j : Finset.Iic n) -> Rat) -> Context)
    (state : (n : Nat) -> ((j : Finset.Iic n) -> Rat) -> State)
    (mean : Context -> Action -> Rat)
    (varianceProxy : Context -> Action -> NNReal)
    (defaultAction : Action)
    (reward : Omega -> RewardTrace Rat)
    (haction : forall t : Nat,
      Measurable (fun omega : Omega => action omega t))
    (hreward : forall t : Nat,
      Measurable (fun omega : Omega => reward omega t))
    (rewardLo rewardHi meanLo meanHi : Nat -> Real)
    (source :
      ConditionalExpectationReward.GeneratedActionRandomPairRawBoundMeanBoundedSource
        mu action rewardKernel policy context state mean varianceProxy
        defaultAction reward haction hreward rewardLo rewardHi meanLo meanHi) :
    ConditionalExpectationReward.GeneratedActionRandomPairRawMeanBoundedSource
      mu action rewardKernel policy context state mean varianceProxy
      defaultAction reward haction hreward rewardLo rewardHi meanLo meanHi := by
  exact
    ConditionalExpectationReward.generatedActionRandomPairRawMeanBoundedSource_of_rawBoundMeanBoundedSource
      (mOmega := mOmega)
      mu action rewardKernel policy context state mean varianceProxy
      defaultAction reward haction hreward rewardLo rewardHi meanLo meanHi
      source

example {Omega Context State Action : Type}
    [mOmega : MeasurableSpace Omega] [StandardBorelSpace Omega]
    [MeasurableSpace Context] [MeasurableSpace State]
    [MeasurableSpace Action] [MeasurableSingletonClass Action]
    [Countable Action]
    (mu : MeasureTheory.Measure Omega) [MeasureTheory.IsFiniteMeasure mu]
    (action : Omega -> ActionTrace Action)
    (rewardKernel : RewardKernel.MarkovRewardKernel (Prod Context Action) Rat)
    (policy : Nat -> Policy.MeasurablePolicy State Action)
    (context : (n : Nat) -> ((j : Finset.Iic n) -> Rat) -> Context)
    (state : (n : Nat) -> ((j : Finset.Iic n) -> Rat) -> State)
    (mean : Context -> Action -> Rat)
    (varianceProxy : Context -> Action -> NNReal)
    (defaultAction : Action)
    (reward : Omega -> RewardTrace Rat)
    (haction : forall t : Nat,
      Measurable (fun omega : Omega => action omega t))
    (hreward : forall t : Nat,
      Measurable (fun omega : Omega => reward omega t))
    (rewardLo rewardHi meanLo meanHi : Nat -> Real)
    (source :
      ConditionalExpectationReward.GeneratedActionRandomPairRawBoundMeanBoundedSource
        mu action rewardKernel policy context state mean varianceProxy
        defaultAction reward haction hreward rewardLo rewardHi meanLo meanHi) :
    ConditionalExpectationReward.GeneratedActionActualRewardMapSource
      mu action rewardKernel policy context state defaultAction reward
      haction hreward := by
  exact
    ConditionalExpectationReward.generatedActionActualRewardMapSource_of_randomPairRawBoundMeanBoundedSource
      (mOmega := mOmega)
      mu action rewardKernel policy context state mean varianceProxy
      defaultAction reward haction hreward rewardLo rewardHi meanLo meanHi
      source

example {Omega Context State Action : Type}
    [mOmega : MeasurableSpace Omega] [StandardBorelSpace Omega]
    [MeasurableSpace Context] [MeasurableSpace State]
    [MeasurableSpace Action] [MeasurableSingletonClass Action]
    [Countable Action]
    (mu : MeasureTheory.Measure Omega) [MeasureTheory.IsFiniteMeasure mu]
    (action : Omega -> ActionTrace Action)
    (rewardKernel : RewardKernel.MarkovRewardKernel (Prod Context Action) Rat)
    (policy : Nat -> Policy.MeasurablePolicy State Action)
    (context : (n : Nat) -> ((j : Finset.Iic n) -> Rat) -> Context)
    (state : (n : Nat) -> ((j : Finset.Iic n) -> Rat) -> State)
    (mean : Context -> Action -> Rat)
    (varianceProxy : Context -> Action -> NNReal)
    (defaultAction : Action)
    (reward : Omega -> RewardTrace Rat)
    (haction : forall t : Nat,
      Measurable (fun omega : Omega => action omega t))
    (hreward : forall t : Nat,
      Measurable (fun omega : Omega => reward omega t))
    (rewardLo rewardHi meanLo meanHi : Nat -> Real)
    (source :
      ConditionalExpectationReward.GeneratedActionRandomPairRawBoundMeanBoundedSource
        mu action rewardKernel policy context state mean varianceProxy
        defaultAction reward haction hreward rewardLo rewardHi meanLo meanHi)
    (i : Nat) :
    AEMeasurable
      (fun omega : Omega =>
        (((reward omega (i + 1) -
          mean
            (context i
              (History.finiteRewardHistoryOfTrace (reward omega) i))
            ((policy i).action
              (state i
                (History.finiteRewardHistoryOfTrace (reward omega) i))) :
            Rat) : Real))) mu := by
  exact
    ConditionalExpectationReward.centeredReward_succ_aemeasurable_of_generatedActionRandomPairRawBoundMeanBoundedSource
      (mOmega := mOmega)
      mu action rewardKernel policy context state mean varianceProxy
      defaultAction reward haction hreward rewardLo rewardHi meanLo meanHi
      source i

example {Omega Context State Action : Type}
    [mOmega : MeasurableSpace Omega] [StandardBorelSpace Omega]
    [MeasurableSpace Context] [MeasurableSpace State]
    [MeasurableSpace Action] [MeasurableSingletonClass Action]
    [Countable Action]
    (mu : MeasureTheory.Measure Omega) [MeasureTheory.IsFiniteMeasure mu]
    (action : Omega -> ActionTrace Action)
    (rewardKernel : RewardKernel.MarkovRewardKernel (Prod Context Action) Rat)
    (policy : Nat -> Policy.MeasurablePolicy State Action)
    (context : (n : Nat) -> ((j : Finset.Iic n) -> Rat) -> Context)
    (state : (n : Nat) -> ((j : Finset.Iic n) -> Rat) -> State)
    (mean : Context -> Action -> Rat)
    (varianceProxy : Context -> Action -> NNReal)
    (defaultAction : Action)
    (reward : Omega -> RewardTrace Rat)
    (haction : forall t : Nat,
      Measurable (fun omega : Omega => action omega t))
    (hreward : forall t : Nat,
      Measurable (fun omega : Omega => reward omega t))
    (rewardLo rewardHi meanLo meanHi : Nat -> Real)
    (source :
      ConditionalExpectationReward.GeneratedActionRandomPairRawBoundMeanBoundedSource
        mu action rewardKernel policy context state mean varianceProxy
        defaultAction reward haction hreward rewardLo rewardHi meanLo meanHi)
    (i : Nat) :
    Filter.Eventually
      (fun omega : Omega =>
        Set.Icc (rewardLo i - meanHi i) (rewardHi i - meanLo i)
          (((reward omega (i + 1) -
            mean
              (context i
                (History.finiteRewardHistoryOfTrace (reward omega) i))
              ((policy i).action
                (state i
                  (History.finiteRewardHistoryOfTrace (reward omega) i))) :
              Rat) : Real)))
      (MeasureTheory.ae mu) := by
  exact
    ConditionalExpectationReward.centeredReward_succ_bound_of_generatedActionRandomPairRawBoundMeanBoundedSource
      (mOmega := mOmega)
      mu action rewardKernel policy context state mean varianceProxy
      defaultAction reward haction hreward rewardLo rewardHi meanLo meanHi
      source i

example {Omega Context State Action : Type}
    [mOmega : MeasurableSpace Omega] [StandardBorelSpace Omega]
    [MeasurableSpace Context] [MeasurableSpace State]
    [MeasurableSpace Action] [MeasurableSingletonClass Action]
    [Countable Action]
    (mu : MeasureTheory.Measure Omega) [MeasureTheory.IsFiniteMeasure mu]
    (action : Omega -> ActionTrace Action)
    (rewardKernel : RewardKernel.MarkovRewardKernel (Prod Context Action) Rat)
    (policy : Nat -> Policy.MeasurablePolicy State Action)
    (context : (n : Nat) -> ((j : Finset.Iic n) -> Rat) -> Context)
    (state : (n : Nat) -> ((j : Finset.Iic n) -> Rat) -> State)
    (mean : Context -> Action -> Rat)
    (varianceProxy : Context -> Action -> NNReal)
    (defaultAction : Action)
    (reward : Omega -> RewardTrace Rat)
    (haction : forall t : Nat,
      Measurable (fun omega : Omega => action omega t))
    (hreward : forall t : Nat,
      Measurable (fun omega : Omega => reward omega t))
    (rewardLo rewardHi meanLo meanHi : Nat -> Real)
    (source :
      ConditionalExpectationReward.GeneratedActionRandomPairRawBoundMeanBoundedSource
        mu action rewardKernel policy context state mean varianceProxy
        defaultAction reward haction hreward rewardLo rewardHi meanLo meanHi)
    (i : Nat) :
    MeasureTheory.Integrable
      (fun omega : Omega =>
        (((reward omega (i + 1) -
          mean
            (context i
              (History.finiteRewardHistoryOfTrace (reward omega) i))
            ((policy i).action
              (state i
                (History.finiteRewardHistoryOfTrace (reward omega) i))) :
              Rat) : Real))) mu := by
  exact
    ConditionalExpectationReward.centeredReward_succ_integrable_of_generatedActionRandomPairRawBoundMeanBoundedSource
      (mOmega := mOmega)
      mu action rewardKernel policy context state mean varianceProxy
      defaultAction reward haction hreward rewardLo rewardHi meanLo meanHi
      source i

example {Omega Context State Action : Type}
    [mOmega : MeasurableSpace Omega] [StandardBorelSpace Omega]
    [MeasurableSpace Context] [MeasurableSpace State]
    [MeasurableSpace Action] [MeasurableSingletonClass Action]
    [Countable Action]
    (mu : MeasureTheory.Measure Omega) [MeasureTheory.IsFiniteMeasure mu]
    (action : Omega -> ActionTrace Action)
    (rewardKernel : RewardKernel.MarkovRewardKernel (Prod Context Action) Rat)
    (policy : Nat -> Policy.MeasurablePolicy State Action)
    (context : (n : Nat) -> ((j : Finset.Iic n) -> Rat) -> Context)
    (state : (n : Nat) -> ((j : Finset.Iic n) -> Rat) -> State)
    (mean : Context -> Action -> Rat)
    (varianceProxy : Context -> Action -> NNReal)
    (defaultAction : Action)
    (reward : Omega -> RewardTrace Rat)
    (haction : forall t : Nat,
      Measurable (fun omega : Omega => action omega t))
    (hreward : forall t : Nat,
      Measurable (fun omega : Omega => reward omega t))
    (rewardLo rewardHi meanLo meanHi : Nat -> Real)
    (source :
      ConditionalExpectationReward.GeneratedActionRandomPairRawBoundMeanBoundedSource
        mu action rewardKernel policy context state mean varianceProxy
        defaultAction reward haction hreward rewardLo rewardHi meanLo meanHi)
    (i : Nat) :
    Filter.Eventually
      (fun omega : Omega =>
        @MeasureTheory.Measure.map Omega (Prod Action Rat) mOmega inferInstance
          (fun y : Omega => (action y (i + 1), reward y (i + 1)))
          (@ProbabilityTheory.condExpKernel Omega mOmega _ mu _
            ((History.historyFiltrationSucc action reward haction hreward) i)
            omega) =
        RewardKernel.actionRewardHistoryStepKernelFamily rewardKernel policy
          (fun n history =>
            context n (History.pairHistoryRewardProjection history))
          (fun n history =>
            state n (History.pairHistoryRewardProjection history))
          (fun n : Nat =>
            (source.hcontext n).comp
              (History.measurable_pairHistoryRewardProjection
                (Action := Action) (Reward := Rat) n))
          (fun n : Nat =>
            (source.hstate n).comp
              (History.measurable_pairHistoryRewardProjection
                (Action := Action) (Reward := Rat) n))
          i
          (History.finitePairHistoryOfTrace
            (action omega) (reward omega) i))
      (MeasureTheory.ae
        (mu.trim
          ((History.historyFiltrationSucc action reward haction hreward).le
            i))) := by
  exact
    ConditionalExpectationReward.actionRewardHistoryStepKernelFamily_pair_map_eq_historyFiltrationSucc_finitePairHistoryOfTrace_of_generatedActionRandomPairRawBoundMeanBoundedSource
      (mOmega := mOmega)
      mu action rewardKernel policy context state mean varianceProxy
      defaultAction reward haction hreward rewardLo rewardHi meanLo meanHi
      source i

example {Omega Context State Action : Type}
    [mOmega : MeasurableSpace Omega] [StandardBorelSpace Omega]
    [MeasurableSpace Context] [MeasurableSpace State]
    [MeasurableSpace Action] [MeasurableSingletonClass Action]
    [Countable Action]
    (mu : MeasureTheory.Measure Omega) [MeasureTheory.IsFiniteMeasure mu]
    (action : Omega -> ActionTrace Action)
    (rewardKernel : RewardKernel.MarkovRewardKernel (Prod Context Action) Rat)
    (policy : Nat -> Policy.MeasurablePolicy State Action)
    (context : (n : Nat) -> ((j : Finset.Iic n) -> Rat) -> Context)
    (state : (n : Nat) -> ((j : Finset.Iic n) -> Rat) -> State)
    (mean : Context -> Action -> Rat)
    (varianceProxy : Context -> Action -> NNReal)
    (defaultAction : Action)
    (reward : Omega -> RewardTrace Rat)
    (haction : forall t : Nat,
      Measurable (fun omega : Omega => action omega t))
    (hreward : forall t : Nat,
      Measurable (fun omega : Omega => reward omega t))
    (rewardLo rewardHi meanLo meanHi : Nat -> Real)
    (source :
      ConditionalExpectationReward.GeneratedActionRandomPairRawBoundMeanBoundedSource
        mu action rewardKernel policy context state mean varianceProxy
        defaultAction reward haction hreward rewardLo rewardHi meanLo meanHi)
    (i : Nat) :
    Filter.Eventually
      (fun omega : Omega =>
        @MeasureTheory.Measure.map Omega ((j : Finset.Iic (i + 1)) -> Prod Action Rat)
          mOmega inferInstance
          (fun y : Omega =>
            History.finitePairHistoryOfTrace (action y) (reward y) (i + 1))
          (@ProbabilityTheory.condExpKernel Omega mOmega _ mu _
            ((History.historyFiltrationSucc action reward haction hreward) i)
            omega) =
        RewardKernel.actionRewardPartialTrajectoryKernel rewardKernel policy
          (fun n history =>
            context n (History.pairHistoryRewardProjection history))
          (fun n history =>
            state n (History.pairHistoryRewardProjection history))
          (fun n : Nat =>
            (source.hcontext n).comp
              (History.measurable_pairHistoryRewardProjection
                (Action := Action) (Reward := Rat) n))
          (fun n : Nat =>
            (source.hstate n).comp
              (History.measurable_pairHistoryRewardProjection
                (Action := Action) (Reward := Rat) n))
          i (i + 1)
          (History.finitePairHistoryOfTrace
            (action omega) (reward omega) i))
      (MeasureTheory.ae
        (mu.trim
          ((History.historyFiltrationSucc action reward haction hreward).le
            i))) := by
  exact
    ConditionalExpectationReward.actionRewardPartialTrajectoryKernel_map_eq_historyFiltrationSucc_finitePairHistoryOfTrace_of_generatedActionRandomPairRawBoundMeanBoundedSource
      (mOmega := mOmega)
      mu action rewardKernel policy context state mean varianceProxy
      defaultAction reward haction hreward rewardLo rewardHi meanLo meanHi
      source i

example {Omega Context State Action : Type}
    [mOmega : MeasurableSpace Omega] [StandardBorelSpace Omega]
    [MeasurableSpace Context] [MeasurableSpace State]
    [MeasurableSpace Action] [MeasurableSingletonClass Action]
    [Countable Action]
    (mu : MeasureTheory.Measure Omega) [MeasureTheory.IsFiniteMeasure mu]
    (action : Omega -> ActionTrace Action)
    (rewardKernel : RewardKernel.MarkovRewardKernel (Prod Context Action) Rat)
    (policy : Nat -> Policy.MeasurablePolicy State Action)
    (context : (n : Nat) -> ((j : Finset.Iic n) -> Rat) -> Context)
    (state : (n : Nat) -> ((j : Finset.Iic n) -> Rat) -> State)
    (mean : Context -> Action -> Rat)
    (varianceProxy : Context -> Action -> NNReal)
    (defaultAction : Action)
    (reward : Omega -> RewardTrace Rat)
    (haction : forall t : Nat,
      Measurable (fun omega : Omega => action omega t))
    (hreward : forall t : Nat,
      Measurable (fun omega : Omega => reward omega t))
    (rewardLo rewardHi meanLo meanHi : Nat -> Real)
    (source :
      ConditionalExpectationReward.GeneratedActionRandomPairRawBoundMeanBoundedSource
        mu action rewardKernel policy context state mean varianceProxy
        defaultAction reward haction hreward rewardLo rewardHi meanLo meanHi)
    (i : Nat) :
    Filter.EventuallyEq (MeasureTheory.ae mu)
      (@MeasureTheory.condExp Omega Real
        ((History.historyFiltrationSucc action reward haction hreward) i)
        mOmega _ _ _ mu
        (fun omega : Omega =>
          (((reward omega (i + 1) -
            mean
              (context i
                (History.finiteRewardHistoryOfTrace (reward omega) i))
              ((policy i).action
                (state i
                  (History.finiteRewardHistoryOfTrace (reward omega) i))) :
                Rat) : Real))))
      (fun _omega : Omega => (0 : Real)) := by
  exact
    ConditionalExpectationReward.centeredReward_succ_condExp_eq_zero_of_generatedActionRandomPairRawBoundMeanBoundedSource
      (mOmega := mOmega)
      mu action rewardKernel policy context state mean varianceProxy
      defaultAction reward haction hreward rewardLo rewardHi meanLo meanHi
      source i

example {Omega Context State Action : Type}
    [mOmega : MeasurableSpace Omega]
    [MeasurableSpace Context] [MeasurableSpace State]
    [MeasurableSpace Action]
    (mu : MeasureTheory.Measure Omega)
    (policy : Nat -> Policy.MeasurablePolicy State Action)
    (context : (n : Nat) -> ((j : Finset.Iic n) -> Rat) -> Context)
    (state : (n : Nat) -> ((j : Finset.Iic n) -> Rat) -> State)
    (mean : Context -> Action -> Rat)
    (reward : Omega -> RewardTrace Rat)
    (hreward : forall t : Nat,
      Measurable (fun omega : Omega => reward omega t))
    (hcontext : forall n : Nat, Measurable (context n))
    (hstate : forall n : Nat, Measurable (state n))
    (hmean :
      Measurable (fun pair : Prod Context Action => mean pair.1 pair.2))
    (i : Nat) :
    AEMeasurable
      (fun omega : Omega =>
        (((mean
          (context i
            (History.finiteRewardHistoryOfTrace (reward omega) i))
          ((policy i).action
            (state i
              (History.finiteRewardHistoryOfTrace (reward omega) i))) :
            Rat) : Real))) mu := by
  exact
    ConditionalExpectationReward.selectedMean_succ_aemeasurable_of_measurable_mean
      (mOmega := mOmega) mu policy context state mean reward hreward
      hcontext hstate hmean i

example {Omega Context State Action : Type}
    [mOmega : MeasurableSpace Omega] [StandardBorelSpace Omega]
    [MeasurableSpace Context] [MeasurableSpace State]
    [MeasurableSpace Action] [MeasurableSingletonClass Action]
    [Countable Action]
    (mu : MeasureTheory.Measure Omega) [MeasureTheory.IsFiniteMeasure mu]
    (action : Omega -> ActionTrace Action)
    (rewardKernel : RewardKernel.MarkovRewardKernel (Prod Context Action) Rat)
    (policy : Nat -> Policy.MeasurablePolicy State Action)
    (context : (n : Nat) -> ((j : Finset.Iic n) -> Rat) -> Context)
    (state : (n : Nat) -> ((j : Finset.Iic n) -> Rat) -> State)
    (mean : Context -> Action -> Rat)
    (varianceProxy : Context -> Action -> NNReal)
    (defaultAction : Action)
    (reward : Omega -> RewardTrace Rat)
    (haction : forall t : Nat,
      Measurable (fun omega : Omega => action omega t))
    (hreward : forall t : Nat,
      Measurable (fun omega : Omega => reward omega t))
    (rewardLo rewardHi meanLo meanHi : Nat -> Real)
    (source :
      ConditionalExpectationReward.GeneratedActionRandomPairRawBoundMeasurableMeanBoundedSource
        mu action rewardKernel policy context state mean varianceProxy
        defaultAction reward haction hreward rewardLo rewardHi meanLo meanHi) :
    ConditionalExpectationReward.GeneratedActionRandomPairRawBoundMeanBoundedSource
      mu action rewardKernel policy context state mean varianceProxy
      defaultAction reward haction hreward rewardLo rewardHi meanLo meanHi := by
  exact
    ConditionalExpectationReward.generatedActionRandomPairRawBoundMeanBoundedSource_of_rawBoundMeasurableMeanBoundedSource
      (mOmega := mOmega)
      mu action rewardKernel policy context state mean varianceProxy
      defaultAction reward haction hreward rewardLo rewardHi meanLo meanHi
      source

example {Omega Context State Action : Type}
    [mOmega : MeasurableSpace Omega] [StandardBorelSpace Omega]
    [MeasurableSpace Context] [MeasurableSpace State]
    [MeasurableSpace Action] [MeasurableSingletonClass Action]
    [Countable Action]
    (mu : MeasureTheory.Measure Omega) [MeasureTheory.IsFiniteMeasure mu]
    (action : Omega -> ActionTrace Action)
    (rewardKernel : RewardKernel.MarkovRewardKernel (Prod Context Action) Rat)
    (policy : Nat -> Policy.MeasurablePolicy State Action)
    (context : (n : Nat) -> ((j : Finset.Iic n) -> Rat) -> Context)
    (state : (n : Nat) -> ((j : Finset.Iic n) -> Rat) -> State)
    (mean : Context -> Action -> Rat)
    (varianceProxy : Context -> Action -> NNReal)
    (defaultAction : Action)
    (reward : Omega -> RewardTrace Rat)
    (haction : forall t : Nat,
      Measurable (fun omega : Omega => action omega t))
    (hreward : forall t : Nat,
      Measurable (fun omega : Omega => reward omega t))
    (rewardLo rewardHi meanLo meanHi : Nat -> Real)
    (source :
      ConditionalExpectationReward.GeneratedActionRandomPairRawBoundMeasurableMeanBoundedSource
        mu action rewardKernel policy context state mean varianceProxy
        defaultAction reward haction hreward rewardLo rewardHi meanLo meanHi) :
    ConditionalExpectationReward.GeneratedActionActualRewardMapSource
      mu action rewardKernel policy context state defaultAction reward
      haction hreward := by
  exact
    ConditionalExpectationReward.generatedActionActualRewardMapSource_of_randomPairRawBoundMeasurableMeanBoundedSource
      (mOmega := mOmega)
      mu action rewardKernel policy context state mean varianceProxy
      defaultAction reward haction hreward rewardLo rewardHi meanLo meanHi
      source

example {Omega Context State Action : Type}
    [mOmega : MeasurableSpace Omega] [StandardBorelSpace Omega]
    [MeasurableSpace Context] [MeasurableSpace State]
    [MeasurableSpace Action] [MeasurableSingletonClass Action]
    [Countable Action]
    (mu : MeasureTheory.Measure Omega) [MeasureTheory.IsFiniteMeasure mu]
    (action : Omega -> ActionTrace Action)
    (rewardKernel : RewardKernel.MarkovRewardKernel (Prod Context Action) Rat)
    (policy : Nat -> Policy.MeasurablePolicy State Action)
    (context : (n : Nat) -> ((j : Finset.Iic n) -> Rat) -> Context)
    (state : (n : Nat) -> ((j : Finset.Iic n) -> Rat) -> State)
    (mean : Context -> Action -> Rat)
    (varianceProxy : Context -> Action -> NNReal)
    (defaultAction : Action)
    (reward : Omega -> RewardTrace Rat)
    (haction : forall t : Nat,
      Measurable (fun omega : Omega => action omega t))
    (hreward : forall t : Nat,
      Measurable (fun omega : Omega => reward omega t))
    (rewardLo rewardHi meanLo meanHi : Nat -> Real)
    (source :
      ConditionalExpectationReward.GeneratedActionRandomPairRawBoundMeasurableMeanBoundedSource
        mu action rewardKernel policy context state mean varianceProxy
        defaultAction reward haction hreward rewardLo rewardHi meanLo meanHi)
    (i : Nat) :
    AEMeasurable
      (fun omega : Omega =>
        (((reward omega (i + 1) -
          mean
            (context i
              (History.finiteRewardHistoryOfTrace (reward omega) i))
            ((policy i).action
              (state i
                (History.finiteRewardHistoryOfTrace (reward omega) i))) :
            Rat) : Real))) mu := by
  exact
    ConditionalExpectationReward.centeredReward_succ_aemeasurable_of_generatedActionRandomPairRawBoundMeasurableMeanBoundedSource
      (mOmega := mOmega)
      mu action rewardKernel policy context state mean varianceProxy
      defaultAction reward haction hreward rewardLo rewardHi meanLo meanHi
      source i

example {Omega Context State Action : Type}
    [mOmega : MeasurableSpace Omega] [StandardBorelSpace Omega]
    [MeasurableSpace Context] [MeasurableSpace State]
    [MeasurableSpace Action] [MeasurableSingletonClass Action]
    [Countable Action]
    (mu : MeasureTheory.Measure Omega) [MeasureTheory.IsFiniteMeasure mu]
    (action : Omega -> ActionTrace Action)
    (rewardKernel : RewardKernel.MarkovRewardKernel (Prod Context Action) Rat)
    (policy : Nat -> Policy.MeasurablePolicy State Action)
    (context : (n : Nat) -> ((j : Finset.Iic n) -> Rat) -> Context)
    (state : (n : Nat) -> ((j : Finset.Iic n) -> Rat) -> State)
    (mean : Context -> Action -> Rat)
    (varianceProxy : Context -> Action -> NNReal)
    (defaultAction : Action)
    (reward : Omega -> RewardTrace Rat)
    (haction : forall t : Nat,
      Measurable (fun omega : Omega => action omega t))
    (hreward : forall t : Nat,
      Measurable (fun omega : Omega => reward omega t))
    (rewardLo rewardHi meanLo meanHi : Nat -> Real)
    (source :
      ConditionalExpectationReward.GeneratedActionRandomPairRawBoundMeasurableMeanBoundedSource
        mu action rewardKernel policy context state mean varianceProxy
        defaultAction reward haction hreward rewardLo rewardHi meanLo meanHi)
    (i : Nat) :
    Filter.Eventually
      (fun omega : Omega =>
        Set.Icc (rewardLo i - meanHi i) (rewardHi i - meanLo i)
          (((reward omega (i + 1) -
            mean
              (context i
                (History.finiteRewardHistoryOfTrace (reward omega) i))
              ((policy i).action
                (state i
                  (History.finiteRewardHistoryOfTrace (reward omega) i))) :
              Rat) : Real)))
      (MeasureTheory.ae mu) := by
  exact
    ConditionalExpectationReward.centeredReward_succ_bound_of_generatedActionRandomPairRawBoundMeasurableMeanBoundedSource
      (mOmega := mOmega)
      mu action rewardKernel policy context state mean varianceProxy
      defaultAction reward haction hreward rewardLo rewardHi meanLo meanHi
      source i

example {Omega Context State Action : Type}
    [mOmega : MeasurableSpace Omega] [StandardBorelSpace Omega]
    [MeasurableSpace Context] [MeasurableSpace State]
    [MeasurableSpace Action] [MeasurableSingletonClass Action]
    [Countable Action]
    (mu : MeasureTheory.Measure Omega) [MeasureTheory.IsFiniteMeasure mu]
    (action : Omega -> ActionTrace Action)
    (rewardKernel : RewardKernel.MarkovRewardKernel (Prod Context Action) Rat)
    (policy : Nat -> Policy.MeasurablePolicy State Action)
    (context : (n : Nat) -> ((j : Finset.Iic n) -> Rat) -> Context)
    (state : (n : Nat) -> ((j : Finset.Iic n) -> Rat) -> State)
    (mean : Context -> Action -> Rat)
    (varianceProxy : Context -> Action -> NNReal)
    (defaultAction : Action)
    (reward : Omega -> RewardTrace Rat)
    (haction : forall t : Nat,
      Measurable (fun omega : Omega => action omega t))
    (hreward : forall t : Nat,
      Measurable (fun omega : Omega => reward omega t))
    (rewardLo rewardHi meanLo meanHi : Nat -> Real)
    (source :
      ConditionalExpectationReward.GeneratedActionRandomPairRawBoundMeasurableMeanBoundedSource
        mu action rewardKernel policy context state mean varianceProxy
        defaultAction reward haction hreward rewardLo rewardHi meanLo meanHi)
    (i : Nat) :
    MeasureTheory.Integrable
      (fun omega : Omega =>
        (((reward omega (i + 1) -
          mean
            (context i
              (History.finiteRewardHistoryOfTrace (reward omega) i))
            ((policy i).action
              (state i
                (History.finiteRewardHistoryOfTrace (reward omega) i))) :
              Rat) : Real))) mu := by
  exact
    ConditionalExpectationReward.centeredReward_succ_integrable_of_generatedActionRandomPairRawBoundMeasurableMeanBoundedSource
      (mOmega := mOmega)
      mu action rewardKernel policy context state mean varianceProxy
      defaultAction reward haction hreward rewardLo rewardHi meanLo meanHi
      source i

example {Omega Context State Action : Type}
    [mOmega : MeasurableSpace Omega] [StandardBorelSpace Omega]
    [MeasurableSpace Context] [MeasurableSpace State]
    [MeasurableSpace Action] [MeasurableSingletonClass Action]
    [Countable Action]
    (mu : MeasureTheory.Measure Omega) [MeasureTheory.IsFiniteMeasure mu]
    (action : Omega -> ActionTrace Action)
    (rewardKernel : RewardKernel.MarkovRewardKernel (Prod Context Action) Rat)
    (policy : Nat -> Policy.MeasurablePolicy State Action)
    (context : (n : Nat) -> ((j : Finset.Iic n) -> Rat) -> Context)
    (state : (n : Nat) -> ((j : Finset.Iic n) -> Rat) -> State)
    (mean : Context -> Action -> Rat)
    (varianceProxy : Context -> Action -> NNReal)
    (defaultAction : Action)
    (reward : Omega -> RewardTrace Rat)
    (haction : forall t : Nat,
      Measurable (fun omega : Omega => action omega t))
    (hreward : forall t : Nat,
      Measurable (fun omega : Omega => reward omega t))
    (rewardLo rewardHi meanLo meanHi : Nat -> Real)
    (source :
      ConditionalExpectationReward.GeneratedActionRandomPairRawBoundMeasurableMeanBoundedSource
        mu action rewardKernel policy context state mean varianceProxy
        defaultAction reward haction hreward rewardLo rewardHi meanLo meanHi)
    (i : Nat) :
    Filter.Eventually
      (fun omega : Omega =>
        @MeasureTheory.Measure.map Omega (Prod Action Rat) mOmega inferInstance
          (fun y : Omega => (action y (i + 1), reward y (i + 1)))
          (@ProbabilityTheory.condExpKernel Omega mOmega _ mu _
            ((History.historyFiltrationSucc action reward haction hreward) i)
            omega) =
        RewardKernel.actionRewardHistoryStepKernelFamily rewardKernel policy
          (fun n history =>
            context n (History.pairHistoryRewardProjection history))
          (fun n history =>
            state n (History.pairHistoryRewardProjection history))
          (fun n : Nat =>
            (source.hcontext n).comp
              (History.measurable_pairHistoryRewardProjection
                (Action := Action) (Reward := Rat) n))
          (fun n : Nat =>
            (source.hstate n).comp
              (History.measurable_pairHistoryRewardProjection
                (Action := Action) (Reward := Rat) n))
          i
          (History.finitePairHistoryOfTrace
            (action omega) (reward omega) i))
      (MeasureTheory.ae
        (mu.trim
          ((History.historyFiltrationSucc action reward haction hreward).le
            i))) := by
  exact
    ConditionalExpectationReward.actionRewardHistoryStepKernelFamily_pair_map_eq_historyFiltrationSucc_finitePairHistoryOfTrace_of_generatedActionRandomPairRawBoundMeasurableMeanBoundedSource
      (mOmega := mOmega)
      mu action rewardKernel policy context state mean varianceProxy
      defaultAction reward haction hreward rewardLo rewardHi meanLo meanHi
      source i

example {Omega Context State Action : Type}
    [mOmega : MeasurableSpace Omega] [StandardBorelSpace Omega]
    [MeasurableSpace Context] [MeasurableSpace State]
    [MeasurableSpace Action] [MeasurableSingletonClass Action]
    [Countable Action]
    (mu : MeasureTheory.Measure Omega) [MeasureTheory.IsFiniteMeasure mu]
    (action : Omega -> ActionTrace Action)
    (rewardKernel : RewardKernel.MarkovRewardKernel (Prod Context Action) Rat)
    (policy : Nat -> Policy.MeasurablePolicy State Action)
    (context : (n : Nat) -> ((j : Finset.Iic n) -> Rat) -> Context)
    (state : (n : Nat) -> ((j : Finset.Iic n) -> Rat) -> State)
    (mean : Context -> Action -> Rat)
    (varianceProxy : Context -> Action -> NNReal)
    (defaultAction : Action)
    (reward : Omega -> RewardTrace Rat)
    (haction : forall t : Nat,
      Measurable (fun omega : Omega => action omega t))
    (hreward : forall t : Nat,
      Measurable (fun omega : Omega => reward omega t))
    (rewardLo rewardHi meanLo meanHi : Nat -> Real)
    (source :
      ConditionalExpectationReward.GeneratedActionRandomPairRawBoundMeasurableMeanBoundedSource
        mu action rewardKernel policy context state mean varianceProxy
        defaultAction reward haction hreward rewardLo rewardHi meanLo meanHi)
    (i : Nat) :
    Filter.Eventually
      (fun omega : Omega =>
        @MeasureTheory.Measure.map Omega ((j : Finset.Iic (i + 1)) -> Prod Action Rat)
          mOmega inferInstance
          (fun y : Omega =>
            History.finitePairHistoryOfTrace (action y) (reward y) (i + 1))
          (@ProbabilityTheory.condExpKernel Omega mOmega _ mu _
            ((History.historyFiltrationSucc action reward haction hreward) i)
            omega) =
        RewardKernel.actionRewardPartialTrajectoryKernel rewardKernel policy
          (fun n history =>
            context n (History.pairHistoryRewardProjection history))
          (fun n history =>
            state n (History.pairHistoryRewardProjection history))
          (fun n : Nat =>
            (source.hcontext n).comp
              (History.measurable_pairHistoryRewardProjection
                (Action := Action) (Reward := Rat) n))
          (fun n : Nat =>
            (source.hstate n).comp
              (History.measurable_pairHistoryRewardProjection
                (Action := Action) (Reward := Rat) n))
          i (i + 1)
          (History.finitePairHistoryOfTrace
            (action omega) (reward omega) i))
      (MeasureTheory.ae
        (mu.trim
          ((History.historyFiltrationSucc action reward haction hreward).le
            i))) := by
  exact
    ConditionalExpectationReward.actionRewardPartialTrajectoryKernel_map_eq_historyFiltrationSucc_finitePairHistoryOfTrace_of_generatedActionRandomPairRawBoundMeasurableMeanBoundedSource
      (mOmega := mOmega)
      mu action rewardKernel policy context state mean varianceProxy
      defaultAction reward haction hreward rewardLo rewardHi meanLo meanHi
      source i

example {Omega Context State Action : Type}
    [mOmega : MeasurableSpace Omega] [StandardBorelSpace Omega]
    [MeasurableSpace Context] [MeasurableSpace State]
    [MeasurableSpace Action] [MeasurableSingletonClass Action]
    [Countable Action]
    (mu : MeasureTheory.Measure Omega) [MeasureTheory.IsFiniteMeasure mu]
    (action : Omega -> ActionTrace Action)
    (rewardKernel : RewardKernel.MarkovRewardKernel (Prod Context Action) Rat)
    (policy : Nat -> Policy.MeasurablePolicy State Action)
    (context : (n : Nat) -> ((j : Finset.Iic n) -> Rat) -> Context)
    (state : (n : Nat) -> ((j : Finset.Iic n) -> Rat) -> State)
    (mean : Context -> Action -> Rat)
    (varianceProxy : Context -> Action -> NNReal)
    (defaultAction : Action)
    (reward : Omega -> RewardTrace Rat)
    (haction : forall t : Nat,
      Measurable (fun omega : Omega => action omega t))
    (hreward : forall t : Nat,
      Measurable (fun omega : Omega => reward omega t))
    (rewardLo rewardHi meanLo meanHi : Nat -> Real)
    (source :
      ConditionalExpectationReward.GeneratedActionRandomPairRawBoundMeasurableMeanBoundedSource
        mu action rewardKernel policy context state mean varianceProxy
        defaultAction reward haction hreward rewardLo rewardHi meanLo meanHi)
    (i : Nat) :
    Filter.EventuallyEq (MeasureTheory.ae mu)
      (@MeasureTheory.condExp Omega Real
        ((History.historyFiltrationSucc action reward haction hreward) i)
        mOmega _ _ _ mu
        (fun omega : Omega =>
          (((reward omega (i + 1) -
            mean
              (context i
                (History.finiteRewardHistoryOfTrace (reward omega) i))
              ((policy i).action
                (state i
                  (History.finiteRewardHistoryOfTrace (reward omega) i))) :
                Rat) : Real))))
      (fun _omega : Omega => (0 : Real)) := by
  exact
    ConditionalExpectationReward.centeredReward_succ_condExp_eq_zero_of_generatedActionRandomPairRawBoundMeasurableMeanBoundedSource
      (mOmega := mOmega)
      mu action rewardKernel policy context state mean varianceProxy
      defaultAction reward haction hreward rewardLo rewardHi meanLo meanHi
      source i

example {Omega Context State Action : Type}
    [mOmega : MeasurableSpace Omega]
    [MeasurableSpace Context] [MeasurableSpace State]
    [MeasurableSpace Action]
    (mu : MeasureTheory.Measure Omega)
    (policy : Nat -> Policy.MeasurablePolicy State Action)
    (context : (n : Nat) -> ((j : Finset.Iic n) -> Rat) -> Context)
    (state : (n : Nat) -> ((j : Finset.Iic n) -> Rat) -> State)
    (mean : Context -> Action -> Rat)
    (reward : Omega -> RewardTrace Rat)
    (meanLo meanHi : Nat -> Real)
    (hmean_bound :
      forall i : Nat, forall context : Context, forall action : Action,
        Set.Icc (meanLo i) (meanHi i)
          (((mean context action : Rat) : Real)))
    (i : Nat) :
    Filter.Eventually
      (fun omega : Omega =>
        Set.Icc (meanLo i) (meanHi i)
          (((mean
            (context i
              (History.finiteRewardHistoryOfTrace (reward omega) i))
            ((policy i).action
              (state i
                (History.finiteRewardHistoryOfTrace (reward omega) i))) :
            Rat) : Real)))
      (MeasureTheory.ae mu) := by
  exact
    ConditionalExpectationReward.selectedMean_succ_bound_of_mean_range_bound
      (mOmega := mOmega) mu policy context state mean reward meanLo meanHi
      hmean_bound i

example {Omega Context State Action : Type}
    [mOmega : MeasurableSpace Omega] [StandardBorelSpace Omega]
    [MeasurableSpace Context] [MeasurableSpace State]
    [MeasurableSpace Action] [MeasurableSingletonClass Action]
    [Countable Action]
    (mu : MeasureTheory.Measure Omega) [MeasureTheory.IsFiniteMeasure mu]
    (action : Omega -> ActionTrace Action)
    (rewardKernel : RewardKernel.MarkovRewardKernel (Prod Context Action) Rat)
    (policy : Nat -> Policy.MeasurablePolicy State Action)
    (context : (n : Nat) -> ((j : Finset.Iic n) -> Rat) -> Context)
    (state : (n : Nat) -> ((j : Finset.Iic n) -> Rat) -> State)
    (mean : Context -> Action -> Rat)
    (varianceProxy : Context -> Action -> NNReal)
    (defaultAction : Action)
    (reward : Omega -> RewardTrace Rat)
    (haction : forall t : Nat,
      Measurable (fun omega : Omega => action omega t))
    (hreward : forall t : Nat,
      Measurable (fun omega : Omega => reward omega t))
    (rewardLo rewardHi meanLo meanHi : Nat -> Real)
    (source :
      ConditionalExpectationReward.GeneratedActionRandomPairRawBoundMeasurableMeanRangeBoundedSource
        mu action rewardKernel policy context state mean varianceProxy
        defaultAction reward haction hreward rewardLo rewardHi meanLo meanHi) :
    ConditionalExpectationReward.GeneratedActionRandomPairRawBoundMeasurableMeanBoundedSource
      mu action rewardKernel policy context state mean varianceProxy
      defaultAction reward haction hreward rewardLo rewardHi meanLo meanHi := by
  exact
    ConditionalExpectationReward.generatedActionRandomPairRawBoundMeasurableMeanBoundedSource_of_rawBoundMeasurableMeanRangeBoundedSource
      (mOmega := mOmega)
      mu action rewardKernel policy context state mean varianceProxy
      defaultAction reward haction hreward rewardLo rewardHi meanLo meanHi
      source

example {Omega Context State Action : Type}
    [mOmega : MeasurableSpace Omega] [StandardBorelSpace Omega]
    [MeasurableSpace Context] [MeasurableSpace State]
    [MeasurableSpace Action] [MeasurableSingletonClass Action]
    [Countable Action]
    (mu : MeasureTheory.Measure Omega) [MeasureTheory.IsFiniteMeasure mu]
    (action : Omega -> ActionTrace Action)
    (rewardKernel : RewardKernel.MarkovRewardKernel (Prod Context Action) Rat)
    (policy : Nat -> Policy.MeasurablePolicy State Action)
    (context : (n : Nat) -> ((j : Finset.Iic n) -> Rat) -> Context)
    (state : (n : Nat) -> ((j : Finset.Iic n) -> Rat) -> State)
    (mean : Context -> Action -> Rat)
    (varianceProxy : Context -> Action -> NNReal)
    (defaultAction : Action)
    (reward : Omega -> RewardTrace Rat)
    (haction : forall t : Nat,
      Measurable (fun omega : Omega => action omega t))
    (hreward : forall t : Nat,
      Measurable (fun omega : Omega => reward omega t))
    (rewardLo rewardHi meanLo meanHi : Nat -> Real)
    (source :
      ConditionalExpectationReward.GeneratedActionRandomPairRawBoundMeasurableMeanRangeBoundedSource
        mu action rewardKernel policy context state mean varianceProxy
        defaultAction reward haction hreward rewardLo rewardHi meanLo meanHi) :
    ConditionalExpectationReward.GeneratedActionActualRewardMapSource
      mu action rewardKernel policy context state defaultAction reward
      haction hreward := by
  exact
    ConditionalExpectationReward.generatedActionActualRewardMapSource_of_randomPairRawBoundMeasurableMeanRangeBoundedSource
      (mOmega := mOmega)
      mu action rewardKernel policy context state mean varianceProxy
      defaultAction reward haction hreward rewardLo rewardHi meanLo meanHi
      source

example {Omega Context State Action : Type}
    [mOmega : MeasurableSpace Omega] [StandardBorelSpace Omega]
    [MeasurableSpace Context] [MeasurableSpace State]
    [MeasurableSpace Action] [MeasurableSingletonClass Action]
    [Countable Action]
    (mu : MeasureTheory.Measure Omega) [MeasureTheory.IsFiniteMeasure mu]
    (action : Omega -> ActionTrace Action)
    (rewardKernel : RewardKernel.MarkovRewardKernel (Prod Context Action) Rat)
    (policy : Nat -> Policy.MeasurablePolicy State Action)
    (context : (n : Nat) -> ((j : Finset.Iic n) -> Rat) -> Context)
    (state : (n : Nat) -> ((j : Finset.Iic n) -> Rat) -> State)
    (mean : Context -> Action -> Rat)
    (varianceProxy : Context -> Action -> NNReal)
    (defaultAction : Action)
    (reward : Omega -> RewardTrace Rat)
    (haction : forall t : Nat,
      Measurable (fun omega : Omega => action omega t))
    (hreward : forall t : Nat,
      Measurable (fun omega : Omega => reward omega t))
    (rewardLo rewardHi meanLo meanHi : Nat -> Real)
    (source :
      ConditionalExpectationReward.GeneratedActionRandomPairRawBoundMeasurableMeanRangeBoundedSource
        mu action rewardKernel policy context state mean varianceProxy
        defaultAction reward haction hreward rewardLo rewardHi meanLo meanHi)
    (i : Nat) :
    AEMeasurable
      (fun omega : Omega =>
        (((reward omega (i + 1) -
          mean
            (context i
              (History.finiteRewardHistoryOfTrace (reward omega) i))
            ((policy i).action
              (state i
                (History.finiteRewardHistoryOfTrace (reward omega) i))) :
            Rat) : Real))) mu := by
  exact
    ConditionalExpectationReward.centeredReward_succ_aemeasurable_of_generatedActionRandomPairRawBoundMeasurableMeanRangeBoundedSource
      (mOmega := mOmega)
      mu action rewardKernel policy context state mean varianceProxy
      defaultAction reward haction hreward rewardLo rewardHi meanLo meanHi
      source i

example {Omega Context State Action : Type}
    [mOmega : MeasurableSpace Omega] [StandardBorelSpace Omega]
    [MeasurableSpace Context] [MeasurableSpace State]
    [MeasurableSpace Action] [MeasurableSingletonClass Action]
    [Countable Action]
    (mu : MeasureTheory.Measure Omega) [MeasureTheory.IsFiniteMeasure mu]
    (action : Omega -> ActionTrace Action)
    (rewardKernel : RewardKernel.MarkovRewardKernel (Prod Context Action) Rat)
    (policy : Nat -> Policy.MeasurablePolicy State Action)
    (context : (n : Nat) -> ((j : Finset.Iic n) -> Rat) -> Context)
    (state : (n : Nat) -> ((j : Finset.Iic n) -> Rat) -> State)
    (mean : Context -> Action -> Rat)
    (varianceProxy : Context -> Action -> NNReal)
    (defaultAction : Action)
    (reward : Omega -> RewardTrace Rat)
    (haction : forall t : Nat,
      Measurable (fun omega : Omega => action omega t))
    (hreward : forall t : Nat,
      Measurable (fun omega : Omega => reward omega t))
    (rewardLo rewardHi meanLo meanHi : Nat -> Real)
    (source :
      ConditionalExpectationReward.GeneratedActionRandomPairRawBoundMeasurableMeanRangeBoundedSource
        mu action rewardKernel policy context state mean varianceProxy
        defaultAction reward haction hreward rewardLo rewardHi meanLo meanHi)
    (i : Nat) :
    Filter.Eventually
      (fun omega : Omega =>
        Set.Icc (rewardLo i - meanHi i) (rewardHi i - meanLo i)
          (((reward omega (i + 1) -
            mean
              (context i
                (History.finiteRewardHistoryOfTrace (reward omega) i))
              ((policy i).action
                (state i
                  (History.finiteRewardHistoryOfTrace (reward omega) i))) :
              Rat) : Real)))
      (MeasureTheory.ae mu) := by
  exact
    ConditionalExpectationReward.centeredReward_succ_bound_of_generatedActionRandomPairRawBoundMeasurableMeanRangeBoundedSource
      (mOmega := mOmega)
      mu action rewardKernel policy context state mean varianceProxy
      defaultAction reward haction hreward rewardLo rewardHi meanLo meanHi
      source i

example {Omega Context State Action : Type}
    [mOmega : MeasurableSpace Omega] [StandardBorelSpace Omega]
    [MeasurableSpace Context] [MeasurableSpace State]
    [MeasurableSpace Action] [MeasurableSingletonClass Action]
    [Countable Action]
    (mu : MeasureTheory.Measure Omega) [MeasureTheory.IsFiniteMeasure mu]
    (action : Omega -> ActionTrace Action)
    (rewardKernel : RewardKernel.MarkovRewardKernel (Prod Context Action) Rat)
    (policy : Nat -> Policy.MeasurablePolicy State Action)
    (context : (n : Nat) -> ((j : Finset.Iic n) -> Rat) -> Context)
    (state : (n : Nat) -> ((j : Finset.Iic n) -> Rat) -> State)
    (mean : Context -> Action -> Rat)
    (varianceProxy : Context -> Action -> NNReal)
    (defaultAction : Action)
    (reward : Omega -> RewardTrace Rat)
    (haction : forall t : Nat,
      Measurable (fun omega : Omega => action omega t))
    (hreward : forall t : Nat,
      Measurable (fun omega : Omega => reward omega t))
    (rewardLo rewardHi meanLo meanHi : Nat -> Real)
    (source :
      ConditionalExpectationReward.GeneratedActionRandomPairRawBoundMeasurableMeanRangeBoundedSource
        mu action rewardKernel policy context state mean varianceProxy
        defaultAction reward haction hreward rewardLo rewardHi meanLo meanHi)
    (i : Nat) :
    MeasureTheory.Integrable
      (fun omega : Omega =>
        (((reward omega (i + 1) -
          mean
            (context i
              (History.finiteRewardHistoryOfTrace (reward omega) i))
            ((policy i).action
              (state i
                (History.finiteRewardHistoryOfTrace (reward omega) i))) :
              Rat) : Real))) mu := by
  exact
    ConditionalExpectationReward.centeredReward_succ_integrable_of_generatedActionRandomPairRawBoundMeasurableMeanRangeBoundedSource
      (mOmega := mOmega)
      mu action rewardKernel policy context state mean varianceProxy
      defaultAction reward haction hreward rewardLo rewardHi meanLo meanHi
      source i

example {Omega Context State Action : Type}
    [mOmega : MeasurableSpace Omega] [StandardBorelSpace Omega]
    [MeasurableSpace Context] [MeasurableSpace State]
    [MeasurableSpace Action] [MeasurableSingletonClass Action]
    [Countable Action]
    (mu : MeasureTheory.Measure Omega) [MeasureTheory.IsFiniteMeasure mu]
    (action : Omega -> ActionTrace Action)
    (rewardKernel : RewardKernel.MarkovRewardKernel (Prod Context Action) Rat)
    (policy : Nat -> Policy.MeasurablePolicy State Action)
    (context : (n : Nat) -> ((j : Finset.Iic n) -> Rat) -> Context)
    (state : (n : Nat) -> ((j : Finset.Iic n) -> Rat) -> State)
    (mean : Context -> Action -> Rat)
    (varianceProxy : Context -> Action -> NNReal)
    (defaultAction : Action)
    (reward : Omega -> RewardTrace Rat)
    (haction : forall t : Nat,
      Measurable (fun omega : Omega => action omega t))
    (hreward : forall t : Nat,
      Measurable (fun omega : Omega => reward omega t))
    (rewardLo rewardHi meanLo meanHi : Nat -> Real)
    (source :
      ConditionalExpectationReward.GeneratedActionRandomPairRawBoundMeasurableMeanRangeBoundedSource
        mu action rewardKernel policy context state mean varianceProxy
        defaultAction reward haction hreward rewardLo rewardHi meanLo meanHi)
    (i : Nat) :
    Filter.Eventually
      (fun omega : Omega =>
        @MeasureTheory.Measure.map Omega (Prod Action Rat) mOmega inferInstance
          (fun y : Omega => (action y (i + 1), reward y (i + 1)))
          (@ProbabilityTheory.condExpKernel Omega mOmega _ mu _
            ((History.historyFiltrationSucc action reward haction hreward) i)
            omega) =
        RewardKernel.actionRewardHistoryStepKernelFamily rewardKernel policy
          (fun n history =>
            context n (History.pairHistoryRewardProjection history))
          (fun n history =>
            state n (History.pairHistoryRewardProjection history))
          (fun n : Nat =>
            (source.hcontext n).comp
              (History.measurable_pairHistoryRewardProjection
                (Action := Action) (Reward := Rat) n))
          (fun n : Nat =>
            (source.hstate n).comp
              (History.measurable_pairHistoryRewardProjection
                (Action := Action) (Reward := Rat) n))
          i
          (History.finitePairHistoryOfTrace
            (action omega) (reward omega) i))
      (MeasureTheory.ae
        (mu.trim
          ((History.historyFiltrationSucc action reward haction hreward).le
            i))) := by
  exact
    ConditionalExpectationReward.actionRewardHistoryStepKernelFamily_pair_map_eq_historyFiltrationSucc_finitePairHistoryOfTrace_of_generatedActionRandomPairRawBoundMeasurableMeanRangeBoundedSource
      (mOmega := mOmega)
      mu action rewardKernel policy context state mean varianceProxy
      defaultAction reward haction hreward rewardLo rewardHi meanLo meanHi
      source i

example {Omega Context State Action : Type}
    [mOmega : MeasurableSpace Omega] [StandardBorelSpace Omega]
    [MeasurableSpace Context] [MeasurableSpace State]
    [MeasurableSpace Action] [MeasurableSingletonClass Action]
    [Countable Action]
    (mu : MeasureTheory.Measure Omega) [MeasureTheory.IsFiniteMeasure mu]
    (action : Omega -> ActionTrace Action)
    (rewardKernel : RewardKernel.MarkovRewardKernel (Prod Context Action) Rat)
    (policy : Nat -> Policy.MeasurablePolicy State Action)
    (context : (n : Nat) -> ((j : Finset.Iic n) -> Rat) -> Context)
    (state : (n : Nat) -> ((j : Finset.Iic n) -> Rat) -> State)
    (mean : Context -> Action -> Rat)
    (varianceProxy : Context -> Action -> NNReal)
    (defaultAction : Action)
    (reward : Omega -> RewardTrace Rat)
    (haction : forall t : Nat,
      Measurable (fun omega : Omega => action omega t))
    (hreward : forall t : Nat,
      Measurable (fun omega : Omega => reward omega t))
    (rewardLo rewardHi meanLo meanHi : Nat -> Real)
    (source :
      ConditionalExpectationReward.GeneratedActionRandomPairRawBoundMeasurableMeanRangeBoundedSource
        mu action rewardKernel policy context state mean varianceProxy
        defaultAction reward haction hreward rewardLo rewardHi meanLo meanHi)
    (i : Nat) :
    Filter.Eventually
      (fun omega : Omega =>
        @MeasureTheory.Measure.map Omega ((j : Finset.Iic (i + 1)) -> Prod Action Rat)
          mOmega inferInstance
          (fun y : Omega =>
            History.finitePairHistoryOfTrace (action y) (reward y) (i + 1))
          (@ProbabilityTheory.condExpKernel Omega mOmega _ mu _
            ((History.historyFiltrationSucc action reward haction hreward) i)
            omega) =
        RewardKernel.actionRewardPartialTrajectoryKernel rewardKernel policy
          (fun n history =>
            context n (History.pairHistoryRewardProjection history))
          (fun n history =>
            state n (History.pairHistoryRewardProjection history))
          (fun n : Nat =>
            (source.hcontext n).comp
              (History.measurable_pairHistoryRewardProjection
                (Action := Action) (Reward := Rat) n))
          (fun n : Nat =>
            (source.hstate n).comp
              (History.measurable_pairHistoryRewardProjection
                (Action := Action) (Reward := Rat) n))
          i (i + 1)
          (History.finitePairHistoryOfTrace
            (action omega) (reward omega) i))
      (MeasureTheory.ae
        (mu.trim
          ((History.historyFiltrationSucc action reward haction hreward).le
            i))) := by
  exact
    ConditionalExpectationReward.actionRewardPartialTrajectoryKernel_map_eq_historyFiltrationSucc_finitePairHistoryOfTrace_of_generatedActionRandomPairRawBoundMeasurableMeanRangeBoundedSource
      (mOmega := mOmega)
      mu action rewardKernel policy context state mean varianceProxy
      defaultAction reward haction hreward rewardLo rewardHi meanLo meanHi
      source i

example {Omega Context State Action : Type}
    [mOmega : MeasurableSpace Omega] [StandardBorelSpace Omega]
    [MeasurableSpace Context] [MeasurableSpace State]
    [MeasurableSpace Action] [MeasurableSingletonClass Action]
    [Countable Action]
    (mu : MeasureTheory.Measure Omega) [MeasureTheory.IsFiniteMeasure mu]
    (action : Omega -> ActionTrace Action)
    (rewardKernel : RewardKernel.MarkovRewardKernel (Prod Context Action) Rat)
    (policy : Nat -> Policy.MeasurablePolicy State Action)
    (context : (n : Nat) -> ((j : Finset.Iic n) -> Rat) -> Context)
    (state : (n : Nat) -> ((j : Finset.Iic n) -> Rat) -> State)
    (mean : Context -> Action -> Rat)
    (varianceProxy : Context -> Action -> NNReal)
    (defaultAction : Action)
    (reward : Omega -> RewardTrace Rat)
    (haction : forall t : Nat,
      Measurable (fun omega : Omega => action omega t))
    (hreward : forall t : Nat,
      Measurable (fun omega : Omega => reward omega t))
    (rewardLo rewardHi meanLo meanHi : Nat -> Real)
    (source :
      ConditionalExpectationReward.GeneratedActionRandomPairRawBoundMeasurableMeanRangeBoundedSource
        mu action rewardKernel policy context state mean varianceProxy
        defaultAction reward haction hreward rewardLo rewardHi meanLo meanHi)
    (i : Nat) :
    Filter.EventuallyEq (MeasureTheory.ae mu)
      (@MeasureTheory.condExp Omega Real
        ((History.historyFiltrationSucc action reward haction hreward) i)
        mOmega _ _ _ mu
        (fun omega : Omega =>
          (((reward omega (i + 1) -
            mean
              (context i
                (History.finiteRewardHistoryOfTrace (reward omega) i))
              ((policy i).action
                (state i
                  (History.finiteRewardHistoryOfTrace (reward omega) i))) :
                Rat) : Real))))
      (fun _omega : Omega => (0 : Real)) := by
  exact
    ConditionalExpectationReward.centeredReward_succ_condExp_eq_zero_of_generatedActionRandomPairRawBoundMeasurableMeanRangeBoundedSource
      (mOmega := mOmega)
      mu action rewardKernel policy context state mean varianceProxy
      defaultAction reward haction hreward rewardLo rewardHi meanLo meanHi
      source i

example {Omega : Type}
    [mOmega : MeasurableSpace Omega]
    (mu : MeasureTheory.Measure Omega)
    (reward : Omega -> RewardTrace Rat)
    (rewardLo rewardHi : Nat -> Real)
    (hreward_bound :
      forall i : Nat, forall omega : Omega,
        Set.Icc (rewardLo i) (rewardHi i)
          (((reward omega (i + 1) : Rat) : Real)))
    (i : Nat) :
    Filter.Eventually
      (fun omega : Omega =>
        Set.Icc (rewardLo i) (rewardHi i)
          (((reward omega (i + 1) : Rat) : Real)))
      (MeasureTheory.ae mu) := by
  exact
    ConditionalExpectationReward.rawReward_succ_bound_of_reward_range_bound
      (mOmega := mOmega) mu reward rewardLo rewardHi hreward_bound i

example {Omega Context State Action : Type}
    [mOmega : MeasurableSpace Omega] [StandardBorelSpace Omega]
    [MeasurableSpace Context] [MeasurableSpace State]
    [MeasurableSpace Action] [MeasurableSingletonClass Action]
    [Countable Action]
    (mu : MeasureTheory.Measure Omega) [MeasureTheory.IsFiniteMeasure mu]
    (action : Omega -> ActionTrace Action)
    (rewardKernel : RewardKernel.MarkovRewardKernel (Prod Context Action) Rat)
    (policy : Nat -> Policy.MeasurablePolicy State Action)
    (context : (n : Nat) -> ((j : Finset.Iic n) -> Rat) -> Context)
    (state : (n : Nat) -> ((j : Finset.Iic n) -> Rat) -> State)
    (mean : Context -> Action -> Rat)
    (varianceProxy : Context -> Action -> NNReal)
    (defaultAction : Action)
    (reward : Omega -> RewardTrace Rat)
    (haction : forall t : Nat,
      Measurable (fun omega : Omega => action omega t))
    (hreward : forall t : Nat,
      Measurable (fun omega : Omega => reward omega t))
    (rewardLo rewardHi meanLo meanHi : Nat -> Real)
    (source :
      ConditionalExpectationReward.GeneratedActionRandomPairRawRangeMeasurableMeanRangeBoundedSource
        mu action rewardKernel policy context state mean varianceProxy
        defaultAction reward haction hreward rewardLo rewardHi meanLo meanHi) :
    ConditionalExpectationReward.GeneratedActionRandomPairRawBoundMeasurableMeanRangeBoundedSource
      mu action rewardKernel policy context state mean varianceProxy
      defaultAction reward haction hreward rewardLo rewardHi meanLo meanHi := by
  exact
    ConditionalExpectationReward.generatedActionRandomPairRawBoundMeasurableMeanRangeBoundedSource_of_rawRangeMeasurableMeanRangeBoundedSource
      (mOmega := mOmega)
      mu action rewardKernel policy context state mean varianceProxy
      defaultAction reward haction hreward rewardLo rewardHi meanLo meanHi
      source

example {Omega Context State Action : Type}
    [mOmega : MeasurableSpace Omega] [StandardBorelSpace Omega]
    [MeasurableSpace Context] [MeasurableSpace State]
    [MeasurableSpace Action] [MeasurableSingletonClass Action]
    [Countable Action]
    (mu : MeasureTheory.Measure Omega) [MeasureTheory.IsFiniteMeasure mu]
    (action : Omega -> ActionTrace Action)
    (rewardKernel : RewardKernel.MarkovRewardKernel (Prod Context Action) Rat)
    (policy : Nat -> Policy.MeasurablePolicy State Action)
    (context : (n : Nat) -> ((j : Finset.Iic n) -> Rat) -> Context)
    (state : (n : Nat) -> ((j : Finset.Iic n) -> Rat) -> State)
    (mean : Context -> Action -> Rat)
    (varianceProxy : Context -> Action -> NNReal)
    (defaultAction : Action)
    (reward : Omega -> RewardTrace Rat)
    (haction : forall t : Nat,
      Measurable (fun omega : Omega => action omega t))
    (hreward : forall t : Nat,
      Measurable (fun omega : Omega => reward omega t))
    (rewardLo rewardHi meanLo meanHi : Nat -> Real)
    (source :
      ConditionalExpectationReward.GeneratedActionRandomPairRawRangeMeasurableMeanRangeBoundedSource
        mu action rewardKernel policy context state mean varianceProxy
        defaultAction reward haction hreward rewardLo rewardHi meanLo meanHi)
    (i : Nat) :
    Filter.Eventually
      (fun omega : Omega =>
        @MeasureTheory.Measure.map Omega (Prod Action Rat) mOmega inferInstance
          (fun y : Omega => (action y (i + 1), reward y (i + 1)))
          (@ProbabilityTheory.condExpKernel Omega mOmega _ mu _
            ((History.historyFiltrationSucc action reward haction hreward) i)
            omega) =
        RewardKernel.actionRewardHistoryStepKernelFamily rewardKernel policy
          (fun n history =>
            context n (History.pairHistoryRewardProjection history))
          (fun n history =>
            state n (History.pairHistoryRewardProjection history))
          (fun n : Nat =>
            (source.hcontext n).comp
              (History.measurable_pairHistoryRewardProjection
                (Action := Action) (Reward := Rat) n))
          (fun n : Nat =>
            (source.hstate n).comp
              (History.measurable_pairHistoryRewardProjection
                (Action := Action) (Reward := Rat) n))
          i
          (History.finitePairHistoryOfTrace
            (action omega) (reward omega) i))
      (MeasureTheory.ae
        (mu.trim
          ((History.historyFiltrationSucc action reward haction hreward).le
            i))) := by
  exact
    ConditionalExpectationReward.actionRewardHistoryStepKernelFamily_pair_map_eq_historyFiltrationSucc_finitePairHistoryOfTrace_of_generatedActionRandomPairRawRangeMeasurableMeanRangeBoundedSource
      (mOmega := mOmega)
      mu action rewardKernel policy context state mean varianceProxy
      defaultAction reward haction hreward rewardLo rewardHi meanLo meanHi
      source i

example {Omega Context State Action : Type}
    [mOmega : MeasurableSpace Omega] [StandardBorelSpace Omega]
    [MeasurableSpace Context] [MeasurableSpace State]
    [MeasurableSpace Action] [MeasurableSingletonClass Action]
    [Countable Action]
    (mu : MeasureTheory.Measure Omega) [MeasureTheory.IsFiniteMeasure mu]
    (action : Omega -> ActionTrace Action)
    (rewardKernel : RewardKernel.MarkovRewardKernel (Prod Context Action) Rat)
    (policy : Nat -> Policy.MeasurablePolicy State Action)
    (context : (n : Nat) -> ((j : Finset.Iic n) -> Rat) -> Context)
    (state : (n : Nat) -> ((j : Finset.Iic n) -> Rat) -> State)
    (mean : Context -> Action -> Rat)
    (varianceProxy : Context -> Action -> NNReal)
    (defaultAction : Action)
    (reward : Omega -> RewardTrace Rat)
    (haction : forall t : Nat,
      Measurable (fun omega : Omega => action omega t))
    (hreward : forall t : Nat,
      Measurable (fun omega : Omega => reward omega t))
    (rewardLo rewardHi meanLo meanHi : Nat -> Real)
    (source :
      ConditionalExpectationReward.GeneratedActionRandomPairRawRangeMeasurableMeanRangeBoundedSource
        mu action rewardKernel policy context state mean varianceProxy
        defaultAction reward haction hreward rewardLo rewardHi meanLo meanHi) :
    ConditionalExpectationReward.GeneratedActionActualRewardMapSource
      mu action rewardKernel policy context state defaultAction reward
      haction hreward := by
  exact
    ConditionalExpectationReward.generatedActionActualRewardMapSource_of_randomPairRawRangeMeasurableMeanRangeBoundedSource
      (mOmega := mOmega)
      mu action rewardKernel policy context state mean varianceProxy
      defaultAction reward haction hreward rewardLo rewardHi meanLo meanHi
      source

example {Omega Context State Action : Type}
    [mOmega : MeasurableSpace Omega] [StandardBorelSpace Omega]
    [MeasurableSpace Context] [MeasurableSpace State]
    [MeasurableSpace Action] [MeasurableSingletonClass Action]
    [Countable Action]
    (mu : MeasureTheory.Measure Omega) [MeasureTheory.IsFiniteMeasure mu]
    (action : Omega -> ActionTrace Action)
    (rewardKernel : RewardKernel.MarkovRewardKernel (Prod Context Action) Rat)
    (policy : Nat -> Policy.MeasurablePolicy State Action)
    (context : (n : Nat) -> ((j : Finset.Iic n) -> Rat) -> Context)
    (state : (n : Nat) -> ((j : Finset.Iic n) -> Rat) -> State)
    (mean : Context -> Action -> Rat)
    (varianceProxy : Context -> Action -> NNReal)
    (defaultAction : Action)
    (reward : Omega -> RewardTrace Rat)
    (haction : forall t : Nat,
      Measurable (fun omega : Omega => action omega t))
    (hreward : forall t : Nat,
      Measurable (fun omega : Omega => reward omega t))
    (rewardLo rewardHi meanLo meanHi : Nat -> Real)
    (source :
      ConditionalExpectationReward.GeneratedActionRandomPairRawRangeMeasurableMeanRangeBoundedSource
        mu action rewardKernel policy context state mean varianceProxy
        defaultAction reward haction hreward rewardLo rewardHi meanLo meanHi)
    (i : Nat) :
    AEMeasurable
      (fun omega : Omega =>
        (((reward omega (i + 1) -
          mean
            (context i
              (History.finiteRewardHistoryOfTrace (reward omega) i))
            ((policy i).action
              (state i
                (History.finiteRewardHistoryOfTrace (reward omega) i))) :
            Rat) : Real))) mu := by
  exact
    ConditionalExpectationReward.centeredReward_succ_aemeasurable_of_generatedActionRandomPairRawRangeMeasurableMeanRangeBoundedSource
      (mOmega := mOmega)
      mu action rewardKernel policy context state mean varianceProxy
      defaultAction reward haction hreward rewardLo rewardHi meanLo meanHi
      source i

example {Omega Context State Action : Type}
    [mOmega : MeasurableSpace Omega] [StandardBorelSpace Omega]
    [MeasurableSpace Context] [MeasurableSpace State]
    [MeasurableSpace Action] [MeasurableSingletonClass Action]
    [Countable Action]
    (mu : MeasureTheory.Measure Omega) [MeasureTheory.IsFiniteMeasure mu]
    (action : Omega -> ActionTrace Action)
    (rewardKernel : RewardKernel.MarkovRewardKernel (Prod Context Action) Rat)
    (policy : Nat -> Policy.MeasurablePolicy State Action)
    (context : (n : Nat) -> ((j : Finset.Iic n) -> Rat) -> Context)
    (state : (n : Nat) -> ((j : Finset.Iic n) -> Rat) -> State)
    (mean : Context -> Action -> Rat)
    (varianceProxy : Context -> Action -> NNReal)
    (defaultAction : Action)
    (reward : Omega -> RewardTrace Rat)
    (haction : forall t : Nat,
      Measurable (fun omega : Omega => action omega t))
    (hreward : forall t : Nat,
      Measurable (fun omega : Omega => reward omega t))
    (rewardLo rewardHi meanLo meanHi : Nat -> Real)
    (source :
      ConditionalExpectationReward.GeneratedActionRandomPairRawRangeMeasurableMeanRangeBoundedSource
        mu action rewardKernel policy context state mean varianceProxy
        defaultAction reward haction hreward rewardLo rewardHi meanLo meanHi)
    (i : Nat) :
    Filter.Eventually
      (fun omega : Omega =>
        Set.Icc (rewardLo i - meanHi i) (rewardHi i - meanLo i)
          (((reward omega (i + 1) -
            mean
              (context i
                (History.finiteRewardHistoryOfTrace (reward omega) i))
              ((policy i).action
                (state i
                  (History.finiteRewardHistoryOfTrace (reward omega) i))) :
              Rat) : Real)))
      (MeasureTheory.ae mu) := by
  exact
    ConditionalExpectationReward.centeredReward_succ_bound_of_generatedActionRandomPairRawRangeMeasurableMeanRangeBoundedSource
      (mOmega := mOmega)
      mu action rewardKernel policy context state mean varianceProxy
      defaultAction reward haction hreward rewardLo rewardHi meanLo meanHi
      source i

example {Omega Context State Action : Type}
    [mOmega : MeasurableSpace Omega] [StandardBorelSpace Omega]
    [MeasurableSpace Context] [MeasurableSpace State]
    [MeasurableSpace Action] [MeasurableSingletonClass Action]
    [Countable Action]
    (mu : MeasureTheory.Measure Omega) [MeasureTheory.IsFiniteMeasure mu]
    (action : Omega -> ActionTrace Action)
    (rewardKernel : RewardKernel.MarkovRewardKernel (Prod Context Action) Rat)
    (policy : Nat -> Policy.MeasurablePolicy State Action)
    (context : (n : Nat) -> ((j : Finset.Iic n) -> Rat) -> Context)
    (state : (n : Nat) -> ((j : Finset.Iic n) -> Rat) -> State)
    (mean : Context -> Action -> Rat)
    (varianceProxy : Context -> Action -> NNReal)
    (defaultAction : Action)
    (reward : Omega -> RewardTrace Rat)
    (haction : forall t : Nat,
      Measurable (fun omega : Omega => action omega t))
    (hreward : forall t : Nat,
      Measurable (fun omega : Omega => reward omega t))
    (rewardLo rewardHi meanLo meanHi : Nat -> Real)
    (source :
      ConditionalExpectationReward.GeneratedActionRandomPairRawRangeMeasurableMeanRangeBoundedSource
        mu action rewardKernel policy context state mean varianceProxy
        defaultAction reward haction hreward rewardLo rewardHi meanLo meanHi)
    (i : Nat) :
    MeasureTheory.Integrable
      (fun omega : Omega =>
        (((reward omega (i + 1) -
          mean
            (context i
              (History.finiteRewardHistoryOfTrace (reward omega) i))
            ((policy i).action
              (state i
                (History.finiteRewardHistoryOfTrace (reward omega) i))) :
              Rat) : Real))) mu := by
  exact
    ConditionalExpectationReward.centeredReward_succ_integrable_of_generatedActionRandomPairRawRangeMeasurableMeanRangeBoundedSource
      (mOmega := mOmega)
      mu action rewardKernel policy context state mean varianceProxy
      defaultAction reward haction hreward rewardLo rewardHi meanLo meanHi
      source i

example {Omega Context State Action : Type}
    [mOmega : MeasurableSpace Omega] [StandardBorelSpace Omega]
    [MeasurableSpace Context] [MeasurableSpace State]
    [MeasurableSpace Action] [MeasurableSingletonClass Action]
    [Countable Action]
    (mu : MeasureTheory.Measure Omega) [MeasureTheory.IsFiniteMeasure mu]
    (action : Omega -> ActionTrace Action)
    (rewardKernel : RewardKernel.MarkovRewardKernel (Prod Context Action) Rat)
    (policy : Nat -> Policy.MeasurablePolicy State Action)
    (context : (n : Nat) -> ((j : Finset.Iic n) -> Rat) -> Context)
    (state : (n : Nat) -> ((j : Finset.Iic n) -> Rat) -> State)
    (mean : Context -> Action -> Rat)
    (varianceProxy : Context -> Action -> NNReal)
    (defaultAction : Action)
    (reward : Omega -> RewardTrace Rat)
    (haction : forall t : Nat,
      Measurable (fun omega : Omega => action omega t))
    (hreward : forall t : Nat,
      Measurable (fun omega : Omega => reward omega t))
    (rewardLo rewardHi meanLo meanHi : Nat -> Real)
    (source :
      ConditionalExpectationReward.GeneratedActionRandomPairRawRangeMeasurableMeanRangeBoundedSource
        mu action rewardKernel policy context state mean varianceProxy
        defaultAction reward haction hreward rewardLo rewardHi meanLo meanHi)
    (i : Nat) :
    Filter.Eventually
      (fun omega : Omega =>
        @MeasureTheory.Measure.map Omega ((j : Finset.Iic (i + 1)) -> Prod Action Rat)
          mOmega inferInstance
          (fun y : Omega =>
            History.finitePairHistoryOfTrace (action y) (reward y) (i + 1))
          (@ProbabilityTheory.condExpKernel Omega mOmega _ mu _
            ((History.historyFiltrationSucc action reward haction hreward) i)
            omega) =
        RewardKernel.actionRewardPartialTrajectoryKernel rewardKernel policy
          (fun n history =>
            context n (History.pairHistoryRewardProjection history))
          (fun n history =>
            state n (History.pairHistoryRewardProjection history))
          (fun n : Nat =>
            (source.hcontext n).comp
              (History.measurable_pairHistoryRewardProjection
                (Action := Action) (Reward := Rat) n))
          (fun n : Nat =>
            (source.hstate n).comp
              (History.measurable_pairHistoryRewardProjection
                (Action := Action) (Reward := Rat) n))
          i (i + 1)
          (History.finitePairHistoryOfTrace
            (action omega) (reward omega) i))
      (MeasureTheory.ae
        (mu.trim
          ((History.historyFiltrationSucc action reward haction hreward).le
            i))) := by
  exact
    ConditionalExpectationReward.actionRewardPartialTrajectoryKernel_map_eq_historyFiltrationSucc_finitePairHistoryOfTrace_of_generatedActionRandomPairRawRangeMeasurableMeanRangeBoundedSource
      (mOmega := mOmega)
      mu action rewardKernel policy context state mean varianceProxy
      defaultAction reward haction hreward rewardLo rewardHi meanLo meanHi
      source i

example {Omega Context State Action : Type}
    [mOmega : MeasurableSpace Omega] [StandardBorelSpace Omega]
    [MeasurableSpace Context] [MeasurableSpace State]
    [MeasurableSpace Action] [MeasurableSingletonClass Action]
    [Countable Action]
    (mu : MeasureTheory.Measure Omega) [MeasureTheory.IsFiniteMeasure mu]
    (action : Omega -> ActionTrace Action)
    (rewardKernel : RewardKernel.MarkovRewardKernel (Prod Context Action) Rat)
    (policy : Nat -> Policy.MeasurablePolicy State Action)
    (context : (n : Nat) -> ((j : Finset.Iic n) -> Rat) -> Context)
    (state : (n : Nat) -> ((j : Finset.Iic n) -> Rat) -> State)
    (mean : Context -> Action -> Rat)
    (varianceProxy : Context -> Action -> NNReal)
    (defaultAction : Action)
    (reward : Omega -> RewardTrace Rat)
    (haction : forall t : Nat,
      Measurable (fun omega : Omega => action omega t))
    (hreward : forall t : Nat,
      Measurable (fun omega : Omega => reward omega t))
    (rewardLo rewardHi meanLo meanHi : Nat -> Real)
    (source :
      ConditionalExpectationReward.GeneratedActionRandomPairRawRangeMeasurableMeanRangeBoundedSource
        mu action rewardKernel policy context state mean varianceProxy
        defaultAction reward haction hreward rewardLo rewardHi meanLo meanHi)
    (i : Nat) :
    Filter.EventuallyEq (MeasureTheory.ae mu)
      (@MeasureTheory.condExp Omega Real
        ((History.historyFiltrationSucc action reward haction hreward) i)
        mOmega _ _ _ mu
        (fun omega : Omega =>
          (((reward omega (i + 1) -
            mean
              (context i
                (History.finiteRewardHistoryOfTrace (reward omega) i))
              ((policy i).action
                (state i
                  (History.finiteRewardHistoryOfTrace (reward omega) i))) :
                Rat) : Real))))
      (fun _omega : Omega => (0 : Real)) := by
  exact
    ConditionalExpectationReward.centeredReward_succ_condExp_eq_zero_of_generatedActionRandomPairRawRangeMeasurableMeanRangeBoundedSource
      (mOmega := mOmega)
      mu action rewardKernel policy context state mean varianceProxy
      defaultAction reward haction hreward rewardLo rewardHi meanLo meanHi
      source i

example {Omega Context State Action : Type}
    [mOmega : MeasurableSpace Omega] [StandardBorelSpace Omega]
    [MeasurableSpace Context] [MeasurableSpace State]
    [MeasurableSpace Action] [MeasurableSingletonClass Action]
    [Countable Action]
    (mu : MeasureTheory.Measure Omega) [MeasureTheory.IsFiniteMeasure mu]
    (action : Omega -> ActionTrace Action)
    (rewardKernel : RewardKernel.MarkovRewardKernel (Prod Context Action) Rat)
    (policy : Nat -> Policy.MeasurablePolicy State Action)
    (context : (n : Nat) -> ((j : Finset.Iic n) -> Rat) -> Context)
    (state : (n : Nat) -> ((j : Finset.Iic n) -> Rat) -> State)
    (mean : Context -> Action -> Rat)
    (varianceProxy : Context -> Action -> NNReal)
    (defaultAction : Action)
    (reward : Omega -> RewardTrace Rat)
    (haction : forall t : Nat,
      Measurable (fun omega : Omega => action omega t))
    (hreward : forall t : Nat,
      Measurable (fun omega : Omega => reward omega t))
    (rewardLo rewardHi meanLo meanHi : Nat -> Real)
    (source :
      ConditionalExpectationReward.GeneratedActionRandomPairRawMeanBoundedSource
        mu action rewardKernel policy context state mean varianceProxy
        defaultAction reward haction hreward rewardLo rewardHi meanLo meanHi)
    (i : Nat) :
    AEMeasurable
      (fun omega : Omega =>
        (((reward omega (i + 1) -
          mean
            (context i
              (History.finiteRewardHistoryOfTrace (reward omega) i))
            ((policy i).action
              (state i
                (History.finiteRewardHistoryOfTrace (reward omega) i))) :
            Rat) : Real))) mu := by
  exact
    ConditionalExpectationReward.centeredReward_succ_aemeasurable_of_generatedActionRandomPairRawMeanBoundedSource
      (mOmega := mOmega)
      mu action rewardKernel policy context state mean varianceProxy
      defaultAction reward haction hreward rewardLo rewardHi meanLo meanHi
      source i

example {Omega Context State Action : Type}
    [mOmega : MeasurableSpace Omega] [StandardBorelSpace Omega]
    [MeasurableSpace Context] [MeasurableSpace State]
    [MeasurableSpace Action] [MeasurableSingletonClass Action]
    [Countable Action]
    (mu : MeasureTheory.Measure Omega) [MeasureTheory.IsFiniteMeasure mu]
    (action : Omega -> ActionTrace Action)
    (rewardKernel : RewardKernel.MarkovRewardKernel (Prod Context Action) Rat)
    (policy : Nat -> Policy.MeasurablePolicy State Action)
    (context : (n : Nat) -> ((j : Finset.Iic n) -> Rat) -> Context)
    (state : (n : Nat) -> ((j : Finset.Iic n) -> Rat) -> State)
    (mean : Context -> Action -> Rat)
    (varianceProxy : Context -> Action -> NNReal)
    (defaultAction : Action)
    (reward : Omega -> RewardTrace Rat)
    (haction : forall t : Nat,
      Measurable (fun omega : Omega => action omega t))
    (hreward : forall t : Nat,
      Measurable (fun omega : Omega => reward omega t))
    (rewardLo rewardHi meanLo meanHi : Nat -> Real)
    (source :
      ConditionalExpectationReward.GeneratedActionRandomPairRawMeanBoundedSource
        mu action rewardKernel policy context state mean varianceProxy
        defaultAction reward haction hreward rewardLo rewardHi meanLo meanHi)
    (i : Nat) :
    Filter.Eventually
      (fun omega : Omega =>
        Set.Icc (rewardLo i - meanHi i) (rewardHi i - meanLo i)
          (((reward omega (i + 1) -
            mean
              (context i
                (History.finiteRewardHistoryOfTrace (reward omega) i))
              ((policy i).action
                (state i
                  (History.finiteRewardHistoryOfTrace (reward omega) i))) :
              Rat) : Real)))
      (MeasureTheory.ae mu) := by
  exact
    ConditionalExpectationReward.centeredReward_succ_bound_of_generatedActionRandomPairRawMeanBoundedSource
      (mOmega := mOmega)
      mu action rewardKernel policy context state mean varianceProxy
      defaultAction reward haction hreward rewardLo rewardHi meanLo meanHi
      source i

example {Omega Context State Action : Type}
    [mOmega : MeasurableSpace Omega] [StandardBorelSpace Omega]
    [MeasurableSpace Context] [MeasurableSpace State]
    [MeasurableSpace Action] [MeasurableSingletonClass Action]
    [Countable Action]
    (mu : MeasureTheory.Measure Omega) [MeasureTheory.IsFiniteMeasure mu]
    (action : Omega -> ActionTrace Action)
    (rewardKernel : RewardKernel.MarkovRewardKernel (Prod Context Action) Rat)
    (policy : Nat -> Policy.MeasurablePolicy State Action)
    (context : (n : Nat) -> ((j : Finset.Iic n) -> Rat) -> Context)
    (state : (n : Nat) -> ((j : Finset.Iic n) -> Rat) -> State)
    (mean : Context -> Action -> Rat)
    (varianceProxy : Context -> Action -> NNReal)
    (defaultAction : Action)
    (reward : Omega -> RewardTrace Rat)
    (haction : forall t : Nat,
      Measurable (fun omega : Omega => action omega t))
    (hreward : forall t : Nat,
      Measurable (fun omega : Omega => reward omega t))
    (rewardLo rewardHi meanLo meanHi : Nat -> Real)
    (source :
      ConditionalExpectationReward.GeneratedActionRandomPairRawMeanBoundedSource
        mu action rewardKernel policy context state mean varianceProxy
        defaultAction reward haction hreward rewardLo rewardHi meanLo meanHi) :
    ConditionalExpectationReward.GeneratedActionRandomPairBoundedCenteredSource
      mu action rewardKernel policy context state mean varianceProxy
      defaultAction reward haction hreward
      (fun i => rewardLo i - meanHi i)
      (fun i => rewardHi i - meanLo i) := by
  exact
    ConditionalExpectationReward.generatedActionRandomPairBoundedCenteredSource_of_rawMeanBoundedSource
      (mOmega := mOmega)
      mu action rewardKernel policy context state mean varianceProxy
      defaultAction reward haction hreward rewardLo rewardHi meanLo meanHi
      source

example {Omega Context State Action : Type}
    [mOmega : MeasurableSpace Omega] [StandardBorelSpace Omega]
    [MeasurableSpace Context] [MeasurableSpace State]
    [MeasurableSpace Action] [MeasurableSingletonClass Action]
    [Countable Action]
    (mu : MeasureTheory.Measure Omega) [MeasureTheory.IsFiniteMeasure mu]
    (action : Omega -> ActionTrace Action)
    (rewardKernel : RewardKernel.MarkovRewardKernel (Prod Context Action) Rat)
    (policy : Nat -> Policy.MeasurablePolicy State Action)
    (context : (n : Nat) -> ((j : Finset.Iic n) -> Rat) -> Context)
    (state : (n : Nat) -> ((j : Finset.Iic n) -> Rat) -> State)
    (mean : Context -> Action -> Rat)
    (varianceProxy : Context -> Action -> NNReal)
    (defaultAction : Action)
    (reward : Omega -> RewardTrace Rat)
    (haction : forall t : Nat,
      Measurable (fun omega : Omega => action omega t))
    (hreward : forall t : Nat,
      Measurable (fun omega : Omega => reward omega t))
    (rewardLo rewardHi meanLo meanHi : Nat -> Real)
    (source :
      ConditionalExpectationReward.GeneratedActionRandomPairRawMeanBoundedSource
        mu action rewardKernel policy context state mean varianceProxy
        defaultAction reward haction hreward rewardLo rewardHi meanLo meanHi) :
    ConditionalExpectationReward.GeneratedActionActualRewardMapSource
      mu action rewardKernel policy context state defaultAction reward
      haction hreward := by
  exact
    ConditionalExpectationReward.generatedActionActualRewardMapSource_of_randomPairRawMeanBoundedSource
      (mOmega := mOmega)
      mu action rewardKernel policy context state mean varianceProxy
      defaultAction reward haction hreward rewardLo rewardHi meanLo meanHi
      source

example {Omega Context State Action : Type}
    [mOmega : MeasurableSpace Omega] [StandardBorelSpace Omega]
    [MeasurableSpace Context] [MeasurableSpace State]
    [MeasurableSpace Action] [MeasurableSingletonClass Action]
    [Countable Action]
    (mu : MeasureTheory.Measure Omega) [MeasureTheory.IsFiniteMeasure mu]
    (action : Omega -> ActionTrace Action)
    (rewardKernel : RewardKernel.MarkovRewardKernel (Prod Context Action) Rat)
    (policy : Nat -> Policy.MeasurablePolicy State Action)
    (context : (n : Nat) -> ((j : Finset.Iic n) -> Rat) -> Context)
    (state : (n : Nat) -> ((j : Finset.Iic n) -> Rat) -> State)
    (mean : Context -> Action -> Rat)
    (varianceProxy : Context -> Action -> NNReal)
    (defaultAction : Action)
    (reward : Omega -> RewardTrace Rat)
    (haction : forall t : Nat,
      Measurable (fun omega : Omega => action omega t))
    (hreward : forall t : Nat,
      Measurable (fun omega : Omega => reward omega t))
    (rewardLo rewardHi meanLo meanHi : Nat -> Real)
    (source :
      ConditionalExpectationReward.GeneratedActionRandomPairRawMeanBoundedSource
        mu action rewardKernel policy context state mean varianceProxy
        defaultAction reward haction hreward rewardLo rewardHi meanLo meanHi)
    (i : Nat) :
    MeasureTheory.Integrable
      (fun omega : Omega =>
        (((reward omega (i + 1) -
          mean
            (context i
              (History.finiteRewardHistoryOfTrace (reward omega) i))
            ((policy i).action
              (state i
                (History.finiteRewardHistoryOfTrace (reward omega) i))) :
              Rat) : Real))) mu := by
  exact
    ConditionalExpectationReward.centeredReward_succ_integrable_of_generatedActionRandomPairRawMeanBoundedSource
      (mOmega := mOmega)
      mu action rewardKernel policy context state mean varianceProxy
      defaultAction reward haction hreward rewardLo rewardHi meanLo meanHi
      source i

example {Omega Context State Action : Type}
    [mOmega : MeasurableSpace Omega] [StandardBorelSpace Omega]
    [MeasurableSpace Context] [MeasurableSpace State]
    [MeasurableSpace Action] [MeasurableSingletonClass Action]
    [Countable Action]
    (mu : MeasureTheory.Measure Omega) [MeasureTheory.IsFiniteMeasure mu]
    (action : Omega -> ActionTrace Action)
    (rewardKernel : RewardKernel.MarkovRewardKernel (Prod Context Action) Rat)
    (policy : Nat -> Policy.MeasurablePolicy State Action)
    (context : (n : Nat) -> ((j : Finset.Iic n) -> Rat) -> Context)
    (state : (n : Nat) -> ((j : Finset.Iic n) -> Rat) -> State)
    (mean : Context -> Action -> Rat)
    (varianceProxy : Context -> Action -> NNReal)
    (defaultAction : Action)
    (reward : Omega -> RewardTrace Rat)
    (haction : forall t : Nat,
      Measurable (fun omega : Omega => action omega t))
    (hreward : forall t : Nat,
      Measurable (fun omega : Omega => reward omega t))
    (rewardLo rewardHi meanLo meanHi : Nat -> Real)
    (source :
      ConditionalExpectationReward.GeneratedActionRandomPairRawMeanBoundedSource
        mu action rewardKernel policy context state mean varianceProxy
        defaultAction reward haction hreward rewardLo rewardHi meanLo meanHi)
    (i : Nat) :
    Filter.Eventually
      (fun omega : Omega =>
        @MeasureTheory.Measure.map Omega (Prod Action Rat) mOmega inferInstance
          (fun y : Omega => (action y (i + 1), reward y (i + 1)))
          (@ProbabilityTheory.condExpKernel Omega mOmega _ mu _
            ((History.historyFiltrationSucc action reward haction hreward) i)
            omega) =
        RewardKernel.actionRewardHistoryStepKernelFamily rewardKernel policy
          (fun n history =>
            context n (History.pairHistoryRewardProjection history))
          (fun n history =>
            state n (History.pairHistoryRewardProjection history))
          (fun n : Nat =>
            (source.hcontext n).comp
              (History.measurable_pairHistoryRewardProjection
                (Action := Action) (Reward := Rat) n))
          (fun n : Nat =>
            (source.hstate n).comp
              (History.measurable_pairHistoryRewardProjection
                (Action := Action) (Reward := Rat) n))
          i
          (History.finitePairHistoryOfTrace
            (action omega) (reward omega) i))
      (MeasureTheory.ae
        (mu.trim
          ((History.historyFiltrationSucc action reward haction hreward).le
            i))) := by
  exact
    ConditionalExpectationReward.actionRewardHistoryStepKernelFamily_pair_map_eq_historyFiltrationSucc_finitePairHistoryOfTrace_of_generatedActionRandomPairRawMeanBoundedSource
      (mOmega := mOmega)
      mu action rewardKernel policy context state mean varianceProxy
      defaultAction reward haction hreward rewardLo rewardHi meanLo meanHi
      source i

example {Omega Context State Action : Type}
    [mOmega : MeasurableSpace Omega] [StandardBorelSpace Omega]
    [MeasurableSpace Context] [MeasurableSpace State]
    [MeasurableSpace Action] [MeasurableSingletonClass Action]
    [Countable Action]
    (mu : MeasureTheory.Measure Omega) [MeasureTheory.IsFiniteMeasure mu]
    (action : Omega -> ActionTrace Action)
    (rewardKernel : RewardKernel.MarkovRewardKernel (Prod Context Action) Rat)
    (policy : Nat -> Policy.MeasurablePolicy State Action)
    (context : (n : Nat) -> ((j : Finset.Iic n) -> Rat) -> Context)
    (state : (n : Nat) -> ((j : Finset.Iic n) -> Rat) -> State)
    (mean : Context -> Action -> Rat)
    (varianceProxy : Context -> Action -> NNReal)
    (defaultAction : Action)
    (reward : Omega -> RewardTrace Rat)
    (haction : forall t : Nat,
      Measurable (fun omega : Omega => action omega t))
    (hreward : forall t : Nat,
      Measurable (fun omega : Omega => reward omega t))
    (rewardLo rewardHi meanLo meanHi : Nat -> Real)
    (source :
      ConditionalExpectationReward.GeneratedActionRandomPairRawMeanBoundedSource
        mu action rewardKernel policy context state mean varianceProxy
        defaultAction reward haction hreward rewardLo rewardHi meanLo meanHi)
    (i : Nat) :
    Filter.Eventually
      (fun omega : Omega =>
        @MeasureTheory.Measure.map Omega ((j : Finset.Iic (i + 1)) -> Prod Action Rat)
          mOmega inferInstance
          (fun y : Omega =>
            History.finitePairHistoryOfTrace (action y) (reward y) (i + 1))
          (@ProbabilityTheory.condExpKernel Omega mOmega _ mu _
            ((History.historyFiltrationSucc action reward haction hreward) i)
            omega) =
        RewardKernel.actionRewardPartialTrajectoryKernel rewardKernel policy
          (fun n history =>
            context n (History.pairHistoryRewardProjection history))
          (fun n history =>
            state n (History.pairHistoryRewardProjection history))
          (fun n : Nat =>
            (source.hcontext n).comp
              (History.measurable_pairHistoryRewardProjection
                (Action := Action) (Reward := Rat) n))
          (fun n : Nat =>
            (source.hstate n).comp
              (History.measurable_pairHistoryRewardProjection
                (Action := Action) (Reward := Rat) n))
          i (i + 1)
          (History.finitePairHistoryOfTrace
            (action omega) (reward omega) i))
      (MeasureTheory.ae
        (mu.trim
          ((History.historyFiltrationSucc action reward haction hreward).le
            i))) := by
  exact
    ConditionalExpectationReward.actionRewardPartialTrajectoryKernel_map_eq_historyFiltrationSucc_finitePairHistoryOfTrace_of_generatedActionRandomPairRawMeanBoundedSource
      (mOmega := mOmega)
      mu action rewardKernel policy context state mean varianceProxy
      defaultAction reward haction hreward rewardLo rewardHi meanLo meanHi
      source i

example {Omega Context State Action : Type}
    [mOmega : MeasurableSpace Omega] [StandardBorelSpace Omega]
    [MeasurableSpace Context] [MeasurableSpace State]
    [MeasurableSpace Action] [MeasurableSingletonClass Action]
    [Countable Action]
    (mu : MeasureTheory.Measure Omega) [MeasureTheory.IsFiniteMeasure mu]
    (action : Omega -> ActionTrace Action)
    (rewardKernel : RewardKernel.MarkovRewardKernel (Prod Context Action) Rat)
    (policy : Nat -> Policy.MeasurablePolicy State Action)
    (context : (n : Nat) -> ((j : Finset.Iic n) -> Rat) -> Context)
    (state : (n : Nat) -> ((j : Finset.Iic n) -> Rat) -> State)
    (mean : Context -> Action -> Rat)
    (varianceProxy : Context -> Action -> NNReal)
    (defaultAction : Action)
    (reward : Omega -> RewardTrace Rat)
    (haction : forall t : Nat,
      Measurable (fun omega : Omega => action omega t))
    (hreward : forall t : Nat,
      Measurable (fun omega : Omega => reward omega t))
    (rewardLo rewardHi meanLo meanHi : Nat -> Real)
    (source :
      ConditionalExpectationReward.GeneratedActionRandomPairRawMeanBoundedSource
        mu action rewardKernel policy context state mean varianceProxy
        defaultAction reward haction hreward rewardLo rewardHi meanLo meanHi)
    (i : Nat) :
    Filter.EventuallyEq (MeasureTheory.ae mu)
      (@MeasureTheory.condExp Omega Real
        ((History.historyFiltrationSucc action reward haction hreward) i)
        mOmega _ _ _ mu
        (fun omega : Omega =>
          (((reward omega (i + 1) -
            mean
              (context i
                (History.finiteRewardHistoryOfTrace (reward omega) i))
              ((policy i).action
                (state i
                  (History.finiteRewardHistoryOfTrace (reward omega) i))) :
                Rat) : Real))))
      (fun _omega : Omega => (0 : Real)) := by
  exact
    ConditionalExpectationReward.centeredReward_succ_condExp_eq_zero_of_generatedActionRandomPairRawMeanBoundedSource
      (mOmega := mOmega)
      mu action rewardKernel policy context state mean varianceProxy
      defaultAction reward haction hreward rewardLo rewardHi meanLo meanHi
      source i

example {Omega : Type} {K : Nat}
    [mOmega : MeasurableSpace Omega]
    (mu : MeasureTheory.Measure Omega)
    [MeasureTheory.IsFiniteMeasure mu]
    (spec : ETC.Spec K)
    (model : FiniteBanditModel K)
    (commitArm : Fin K)
    (reward : Omega -> RewardTrace Rat)
    (hreward : forall t : Nat,
      @Measurable Omega Rat mOmega inferInstance
        (fun omega : Omega => reward omega t))
    (b : Fin K) (t : Nat)
    (h_indep :
      ProbabilityTheory.Indep
        (MeasurableSpace.comap
          (fun omega : Omega =>
            (((reward omega t - model.mean b : Rat) : Real)))
          inferInstance)
        (History.historyFiltrationSucc
          (fun _omega : Omega => ETC.actionWithCommit spec commitArm)
          reward
          (fun _t : Nat => measurable_const)
          hreward t)
        mu)
    (h_integral :
      MeasureTheory.integral mu
        (fun omega : Omega =>
          (((reward omega t - model.mean b : Rat) : Real))) = 0) :
    Filter.EventuallyEq (MeasureTheory.ae mu)
      (MeasureTheory.condExp
        (History.historyFiltrationSucc
          (fun _omega : Omega => ETC.actionWithCommit spec commitArm)
          reward
          (fun _t : Nat => measurable_const)
          hreward t)
        mu
        (fun omega : Omega =>
          (((reward omega t - model.mean b : Rat) : Real))))
      (fun _omega : Omega => (0 : Real)) := by
  exact
    ETC.centeredReward_condExp_historyFiltrationSucc_eq_zero_of_indep
      (mOmega := mOmega)
      mu spec model commitArm reward hreward b t h_indep h_integral

example {Omega : Type} {K : Nat}
    [mOmega : MeasurableSpace Omega]
    (mu : MeasureTheory.Measure Omega)
    (model : FiniteBanditModel K)
    (reward : Omega -> RewardTrace Rat)
    (hreward : forall t : Nat,
      @Measurable Omega Rat mOmega inferInstance
        (fun omega : Omega => reward omega t))
    (h_reward_indep :
      ProbabilityTheory.iIndepFun
        (fun t omega => reward omega t) mu)
    (b : Fin K) (i : Nat) :
    ProbabilityTheory.Indep
      (MeasurableSpace.comap
        (fun omega : Omega =>
          (((reward omega (i + 1) - model.mean b : Rat) : Real)))
        inferInstance)
      (iSup fun j : Nat =>
        iSup fun _h : j <= i =>
          MeasurableSpace.comap
            (fun omega : Omega => reward omega j) inferInstance)
      mu := by
  exact
    ETC.indep_centeredReward_succ_pastReward_iSup_of_iIndepFun_reward
      (mOmega := mOmega)
      mu model reward hreward h_reward_indep b i

example {Omega : Type} {K : Nat}
    [mOmega : MeasurableSpace Omega]
    (spec : ETC.Spec K)
    (commitArm : Fin K)
    (reward : Omega -> RewardTrace Rat)
    (hreward : forall t : Nat,
      @Measurable Omega Rat mOmega inferInstance
        (fun omega : Omega => reward omega t))
    (i : Nat) :
    (History.historyFiltrationSucc
      (fun _omega : Omega => ETC.actionWithCommit spec commitArm)
      reward
      (fun _t : Nat => measurable_const)
      hreward i : MeasurableSpace Omega) <=
    (iSup fun j : Nat =>
      iSup fun _h : j <= i =>
        MeasurableSpace.comap
          (fun omega : Omega => reward omega j) inferInstance) := by
  exact
    ETC.historyFiltrationSucc_actionWithCommit_le_pastReward_iSup
      (mOmega := mOmega)
      spec commitArm reward hreward i

example {Omega : Type} {K : Nat}
    [mOmega : MeasurableSpace Omega]
    (mu : MeasureTheory.Measure Omega)
    (spec : ETC.Spec K)
    (model : FiniteBanditModel K)
    (commitArm : Fin K)
    (reward : Omega -> RewardTrace Rat)
    (hreward : forall t : Nat,
      @Measurable Omega Rat mOmega inferInstance
        (fun omega : Omega => reward omega t))
    (h_reward_indep :
      ProbabilityTheory.iIndepFun
        (fun t omega => reward omega t) mu)
    (b : Fin K) (i : Nat) :
    ProbabilityTheory.Indep
      (MeasurableSpace.comap
        (fun omega : Omega =>
          (((reward omega (i + 1) - model.mean b : Rat) : Real)))
        inferInstance)
      (History.historyFiltrationSucc
        (fun _omega : Omega => ETC.actionWithCommit spec commitArm)
        reward
        (fun _t : Nat => measurable_const)
        hreward i)
      mu := by
  exact
    ETC.indep_centeredReward_succ_historyFiltrationSucc_of_iIndepFun_reward
      (mOmega := mOmega)
      mu spec model commitArm reward hreward h_reward_indep b i

example {Omega : Type} {K : Nat}
    [mOmega : MeasurableSpace Omega]
    (mu : MeasureTheory.Measure Omega)
    [MeasureTheory.IsFiniteMeasure mu]
    (spec : ETC.Spec K)
    (model : FiniteBanditModel K)
    (commitArm : Fin K)
    (reward : Omega -> RewardTrace Rat)
    (hreward : forall t : Nat,
      @Measurable Omega Rat mOmega inferInstance
        (fun omega : Omega => reward omega t))
    (b : Fin K) (i : Nat)
    (h_indep :
      ProbabilityTheory.Indep
        (MeasurableSpace.comap
          (fun omega : Omega =>
            (((reward omega (i + 1) - model.mean b : Rat) : Real)))
          inferInstance)
        (History.historyFiltrationSucc
          (fun _omega : Omega => ETC.actionWithCommit spec commitArm)
          reward
          (fun _t : Nat => measurable_const)
          hreward i)
        mu)
    (h_integral :
      MeasureTheory.integral mu
        (fun omega : Omega =>
          (((reward omega (i + 1) - model.mean b : Rat) : Real))) = 0) :
    Filter.EventuallyEq (MeasureTheory.ae mu)
      (MeasureTheory.condExp
        (History.historyFiltrationSucc
          (fun _omega : Omega => ETC.actionWithCommit spec commitArm)
          reward
          (fun _t : Nat => measurable_const)
          hreward i)
        mu
        (fun omega : Omega =>
          (((reward omega (i + 1) - model.mean b : Rat) : Real))))
      (fun _omega : Omega => (0 : Real)) := by
  exact
    ETC.centeredReward_succ_condExp_historyFiltrationSucc_eq_zero_of_indep
      (mOmega := mOmega)
      mu spec model commitArm reward hreward b i h_indep h_integral

example {Omega : Type} {K : Nat}
    [mOmega : MeasurableSpace Omega]
    (mu : MeasureTheory.Measure Omega)
    [MeasureTheory.IsFiniteMeasure mu]
    (spec : ETC.Spec K)
    (model : FiniteBanditModel K)
    (commitArm : Fin K)
    (reward : Omega -> RewardTrace Rat)
    (hreward : forall t : Nat,
      @Measurable Omega Rat mOmega inferInstance
        (fun omega : Omega => reward omega t))
    (h_reward_indep :
      ProbabilityTheory.iIndepFun
        (fun t omega => reward omega t) mu)
    (b : Fin K) (i : Nat)
    (h_integral :
      MeasureTheory.integral mu
        (fun omega : Omega =>
          (((reward omega (i + 1) - model.mean b : Rat) : Real))) = 0) :
    Filter.EventuallyEq (MeasureTheory.ae mu)
      (MeasureTheory.condExp
        (History.historyFiltrationSucc
          (fun _omega : Omega => ETC.actionWithCommit spec commitArm)
          reward
          (fun _t : Nat => measurable_const)
          hreward i)
        mu
        (fun omega : Omega =>
          (((reward omega (i + 1) - model.mean b : Rat) : Real))))
      (fun _omega : Omega => (0 : Real)) := by
  exact
    ETC.centeredReward_succ_condExp_historyFiltrationSucc_eq_zero_of_iIndepFun_reward
      (mOmega := mOmega)
      mu spec model commitArm reward hreward h_reward_indep b i h_integral

example {Omega : Type}
    [mOmega : MeasurableSpace Omega] [StandardBorelSpace Omega]
    (mu : MeasureTheory.Measure Omega)
    [MeasureTheory.IsFiniteMeasure mu]
    (mcond : MeasurableSpace Omega) (hm : mcond <= mOmega)
    (X : Omega -> Real) (c : NNReal)
    (hmeasX : @Measurable Omega Real mOmega inferInstance X)
    (h_subG : ProbabilityTheory.HasSubgaussianMGF X c mu)
    (h_indep :
      ProbabilityTheory.Indep
        (MeasurableSpace.comap X inferInstance) mcond mu) :
    ProbabilityTheory.HasCondSubgaussianMGF mcond hm X c mu := by
  exact
    ETC.hasCondSubgaussianMGF_of_indep_comap
      (mOmega := mOmega)
      mu mcond hm X c hmeasX h_subG h_indep

example {Omega : Type} {K : Nat}
    [mOmega : MeasurableSpace Omega] [StandardBorelSpace Omega]
    (mu : MeasureTheory.Measure Omega)
    [MeasureTheory.IsFiniteMeasure mu]
    (spec : ETC.Spec K)
    (model : FiniteBanditModel K)
    (commitArm : Fin K)
    (reward : Omega -> RewardTrace Rat)
    (hreward : forall t : Nat,
      @Measurable Omega Rat mOmega inferInstance
        (fun omega : Omega => reward omega t))
    (h_reward_indep :
      ProbabilityTheory.iIndepFun
        (fun t omega => reward omega t) mu)
    (b : Fin K) (i : Nat) (c : NNReal)
    (h_subG :
      ProbabilityTheory.HasSubgaussianMGF
        (fun omega : Omega =>
          (((reward omega (i + 1) - model.mean b : Rat) : Real)))
        c mu) :
    ProbabilityTheory.HasCondSubgaussianMGF
      (History.historyFiltrationSucc
        (fun _omega : Omega => ETC.actionWithCommit spec commitArm)
        reward
        (fun _t : Nat => measurable_const)
        hreward i)
      ((History.historyFiltrationSucc
        (fun _omega : Omega => ETC.actionWithCommit spec commitArm)
        reward
        (fun _t : Nat => measurable_const)
        hreward).le i)
      (fun omega : Omega =>
        (((reward omega (i + 1) - model.mean b : Rat) : Real)))
      c mu := by
  exact
    ETC.centeredReward_succ_hasCondSubgaussianMGF_historyFiltrationSucc_of_iIndepFun_reward
      (mOmega := mOmega)
      mu spec model commitArm reward hreward h_reward_indep b i c h_subG

noncomputable example {Omega : Type} {K : Nat}
    [MeasurableSpace Omega]
    (mu : MeasureTheory.Measure Omega)
    (spec : ETC.Spec K)
    (model : FiniteBanditModel K)
    (commitArm : Fin K)
    (reward : Omega -> RewardTrace Rat)
    (c : Fin K -> Nat -> NNReal)
    (h_indep :
      forall a : Fin K, (a = model.bestArm -> False) ->
        ProbabilityTheory.iIndepFun
          (fun t omega =>
            ETC.centeredPairwiseRewardDiff
              spec model commitArm reward a t omega)
          mu)
    (h_subG :
      forall a : Fin K, (a = model.bestArm -> False) ->
        forall t, t ∈ Finset.range (spec.explorationPulls * K) ->
          ProbabilityTheory.HasSubgaussianMGF
            (fun omega =>
              ETC.centeredPairwiseRewardDiff
                spec model commitArm reward a t omega)
            (c a t) mu) :
    ETC.CenteredDiffSubGaussianWitnesses
      mu spec model commitArm reward
      (ETC.centeredDiffSubGaussianTail spec model c) :=
  ETC.centeredDiffSubGaussianWitnesses_of_indep_subG
    mu spec model commitArm reward c h_indep h_subG

example {Omega : Type} {K : Nat}
    [MeasurableSpace Omega]
    (mu : MeasureTheory.Measure Omega) [MeasureTheory.IsFiniteMeasure mu]
    (spec : ETC.Spec K)
    (model : FiniteBanditModel K)
    (commitArm : Fin K)
    (reward : Omega -> RewardTrace Rat)
    (c : Fin K -> Nat -> NNReal)
    (hexplorationPulls_pos : 0 < spec.explorationPulls)
    (h_indep :
      forall a : Fin K, (a = model.bestArm -> False) ->
        ProbabilityTheory.iIndepFun
          (fun t omega =>
            ETC.centeredPairwiseRewardDiff
              spec model commitArm reward a t omega)
          mu)
    (h_subG :
      forall a : Fin K, (a = model.bestArm -> False) ->
        forall t, t ∈ Finset.range (spec.explorationPulls * K) ->
          ProbabilityTheory.HasSubgaussianMGF
            (fun omega =>
              ETC.centeredPairwiseRewardDiff
                spec model commitArm reward a t omega)
            (c a t) mu) :
    ETC.PairwiseEmpMeanTailContract
      mu spec model commitArm reward
      (ETC.centeredDiffSubGaussianTail spec model c) := by
  exact
    ETC.pairwiseEmpMeanTailContract_of_centeredDiff_indep_subG
      mu spec model commitArm reward c hexplorationPulls_pos h_indep h_subG

example (t n : Nat) :
    pullCount alternatingAction 0 (t + n) ≤ pullCount alternatingAction 0 t + n :=
  pullCount_add_le alternatingAction 0 t n

example (t n : Nat) :
    pullCount alternatingAction 0 t ≤ pullCount alternatingAction 0 (t + n) :=
  pullCount_le_add (action := alternatingAction) (a := 0) (t := t) (n := n)

example : pullCount constantZeroAction 1 4 = 0 := by
  apply pullCount_eq_zero_of_forall_ne
  intro s _hs
  simp [constantZeroAction]

example : pullCount constantZeroAction 0 4 = 4 := by
  apply pullCount_eq_time_of_forall_eq
  intro s _hs
  rfl

example : pullCount (fun _ : Nat => 2) 2 7 = 7 := by
  simp

example : pullCount (fun _ : Nat => 2) 1 7 = 0 := by
  exact pullCount_const_of_ne (a := 1) 2 (by decide) 7

example :
    pullCount (fun _ : Nat => 0) 1 (2 + 5) =
      pullCount (fun _ : Nat => 0) 1 2 := by
  apply pullCount_add_eq_of_forall_ne_between
  intro _s _hlo _hhi
  decide

example :
    pullCount (fun _ : Nat => 0) 0 (2 + 5) =
      pullCount (fun _ : Nat => 0) 0 2 + 5 := by
  apply pullCount_add_eq_add_of_forall_eq_between
  intro _s _hlo _hhi
  rfl

example : 0 < pullCount alternatingAction 0 5 := by
  exact pullCount_pos_of_eq_before alternatingAction 0
    (s := 0) (t := 5) (by decide) (by native_decide)

def natReward : Nat → Nat := fun t => t + 1

example :
    sumRewards alternatingAction natReward 0 5 =
      (List.range 5).foldl
        (fun acc s => acc + if alternatingAction s = 0 then natReward s else 0)
        0 := by
  exact sumRewards_eq_list_range_foldl alternatingAction natReward 0 5

example :
    sumRewards alternatingAction natReward 0 5 =
      ((List.range 5).filter
        (fun s : Nat => decide (alternatingAction s = 0))).foldl
        (fun acc s => acc + natReward s)
        0 := by
  exact sumRewards_eq_list_range_filter_foldl alternatingAction natReward 0 5
    (fun x => Nat.add_zero x)

example :
    sumRewards alternatingAction natReward 0 5 =
      ((Finset.range 5).filter
        (fun s : Nat => alternatingAction s = 0)).sum
        (fun s : Nat => natReward s) := by
  exact sumRewards_eq_finset_filter_sum alternatingAction natReward 0 5

example : sumRewards (fun _ : Nat => 2) natReward 1 6 = 0 := by
  exact sumRewards_const_of_ne (a := 1) (reward := natReward)
    (fun x => Nat.add_zero x) 2 (by decide) 6

example :
    sumRewards (fun _ : Nat => 2) natReward 1 (2 + 5) =
      sumRewards (fun _ : Nat => 2) natReward 1 2 := by
  apply sumRewards_add_eq_of_forall_ne_between
  · exact fun x => Nat.add_zero x
  · intro _s _hlo _hhi
    decide

def etcSpec : ETC.Spec 2 where
  hK := by decide
  explorationPulls := 3

example : ETC.exploreArm etcSpec 0 = ETC.exploreArm etcSpec 2 := by
  apply ETC.exploreArm_eq_of_mod_eq
  native_decide

example (t : Nat) :
    ETC.exploreArm etcSpec (t + 2) = ETC.exploreArm etcSpec t := by
  exact ETC.exploreArm_add_K etcSpec t

example (t : Nat) (a : Fin 2) :
    ETC.exploreArm etcSpec t = a ↔ t % 2 = a.val := by
  exact ETC.exploreArm_eq_iff_mod_eq_val etcSpec t a

example (a : Fin 2) :
    pullCount (ETC.exploreArm etcSpec) a 2 = 1 := by
  exact ETC.pullCount_exploreArm_K_eq_one etcSpec a

example (a : Fin 2) (t : Nat) :
    pullCount (ETC.exploreArm etcSpec) a (t + 2) =
      pullCount (ETC.exploreArm etcSpec) a t + 1 := by
  exact ETC.pullCount_exploreArm_add_K_eq_add_one etcSpec a t

example (a : Fin 2) (m : Nat) :
    pullCount (ETC.exploreArm etcSpec) a (m * 2) = m := by
  exact ETC.pullCount_exploreArm_mul_K_eq etcSpec a m

example (a : Fin 2) :
    pullCount (ETC.exploreArm etcSpec) a (etcSpec.explorationPulls * 2) =
      etcSpec.explorationPulls := by
  exact ETC.pullCount_exploreArm_explorationPulls_mul_K_eq etcSpec a

example (commitArm : Fin 2) {t : Nat} (h : t < etcSpec.explorationPulls * 2) :
    ETC.actionWithCommit etcSpec commitArm t = ETC.exploreArm etcSpec t := by
  exact ETC.actionWithCommit_eq_exploreArm_of_lt etcSpec commitArm h

example (commitArm : Fin 2) {t : Nat} (h : etcSpec.explorationPulls * 2 <= t) :
    ETC.actionWithCommit etcSpec commitArm t = commitArm := by
  exact ETC.actionWithCommit_eq_commitArm_of_ge etcSpec commitArm h

example (model : FiniteBanditModel 2) {t : Nat}
    (h : etcSpec.explorationPulls * 2 <= t) :
    ETC.actionWithCommit etcSpec model.bestArm t = model.bestArm := by
  exact
    ETC.actionWithCommit_eq_bestArm_of_commitArm_eq_bestArm_of_explorationPulls_mul_K_le
      etcSpec model model.bestArm t rfl h

example (commitArm a : Fin 2) (n : Nat)
    (hn : n <= etcSpec.explorationPulls * 2) :
    pullCount (ETC.actionWithCommit etcSpec commitArm) a n =
      pullCount (ETC.exploreArm etcSpec) a n := by
  exact
    ETC.pullCount_actionWithCommit_eq_pullCount_exploreArm_of_le
      etcSpec commitArm a n hn

example (commitArm a : Fin 2) :
    pullCount (ETC.actionWithCommit etcSpec commitArm) a
        (etcSpec.explorationPulls * 2) =
      etcSpec.explorationPulls := by
  exact
    ETC.pullCount_actionWithCommit_explorationPulls_mul_K_eq
      etcSpec commitArm a

example (commitArm a : Fin 2) {t : Nat}
    (ht : etcSpec.explorationPulls * 2 <= t) :
    pullCount (ETC.actionWithCommit etcSpec commitArm) a (Nat.succ t) =
      pullCount (ETC.actionWithCommit etcSpec commitArm) a t +
        if commitArm = a then 1 else 0 := by
  exact
    ETC.pullCount_actionWithCommit_succ_eq_add_if_commitArm_of_ge
      etcSpec commitArm a ht

example (commitArm a : Fin 2) (r : Nat) :
    pullCount (ETC.actionWithCommit etcSpec commitArm) a
        (etcSpec.explorationPulls * 2 + r) =
      etcSpec.explorationPulls + (if commitArm = a then r else 0) := by
  exact
    ETC.pullCount_actionWithCommit_explorationPulls_mul_K_add_eq
      etcSpec commitArm a r

example {commitArm a : Fin 2} (hne : commitArm ≠ a) (r : Nat) :
    pullCount (ETC.actionWithCommit etcSpec commitArm) a
        (etcSpec.explorationPulls * 2 + r) =
      etcSpec.explorationPulls := by
  exact
    ETC.pullCount_actionWithCommit_explorationPulls_mul_K_add_eq_of_ne
      etcSpec hne r

example (commitArm : Fin 2) (r : Nat) :
    pullCount (ETC.actionWithCommit etcSpec commitArm) commitArm
        (etcSpec.explorationPulls * 2 + r) =
      etcSpec.explorationPulls + r := by
  exact
    ETC.pullCount_actionWithCommit_explorationPulls_mul_K_add_eq_commitArm
      etcSpec commitArm r

def ucbSpec : UCB.Spec 2 where
  hK := by decide
  explorationScale := 1

def ucbState : UCB.IndexState 2 where
  empiricalMean := fun arm => if arm.val = 0 then 1 else 0
  pulls := fun _ => 1

example (arm : Fin 2) :
    UCB.score ucbSpec ucbState arm = ucbState.empiricalMean arm := by
  simp

def twoArmModel : FiniteBanditModel 2 where
  hK := by decide
  mean := fun arm => if arm.val = 0 then 1 else 0

example {K : Nat} (model : FiniteBanditModel K) (a : Fin K) :
    model.mean a <= model.mean model.bestArm := by
  exact FiniteBanditModel.mean_le_bestArm_mean model a

example {K : Nat} (model : FiniteBanditModel K) (a : Fin K) :
    (0 : Rat) <= model.gap a := by
  exact FiniteBanditModel.gap_nonneg model a

example : twoArmModel.gap twoArmModel.bestArm = 0 := by
  simp

example : pseudoRegret twoArmModel (fun _ => twoArmModel.bestArm) 1 = 0 := by
  rw [pseudoRegret_one]
  simp [FiniteBanditModel.gap_bestArm]

example (t : Nat) :
    pseudoRegret twoArmModel (fun _ => twoArmModel.bestArm) (t + 1) =
      pseudoRegret twoArmModel (fun _ => twoArmModel.bestArm) t := by
  apply pseudoRegret_succ_of_bestArm
  rfl

example (t : Nat) :
    pseudoRegret twoArmModel (fun _ => twoArmModel.bestArm) t = 0 := by
  simp

example (t : Nat) :
    pseudoRegret twoArmModel (fun _ => twoArmModel.bestArm) t = 0 := by
  apply pseudoRegret_eq_zero_of_forall_gap_zero
  intro _s _hs
  simp

example (t : Nat) :
    pseudoRegret twoArmModel (fun _ => twoArmModel.bestArm) t = 0 := by
  exact pseudoRegret_const_bestArm twoArmModel t

example :
    pseudoRegret twoArmModel alternatingAction 5 =
      (List.range 5).foldl
        (fun acc s => acc + twoArmModel.gap (alternatingAction s))
        0 := by
  exact pseudoRegret_eq_list_range_foldl twoArmModel alternatingAction 5

example :
    pseudoRegret twoArmModel alternatingAction 5 =
      (Finset.range 5).sum
        (fun s : Nat => twoArmModel.gap (alternatingAction s)) := by
  exact pseudoRegret_eq_finset_sum twoArmModel alternatingAction 5

example :
    pseudoRegret twoArmModel alternatingAction 5 =
      (Finset.univ : Finset (Fin 2)).sum
        (fun a : Fin 2 =>
          twoArmModel.gap a * (pullCount alternatingAction a 5 : Rat)) := by
  exact pseudoRegret_eq_finset_sum_gap_mul_pullCount
    twoArmModel alternatingAction 5

example (B : Fin 2 -> Rat)
    (hB : forall a : Fin 2,
      ((pullCount alternatingAction a 5 : Nat) : Rat) <= B a) :
    pseudoRegret twoArmModel alternatingAction 5 <=
      (Finset.univ : Finset (Fin 2)).sum
        (fun a : Fin 2 => twoArmModel.gap a * B a) := by
  exact
    pseudoRegret_le_finset_sum_gap_mul_count_bound
      twoArmModel alternatingAction 5 B hB

example (B : Fin 2 -> Nat)
    (hB : forall a : Fin 2,
      pullCount alternatingAction a 5 <= B a) :
    pseudoRegret twoArmModel alternatingAction 5 <=
      (Finset.univ : Finset (Fin 2)).sum
        (fun a : Fin 2 => twoArmModel.gap a * (((B a : Nat) : Rat))) := by
  exact
    pseudoRegret_le_finset_sum_gap_mul_nat_count_bound
      twoArmModel alternatingAction 5 B hB

example (B : Nat)
    (hB : forall a : Fin 2,
      pullCount alternatingAction a 5 <= B) :
    pseudoRegret twoArmModel alternatingAction 5 <=
      ((Finset.univ : Finset (Fin 2)).sum
        (fun a : Fin 2 => twoArmModel.gap a)) * (((B : Nat) : Rat)) := by
  exact
    pseudoRegret_le_sum_gap_mul_uniform_nat_count_bound
      twoArmModel alternatingAction 5 B hB

example :
    pseudoRegret twoArmModel (ETC.exploreArm etcSpec)
        (etcSpec.explorationPulls * 2) <=
      ((Finset.univ : Finset (Fin 2)).sum
        (fun a : Fin 2 => twoArmModel.gap a)) *
        (((etcSpec.explorationPulls : Nat) : Rat)) := by
  exact
    ETC.pseudoRegret_exploreArm_explorationPulls_mul_K_le_sum_gap_mul_explorationPulls
      etcSpec twoArmModel

example (commitArm : Fin 2) :
    pseudoRegret twoArmModel (ETC.actionWithCommit etcSpec commitArm)
        (etcSpec.explorationPulls * 2) <=
      ((Finset.univ : Finset (Fin 2)).sum
        (fun a : Fin 2 => twoArmModel.gap a)) *
        (((etcSpec.explorationPulls : Nat) : Rat)) := by
  exact
    ETC.pseudoRegret_actionWithCommit_explorationPulls_mul_K_le_sum_gap_mul_explorationPulls
      etcSpec twoArmModel commitArm

example (commitArm : Fin 2) (r : Nat) :
    pseudoRegret twoArmModel (ETC.actionWithCommit etcSpec commitArm)
        (etcSpec.explorationPulls * 2 + r) <=
      (Finset.univ : Finset (Fin 2)).sum
        (fun a : Fin 2 =>
          twoArmModel.gap a *
            (((etcSpec.explorationPulls +
                (if commitArm = a then r else 0) : Nat) : Rat))) := by
  exact
    ETC.pseudoRegret_actionWithCommit_explorationPulls_mul_K_add_le_sum_gap_mul_suffix_count_budget
      etcSpec twoArmModel commitArm r

example (commitArm : Fin 2) (r : Nat) :
    pseudoRegret twoArmModel (ETC.actionWithCommit etcSpec commitArm)
        (etcSpec.explorationPulls * 2 + r) <=
      ((Finset.univ : Finset (Fin 2)).sum
        (fun a : Fin 2 => twoArmModel.gap a)) *
        ((((etcSpec.explorationPulls + r : Nat) : Rat))) := by
  exact
    ETC.pseudoRegret_actionWithCommit_explorationPulls_mul_K_add_le_sum_gap_mul_explorationPulls_add_suffix
      etcSpec twoArmModel commitArm r

example (commitArm : Fin 2) (r : Nat) :
    pseudoRegret twoArmModel (ETC.actionWithCommit etcSpec commitArm)
        (etcSpec.explorationPulls * 2 + r) =
      pseudoRegret twoArmModel (ETC.actionWithCommit etcSpec commitArm)
        (etcSpec.explorationPulls * 2) +
        (((r : Nat) : Rat) * twoArmModel.gap commitArm) := by
  exact
    ETC.pseudoRegret_actionWithCommit_explorationPulls_mul_K_add_eq_add_suffix_gap
      etcSpec twoArmModel commitArm r

example (commitArm : Fin 2) (r : Nat) :
    pseudoRegret twoArmModel (ETC.actionWithCommit etcSpec commitArm)
        (etcSpec.explorationPulls * 2 + r) <=
      ((Finset.univ : Finset (Fin 2)).sum
        (fun a : Fin 2 => twoArmModel.gap a)) *
        (((etcSpec.explorationPulls : Nat) : Rat)) +
      (((r : Nat) : Rat) * twoArmModel.gap commitArm) := by
  exact
    ETC.pseudoRegret_actionWithCommit_explorationPulls_mul_K_add_le_sum_gap_mul_explorationPulls_add_suffix_gap
      etcSpec twoArmModel commitArm r

example (r : Nat) :
    pseudoRegret twoArmModel (ETC.actionWithCommit etcSpec twoArmModel.bestArm)
        (etcSpec.explorationPulls * 2 + r) =
      pseudoRegret twoArmModel (ETC.actionWithCommit etcSpec twoArmModel.bestArm)
        (etcSpec.explorationPulls * 2) := by
  exact
    ETC.pseudoRegret_actionWithCommit_explorationPulls_mul_K_add_eq_of_commitArm_eq_bestArm
      etcSpec twoArmModel twoArmModel.bestArm r rfl

example (r : Nat) :
    pseudoRegret twoArmModel (ETC.actionWithCommit etcSpec twoArmModel.bestArm)
        (etcSpec.explorationPulls * 2 + r) <=
      ((Finset.univ : Finset (Fin 2)).sum
        (fun a : Fin 2 => twoArmModel.gap a)) *
        (((etcSpec.explorationPulls : Nat) : Rat)) := by
  exact
    ETC.pseudoRegret_actionWithCommit_explorationPulls_mul_K_add_le_sum_gap_mul_explorationPulls_of_commitArm_eq_bestArm
      etcSpec twoArmModel twoArmModel.bestArm r rfl

example {Omega : Type} (commit : Omega -> Fin 2) (omega : Omega)
    (r : Nat) (badGapBound : Rat)
    (hbadGap :
      forall a : Fin 2, (a = twoArmModel.bestArm -> False) ->
        twoArmModel.gap a <= badGapBound) :
    pseudoRegret twoArmModel (ETC.actionWithCommit etcSpec (commit omega))
        (etcSpec.explorationPulls * 2 + r) <=
      ((Finset.univ : Finset (Fin 2)).sum
        (fun a : Fin 2 => twoArmModel.gap a)) *
        (((etcSpec.explorationPulls : Nat) : Rat)) +
      (((r : Nat) : Rat) *
        (if commit omega = twoArmModel.bestArm then 0 else badGapBound)) := by
  exact
    ETC.pseudoRegret_actionWithCommit_choice_le_sum_gap_mul_explorationPulls_add_suffix_badGap
      etcSpec twoArmModel commit r badGapBound hbadGap omega

example {Omega : Type} [MeasurableSpace Omega]
    (mu : MeasureTheory.Measure Omega) [MeasureTheory.IsProbabilityMeasure mu]
    (commit : Omega -> Fin 2) (r : Nat)
    (badGapBound : Rat) (pWrong : ENNReal)
    (hbadGap :
      forall a : Fin 2, (a = twoArmModel.bestArm -> False) ->
        twoArmModel.gap a <= badGapBound)
    (hmeas_wrong :
      MeasurableSet
        {omega : Omega | commit omega = twoArmModel.bestArm -> False})
    (hprob_wrong :
      mu {omega : Omega | commit omega = twoArmModel.bestArm -> False} <=
        pWrong) :
    MeasureTheory.lintegral mu
      (fun omega : Omega =>
        ENNReal.ofReal
          (((pseudoRegret twoArmModel
              (ETC.actionWithCommit etcSpec (commit omega))
              (etcSpec.explorationPulls * 2 + r) : Rat) : Real))) <=
    ENNReal.ofReal
      (((((Finset.univ : Finset (Fin 2)).sum
        (fun a : Fin 2 => twoArmModel.gap a)) *
        (((etcSpec.explorationPulls : Nat) : Rat)) : Rat) : Real)) +
    ENNReal.ofReal
      ((((((r : Nat) : Rat) * badGapBound : Rat) : Real))) * pWrong := by
  exact
    ETC.lintegral_ofReal_pseudoRegret_actionWithCommit_choice_le_exploration_add_suffix_badGap_prob
      mu etcSpec twoArmModel commit r badGapBound pWrong
      hbadGap hmeas_wrong hprob_wrong

example :
    pseudoRegret twoArmModel (fun _ => twoArmModel.bestArm) (2 + 5) =
      pseudoRegret twoArmModel (fun _ => twoArmModel.bestArm) 2 := by
  apply pseudoRegret_add_eq_of_forall_bestArm_between
  intro _s _hlo _hhi
  rfl

example :
    pseudoRegret twoArmModel (fun _ => twoArmModel.bestArm) (2 + 5) =
      pseudoRegret twoArmModel (fun _ => twoArmModel.bestArm) 2 := by
  apply pseudoRegret_add_eq_of_forall_gap_zero_between
  intro _s _hlo _hhi
  simp

example {Omega : Type} {K : Nat}
    [MeasurableSpace Omega]
    (hK : 0 < K)
    (mu : MeasureTheory.Measure Omega) [MeasureTheory.IsFiniteMeasure mu]
    (spec : ETC.Spec K)
    (model : FiniteBanditModel K)
    (commitArm : Fin K)
    (reward : Omega -> RewardTrace Rat)
    (c : Fin K -> Nat -> NNReal)
    (hexplorationPulls_pos : 0 < spec.explorationPulls)
    (h_indep :
      forall a : Fin K, (a = model.bestArm -> False) ->
        ProbabilityTheory.iIndepFun
          (fun t omega =>
            ETC.centeredPairwiseRewardDiff
              spec model commitArm reward a t omega)
          mu)
    (h_subG :
      forall a : Fin K, (a = model.bestArm -> False) ->
        forall t, t ∈ Finset.range (spec.explorationPulls * K) ->
          ProbabilityTheory.HasSubgaussianMGF
            (fun omega =>
              ETC.centeredPairwiseRewardDiff
                spec model commitArm reward a t omega)
            (c a t) mu) :
    mu {omega : Omega |
        (ETC.argmaxCommitOracle hK).choose
          (fun a : Fin K =>
            ETC.empMeanAtExploration spec commitArm (reward omega) a) =
          model.bestArm -> False} <=
    ((Finset.univ : Finset (Fin K)).filter
      (fun a : Fin K => a = model.bestArm -> False)).sum
      (ETC.centeredDiffSubGaussianTail spec model c) := by
  exact
    ETC.prob_argmaxCommitOracle_ne_bestArm_le_filtered_sum_centeredDiffSubGaussianTail
      hK mu spec model commitArm reward c hexplorationPulls_pos h_indep h_subG

example {Omega : Type} {K : Nat}
    [MeasurableSpace Omega]
    (mu : MeasureTheory.Measure Omega)
    (spec : ETC.Spec K)
    (model : FiniteBanditModel K)
    (commitArm : Fin K)
    (reward : Omega -> RewardTrace Rat)
    (h_reward_indep :
      ProbabilityTheory.iIndepFun
        (fun t omega => reward omega t) mu) :
    forall a : Fin K, (a = model.bestArm -> False) ->
      ProbabilityTheory.iIndepFun
        (fun t omega =>
          ETC.centeredPairwiseRewardDiff spec model commitArm reward a t omega)
        mu := by
  exact
    ETC.iIndepFun_centeredPairwiseRewardDiff_of_iIndepFun_reward
      mu spec model commitArm reward h_reward_indep

example {Omega : Type} {K : Nat}
    [MeasurableSpace Omega]
    (hK : 0 < K)
    (mu : MeasureTheory.Measure Omega) [MeasureTheory.IsFiniteMeasure mu]
      [MeasureTheory.IsZeroOrProbabilityMeasure mu]
    (spec : ETC.Spec K)
    (model : FiniteBanditModel K)
    (commitArm : Fin K)
    (reward : Omega -> RewardTrace Rat)
    (cReward : Fin K -> Nat -> NNReal)
    (hexplorationPulls_pos : 0 < spec.explorationPulls)
    (h_reward_indep :
      ProbabilityTheory.iIndepFun
        (fun t omega => reward omega t) mu)
    (h_reward_subG :
      forall b : Fin K, forall t, t < spec.explorationPulls * K ->
        ProbabilityTheory.HasSubgaussianMGF
          (fun omega : Omega => (((reward omega t - model.mean b : Rat) : Real)))
          (cReward b t) mu) :
    mu {omega : Omega |
        (ETC.argmaxCommitOracle hK).choose
          (fun a : Fin K =>
            ETC.empMeanAtExploration spec commitArm (reward omega) a) =
          model.bestArm -> False} <=
    ((Finset.univ : Finset (Fin K)).filter
      (fun a : Fin K => a = model.bestArm -> False)).sum
      (ETC.centeredDiffSubGaussianTail spec model
        (ETC.centeredPairwiseRewardDiffVarianceProxy spec model commitArm cReward)) := by
  exact
    ETC.prob_argmaxCommitOracle_ne_bestArm_le_filtered_sum_centeredDiffSubGaussianTail_of_reward_iIndepFun_centeredReward_subG
      hK mu spec model commitArm reward cReward hexplorationPulls_pos
      h_reward_indep h_reward_subG

example {Omega : Type} {K : Nat}
    [MeasurableSpace Omega]
    (hK : 0 < K)
    (mu : MeasureTheory.Measure Omega) [MeasureTheory.IsProbabilityMeasure mu]
    (spec : ETC.Spec K)
    (model : FiniteBanditModel K)
    (commitArm : Fin K)
    (reward : Omega -> RewardTrace Rat)
    (lo hi : Fin K -> Nat -> Real)
    (hexplorationPulls_pos : 0 < spec.explorationPulls)
    (h_reward_indep :
      ProbabilityTheory.iIndepFun
        (fun t omega => reward omega t) mu)
    (h_reward_meas :
      forall _b : Fin K, forall t, t < spec.explorationPulls * K ->
        AEMeasurable (fun omega : Omega => (((reward omega t : Rat) : Real))) mu)
    (h_reward_bound :
      forall b : Fin K, forall t, t < spec.explorationPulls * K ->
        Filter.Eventually
          (fun omega : Omega =>
            Set.Icc (lo b t) (hi b t) (((reward omega t : Rat) : Real)))
          (MeasureTheory.ae mu))
    (h_reward_mean :
      forall b : Fin K, forall t, t < spec.explorationPulls * K ->
        MeasureTheory.integral mu
          (fun omega : Omega => (((reward omega t : Rat) : Real))) =
          (((model.mean b : Rat) : Real))) :
    mu {omega : Omega |
        (ETC.argmaxCommitOracle hK).choose
          (fun a : Fin K =>
            ETC.empMeanAtExploration spec commitArm (reward omega) a) =
          model.bestArm -> False} <=
    ((Finset.univ : Finset (Fin K)).filter
      (fun a : Fin K => a = model.bestArm -> False)).sum
      (ETC.centeredDiffSubGaussianTail spec model
        (ETC.centeredPairwiseRewardDiffVarianceProxy spec model commitArm
          (ETC.centeredRewardBoundVarianceProxy lo hi))) := by
  exact
    ETC.prob_argmaxCommitOracle_ne_bestArm_le_filtered_sum_centeredDiffSubGaussianTail_of_reward_iIndepFun_bounded_centered
      hK mu spec model commitArm reward lo hi hexplorationPulls_pos
      h_reward_indep h_reward_meas h_reward_bound h_reward_mean

example
    {Omega : Type u} {K : Nat}
    [MeasurableSpace Omega]
    (mu : MeasureTheory.Measure Omega) [MeasureTheory.IsFiniteMeasure mu]
    (reward : Omega -> RewardTrace Rat)
    (lo hi : Fin K -> Nat -> Real)
    (a : Fin K) (t : Nat)
    (hmeas : AEMeasurable
      (fun omega : Omega => (((reward omega t : Rat) : Real))) mu)
    (hbound : Filter.Eventually
      (fun omega : Omega =>
        Set.Icc (lo a t) (hi a t) (((reward omega t : Rat) : Real)))
      (MeasureTheory.ae mu)) :
    MeasureTheory.Integrable
      (fun omega : Omega => (((reward omega t : Rat) : Real))) mu := by
  exact
    ETC.centeredReward_integrable_of_mem_Icc
      mu reward lo hi a t hmeas hbound

example
    {Omega : Type u} {K : Nat}
    [MeasurableSpace Omega]
    (mu : MeasureTheory.Measure Omega) [MeasureTheory.IsProbabilityMeasure mu]
    (model : FiniteBanditModel K)
    (reward : Omega -> RewardTrace Rat)
    (a : Fin K) (t : Nat)
    (hint : MeasureTheory.Integrable
      (fun omega : Omega => (((reward omega t : Rat) : Real))) mu)
    (hmean :
      MeasureTheory.integral mu
        (fun omega : Omega => (((reward omega t : Rat) : Real))) =
      (((model.mean a : Rat) : Real))) :
    MeasureTheory.integral mu
      (fun omega : Omega =>
        (((reward omega t - model.mean a : Rat) : Real))) = 0 := by
  exact
    ETC.centeredReward_integral_eq_zero_of_integral_eq_mean
      mu model reward a t hint hmean

example
    {Omega : Type u} {K : Nat}
    [MeasurableSpace Omega]
    (mu : MeasureTheory.Measure Omega) [MeasureTheory.IsProbabilityMeasure mu]
    (model : FiniteBanditModel K)
    (reward : Omega -> RewardTrace Rat)
    (lo hi : Fin K -> Nat -> Real)
    (a : Fin K) (t : Nat)
    (hmeas : AEMeasurable
      (fun omega : Omega => (((reward omega t : Rat) : Real))) mu)
    (hbound : Filter.Eventually
      (fun omega : Omega =>
        Set.Icc (lo a t) (hi a t) (((reward omega t : Rat) : Real)))
      (MeasureTheory.ae mu))
    (hmean :
      MeasureTheory.integral mu
        (fun omega : Omega => (((reward omega t : Rat) : Real))) =
      (((model.mean a : Rat) : Real))) :
    MeasureTheory.integral mu
      (fun omega : Omega =>
        (((reward omega t - model.mean a : Rat) : Real))) = 0 := by
  exact
    ETC.centeredReward_integral_eq_zero_of_mem_Icc_integral_eq_mean
      mu model reward lo hi a t hmeas hbound hmean

example
    {Omega : Type u} {K : Nat}
    [MeasurableSpace Omega]
    (hK : 0 < K)
    (mu : MeasureTheory.Measure Omega) [MeasureTheory.IsProbabilityMeasure mu]
    (spec : ETC.Spec K)
    (model : FiniteBanditModel K)
    (commitArm : Fin K)
    (reward : Omega -> RewardTrace Rat)
    (lo hi : Fin K -> Nat -> Real)
    (hexplorationPulls_pos : 0 < spec.explorationPulls)
    (h_reward_indep :
      ProbabilityTheory.iIndepFun
        (fun t omega => reward omega t) mu)
    (h_reward_meas :
      forall t, t < spec.explorationPulls * K ->
        AEMeasurable (fun omega : Omega => (((reward omega t : Rat) : Real))) mu)
    (h_reward_bound :
      forall t, t < spec.explorationPulls * K ->
        Filter.Eventually
          (fun omega : Omega =>
            Set.Icc
              (lo (ETC.actionWithCommit spec commitArm t) t)
              (hi (ETC.actionWithCommit spec commitArm t) t)
              (((reward omega t : Rat) : Real)))
          (MeasureTheory.ae mu))
    (h_reward_mean :
      forall t, t < spec.explorationPulls * K ->
        MeasureTheory.integral mu
          (fun omega : Omega => (((reward omega t : Rat) : Real))) =
        (((model.mean (ETC.actionWithCommit spec commitArm t) : Rat) : Real))) :
    mu {omega : Omega |
        (ETC.argmaxCommitOracle hK).choose
          (fun a : Fin K =>
            ETC.empMeanAtExploration spec commitArm (reward omega) a) =
          model.bestArm -> False} <=
    ((Finset.univ : Finset (Fin K)).filter
      (fun a : Fin K => a = model.bestArm -> False)).sum
      (ETC.centeredDiffSubGaussianTail spec model
        (ETC.centeredPairwiseRewardDiffVarianceProxy spec model commitArm
          (ETC.centeredRewardBoundVarianceProxy lo hi))) := by
  exact
    ETC.prob_argmaxCommitOracle_ne_bestArm_le_filtered_sum_centeredDiffSubGaussianTail_of_reward_iIndepFun_action_bounded_centered
      hK mu spec model commitArm reward lo hi hexplorationPulls_pos
      h_reward_indep h_reward_meas h_reward_bound h_reward_mean

example
    {Omega : Type u} {K : Nat}
    [MeasurableSpace Omega]
    (mu : MeasureTheory.Measure Omega) [MeasureTheory.IsProbabilityMeasure mu]
    (spec : ETC.Spec K)
    (model : FiniteBanditModel K)
    (commitArm : Fin K)
    (reward : Omega -> RewardTrace Rat)
    (lo hi : Fin K -> Nat -> Real)
    (source : ETC.BoundedRewardTraceSource mu spec model commitArm reward lo hi)
    (t : Nat) (ht : t < spec.explorationPulls * K) :
    MeasureTheory.Integrable
      (fun omega : Omega => (((reward omega t : Rat) : Real))) mu := by
  exact
    ETC.centeredReward_integrable_of_boundedRewardTraceSource
      mu spec model commitArm reward lo hi source t ht

example
    {Omega : Type u} {K : Nat}
    [MeasurableSpace Omega]
    (mu : MeasureTheory.Measure Omega) [MeasureTheory.IsProbabilityMeasure mu]
    (spec : ETC.Spec K)
    (model : FiniteBanditModel K)
    (commitArm : Fin K)
    (reward : Omega -> RewardTrace Rat)
    (lo hi : Fin K -> Nat -> Real)
    (source : ETC.BoundedRewardTraceSource mu spec model commitArm reward lo hi)
    (t : Nat) (ht : t < spec.explorationPulls * K) :
    MeasureTheory.integral mu
      (fun omega : Omega =>
        (((reward omega t -
          model.mean (ETC.actionWithCommit spec commitArm t) : Rat) : Real))) =
      0 := by
  exact
    ETC.centeredReward_integral_eq_zero_of_boundedRewardTraceSource_mean
      mu spec model commitArm reward lo hi source t ht

example
    {Omega : Type u} {K : Nat}
    [mOmega : MeasurableSpace Omega]
    (mu : MeasureTheory.Measure Omega) [MeasureTheory.IsProbabilityMeasure mu]
    (spec : ETC.Spec K)
    (model : FiniteBanditModel K)
    (commitArm : Fin K)
    (reward : Omega -> RewardTrace Rat)
    (lo hi : Fin K -> Nat -> Real)
    (source : ETC.BoundedRewardTraceSource mu spec model commitArm reward lo hi)
    (hreward : forall t : Nat,
      @Measurable Omega Rat mOmega inferInstance
        (fun omega : Omega => reward omega t))
    (b : Fin K) (i : Nat)
    (hact : ETC.actionWithCommit spec commitArm (i + 1) = b)
    (ht : i + 1 < spec.explorationPulls * K) :
    Filter.EventuallyEq (MeasureTheory.ae mu)
      (MeasureTheory.condExp
        (History.historyFiltrationSucc
          (fun _omega : Omega => ETC.actionWithCommit spec commitArm)
          reward
          (fun _t : Nat => measurable_const)
          hreward i)
        mu
        (fun omega : Omega =>
          (((reward omega (i + 1) - model.mean b : Rat) : Real))))
      (fun _omega : Omega => (0 : Real)) := by
  exact
    ETC.centeredReward_succ_condExp_historyFiltrationSucc_eq_zero_of_boundedRewardTraceSource
      (mOmega := mOmega)
      mu spec model commitArm reward lo hi source hreward b i hact ht

example
    {Omega : Type u} {K : Nat}
    [mOmega : MeasurableSpace Omega]
    (mu : MeasureTheory.Measure Omega) [MeasureTheory.IsProbabilityMeasure mu]
    (spec : ETC.Spec K)
    (model : FiniteBanditModel K)
    (commitArm : Fin K)
    (reward : Omega -> RewardTrace Rat)
    (lo hi : Fin K -> Nat -> Real)
    (source : ETC.BoundedRewardTraceSource mu spec model commitArm reward lo hi)
    (hreward : forall t : Nat,
      @Measurable Omega Rat mOmega inferInstance
        (fun omega : Omega => reward omega t))
    (n : Nat) (hn : n <= spec.explorationPulls * K) :
    MartingaleDiff.SuccMartingaleDifferencePrefix
      mu
      (History.historyFiltrationSucc
        (fun _omega : Omega => ETC.actionWithCommit spec commitArm)
        reward
        (fun _t : Nat => measurable_const)
        hreward)
      (fun t omega =>
        (((reward omega t -
          model.mean (ETC.actionWithCommit spec commitArm t) :
            Rat) : Real)))
      n := by
  exact
    ETC.centeredReward_actionWithCommit_succMartingaleDifferencePrefix_of_boundedRewardTraceSource
      (mOmega := mOmega)
      mu spec model commitArm reward lo hi source hreward n hn

example
    {Omega : Type u}
    [mOmega : MeasurableSpace Omega]
    (mu : MeasureTheory.Measure Omega) [MeasureTheory.IsFiniteMeasure mu]
    (F : MeasureTheory.Filtration Nat mOmega)
    (Y : Nat -> Omega -> Real)
    (h : MartingaleDiff.SuccMartingaleDifference mu F Y) :
    MeasureTheory.Martingale
      (MartingaleDiff.partialSumsSucc Y) F mu := by
  exact
    MartingaleDiff.martingale_partialSumsSucc_of_succMartingaleDifference
      mu h

example
    {Omega : Type u}
    [mOmega : MeasurableSpace Omega]
    (mu : MeasureTheory.Measure Omega)
    (F : MeasureTheory.Filtration Nat mOmega)
    (reward baseline : Nat -> Omega -> Real)
    (n : Nat)
    (hadapted :
      MeasureTheory.StronglyAdapted F
        (MartingaleDiff.centeredRewardProcess reward baseline))
    (hintegrable :
      forall t, t < n ->
        MeasureTheory.Integrable
          (MartingaleDiff.centeredRewardProcess reward baseline t) mu)
    (hcond :
      forall i, i + 1 < n ->
        Filter.EventuallyEq (MeasureTheory.ae mu)
          (MeasureTheory.condExp (F i) mu
            (MartingaleDiff.centeredRewardProcess reward baseline (i + 1)))
          (fun _omega : Omega => (0 : Real))) :
    MartingaleDiff.SuccMartingaleDifferencePrefix mu F
      (MartingaleDiff.centeredRewardProcess reward baseline) n := by
  exact
    MartingaleDiff.succMartingaleDifferencePrefix_centeredRewardProcess_of_condExp
      mu reward baseline n hadapted hintegrable hcond

example
    {Omega : Type u}
    [mOmega : MeasurableSpace Omega]
    (mu : MeasureTheory.Measure Omega) [MeasureTheory.IsFiniteMeasure mu]
    (F : MeasureTheory.Filtration Nat mOmega)
    (reward baseline : Nat -> Omega -> Real)
    (hadapted :
      MeasureTheory.StronglyAdapted F
        (MartingaleDiff.centeredRewardProcess reward baseline))
    (hintegrable :
      forall t,
        MeasureTheory.Integrable
          (MartingaleDiff.centeredRewardProcess reward baseline t) mu)
    (hcond :
      forall i,
        Filter.EventuallyEq (MeasureTheory.ae mu)
          (MeasureTheory.condExp (F i) mu
            (MartingaleDiff.centeredRewardProcess reward baseline (i + 1)))
          (fun _omega : Omega => (0 : Real))) :
    MeasureTheory.Martingale
      (MartingaleDiff.partialSumsSucc
        (MartingaleDiff.centeredRewardProcess reward baseline)) F mu := by
  exact
    MartingaleDiff.martingale_partialSumsSucc_centeredRewardProcess_of_condExp
      mu reward baseline hadapted hintegrable hcond

example
    {Omega : Type u} {K : Nat}
    [MeasurableSpace Omega]
    (hK : 0 < K)
    (mu : MeasureTheory.Measure Omega) [MeasureTheory.IsProbabilityMeasure mu]
    (spec : ETC.Spec K)
    (model : FiniteBanditModel K)
    (commitArm : Fin K)
    (reward : Omega -> RewardTrace Rat)
    (lo hi : Fin K -> Nat -> Real)
    (hexplorationPulls_pos : 0 < spec.explorationPulls)
    (source : ETC.BoundedRewardTraceSource mu spec model commitArm reward lo hi) :
    mu {omega : Omega |
        (ETC.argmaxCommitOracle hK).choose
          (fun a : Fin K =>
            ETC.empMeanAtExploration spec commitArm (reward omega) a) =
          model.bestArm -> False} <=
    ((Finset.univ : Finset (Fin K)).filter
      (fun a : Fin K => a = model.bestArm -> False)).sum
      (ETC.centeredDiffSubGaussianTail spec model
        (ETC.centeredPairwiseRewardDiffVarianceProxy spec model commitArm
          (ETC.centeredRewardBoundVarianceProxy lo hi))) := by
  exact
    ETC.prob_argmaxCommitOracle_ne_bestArm_le_filtered_sum_centeredDiffSubGaussianTail_of_boundedRewardTraceSource
      hK mu spec model commitArm reward lo hi hexplorationPulls_pos source

example
    {Omega : Type u} {K : Nat}
    [mOmega : MeasurableSpace Omega] [StandardBorelSpace Omega]
    (mu : MeasureTheory.Measure Omega) [MeasureTheory.IsProbabilityMeasure mu]
    (spec : ETC.Spec K)
    (model : FiniteBanditModel K)
    (commitArm : Fin K)
    (reward : Omega -> RewardTrace Rat)
    (lo hi : Fin K -> Nat -> Real)
    (source : ETC.BoundedRewardTraceSource mu spec model commitArm reward lo hi)
    (hreward : forall t : Nat,
      @Measurable Omega Rat mOmega inferInstance
        (fun omega : Omega => reward omega t))
    (b : Fin K) (i : Nat)
    (hact : ETC.actionWithCommit spec commitArm (i + 1) = b)
    (ht : i + 1 < spec.explorationPulls * K) :
    ProbabilityTheory.HasCondSubgaussianMGF
      (History.historyFiltrationSucc
        (fun _omega : Omega => ETC.actionWithCommit spec commitArm)
        reward
        (fun _t : Nat => measurable_const)
        hreward i)
      ((History.historyFiltrationSucc
        (fun _omega : Omega => ETC.actionWithCommit spec commitArm)
        reward
        (fun _t : Nat => measurable_const)
        hreward).le i)
      (fun omega : Omega =>
        (((reward omega (i + 1) - model.mean b : Rat) : Real)))
      (ETC.centeredRewardBoundVarianceProxy lo hi b (i + 1)) mu := by
  exact
    ETC.centeredReward_succ_hasCondSubgaussianMGF_historyFiltrationSucc_of_boundedRewardTraceSource
      (mOmega := mOmega)
      mu spec model commitArm reward lo hi source hreward b i hact ht

noncomputable example
    {Omega : Type u} {K : Nat}
    [mOmega : MeasurableSpace Omega] [StandardBorelSpace Omega]
    (mu : MeasureTheory.Measure Omega) [MeasureTheory.IsProbabilityMeasure mu]
    (spec : ETC.Spec K)
    (model : FiniteBanditModel K)
    (commitArm : Fin K)
    (reward : Omega -> RewardTrace Rat)
    (lo hi : Fin K -> Nat -> Real)
    (source : ETC.BoundedRewardTraceSource mu spec model commitArm reward lo hi)
    (hreward : forall t : Nat,
      @Measurable Omega Rat mOmega inferInstance
        (fun omega : Omega => reward omega t))
    (tail : Fin K -> ENNReal)
    (horizon_pos : 0 < spec.explorationPulls * K)
    (htail :
      forall a : Fin K, (a = model.bestArm -> False) ->
        ENNReal.ofReal
          (Real.exp
            (-(ETC.centeredPairwiseGapThreshold spec model a) ^ 2 /
              (2 *
                (((Finset.range (spec.explorationPulls * K)).sum
                  (fun t =>
                    ETC.centeredPairwiseRewardDiffVarianceProxy
                      spec model commitArm
                      (ETC.centeredRewardBoundVarianceProxy lo hi) a t) :
                    NNReal) : Real)))) <=
          tail a) :
    ETC.CenteredRewardCondSubGaussianWitnesses
      mu spec model commitArm reward tail := by
  exact
    ETC.centeredRewardCondSubGaussianWitnesses_of_boundedRewardTraceSource
      (mOmega := mOmega)
      mu spec model commitArm reward lo hi source hreward tail horizon_pos htail

example
    {Omega : Type u} {K : Nat}
    [mOmega : MeasurableSpace Omega] [StandardBorelSpace Omega]
    (mu : MeasureTheory.Measure Omega) [MeasureTheory.IsProbabilityMeasure mu]
    (spec : ETC.Spec K)
    (model : FiniteBanditModel K)
    (commitArm : Fin K)
    (reward : Omega -> RewardTrace Rat)
    (lo hi : Fin K -> Nat -> Real)
    (source : ETC.BoundedRewardTraceSource mu spec model commitArm reward lo hi)
    (hreward : forall t : Nat,
      @Measurable Omega Rat mOmega inferInstance
        (fun omega : Omega => reward omega t))
    (tail : Fin K -> ENNReal)
    (horizon_pos : 0 < spec.explorationPulls * K)
    (hexplorationPulls_pos : 0 < spec.explorationPulls)
    (htail :
      forall a : Fin K, (a = model.bestArm -> False) ->
        ENNReal.ofReal
          (Real.exp
            (-(ETC.centeredPairwiseGapThreshold spec model a) ^ 2 /
              (2 *
                (((Finset.range (spec.explorationPulls * K)).sum
                  (fun t =>
                    ETC.centeredPairwiseRewardDiffVarianceProxy
                      spec model commitArm
                      (ETC.centeredRewardBoundVarianceProxy lo hi) a t) :
                    NNReal) : Real)))) <=
          tail a) :
    ETC.PairwiseEmpMeanTailContract
      mu spec model commitArm reward tail := by
  exact
    ETC.pairwiseEmpMeanTailContract_of_boundedRewardTraceSource_condSubGaussian
      (mOmega := mOmega)
      mu spec model commitArm reward lo hi source hreward tail
      horizon_pos hexplorationPulls_pos htail

example
    {Omega : Type u} {K : Nat}
    [mOmega : MeasurableSpace Omega] [StandardBorelSpace Omega]
    (hK : 0 < K)
    (mu : MeasureTheory.Measure Omega) [MeasureTheory.IsProbabilityMeasure mu]
    (spec : ETC.Spec K)
    (model : FiniteBanditModel K)
    (commitArm : Fin K)
    (reward : Omega -> RewardTrace Rat)
    (lo hi : Fin K -> Nat -> Real)
    (source : ETC.BoundedRewardTraceSource mu spec model commitArm reward lo hi)
    (hreward : forall t : Nat,
      @Measurable Omega Rat mOmega inferInstance
        (fun omega : Omega => reward omega t))
    (tail : Fin K -> ENNReal)
    (horizon_pos : 0 < spec.explorationPulls * K)
    (hexplorationPulls_pos : 0 < spec.explorationPulls)
    (htail :
      forall a : Fin K, (a = model.bestArm -> False) ->
        ENNReal.ofReal
          (Real.exp
            (-(ETC.centeredPairwiseGapThreshold spec model a) ^ 2 /
              (2 *
                (((Finset.range (spec.explorationPulls * K)).sum
                  (fun t =>
                    ETC.centeredPairwiseRewardDiffVarianceProxy
                      spec model commitArm
                      (ETC.centeredRewardBoundVarianceProxy lo hi) a t) :
                    NNReal) : Real)))) <=
          tail a) :
    mu {omega : Omega |
        (ETC.argmaxCommitOracle hK).choose
          (fun a : Fin K =>
            ETC.empMeanAtExploration spec commitArm (reward omega) a) =
          model.bestArm -> False} <=
    ((Finset.univ : Finset (Fin K)).filter
      (fun a : Fin K => a = model.bestArm -> False)).sum tail := by
  exact
    ETC.prob_argmaxCommitOracle_ne_bestArm_le_filtered_sum_pairwise_tail_of_boundedRewardTraceSource_condSubGaussian
      (mOmega := mOmega)
      hK mu spec model commitArm reward lo hi source hreward tail
      horizon_pos hexplorationPulls_pos htail

noncomputable example
    {Omega : Type u} {K : Nat}
    [mOmega : MeasurableSpace Omega] [StandardBorelSpace Omega]
    (mu : MeasureTheory.Measure Omega) [MeasureTheory.IsProbabilityMeasure mu]
    (spec : ETC.Spec K)
    (model : FiniteBanditModel K)
    (commitArm : Fin K)
    (reward : Omega -> RewardTrace Rat)
    (lo hi : Fin K -> Nat -> Real)
    (source : ETC.BoundedRewardTraceSource mu spec model commitArm reward lo hi)
    (hreward : forall t : Nat,
      @Measurable Omega Rat mOmega inferInstance
        (fun omega : Omega => reward omega t))
    (horizon_pos : 0 < spec.explorationPulls * K) :
    ETC.CenteredRewardCondSubGaussianWitnesses
      mu spec model commitArm reward
      (ETC.centeredDiffSubGaussianTail spec model
        (ETC.centeredPairwiseRewardDiffVarianceProxy spec model commitArm
          (ETC.centeredRewardBoundVarianceProxy lo hi))) := by
  exact
    ETC.centeredRewardCondSubGaussianWitnesses_of_boundedRewardTraceSource_canonicalTail
      (mOmega := mOmega)
      mu spec model commitArm reward lo hi source hreward horizon_pos

example
    {Omega : Type u} {K : Nat}
    [mOmega : MeasurableSpace Omega] [StandardBorelSpace Omega]
    (mu : MeasureTheory.Measure Omega) [MeasureTheory.IsProbabilityMeasure mu]
    (spec : ETC.Spec K)
    (model : FiniteBanditModel K)
    (commitArm : Fin K)
    (reward : Omega -> RewardTrace Rat)
    (lo hi : Fin K -> Nat -> Real)
    (source : ETC.BoundedRewardTraceSource mu spec model commitArm reward lo hi)
    (hreward : forall t : Nat,
      @Measurable Omega Rat mOmega inferInstance
        (fun omega : Omega => reward omega t))
    (horizon_pos : 0 < spec.explorationPulls * K)
    (hexplorationPulls_pos : 0 < spec.explorationPulls) :
    ETC.PairwiseEmpMeanTailContract
      mu spec model commitArm reward
      (ETC.centeredDiffSubGaussianTail spec model
        (ETC.centeredPairwiseRewardDiffVarianceProxy spec model commitArm
          (ETC.centeredRewardBoundVarianceProxy lo hi))) := by
  exact
    ETC.pairwiseEmpMeanTailContract_of_boundedRewardTraceSource_condSubGaussian_canonicalTail
      (mOmega := mOmega)
      mu spec model commitArm reward lo hi source hreward
      horizon_pos hexplorationPulls_pos

example
    {Omega : Type u} {K : Nat}
    [mOmega : MeasurableSpace Omega] [StandardBorelSpace Omega]
    (hK : 0 < K)
    (mu : MeasureTheory.Measure Omega) [MeasureTheory.IsProbabilityMeasure mu]
    (spec : ETC.Spec K)
    (model : FiniteBanditModel K)
    (commitArm : Fin K)
    (reward : Omega -> RewardTrace Rat)
    (lo hi : Fin K -> Nat -> Real)
    (source : ETC.BoundedRewardTraceSource mu spec model commitArm reward lo hi)
    (hreward : forall t : Nat,
      @Measurable Omega Rat mOmega inferInstance
        (fun omega : Omega => reward omega t))
    (horizon_pos : 0 < spec.explorationPulls * K)
    (hexplorationPulls_pos : 0 < spec.explorationPulls) :
    mu {omega : Omega |
        (ETC.argmaxCommitOracle hK).choose
          (fun a : Fin K =>
            ETC.empMeanAtExploration spec commitArm (reward omega) a) =
          model.bestArm -> False} <=
    ((Finset.univ : Finset (Fin K)).filter
      (fun a : Fin K => a = model.bestArm -> False)).sum
      (ETC.centeredDiffSubGaussianTail spec model
        (ETC.centeredPairwiseRewardDiffVarianceProxy spec model commitArm
          (ETC.centeredRewardBoundVarianceProxy lo hi))) := by
  exact
    ETC.prob_argmaxCommitOracle_ne_bestArm_le_filtered_sum_centeredDiffSubGaussianTail_of_boundedRewardTraceSource_condSubGaussian
      (mOmega := mOmega)
      hK mu spec model commitArm reward lo hi source hreward
      horizon_pos hexplorationPulls_pos

example
    {K : Nat}
    (coordLaw : Nat -> MeasureTheory.Measure Rat)
    [forall t : Nat, MeasureTheory.IsProbabilityMeasure (coordLaw t)]
    (model : FiniteBanditModel K)
    (b : Fin K) (i : Nat) :
    ProbabilityTheory.Indep
      (MeasurableSpace.comap
        (fun omega : RewardTrace Rat =>
          (((omega (i + 1) - model.mean b : Rat) : Real)))
        inferInstance)
      (iSup fun j : Nat =>
        iSup fun _h : j <= i =>
          MeasurableSpace.comap
            (fun omega : RewardTrace Rat => omega j) inferInstance)
      (MeasureTheory.Measure.infinitePi coordLaw) := by
  exact
    ETC.indep_centeredReward_succ_pastReward_iSup_infinitePi
      coordLaw model b i

example
    {K : Nat}
    (coordLaw : Nat -> MeasureTheory.Measure Rat)
    [forall t : Nat, MeasureTheory.IsProbabilityMeasure (coordLaw t)]
    (spec : ETC.Spec K)
    (model : FiniteBanditModel K)
    (commitArm : Fin K)
    (b : Fin K) (i : Nat) :
    ProbabilityTheory.Indep
      (MeasurableSpace.comap
        (fun omega : RewardTrace Rat =>
          (((omega (i + 1) - model.mean b : Rat) : Real)))
        inferInstance)
      (History.historyFiltrationSucc
        (fun _omega : RewardTrace Rat => ETC.actionWithCommit spec commitArm)
        (fun omega : RewardTrace Rat => omega)
        (fun _t : Nat => measurable_const)
        (fun t : Nat => measurable_pi_apply t)
        i)
      (MeasureTheory.Measure.infinitePi coordLaw) := by
  exact
    ETC.indep_centeredReward_succ_historyFiltrationSucc_infinitePi
      coordLaw spec model commitArm b i

example
    {K : Nat}
    (hK : 0 < K)
    (coordLaw : Nat -> MeasureTheory.Measure Rat)
    [forall t : Nat, MeasureTheory.IsProbabilityMeasure (coordLaw t)]
    (spec : ETC.Spec K)
    (model : FiniteBanditModel K)
    (commitArm : Fin K)
    (lo hi : Fin K -> Nat -> Real)
    (hexplorationPulls_pos : 0 < spec.explorationPulls)
    (h_coord_bound :
      forall t, t < spec.explorationPulls * K ->
        Filter.Eventually
          (fun r : Rat =>
            Set.Icc
              (lo (ETC.actionWithCommit spec commitArm t) t)
              (hi (ETC.actionWithCommit spec commitArm t) t)
              (((r : Rat) : Real)))
          (MeasureTheory.ae (coordLaw t)))
    (h_coord_mean :
      forall t, t < spec.explorationPulls * K ->
        MeasureTheory.integral (coordLaw t)
          (fun r : Rat => (((r : Rat) : Real))) =
        (((model.mean (ETC.actionWithCommit spec commitArm t) : Rat) : Real))) :
    MeasureTheory.Measure.infinitePi coordLaw
      {omega : RewardTrace Rat |
        (ETC.argmaxCommitOracle hK).choose
          (fun a : Fin K =>
            ETC.empMeanAtExploration spec commitArm omega a) =
          model.bestArm -> False} <=
    ((Finset.univ : Finset (Fin K)).filter
      (fun a : Fin K => a = model.bestArm -> False)).sum
      (ETC.centeredDiffSubGaussianTail spec model
        (ETC.centeredPairwiseRewardDiffVarianceProxy spec model commitArm
          (ETC.centeredRewardBoundVarianceProxy lo hi))) := by
  exact
    ETC.prob_argmaxCommitOracle_ne_bestArm_le_filtered_sum_centeredDiffSubGaussianTail_of_infinitePi_bounded_actionMean
      hK coordLaw spec model commitArm lo hi hexplorationPulls_pos
      h_coord_bound h_coord_mean

noncomputable example
    {K : Nat}
    (coordLaw : Nat -> MeasureTheory.Measure Rat)
    [forall t : Nat, MeasureTheory.IsProbabilityMeasure (coordLaw t)]
    (spec : ETC.Spec K)
    (model : FiniteBanditModel K)
    (commitArm : Fin K)
    (lo hi : Fin K -> Nat -> Real)
    (horizon_pos : 0 < spec.explorationPulls * K)
    (h_coord_bound :
      forall t, t < spec.explorationPulls * K ->
        Filter.Eventually
          (fun r : Rat =>
            Set.Icc
              (lo (ETC.actionWithCommit spec commitArm t) t)
              (hi (ETC.actionWithCommit spec commitArm t) t)
              (((r : Rat) : Real)))
          (MeasureTheory.ae (coordLaw t)))
    (h_coord_mean :
      forall t, t < spec.explorationPulls * K ->
        MeasureTheory.integral (coordLaw t)
          (fun r : Rat => (((r : Rat) : Real))) =
        (((model.mean (ETC.actionWithCommit spec commitArm t) : Rat) : Real))) :
    ETC.CenteredRewardCondSubGaussianWitnesses
      (MeasureTheory.Measure.infinitePi coordLaw)
      spec model commitArm
      (fun omega : RewardTrace Rat => omega)
      (ETC.centeredDiffSubGaussianTail spec model
        (ETC.centeredPairwiseRewardDiffVarianceProxy spec model commitArm
          (ETC.centeredRewardBoundVarianceProxy lo hi))) := by
  exact
    ETC.centeredRewardCondSubGaussianWitnesses_of_infinitePi_bounded_actionMean_canonicalTail
      coordLaw spec model commitArm lo hi horizon_pos
      h_coord_bound h_coord_mean

example
    {K : Nat}
    (coordLaw : Nat -> MeasureTheory.Measure Rat)
    [forall t : Nat, MeasureTheory.IsProbabilityMeasure (coordLaw t)]
    (spec : ETC.Spec K)
    (model : FiniteBanditModel K)
    (commitArm : Fin K)
    (lo hi : Fin K -> Nat -> Real)
    (horizon_pos : 0 < spec.explorationPulls * K)
    (hexplorationPulls_pos : 0 < spec.explorationPulls)
    (h_coord_bound :
      forall t, t < spec.explorationPulls * K ->
        Filter.Eventually
          (fun r : Rat =>
            Set.Icc
              (lo (ETC.actionWithCommit spec commitArm t) t)
              (hi (ETC.actionWithCommit spec commitArm t) t)
              (((r : Rat) : Real)))
          (MeasureTheory.ae (coordLaw t)))
    (h_coord_mean :
      forall t, t < spec.explorationPulls * K ->
        MeasureTheory.integral (coordLaw t)
          (fun r : Rat => (((r : Rat) : Real))) =
        (((model.mean (ETC.actionWithCommit spec commitArm t) : Rat) : Real))) :
    ETC.PairwiseEmpMeanTailContract
      (MeasureTheory.Measure.infinitePi coordLaw)
      spec model commitArm
      (fun omega : RewardTrace Rat => omega)
      (ETC.centeredDiffSubGaussianTail spec model
        (ETC.centeredPairwiseRewardDiffVarianceProxy spec model commitArm
          (ETC.centeredRewardBoundVarianceProxy lo hi))) := by
  exact
    ETC.pairwiseEmpMeanTailContract_of_infinitePi_bounded_actionMean_condSubGaussian_canonicalTail
      coordLaw spec model commitArm lo hi horizon_pos hexplorationPulls_pos
      h_coord_bound h_coord_mean

example
    {K : Nat}
    (hK : 0 < K)
    (coordLaw : Nat -> MeasureTheory.Measure Rat)
    [forall t : Nat, MeasureTheory.IsProbabilityMeasure (coordLaw t)]
    (spec : ETC.Spec K)
    (model : FiniteBanditModel K)
    (commitArm : Fin K)
    (lo hi : Fin K -> Nat -> Real)
    (hexplorationPulls_pos : 0 < spec.explorationPulls)
    (h_coord_bound :
      forall t, t < spec.explorationPulls * K ->
        Filter.Eventually
          (fun r : Rat =>
            Set.Icc
              (lo (ETC.actionWithCommit spec commitArm t) t)
              (hi (ETC.actionWithCommit spec commitArm t) t)
              (((r : Rat) : Real)))
          (MeasureTheory.ae (coordLaw t)))
    (h_coord_mean :
      forall t, t < spec.explorationPulls * K ->
        MeasureTheory.integral (coordLaw t)
          (fun r : Rat => (((r : Rat) : Real))) =
        (((model.mean (ETC.actionWithCommit spec commitArm t) : Rat) : Real))) :
    MeasureTheory.Measure.infinitePi coordLaw
      {omega : RewardTrace Rat |
        (ETC.argmaxCommitOracle hK).choose
          (fun a : Fin K =>
            ETC.empMeanAtExploration spec commitArm omega a) =
          model.bestArm -> False} <=
    ((Finset.univ : Finset (Fin K)).filter
      (fun a : Fin K => a = model.bestArm -> False)).sum
      (ETC.centeredDiffSubGaussianTail spec model
        (ETC.centeredPairwiseRewardDiffVarianceProxy spec model commitArm
          (ETC.centeredRewardBoundVarianceProxy lo hi))) := by
  exact
    ETC.prob_argmaxCommitOracle_ne_bestArm_le_filtered_sum_centeredDiffSubGaussianTail_of_infinitePi_bounded_actionMean_condSubGaussian
      hK coordLaw spec model commitArm lo hi hexplorationPulls_pos
      h_coord_bound h_coord_mean

example
    {K : Nat}
    (coordLaw : Nat -> MeasureTheory.Measure Rat)
    [forall t : Nat, MeasureTheory.IsProbabilityMeasure (coordLaw t)]
    (spec : ETC.Spec K)
    (model : FiniteBanditModel K)
    (baseCommitArm : Fin K)
    (r : Nat)
    (badGapBound : Rat)
    (lo hi : Fin K -> Nat -> Real)
    (hexplorationPulls_pos : 0 < spec.explorationPulls)
    (hbadGap :
      forall a : Fin K, (a = model.bestArm -> False) ->
        model.gap a <= badGapBound)
    (h_coord_bound :
      forall t, t < spec.explorationPulls * K ->
        Filter.Eventually
          (fun rewardValue : Rat =>
            Set.Icc
              (lo (ETC.actionWithCommit spec baseCommitArm t) t)
              (hi (ETC.actionWithCommit spec baseCommitArm t) t)
              (((rewardValue : Rat) : Real)))
          (MeasureTheory.ae (coordLaw t)))
    (h_coord_mean :
      forall t, t < spec.explorationPulls * K ->
        MeasureTheory.integral (coordLaw t)
          (fun rewardValue : Rat => (((rewardValue : Rat) : Real))) =
        (((model.mean (ETC.actionWithCommit spec baseCommitArm t) : Rat) : Real))) :
    MeasureTheory.lintegral (MeasureTheory.Measure.infinitePi coordLaw)
      (fun omega : RewardTrace Rat =>
        ENNReal.ofReal
          (((pseudoRegret model
              (ETC.actionWithCommit spec
                ((ETC.argmaxCommitOracle model.hK).choose
                  (fun a : Fin K =>
                    ETC.empMeanAtExploration spec baseCommitArm omega a)))
              (spec.explorationPulls * K + r) : Rat) : Real))) <=
    ENNReal.ofReal
      (((((Finset.univ : Finset (Fin K)).sum
        (fun a : Fin K => model.gap a)) *
        (((spec.explorationPulls : Nat) : Rat)) : Rat) : Real)) +
    ENNReal.ofReal
      ((((((r : Nat) : Rat) * badGapBound : Rat) : Real))) *
      ((Finset.univ : Finset (Fin K)).filter
        (fun a : Fin K => a = model.bestArm -> False)).sum
        (ETC.centeredDiffSubGaussianTail spec model
          (ETC.centeredPairwiseRewardDiffVarianceProxy spec model baseCommitArm
            (ETC.centeredRewardBoundVarianceProxy lo hi))) := by
  exact
    ETC.lintegral_ofReal_pseudoRegret_argmaxCommitOracle_actionWithCommit_le_exploration_add_suffix_badGap_prob_of_infinitePi_bounded_actionMean
      coordLaw spec model baseCommitArm r badGapBound lo hi
      hexplorationPulls_pos hbadGap h_coord_bound h_coord_mean

example
    {K : Nat}
    (coordLaw : Nat -> MeasureTheory.Measure Rat)
    [forall t : Nat, MeasureTheory.IsProbabilityMeasure (coordLaw t)]
    (spec : ETC.Spec K)
    (model : FiniteBanditModel K)
    (baseCommitArm : Fin K)
    (r : Nat)
    (lo hi : Fin K -> Nat -> Real)
    (hexplorationPulls_pos : 0 < spec.explorationPulls)
    (h_coord_bound :
      forall t, t < spec.explorationPulls * K ->
        Filter.Eventually
          (fun rewardValue : Rat =>
            Set.Icc
              (lo (ETC.actionWithCommit spec baseCommitArm t) t)
              (hi (ETC.actionWithCommit spec baseCommitArm t) t)
              (((rewardValue : Rat) : Real)))
          (MeasureTheory.ae (coordLaw t)))
    (h_coord_mean :
      forall t, t < spec.explorationPulls * K ->
        MeasureTheory.integral (coordLaw t)
          (fun rewardValue : Rat => (((rewardValue : Rat) : Real))) =
        (((model.mean (ETC.actionWithCommit spec baseCommitArm t) : Rat) : Real))) :
    MeasureTheory.lintegral (MeasureTheory.Measure.infinitePi coordLaw)
      (fun omega : RewardTrace Rat =>
        ENNReal.ofReal
          (((pseudoRegret model
              (ETC.actionWithCommit spec
                ((ETC.argmaxCommitOracle model.hK).choose
                  (fun a : Fin K =>
                    ETC.empMeanAtExploration spec baseCommitArm omega a)))
              (spec.explorationPulls * K + r) : Rat) : Real))) <=
    ENNReal.ofReal
      (((((Finset.univ : Finset (Fin K)).sum
        (fun a : Fin K => model.gap a)) *
        (((spec.explorationPulls : Nat) : Rat)) : Rat) : Real)) +
    ENNReal.ofReal
      ((((((r : Nat) : Rat) *
        ((Finset.univ : Finset (Fin K)).sum
          (fun a : Fin K => model.gap a)) : Rat) : Real))) *
      ((Finset.univ : Finset (Fin K)).filter
        (fun a : Fin K => a = model.bestArm -> False)).sum
        (ETC.centeredDiffSubGaussianTail spec model
          (ETC.centeredPairwiseRewardDiffVarianceProxy spec model baseCommitArm
            (ETC.centeredRewardBoundVarianceProxy lo hi))) := by
  exact
    ETC.lintegral_ofReal_pseudoRegret_argmaxCommitOracle_actionWithCommit_le_exploration_add_suffix_sumGap_prob_of_infinitePi_bounded_actionMean
      coordLaw spec model baseCommitArm r lo hi
      hexplorationPulls_pos h_coord_bound h_coord_mean

example
    {K : Nat}
    (coordLaw : Nat -> MeasureTheory.Measure Rat)
    [forall t : Nat, MeasureTheory.IsProbabilityMeasure (coordLaw t)]
    (spec : ETC.Spec K)
    (model : FiniteBanditModel K)
    (baseCommitArm : Fin K)
    (r : Nat)
    (lo hi : Fin K -> Nat -> Real)
    (hexplorationPulls_pos : 0 < spec.explorationPulls)
    (h_coord_bound :
      forall t, t < spec.explorationPulls * K ->
        Filter.Eventually
          (fun rewardValue : Rat =>
            Set.Icc
              (lo (ETC.actionWithCommit spec baseCommitArm t) t)
              (hi (ETC.actionWithCommit spec baseCommitArm t) t)
              (((rewardValue : Rat) : Real)))
          (MeasureTheory.ae (coordLaw t)))
    (h_coord_mean :
      forall t, t < spec.explorationPulls * K ->
        MeasureTheory.integral (coordLaw t)
          (fun rewardValue : Rat => (((rewardValue : Rat) : Real))) =
        (((model.mean (ETC.actionWithCommit spec baseCommitArm t) : Rat) : Real))) :
    MeasureTheory.lintegral (MeasureTheory.Measure.infinitePi coordLaw)
      (fun omega : RewardTrace Rat =>
        ENNReal.ofReal
          (((pseudoRegret model
              (ETC.actionWithCommit spec
                ((ETC.argmaxCommitOracle model.hK).choose
                  (fun a : Fin K =>
                    ETC.empMeanAtExploration spec baseCommitArm omega a)))
              (spec.explorationPulls * K + r) : Rat) : Real))) <=
    ENNReal.ofReal
      (((((Finset.univ : Finset (Fin K)).sum
        (fun a : Fin K => model.gap a)) *
        (((spec.explorationPulls : Nat) : Rat)) : Rat) : Real)) +
    ENNReal.ofReal
      ((((((r : Nat) : Rat) * model.maxGap : Rat) : Real))) *
      ((Finset.univ : Finset (Fin K)).filter
        (fun a : Fin K => a = model.bestArm -> False)).sum
        (ETC.centeredDiffSubGaussianTail spec model
          (ETC.centeredPairwiseRewardDiffVarianceProxy spec model baseCommitArm
            (ETC.centeredRewardBoundVarianceProxy lo hi))) := by
  exact
    ETC.lintegral_ofReal_pseudoRegret_argmaxCommitOracle_actionWithCommit_le_exploration_add_suffix_maxGap_prob_of_infinitePi_bounded_actionMean
      coordLaw spec model baseCommitArm r lo hi
      hexplorationPulls_pos h_coord_bound h_coord_mean

example
    {K : Nat}
    (coordLaw : Nat -> MeasureTheory.Measure Rat)
    [forall t : Nat, MeasureTheory.IsProbabilityMeasure (coordLaw t)]
    (spec : ETC.Spec K)
    (model : FiniteBanditModel K)
    (baseCommitArm : Fin K)
    (r : Nat)
    (lo hi : Fin K -> Nat -> Real)
    (hexplorationPulls_pos : 0 < spec.explorationPulls)
    (h_coord_bound :
      forall t, t < spec.explorationPulls * K ->
        Filter.Eventually
          (fun rewardValue : Rat =>
            Set.Icc
              (lo (ETC.actionWithCommit spec baseCommitArm t) t)
              (hi (ETC.actionWithCommit spec baseCommitArm t) t)
              (((rewardValue : Rat) : Real)))
          (MeasureTheory.ae (coordLaw t)))
    (h_coord_mean :
      forall t, t < spec.explorationPulls * K ->
        MeasureTheory.integral (coordLaw t)
          (fun rewardValue : Rat => (((rewardValue : Rat) : Real))) =
        (((model.mean (ETC.actionWithCommit spec baseCommitArm t) : Rat) : Real))) :
    MeasureTheory.lintegral (MeasureTheory.Measure.infinitePi coordLaw)
      (fun omega : RewardTrace Rat =>
        ENNReal.ofReal
          (((pseudoRegret model
              (ETC.fixedProductArgmaxAction spec model baseCommitArm omega)
              (spec.explorationPulls * K + r) : Rat) : Real))) <=
    ETC.fixedProductMaxGapLintegralRegretBound spec model baseCommitArm r lo hi := by
  exact
    ETC.lintegral_ofReal_pseudoRegret_fixedProductArgmaxAction_le_fixedProductMaxGapLintegralRegretBound_of_infinitePi_bounded_actionMean
      coordLaw spec model baseCommitArm r lo hi
      hexplorationPulls_pos h_coord_bound h_coord_mean

example {Action : Type} (arms : Finset Action)
    (eta : Real) (w loss : Action -> Real) :
    Exp3Potential.updatedPotential arms eta w loss =
      arms.sum (fun a => w a * Real.exp (-eta * loss a)) := by
  exact Exp3Potential.updatedPotential_eq_sum arms eta w loss

example {Action : Type} (arms : Finset Action)
    (eta : Real) (w loss : Action -> Real)
    (hw : forall a, a ∈ arms -> 0 <= w a) :
    0 <= Exp3Potential.updatedPotential arms eta w loss := by
  exact Exp3Potential.updatedPotential_nonneg_of_nonneg arms eta w loss hw

example {Action : Type} (arms : Finset Action)
    (eta : Real) (w loss : Action -> Real) :
    Exp3Potential.updatedPotential arms eta w loss -
        Exp3Potential.potential arms w =
      arms.sum (fun a => w a * (Real.exp (-eta * loss a) - 1)) := by
  exact
    Exp3Potential.updatedPotential_sub_potential_eq_sum_weight_mul_exp_sub_one
      arms eta w loss

example (Phi : Nat -> Real) (T : Nat) :
    (Finset.range T).sum (fun t => Phi (t + 1) - Phi t) =
      Phi T - Phi 0 := by
  exact Exp3Potential.sum_range_forward_difference Phi T

example {Action : Type} (arms : Finset Action)
    (w : Nat -> Action -> Real) (T : Nat) :
    (Finset.range T).sum
        (fun t => Exp3Potential.potentialProcess arms w (t + 1) -
          Exp3Potential.potentialProcess arms w t) =
      Exp3Potential.potentialProcess arms w T -
        Exp3Potential.potentialProcess arms w 0 := by
  exact Exp3Potential.potentialProcess_telescope_sum_range arms w T

example {Action : Type} (arms : Finset Action)
    (p loss : Action -> Real) :
    FTRL.linearLoss arms p loss =
      arms.sum (fun a => p a * loss a) := by
  rfl

example {Action : Type}
    (feasible : (Action -> Real) -> Prop)
    (arms : Finset Action) (eta : Real)
    (regularizer : (Action -> Real) -> Real)
    (loss : Action -> Real) (p q : Action -> Real)
    (heta : 0 < eta)
    (hp : FTRL.IsRegularizedMinimizer feasible arms eta regularizer loss p)
    (hq : feasible q) :
    FTRL.linearLoss arms p loss - FTRL.linearLoss arms q loss <=
      (regularizer q - regularizer p) / eta := by
  exact
    FTRL.linearLoss_sub_le_regularizer_sub_div_of_isRegularizedMinimizer
      feasible arms eta regularizer loss p q heta hp hq

example {Action : Type}
    (arms : Finset Action) (eta : Real)
    (regularizer : (Action -> Real) -> Real)
    (loss : Action -> Real) (p q : Action -> Real)
    (heta : 0 < eta)
    (hp : FTRL.IsRegularizedMinimizer (FTRL.finiteSimplex arms) arms eta
      regularizer loss p)
    (hq : FTRL.finiteSimplex arms q) :
    FTRL.linearLoss arms p loss - FTRL.linearLoss arms q loss <=
      (regularizer q - regularizer p) / eta := by
  exact
    FTRL.linearLoss_sub_le_regularizer_sub_div_of_simplex_minimizer
      arms eta regularizer loss p q heta hp hq

example {Action : Type} (arms : Finset Action)
    (alpha : Real) (p : Action -> Real)
    (hp : FTRL.finiteSimplex arms p) :
    0 <= Tsallis.powerSum arms alpha p := by
  exact Tsallis.powerSum_nonneg_of_finiteSimplex arms alpha p hp

example {alpha : Real} (halpha : alpha ≠ 1) :
    1 - alpha ≠ 0 := by
  exact Tsallis.one_sub_exponent_ne_zero halpha

example {Action : Type} (arms : Finset Action)
    (alpha : Real) (p : Action -> Real)
    (hp : FTRL.finiteSimplex arms p) (halpha : alpha ≠ 1) :
    0 <= Tsallis.powerSum arms alpha p ∧
      1 - alpha ≠ 0 ∧
      Tsallis.negEntropyRegularizer arms alpha p =
        - ((Tsallis.powerSum arms alpha p - 1) / (1 - alpha)) := by
  exact
    Tsallis.negEntropyRegularizer_wellDefined_on_finiteSimplex
      arms alpha p hp halpha

end BanditRLProof
