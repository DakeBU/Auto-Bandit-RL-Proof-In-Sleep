import BanditRLProof.Algorithms.UCBConditionalRewardLaw
import BanditRLProof.Algorithms.UCBArmStreamProcess
import BanditRLProof.Algorithms.ETCCountLemmas

/-!
# Generated finite-history UCB policy for the practical reward-law route

This module constructs a reward-history-generated finite-arm UCB policy whose
score is exactly the realized-count score from `UCBConditionalRewardLaw`.
Successor actions `1, ..., K` initialize every arm once. Later actions maximize
the practical random-width index computed from the inclusive pair history.
-/

namespace BanditRLProof
namespace UCB

open MeasureTheory

/-- A finite pair history packaged with its dependent horizon. -/
structure SelectedPolicySuccessorFiniteHistoryState (K : Nat) where
  time : Nat
  history : History.FinitePairHistory (Fin K) Rat time

instance selectedPolicySuccessorFiniteHistoryStateMeasurableSpace (K : Nat) :
    MeasurableSpace (SelectedPolicySuccessorFiniteHistoryState K) :=
  ⊤

/-- Complete a finite pair history with a fixed pair outside its prefix. -/
def completeFinitePairHistory
    {Action Reward : Type}
    (t : Nat) (history : History.FinitePairHistory Action Reward t)
    (defaultAction : Action) (defaultReward : Reward) :
    Nat -> Action × Reward :=
  fun s =>
    if h : s <= t then
      history ⟨s, Finset.mem_Iic.mpr h⟩
    else
      (defaultAction, defaultReward)

/-- Action projection of a completed finite pair history. -/
def completeFinitePairHistoryAction
    {Action Reward : Type}
    (t : Nat) (history : History.FinitePairHistory Action Reward t)
    (defaultAction : Action) (defaultReward : Reward) :
    ActionTrace Action :=
  fun s => (completeFinitePairHistory t history defaultAction defaultReward s).1

/-- Reward projection of a completed finite pair history. -/
def completeFinitePairHistoryReward
    {Action Reward : Type}
    (t : Nat) (history : History.FinitePairHistory Action Reward t)
    (defaultAction : Action) (defaultReward : Reward) :
    RewardTrace Reward :=
  fun s => (completeFinitePairHistory t history defaultAction defaultReward s).2

@[simp]
theorem completeFinitePairHistory_finitePairHistoryOfTrace_apply_of_le
    {Action Reward : Type}
    (action : ActionTrace Action) (reward : RewardTrace Reward)
    (t s : Nat) (defaultAction : Action) (defaultReward : Reward)
    (hs : s <= t) :
    completeFinitePairHistory t
        (History.finitePairHistoryOfTrace action reward t)
        defaultAction defaultReward s =
      (action s, reward s) := by
  simp [completeFinitePairHistory, hs, History.finitePairHistoryOfTrace]

/-- Practical random-width UCB score reconstructed from one finite history. -/
noncomputable def selectedPolicySuccessorHistoryIndex
    {K : Nat}
    (sigma2 : NNReal) (T : Nat) (delta : Real)
    (defaultAction : Fin K) (t : Nat)
    (history : History.FinitePairHistory (Fin K) Rat t)
    (arm : Fin K) : Real :=
  let action :=
    completeFinitePairHistoryAction t history defaultAction (0 : Rat)
  let reward :=
    completeFinitePairHistoryReward t history defaultAction (0 : Rat)
  confidenceScore
    (fun candidate =>
      ConditionalExpectationReward.successorArmEmpiricalMean
        action reward candidate (t + 1))
    (fun candidate =>
      ConditionalExpectationReward.successorArmEmpiricalMeanFiniteArmTimePeelingRadius
        sigma2
        (ConditionalExpectationReward.successorArmPullCount
          action candidate (t + 1))
        (t + 1) (Finset.univ : Finset (Fin K)) T delta)
    arm

/-- Round-robin initialization followed by finite-history score maximization. -/
noncomputable def selectedPolicySuccessorHistoryNextArm
    {K : Nat} (hK : 0 < K)
    (sigma2 : NNReal) (T : Nat) (delta : Real)
    (defaultAction : Fin K) (t : Nat)
    (history : History.FinitePairHistory (Fin K) Rat t) : Fin K :=
  if t < K then
    initializationArm hK t
  else
    scoreArgmax hK
      (selectedPolicySuccessorHistoryIndex
        sigma2 T delta defaultAction t history)

/-- The post-initialization history selector maximizes every candidate score. -/
theorem selectedPolicySuccessorHistoryIndex_le_nextArm_of_K_le
    {K : Nat} (hK : 0 < K)
    (sigma2 : NNReal) (T : Nat) (delta : Real)
    (defaultAction : Fin K) (t : Nat)
    (history : History.FinitePairHistory (Fin K) Rat t)
    (ht : K <= t) (arm : Fin K) :
    selectedPolicySuccessorHistoryIndex
        sigma2 T delta defaultAction t history arm <=
      selectedPolicySuccessorHistoryIndex
        sigma2 T delta defaultAction t history
        (selectedPolicySuccessorHistoryNextArm
          hK sigma2 T delta defaultAction t history) := by
  rw [selectedPolicySuccessorHistoryNextArm, if_neg (not_lt_of_ge ht)]
  exact scoreArgmax_spec hK
    (selectedPolicySuccessorHistoryIndex
      sigma2 T delta defaultAction t history) arm

/--
Reconstruct the inclusive action/reward pair history from a finite reward
history. The recursion uses only the preceding reconstructed pair prefix when
selecting the next action.
-/
noncomputable def selectedPolicySuccessorPairHistory
    {K : Nat} (hK : 0 < K)
    (sigma2 : NNReal) (T : Nat) (delta : Real)
    (defaultAction : Fin K) :
    (n : Nat) -> History.FiniteRewardHistory Rat n ->
      History.FinitePairHistory (Fin K) Rat n
  | 0, rewardHistory =>
      fun i => (defaultAction, rewardHistory i)
  | n + 1, rewardHistory =>
      let previousRewardHistory : History.FiniteRewardHistory Rat n :=
        fun i => rewardHistory
          ⟨i.1, Finset.mem_Iic.mpr
            ((Finset.mem_Iic.mp i.2).trans (Nat.le_succ n))⟩
      let previousHistory :=
        selectedPolicySuccessorPairHistory hK sigma2 T delta defaultAction
          n previousRewardHistory
      let nextAction :=
        selectedPolicySuccessorHistoryNextArm
          hK sigma2 T delta defaultAction n previousHistory
      History.extendPairHistorySucc previousHistory
        (nextAction,
          rewardHistory ⟨n + 1, Finset.mem_Iic.mpr le_rfl⟩)

/-- Package the reconstructed history as the fixed policy state type. -/
noncomputable def selectedPolicySuccessorHistoryState
    {K : Nat} (hK : 0 < K)
    (sigma2 : NNReal) (T : Nat) (delta : Real)
    (defaultAction : Fin K)
    (n : Nat) (rewardHistory : History.FiniteRewardHistory Rat n) :
    SelectedPolicySuccessorFiniteHistoryState K :=
  ⟨n,
    selectedPolicySuccessorPairHistory
      hK sigma2 T delta defaultAction n rewardHistory⟩

/-- Every finite reward-history state reconstruction is measurable. -/
theorem measurable_selectedPolicySuccessorHistoryState
    {K : Nat} (hK : 0 < K)
    (sigma2 : NNReal) (T : Nat) (delta : Real)
    (defaultAction : Fin K) (n : Nat) :
    Measurable
      (selectedPolicySuccessorHistoryState
        hK sigma2 T delta defaultAction n) := by
  exact measurable_of_countable _

/-- Measurable policy reading the packaged finite pair history. -/
noncomputable def selectedPolicySuccessorHistoryPolicy
    {K : Nat} (hK : 0 < K)
    (sigma2 : NNReal) (T : Nat) (delta : Real)
    (defaultAction : Fin K) (_t : Nat) :
    Policy.MeasurablePolicy
      (SelectedPolicySuccessorFiniteHistoryState K) (Fin K) where
  action := fun state =>
    selectedPolicySuccessorHistoryNextArm
      hK sigma2 T delta defaultAction state.time state.history
  measurable_action := by
    exact Measurable.of_comap_le le_top

/-- Generated action trace for the concrete finite-history UCB policy. -/
noncomputable def selectedPolicySuccessorGeneratedUCBAction
    {Omega : Type} {K : Nat} (hK : 0 < K)
    (sigma2 : NNReal) (T : Nat) (delta : Real)
    (defaultAction : Fin K)
    (reward : Omega -> RewardTrace Rat) :
    Omega -> ActionTrace (Fin K) :=
  ConditionalExpectationReward.generatedActionFromRewardHistory
    (selectedPolicySuccessorHistoryPolicy
      hK sigma2 T delta defaultAction)
    (selectedPolicySuccessorHistoryState
      hK sigma2 T delta defaultAction)
    defaultAction reward

@[simp]
theorem selectedPolicySuccessorGeneratedUCBAction_succ
    {Omega : Type} {K : Nat} (hK : 0 < K)
    (sigma2 : NNReal) (T : Nat) (delta : Real)
    (defaultAction : Fin K)
    (reward : Omega -> RewardTrace Rat) (omega : Omega) (t : Nat) :
    selectedPolicySuccessorGeneratedUCBAction
        hK sigma2 T delta defaultAction reward omega (t + 1) =
      selectedPolicySuccessorHistoryNextArm
        hK sigma2 T delta defaultAction t
        (selectedPolicySuccessorPairHistory
          hK sigma2 T delta defaultAction t
          (History.finiteRewardHistoryOfTrace (reward omega) t)) := by
  simp [selectedPolicySuccessorGeneratedUCBAction,
    ConditionalExpectationReward.generatedActionFromRewardHistory,
    Policy.generatedActionTraceSucc,
    selectedPolicySuccessorHistoryPolicy,
    selectedPolicySuccessorHistoryState]

/-- The reconstructed pair state is exactly the generated trace prefix. -/
theorem selectedPolicySuccessorPairHistory_eq_finitePairHistoryOfTrace
    {Omega : Type} {K : Nat} (hK : 0 < K)
    (sigma2 : NNReal) (T : Nat) (delta : Real)
    (defaultAction : Fin K)
    (reward : Omega -> RewardTrace Rat) (omega : Omega) (n : Nat) :
    selectedPolicySuccessorPairHistory
        hK sigma2 T delta defaultAction n
        (History.finiteRewardHistoryOfTrace (reward omega) n) =
      History.finitePairHistoryOfTrace
        (selectedPolicySuccessorGeneratedUCBAction
          hK sigma2 T delta defaultAction reward omega)
        (reward omega) n := by
  induction n with
  | zero =>
      funext i
      have hi : i.1 = 0 :=
        Nat.eq_zero_of_le_zero (Finset.mem_Iic.mp i.2)
      have hi_subtype :
          i = ⟨0, Finset.mem_Iic.mpr le_rfl⟩ := Subtype.ext hi
      subst i
      simp [selectedPolicySuccessorPairHistory,
        selectedPolicySuccessorGeneratedUCBAction,
        ConditionalExpectationReward.generatedActionFromRewardHistory,
        Policy.generatedActionTraceSucc]
  | succ n ih =>
      let previousRewardHistory : History.FiniteRewardHistory Rat n :=
        fun i =>
          History.finiteRewardHistoryOfTrace (reward omega) (n + 1)
            ⟨i.1, Finset.mem_Iic.mpr
              ((Finset.mem_Iic.mp i.2).trans (Nat.le_succ n))⟩
      have hprevious : previousRewardHistory =
          History.finiteRewardHistoryOfTrace (reward omega) n := by
        rfl
      rw [selectedPolicySuccessorPairHistory]
      change
        History.extendPairHistorySucc
            (selectedPolicySuccessorPairHistory
              hK sigma2 T delta defaultAction n previousRewardHistory)
            _ = _
      rw [hprevious, ih, History.finitePairHistoryOfTrace_succ]
      apply congrArg
        (History.extendPairHistorySucc
          (History.finitePairHistoryOfTrace
            (selectedPolicySuccessorGeneratedUCBAction
              hK sigma2 T delta defaultAction reward omega)
            (reward omega) n))
      apply Prod.ext
      · exact (selectedPolicySuccessorGeneratedUCBAction_succ
          hK sigma2 T delta defaultAction reward omega n).symm
      · rfl

private theorem sumRewards_eq_of_forall_lt
    {Action : Type} [DecidableEq Action]
    (action action' : ActionTrace Action)
    (reward reward' : RewardTrace Real) (arm : Action) :
    forall n : Nat,
      (forall s, s < n -> action s = action' s) ->
      (forall s, s < n -> reward s = reward' s) ->
      sumRewards action reward arm n =
        sumRewards action' reward' arm n := by
  intro n
  induction n with
  | zero =>
      intro _haction _hreward
      simp
  | succ n ih =>
      intro haction hreward
      rw [sumRewards_succ, sumRewards_succ]
      rw [ih
        (fun s hs => haction s (Nat.lt_trans hs (Nat.lt_succ_self n)))
        (fun s hs => hreward s (Nat.lt_trans hs (Nat.lt_succ_self n)))]
      rw [haction n (Nat.lt_succ_self n), hreward n (Nat.lt_succ_self n)]

/-- Completed actual prefixes preserve every successor pull count. -/
theorem successorArmPullCount_completeFinitePairHistory
    {K : Nat}
    (action : ActionTrace (Fin K)) (reward : RewardTrace Rat)
    (defaultAction : Fin K) (t : Nat) (arm : Fin K) :
    ConditionalExpectationReward.successorArmPullCount
        (completeFinitePairHistoryAction t
          (History.finitePairHistoryOfTrace action reward t)
          defaultAction (0 : Rat)) arm (t + 1) =
      ConditionalExpectationReward.successorArmPullCount
        action arm (t + 1) := by
  unfold ConditionalExpectationReward.successorArmPullCount
  simp only [Nat.add_sub_cancel]
  apply pullCount_eq_of_forall_lt
  intro s hs
  simp [completeFinitePairHistoryAction,
    completeFinitePairHistory, Nat.succ_le_iff.mpr hs]

/-- Completed actual prefixes preserve every successor selected reward sum. -/
theorem successorArmRewardSum_completeFinitePairHistory
    {K : Nat}
    (action : ActionTrace (Fin K)) (reward : RewardTrace Rat)
    (defaultAction : Fin K) (t : Nat) (arm : Fin K) :
    ConditionalExpectationReward.successorArmRewardSum
        (completeFinitePairHistoryAction t
          (History.finitePairHistoryOfTrace action reward t)
          defaultAction (0 : Rat))
        (completeFinitePairHistoryReward t
          (History.finitePairHistoryOfTrace action reward t)
          defaultAction (0 : Rat)) arm (t + 1) =
      ConditionalExpectationReward.successorArmRewardSum
        action reward arm (t + 1) := by
  unfold ConditionalExpectationReward.successorArmRewardSum
  simp only [Nat.add_sub_cancel]
  apply sumRewards_eq_of_forall_lt
  · intro s hs
    simp [completeFinitePairHistoryAction,
      completeFinitePairHistory, Nat.succ_le_iff.mpr hs]
  · intro s hs
    simp [completeFinitePairHistoryReward,
      completeFinitePairHistory, Nat.succ_le_iff.mpr hs]

/-- The finite-history score is exactly the score on the generated trace. -/
theorem selectedPolicySuccessorHistoryIndex_finitePairHistoryOfTrace
    {Omega : Type} {K : Nat}
    (action : Omega -> ActionTrace (Fin K))
    (reward : Omega -> RewardTrace Rat)
    (sigma2 : NNReal) (T : Nat) (delta : Real)
    (defaultAction : Fin K) (omega : Omega) (t : Nat) (arm : Fin K) :
    selectedPolicySuccessorHistoryIndex sigma2 T delta defaultAction t
        (History.finitePairHistoryOfTrace
          (action omega) (reward omega) t) arm =
      selectedPolicySuccessorIndexAt
        action reward sigma2 (Finset.univ : Finset (Fin K)) T delta
          omega t arm := by
  unfold selectedPolicySuccessorHistoryIndex
    selectedPolicySuccessorIndexAt confidenceScore
    selectedPolicySuccessorEmpiricalMeanAt selectedPolicySuccessorRadiusAt
    ConditionalExpectationReward.successorArmEmpiricalMean
  simp only
  rw [successorArmRewardSum_completeFinitePairHistory,
    successorArmPullCount_completeFinitePairHistory]

/-- During initialization, successor action `t + 1` follows round robin. -/
theorem selectedPolicySuccessorGeneratedUCBAction_succ_eq_initializationArm_of_lt
    {Omega : Type} {K : Nat} (hK : 0 < K)
    (sigma2 : NNReal) (T : Nat) (delta : Real)
    (defaultAction : Fin K)
    (reward : Omega -> RewardTrace Rat) (omega : Omega)
    (t : Nat) (ht : t < K) :
    selectedPolicySuccessorGeneratedUCBAction
        hK sigma2 T delta defaultAction reward omega (t + 1) =
      initializationArm hK t := by
  simp [selectedPolicySuccessorHistoryNextArm, ht]

/-- Every arm appears once among successor actions `1, ..., K`. -/
theorem successorArmPullCount_selectedPolicySuccessorGeneratedUCBAction_K_add_one_eq_one
    {Omega : Type} {K : Nat} (hK : 0 < K)
    (sigma2 : NNReal) (T : Nat) (delta : Real)
    (defaultAction : Fin K)
    (reward : Omega -> RewardTrace Rat) (omega : Omega) (arm : Fin K) :
    ConditionalExpectationReward.successorArmPullCount
        (selectedPolicySuccessorGeneratedUCBAction
          hK sigma2 T delta defaultAction reward omega)
        arm (K + 1) = 1 := by
  let spec : ETC.Spec K := { hK := hK, explorationPulls := 1 }
  let action := selectedPolicySuccessorGeneratedUCBAction
    hK sigma2 T delta defaultAction reward omega
  have haction : forall t, t < K ->
      action (t + 1) = ETC.exploreArm spec t := by
    intro t ht
    exact selectedPolicySuccessorGeneratedUCBAction_succ_eq_initializationArm_of_lt
      hK sigma2 T delta defaultAction reward omega t ht
  unfold ConditionalExpectationReward.successorArmPullCount
  simp only [Nat.add_sub_cancel]
  have hcount :
      pullCount (fun i => action (i + 1)) arm K =
        pullCount (ETC.exploreArm spec) arm K := by
    apply pullCount_eq_of_forall_lt
    exact haction
  rw [hcount]
  exact ETC.pullCount_exploreArm_K_eq_one spec arm

/-- After the successor initialization cycle, every arm count is positive. -/
theorem successorArmPullCount_selectedPolicySuccessorGeneratedUCBAction_pos_of_K_le
    {Omega : Type} {K : Nat} (hK : 0 < K)
    (sigma2 : NNReal) (T : Nat) (delta : Real)
    (defaultAction : Fin K)
    (reward : Omega -> RewardTrace Rat) (omega : Omega)
    (arm : Fin K) (t : Nat) (ht : K <= t) :
    0 < ConditionalExpectationReward.successorArmPullCount
      (selectedPolicySuccessorGeneratedUCBAction
        hK sigma2 T delta defaultAction reward omega)
      arm (t + 1) := by
  let action := selectedPolicySuccessorGeneratedUCBAction
    hK sigma2 T delta defaultAction reward omega
  have hmono := pullCount_mono
    (fun i => action (i + 1)) arm ht
  have hinit :=
    successorArmPullCount_selectedPolicySuccessorGeneratedUCBAction_K_add_one_eq_one
      hK sigma2 T delta defaultAction reward omega arm
  unfold ConditionalExpectationReward.successorArmPullCount at hinit ⊢
  simp only [Nat.add_sub_cancel] at hinit ⊢
  have hinit' : pullCount (fun i => action (i + 1)) arm K = 1 := by
    simpa [action] using hinit
  rw [hinit'] at hmono
  have hone_le : 1 <= pullCount (fun i => action (i + 1)) arm t := by
    exact hmono
  exact hone_le

/--
Concrete initialized score-max source for the practical selected-policy UCB
route. Charged times are exactly the post-initialization times below `T`.
-/
noncomputable def selectedPolicySuccessorGeneratedUCBInitializedScoreMaxSource
    {Omega : Type} {K : Nat} (hK : 0 < K)
    (reward : Omega -> RewardTrace Rat)
    (armMean : Fin K -> Rat)
    (sigma2 : NNReal) (T : Nat) (delta : Real)
    (defaultAction best : Fin K) :
    SelectedPolicySuccessorInitializedScoreMaxSource
      (selectedPolicySuccessorGeneratedUCBAction
        hK sigma2 T delta defaultAction reward)
      reward Finset.univ armMean sigma2 T delta where
  times := (Finset.range T).filter (fun t => K <= t)
  best := best
  chosen := fun omega t =>
    selectedPolicySuccessorGeneratedUCBAction
      hK sigma2 T delta defaultAction reward omega (t + 1)
  times_lt := by
    intro t ht
    exact Finset.mem_range.mp (Finset.mem_filter.mp ht).1
  best_mem := Finset.mem_univ best
  chosen_mem := by
    intro omega t ht
    exact Finset.mem_univ _
  best_count_pos := by
    intro omega t ht
    exact
      successorArmPullCount_selectedPolicySuccessorGeneratedUCBAction_pos_of_K_le
        hK sigma2 T delta defaultAction reward omega best t
        (Finset.mem_filter.mp ht).2
  chosen_count_pos := by
    intro omega t ht
    exact
      successorArmPullCount_selectedPolicySuccessorGeneratedUCBAction_pos_of_K_le
        hK sigma2 T delta defaultAction reward omega
        (selectedPolicySuccessorGeneratedUCBAction
          hK sigma2 T delta defaultAction reward omega (t + 1))
        t (Finset.mem_filter.mp ht).2
  score_max := by
    intro omega t ht
    let action := selectedPolicySuccessorGeneratedUCBAction
      hK sigma2 T delta defaultAction reward
    let history := History.finitePairHistoryOfTrace
      (action omega) (reward omega) t
    have hhistory :
        selectedPolicySuccessorPairHistory
            hK sigma2 T delta defaultAction t
            (History.finiteRewardHistoryOfTrace (reward omega) t) =
          history := by
      exact selectedPolicySuccessorPairHistory_eq_finitePairHistoryOfTrace
        hK sigma2 T delta defaultAction reward omega t
    have hselected :
        action omega (t + 1) =
          selectedPolicySuccessorHistoryNextArm
            hK sigma2 T delta defaultAction t history := by
      simpa [action, history, hhistory] using
        (selectedPolicySuccessorGeneratedUCBAction_succ
          hK sigma2 T delta defaultAction reward omega t)
    have hmax :=
      selectedPolicySuccessorHistoryIndex_le_nextArm_of_K_le
        hK sigma2 T delta defaultAction t history
        (Finset.mem_filter.mp ht).2 best
    rw [← hselected] at hmax
    simpa [action, history] using
      (show
        selectedPolicySuccessorIndexAt
            action reward sigma2 Finset.univ T delta omega t best <=
          selectedPolicySuccessorIndexAt
            action reward sigma2 Finset.univ T delta omega t
              (action omega (t + 1)) by
        simpa only [
          ← selectedPolicySuccessorHistoryIndex_finitePairHistoryOfTrace
            action reward sigma2 T delta defaultAction omega t best,
          ← selectedPolicySuccessorHistoryIndex_finitePairHistoryOfTrace
            action reward sigma2 T delta defaultAction omega t
              (action omega (t + 1))] using hmax)

/--
If the final pull count exceeds `B`, some selected time has prior pull count at
least `B`.
-/
theorem exists_selected_with_threshold_le_prior_pullCount
    {Action : Type} [DecidableEq Action]
    (action : ActionTrace Action) (arm : Action) (T B : Nat)
    (hcount : B < pullCount action arm T) :
    exists t, t < T ∧ action t = arm ∧ B <= pullCount action arm t := by
  induction T with
  | zero => simp at hcount
  | succ T ih =>
      by_cases hselected : action T = arm
      · by_cases hprior : B <= pullCount action arm T
        · exact ⟨T, Nat.lt_succ_self T, hselected, hprior⟩
        · have hprior_lt : pullCount action arm T < B :=
            Nat.lt_of_not_ge hprior
          rw [pullCount_succ_of_eq action arm T hselected] at hcount
          omega
      · rw [pullCount_succ_of_ne action arm T hselected] at hcount
        obtain ⟨t, ht, haction, hprior⟩ := ih hcount
        exact ⟨t, ht.trans (Nat.lt_succ_self T), haction, hprior⟩

/-- Log budget hidden inside one finite-arm/time peeling radius. -/
noncomputable def selectedPolicySuccessorFiniteArmTimeLogBudget
    (K T n : Nat) (delta : Real) : Real :=
  max
    (Real.log
      (1 / (((delta / ((K * T : Nat) : Real)) / (n : Real)) / 2)))
    0

/-- The local log budget is maximized at the full positive horizon. -/
theorem selectedPolicySuccessorFiniteArmTimeLogBudget_le_horizon
    (K T n : Nat) (delta : Real)
    (hK : 0 < K) (hT : 0 < T) (hnT : n <= T)
    (hdelta : 0 < delta) :
    selectedPolicySuccessorFiniteArmTimeLogBudget K T n delta <=
      selectedPolicySuccessorFiniteArmTimeLogBudget K T T delta := by
  cases n with
  | zero =>
      simp [selectedPolicySuccessorFiniteArmTimeLogBudget]
  | succ n =>
      have hn : 0 < n + 1 := Nat.succ_pos n
      have hlocal :
          1 / (((delta / ((K * T : Nat) : Real)) /
              ((n + 1 : Nat) : Real)) / 2) =
            2 * (((K * T : Nat) : Real)) * ((n + 1 : Nat) : Real) /
              delta := by
        have hKT : (((K * T : Nat) : Real)) ≠ 0 := by positivity
        have hn' : (((n + 1 : Nat) : Real)) ≠ 0 := by positivity
        have hd : delta ≠ 0 := ne_of_gt hdelta
        field_simp
      have hglobal :
          1 / (((delta / ((K * T : Nat) : Real)) / (T : Real)) / 2) =
            2 * (((K * T : Nat) : Real)) * (T : Real) / delta := by
        have hKT : (((K * T : Nat) : Real)) ≠ 0 := by positivity
        have hT' : (T : Real) ≠ 0 := by positivity
        have hd : delta ≠ 0 := ne_of_gt hdelta
        field_simp
      have harg_pos :
          0 < 2 * (((K * T : Nat) : Real)) * ((n + 1 : Nat) : Real) /
            delta := by
        positivity
      have harg_le :
          2 * (((K * T : Nat) : Real)) * ((n + 1 : Nat) : Real) /
              delta <=
            2 * (((K * T : Nat) : Real)) * (T : Real) / delta := by
        gcongr
      unfold selectedPolicySuccessorFiniteArmTimeLogBudget
      rw [hlocal, hglobal]
      exact max_le_max (Real.log_le_log harg_pos harg_le) le_rfl

/--
Real count threshold that simultaneously dominates the quadratic and linear
parts of the practical random-width radius inversion.
-/
noncomputable def selectedPolicySuccessorRealPullThreshold
    (K : Nat) (sigma2 : NNReal) (T : Nat) (delta gap : Real) : Real :=
  max
    (32 * (((sigma2 : NNReal) : Real)) *
      selectedPolicySuccessorFiniteArmTimeLogBudget K T T delta / gap ^ 2)
    (4 * selectedPolicySuccessorFiniteArmTimeLogBudget K T T delta / gap)

/-- One more than the ceiling supplies the strict margin needed by the radius. -/
noncomputable def selectedPolicySuccessorPullThreshold
    (K : Nat) (sigma2 : NNReal) (T : Nat) (delta gap : Real) : Nat :=
  Nat.ceil
      (selectedPolicySuccessorRealPullThreshold K sigma2 T delta gap) + 1

/--
The explicit integer threshold is positive and satisfies both full-horizon
strict radius-inversion inequalities.
-/
theorem selectedPolicySuccessorPullThreshold_contracts
    (K : Nat) (sigma2 : NNReal) (T : Nat) (delta gap : Real)
    (hgap : 0 < gap) :
    0 < selectedPolicySuccessorPullThreshold K sigma2 T delta gap /\
      32 * (((sigma2 : NNReal) : Real)) *
          selectedPolicySuccessorFiniteArmTimeLogBudget K T T delta <
        gap ^ 2 *
          (selectedPolicySuccessorPullThreshold K sigma2 T delta gap : Real) /\
      4 * selectedPolicySuccessorFiniteArmTimeLogBudget K T T delta <
        gap *
          (selectedPolicySuccessorPullThreshold K sigma2 T delta gap : Real) := by
  let budget := selectedPolicySuccessorFiniteArmTimeLogBudget K T T delta
  let variance := (((sigma2 : NNReal) : Real))
  let realThreshold :=
    max (32 * variance * budget / gap ^ 2) (4 * budget / gap)
  let threshold := Nat.ceil realThreshold + 1
  have hbudget : 0 <= budget := by
    exact le_max_right _ _
  have hvariance : 0 <= variance := by positivity
  have hquadratic_nonneg : 0 <= 32 * variance * budget / gap ^ 2 := by
    positivity
  have hrealThreshold_nonneg : 0 <= realThreshold := by
    exact hquadratic_nonneg.trans (le_max_left _ _)
  have hrealThreshold_le_ceil :
      realThreshold <= (Nat.ceil realThreshold : Real) :=
    Nat.le_ceil _
  have hrealThreshold_lt : realThreshold < (threshold : Real) := by
    dsimp only [threshold]
    rw [Nat.cast_add, Nat.cast_one]
    linarith
  have hquadratic_div :
      32 * variance * budget / gap ^ 2 < (threshold : Real) :=
    (le_max_left _ _).trans_lt hrealThreshold_lt
  have hlinear_div :
      4 * budget / gap < (threshold : Real) :=
    (le_max_right _ _).trans_lt hrealThreshold_lt
  have hquadratic :
      32 * variance * budget < gap ^ 2 * (threshold : Real) := by
    have hmul := (div_lt_iff₀ (sq_pos_of_pos hgap)).mp hquadratic_div
    nlinarith
  have hlinear : 4 * budget < gap * (threshold : Real) := by
    have hmul := (div_lt_iff₀ hgap).mp hlinear_div
    nlinarith
  simpa [selectedPolicySuccessorPullThreshold,
    selectedPolicySuccessorRealPullThreshold, threshold, realThreshold,
    variance, budget] using
      (show 0 < threshold /\
          32 * variance * budget < gap ^ 2 * (threshold : Real) /\
          4 * budget < gap * (threshold : Real) from
        ⟨Nat.succ_pos _, hquadratic, hlinear⟩)

/-- Expanded algebraic form of the practical finite-arm/time radius. -/
theorem successorArmEmpiricalMeanFiniteArmTimePeelingRadius_eq
    {K : Nat} (sigma2 : NNReal) (k n T : Nat) (delta : Real) :
    ConditionalExpectationReward.successorArmEmpiricalMeanFiniteArmTimePeelingRadius
        sigma2 k n (Finset.univ : Finset (Fin K)) T delta =
      (2 * Real.sqrt
          ((1 / 2 : Real) * (((sigma2 : NNReal) : Real) * (k : Real)) *
            selectedPolicySuccessorFiniteArmTimeLogBudget K T n delta) +
        selectedPolicySuccessorFiniteArmTimeLogBudget K T n delta) /
      (k : Real) := by
  simp [ConditionalExpectationReward.successorArmEmpiricalMeanFiniteArmTimePeelingRadius,
    ConditionalExpectationReward.successorArmEmpiricalMeanPeelingRadius,
    ConditionalExpectationReward.successorArmEmpiricalMeanExactCountRadius,
    ConditionalExpectationReward.successorArmEmpiricalMeanFiniteArmTimeConfidenceShare,
    Concentration.subGaussianPredictableVarianceRadius,
    Concentration.quadraticFixedMGFRadius,
    selectedPolicySuccessorFiniteArmTimeLogBudget]

/--
Sufficient square-root and linear inequalities for inverting one realized-count
peeling radius below half a positive arm gap.
-/
theorem two_mul_successorArmEmpiricalMeanFiniteArmTimePeelingRadius_lt_gap
    {K : Nat} (sigma2 : NNReal) (k n T : Nat) (delta gap : Real)
    (hk : 0 < k) (hgap : 0 < gap)
    (hquadratic :
      32 * (((sigma2 : NNReal) : Real)) *
          selectedPolicySuccessorFiniteArmTimeLogBudget K T n delta <
        gap ^ 2 * (k : Real))
    (hlinear :
      4 * selectedPolicySuccessorFiniteArmTimeLogBudget K T n delta <
        gap * (k : Real)) :
    2 * ConditionalExpectationReward.successorArmEmpiricalMeanFiniteArmTimePeelingRadius
          sigma2 k n (Finset.univ : Finset (Fin K)) T delta <
      gap := by
  let budget := selectedPolicySuccessorFiniteArmTimeLogBudget K T n delta
  let variance := (((sigma2 : NNReal) : Real))
  let count := (k : Real)
  let root := Real.sqrt ((1 / 2 : Real) * (variance * count) * budget)
  have hbudget : 0 <= budget := by
    exact le_max_right _ _
  have hvariance : 0 <= variance := by positivity
  have hcount : 0 < count := by
    dsimp only [count]
    exact_mod_cast hk
  have hroot : 0 <= root := Real.sqrt_nonneg _
  have hinside : 0 <= (1 / 2 : Real) * (variance * count) * budget := by
    positivity
  have hroot_sq : root ^ 2 =
      (1 / 2 : Real) * (variance * count) * budget := by
    exact Real.sq_sqrt hinside
  have hquadratic' :
      32 * variance * budget * count < gap ^ 2 * count ^ 2 := by
    have := mul_lt_mul_of_pos_right hquadratic hcount
    simpa [variance, count, budget, mul_assoc, pow_two] using this
  have hsquares : (8 * root) ^ 2 < (gap * count) ^ 2 := by
    rw [mul_pow, hroot_sq]
    nlinarith
  have hroot_term : 8 * root < gap * count := by
    exact (sq_lt_sq₀ (by positivity) (mul_nonneg hgap.le hcount.le)).mp
      hsquares
  have hnumerator : 2 * (2 * root + budget) < gap * count := by
    have hlinear' : 4 * budget < gap * count := by
      simpa [budget, count] using hlinear
    nlinarith
  rw [successorArmEmpiricalMeanFiniteArmTimePeelingRadius_eq]
  change 2 * ((2 * root + budget) / count) < gap
  calc
    2 * ((2 * root + budget) / count) =
        (2 * (2 * root + budget)) / count := by ring
    _ < gap := (div_lt_iff₀ hcount).2 hnumerator

/--
Uniform count-threshold inversion. It is enough to check the quadratic and
linear log-budget inequalities at the threshold `B`; larger realized counts
only improve the radius.
-/
theorem successorArmEmpiricalMeanFiniteArmTimePeelingRadius_lt_gap_of_threshold
    {K : Nat} (sigma2 : NNReal) (T : Nat) (delta gap : Real)
    (B : Nat) (hB : 0 < B) (hgap : 0 < gap)
    (hquadratic : forall n : Nat, n <= T ->
      32 * (((sigma2 : NNReal) : Real)) *
          selectedPolicySuccessorFiniteArmTimeLogBudget K T n delta <
        gap ^ 2 * (B : Real))
    (hlinear : forall n : Nat, n <= T ->
      4 * selectedPolicySuccessorFiniteArmTimeLogBudget K T n delta <
        gap * (B : Real)) :
    forall k n : Nat, B <= k -> n <= T ->
      2 * ConditionalExpectationReward.successorArmEmpiricalMeanFiniteArmTimePeelingRadius
            sigma2 k n (Finset.univ : Finset (Fin K)) T delta <
        gap := by
  intro k n hBk hn
  have hk : 0 < k := lt_of_lt_of_le hB hBk
  have hBkReal : (B : Real) <= (k : Real) := by exact_mod_cast hBk
  have hgapSq : 0 <= gap ^ 2 := sq_nonneg gap
  have hquadratic' :
      32 * (((sigma2 : NNReal) : Real)) *
          selectedPolicySuccessorFiniteArmTimeLogBudget K T n delta <
        gap ^ 2 * (k : Real) :=
    (hquadratic n hn).trans_le
      (mul_le_mul_of_nonneg_left hBkReal hgapSq)
  have hlinear' :
      4 * selectedPolicySuccessorFiniteArmTimeLogBudget K T n delta <
        gap * (k : Real) :=
    (hlinear n hn).trans_le
      (mul_le_mul_of_nonneg_left hBkReal hgap.le)
  exact
    two_mul_successorArmEmpiricalMeanFiniteArmTimePeelingRadius_lt_gap
      sigma2 k n T delta gap hk hgap hquadratic' hlinear'

/--
Full-horizon sufficient condition for uniform radius inversion. The finite
arm/time/count peeling log cost is summarized by the single deterministic
budget at `n = T`.
-/
theorem successorArmEmpiricalMeanFiniteArmTimePeelingRadius_lt_gap_of_global_threshold
    {K : Nat} (hK : 0 < K)
    (sigma2 : NNReal) (T : Nat) (hT : 0 < T)
    (delta : Real) (hdelta : 0 < delta)
    (gap : Real) (hgap : 0 < gap)
    (B : Nat) (hB : 0 < B)
    (hquadratic :
      32 * (((sigma2 : NNReal) : Real)) *
          selectedPolicySuccessorFiniteArmTimeLogBudget K T T delta <
        gap ^ 2 * (B : Real))
    (hlinear :
      4 * selectedPolicySuccessorFiniteArmTimeLogBudget K T T delta <
        gap * (B : Real)) :
    forall k n : Nat, B <= k -> n <= T ->
      2 * ConditionalExpectationReward.successorArmEmpiricalMeanFiniteArmTimePeelingRadius
            sigma2 k n (Finset.univ : Finset (Fin K)) T delta <
        gap := by
  apply successorArmEmpiricalMeanFiniteArmTimePeelingRadius_lt_gap_of_threshold
    sigma2 T delta gap B hB hgap
  · intro n hn
    have hbudget :=
      selectedPolicySuccessorFiniteArmTimeLogBudget_le_horizon
        K T n delta hK hT hn hdelta
    exact (mul_le_mul_of_nonneg_left hbudget (by positivity)).trans_lt
      hquadratic
  · intro n hn
    have hbudget :=
      selectedPolicySuccessorFiniteArmTimeLogBudget_le_horizon
        K T n delta hK hT hn hdelta
    exact (mul_le_mul_of_nonneg_left hbudget (by norm_num)).trans_lt
      hlinear

/--
Uniform radius inversion at the explicit one-more-than-ceiling pull threshold.
-/
theorem successorArmEmpiricalMeanFiniteArmTimePeelingRadius_lt_gap_of_explicitPullThreshold
    {K : Nat} (hK : 0 < K)
    (sigma2 : NNReal) (T : Nat) (hT : 0 < T)
    (delta : Real) (hdelta : 0 < delta)
    (gap : Real) (hgap : 0 < gap) :
    forall k n : Nat,
      selectedPolicySuccessorPullThreshold K sigma2 T delta gap <= k ->
      n <= T ->
        2 * ConditionalExpectationReward.successorArmEmpiricalMeanFiniteArmTimePeelingRadius
              sigma2 k n (Finset.univ : Finset (Fin K)) T delta <
          gap := by
  have hcontracts :=
    selectedPolicySuccessorPullThreshold_contracts
      K sigma2 T delta gap hgap
  exact
    successorArmEmpiricalMeanFiniteArmTimePeelingRadius_lt_gap_of_global_threshold
      hK sigma2 T hT delta hdelta gap hgap
      (selectedPolicySuccessorPullThreshold K sigma2 T delta gap)
      hcontracts.1 hcontracts.2.1 hcontracts.2.2

/--
A selected time with a positive prior count cannot lie inside the one-pass
round-robin initialization prefix.
-/
theorem K_le_of_selectedPolicySuccessorGeneratedUCBAction_selected_and_count_pos
    {Omega : Type} {K : Nat} (hK : 0 < K)
    (sigma2 : NNReal) (T : Nat) (delta : Real)
    (defaultAction : Fin K)
    (reward : Omega -> RewardTrace Rat) (omega : Omega)
    (arm : Fin K) (t : Nat)
    (hselected :
      selectedPolicySuccessorGeneratedUCBAction
        hK sigma2 T delta defaultAction reward omega (t + 1) = arm)
    (hcount :
      0 < ConditionalExpectationReward.successorArmPullCount
        (selectedPolicySuccessorGeneratedUCBAction
          hK sigma2 T delta defaultAction reward omega)
        arm (t + 1)) :
    K <= t := by
  by_contra hnot
  have ht : t < K := Nat.lt_of_not_ge hnot
  let action := selectedPolicySuccessorGeneratedUCBAction
    hK sigma2 T delta defaultAction reward omega
  have hselected' : (fun i => action (i + 1)) t = arm := by
    simpa [action] using hselected
  have hstep := pullCount_succ_of_eq
    (fun i => action (i + 1)) arm t hselected'
  have hmono := pullCount_mono
    (fun i => action (i + 1)) arm (Nat.succ_le_of_lt ht)
  have hinit :=
    successorArmPullCount_selectedPolicySuccessorGeneratedUCBAction_K_add_one_eq_one
      hK sigma2 T delta defaultAction reward omega arm
  have hinit' : pullCount (fun i => action (i + 1)) arm K = 1 := by
    simpa [action, ConditionalExpectationReward.successorArmPullCount] using hinit
  have hprior : 0 < pullCount (fun i => action (i + 1)) arm t := by
    simpa [action, ConditionalExpectationReward.successorArmPullCount] using
      hcount
  rw [hstep, hinit'] at hmono
  omega

/--
Generated-policy high-probability pull-count consumer.

The deterministic `hradius` contract is the exact remaining radius-inversion
obligation: every count at least `B`, at every horizon at most `T`, must make
twice the realized confidence radius strictly smaller than the chosen arm gap.
Under that contract, exceeding `B` pulls forces the global large-gap event.
-/
theorem measure_successorArmPullCount_selectedPolicySuccessorGeneratedUCBAction_gt_threshold_le_of_largeGap
    {Omega : Type} [MeasurableSpace Omega]
    {K : Nat} (hK : 0 < K)
    (mu : Measure Omega)
    (reward : Omega -> RewardTrace Rat)
    (armMean : Fin K -> Rat)
    (sigma2 : NNReal) (T : Nat) (delta : Real)
    (defaultAction best chosen : Fin K)
    (B : Nat) (hB : 0 < B)
    (hradius : forall k n : Nat,
      B <= k -> n <= T ->
        2 * ConditionalExpectationReward.successorArmEmpiricalMeanFiniteArmTimePeelingRadius
              sigma2 k n (Finset.univ : Finset (Fin K)) T delta <
          meanGap (fun arm => (armMean arm : Real)) best chosen)
    (hlargeGap :
      mu (selectedPolicySuccessorLargeGapEvent
        (selectedPolicySuccessorGeneratedUCBInitializedScoreMaxSource
          hK reward armMean sigma2 T delta defaultAction best)) <=
        ENNReal.ofReal delta) :
    mu {omega |
        B < ConditionalExpectationReward.successorArmPullCount
          (selectedPolicySuccessorGeneratedUCBAction
            hK sigma2 T delta defaultAction reward omega)
          chosen (T + 1)} <=
      ENNReal.ofReal delta := by
  let action := selectedPolicySuccessorGeneratedUCBAction
    hK sigma2 T delta defaultAction reward
  let source :=
    selectedPolicySuccessorGeneratedUCBInitializedScoreMaxSource
      hK reward armMean sigma2 T delta defaultAction best
  refine (measure_mono ?_).trans (by simpa [source] using hlargeGap)
  intro omega homega
  have hfinal : B < pullCount (fun i => action omega (i + 1)) chosen T := by
    simpa [action, ConditionalExpectationReward.successorArmPullCount] using
      homega
  obtain ⟨t, ht, hselected, hprior⟩ :=
    exists_selected_with_threshold_le_prior_pullCount
      (fun i => action omega (i + 1)) chosen T B hfinal
  have hprior_pos :
      0 < ConditionalExpectationReward.successorArmPullCount
        (action omega) chosen (t + 1) := by
    have : 0 < pullCount (fun i => action omega (i + 1)) chosen t :=
      lt_of_lt_of_le hB hprior
    simpa [ConditionalExpectationReward.successorArmPullCount] using this
  have hKle : K <= t :=
    K_le_of_selectedPolicySuccessorGeneratedUCBAction_selected_and_count_pos
      hK sigma2 T delta defaultAction reward omega chosen t
      (by simpa [action] using hselected) hprior_pos
  have ht_source : t ∈ source.times := by
    exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr ht, hKle⟩
  have hsource_chosen : source.chosen omega t = chosen := by
    simpa [source, action,
      selectedPolicySuccessorGeneratedUCBInitializedScoreMaxSource] using
      hselected
  refine Set.mem_setOf_eq.mpr ⟨t, ht_source, ?_⟩
  have hn : t + 1 <= T := Nat.succ_le_of_lt ht
  have hgap := hradius
    (ConditionalExpectationReward.successorArmPullCount
      (action omega) chosen (t + 1))
    (t + 1)
    (by simpa [ConditionalExpectationReward.successorArmPullCount] using hprior)
    hn
  rw [hsource_chosen]
  simpa [action, selectedPolicySuccessorRadiusAt] using hgap

/--
Generated-policy high-probability pull-count bound with the radius inversion
discharged by the two full-horizon numeric threshold inequalities.
-/
theorem measure_successorArmPullCount_selectedPolicySuccessorGeneratedUCBAction_gt_threshold_le_of_global_threshold
    {Omega : Type} [MeasurableSpace Omega]
    {K : Nat} (hK : 0 < K)
    (mu : Measure Omega)
    (reward : Omega -> RewardTrace Rat)
    (armMean : Fin K -> Rat)
    (sigma2 : NNReal) (T : Nat) (hT : 0 < T)
    (delta : Real) (hdelta : 0 < delta)
    (defaultAction best chosen : Fin K)
    (B : Nat) (hB : 0 < B)
    (hgap : 0 < meanGap (fun arm => (armMean arm : Real)) best chosen)
    (hquadratic :
      32 * (((sigma2 : NNReal) : Real)) *
          selectedPolicySuccessorFiniteArmTimeLogBudget K T T delta <
        meanGap (fun arm => (armMean arm : Real)) best chosen ^ 2 * (B : Real))
    (hlinear :
      4 * selectedPolicySuccessorFiniteArmTimeLogBudget K T T delta <
        meanGap (fun arm => (armMean arm : Real)) best chosen * (B : Real))
    (hlargeGap :
      mu (selectedPolicySuccessorLargeGapEvent
        (selectedPolicySuccessorGeneratedUCBInitializedScoreMaxSource
          hK reward armMean sigma2 T delta defaultAction best)) <=
        ENNReal.ofReal delta) :
    mu {omega |
        B < ConditionalExpectationReward.successorArmPullCount
          (selectedPolicySuccessorGeneratedUCBAction
            hK sigma2 T delta defaultAction reward omega)
          chosen (T + 1)} <=
      ENNReal.ofReal delta := by
  apply
    measure_successorArmPullCount_selectedPolicySuccessorGeneratedUCBAction_gt_threshold_le_of_largeGap
      hK mu reward armMean sigma2 T delta defaultAction best chosen B hB
  · exact
      successorArmEmpiricalMeanFiniteArmTimePeelingRadius_lt_gap_of_global_threshold
        hK sigma2 T hT delta hdelta
        (meanGap (fun arm => (armMean arm : Real)) best chosen)
        hgap B hB hquadratic hlinear
  · exact hlargeGap

/--
Generated-policy pull-count tail at the explicit one-more-than-ceiling
threshold; no caller-supplied radius or numeric threshold inequalities remain.
-/
theorem measure_successorArmPullCount_selectedPolicySuccessorGeneratedUCBAction_gt_explicitPullThreshold_le_of_largeGap
    {Omega : Type} [MeasurableSpace Omega]
    {K : Nat} (hK : 0 < K)
    (mu : Measure Omega)
    (reward : Omega -> RewardTrace Rat)
    (armMean : Fin K -> Rat)
    (sigma2 : NNReal) (T : Nat) (hT : 0 < T)
    (delta : Real) (hdelta : 0 < delta)
    (defaultAction best chosen : Fin K)
    (hgap : 0 < meanGap (fun arm => (armMean arm : Real)) best chosen)
    (hlargeGap :
      mu (selectedPolicySuccessorLargeGapEvent
        (selectedPolicySuccessorGeneratedUCBInitializedScoreMaxSource
          hK reward armMean sigma2 T delta defaultAction best)) <=
        ENNReal.ofReal delta) :
    mu {omega |
        selectedPolicySuccessorPullThreshold K sigma2 T delta
            (meanGap (fun arm => (armMean arm : Real)) best chosen) <
          ConditionalExpectationReward.successorArmPullCount
            (selectedPolicySuccessorGeneratedUCBAction
              hK sigma2 T delta defaultAction reward omega)
            chosen (T + 1)} <=
      ENNReal.ofReal delta := by
  have hcontracts :=
    selectedPolicySuccessorPullThreshold_contracts K sigma2 T delta
      (meanGap (fun arm => (armMean arm : Real)) best chosen) hgap
  exact
    measure_successorArmPullCount_selectedPolicySuccessorGeneratedUCBAction_gt_threshold_le_of_global_threshold
      hK mu reward armMean sigma2 T hT delta hdelta
      defaultAction best chosen
      (selectedPolicySuccessorPullThreshold K sigma2 T delta
        (meanGap (fun arm => (armMean arm : Real)) best chosen))
      hcontracts.1 hgap hcontracts.2.1 hcontracts.2.2 hlargeGap

/--
Practical selected-reward-law producer for the concrete generated UCB source's
global random-width large-gap event.
-/
theorem measure_selectedPolicySuccessorLargeGapEvent_generatedUCB_le_ennreal_delta_of_reward_map_eq_selected_policy
    {Omega Context : Type} {K : Nat}
    [mOmega : MeasurableSpace Omega] [StandardBorelSpace Omega]
    [MeasurableSpace Context]
    (hK : 0 < K)
    (mu : Measure Omega) [IsProbabilityMeasure mu]
    (rewardKernel : RewardKernel.MarkovRewardKernel (Context × Fin K) Rat)
    (context : (n : Nat) -> History.FiniteRewardHistory Rat n -> Context)
    (mean : Context -> Fin K -> Rat)
    (varianceProxy : Context -> Fin K -> NNReal)
    (defaultAction best : Fin K)
    (armMean : Fin K -> Rat)
    (reward : Omega -> RewardTrace Rat)
    (hreward : forall t : Nat,
      Measurable (fun omega : Omega => reward omega t))
    (rewardLo rewardHi meanLo meanHi : Nat -> Real)
    (sigma2 : NNReal)
    (hcontext : forall n : Nat, Measurable (context n))
    (hmean : Measurable (fun pair : Context × Fin K => mean pair.1 pair.2))
    (hkernel :
      RewardKernel.CenteredRewardKernelLaw rewardKernel mean varianceProxy)
    (hraw : forall i : Nat, forall omega : Omega,
      Set.Icc (rewardLo i) (rewardHi i)
        (((reward omega (i + 1) : Rat) : Real)))
    (hmean_range : forall i : Nat, forall c : Context, forall arm : Fin K,
      Set.Icc (meanLo i) (meanHi i) (((mean c arm : Rat) : Real)))
    (T : Nat) (hT : 0 < T)
    (hsigma2 : 0 < (((sigma2 : NNReal) : Real)))
    (delta : Real) (hdelta : 0 < delta)
    (hvariance : forall i : Nat,
      forall history : History.FiniteRewardHistory Rat i,
        varianceProxy (context i history)
            ((selectedPolicySuccessorHistoryPolicy
              hK sigma2 T delta defaultAction i).action
              (selectedPolicySuccessorHistoryState
                hK sigma2 T delta defaultAction i history)) <=
          sigma2)
    (harmMean : forall i : Nat,
      forall history : History.FiniteRewardHistory Rat i,
        forall arm : Fin K,
          mean (context i history) arm = armMean arm)
    (h_reward_map_eq_policy : forall i : Nat,
      Filter.Eventually
        (fun omega : Omega =>
          @Measure.map Omega Rat mOmega inferInstance
            (fun y : Omega => reward y (i + 1))
            (@ProbabilityTheory.condExpKernel Omega mOmega _ mu _
              ((History.historyFiltrationSucc
                (selectedPolicySuccessorGeneratedUCBAction
                  hK sigma2 T delta defaultAction reward)
                reward
                (ConditionalExpectationReward.generatedActionFromRewardHistory_measurable
                  (policy := selectedPolicySuccessorHistoryPolicy
                    hK sigma2 T delta defaultAction)
                  (state := selectedPolicySuccessorHistoryState
                    hK sigma2 T delta defaultAction)
                  (defaultAction := defaultAction) (reward := reward)
                  hreward
                  (measurable_selectedPolicySuccessorHistoryState
                    hK sigma2 T delta defaultAction))
                hreward) i)
              omega) =
          RewardKernel.selectedMeasure rewardKernel
            (context i
              (History.finiteRewardHistoryOfTrace (reward omega) i))
            ((selectedPolicySuccessorHistoryPolicy
              hK sigma2 T delta defaultAction i).action
              (selectedPolicySuccessorHistoryState
                hK sigma2 T delta defaultAction i
                (History.finiteRewardHistoryOfTrace (reward omega) i))))
        (ae
          (mu.trim
            ((History.historyFiltrationSucc
              (selectedPolicySuccessorGeneratedUCBAction
                hK sigma2 T delta defaultAction reward)
              reward
              (ConditionalExpectationReward.generatedActionFromRewardHistory_measurable
                (policy := selectedPolicySuccessorHistoryPolicy
                  hK sigma2 T delta defaultAction)
                (state := selectedPolicySuccessorHistoryState
                  hK sigma2 T delta defaultAction)
                (defaultAction := defaultAction) (reward := reward)
                hreward
                (measurable_selectedPolicySuccessorHistoryState
                  hK sigma2 T delta defaultAction))
              hreward).le i)))) :
    mu (selectedPolicySuccessorLargeGapEvent
        (selectedPolicySuccessorGeneratedUCBInitializedScoreMaxSource
          hK reward armMean sigma2 T delta defaultAction best)) <=
      ENNReal.ofReal delta := by
  let policy := selectedPolicySuccessorHistoryPolicy
    hK sigma2 T delta defaultAction
  let state := selectedPolicySuccessorHistoryState
    hK sigma2 T delta defaultAction
  let action := selectedPolicySuccessorGeneratedUCBAction
    hK sigma2 T delta defaultAction reward
  let source :=
    selectedPolicySuccessorGeneratedUCBInitializedScoreMaxSource
      hK reward armMean sigma2 T delta defaultAction best
  have htail :=
    measure_selectedPolicySuccessorLargeGapEvent_le_ennreal_delta_of_reward_map_eq_selected_policy_definitionalRawRangeMeasurableMeanRangeHistoryVarianceBounded
      (mu := mu)
      (rewardKernel := rewardKernel)
      (policy := policy)
      (context := context)
      (state := state)
      (mean := mean)
      (varianceProxy := varianceProxy)
      (defaultAction := defaultAction)
      (arms := (Finset.univ : Finset (Fin K)))
      (by exact ⟨defaultAction, Finset.mem_univ _⟩)
      (armMean := armMean)
      (reward := reward)
      (hreward := hreward)
      (rewardLo := rewardLo)
      (rewardHi := rewardHi)
      (meanLo := meanLo)
      (meanHi := meanHi)
      (sigma2 := sigma2)
      (hcontext := hcontext)
      (hstate := measurable_selectedPolicySuccessorHistoryState
        hK sigma2 T delta defaultAction)
      (hmean := hmean)
      (hkernel := hkernel)
      (hraw := hraw)
      (hmean_range := hmean_range)
      (hvariance := hvariance)
      (harmMean := by
        intro i history arm _harm
        exact harmMean i history arm)
      (h_reward_map_eq_policy := h_reward_map_eq_policy)
      T hT hsigma2 delta hdelta source
  simpa [source, action, policy, state,
    selectedPolicySuccessorGeneratedUCBAction] using htail

/--
Practical conditional-reward-law endpoint for the concrete generated UCB
policy. The only algorithmic numeric remainder is the explicit deterministic
radius-inversion contract `hradius`.
-/
theorem measure_successorArmPullCount_selectedPolicySuccessorGeneratedUCBAction_gt_threshold_le_ennreal_delta_of_reward_map_eq_selected_policy
    {Omega Context : Type} {K : Nat}
    [mOmega : MeasurableSpace Omega] [StandardBorelSpace Omega]
    [MeasurableSpace Context]
    (hK : 0 < K)
    (mu : Measure Omega) [IsProbabilityMeasure mu]
    (rewardKernel : RewardKernel.MarkovRewardKernel (Context × Fin K) Rat)
    (context : (n : Nat) -> History.FiniteRewardHistory Rat n -> Context)
    (mean : Context -> Fin K -> Rat)
    (varianceProxy : Context -> Fin K -> NNReal)
    (defaultAction best chosen : Fin K)
    (armMean : Fin K -> Rat)
    (reward : Omega -> RewardTrace Rat)
    (hreward : forall t : Nat,
      Measurable (fun omega : Omega => reward omega t))
    (rewardLo rewardHi meanLo meanHi : Nat -> Real)
    (sigma2 : NNReal)
    (hcontext : forall n : Nat, Measurable (context n))
    (hmean : Measurable (fun pair : Context × Fin K => mean pair.1 pair.2))
    (hkernel :
      RewardKernel.CenteredRewardKernelLaw rewardKernel mean varianceProxy)
    (hraw : forall i : Nat, forall omega : Omega,
      Set.Icc (rewardLo i) (rewardHi i)
        (((reward omega (i + 1) : Rat) : Real)))
    (hmean_range : forall i : Nat, forall c : Context, forall arm : Fin K,
      Set.Icc (meanLo i) (meanHi i) (((mean c arm : Rat) : Real)))
    (T : Nat) (hT : 0 < T)
    (hsigma2 : 0 < (((sigma2 : NNReal) : Real)))
    (delta : Real) (hdelta : 0 < delta)
    (hvariance : forall i : Nat,
      forall history : History.FiniteRewardHistory Rat i,
        varianceProxy (context i history)
            ((selectedPolicySuccessorHistoryPolicy
              hK sigma2 T delta defaultAction i).action
              (selectedPolicySuccessorHistoryState
                hK sigma2 T delta defaultAction i history)) <=
          sigma2)
    (harmMean : forall i : Nat,
      forall history : History.FiniteRewardHistory Rat i,
        forall arm : Fin K,
          mean (context i history) arm = armMean arm)
    (h_reward_map_eq_policy : forall i : Nat,
      Filter.Eventually
        (fun omega : Omega =>
          @Measure.map Omega Rat mOmega inferInstance
            (fun y : Omega => reward y (i + 1))
            (@ProbabilityTheory.condExpKernel Omega mOmega _ mu _
              ((History.historyFiltrationSucc
                (selectedPolicySuccessorGeneratedUCBAction
                  hK sigma2 T delta defaultAction reward)
                reward
                (ConditionalExpectationReward.generatedActionFromRewardHistory_measurable
                  (policy := selectedPolicySuccessorHistoryPolicy
                    hK sigma2 T delta defaultAction)
                  (state := selectedPolicySuccessorHistoryState
                    hK sigma2 T delta defaultAction)
                  (defaultAction := defaultAction) (reward := reward)
                  hreward
                  (measurable_selectedPolicySuccessorHistoryState
                    hK sigma2 T delta defaultAction))
                hreward) i)
              omega) =
          RewardKernel.selectedMeasure rewardKernel
            (context i
              (History.finiteRewardHistoryOfTrace (reward omega) i))
            ((selectedPolicySuccessorHistoryPolicy
              hK sigma2 T delta defaultAction i).action
              (selectedPolicySuccessorHistoryState
                hK sigma2 T delta defaultAction i
                (History.finiteRewardHistoryOfTrace (reward omega) i))))
        (ae
          (mu.trim
            ((History.historyFiltrationSucc
              (selectedPolicySuccessorGeneratedUCBAction
                hK sigma2 T delta defaultAction reward)
              reward
              (ConditionalExpectationReward.generatedActionFromRewardHistory_measurable
                (policy := selectedPolicySuccessorHistoryPolicy
                  hK sigma2 T delta defaultAction)
                (state := selectedPolicySuccessorHistoryState
                  hK sigma2 T delta defaultAction)
                (defaultAction := defaultAction) (reward := reward)
                hreward
                (measurable_selectedPolicySuccessorHistoryState
                  hK sigma2 T delta defaultAction))
              hreward).le i))))
    (B : Nat) (hB : 0 < B)
    (hradius : forall k n : Nat,
      B <= k -> n <= T ->
        2 * ConditionalExpectationReward.successorArmEmpiricalMeanFiniteArmTimePeelingRadius
              sigma2 k n (Finset.univ : Finset (Fin K)) T delta <
          meanGap (fun arm => (armMean arm : Real)) best chosen) :
    mu {omega |
        B < ConditionalExpectationReward.successorArmPullCount
          (selectedPolicySuccessorGeneratedUCBAction
            hK sigma2 T delta defaultAction reward omega)
          chosen (T + 1)} <=
      ENNReal.ofReal delta := by
  let policy := selectedPolicySuccessorHistoryPolicy
    hK sigma2 T delta defaultAction
  let state := selectedPolicySuccessorHistoryState
    hK sigma2 T delta defaultAction
  let action := selectedPolicySuccessorGeneratedUCBAction
    hK sigma2 T delta defaultAction reward
  let source :=
    selectedPolicySuccessorGeneratedUCBInitializedScoreMaxSource
      hK reward armMean sigma2 T delta defaultAction best
  have hlarge :
      mu (selectedPolicySuccessorLargeGapEvent source) <=
        ENNReal.ofReal delta := by
    have htail :=
      measure_selectedPolicySuccessorLargeGapEvent_le_ennreal_delta_of_reward_map_eq_selected_policy_definitionalRawRangeMeasurableMeanRangeHistoryVarianceBounded
        (mu := mu)
        (rewardKernel := rewardKernel)
        (policy := policy)
        (context := context)
        (state := state)
        (mean := mean)
        (varianceProxy := varianceProxy)
        (defaultAction := defaultAction)
        (arms := (Finset.univ : Finset (Fin K)))
        (by exact ⟨defaultAction, Finset.mem_univ _⟩)
        (armMean := armMean)
        (reward := reward)
        (hreward := hreward)
        (rewardLo := rewardLo)
        (rewardHi := rewardHi)
        (meanLo := meanLo)
        (meanHi := meanHi)
        (sigma2 := sigma2)
        (hcontext := hcontext)
        (hstate := measurable_selectedPolicySuccessorHistoryState
          hK sigma2 T delta defaultAction)
        (hmean := hmean)
        (hkernel := hkernel)
        (hraw := hraw)
        (hmean_range := hmean_range)
        (hvariance := hvariance)
        (harmMean := by
          intro i history arm _harm
          exact harmMean i history arm)
        (h_reward_map_eq_policy := h_reward_map_eq_policy)
        T hT hsigma2 delta hdelta source
    simpa [source, action, policy, state,
      selectedPolicySuccessorGeneratedUCBAction] using htail
  exact
    measure_successorArmPullCount_selectedPolicySuccessorGeneratedUCBAction_gt_threshold_le_of_largeGap
      hK mu reward armMean sigma2 T delta defaultAction best chosen B hB
      hradius (by simpa [source] using hlarge)

/-- Timewise measurability of the concrete generated UCB action trace. -/
theorem measurable_selectedPolicySuccessorGeneratedUCBAction
    {Omega : Type} [MeasurableSpace Omega]
    {K : Nat} (hK : 0 < K)
    (sigma2 : NNReal) (T : Nat) (delta : Real)
    (defaultAction : Fin K)
    (reward : Omega -> RewardTrace Rat)
    (hreward : forall t : Nat,
      Measurable (fun omega : Omega => reward omega t))
    (t : Nat) :
    Measurable (fun omega =>
      selectedPolicySuccessorGeneratedUCBAction
        hK sigma2 T delta defaultAction reward omega t) := by
  exact
    ConditionalExpectationReward.generatedActionFromRewardHistory_measurable
      (policy := selectedPolicySuccessorHistoryPolicy
        hK sigma2 T delta defaultAction)
      (state := selectedPolicySuccessorHistoryState
        hK sigma2 T delta defaultAction)
      (defaultAction := defaultAction) (reward := reward)
      hreward
      (measurable_selectedPolicySuccessorHistoryState
        hK sigma2 T delta defaultAction)
      t

/--
Integrate a bounded Nat-valued random variable from one upper-tail probability
bound. This is the exact `B + horizon * delta` layer used by the generated UCB
pull-count theorem below.
-/
theorem lintegral_natCast_le_threshold_add_bound_mul_of_measure_gt
    {Omega : Type} [MeasurableSpace Omega]
    (mu : Measure Omega) [IsProbabilityMeasure mu]
    (count : Omega -> Nat) (hcount : Measurable count)
    (threshold bound : Nat)
    (hbound : forall omega, count omega <= bound)
    (epsilon : ENNReal)
    (htail : mu {omega | threshold < count omega} <= epsilon) :
    ∫⁻ omega, (count omega : ENNReal) ∂mu <=
      (threshold : ENNReal) + (bound : ENNReal) * epsilon := by
  let bad : Set Omega := {omega | threshold < count omega}
  have hbad : MeasurableSet bad := by
    simpa [bad] using measurableSet_lt measurable_const hcount
  let overflow : Omega -> ENNReal :=
    fun omega => bad.indicator (fun _ => (bound : ENNReal)) omega
  have hpoint : forall omega,
      (count omega : ENNReal) <= (threshold : ENNReal) + overflow omega := by
    intro omega
    by_cases homega : omega ∈ bad
    · have hc : (count omega : ENNReal) <= (bound : ENNReal) := by
        exact_mod_cast hbound omega
      calc
        (count omega : ENNReal) <= (bound : ENNReal) := hc
        _ <= (threshold : ENNReal) + (bound : ENNReal) := by
          exact le_add_left (le_refl (bound : ENNReal))
        _ = (threshold : ENNReal) + overflow omega := by
          simp [overflow, Set.indicator_of_mem homega]
    · have hc : count omega <= threshold := by
        exact Nat.le_of_not_gt (by simpa [bad] using homega)
      calc
        (count omega : ENNReal) <= (threshold : ENNReal) := by
          exact_mod_cast hc
        _ = (threshold : ENNReal) + overflow omega := by
          simp [overflow, Set.indicator_of_notMem homega]
  calc
    ∫⁻ omega, (count omega : ENNReal) ∂mu <=
        ∫⁻ omega, ((threshold : ENNReal) + overflow omega) ∂mu :=
      lintegral_mono hpoint
    _ = ∫⁻ _omega : Omega, (threshold : ENNReal) ∂mu +
        ∫⁻ omega, overflow omega ∂mu := by
      rw [lintegral_add_left measurable_const]
    _ = (threshold : ENNReal) + (bound : ENNReal) * mu bad := by
      rw [lintegral_const,
        lintegral_indicator_const hbad (bound : ENNReal)]
      simp [overflow, IsProbabilityMeasure.measure_univ]
    _ <= (threshold : ENNReal) + (bound : ENNReal) * epsilon := by
      exact add_le_add le_rfl
        (mul_le_mul_left' (by simpa [bad] using htail) _)

/--
ENNReal expected pull-count bound for the concrete generated UCB process from
the global large-gap probability theorem and the deterministic radius
inversion contract.
-/
theorem lintegral_successorArmPullCount_selectedPolicySuccessorGeneratedUCBAction_le_threshold_add_horizon_mul_delta_of_largeGap
    {Omega : Type} [MeasurableSpace Omega]
    {K : Nat} (hK : 0 < K)
    (mu : Measure Omega) [IsProbabilityMeasure mu]
    (reward : Omega -> RewardTrace Rat)
    (hreward : forall t : Nat,
      Measurable (fun omega : Omega => reward omega t))
    (armMean : Fin K -> Rat)
    (sigma2 : NNReal) (T : Nat) (delta : Real)
    (defaultAction best chosen : Fin K)
    (B : Nat) (hB : 0 < B)
    (hradius : forall k n : Nat,
      B <= k -> n <= T ->
        2 * ConditionalExpectationReward.successorArmEmpiricalMeanFiniteArmTimePeelingRadius
              sigma2 k n (Finset.univ : Finset (Fin K)) T delta <
          meanGap (fun arm => (armMean arm : Real)) best chosen)
    (hlargeGap :
      mu (selectedPolicySuccessorLargeGapEvent
        (selectedPolicySuccessorGeneratedUCBInitializedScoreMaxSource
          hK reward armMean sigma2 T delta defaultAction best)) <=
        ENNReal.ofReal delta) :
    ∫⁻ omega,
        (ConditionalExpectationReward.successorArmPullCount
          (selectedPolicySuccessorGeneratedUCBAction
            hK sigma2 T delta defaultAction reward omega)
          chosen (T + 1) : ENNReal) ∂mu <=
      (B : ENNReal) + (T : ENNReal) * ENNReal.ofReal delta := by
  let action := selectedPolicySuccessorGeneratedUCBAction
    hK sigma2 T delta defaultAction reward
  let count : Omega -> Nat := fun omega =>
    ConditionalExpectationReward.successorArmPullCount
      (action omega) chosen (T + 1)
  have haction : forall t : Nat,
      Measurable (fun omega => action omega t) := by
    intro t
    exact measurable_selectedPolicySuccessorGeneratedUCBAction
      hK sigma2 T delta defaultAction reward hreward t
  have hcount_meas : Measurable count := by
    unfold count ConditionalExpectationReward.successorArmPullCount
    exact measurable_pullCount
      (fun omega i => action omega (i + 1))
      (fun i => haction (i + 1)) chosen (T + 1 - 1)
  have hcount_le : forall omega, count omega <= T := by
    intro omega
    unfold count ConditionalExpectationReward.successorArmPullCount
    simp only [Nat.add_sub_cancel]
    exact pullCount_le_time (fun i => action omega (i + 1)) chosen T
  have htail : mu {omega | B < count omega} <= ENNReal.ofReal delta := by
    simpa [count, action] using
      measure_successorArmPullCount_selectedPolicySuccessorGeneratedUCBAction_gt_threshold_le_of_largeGap
        hK mu reward armMean sigma2 T delta defaultAction best chosen B hB
        hradius hlargeGap
  simpa [count, action] using
    lintegral_natCast_le_threshold_add_bound_mul_of_measure_gt
      mu count hcount_meas B T hcount_le (ENNReal.ofReal delta) htail

/--
ENNReal expected pull-count bound whose algorithmic remainder is stated only
through the two full-horizon numeric threshold inequalities.
-/
theorem lintegral_successorArmPullCount_selectedPolicySuccessorGeneratedUCBAction_le_threshold_add_horizon_mul_delta_of_global_threshold
    {Omega : Type} [MeasurableSpace Omega]
    {K : Nat} (hK : 0 < K)
    (mu : Measure Omega) [IsProbabilityMeasure mu]
    (reward : Omega -> RewardTrace Rat)
    (hreward : forall t : Nat,
      Measurable (fun omega : Omega => reward omega t))
    (armMean : Fin K -> Rat)
    (sigma2 : NNReal) (T : Nat) (hT : 0 < T)
    (delta : Real) (hdelta : 0 < delta)
    (defaultAction best chosen : Fin K)
    (B : Nat) (hB : 0 < B)
    (hgap : 0 < meanGap (fun arm => (armMean arm : Real)) best chosen)
    (hquadratic :
      32 * (((sigma2 : NNReal) : Real)) *
          selectedPolicySuccessorFiniteArmTimeLogBudget K T T delta <
        meanGap (fun arm => (armMean arm : Real)) best chosen ^ 2 * (B : Real))
    (hlinear :
      4 * selectedPolicySuccessorFiniteArmTimeLogBudget K T T delta <
        meanGap (fun arm => (armMean arm : Real)) best chosen * (B : Real))
    (hlargeGap :
      mu (selectedPolicySuccessorLargeGapEvent
        (selectedPolicySuccessorGeneratedUCBInitializedScoreMaxSource
          hK reward armMean sigma2 T delta defaultAction best)) <=
        ENNReal.ofReal delta) :
    ∫⁻ omega,
        (ConditionalExpectationReward.successorArmPullCount
          (selectedPolicySuccessorGeneratedUCBAction
            hK sigma2 T delta defaultAction reward omega)
          chosen (T + 1) : ENNReal) ∂mu <=
      (B : ENNReal) + (T : ENNReal) * ENNReal.ofReal delta := by
  apply
    lintegral_successorArmPullCount_selectedPolicySuccessorGeneratedUCBAction_le_threshold_add_horizon_mul_delta_of_largeGap
      hK mu reward hreward armMean sigma2 T delta defaultAction best chosen B hB
  · exact
      successorArmEmpiricalMeanFiniteArmTimePeelingRadius_lt_gap_of_global_threshold
        hK sigma2 T hT delta hdelta
        (meanGap (fun arm => (armMean arm : Real)) best chosen)
        hgap B hB hquadratic hlinear
  · exact hlargeGap

/--
ENNReal expected pull-count bound at the explicit one-more-than-ceiling
threshold; the numeric radius inversion is fully discharged internally.
-/
theorem lintegral_successorArmPullCount_selectedPolicySuccessorGeneratedUCBAction_le_explicitPullThreshold_add_horizon_mul_delta_of_largeGap
    {Omega : Type} [MeasurableSpace Omega]
    {K : Nat} (hK : 0 < K)
    (mu : Measure Omega) [IsProbabilityMeasure mu]
    (reward : Omega -> RewardTrace Rat)
    (hreward : forall t : Nat,
      Measurable (fun omega : Omega => reward omega t))
    (armMean : Fin K -> Rat)
    (sigma2 : NNReal) (T : Nat) (hT : 0 < T)
    (delta : Real) (hdelta : 0 < delta)
    (defaultAction best chosen : Fin K)
    (hgap : 0 < meanGap (fun arm => (armMean arm : Real)) best chosen)
    (hlargeGap :
      mu (selectedPolicySuccessorLargeGapEvent
        (selectedPolicySuccessorGeneratedUCBInitializedScoreMaxSource
          hK reward armMean sigma2 T delta defaultAction best)) <=
        ENNReal.ofReal delta) :
    ∫⁻ omega,
        (ConditionalExpectationReward.successorArmPullCount
          (selectedPolicySuccessorGeneratedUCBAction
            hK sigma2 T delta defaultAction reward omega)
          chosen (T + 1) : ENNReal) ∂mu <=
      (selectedPolicySuccessorPullThreshold K sigma2 T delta
          (meanGap (fun arm => (armMean arm : Real)) best chosen) : ENNReal) +
        (T : ENNReal) * ENNReal.ofReal delta := by
  have hcontracts :=
    selectedPolicySuccessorPullThreshold_contracts K sigma2 T delta
      (meanGap (fun arm => (armMean arm : Real)) best chosen) hgap
  exact
    lintegral_successorArmPullCount_selectedPolicySuccessorGeneratedUCBAction_le_threshold_add_horizon_mul_delta_of_global_threshold
      hK mu reward hreward armMean sigma2 T hT delta hdelta
      defaultAction best chosen
      (selectedPolicySuccessorPullThreshold K sigma2 T delta
        (meanGap (fun arm => (armMean arm : Real)) best chosen))
      hcontracts.1 hgap hcontracts.2.1 hcontracts.2.2 hlargeGap

/--
End-to-end practical selected-reward-law expected pull-count theorem for the
concrete generated UCB policy at its explicit integer threshold.
-/
theorem lintegral_successorArmPullCount_selectedPolicySuccessorGeneratedUCBAction_le_explicitPullThreshold_add_horizon_mul_delta_of_reward_map_eq_selected_policy
    {Omega Context : Type} {K : Nat}
    [mOmega : MeasurableSpace Omega] [StandardBorelSpace Omega]
    [MeasurableSpace Context]
    (hK : 0 < K)
    (mu : Measure Omega) [IsProbabilityMeasure mu]
    (rewardKernel : RewardKernel.MarkovRewardKernel (Context × Fin K) Rat)
    (context : (n : Nat) -> History.FiniteRewardHistory Rat n -> Context)
    (mean : Context -> Fin K -> Rat)
    (varianceProxy : Context -> Fin K -> NNReal)
    (defaultAction best chosen : Fin K)
    (armMean : Fin K -> Rat)
    (reward : Omega -> RewardTrace Rat)
    (hreward : forall t : Nat,
      Measurable (fun omega : Omega => reward omega t))
    (rewardLo rewardHi meanLo meanHi : Nat -> Real)
    (sigma2 : NNReal)
    (hcontext : forall n : Nat, Measurable (context n))
    (hmean : Measurable (fun pair : Context × Fin K => mean pair.1 pair.2))
    (hkernel :
      RewardKernel.CenteredRewardKernelLaw rewardKernel mean varianceProxy)
    (hraw : forall i : Nat, forall omega : Omega,
      Set.Icc (rewardLo i) (rewardHi i)
        (((reward omega (i + 1) : Rat) : Real)))
    (hmean_range : forall i : Nat, forall c : Context, forall arm : Fin K,
      Set.Icc (meanLo i) (meanHi i) (((mean c arm : Rat) : Real)))
    (T : Nat) (hT : 0 < T)
    (hsigma2 : 0 < (((sigma2 : NNReal) : Real)))
    (delta : Real) (hdelta : 0 < delta)
    (hvariance : forall i : Nat,
      forall history : History.FiniteRewardHistory Rat i,
        varianceProxy (context i history)
            ((selectedPolicySuccessorHistoryPolicy
              hK sigma2 T delta defaultAction i).action
              (selectedPolicySuccessorHistoryState
                hK sigma2 T delta defaultAction i history)) <=
          sigma2)
    (harmMean : forall i : Nat,
      forall history : History.FiniteRewardHistory Rat i,
        forall arm : Fin K,
          mean (context i history) arm = armMean arm)
    (h_reward_map_eq_policy : forall i : Nat,
      Filter.Eventually
        (fun omega : Omega =>
          @Measure.map Omega Rat mOmega inferInstance
            (fun y : Omega => reward y (i + 1))
            (@ProbabilityTheory.condExpKernel Omega mOmega _ mu _
              ((History.historyFiltrationSucc
                (selectedPolicySuccessorGeneratedUCBAction
                  hK sigma2 T delta defaultAction reward)
                reward
                (ConditionalExpectationReward.generatedActionFromRewardHistory_measurable
                  (policy := selectedPolicySuccessorHistoryPolicy
                    hK sigma2 T delta defaultAction)
                  (state := selectedPolicySuccessorHistoryState
                    hK sigma2 T delta defaultAction)
                  (defaultAction := defaultAction) (reward := reward)
                  hreward
                  (measurable_selectedPolicySuccessorHistoryState
                    hK sigma2 T delta defaultAction))
                hreward) i)
              omega) =
          RewardKernel.selectedMeasure rewardKernel
            (context i
              (History.finiteRewardHistoryOfTrace (reward omega) i))
            ((selectedPolicySuccessorHistoryPolicy
              hK sigma2 T delta defaultAction i).action
              (selectedPolicySuccessorHistoryState
                hK sigma2 T delta defaultAction i
                (History.finiteRewardHistoryOfTrace (reward omega) i))))
        (ae
          (mu.trim
            ((History.historyFiltrationSucc
              (selectedPolicySuccessorGeneratedUCBAction
                hK sigma2 T delta defaultAction reward)
              reward
              (ConditionalExpectationReward.generatedActionFromRewardHistory_measurable
                (policy := selectedPolicySuccessorHistoryPolicy
                  hK sigma2 T delta defaultAction)
                (state := selectedPolicySuccessorHistoryState
                  hK sigma2 T delta defaultAction)
                (defaultAction := defaultAction) (reward := reward)
                hreward
                (measurable_selectedPolicySuccessorHistoryState
                  hK sigma2 T delta defaultAction))
              hreward).le i))))
    (hgap : 0 < meanGap (fun arm => (armMean arm : Real)) best chosen) :
    ∫⁻ omega,
        (ConditionalExpectationReward.successorArmPullCount
          (selectedPolicySuccessorGeneratedUCBAction
            hK sigma2 T delta defaultAction reward omega)
          chosen (T + 1) : ENNReal) ∂mu <=
      (selectedPolicySuccessorPullThreshold K sigma2 T delta
          (meanGap (fun arm => (armMean arm : Real)) best chosen) : ENNReal) +
        (T : ENNReal) * ENNReal.ofReal delta := by
  have hlargeGap :=
    measure_selectedPolicySuccessorLargeGapEvent_generatedUCB_le_ennreal_delta_of_reward_map_eq_selected_policy
      (hK := hK)
      (mu := mu)
      (rewardKernel := rewardKernel)
      (context := context)
      (mean := mean)
      (varianceProxy := varianceProxy)
      (defaultAction := defaultAction)
      (best := best)
      (armMean := armMean)
      (reward := reward)
      (hreward := hreward)
      (rewardLo := rewardLo)
      (rewardHi := rewardHi)
      (meanLo := meanLo)
      (meanHi := meanHi)
      (sigma2 := sigma2)
      (hcontext := hcontext)
      (hmean := hmean)
      (hkernel := hkernel)
      (hraw := hraw)
      (hmean_range := hmean_range)
      (T := T)
      (hT := hT)
      (hsigma2 := hsigma2)
      (delta := delta)
      (hdelta := hdelta)
      (hvariance := hvariance)
      (harmMean := harmMean)
      (h_reward_map_eq_policy := h_reward_map_eq_policy)
  exact
    lintegral_successorArmPullCount_selectedPolicySuccessorGeneratedUCBAction_le_explicitPullThreshold_add_horizon_mul_delta_of_largeGap
      hK mu reward hreward armMean sigma2 T hT delta hdelta
      defaultAction best chosen hgap hlargeGap

end UCB
end BanditRLProof
