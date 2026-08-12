import BanditRLProof.Algorithms.UCBConditionalRewardPairTrajectory
import BanditRLProof.Algorithms.UCBConditionalRewardLawRegret
import BanditRLProof.ConditionalRewardPartialTrajectoryTelescopingAllTime

/-!
# Horizon-free telescoping-scheduled UCB

This module defines one finite-arm UCB policy.  Its score at history index `t`
uses the summable confidence share
`telescopingConfidenceShare delta t / K`; no terminal horizon occurs in the
policy, state, score, or generated-action declarations.  Finite horizons occur
only in downstream count and regret consumers.
-/

namespace BanditRLProof
namespace UCB

open MeasureTheory

/-- Realized-count radius with the time-`t` telescoping share divided over the
finite arm set. -/
noncomputable def selectedPolicySuccessorTelescopingRadiusAt
    {Omega : Type} {K : Nat}
    (action : Omega -> ActionTrace (Fin K)) (sigma2 : NNReal) (delta : Real)
    (omega : Omega) (t : Nat) (arm : Fin K) : Real :=
  ConditionalExpectationReward.successorArmEmpiricalMeanPeelingRadius
    sigma2
    (ConditionalExpectationReward.successorArmPullCount
      (action omega) arm (t + 1))
    (t + 1)
    (Concentration.telescopingConfidenceShare delta t / (K : Real))

/-- The scheduled radius is nonnegative, including its explicit zero-count
convention inherited from division in `Real`. -/
theorem selectedPolicySuccessorTelescopingRadiusAt_nonneg
    {Omega : Type} {K : Nat}
    (action : Omega -> ActionTrace (Fin K)) (sigma2 : NNReal) (delta : Real)
    (omega : Omega) (t : Nat) (arm : Fin K) :
    0 <= selectedPolicySuccessorTelescopingRadiusAt
      action sigma2 delta omega t arm := by
  unfold selectedPolicySuccessorTelescopingRadiusAt
    ConditionalExpectationReward.successorArmEmpiricalMeanPeelingRadius
    ConditionalExpectationReward.successorArmEmpiricalMeanExactCountRadius
    Concentration.subGaussianPredictableVarianceRadius
    Concentration.quadraticFixedMGFRadius
  positivity

/-- The horizon-free scheduled UCB index on an action/reward trace. -/
noncomputable def selectedPolicySuccessorTelescopingIndexAt
    {Omega : Type} {K : Nat}
    (action : Omega -> ActionTrace (Fin K))
    (reward : Omega -> RewardTrace Rat)
    (sigma2 : NNReal) (delta : Real)
    (omega : Omega) (t : Nat) (arm : Fin K) : Real :=
  confidenceScore
    (fun candidate =>
      selectedPolicySuccessorEmpiricalMeanAt action reward omega t candidate)
    (fun candidate =>
      selectedPolicySuccessorTelescopingRadiusAt
        action sigma2 delta omega t candidate)
    arm

/-- Scheduled score reconstructed from one finite generated pair history. -/
noncomputable def selectedPolicySuccessorTelescopingHistoryIndex
    {K : Nat} (sigma2 : NNReal) (delta : Real)
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
      ConditionalExpectationReward.successorArmEmpiricalMeanPeelingRadius
        sigma2
        (ConditionalExpectationReward.successorArmPullCount
          action candidate (t + 1))
        (t + 1)
        (Concentration.telescopingConfidenceShare delta t / (K : Real)))
    arm

/-- Every fixed-arm scheduled history score is measurable. -/
theorem measurable_selectedPolicySuccessorTelescopingHistoryIndex
    {K : Nat} (sigma2 : NNReal) (delta : Real)
    (defaultAction : Fin K) (t : Nat) (arm : Fin K) :
    Measurable (fun history : History.FinitePairHistory (Fin K) Rat t =>
      selectedPolicySuccessorTelescopingHistoryIndex
        sigma2 delta defaultAction t history arm) := by
  exact measurable_of_countable _

/-- Round-robin initialization followed by the scheduled score argmax. -/
noncomputable def selectedPolicySuccessorTelescopingHistoryNextArm
    {K : Nat} (hK : 0 < K) (sigma2 : NNReal) (delta : Real)
    (defaultAction : Fin K) (t : Nat)
    (history : History.FinitePairHistory (Fin K) Rat t) : Fin K :=
  if t < K then
    initializationArm hK t
  else
    scoreArgmax hK
      (selectedPolicySuccessorTelescopingHistoryIndex
        sigma2 delta defaultAction t history)

/-- After initialization, the scheduled selector maximizes every arm score. -/
theorem selectedPolicySuccessorTelescopingHistoryIndex_le_nextArm_of_K_le
    {K : Nat} (hK : 0 < K) (sigma2 : NNReal) (delta : Real)
    (defaultAction : Fin K) (t : Nat)
    (history : History.FinitePairHistory (Fin K) Rat t)
    (ht : K <= t) (arm : Fin K) :
    selectedPolicySuccessorTelescopingHistoryIndex
        sigma2 delta defaultAction t history arm <=
      selectedPolicySuccessorTelescopingHistoryIndex
        sigma2 delta defaultAction t history
        (selectedPolicySuccessorTelescopingHistoryNextArm
          hK sigma2 delta defaultAction t history) := by
  rw [selectedPolicySuccessorTelescopingHistoryNextArm,
    if_neg (not_lt_of_ge ht)]
  exact scoreArgmax_spec hK
    (selectedPolicySuccessorTelescopingHistoryIndex
      sigma2 delta defaultAction t history) arm

/-- Pair-history reconstruction for the single scheduled policy. -/
noncomputable def selectedPolicySuccessorTelescopingPairHistory
    {K : Nat} (hK : 0 < K) (sigma2 : NNReal) (delta : Real)
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
        selectedPolicySuccessorTelescopingPairHistory
          hK sigma2 delta defaultAction n previousRewardHistory
      let nextAction :=
        selectedPolicySuccessorTelescopingHistoryNextArm
          hK sigma2 delta defaultAction n previousHistory
      History.extendPairHistorySucc previousHistory
        (nextAction,
          rewardHistory ⟨n + 1, Finset.mem_Iic.mpr le_rfl⟩)

/-- Fixed state package reconstructed by the scheduled policy. -/
noncomputable def selectedPolicySuccessorTelescopingHistoryState
    {K : Nat} (hK : 0 < K) (sigma2 : NNReal) (delta : Real)
    (defaultAction : Fin K)
    (n : Nat) (rewardHistory : History.FiniteRewardHistory Rat n) :
    SelectedPolicySuccessorFiniteHistoryState K :=
  ⟨n,
    selectedPolicySuccessorTelescopingPairHistory
      hK sigma2 delta defaultAction n rewardHistory⟩

/-- Scheduled state reconstruction is measurable at every history index. -/
theorem measurable_selectedPolicySuccessorTelescopingHistoryState
    {K : Nat} (hK : 0 < K) (sigma2 : NNReal) (delta : Real)
    (defaultAction : Fin K) (n : Nat) :
    Measurable
      (selectedPolicySuccessorTelescopingHistoryState
        hK sigma2 delta defaultAction n) := by
  exact measurable_of_countable _

/-- One measurable UCB policy.  Its declaration has no terminal horizon. -/
noncomputable def selectedPolicySuccessorTelescopingHistoryPolicy
    {K : Nat} (hK : 0 < K) (sigma2 : NNReal) (delta : Real)
    (defaultAction : Fin K) (_t : Nat) :
    Policy.MeasurablePolicy
      (SelectedPolicySuccessorFiniteHistoryState K) (Fin K) where
  action := fun state =>
    selectedPolicySuccessorTelescopingHistoryNextArm
      hK sigma2 delta defaultAction state.time state.history
  measurable_action := by
    exact Measurable.of_comap_le le_top

/-- Generated action trace for the single scheduled UCB policy. -/
noncomputable def selectedPolicySuccessorTelescopingGeneratedUCBAction
    {Omega : Type} {K : Nat} (hK : 0 < K)
    (sigma2 : NNReal) (delta : Real) (defaultAction : Fin K)
    (reward : Omega -> RewardTrace Rat) : Omega -> ActionTrace (Fin K) :=
  ConditionalExpectationReward.generatedActionFromRewardHistory
    (selectedPolicySuccessorTelescopingHistoryPolicy
      hK sigma2 delta defaultAction)
    (selectedPolicySuccessorTelescopingHistoryState
      hK sigma2 delta defaultAction)
    defaultAction reward

@[simp]
theorem selectedPolicySuccessorTelescopingGeneratedUCBAction_succ
    {Omega : Type} {K : Nat} (hK : 0 < K)
    (sigma2 : NNReal) (delta : Real) (defaultAction : Fin K)
    (reward : Omega -> RewardTrace Rat) (omega : Omega) (t : Nat) :
    selectedPolicySuccessorTelescopingGeneratedUCBAction
        hK sigma2 delta defaultAction reward omega (t + 1) =
      selectedPolicySuccessorTelescopingHistoryNextArm
        hK sigma2 delta defaultAction t
        (selectedPolicySuccessorTelescopingPairHistory
          hK sigma2 delta defaultAction t
          (History.finiteRewardHistoryOfTrace (reward omega) t)) := by
  simp [selectedPolicySuccessorTelescopingGeneratedUCBAction,
    ConditionalExpectationReward.generatedActionFromRewardHistory,
    Policy.generatedActionTraceSucc,
    selectedPolicySuccessorTelescopingHistoryPolicy,
    selectedPolicySuccessorTelescopingHistoryState]

/-- The reconstructed scheduled pair state is the generated trace prefix. -/
theorem selectedPolicySuccessorTelescopingPairHistory_eq_finitePairHistoryOfTrace
    {Omega : Type} {K : Nat} (hK : 0 < K)
    (sigma2 : NNReal) (delta : Real) (defaultAction : Fin K)
    (reward : Omega -> RewardTrace Rat) (omega : Omega) (n : Nat) :
    selectedPolicySuccessorTelescopingPairHistory
        hK sigma2 delta defaultAction n
        (History.finiteRewardHistoryOfTrace (reward omega) n) =
      History.finitePairHistoryOfTrace
        (selectedPolicySuccessorTelescopingGeneratedUCBAction
          hK sigma2 delta defaultAction reward omega)
        (reward omega) n := by
  induction n with
  | zero =>
      funext i
      have hi : i.1 = 0 :=
        Nat.eq_zero_of_le_zero (Finset.mem_Iic.mp i.2)
      have hi_subtype : i = ⟨0, Finset.mem_Iic.mpr le_rfl⟩ := Subtype.ext hi
      subst i
      simp [selectedPolicySuccessorTelescopingPairHistory,
        selectedPolicySuccessorTelescopingGeneratedUCBAction,
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
      rw [selectedPolicySuccessorTelescopingPairHistory]
      change
        History.extendPairHistorySucc
            (selectedPolicySuccessorTelescopingPairHistory
              hK sigma2 delta defaultAction n previousRewardHistory)
            _ = _
      rw [hprevious, ih, History.finitePairHistoryOfTrace_succ]
      apply congrArg
        (History.extendPairHistorySucc
          (History.finitePairHistoryOfTrace
            (selectedPolicySuccessorTelescopingGeneratedUCBAction
              hK sigma2 delta defaultAction reward omega)
            (reward omega) n))
      apply Prod.ext
      · exact (selectedPolicySuccessorTelescopingGeneratedUCBAction_succ
          hK sigma2 delta defaultAction reward omega n).symm
      · rfl

/-- Finite-history score, empirical count, and empirical mean are exactly the
score, count, and mean on the generated scheduled trajectory. -/
theorem selectedPolicySuccessorTelescopingHistoryIndex_finitePairHistoryOfTrace
    {Omega : Type} {K : Nat}
    (action : Omega -> ActionTrace (Fin K))
    (reward : Omega -> RewardTrace Rat)
    (sigma2 : NNReal) (delta : Real) (defaultAction : Fin K)
    (omega : Omega) (t : Nat) (arm : Fin K) :
    selectedPolicySuccessorTelescopingHistoryIndex sigma2 delta defaultAction t
        (History.finitePairHistoryOfTrace
          (action omega) (reward omega) t) arm =
      selectedPolicySuccessorTelescopingIndexAt
        action reward sigma2 delta omega t arm := by
  unfold selectedPolicySuccessorTelescopingHistoryIndex
    selectedPolicySuccessorTelescopingIndexAt confidenceScore
    selectedPolicySuccessorEmpiricalMeanAt
    selectedPolicySuccessorTelescopingRadiusAt
    ConditionalExpectationReward.successorArmEmpiricalMean
  simp only
  rw [successorArmRewardSum_completeFinitePairHistory,
    successorArmPullCount_completeFinitePairHistory]

/-- At every post-initialization generated round, the chosen scheduled score
dominates every candidate arm score on the same generated trace. -/
theorem selectedPolicySuccessorTelescopingIndexAt_le_generatedAction_of_K_le
    {Omega : Type} {K : Nat} (hK : 0 < K)
    (sigma2 : NNReal) (delta : Real) (defaultAction : Fin K)
    (reward : Omega -> RewardTrace Rat) (omega : Omega)
    (t : Nat) (ht : K <= t) (arm : Fin K) :
    let action := selectedPolicySuccessorTelescopingGeneratedUCBAction
      hK sigma2 delta defaultAction reward
    selectedPolicySuccessorTelescopingIndexAt
        action reward sigma2 delta omega t arm <=
      selectedPolicySuccessorTelescopingIndexAt
        action reward sigma2 delta omega t (action omega (t + 1)) := by
  let action := selectedPolicySuccessorTelescopingGeneratedUCBAction
    hK sigma2 delta defaultAction reward
  let history := History.finitePairHistoryOfTrace
    (action omega) (reward omega) t
  have hhistory :
      selectedPolicySuccessorTelescopingPairHistory
          hK sigma2 delta defaultAction t
          (History.finiteRewardHistoryOfTrace (reward omega) t) =
        history := by
    exact selectedPolicySuccessorTelescopingPairHistory_eq_finitePairHistoryOfTrace
      hK sigma2 delta defaultAction reward omega t
  have hselected :
      action omega (t + 1) =
        selectedPolicySuccessorTelescopingHistoryNextArm
          hK sigma2 delta defaultAction t history := by
    simpa [action, history, hhistory] using
      (selectedPolicySuccessorTelescopingGeneratedUCBAction_succ
        hK sigma2 delta defaultAction reward omega t)
  have hmax :=
    selectedPolicySuccessorTelescopingHistoryIndex_le_nextArm_of_K_le
      hK sigma2 delta defaultAction t history ht arm
  rw [← hselected] at hmax
  simpa [action, history] using
    (show
      selectedPolicySuccessorTelescopingIndexAt
          action reward sigma2 delta omega t arm <=
        selectedPolicySuccessorTelescopingIndexAt
          action reward sigma2 delta omega t (action omega (t + 1)) by
      simpa only [
        ← selectedPolicySuccessorTelescopingHistoryIndex_finitePairHistoryOfTrace
          action reward sigma2 delta defaultAction omega t arm,
        ← selectedPolicySuccessorTelescopingHistoryIndex_finitePairHistoryOfTrace
          action reward sigma2 delta defaultAction omega t
            (action omega (t + 1))] using hmax)

/-- Scheduled successor initialization remains the one-pass round robin. -/
theorem selectedPolicySuccessorTelescopingGeneratedUCBAction_succ_eq_initializationArm_of_lt
    {Omega : Type} {K : Nat} (hK : 0 < K)
    (sigma2 : NNReal) (delta : Real) (defaultAction : Fin K)
    (reward : Omega -> RewardTrace Rat) (omega : Omega)
    (t : Nat) (ht : t < K) :
    selectedPolicySuccessorTelescopingGeneratedUCBAction
        hK sigma2 delta defaultAction reward omega (t + 1) =
      initializationArm hK t := by
  simp [selectedPolicySuccessorTelescopingHistoryNextArm, ht]

/-- Every arm is pulled exactly once in the scheduled initialization cycle. -/
theorem successorArmPullCount_selectedPolicySuccessorTelescopingGeneratedUCBAction_K_add_one_eq_one
    {Omega : Type} {K : Nat} (hK : 0 < K)
    (sigma2 : NNReal) (delta : Real) (defaultAction : Fin K)
    (reward : Omega -> RewardTrace Rat) (omega : Omega) (arm : Fin K) :
    ConditionalExpectationReward.successorArmPullCount
        (selectedPolicySuccessorTelescopingGeneratedUCBAction
          hK sigma2 delta defaultAction reward omega)
        arm (K + 1) = 1 := by
  let spec : ETC.Spec K := { hK := hK, explorationPulls := 1 }
  let action := selectedPolicySuccessorTelescopingGeneratedUCBAction
    hK sigma2 delta defaultAction reward omega
  have haction : forall t, t < K ->
      action (t + 1) = ETC.exploreArm spec t := by
    intro t ht
    exact
      selectedPolicySuccessorTelescopingGeneratedUCBAction_succ_eq_initializationArm_of_lt
        hK sigma2 delta defaultAction reward omega t ht
  unfold ConditionalExpectationReward.successorArmPullCount
  simp only [Nat.add_sub_cancel]
  have hcount :
      pullCount (fun i => action (i + 1)) arm K =
        pullCount (ETC.exploreArm spec) arm K := by
    apply pullCount_eq_of_forall_lt
    exact haction
  rw [hcount]
  exact ETC.pullCount_exploreArm_K_eq_one spec arm

/-- After initialization every scheduled successor arm count is positive. -/
theorem successorArmPullCount_selectedPolicySuccessorTelescopingGeneratedUCBAction_pos_of_K_le
    {Omega : Type} {K : Nat} (hK : 0 < K)
    (sigma2 : NNReal) (delta : Real) (defaultAction : Fin K)
    (reward : Omega -> RewardTrace Rat) (omega : Omega)
    (arm : Fin K) (t : Nat) (ht : K <= t) :
    0 < ConditionalExpectationReward.successorArmPullCount
      (selectedPolicySuccessorTelescopingGeneratedUCBAction
        hK sigma2 delta defaultAction reward omega)
      arm (t + 1) := by
  let action := selectedPolicySuccessorTelescopingGeneratedUCBAction
    hK sigma2 delta defaultAction reward omega
  have hmono := pullCount_mono (fun i => action (i + 1)) arm ht
  have hinit :=
    successorArmPullCount_selectedPolicySuccessorTelescopingGeneratedUCBAction_K_add_one_eq_one
      hK sigma2 delta defaultAction reward omega arm
  unfold ConditionalExpectationReward.successorArmPullCount at hinit ⊢
  simp only [Nat.add_sub_cancel] at hinit ⊢
  have hinit' : pullCount (fun i => action (i + 1)) arm K = 1 := by
    simpa [action] using hinit
  rw [hinit'] at hmono
  exact lt_of_lt_of_le Nat.zero_lt_one hmono

/-- A selected scheduled round with positive prior count is post-initialization. -/
theorem K_le_of_selectedPolicySuccessorTelescopingGeneratedUCBAction_selected_and_count_pos
    {Omega : Type} {K : Nat} (hK : 0 < K)
    (sigma2 : NNReal) (delta : Real) (defaultAction : Fin K)
    (reward : Omega -> RewardTrace Rat) (omega : Omega)
    (arm : Fin K) (t : Nat)
    (hselected :
      selectedPolicySuccessorTelescopingGeneratedUCBAction
        hK sigma2 delta defaultAction reward omega (t + 1) = arm)
    (hcount :
      0 < ConditionalExpectationReward.successorArmPullCount
        (selectedPolicySuccessorTelescopingGeneratedUCBAction
          hK sigma2 delta defaultAction reward omega)
        arm (t + 1)) : K <= t := by
  by_contra hnot
  have ht : t < K := Nat.lt_of_not_ge hnot
  let action := selectedPolicySuccessorTelescopingGeneratedUCBAction
    hK sigma2 delta defaultAction reward omega
  have hselected' : (fun i => action (i + 1)) t = arm := by
    simpa [action] using hselected
  have hstep := pullCount_succ_of_eq
    (fun i => action (i + 1)) arm t hselected'
  have hmono := pullCount_mono
    (fun i => action (i + 1)) arm (Nat.succ_le_of_lt ht)
  have hinit :=
    successorArmPullCount_selectedPolicySuccessorTelescopingGeneratedUCBAction_K_add_one_eq_one
      hK sigma2 delta defaultAction reward omega arm
  have hinit' : pullCount (fun i => action (i + 1)) arm K = 1 := by
    simpa [action, ConditionalExpectationReward.successorArmPullCount] using hinit
  have hprior : 0 < pullCount (fun i => action (i + 1)) arm t := by
    simpa [action, ConditionalExpectationReward.successorArmPullCount] using hcount
  rw [hstep, hinit'] at hmono
  omega

/-- Timewise measurability of the fixed-policy generated action. -/
theorem measurable_selectedPolicySuccessorTelescopingGeneratedUCBAction
    {Omega : Type} [MeasurableSpace Omega]
    {K : Nat} (hK : 0 < K) (sigma2 : NNReal) (delta : Real)
    (defaultAction : Fin K) (reward : Omega -> RewardTrace Rat)
    (hreward : forall t : Nat,
      Measurable (fun omega : Omega => reward omega t)) (t : Nat) :
    Measurable (fun omega =>
      selectedPolicySuccessorTelescopingGeneratedUCBAction
        hK sigma2 delta defaultAction reward omega t) := by
  exact
    ConditionalExpectationReward.generatedActionFromRewardHistory_measurable
      (policy := selectedPolicySuccessorTelescopingHistoryPolicy
        hK sigma2 delta defaultAction)
      (state := selectedPolicySuccessorTelescopingHistoryState
        hK sigma2 delta defaultAction)
      (defaultAction := defaultAction) (reward := reward)
      hreward
      (measurable_selectedPolicySuccessorTelescopingHistoryState
        hK sigma2 delta defaultAction)
      t

/-- The logarithmic budget inside the scheduled radius at history index `n`. -/
noncomputable def selectedPolicySuccessorTelescopingLogBudget
    (K n : Nat) (delta : Real) : Real :=
  selectedPolicySuccessorFiniteArmTimeLogBudget K 1 (n + 1)
    (Concentration.telescopingConfidenceShare delta n)

/-- Explicit polynomial reciprocal form of the scheduled log budget. -/
theorem selectedPolicySuccessorTelescopingLogBudget_eq
    (K n : Nat) (delta : Real) (hK : 0 < K) (hdelta : 0 < delta) :
    selectedPolicySuccessorTelescopingLogBudget K n delta =
      max (Real.log
        (2 * (K : Real) * ((n + 1 : Nat) : Real) ^ 2 *
          ((n + 2 : Nat) : Real) / delta)) 0 := by
  unfold selectedPolicySuccessorTelescopingLogBudget
    selectedPolicySuccessorFiniteArmTimeLogBudget
  rw [Concentration.telescopingConfidenceShare_eq_div]
  congr 2
  field_simp
  ring_nf

/-- The scheduled log budget is nondecreasing in the history index. -/
theorem selectedPolicySuccessorTelescopingLogBudget_mono
    (K n T : Nat) (delta : Real) (hK : 0 < K) (hdelta : 0 < delta)
    (hnT : n <= T) :
    selectedPolicySuccessorTelescopingLogBudget K n delta <=
      selectedPolicySuccessorTelescopingLogBudget K T delta := by
  rw [selectedPolicySuccessorTelescopingLogBudget_eq K n delta hK hdelta,
    selectedPolicySuccessorTelescopingLogBudget_eq K T delta hK hdelta]
  apply max_le_max _ le_rfl
  apply Real.log_le_log
  · positivity
  · have h1 : ((n + 1 : Nat) : Real) <= ((T + 1 : Nat) : Real) := by
      exact_mod_cast Nat.add_le_add_right hnT 1
    have h2 : ((n + 2 : Nat) : Real) <= ((T + 2 : Nat) : Real) := by
      exact_mod_cast Nat.add_le_add_right hnT 2
    have hKReal : 0 <= (K : Real) := by positivity
    have hdeltaReal : 0 < delta := hdelta
    gcongr

/-- Expanded algebraic form of one scheduled random-count radius. -/
theorem successorArmEmpiricalMeanTelescopingPeelingRadius_eq
    {K : Nat} (sigma2 : NNReal) (k n : Nat) (delta : Real) :
    ConditionalExpectationReward.successorArmEmpiricalMeanPeelingRadius
        sigma2 k (n + 1)
        (Concentration.telescopingConfidenceShare delta n / (K : Real)) =
      (2 * Real.sqrt
          ((1 / 2 : Real) * (((sigma2 : NNReal) : Real) * (k : Real)) *
            selectedPolicySuccessorTelescopingLogBudget K n delta) +
        selectedPolicySuccessorTelescopingLogBudget K n delta) /
      (k : Real) := by
  simpa [selectedPolicySuccessorTelescopingLogBudget,
    ConditionalExpectationReward.successorArmEmpiricalMeanFiniteArmTimePeelingRadius,
    ConditionalExpectationReward.successorArmEmpiricalMeanFiniteArmTimeConfidenceShare]
    using
      (successorArmEmpiricalMeanFiniteArmTimePeelingRadius_eq
        (K := K) sigma2 k (n + 1) 1
        (Concentration.telescopingConfidenceShare delta n))

/-- Real terminal envelope for inverting every scheduled radius up to index
`T`. -/
noncomputable def selectedPolicySuccessorTelescopingRealPullThreshold
    (K : Nat) (sigma2 : NNReal) (T : Nat) (delta gap : Real) : Real :=
  max
    (32 * (((sigma2 : NNReal) : Real)) *
      selectedPolicySuccessorTelescopingLogBudget K T delta / gap ^ 2)
    (4 * selectedPolicySuccessorTelescopingLogBudget K T delta / gap)

/-- One more than the ceiling supplies the strict count-inversion margin. -/
noncomputable def selectedPolicySuccessorTelescopingPullThreshold
    (K : Nat) (sigma2 : NNReal) (T : Nat) (delta gap : Real) : Nat :=
  Nat.ceil
      (selectedPolicySuccessorTelescopingRealPullThreshold
        K sigma2 T delta gap) + 1

/-- The terminal scheduled threshold satisfies the quadratic and linear
radius-inversion contracts. -/
theorem selectedPolicySuccessorTelescopingPullThreshold_contracts
    (K : Nat) (sigma2 : NNReal) (T : Nat) (delta gap : Real)
    (hgap : 0 < gap) :
    0 < selectedPolicySuccessorTelescopingPullThreshold
        K sigma2 T delta gap /\
      32 * (((sigma2 : NNReal) : Real)) *
          selectedPolicySuccessorTelescopingLogBudget K T delta <
        gap ^ 2 *
          (selectedPolicySuccessorTelescopingPullThreshold
            K sigma2 T delta gap : Real) /\
      4 * selectedPolicySuccessorTelescopingLogBudget K T delta <
        gap *
          (selectedPolicySuccessorTelescopingPullThreshold
            K sigma2 T delta gap : Real) := by
  let budget := selectedPolicySuccessorTelescopingLogBudget K T delta
  let variance := (((sigma2 : NNReal) : Real))
  let realThreshold :=
    max (32 * variance * budget / gap ^ 2) (4 * budget / gap)
  let threshold := Nat.ceil realThreshold + 1
  have hbudget : 0 <= budget := by
    exact le_max_right _ _
  have hquadratic_nonneg : 0 <= 32 * variance * budget / gap ^ 2 := by
    positivity
  have hrealThreshold_nonneg : 0 <= realThreshold := by
    exact hquadratic_nonneg.trans (le_max_left _ _)
  have hrealThreshold_le_ceil :
      realThreshold <= (Nat.ceil realThreshold : Real) := Nat.le_ceil _
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
    simpa [mul_comm] using
      (div_lt_iff₀ (sq_pos_of_pos hgap)).mp hquadratic_div
  have hlinear : 4 * budget < gap * (threshold : Real) := by
    simpa [mul_comm] using (div_lt_iff₀ hgap).mp hlinear_div
  simpa [selectedPolicySuccessorTelescopingPullThreshold,
    selectedPolicySuccessorTelescopingRealPullThreshold,
    threshold, realThreshold, variance, budget] using
      (show 0 < threshold /\
          32 * variance * budget < gap ^ 2 * (threshold : Real) /\
          4 * budget < gap * (threshold : Real) from
        ⟨Nat.succ_pos _, hquadratic, hlinear⟩)

/-- Every count beyond the terminal envelope makes the scheduled radius at
every earlier history index strictly smaller than half the positive gap. -/
theorem two_mul_successorArmEmpiricalMeanTelescopingPeelingRadius_lt_gap_of_threshold
    {K : Nat} (hK : 0 < K) (sigma2 : NNReal) (delta gap : Real)
    (hdelta : 0 < delta) (hgap : 0 < gap)
    (k n T : Nat)
    (hk : selectedPolicySuccessorTelescopingPullThreshold
      K sigma2 T delta gap <= k)
    (hnT : n <= T) :
    2 * ConditionalExpectationReward.successorArmEmpiricalMeanPeelingRadius
          sigma2 k (n + 1)
          (Concentration.telescopingConfidenceShare delta n / (K : Real)) <
      gap := by
  have hcontracts :=
    selectedPolicySuccessorTelescopingPullThreshold_contracts
      K sigma2 T delta gap hgap
  have hkpos : 0 < k := lt_of_lt_of_le hcontracts.1 hk
  have hbudget :=
    selectedPolicySuccessorTelescopingLogBudget_mono
      K n T delta hK hdelta hnT
  have hkReal :
      (selectedPolicySuccessorTelescopingPullThreshold
        K sigma2 T delta gap : Real) <= (k : Real) := by
    exact_mod_cast hk
  have hquadratic :
      32 * (((sigma2 : NNReal) : Real)) *
          selectedPolicySuccessorTelescopingLogBudget K n delta <
        gap ^ 2 * (k : Real) := by
    calc
      32 * (((sigma2 : NNReal) : Real)) *
          selectedPolicySuccessorTelescopingLogBudget K n delta <=
        32 * (((sigma2 : NNReal) : Real)) *
          selectedPolicySuccessorTelescopingLogBudget K T delta := by
            gcongr
      _ < gap ^ 2 *
          (selectedPolicySuccessorTelescopingPullThreshold
            K sigma2 T delta gap : Real) := hcontracts.2.1
      _ <= gap ^ 2 * (k : Real) := by gcongr
  have hlinear :
      4 * selectedPolicySuccessorTelescopingLogBudget K n delta <
        gap * (k : Real) := by
    calc
      4 * selectedPolicySuccessorTelescopingLogBudget K n delta <=
          4 * selectedPolicySuccessorTelescopingLogBudget K T delta := by
            gcongr
      _ < gap *
          (selectedPolicySuccessorTelescopingPullThreshold
            K sigma2 T delta gap : Real) := hcontracts.2.2
      _ <= gap * (k : Real) := by gcongr
  have hbase :=
    two_mul_successorArmEmpiricalMeanFiniteArmTimePeelingRadius_lt_gap
      (K := K) sigma2 k (n + 1) 1
      (Concentration.telescopingConfidenceShare delta n) gap
      hkpos hgap hquadratic hlinear
  simpa [
    ConditionalExpectationReward.successorArmEmpiricalMeanFiniteArmTimePeelingRadius,
    ConditionalExpectationReward.successorArmEmpiricalMeanFiniteArmTimeConfidenceShare]
    using hbase

/-- Outside the one telescoping bad event, scheduled score maximality implies
the standard UCB gap bound at every initialized generated round. -/
theorem selectedPolicySuccessorTelescoping_meanGap_le_two_radius_of_not_badEvent
    {Omega : Type} {K : Nat} (hK : 0 < K)
    (reward : Omega -> RewardTrace Rat) (armMean : Fin K -> Rat)
    (sigma2 : NNReal) (delta : Real) (defaultAction best : Fin K)
    (omega : Omega) (t : Nat) (ht : K <= t)
    (hgood : omega ∉
      ConditionalExpectationReward.successorArmEmpiricalMeanFintypeTelescopingAllTimeBadEvent
        (selectedPolicySuccessorTelescopingGeneratedUCBAction
          hK sigma2 delta defaultAction reward)
        reward armMean sigma2 delta) :
    let action := selectedPolicySuccessorTelescopingGeneratedUCBAction
      hK sigma2 delta defaultAction reward
    meanGap (fun arm => (armMean arm : Real)) best
        (action omega (t + 1)) <=
      2 * selectedPolicySuccessorTelescopingRadiusAt
        action sigma2 delta omega t (action omega (t + 1)) := by
  let action := selectedPolicySuccessorTelescopingGeneratedUCBAction
    hK sigma2 delta defaultAction reward
  let empiricalMean : Fin K -> Real := fun arm =>
    selectedPolicySuccessorEmpiricalMeanAt action reward omega t arm
  let radius : Fin K -> Real := fun arm =>
    selectedPolicySuccessorTelescopingRadiusAt
      action sigma2 delta omega t arm
  have hcount (arm : Fin K) :
      0 < ConditionalExpectationReward.successorArmPullCount
        (action omega) arm (t + 1) :=
    successorArmPullCount_selectedPolicySuccessorTelescopingGeneratedUCBAction_pos_of_K_le
      hK sigma2 delta defaultAction reward omega arm t ht
  have hpair (arm : Fin K)
      (hdeviation : radius arm <=
        |empiricalMean arm - (armMean arm : Real)|) :
      omega ∈
        ConditionalExpectationReward.successorArmEmpiricalMeanFintypeTelescopingAllTimeBadEvent
          action reward armMean sigma2 delta := by
    unfold ConditionalExpectationReward.successorArmEmpiricalMeanFintypeTelescopingAllTimeBadEvent
    exact Set.mem_iUnion.mpr ⟨t, Set.mem_iUnion.mpr ⟨arm, by
      simpa [action, empiricalMean, radius,
        selectedPolicySuccessorEmpiricalMeanAt,
        selectedPolicySuccessorTelescopingRadiusAt] using
          And.intro (hcount arm) hdeviation⟩⟩
  have hbestAbs :
      |empiricalMean best - (armMean best : Real)| < radius best := by
    by_contra hnot
    exact hgood (hpair best (le_of_not_gt hnot))
  have hchosenAbs :
      |empiricalMean (action omega (t + 1)) -
          (armMean (action omega (t + 1)) : Real)| <
        radius (action omega (t + 1)) := by
    by_contra hnot
    exact hgood (hpair (action omega (t + 1)) (le_of_not_gt hnot))
  have hbestUpper :
      (armMean best : Real) <= confidenceScore empiricalMean radius best := by
    have hneg := neg_le_abs (empiricalMean best - (armMean best : Real))
    simp only [confidenceScore]
    linarith
  have hchosenLower :
      empiricalMean (action omega (t + 1)) -
          radius (action omega (t + 1)) <=
        (armMean (action omega (t + 1)) : Real) := by
    have hself := le_abs_self
      (empiricalMean (action omega (t + 1)) -
        (armMean (action omega (t + 1)) : Real))
    linarith
  have hscore :
      confidenceScore empiricalMean radius best <=
        confidenceScore empiricalMean radius (action omega (t + 1)) := by
    simpa [empiricalMean, radius,
      selectedPolicySuccessorTelescopingIndexAt] using
      (selectedPolicySuccessorTelescopingIndexAt_le_generatedAction_of_K_le
        hK sigma2 delta defaultAction reward omega t ht best)
  simpa [action, radius] using
    (meanGap_le_two_radius_of_confidenceScore_max
      (fun arm => (armMean arm : Real)) empiricalMean radius
      best (action omega (t + 1)) hbestUpper hchosenLower hscore)

/-- The single all-time good event controls one positive-gap arm at every
finite horizon; the horizon appears only in the deterministic bound. -/
theorem selectedPolicySuccessorTelescoping_pullCount_le_of_not_badEvent
    {Omega : Type} {K : Nat} (hK : 0 < K)
    (reward : Omega -> RewardTrace Rat) (armMean : Fin K -> Rat)
    (sigma2 : NNReal) (delta : Real) (hdelta : 0 < delta)
    (defaultAction best chosen : Fin K) (omega : Omega) (T : Nat)
    (hgap : 0 < meanGap (fun arm => (armMean arm : Real)) best chosen)
    (hgood : omega ∉
      ConditionalExpectationReward.successorArmEmpiricalMeanFintypeTelescopingAllTimeBadEvent
        (selectedPolicySuccessorTelescopingGeneratedUCBAction
          hK sigma2 delta defaultAction reward)
        reward armMean sigma2 delta) :
    ConditionalExpectationReward.successorArmPullCount
        (selectedPolicySuccessorTelescopingGeneratedUCBAction
          hK sigma2 delta defaultAction reward omega)
        chosen (T + 1) <=
      selectedPolicySuccessorTelescopingPullThreshold
        K sigma2 T delta
          (meanGap (fun arm => (armMean arm : Real)) best chosen) := by
  let action := selectedPolicySuccessorTelescopingGeneratedUCBAction
    hK sigma2 delta defaultAction reward
  let gap := meanGap (fun arm => (armMean arm : Real)) best chosen
  let B := selectedPolicySuccessorTelescopingPullThreshold
    K sigma2 T delta gap
  by_contra hnot
  have hfinal : B < pullCount (fun i => action omega (i + 1)) chosen T := by
    simpa [action, B, ConditionalExpectationReward.successorArmPullCount]
      using Nat.lt_of_not_ge hnot
  obtain ⟨t, ht, hselected, hprior⟩ :=
    exists_selected_with_threshold_le_prior_pullCount
      (fun i => action omega (i + 1)) chosen T B hfinal
  have hBpos : 0 < B :=
    (selectedPolicySuccessorTelescopingPullThreshold_contracts
      K sigma2 T delta gap (by simpa [gap] using hgap)).1
  have hpriorPos :
      0 < ConditionalExpectationReward.successorArmPullCount
        (action omega) chosen (t + 1) := by
    have : 0 < pullCount (fun i => action omega (i + 1)) chosen t :=
      lt_of_lt_of_le hBpos hprior
    simpa [ConditionalExpectationReward.successorArmPullCount] using this
  have hKle : K <= t :=
    K_le_of_selectedPolicySuccessorTelescopingGeneratedUCBAction_selected_and_count_pos
      hK sigma2 delta defaultAction reward omega chosen t
      (by simpa [action] using hselected) hpriorPos
  have hgapBound :=
    selectedPolicySuccessorTelescoping_meanGap_le_two_radius_of_not_badEvent
      hK reward armMean sigma2 delta defaultAction best omega t hKle hgood
  have hradius :=
    two_mul_successorArmEmpiricalMeanTelescopingPeelingRadius_lt_gap_of_threshold
      hK sigma2 delta gap hdelta (by simpa [gap] using hgap)
      (ConditionalExpectationReward.successorArmPullCount
        (action omega) chosen (t + 1)) t T
      (by simpa [B, ConditionalExpectationReward.successorArmPullCount]
        using hprior)
      (Nat.le_of_lt ht)
  have hselected' : action omega (t + 1) = chosen := by
    simpa using hselected
  dsimp only at hgapBound
  change
    selectedPolicySuccessorTelescopingGeneratedUCBAction
      hK sigma2 delta defaultAction reward omega (t + 1) = chosen
    at hselected'
  rw [hselected'] at hgapBound
  have hgapBound' : gap <=
      2 * ConditionalExpectationReward.successorArmEmpiricalMeanPeelingRadius
        sigma2
        (ConditionalExpectationReward.successorArmPullCount
          (action omega) chosen (t + 1))
        (t + 1)
        (Concentration.telescopingConfidenceShare delta t / (K : Real)) := by
    simpa [action, gap,
      selectedPolicySuccessorTelescopingRadiusAt] using hgapBound
  exact (not_lt_of_ge hgapBound') hradius

/-- The accepted telescoping all-time confidence producer instantiated on the
single scheduled policy.  The sampled pair action and the reward-reconstructed
policy action are transported on their explicit almost-everywhere alignment
set, so the conclusion is about the action actually consumed by the UCB score
and regret definitions. -/
theorem actionRewardHistoryStepKernelFamily_selectedPolicySuccessorTelescoping_allTimeConfidence
    {Context : Type} {K : Nat} [MeasurableSpace Context]
    (hK : 0 < K)
    (mu0 : Measure (Prod (Fin K) Rat)) [IsProbabilityMeasure mu0]
    (rewardKernel : RewardKernel.MarkovRewardKernel (Prod Context (Fin K)) Rat)
    (context : (n : Nat) -> ((j : Finset.Iic n) -> Rat) -> Context)
    (mean : Context -> Fin K -> Rat)
    (varianceProxy : Context -> Fin K -> NNReal)
    (defaultAction : Fin K) (armMean : Fin K -> Rat)
    (sigma2 : NNReal) (delta : Real)
    (hcontext : forall n : Nat, Measurable (context n))
    (hmean : Measurable (fun pair : Prod Context (Fin K) =>
      mean pair.1 pair.2))
    (law : RewardKernel.CenteredRewardKernelLaw rewardKernel mean varianceProxy)
    (hvariance : forall i : Nat,
      forall history : ((j : Finset.Iic i) -> Rat),
        varianceProxy (context i history)
            ((selectedPolicySuccessorTelescopingHistoryPolicy
              hK sigma2 delta defaultAction i).action
              (selectedPolicySuccessorTelescopingHistoryState
                hK sigma2 delta defaultAction i history)) <= sigma2)
    (harmMean : forall i : Nat,
      forall history : ((j : Finset.Iic i) -> Rat),
        forall arm : Fin K,
          mean (context i history) arm = armMean arm)
    (hsigma2 : 0 < (((sigma2 : NNReal) : Real)))
    (hdelta : 0 < delta) :
    let policy := selectedPolicySuccessorTelescopingHistoryPolicy
      hK sigma2 delta defaultAction
    let state := selectedPolicySuccessorTelescopingHistoryState
      hK sigma2 delta defaultAction
    let pairContext :
        (i : Nat) -> ((j : Finset.Iic i) -> Prod (Fin K) Rat) -> Context :=
      fun i history => context i (History.pairHistoryRewardProjection history)
    let pairState :
        (i : Nat) -> ((j : Finset.Iic i) -> Prod (Fin K) Rat) ->
          SelectedPolicySuccessorFiniteHistoryState K :=
      fun i history => state i (History.pairHistoryRewardProjection history)
    let hpairContext : forall i : Nat, Measurable (pairContext i) := fun i =>
      (hcontext i).comp
        (History.measurable_pairHistoryRewardProjection
          (Action := Fin K) (Reward := Rat) i)
    let hpairState : forall i : Nat, Measurable (pairState i) := fun i =>
      (measurable_selectedPolicySuccessorTelescopingHistoryState
        hK sigma2 delta defaultAction i).comp
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
    let generatedAction :=
      selectedPolicySuccessorTelescopingGeneratedUCBAction
        hK sigma2 delta defaultAction reward
    mu
        (ConditionalExpectationReward.successorArmEmpiricalMeanFintypeTelescopingAllTimeBadEvent
          generatedAction reward armMean sigma2 delta) <=
      ENNReal.ofReal delta := by
  classical
  letI : Nonempty (Fin K) := ⟨Fin.mk 0 hK⟩
  let policy := selectedPolicySuccessorTelescopingHistoryPolicy
    hK sigma2 delta defaultAction
  let state := selectedPolicySuccessorTelescopingHistoryState
    hK sigma2 delta defaultAction
  let pairContext :
      (i : Nat) -> ((j : Finset.Iic i) -> Prod (Fin K) Rat) -> Context :=
    fun i history => context i (History.pairHistoryRewardProjection history)
  let pairState :
      (i : Nat) -> ((j : Finset.Iic i) -> Prod (Fin K) Rat) ->
        SelectedPolicySuccessorFiniteHistoryState K :=
    fun i history => state i (History.pairHistoryRewardProjection history)
  let hpairContext : forall i : Nat, Measurable (pairContext i) := fun i =>
    (hcontext i).comp
      (History.measurable_pairHistoryRewardProjection
        (Action := Fin K) (Reward := Rat) i)
  let hpairState : forall i : Nat, Measurable (pairState i) := fun i =>
    (measurable_selectedPolicySuccessorTelescopingHistoryState
      hK sigma2 delta defaultAction i).comp
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
  let generatedAction :=
    selectedPolicySuccessorTelescopingGeneratedUCBAction
      hK sigma2 delta defaultAction reward
  let sampledBad :=
    ConditionalExpectationReward.successorArmEmpiricalMeanFintypeTelescopingAllTimeBadEvent
      sampledAction reward armMean sigma2 delta
  let generatedBad :=
    ConditionalExpectationReward.successorArmEmpiricalMeanFintypeTelescopingAllTimeBadEvent
      generatedAction reward armMean sigma2 delta
  have htail :=
    ConditionalExpectationReward.actionRewardHistoryStepKernelFamily_successorArmEmpiricalMean_simultaneous_fintype_telescopingAllTime_abs_tail_ennreal_delta_trajMeasure
      (mu0 := mu0)
      (rewardKernel := rewardKernel)
      (policy := policy)
      (context := context)
      (state := state)
      (hcontext := hcontext)
      (hstate := measurable_selectedPolicySuccessorTelescopingHistoryState
        hK sigma2 delta defaultAction)
      (mean := mean)
      (varianceProxy := varianceProxy)
      (law := law)
      (hmean := hmean)
      (armMean := armMean)
      (sigma2 := sigma2)
      (hvariance := hvariance)
      (harmMean := harmMean)
      hsigma2 delta hdelta
  have htail' : mu sampledBad <= ENNReal.ofReal delta := by
    simpa [policy, state, pairContext, pairState, hpairContext, hpairState,
      stepKernel, mu, sampledAction, reward, sampledBad] using htail
  have hactionEq : forall i : Nat,
      Filter.EventuallyEq (ae mu)
        (fun trajectory : Nat -> Prod (Fin K) Rat =>
          sampledAction trajectory (i + 1))
        (fun trajectory : Nat -> Prod (Fin K) Rat =>
          generatedAction trajectory (i + 1)) := by
    intro i
    have hcanonical :=
      ConditionalExpectationReward.actionRewardHistoryStepKernelFamily_action_succ_ae_eq_policy_trajMeasure
        mu0 rewardKernel policy pairContext pairState hpairContext hpairState i
    simpa [mu, stepKernel, sampledAction, generatedAction,
      selectedPolicySuccessorTelescopingGeneratedUCBAction,
      ConditionalExpectationReward.generatedActionFromRewardHistory,
      Policy.generatedActionTraceSucc, policy, state, pairState, reward,
      History.pairHistoryRewardProjection, History.finiteRewardHistoryOfTrace,
      Preorder.frestrictLe_apply] using hcanonical
  have hactionAll : ∀ᵐ trajectory ∂mu, forall i : Nat,
      sampledAction trajectory (i + 1) =
        generatedAction trajectory (i + 1) :=
    ae_all_iff.2 hactionEq
  have hgeneratedBad_to_sampledBad : ∀ᵐ trajectory ∂mu,
      trajectory ∈ generatedBad -> trajectory ∈ sampledBad := by
    filter_upwards [hactionAll] with trajectory htrajectory
    intro hbad
    have hshift :
        (fun i => sampledAction trajectory (i + 1)) =
          (fun i => generatedAction trajectory (i + 1)) := by
      funext i
      exact htrajectory i
    simpa [sampledBad, generatedBad,
      ConditionalExpectationReward.successorArmEmpiricalMeanFintypeTelescopingAllTimeBadEvent,
      ConditionalExpectationReward.successorArmEmpiricalMean,
      ConditionalExpectationReward.successorArmRewardSum,
      ConditionalExpectationReward.successorArmPullCount, hshift] using hbad
  have hresult : mu generatedBad <= ENNReal.ofReal delta :=
    (measure_mono_ae hgeneratedBad_to_sampledBad).trans htail'
  simpa [policy, state, pairContext, pairState, hpairContext, hpairState,
    stepKernel, mu, reward, generatedAction, generatedBad] using hresult

/-- One global all-time confidence event yields the terminal pull-count tail
for any requested finite horizon. -/
theorem measure_selectedPolicySuccessorTelescoping_pullCount_gt_threshold_le_of_allTimeConfidence
    {Omega : Type} [MeasurableSpace Omega] {K : Nat} (hK : 0 < K)
    (mu : Measure Omega)
    (reward : Omega -> RewardTrace Rat) (armMean : Fin K -> Rat)
    (sigma2 : NNReal) (delta : Real) (hdelta : 0 < delta)
    (defaultAction best chosen : Fin K) (T : Nat)
    (hgap : 0 < meanGap (fun arm => (armMean arm : Real)) best chosen)
    (hconfidence :
      mu
          (ConditionalExpectationReward.successorArmEmpiricalMeanFintypeTelescopingAllTimeBadEvent
            (selectedPolicySuccessorTelescopingGeneratedUCBAction
              hK sigma2 delta defaultAction reward)
            reward armMean sigma2 delta) <=
        ENNReal.ofReal delta) :
    mu {omega |
        selectedPolicySuccessorTelescopingPullThreshold
            K sigma2 T delta
              (meanGap (fun arm => (armMean arm : Real)) best chosen) <
          ConditionalExpectationReward.successorArmPullCount
            (selectedPolicySuccessorTelescopingGeneratedUCBAction
              hK sigma2 delta defaultAction reward omega)
            chosen (T + 1)} <=
      ENNReal.ofReal delta := by
  refine (measure_mono ?_).trans hconfidence
  intro omega htail
  by_contra hgood
  have hcount :=
    selectedPolicySuccessorTelescoping_pullCount_le_of_not_badEvent
      hK reward armMean sigma2 delta hdelta defaultAction best chosen
      omega T hgap hgood
  exact (not_lt_of_ge hcount) htail

/-- Expected scheduled pull count at any finite horizon.  The explicit
`T * delta` term is retained; no unconditional expectation claim is made from
the good event alone. -/
theorem lintegral_selectedPolicySuccessorTelescoping_pullCount_le_of_allTimeConfidence
    {Omega : Type} [MeasurableSpace Omega] {K : Nat} (hK : 0 < K)
    (mu : Measure Omega) [IsProbabilityMeasure mu]
    (reward : Omega -> RewardTrace Rat)
    (hreward : forall t : Nat,
      Measurable (fun omega : Omega => reward omega t))
    (armMean : Fin K -> Rat) (sigma2 : NNReal) (delta : Real)
    (hdelta : 0 < delta) (defaultAction best chosen : Fin K) (T : Nat)
    (hgap : 0 < meanGap (fun arm => (armMean arm : Real)) best chosen)
    (hconfidence :
      mu
          (ConditionalExpectationReward.successorArmEmpiricalMeanFintypeTelescopingAllTimeBadEvent
            (selectedPolicySuccessorTelescopingGeneratedUCBAction
              hK sigma2 delta defaultAction reward)
            reward armMean sigma2 delta) <=
        ENNReal.ofReal delta) :
    ∫⁻ omega,
        (ConditionalExpectationReward.successorArmPullCount
          (selectedPolicySuccessorTelescopingGeneratedUCBAction
            hK sigma2 delta defaultAction reward omega)
          chosen (T + 1) : ENNReal) ∂mu <=
      (selectedPolicySuccessorTelescopingPullThreshold
        K sigma2 T delta
          (meanGap (fun arm => (armMean arm : Real)) best chosen) : ENNReal) +
        (T : ENNReal) * ENNReal.ofReal delta := by
  let action := selectedPolicySuccessorTelescopingGeneratedUCBAction
    hK sigma2 delta defaultAction reward
  let count : Omega -> Nat := fun omega =>
    ConditionalExpectationReward.successorArmPullCount
      (action omega) chosen (T + 1)
  let threshold := selectedPolicySuccessorTelescopingPullThreshold
    K sigma2 T delta
      (meanGap (fun arm => (armMean arm : Real)) best chosen)
  have haction : forall t : Nat,
      Measurable (fun omega => action omega t) := by
    intro t
    exact measurable_selectedPolicySuccessorTelescopingGeneratedUCBAction
      hK sigma2 delta defaultAction reward hreward t
  have hcountMeas : Measurable count := by
    unfold count ConditionalExpectationReward.successorArmPullCount
    exact measurable_pullCount
      (fun omega i => action omega (i + 1))
      (fun i => haction (i + 1)) chosen (T + 1 - 1)
  have hcountLe : forall omega, count omega <= T := by
    intro omega
    unfold count ConditionalExpectationReward.successorArmPullCount
    simp only [Nat.add_sub_cancel]
    exact pullCount_le_time (fun i => action omega (i + 1)) chosen T
  have htail : mu {omega | threshold < count omega} <=
      ENNReal.ofReal delta := by
    simpa [threshold, count, action] using
      measure_selectedPolicySuccessorTelescoping_pullCount_gt_threshold_le_of_allTimeConfidence
        hK mu reward armMean sigma2 delta hdelta defaultAction best chosen T
        hgap hconfidence
  simpa [threshold, count, action] using
    lintegral_natCast_le_threshold_add_bound_mul_of_measure_gt
      mu count hcountMeas threshold T hcountLe (ENNReal.ofReal delta) htail

/-- Standard regret-time shift of the single scheduled generated policy. -/
noncomputable def selectedPolicySuccessorTelescopingGeneratedUCBRegretAction
    {Omega : Type} {K : Nat} (hK : 0 < K)
    (sigma2 : NNReal) (delta : Real) (defaultAction : Fin K)
    (reward : Omega -> RewardTrace Rat) : Omega -> ActionTrace (Fin K) :=
  fun omega t =>
    selectedPolicySuccessorTelescopingGeneratedUCBAction
      hK sigma2 delta defaultAction reward omega (t + 1)

/-- Timewise measurability of the shifted fixed-policy regret action. -/
theorem measurable_selectedPolicySuccessorTelescopingGeneratedUCBRegretAction
    {Omega : Type} [MeasurableSpace Omega]
    {K : Nat} (hK : 0 < K) (sigma2 : NNReal) (delta : Real)
    (defaultAction : Fin K) (reward : Omega -> RewardTrace Rat)
    (hreward : forall t : Nat,
      Measurable (fun omega : Omega => reward omega t)) (t : Nat) :
    Measurable (fun omega =>
      selectedPolicySuccessorTelescopingGeneratedUCBRegretAction
        hK sigma2 delta defaultAction reward omega t) := by
  exact measurable_selectedPolicySuccessorTelescopingGeneratedUCBAction
    hK sigma2 delta defaultAction reward hreward (t + 1)

/-- Shifted fixed-policy pull counts are the existing successor counts. -/
theorem pullCount_selectedPolicySuccessorTelescopingGeneratedUCBRegretAction_eq
    {Omega : Type} {K : Nat} (hK : 0 < K)
    (sigma2 : NNReal) (delta : Real) (defaultAction : Fin K)
    (reward : Omega -> RewardTrace Rat) (omega : Omega)
    (arm : Fin K) (T : Nat) :
    pullCount
        (selectedPolicySuccessorTelescopingGeneratedUCBRegretAction
          hK sigma2 delta defaultAction reward omega)
        arm T =
      ConditionalExpectationReward.successorArmPullCount
        (selectedPolicySuccessorTelescopingGeneratedUCBAction
          hK sigma2 delta defaultAction reward omega)
        arm (T + 1) := by
  unfold ConditionalExpectationReward.successorArmPullCount
    selectedPolicySuccessorTelescopingGeneratedUCBRegretAction
  rw [Nat.add_sub_cancel]

/-- Finite-time expected pseudo-regret for the single scheduled policy from
its one all-time confidence event. -/
theorem lintegral_ofReal_pseudoRegret_selectedPolicySuccessorTelescoping_le_of_allTimeConfidence
    {Omega : Type} [MeasurableSpace Omega] {K : Nat}
    (mu : Measure Omega) [IsProbabilityMeasure mu]
    (model : FiniteBanditModel K)
    (reward : Omega -> RewardTrace Rat)
    (hreward : forall t : Nat,
      Measurable (fun omega : Omega => reward omega t))
    (sigma2 : NNReal) (delta : Real) (hdelta : 0 < delta)
    (defaultAction : Fin K) (T : Nat)
    (hconfidence :
      mu
          (ConditionalExpectationReward.successorArmEmpiricalMeanFintypeTelescopingAllTimeBadEvent
            (selectedPolicySuccessorTelescopingGeneratedUCBAction
              model.hK sigma2 delta defaultAction reward)
            reward model.mean sigma2 delta) <=
        ENNReal.ofReal delta) :
    ∫⁻ omega,
        ENNReal.ofReal
          (((pseudoRegret model
            (selectedPolicySuccessorTelescopingGeneratedUCBRegretAction
              model.hK sigma2 delta defaultAction reward omega)
            T : Rat) : Real)) ∂mu <=
      (Finset.univ : Finset (Fin K)).sum (fun arm =>
        ENNReal.ofReal (((model.gap arm : Rat) : Real)) *
          ((selectedPolicySuccessorTelescopingPullThreshold
              K sigma2 T delta (((model.gap arm : Rat) : Real)) : Nat) :
                ENNReal) +
            ENNReal.ofReal (((model.gap arm : Rat) : Real)) *
              ((T : ENNReal) * ENNReal.ofReal delta)) := by
  let action := selectedPolicySuccessorTelescopingGeneratedUCBRegretAction
    model.hK sigma2 delta defaultAction reward
  simp_rw [← mul_add]
  apply
    lintegral_ofReal_pseudoRegret_le_sum_gap_mul_bound_of_positiveGap_pullCount
      mu model action
      (measurable_selectedPolicySuccessorTelescopingGeneratedUCBRegretAction
        model.hK sigma2 delta defaultAction reward hreward)
      T
      (fun arm =>
        (selectedPolicySuccessorTelescopingPullThreshold
          K sigma2 T delta (((model.gap arm : Rat) : Real)) : ENNReal) +
          (T : ENNReal) * ENNReal.ofReal delta)
  intro arm hgap
  have hgapEq := modelMeanGap_bestArm_eq_realGap model arm
  have hmeanGap :
      0 < meanGap (fun a => ((model.mean a : Rat) : Real))
        model.bestArm arm := by
    rw [hgapEq]
    exact hgap
  have hcount :=
    lintegral_selectedPolicySuccessorTelescoping_pullCount_le_of_allTimeConfidence
      model.hK mu reward hreward model.mean sigma2 delta hdelta
      defaultAction model.bestArm arm T hmeanGap hconfidence
  rw [hgapEq] at hcount
  simpa [action,
    pullCount_selectedPolicySuccessorTelescopingGeneratedUCBRegretAction_eq]
    using hcount

/-- A single good sample controls every finite horizon and every positive-gap
arm simultaneously. -/
theorem selectedPolicySuccessorTelescoping_allHorizonPullCount_of_not_badEvent
    {Omega : Type} {K : Nat} (hK : 0 < K)
    (reward : Omega -> RewardTrace Rat) (armMean : Fin K -> Rat)
    (sigma2 : NNReal) (delta : Real) (hdelta : 0 < delta)
    (defaultAction best : Fin K) (omega : Omega)
    (hgood : omega ∉
      ConditionalExpectationReward.successorArmEmpiricalMeanFintypeTelescopingAllTimeBadEvent
        (selectedPolicySuccessorTelescopingGeneratedUCBAction
          hK sigma2 delta defaultAction reward)
        reward armMean sigma2 delta) :
    forall T : Nat, forall chosen : Fin K,
      0 < meanGap (fun arm => (armMean arm : Real)) best chosen ->
      ConditionalExpectationReward.successorArmPullCount
          (selectedPolicySuccessorTelescopingGeneratedUCBAction
            hK sigma2 delta defaultAction reward omega)
          chosen (T + 1) <=
        selectedPolicySuccessorTelescopingPullThreshold
          K sigma2 T delta
            (meanGap (fun arm => (armMean arm : Real)) best chosen) := by
  intro T chosen hgap
  exact selectedPolicySuccessorTelescoping_pullCount_le_of_not_badEvent
    hK reward armMean sigma2 delta hdelta defaultAction best chosen
    omega T hgap hgood

/-- The canonical action/reward trajectory measure of the single scheduled
policy.  This declaration itself contains no terminal horizon. -/
noncomputable def selectedPolicySuccessorTelescopingActionRewardTrajMeasure
    {Context : Type} {K : Nat} [MeasurableSpace Context]
    (hK : 0 < K)
    (mu0 : Measure (Prod (Fin K) Rat))
    (rewardKernel : RewardKernel.MarkovRewardKernel (Prod Context (Fin K)) Rat)
    (context : (n : Nat) -> ((j : Finset.Iic n) -> Rat) -> Context)
    (hcontext : forall n : Nat, Measurable (context n))
    (sigma2 : NNReal) (delta : Real) (defaultAction : Fin K) :
    Measure (Nat -> Prod (Fin K) Rat) :=
  let policy := selectedPolicySuccessorTelescopingHistoryPolicy
    hK sigma2 delta defaultAction
  let state := selectedPolicySuccessorTelescopingHistoryState
    hK sigma2 delta defaultAction
  let pairContext :
      (i : Nat) -> ((j : Finset.Iic i) -> Prod (Fin K) Rat) -> Context :=
    fun i history => context i (History.pairHistoryRewardProjection history)
  let pairState :
      (i : Nat) -> ((j : Finset.Iic i) -> Prod (Fin K) Rat) ->
        SelectedPolicySuccessorFiniteHistoryState K :=
    fun i history => state i (History.pairHistoryRewardProjection history)
  let hpairContext : forall i : Nat, Measurable (pairContext i) := fun i =>
    (hcontext i).comp
      (History.measurable_pairHistoryRewardProjection
        (Action := Fin K) (Reward := Rat) i)
  let hpairState : forall i : Nat, Measurable (pairState i) := fun i =>
    (measurable_selectedPolicySuccessorTelescopingHistoryState
      hK sigma2 delta defaultAction i).comp
      (History.measurable_pairHistoryRewardProjection
        (Action := Fin K) (Reward := Rat) i)
  let stepKernel :=
    RewardKernel.actionRewardHistoryStepKernelFamily rewardKernel policy
      pairContext pairState hpairContext hpairState
  ProbabilityTheory.Kernel.trajMeasure
    (X := fun _ : Nat => Prod (Fin K) Rat) mu0 stepKernel

/-- Short canonical surface for the same-policy all-time confidence theorem. -/
theorem measure_selectedPolicySuccessorTelescoping_allTimeBadEvent_le_trajMeasure
    {Context : Type} {K : Nat} [MeasurableSpace Context]
    (hK : 0 < K)
    (mu0 : Measure (Prod (Fin K) Rat)) [IsProbabilityMeasure mu0]
    (rewardKernel : RewardKernel.MarkovRewardKernel (Prod Context (Fin K)) Rat)
    (context : (n : Nat) -> ((j : Finset.Iic n) -> Rat) -> Context)
    (mean : Context -> Fin K -> Rat)
    (varianceProxy : Context -> Fin K -> NNReal)
    (defaultAction : Fin K) (armMean : Fin K -> Rat)
    (sigma2 : NNReal) (delta : Real)
    (hcontext : forall n : Nat, Measurable (context n))
    (hmean : Measurable (fun pair : Prod Context (Fin K) =>
      mean pair.1 pair.2))
    (law : RewardKernel.CenteredRewardKernelLaw rewardKernel mean varianceProxy)
    (hvariance : forall i : Nat,
      forall history : ((j : Finset.Iic i) -> Rat),
        varianceProxy (context i history)
            ((selectedPolicySuccessorTelescopingHistoryPolicy
              hK sigma2 delta defaultAction i).action
              (selectedPolicySuccessorTelescopingHistoryState
                hK sigma2 delta defaultAction i history)) <= sigma2)
    (harmMean : forall i : Nat,
      forall history : ((j : Finset.Iic i) -> Rat),
        forall arm : Fin K,
          mean (context i history) arm = armMean arm)
    (hsigma2 : 0 < (((sigma2 : NNReal) : Real)))
    (hdelta : 0 < delta) :
    let mu := selectedPolicySuccessorTelescopingActionRewardTrajMeasure
      hK mu0 rewardKernel context hcontext sigma2 delta defaultAction
    let reward : (Nat -> Prod (Fin K) Rat) -> RewardTrace Rat :=
      fun trajectory t => (trajectory t).2
    let action := selectedPolicySuccessorTelescopingGeneratedUCBAction
      hK sigma2 delta defaultAction reward
    mu
        (ConditionalExpectationReward.successorArmEmpiricalMeanFintypeTelescopingAllTimeBadEvent
          action reward armMean sigma2 delta) <=
      ENNReal.ofReal delta := by
  simpa [selectedPolicySuccessorTelescopingActionRewardTrajMeasure] using
    (actionRewardHistoryStepKernelFamily_selectedPolicySuccessorTelescoping_allTimeConfidence
      hK mu0 rewardKernel context mean varianceProxy defaultAction armMean
      sigma2 delta hcontext hmean law hvariance harmMean hsigma2 hdelta)

/-- Canonical finite-horizon pull-count tail for the single scheduled policy
and the same trajectory measure used by the all-time confidence theorem. -/
theorem measure_selectedPolicySuccessorTelescoping_pullCount_gt_threshold_le_trajMeasure
    {Context : Type} {K : Nat} [MeasurableSpace Context]
    (hK : 0 < K)
    (mu0 : Measure (Prod (Fin K) Rat)) [IsProbabilityMeasure mu0]
    (rewardKernel : RewardKernel.MarkovRewardKernel (Prod Context (Fin K)) Rat)
    (context : (n : Nat) -> ((j : Finset.Iic n) -> Rat) -> Context)
    (mean : Context -> Fin K -> Rat)
    (varianceProxy : Context -> Fin K -> NNReal)
    (defaultAction best chosen : Fin K) (armMean : Fin K -> Rat)
    (sigma2 : NNReal) (delta : Real) (T : Nat)
    (hcontext : forall n : Nat, Measurable (context n))
    (hmean : Measurable (fun pair : Prod Context (Fin K) =>
      mean pair.1 pair.2))
    (law : RewardKernel.CenteredRewardKernelLaw rewardKernel mean varianceProxy)
    (hvariance : forall i : Nat,
      forall history : ((j : Finset.Iic i) -> Rat),
        varianceProxy (context i history)
            ((selectedPolicySuccessorTelescopingHistoryPolicy
              hK sigma2 delta defaultAction i).action
              (selectedPolicySuccessorTelescopingHistoryState
                hK sigma2 delta defaultAction i history)) <= sigma2)
    (harmMean : forall i : Nat,
      forall history : ((j : Finset.Iic i) -> Rat),
        forall arm : Fin K,
          mean (context i history) arm = armMean arm)
    (hsigma2 : 0 < (((sigma2 : NNReal) : Real)))
    (hdelta : 0 < delta)
    (hgap : 0 < meanGap (fun arm => (armMean arm : Real)) best chosen) :
    let mu := selectedPolicySuccessorTelescopingActionRewardTrajMeasure
      hK mu0 rewardKernel context hcontext sigma2 delta defaultAction
    let reward : (Nat -> Prod (Fin K) Rat) -> RewardTrace Rat :=
      fun trajectory t => (trajectory t).2
    let action := selectedPolicySuccessorTelescopingGeneratedUCBAction
      hK sigma2 delta defaultAction reward
    mu {trajectory |
        selectedPolicySuccessorTelescopingPullThreshold
            K sigma2 T delta
              (meanGap (fun arm => (armMean arm : Real)) best chosen) <
          ConditionalExpectationReward.successorArmPullCount
            (action trajectory) chosen (T + 1)} <=
      ENNReal.ofReal delta := by
  let mu := selectedPolicySuccessorTelescopingActionRewardTrajMeasure
    hK mu0 rewardKernel context hcontext sigma2 delta defaultAction
  let reward : (Nat -> Prod (Fin K) Rat) -> RewardTrace Rat :=
    fun trajectory t => (trajectory t).2
  have hconfidence :=
    measure_selectedPolicySuccessorTelescoping_allTimeBadEvent_le_trajMeasure
      hK mu0 rewardKernel context mean varianceProxy defaultAction armMean
      sigma2 delta hcontext hmean law hvariance harmMean hsigma2 hdelta
  simpa [mu, reward] using
    (measure_selectedPolicySuccessorTelescoping_pullCount_gt_threshold_le_of_allTimeConfidence
      hK mu reward armMean sigma2 delta hdelta defaultAction best chosen T
      hgap (by simpa [mu, reward] using hconfidence))

/-- Canonical finite-time expected pseudo-regret of the single scheduled
policy.  The same all-time event supplies every horizon, and the failure term
is explicitly retained as `T * delta`. -/
theorem lintegral_ofReal_pseudoRegret_selectedPolicySuccessorTelescoping_le_trajMeasure
    {Context : Type} {K : Nat} [MeasurableSpace Context]
    (model : FiniteBanditModel K)
    (mu0 : Measure (Prod (Fin K) Rat)) [IsProbabilityMeasure mu0]
    (rewardKernel : RewardKernel.MarkovRewardKernel (Prod Context (Fin K)) Rat)
    (context : (n : Nat) -> ((j : Finset.Iic n) -> Rat) -> Context)
    (mean : Context -> Fin K -> Rat)
    (varianceProxy : Context -> Fin K -> NNReal)
    (defaultAction : Fin K) (sigma2 : NNReal) (delta : Real) (T : Nat)
    (hcontext : forall n : Nat, Measurable (context n))
    (hmean : Measurable (fun pair : Prod Context (Fin K) =>
      mean pair.1 pair.2))
    (law : RewardKernel.CenteredRewardKernelLaw rewardKernel mean varianceProxy)
    (hvariance : forall i : Nat,
      forall history : ((j : Finset.Iic i) -> Rat),
        varianceProxy (context i history)
            ((selectedPolicySuccessorTelescopingHistoryPolicy
              model.hK sigma2 delta defaultAction i).action
              (selectedPolicySuccessorTelescopingHistoryState
                model.hK sigma2 delta defaultAction i history)) <= sigma2)
    (harmMean : forall i : Nat,
      forall history : ((j : Finset.Iic i) -> Rat),
        forall arm : Fin K,
          mean (context i history) arm = model.mean arm)
    (hsigma2 : 0 < (((sigma2 : NNReal) : Real)))
    (hdelta : 0 < delta) :
    let mu := selectedPolicySuccessorTelescopingActionRewardTrajMeasure
      model.hK mu0 rewardKernel context hcontext sigma2 delta defaultAction
    let reward : (Nat -> Prod (Fin K) Rat) -> RewardTrace Rat :=
      fun trajectory t => (trajectory t).2
    let action := selectedPolicySuccessorTelescopingGeneratedUCBRegretAction
      model.hK sigma2 delta defaultAction reward
    ∫⁻ trajectory,
        ENNReal.ofReal
          (((pseudoRegret model (action trajectory) T : Rat) : Real)) ∂mu <=
      (Finset.univ : Finset (Fin K)).sum (fun arm =>
        ENNReal.ofReal (((model.gap arm : Rat) : Real)) *
          ((selectedPolicySuccessorTelescopingPullThreshold
              K sigma2 T delta (((model.gap arm : Rat) : Real)) : Nat) :
                ENNReal) +
            ENNReal.ofReal (((model.gap arm : Rat) : Real)) *
              ((T : ENNReal) * ENNReal.ofReal delta)) := by
  let mu := selectedPolicySuccessorTelescopingActionRewardTrajMeasure
    model.hK mu0 rewardKernel context hcontext sigma2 delta defaultAction
  letI : IsProbabilityMeasure mu := by
    dsimp [mu, selectedPolicySuccessorTelescopingActionRewardTrajMeasure]
    infer_instance
  let reward : (Nat -> Prod (Fin K) Rat) -> RewardTrace Rat :=
    fun trajectory t => (trajectory t).2
  have hreward : forall t : Nat,
      Measurable (fun trajectory : Nat -> Prod (Fin K) Rat =>
        reward trajectory t) := by
    intro t
    exact measurable_snd.comp (measurable_pi_apply t)
  have hconfidence :=
    measure_selectedPolicySuccessorTelescoping_allTimeBadEvent_le_trajMeasure
      model.hK mu0 rewardKernel context mean varianceProxy defaultAction
      model.mean sigma2 delta hcontext hmean law hvariance harmMean
      hsigma2 hdelta
  simpa [mu, reward] using
    (lintegral_ofReal_pseudoRegret_selectedPolicySuccessorTelescoping_le_of_allTimeConfidence
      mu model reward hreward sigma2 delta hdelta defaultAction T
      (by simpa [mu, reward] using hconfidence))

end UCB
end BanditRLProof
