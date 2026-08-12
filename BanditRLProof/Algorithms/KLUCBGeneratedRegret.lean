import BanditRLProof.Algorithms.KLUCBBernoulli
import BanditRLProof.Algorithms.UCBFixedPolicyTelescopingAnytimeRegret

/-!
# Generated finite-arm KL-UCB

This module defines one horizon-free KL-UCB policy on the canonical generated
Rat action/reward trajectory.  The confidence budget is calibrated from the
accepted telescoping empirical-mean radius and an explicit common interior
margin.  The selected score is nevertheless the supremum of the genuine
Bernoulli-KL confidence set; it is not the ordinary additive UCB score.
-/

namespace BanditRLProof
namespace KLUCB

open MeasureTheory

noncomputable section

/-- KL exploration budget on a realized generated prefix.  The margin is a
known regularity contract, while the empirical count and radius are computed
from the actual action/reward trace. -/
def generatedBudgetAt
    {Omega : Type} {K : Nat}
    (action : Omega -> ActionTrace (Fin K)) (sigma2 : NNReal)
    (delta margin : Real) (omega : Omega) (t : Nat) (arm : Fin K) : Real :=
  let count := ConditionalExpectationReward.successorArmPullCount
    (action omega) arm (t + 1)
  let radius := UCB.selectedPolicySuccessorTelescopingRadiusAt
    action sigma2 delta omega t arm
  (count : Real) * radius ^ 2 / (margin * (1 - margin))

theorem generatedBudgetAt_nonneg
    {Omega : Type} {K : Nat}
    (action : Omega -> ActionTrace (Fin K)) (sigma2 : NNReal)
    (delta margin : Real) (hmargin0 : 0 < margin) (hmargin1 : margin < 1)
    (omega : Omega) (t : Nat) (arm : Fin K) :
    0 <= generatedBudgetAt action sigma2 delta margin omega t arm := by
  unfold generatedBudgetAt
  apply div_nonneg
  · exact mul_nonneg (Nat.cast_nonneg _) (sq_nonneg _)
  · exact mul_nonneg hmargin0.le (sub_nonneg.mpr hmargin1.le)

/-- Genuine Bernoulli-KL index on one generated prefix. -/
def generatedIndexAt
    {Omega : Type} {K : Nat}
    (action : Omega -> ActionTrace (Fin K))
    (reward : Omega -> RewardTrace Rat)
    (sigma2 : NNReal) (delta margin : Real)
    (omega : Omega) (t : Nat) (arm : Fin K) : Real :=
  index
    (UCB.selectedPolicySuccessorEmpiricalMeanAt action reward omega t arm)
    (ConditionalExpectationReward.successorArmPullCount
      (action omega) arm (t + 1))
    (generatedBudgetAt action sigma2 delta margin omega t arm)

/-- KL score reconstructed from a finite generated pair history. -/
def historyIndex
    {K : Nat} (sigma2 : NNReal) (delta margin : Real)
    (defaultAction : Fin K) (t : Nat)
    (history : History.FinitePairHistory (Fin K) Rat t)
    (arm : Fin K) : Real :=
  let action := UCB.completeFinitePairHistoryAction
    t history defaultAction (0 : Rat)
  let reward := UCB.completeFinitePairHistoryReward
    t history defaultAction (0 : Rat)
  let count := ConditionalExpectationReward.successorArmPullCount
    action arm (t + 1)
  let empiricalMean := ConditionalExpectationReward.successorArmEmpiricalMean
    action reward arm (t + 1)
  let radius :=
    ConditionalExpectationReward.successorArmEmpiricalMeanPeelingRadius
      sigma2 count (t + 1)
        (Concentration.telescopingConfidenceShare delta t / (K : Real))
  index empiricalMean count
    ((count : Real) * radius ^ 2 / (margin * (1 - margin)))

theorem measurable_historyIndex
    {K : Nat} (sigma2 : NNReal) (delta margin : Real)
    (defaultAction : Fin K) (t : Nat) (arm : Fin K) :
    Measurable (fun history : History.FinitePairHistory (Fin K) Rat t =>
      historyIndex sigma2 delta margin defaultAction t history arm) := by
  exact measurable_of_countable _

/-- Round-robin initialization followed by KL-index maximization. -/
def historyNextArm
    {K : Nat} (hK : 0 < K) (sigma2 : NNReal) (delta margin : Real)
    (defaultAction : Fin K) (t : Nat)
    (history : History.FinitePairHistory (Fin K) Rat t) : Fin K :=
  if t < K then UCB.initializationArm hK t
  else UCB.scoreArgmax hK
    (historyIndex sigma2 delta margin defaultAction t history)

theorem historyIndex_le_nextArm_of_K_le
    {K : Nat} (hK : 0 < K) (sigma2 : NNReal) (delta margin : Real)
    (defaultAction : Fin K) (t : Nat)
    (history : History.FinitePairHistory (Fin K) Rat t)
    (ht : K <= t) (arm : Fin K) :
    historyIndex sigma2 delta margin defaultAction t history arm <=
      historyIndex sigma2 delta margin defaultAction t history
        (historyNextArm hK sigma2 delta margin defaultAction t history) := by
  rw [historyNextArm, if_neg (not_lt_of_ge ht)]
  exact UCB.scoreArgmax_spec hK
    (historyIndex sigma2 delta margin defaultAction t history) arm

/-- Pair-history reconstruction for the KL-UCB policy. -/
def pairHistory
    {K : Nat} (hK : 0 < K) (sigma2 : NNReal) (delta margin : Real)
    (defaultAction : Fin K) :
    (n : Nat) -> History.FiniteRewardHistory Rat n ->
      History.FinitePairHistory (Fin K) Rat n
  | 0, rewardHistory => fun i => (defaultAction, rewardHistory i)
  | n + 1, rewardHistory =>
      let previousRewardHistory : History.FiniteRewardHistory Rat n :=
        fun i => rewardHistory
          ⟨i.1, Finset.mem_Iic.mpr
            ((Finset.mem_Iic.mp i.2).trans (Nat.le_succ n))⟩
      let previousHistory := pairHistory hK sigma2 delta margin
        defaultAction n previousRewardHistory
      let nextAction := historyNextArm hK sigma2 delta margin
        defaultAction n previousHistory
      History.extendPairHistorySucc previousHistory
        (nextAction, rewardHistory ⟨n + 1, Finset.mem_Iic.mpr le_rfl⟩)

def historyState
    {K : Nat} (hK : 0 < K) (sigma2 : NNReal) (delta margin : Real)
    (defaultAction : Fin K)
    (n : Nat) (rewardHistory : History.FiniteRewardHistory Rat n) :
    UCB.SelectedPolicySuccessorFiniteHistoryState K :=
  ⟨n, pairHistory hK sigma2 delta margin defaultAction n rewardHistory⟩

theorem measurable_historyState
    {K : Nat} (hK : 0 < K) (sigma2 : NNReal) (delta margin : Real)
    (defaultAction : Fin K) (n : Nat) :
    Measurable (historyState hK sigma2 delta margin defaultAction n) := by
  exact measurable_of_countable _

/-- The measurable KL-UCB policy.  Its declaration has no terminal horizon. -/
def historyPolicy
    {K : Nat} (hK : 0 < K) (sigma2 : NNReal) (delta margin : Real)
    (defaultAction : Fin K) (_t : Nat) :
    Policy.MeasurablePolicy
      (UCB.SelectedPolicySuccessorFiniteHistoryState K) (Fin K) where
  action := fun state => historyNextArm hK sigma2 delta margin
    defaultAction state.time state.history
  measurable_action := Measurable.of_comap_le le_top

/-- Canonical generated action trace of the KL-UCB policy. -/
def generatedAction
    {Omega : Type} {K : Nat} (hK : 0 < K)
    (sigma2 : NNReal) (delta margin : Real) (defaultAction : Fin K)
    (reward : Omega -> RewardTrace Rat) : Omega -> ActionTrace (Fin K) :=
  ConditionalExpectationReward.generatedActionFromRewardHistory
    (historyPolicy hK sigma2 delta margin defaultAction)
    (historyState hK sigma2 delta margin defaultAction)
    defaultAction reward

@[simp]
theorem generatedAction_succ
    {Omega : Type} {K : Nat} (hK : 0 < K)
    (sigma2 : NNReal) (delta margin : Real) (defaultAction : Fin K)
    (reward : Omega -> RewardTrace Rat) (omega : Omega) (t : Nat) :
    generatedAction hK sigma2 delta margin defaultAction reward omega (t + 1) =
      historyNextArm hK sigma2 delta margin defaultAction t
        (pairHistory hK sigma2 delta margin defaultAction t
          (History.finiteRewardHistoryOfTrace (reward omega) t)) := by
  simp [generatedAction,
    ConditionalExpectationReward.generatedActionFromRewardHistory,
    Policy.generatedActionTraceSucc, historyPolicy, historyState]

theorem pairHistory_eq_finitePairHistoryOfTrace
    {Omega : Type} {K : Nat} (hK : 0 < K)
    (sigma2 : NNReal) (delta margin : Real) (defaultAction : Fin K)
    (reward : Omega -> RewardTrace Rat) (omega : Omega) (n : Nat) :
    pairHistory hK sigma2 delta margin defaultAction n
        (History.finiteRewardHistoryOfTrace (reward omega) n) =
      History.finitePairHistoryOfTrace
        (generatedAction hK sigma2 delta margin defaultAction reward omega)
        (reward omega) n := by
  induction n with
  | zero =>
      funext i
      have hi : i.1 = 0 := Nat.eq_zero_of_le_zero (Finset.mem_Iic.mp i.2)
      have hiSubtype : i = ⟨0, Finset.mem_Iic.mpr le_rfl⟩ := Subtype.ext hi
      subst i
      simp [pairHistory, generatedAction,
        ConditionalExpectationReward.generatedActionFromRewardHistory,
        Policy.generatedActionTraceSucc]
  | succ n ih =>
      let previousRewardHistory : History.FiniteRewardHistory Rat n :=
        fun i => History.finiteRewardHistoryOfTrace (reward omega) (n + 1)
          ⟨i.1, Finset.mem_Iic.mpr
            ((Finset.mem_Iic.mp i.2).trans (Nat.le_succ n))⟩
      have hprevious : previousRewardHistory =
          History.finiteRewardHistoryOfTrace (reward omega) n := by rfl
      rw [pairHistory]
      change History.extendPairHistorySucc
          (pairHistory hK sigma2 delta margin defaultAction n previousRewardHistory)
          _ = _
      rw [hprevious, ih, History.finitePairHistoryOfTrace_succ]
      apply congrArg
        (History.extendPairHistorySucc
          (History.finitePairHistoryOfTrace
            (generatedAction hK sigma2 delta margin defaultAction reward omega)
            (reward omega) n))
      apply Prod.ext
      · exact (generatedAction_succ hK sigma2 delta margin defaultAction
          reward omega n).symm
      · rfl

/-- The finite-history score, count, mean, and budget are definitionally the
ones on the same generated trajectory. -/
theorem historyIndex_finitePairHistoryOfTrace
    {Omega : Type} {K : Nat}
    (action : Omega -> ActionTrace (Fin K))
    (reward : Omega -> RewardTrace Rat)
    (sigma2 : NNReal) (delta margin : Real) (defaultAction : Fin K)
    (omega : Omega) (t : Nat) (arm : Fin K) :
    historyIndex sigma2 delta margin defaultAction t
        (History.finitePairHistoryOfTrace (action omega) (reward omega) t) arm =
      generatedIndexAt action reward sigma2 delta margin omega t arm := by
  unfold historyIndex generatedIndexAt generatedBudgetAt
    UCB.selectedPolicySuccessorEmpiricalMeanAt
    UCB.selectedPolicySuccessorTelescopingRadiusAt
    ConditionalExpectationReward.successorArmEmpiricalMean
  simp only
  rw [UCB.successorArmRewardSum_completeFinitePairHistory,
    UCB.successorArmPullCount_completeFinitePairHistory]

/-- Selected KL index maximality on the actual generated action/reward trace. -/
theorem generatedIndexAt_le_selected_of_K_le
    {Omega : Type} {K : Nat} (hK : 0 < K)
    (sigma2 : NNReal) (delta margin : Real) (defaultAction : Fin K)
    (reward : Omega -> RewardTrace Rat) (omega : Omega)
    (t : Nat) (ht : K <= t) (arm : Fin K) :
    let action := generatedAction hK sigma2 delta margin defaultAction reward
    generatedIndexAt action reward sigma2 delta margin omega t arm <=
      generatedIndexAt action reward sigma2 delta margin omega t
        (action omega (t + 1)) := by
  let action := generatedAction hK sigma2 delta margin defaultAction reward
  let history := History.finitePairHistoryOfTrace
    (action omega) (reward omega) t
  have hhistory :
      pairHistory hK sigma2 delta margin defaultAction t
          (History.finiteRewardHistoryOfTrace (reward omega) t) = history :=
    pairHistory_eq_finitePairHistoryOfTrace hK sigma2 delta margin
      defaultAction reward omega t
  have hselected : action omega (t + 1) =
      historyNextArm hK sigma2 delta margin defaultAction t history := by
    simpa [action, history, hhistory] using
      (generatedAction_succ hK sigma2 delta margin defaultAction reward omega t)
  have hmax := historyIndex_le_nextArm_of_K_le hK sigma2 delta margin
    defaultAction t history ht arm
  rw [← hselected] at hmax
  simpa [action, history] using
    (show generatedIndexAt action reward sigma2 delta margin omega t arm <=
        generatedIndexAt action reward sigma2 delta margin omega t
          (action omega (t + 1)) by
      simpa only [
        ← historyIndex_finitePairHistoryOfTrace action reward sigma2 delta
          margin defaultAction omega t arm,
        ← historyIndex_finitePairHistoryOfTrace action reward sigma2 delta
          margin defaultAction omega t (action omega (t + 1))] using hmax)

theorem generatedAction_succ_eq_initializationArm_of_lt
    {Omega : Type} {K : Nat} (hK : 0 < K)
    (sigma2 : NNReal) (delta margin : Real) (defaultAction : Fin K)
    (reward : Omega -> RewardTrace Rat) (omega : Omega)
    (t : Nat) (ht : t < K) :
    generatedAction hK sigma2 delta margin defaultAction reward omega (t + 1) =
      UCB.initializationArm hK t := by
  simp [historyNextArm, ht]

theorem successorArmPullCount_generatedAction_K_add_one_eq_one
    {Omega : Type} {K : Nat} (hK : 0 < K)
    (sigma2 : NNReal) (delta margin : Real) (defaultAction : Fin K)
    (reward : Omega -> RewardTrace Rat) (omega : Omega) (arm : Fin K) :
    ConditionalExpectationReward.successorArmPullCount
        (generatedAction hK sigma2 delta margin defaultAction reward omega)
        arm (K + 1) = 1 := by
  let spec : ETC.Spec K := { hK := hK, explorationPulls := 1 }
  let action := generatedAction hK sigma2 delta margin defaultAction reward omega
  have haction : forall t, t < K ->
      action (t + 1) = ETC.exploreArm spec t := by
    intro t ht
    exact generatedAction_succ_eq_initializationArm_of_lt hK sigma2 delta
      margin defaultAction reward omega t ht
  unfold ConditionalExpectationReward.successorArmPullCount
  simp only [Nat.add_sub_cancel]
  have hcount : pullCount (fun i => action (i + 1)) arm K =
      pullCount (ETC.exploreArm spec) arm K := by
    apply pullCount_eq_of_forall_lt
    exact haction
  rw [hcount]
  exact ETC.pullCount_exploreArm_K_eq_one spec arm

theorem successorArmPullCount_generatedAction_pos_of_K_le
    {Omega : Type} {K : Nat} (hK : 0 < K)
    (sigma2 : NNReal) (delta margin : Real) (defaultAction : Fin K)
    (reward : Omega -> RewardTrace Rat) (omega : Omega)
    (arm : Fin K) (t : Nat) (ht : K <= t) :
    0 < ConditionalExpectationReward.successorArmPullCount
      (generatedAction hK sigma2 delta margin defaultAction reward omega)
      arm (t + 1) := by
  let action := generatedAction hK sigma2 delta margin defaultAction reward omega
  have hmono := pullCount_mono (fun i => action (i + 1)) arm ht
  have hinit := successorArmPullCount_generatedAction_K_add_one_eq_one
    hK sigma2 delta margin defaultAction reward omega arm
  unfold ConditionalExpectationReward.successorArmPullCount at hinit ⊢
  simp only [Nat.add_sub_cancel] at hinit ⊢
  have hinit' : pullCount (fun i => action (i + 1)) arm K = 1 := by
    simpa [action] using hinit
  rw [hinit'] at hmono
  exact lt_of_lt_of_le Nat.zero_lt_one hmono

theorem K_le_of_generatedAction_selected_and_count_pos
    {Omega : Type} {K : Nat} (hK : 0 < K)
    (sigma2 : NNReal) (delta margin : Real) (defaultAction : Fin K)
    (reward : Omega -> RewardTrace Rat) (omega : Omega)
    (arm : Fin K) (t : Nat)
    (hselected : generatedAction hK sigma2 delta margin defaultAction reward
      omega (t + 1) = arm)
    (hcount : 0 < ConditionalExpectationReward.successorArmPullCount
      (generatedAction hK sigma2 delta margin defaultAction reward omega)
      arm (t + 1)) : K <= t := by
  by_contra hnot
  have ht : t < K := Nat.lt_of_not_ge hnot
  let action := generatedAction hK sigma2 delta margin defaultAction reward omega
  have hselected' : (fun i => action (i + 1)) t = arm := by
    simpa [action] using hselected
  have hstep := pullCount_succ_of_eq
    (fun i => action (i + 1)) arm t hselected'
  have hmono := pullCount_mono
    (fun i => action (i + 1)) arm (Nat.succ_le_of_lt ht)
  have hinit := successorArmPullCount_generatedAction_K_add_one_eq_one
    hK sigma2 delta margin defaultAction reward omega arm
  have hinit' : pullCount (fun i => action (i + 1)) arm K = 1 := by
    simpa [action, ConditionalExpectationReward.successorArmPullCount] using hinit
  have hprior : 0 < pullCount (fun i => action (i + 1)) arm t := by
    simpa [action, ConditionalExpectationReward.successorArmPullCount] using hcount
  rw [hstep, hinit'] at hmono
  omega

/-- A bounded empirical-mean deviation on the actual prefix makes the true
interior arm mean feasible for the KL confidence set used by the policy. -/
theorem armMean_mem_confidenceSet_of_abs_lt_radius
    {Omega : Type} {K : Nat}
    (action : Omega -> ActionTrace (Fin K))
    (reward : Omega -> RewardTrace Rat)
    (sigma2 : NNReal) (delta margin : Real)
    (hmargin0 : 0 < margin) (hmarginHalf : margin <= 1 / 2)
    (armMean : Fin K -> Rat) (omega : Omega) (t : Nat) (arm : Fin K)
    (hemp : IsBernoulliParameter
      (UCB.selectedPolicySuccessorEmpiricalMeanAt action reward omega t arm))
    (hmean : (armMean arm : Real) ∈ Set.Icc margin (1 - margin))
    (hdev :
      |UCB.selectedPolicySuccessorEmpiricalMeanAt action reward omega t arm -
          (armMean arm : Real)| <
        UCB.selectedPolicySuccessorTelescopingRadiusAt
          action sigma2 delta omega t arm) :
    (armMean arm : Real) ∈ confidenceSet
      (UCB.selectedPolicySuccessorEmpiricalMeanAt action reward omega t arm)
      (ConditionalExpectationReward.successorArmPullCount
        (action omega) arm (t + 1))
      (generatedBudgetAt action sigma2 delta margin omega t arm) := by
  let empirical :=
    UCB.selectedPolicySuccessorEmpiricalMeanAt action reward omega t arm
  let mean := (armMean arm : Real)
  let count := ConditionalExpectationReward.successorArmPullCount
    (action omega) arm (t + 1)
  let radius := UCB.selectedPolicySuccessorTelescopingRadiusAt
    action sigma2 delta omega t arm
  have hmargin1 : margin < 1 :=
    lt_of_le_of_lt hmarginHalf (by norm_num : (1 / 2 : Real) < 1)
  have hmean0 : 0 < mean := hmargin0.trans_le hmean.1
  have hmean1 : mean < 1 := hmean.2.trans_lt (sub_lt_self 1 hmargin0)
  have hmarginDen : 0 < margin * (1 - margin) :=
    mul_pos hmargin0 (sub_pos.mpr hmargin1)
  have hmeanDen : 0 < mean * (1 - mean) :=
    mul_pos hmean0 (sub_pos.mpr hmean1)
  have hdenLe : margin * (1 - margin) <= mean * (1 - mean) := by
    have hprod := mul_nonneg (sub_nonneg.mpr hmean.1)
      (sub_nonneg.mpr hmean.2)
    nlinarith
  have hradius0 : 0 < radius := lt_of_le_of_lt (abs_nonneg _) hdev
  have hradiusNonneg : 0 <= radius := hradius0.le
  have hsq : (empirical - mean) ^ 2 < radius ^ 2 := by
    rw [sq_lt_sq, abs_of_nonneg hradiusNonneg]
    simpa [empirical, mean, radius] using hdev
  have hdiv : (empirical - mean) ^ 2 / (mean * (1 - mean)) <
      radius ^ 2 / (margin * (1 - margin)) := by
    apply (div_lt_div_iff₀ hmeanDen hmarginDen).2
    calc
      (empirical - mean) ^ 2 * (margin * (1 - margin)) <
          radius ^ 2 * (margin * (1 - margin)) := by gcongr
      _ <= radius ^ 2 * (mean * (1 - mean)) := by gcongr
  apply mem_confidenceSet_of_natCast_mul_core_le hemp hmean0 hmean1
  unfold generatedBudgetAt
  change (count : Real) * bernoulliKLCore empirical mean <=
    (count : Real) * radius ^ 2 / (margin * (1 - margin))
  have hcore := bernoulliKLCore_le_sq_div hemp hmean0 hmean1
  calc
    (count : Real) * bernoulliKLCore empirical mean <=
        (count : Real) * ((empirical - mean) ^ 2 /
          (mean * (1 - mean))) := by gcongr
    _ <= (count : Real) * (radius ^ 2 /
          (margin * (1 - margin))) := by
        gcongr
    _ = (count : Real) * radius ^ 2 /
          (margin * (1 - margin)) := by ring

theorem armMean_le_generatedIndexAt_of_abs_lt_radius
    {Omega : Type} {K : Nat}
    (action : Omega -> ActionTrace (Fin K))
    (reward : Omega -> RewardTrace Rat)
    (sigma2 : NNReal) (delta margin : Real)
    (hmargin0 : 0 < margin) (hmarginHalf : margin <= 1 / 2)
    (armMean : Fin K -> Rat) (omega : Omega) (t : Nat) (arm : Fin K)
    (hemp : IsBernoulliParameter
      (UCB.selectedPolicySuccessorEmpiricalMeanAt action reward omega t arm))
    (hmean : (armMean arm : Real) ∈ Set.Icc margin (1 - margin))
    (hdev :
      |UCB.selectedPolicySuccessorEmpiricalMeanAt action reward omega t arm -
          (armMean arm : Real)| <
        UCB.selectedPolicySuccessorTelescopingRadiusAt
          action sigma2 delta omega t arm) :
    (armMean arm : Real) <=
      generatedIndexAt action reward sigma2 delta margin omega t arm := by
  exact le_index_of_mem_confidenceSet
    (armMean_mem_confidenceSet_of_abs_lt_radius action reward sigma2 delta margin
      hmargin0 hmarginHalf armMean omega t arm hemp hmean hdev)

set_option maxHeartbeats 800000 in
/-- On the common generated all-time good event, selection of a positive-gap
arm forces its realized KL calibration radius to remain large.  This is the
single-arm, single-round KL pull-threshold leaf. -/
theorem margin_mul_gap_div_eight_le_radius_of_selected_of_not_badEvent
    {Omega : Type} {K : Nat} (hK : 0 < K)
    (reward : Omega -> RewardTrace Rat) (armMean : Fin K -> Rat)
    (sigma2 : NNReal) (delta margin : Real)
    (hmargin0 : 0 < margin) (hmarginHalf : margin <= 1 / 2)
    (hmean : forall arm : Fin K,
      (armMean arm : Real) ∈ Set.Icc margin (1 - margin))
    (defaultAction best : Fin K) (omega : Omega) (t : Nat) (ht : K <= t)
    (hemp : forall arm : Fin K, IsBernoulliParameter
      (UCB.selectedPolicySuccessorEmpiricalMeanAt
        (generatedAction hK sigma2 delta margin defaultAction reward)
        reward omega t arm))
    (hbest : forall arm : Fin K, (armMean arm : Real) <= (armMean best : Real))
    (hgap : 0 < UCB.meanGap (fun arm => (armMean arm : Real)) best
      (generatedAction hK sigma2 delta margin defaultAction reward omega (t + 1)))
    (hgood : omega ∉
      ConditionalExpectationReward.successorArmEmpiricalMeanFintypeTelescopingAllTimeBadEvent
        (generatedAction hK sigma2 delta margin defaultAction reward)
        reward armMean sigma2 delta) :
    margin * UCB.meanGap (fun arm => (armMean arm : Real)) best
        (generatedAction hK sigma2 delta margin defaultAction reward omega (t + 1)) / 8 <=
      UCB.selectedPolicySuccessorTelescopingRadiusAt
        (generatedAction hK sigma2 delta margin defaultAction reward)
        sigma2 delta omega t
        (generatedAction hK sigma2 delta margin defaultAction reward omega (t + 1)) := by
  let action := generatedAction hK sigma2 delta margin defaultAction reward
  let chosen := action omega (t + 1)
  let empirical : Fin K -> Real := fun arm =>
    UCB.selectedPolicySuccessorEmpiricalMeanAt action reward omega t arm
  let radius : Fin K -> Real := fun arm =>
    UCB.selectedPolicySuccessorTelescopingRadiusAt
      action sigma2 delta omega t arm
  let gap := UCB.meanGap (fun arm => (armMean arm : Real)) best chosen
  have hcount (arm : Fin K) :
      0 < ConditionalExpectationReward.successorArmPullCount
        (action omega) arm (t + 1) :=
    successorArmPullCount_generatedAction_pos_of_K_le hK sigma2 delta margin
      defaultAction reward omega arm t ht
  have hpair (arm : Fin K)
      (hdeviation : radius arm <= |empirical arm - (armMean arm : Real)|) :
      omega ∈
        ConditionalExpectationReward.successorArmEmpiricalMeanFintypeTelescopingAllTimeBadEvent
          action reward armMean sigma2 delta := by
    unfold ConditionalExpectationReward.successorArmEmpiricalMeanFintypeTelescopingAllTimeBadEvent
    exact Set.mem_iUnion.mpr ⟨t, Set.mem_iUnion.mpr ⟨arm, by
      simpa [action, empirical, radius,
        UCB.selectedPolicySuccessorEmpiricalMeanAt,
        UCB.selectedPolicySuccessorTelescopingRadiusAt] using
          And.intro (hcount arm) hdeviation⟩⟩
  have hbestAbs : |empirical best - (armMean best : Real)| < radius best := by
    by_contra hnot
    exact hgood (hpair best (le_of_not_gt hnot))
  have hchosenAbs : |empirical chosen - (armMean chosen : Real)| < radius chosen := by
    by_contra hnot
    exact hgood (hpair chosen (le_of_not_gt hnot))
  have hbestOptimistic : (armMean best : Real) <=
      generatedIndexAt action reward sigma2 delta margin omega t best :=
    armMean_le_generatedIndexAt_of_abs_lt_radius action reward sigma2 delta margin
      hmargin0 hmarginHalf armMean omega t best (hemp best) (hmean best)
      (by simpa [empirical, radius] using hbestAbs)
  have hscore : generatedIndexAt action reward sigma2 delta margin omega t best <=
      generatedIndexAt action reward sigma2 delta margin omega t chosen := by
    simpa [action, chosen] using
      (generatedIndexAt_le_selected_of_K_le hK sigma2 delta margin
        defaultAction reward omega t ht best)
  have hchosenIndex : (armMean best : Real) <=
      generatedIndexAt action reward sigma2 delta margin omega t chosen :=
    hbestOptimistic.trans hscore
  have hmargin1 : margin < 1 :=
    lt_of_le_of_lt hmarginHalf (by norm_num : (1 / 2 : Real) < 1)
  have hmarginDen : 0 < margin * (1 - margin) :=
    mul_pos hmargin0 (sub_pos.mpr hmargin1)
  have hgap' : 0 < gap := by simpa [action, chosen, gap] using hgap
  by_contra hnot
  have hrsmall : radius chosen < margin * gap / 8 := by
    simpa [action, chosen, radius, gap] using lt_of_not_ge hnot
  have hradiusNonneg : 0 <= radius chosen :=
    UCB.selectedPolicySuccessorTelescopingRadiusAt_nonneg
      action sigma2 delta omega t chosen
  let level := (armMean best : Real) - gap / 4
  have hlevelLower : margin <= level := by
    have hchosenMean := hmean chosen
    have hgapEq : gap = (armMean best : Real) - (armMean chosen : Real) := rfl
    dsimp [level]
    rw [hgapEq]
    nlinarith [(hmean best).1, hchosenMean.1]
  have hlevelIndex : level <
      generatedIndexAt action reward sigma2 delta margin omega t chosen := by
    dsimp [level]
    exact lt_of_lt_of_le (sub_lt_self _ (div_pos hgap' (by norm_num))) hchosenIndex
  have hbudgetNonneg : 0 <= generatedBudgetAt action sigma2 delta margin omega t chosen :=
    generatedBudgetAt_nonneg action sigma2 delta margin hmargin0 hmargin1
      omega t chosen
  obtain ⟨q, hqmem, hlevelq⟩ := exists_mem_confidenceSet_of_lt_index
    (hemp chosen) hbudgetNonneg hlevelIndex
  have hq0 : 0 < q := lt_of_le_of_lt (hmargin0.le.trans hlevelLower) hlevelq
  have hqle1 : q <= 1 := hqmem.1.2
  by_cases hq1eq : q = 1
  · subst q
    have hempOne : empirical chosen = 1 := by
      by_contra hp1
      have htop := bernoulliKL_eq_top_right_one (hemp chosen) hp1
      have hfinite := hqmem.2
      rw [htop] at hfinite
      have hcountNe :
          ((ConditionalExpectationReward.successorArmPullCount
            (action omega) chosen (t + 1) : Nat) : ENNReal) ≠ 0 := by
        exact_mod_cast (Nat.ne_of_gt (hcount chosen))
      simp [hcountNe] at hfinite
    have hgapLe : gap <= |empirical chosen - (armMean chosen : Real)| := by
      have hchosenLeOne : (armMean chosen : Real) <= 1 :=
        (hmean chosen).2.trans (sub_le_self 1 hmargin0.le)
      have hbestLeOne : (armMean best : Real) <= 1 :=
        (hmean best).2.trans (sub_le_self 1 hmargin0.le)
      rw [hempOne, abs_of_nonneg (sub_nonneg.mpr hchosenLeOne)]
      change (armMean best : Real) - (armMean chosen : Real) <=
        1 - (armMean chosen : Real)
      linarith
    have hgapRadius : gap < radius chosen := hgapLe.trans_lt hchosenAbs
    have hmarginGap : margin * gap / 8 <= gap := by
      have : margin <= 8 := hmarginHalf.trans (by norm_num)
      nlinarith
    exact (not_lt_of_ge hgapRadius.le) (hrsmall.trans_le hmarginGap)
  · have hq1 : q < 1 := lt_of_le_of_ne hqle1 hq1eq
    have hfeasible := natCast_mul_half_sq_sub_le_budget_of_mem
      (hemp chosen) hq0 hq1 hbudgetNonneg hqmem
    let count := ConditionalExpectationReward.successorArmPullCount
      (action omega) chosen (t + 1)
    have hcountReal : 0 < (count : Real) := by
      exact_mod_cast hcount chosen
    have hcancel : (1 / 2 : Real) * (empirical chosen - q) ^ 2 <=
        radius chosen ^ 2 / (margin * (1 - margin)) := by
      unfold generatedBudgetAt at hfeasible
      change (count : Real) * ((1 / 2 : Real) * (empirical chosen - q) ^ 2) <=
        (count : Real) * radius chosen ^ 2 / (margin * (1 - margin)) at hfeasible
      have hreassoc : (count : Real) * radius chosen ^ 2 /
          (margin * (1 - margin)) =
          (count : Real) * (radius chosen ^ 2 /
            (margin * (1 - margin))) := by ring
      rw [hreassoc] at hfeasible
      exact le_of_mul_le_mul_left hfeasible hcountReal
    have hchosenUpper : empirical chosen < (armMean chosen : Real) + radius chosen := by
      have := (abs_lt.mp hchosenAbs).2
      linarith
    have hmarginLeOne : margin <= 1 := hmarginHalf.trans (by norm_num)
    have hrGap : radius chosen < gap / 8 := by
      calc
        radius chosen < margin * gap / 8 := hrsmall
        _ <= gap / 8 := by nlinarith
    have hqEmp : gap / 2 < q - empirical chosen := by
      have hgapEq : gap = (armMean best : Real) - (armMean chosen : Real) := rfl
      dsimp [level] at hlevelq
      rw [hgapEq] at hlevelq
      nlinarith
    have hsquareLower : gap ^ 2 / 4 < (empirical chosen - q) ^ 2 := by
      nlinarith [sq_pos_of_pos hgap', sq_nonneg (q - empirical chosen)]
    have hrSquare : radius chosen ^ 2 < (margin * gap / 8) ^ 2 := by
      nlinarith [hradiusNonneg, hmargin0, hgap']
    have htarget : (margin * gap / 8) ^ 2 <=
        (gap ^ 2 / 8) * (margin * (1 - margin)) := by
      nlinarith [sq_nonneg gap]
    have hdivSmall : radius chosen ^ 2 /
        (margin * (1 - margin)) < gap ^ 2 / 8 := by
      apply (div_lt_iff₀ hmarginDen).2
      exact hrSquare.trans_le htarget
    have : gap ^ 2 / 8 <
        (1 / 2 : Real) * (empirical chosen - q) ^ 2 := by
      nlinarith
    exact (not_lt_of_ge hcancel) (hdivSmall.trans this)

/-- Explicit KL-UCB pull threshold, obtained by inverting the accepted
telescoping radius at the effective gap `margin * gap / 4`. -/
def pullThreshold
    (K : Nat) (sigma2 : NNReal) (T : Nat)
    (delta margin gap : Real) : Nat :=
  UCB.selectedPolicySuccessorTelescopingPullThreshold
    K sigma2 T delta (margin * gap / 4)

theorem pullCount_le_of_not_badEvent
    {Omega : Type} {K : Nat} (hK : 0 < K)
    (reward : Omega -> RewardTrace Rat) (armMean : Fin K -> Rat)
    (sigma2 : NNReal) (delta margin : Real)
    (hdelta : 0 < delta) (hmargin0 : 0 < margin)
    (hmarginHalf : margin <= 1 / 2)
    (hmean : forall arm : Fin K,
      (armMean arm : Real) ∈ Set.Icc margin (1 - margin))
    (defaultAction best chosen : Fin K) (omega : Omega) (T : Nat)
    (hbest : forall arm : Fin K, (armMean arm : Real) <= (armMean best : Real))
    (hemp : forall t : Nat, forall arm : Fin K, IsBernoulliParameter
      (UCB.selectedPolicySuccessorEmpiricalMeanAt
        (generatedAction hK sigma2 delta margin defaultAction reward)
        reward omega t arm))
    (hgap : 0 < UCB.meanGap (fun arm => (armMean arm : Real)) best chosen)
    (hgood : omega ∉
      ConditionalExpectationReward.successorArmEmpiricalMeanFintypeTelescopingAllTimeBadEvent
        (generatedAction hK sigma2 delta margin defaultAction reward)
        reward armMean sigma2 delta) :
    ConditionalExpectationReward.successorArmPullCount
        (generatedAction hK sigma2 delta margin defaultAction reward omega)
        chosen (T + 1) <=
      pullThreshold K sigma2 T delta margin
        (UCB.meanGap (fun arm => (armMean arm : Real)) best chosen) := by
  let action := generatedAction hK sigma2 delta margin defaultAction reward
  let gap := UCB.meanGap (fun arm => (armMean arm : Real)) best chosen
  let effectiveGap := margin * gap / 4
  let B := pullThreshold K sigma2 T delta margin gap
  have heffective : 0 < effectiveGap := by
    dsimp [effectiveGap]
    positivity
  by_contra hnot
  have hfinal : B < pullCount (fun i => action omega (i + 1)) chosen T := by
    simpa [action, B, ConditionalExpectationReward.successorArmPullCount]
      using Nat.lt_of_not_ge hnot
  obtain ⟨t, ht, hselected, hprior⟩ :=
    UCB.exists_selected_with_threshold_le_prior_pullCount
      (fun i => action omega (i + 1)) chosen T B hfinal
  have hBpos : 0 < B := by
    exact (UCB.selectedPolicySuccessorTelescopingPullThreshold_contracts
      K sigma2 T delta effectiveGap heffective).1
  have hpriorPos : 0 < ConditionalExpectationReward.successorArmPullCount
      (action omega) chosen (t + 1) := by
    have : 0 < pullCount (fun i => action omega (i + 1)) chosen t :=
      lt_of_lt_of_le hBpos hprior
    simpa [ConditionalExpectationReward.successorArmPullCount] using this
  have hKle : K <= t :=
    K_le_of_generatedAction_selected_and_count_pos hK sigma2 delta margin
      defaultAction reward omega chosen t (by simpa [action] using hselected)
      hpriorPos
  have hselected' : action omega (t + 1) = chosen := by simpa using hselected
  have hselectedGenerated :
      generatedAction hK sigma2 delta margin defaultAction reward omega (t + 1) =
        chosen := by simpa [action] using hselected
  have hlower :=
    margin_mul_gap_div_eight_le_radius_of_selected_of_not_badEvent
      hK reward armMean sigma2 delta margin hmargin0 hmarginHalf hmean
      defaultAction best omega t hKle (hemp t) hbest
      (by rw [hselectedGenerated]; exact hgap) hgood
  have hupper :=
    UCB.two_mul_successorArmEmpiricalMeanTelescopingPeelingRadius_lt_gap_of_threshold
      hK sigma2 delta effectiveGap hdelta heffective
      (ConditionalExpectationReward.successorArmPullCount
        (action omega) chosen (t + 1)) t T
      (by
        change UCB.selectedPolicySuccessorTelescopingPullThreshold
          K sigma2 T delta effectiveGap <=
            ConditionalExpectationReward.successorArmPullCount
              (action omega) chosen (t + 1)
        simpa [B, pullThreshold, effectiveGap,
          ConditionalExpectationReward.successorArmPullCount] using hprior)
      (Nat.le_of_lt ht)
  rw [hselectedGenerated] at hlower
  have hlower' : effectiveGap <=
      2 * UCB.selectedPolicySuccessorTelescopingRadiusAt
        action sigma2 delta omega t chosen := by
    change margin * gap / 8 <=
      UCB.selectedPolicySuccessorTelescopingRadiusAt
        action sigma2 delta omega t chosen at hlower
    change margin * gap / 4 <=
      2 * UCB.selectedPolicySuccessorTelescopingRadiusAt
        action sigma2 delta omega t chosen
    nlinarith
  have hupper' :
      2 * UCB.selectedPolicySuccessorTelescopingRadiusAt
        action sigma2 delta omega t chosen < effectiveGap := by
    simpa [UCB.selectedPolicySuccessorTelescopingRadiusAt] using hupper
  exact (not_lt_of_ge hlower') hupper'

/-- The accepted all-time telescoping confidence producer instantiated on the
KL-UCB policy.  The theorem explicitly transports the sampled pair action to
the reward-reconstructed action used by `generatedIndexAt`. -/
theorem actionRewardHistoryStepKernelFamily_allTimeConfidence
    {Context : Type} {K : Nat} [MeasurableSpace Context]
    (hK : 0 < K)
    (mu0 : Measure (Prod (Fin K) Rat)) [IsProbabilityMeasure mu0]
    (rewardKernel : RewardKernel.MarkovRewardKernel (Prod Context (Fin K)) Rat)
    (context : (n : Nat) -> ((j : Finset.Iic n) -> Rat) -> Context)
    (mean : Context -> Fin K -> Rat)
    (varianceProxy : Context -> Fin K -> NNReal)
    (defaultAction : Fin K) (armMean : Fin K -> Rat)
    (sigma2 : NNReal) (delta margin : Real)
    (hcontext : forall n : Nat, Measurable (context n))
    (hmean : Measurable (fun pair : Prod Context (Fin K) => mean pair.1 pair.2))
    (law : RewardKernel.CenteredRewardKernelLaw rewardKernel mean varianceProxy)
    (hvariance : forall i : Nat,
      forall history : ((j : Finset.Iic i) -> Rat),
        varianceProxy (context i history)
            ((historyPolicy hK sigma2 delta margin defaultAction i).action
              (historyState hK sigma2 delta margin defaultAction i history)) <= sigma2)
    (harmMean : forall i : Nat,
      forall history : ((j : Finset.Iic i) -> Rat),
        forall arm : Fin K, mean (context i history) arm = armMean arm)
    (hsigma2 : 0 < (((sigma2 : NNReal) : Real)))
    (hdelta : 0 < delta) :
    let policy := historyPolicy hK sigma2 delta margin defaultAction
    let state := historyState hK sigma2 delta margin defaultAction
    let pairContext :
        (i : Nat) -> ((j : Finset.Iic i) -> Prod (Fin K) Rat) -> Context :=
      fun i history => context i (History.pairHistoryRewardProjection history)
    let pairState :
        (i : Nat) -> ((j : Finset.Iic i) -> Prod (Fin K) Rat) ->
          UCB.SelectedPolicySuccessorFiniteHistoryState K :=
      fun i history => state i (History.pairHistoryRewardProjection history)
    let hpairContext : forall i : Nat, Measurable (pairContext i) := fun i =>
      (hcontext i).comp
        (History.measurable_pairHistoryRewardProjection
          (Action := Fin K) (Reward := Rat) i)
    let hpairState : forall i : Nat, Measurable (pairState i) := fun i =>
      (measurable_historyState hK sigma2 delta margin defaultAction i).comp
        (History.measurable_pairHistoryRewardProjection
          (Action := Fin K) (Reward := Rat) i)
    let stepKernel := RewardKernel.actionRewardHistoryStepKernelFamily
      rewardKernel policy pairContext pairState hpairContext hpairState
    let mu := ProbabilityTheory.Kernel.trajMeasure
      (X := fun _ : Nat => Prod (Fin K) Rat) mu0 stepKernel
    let reward : (Nat -> Prod (Fin K) Rat) -> RewardTrace Rat :=
      fun trajectory t => (trajectory t).2
    let generated := generatedAction hK sigma2 delta margin defaultAction reward
    mu
        (ConditionalExpectationReward.successorArmEmpiricalMeanFintypeTelescopingAllTimeBadEvent
          generated reward armMean sigma2 delta) <=
      ENNReal.ofReal delta := by
  classical
  letI : Nonempty (Fin K) := ⟨Fin.mk 0 hK⟩
  let policy := historyPolicy hK sigma2 delta margin defaultAction
  let state := historyState hK sigma2 delta margin defaultAction
  let pairContext :
      (i : Nat) -> ((j : Finset.Iic i) -> Prod (Fin K) Rat) -> Context :=
    fun i history => context i (History.pairHistoryRewardProjection history)
  let pairState :
      (i : Nat) -> ((j : Finset.Iic i) -> Prod (Fin K) Rat) ->
        UCB.SelectedPolicySuccessorFiniteHistoryState K :=
    fun i history => state i (History.pairHistoryRewardProjection history)
  let hpairContext : forall i : Nat, Measurable (pairContext i) := fun i =>
    (hcontext i).comp
      (History.measurable_pairHistoryRewardProjection
        (Action := Fin K) (Reward := Rat) i)
  let hpairState : forall i : Nat, Measurable (pairState i) := fun i =>
    (measurable_historyState hK sigma2 delta margin defaultAction i).comp
      (History.measurable_pairHistoryRewardProjection
        (Action := Fin K) (Reward := Rat) i)
  let stepKernel := RewardKernel.actionRewardHistoryStepKernelFamily
    rewardKernel policy pairContext pairState hpairContext hpairState
  let mu := ProbabilityTheory.Kernel.trajMeasure
    (X := fun _ : Nat => Prod (Fin K) Rat) mu0 stepKernel
  let sampledAction : (Nat -> Prod (Fin K) Rat) -> ActionTrace (Fin K) :=
    fun trajectory t => (trajectory t).1
  let reward : (Nat -> Prod (Fin K) Rat) -> RewardTrace Rat :=
    fun trajectory t => (trajectory t).2
  let generated := generatedAction hK sigma2 delta margin defaultAction reward
  let sampledBad :=
    ConditionalExpectationReward.successorArmEmpiricalMeanFintypeTelescopingAllTimeBadEvent
      sampledAction reward armMean sigma2 delta
  let generatedBad :=
    ConditionalExpectationReward.successorArmEmpiricalMeanFintypeTelescopingAllTimeBadEvent
      generated reward armMean sigma2 delta
  have htail :=
    ConditionalExpectationReward.actionRewardHistoryStepKernelFamily_successorArmEmpiricalMean_simultaneous_fintype_telescopingAllTime_abs_tail_ennreal_delta_trajMeasure
      (mu0 := mu0) (rewardKernel := rewardKernel) (policy := policy)
      (context := context) (state := state) (hcontext := hcontext)
      (hstate := measurable_historyState hK sigma2 delta margin defaultAction)
      (mean := mean) (varianceProxy := varianceProxy) (law := law)
      (hmean := hmean) (armMean := armMean) (sigma2 := sigma2)
      (hvariance := hvariance) (harmMean := harmMean) hsigma2 delta hdelta
  have htail' : mu sampledBad <= ENNReal.ofReal delta := by
    simpa [policy, state, pairContext, pairState, hpairContext, hpairState,
      stepKernel, mu, sampledAction, reward, sampledBad] using htail
  have hactionEq : forall i : Nat,
      Filter.EventuallyEq (ae mu)
        (fun trajectory : Nat -> Prod (Fin K) Rat => sampledAction trajectory (i + 1))
        (fun trajectory : Nat -> Prod (Fin K) Rat => generated trajectory (i + 1)) := by
    intro i
    have hcanonical :=
      ConditionalExpectationReward.actionRewardHistoryStepKernelFamily_action_succ_ae_eq_policy_trajMeasure
        mu0 rewardKernel policy pairContext pairState hpairContext hpairState i
    simpa [mu, stepKernel, sampledAction, generated, generatedAction,
      ConditionalExpectationReward.generatedActionFromRewardHistory,
      Policy.generatedActionTraceSucc, policy, state, pairState, reward,
      History.pairHistoryRewardProjection, History.finiteRewardHistoryOfTrace,
      Preorder.frestrictLe_apply] using hcanonical
  have hactionAll : ∀ᵐ trajectory ∂mu, forall i : Nat,
      sampledAction trajectory (i + 1) = generated trajectory (i + 1) :=
    ae_all_iff.2 hactionEq
  have hgeneratedBad_to_sampledBad : ∀ᵐ trajectory ∂mu,
      trajectory ∈ generatedBad -> trajectory ∈ sampledBad := by
    filter_upwards [hactionAll] with trajectory htrajectory
    intro hbad
    have hshift : (fun i => sampledAction trajectory (i + 1)) =
        (fun i => generated trajectory (i + 1)) := by
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
    stepKernel, mu, reward, generated, generatedBad] using hresult

/-- Arms-by-times KL-confidence failure event on the exact generated trace. -/
def generatedKLAllTimeBadEvent
    {Omega : Type} {K : Nat}
    (action : Omega -> ActionTrace (Fin K))
    (reward : Omega -> RewardTrace Rat) (armMean : Fin K -> Rat)
    (sigma2 : NNReal) (delta margin : Real) : Set Omega :=
  ⋃ t : Nat, ⋃ arm : Fin K,
    {omega | 0 < ConditionalExpectationReward.successorArmPullCount
        (action omega) arm (t + 1) ∧
      ENNReal.ofReal (generatedBudgetAt action sigma2 delta margin omega t arm) <
        (ConditionalExpectationReward.successorArmPullCount
          (action omega) arm (t + 1) : ENNReal) *
          bernoulliKL
            (UCB.selectedPolicySuccessorEmpiricalMeanAt
              action reward omega t arm)
            (armMean arm : Real)}

theorem generatedKLAllTimeBadEvent_subset_absBadEvent
    {Omega : Type} {K : Nat}
    (action : Omega -> ActionTrace (Fin K))
    (reward : Omega -> RewardTrace Rat) (armMean : Fin K -> Rat)
    (sigma2 : NNReal) (delta margin : Real)
    (hmargin0 : 0 < margin) (hmarginHalf : margin <= 1 / 2)
    (hmean : forall arm : Fin K,
      (armMean arm : Real) ∈ Set.Icc margin (1 - margin))
    (hemp : forall omega t arm, IsBernoulliParameter
      (UCB.selectedPolicySuccessorEmpiricalMeanAt action reward omega t arm)) :
    generatedKLAllTimeBadEvent action reward armMean sigma2 delta margin ⊆
      ConditionalExpectationReward.successorArmEmpiricalMeanFintypeTelescopingAllTimeBadEvent
        action reward armMean sigma2 delta := by
  intro omega hkl
  unfold generatedKLAllTimeBadEvent at hkl
  rcases Set.mem_iUnion.mp hkl with ⟨t, hkl⟩
  rcases Set.mem_iUnion.mp hkl with ⟨arm, hkl⟩
  by_contra habs
  have hdev :
      |UCB.selectedPolicySuccessorEmpiricalMeanAt action reward omega t arm -
          (armMean arm : Real)| <
        UCB.selectedPolicySuccessorTelescopingRadiusAt
          action sigma2 delta omega t arm := by
    by_contra hnot
    apply habs
    unfold ConditionalExpectationReward.successorArmEmpiricalMeanFintypeTelescopingAllTimeBadEvent
    exact Set.mem_iUnion.mpr ⟨t, Set.mem_iUnion.mpr ⟨arm, by
      simpa [UCB.selectedPolicySuccessorEmpiricalMeanAt,
        UCB.selectedPolicySuccessorTelescopingRadiusAt] using
          And.intro hkl.1 (le_of_not_gt hnot)⟩⟩
  have hmem := armMean_mem_confidenceSet_of_abs_lt_radius
    action reward sigma2 delta margin hmargin0 hmarginHalf armMean omega t arm
    (hemp omega t arm) (hmean arm) hdev
  exact (not_lt_of_ge hmem.2) hkl.2

theorem measure_generatedKLAllTimeBadEvent_le
    {Omega : Type} [MeasurableSpace Omega] {K : Nat}
    (mu : Measure Omega)
    (action : Omega -> ActionTrace (Fin K))
    (reward : Omega -> RewardTrace Rat) (armMean : Fin K -> Rat)
    (sigma2 : NNReal) (delta margin : Real)
    (hmargin0 : 0 < margin) (hmarginHalf : margin <= 1 / 2)
    (hmean : forall arm : Fin K,
      (armMean arm : Real) ∈ Set.Icc margin (1 - margin))
    (hemp : ∀ᵐ omega ∂mu, forall t arm, IsBernoulliParameter
      (UCB.selectedPolicySuccessorEmpiricalMeanAt action reward omega t arm))
    (hconfidence :
      mu (ConditionalExpectationReward.successorArmEmpiricalMeanFintypeTelescopingAllTimeBadEvent
        action reward armMean sigma2 delta) <= ENNReal.ofReal delta) :
    mu (generatedKLAllTimeBadEvent action reward armMean sigma2 delta margin) <=
      ENNReal.ofReal delta := by
  refine (measure_mono_ae ?_).trans hconfidence
  filter_upwards [hemp] with omega homega
  intro hkl
  unfold generatedKLAllTimeBadEvent at hkl
  rcases Set.mem_iUnion.mp hkl with ⟨t, hkl⟩
  rcases Set.mem_iUnion.mp hkl with ⟨arm, hkl⟩
  by_contra habs
  have hdev :
      |UCB.selectedPolicySuccessorEmpiricalMeanAt action reward omega t arm -
          (armMean arm : Real)| <
        UCB.selectedPolicySuccessorTelescopingRadiusAt
          action sigma2 delta omega t arm := by
    by_contra hnot
    apply habs
    unfold ConditionalExpectationReward.successorArmEmpiricalMeanFintypeTelescopingAllTimeBadEvent
    exact Set.mem_iUnion.mpr ⟨t, Set.mem_iUnion.mpr ⟨arm, by
      simpa [UCB.selectedPolicySuccessorEmpiricalMeanAt,
        UCB.selectedPolicySuccessorTelescopingRadiusAt] using
          And.intro hkl.1 (le_of_not_gt hnot)⟩⟩
  have hmem := armMean_mem_confidenceSet_of_abs_lt_radius
    action reward sigma2 delta margin hmargin0 hmarginHalf armMean omega t arm
    (homega t arm) (hmean arm) hdev
  exact (not_lt_of_ge hmem.2) hkl.2

/-- Selected reward sums remain nonnegative under a pathwise `[0,1]` reward
contract. -/
theorem sumRewards_nonneg_of_mem_Icc_zero_one
    {Action : Type} [DecidableEq Action]
    (action : ActionTrace Action) (reward : RewardTrace Real)
    (arm : Action) (n : Nat)
    (hraw : forall i, i < n -> reward i ∈ Set.Icc (0 : Real) 1) :
    0 <= sumRewards action reward arm n := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [sumRewards_succ]
      split_ifs
      · exact add_nonneg (ih (fun i hi => hraw i (hi.trans (Nat.lt_succ_self n))))
          (hraw n (Nat.lt_succ_self n)).1
      · simpa using ih (fun i hi => hraw i (hi.trans (Nat.lt_succ_self n)))

theorem sumRewards_le_pullCount_of_mem_Icc_zero_one
    {Action : Type} [DecidableEq Action]
    (action : ActionTrace Action) (reward : RewardTrace Real)
    (arm : Action) (n : Nat)
    (hraw : forall i, i < n -> reward i ∈ Set.Icc (0 : Real) 1) :
    sumRewards action reward arm n <= (pullCount action arm n : Real) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [sumRewards_succ, pullCount_succ]
      split_ifs
      · simp only [Nat.cast_add, Nat.cast_one]
        have hprev := ih (fun i hi => hraw i (hi.trans (Nat.lt_succ_self n)))
        have hnow := (hraw n (Nat.lt_succ_self n)).2
        linarith
      · simpa using ih (fun i hi => hraw i (hi.trans (Nat.lt_succ_self n)))

/-- Hence every positive-count empirical mean on the canonical successor
trace is a Bernoulli parameter. -/
theorem successorArmEmpiricalMean_isBernoulliParameter_of_rewards_mem_Icc
    {Action : Type} [DecidableEq Action]
    (action : ActionTrace Action) (reward : RewardTrace Rat)
    (arm : Action) (n : Nat)
    (hcount : 0 < ConditionalExpectationReward.successorArmPullCount
      action arm n)
    (hraw : forall i : Nat, (((reward i : Rat) : Real)) ∈ Set.Icc (0 : Real) 1) :
    IsBernoulliParameter
      (ConditionalExpectationReward.successorArmEmpiricalMean action reward arm n) := by
  let shiftedAction : ActionTrace Action := fun i => action (i + 1)
  let shiftedReward : RewardTrace Real := fun i => (((reward (i + 1) : Rat) : Real))
  let count := pullCount shiftedAction arm (n - 1)
  have hcountPos : 0 < (count : Real) := by
    exact_mod_cast hcount
  have hsum0 : 0 <= sumRewards shiftedAction shiftedReward arm (n - 1) :=
    sumRewards_nonneg_of_mem_Icc_zero_one shiftedAction shiftedReward arm (n - 1)
      (fun i _ => hraw (i + 1))
  have hsum1 : sumRewards shiftedAction shiftedReward arm (n - 1) <=
      (count : Real) :=
    sumRewards_le_pullCount_of_mem_Icc_zero_one shiftedAction shiftedReward arm
      (n - 1) (fun i _ => hraw (i + 1))
  unfold IsBernoulliParameter
  constructor
  · unfold ConditionalExpectationReward.successorArmEmpiricalMean
      ConditionalExpectationReward.successorArmRewardSum
      ConditionalExpectationReward.successorArmPullCount
    exact div_nonneg hsum0 hcountPos.le
  · unfold ConditionalExpectationReward.successorArmEmpiricalMean
      ConditionalExpectationReward.successorArmRewardSum
      ConditionalExpectationReward.successorArmPullCount
    exact (div_le_iff₀ hcountPos).2 (by simpa [count, shiftedAction, shiftedReward] using hsum1)

theorem generatedEmpiricalMean_isBernoulliParameter_of_rewards_mem_Icc
    {Omega : Type} {K : Nat} (hK : 0 < K)
    (sigma2 : NNReal) (delta margin : Real) (defaultAction : Fin K)
    (reward : Omega -> RewardTrace Rat) (omega : Omega)
    (hraw : forall i : Nat, (((reward omega i : Rat) : Real)) ∈ Set.Icc (0 : Real) 1)
    (t : Nat) (ht : K <= t) (arm : Fin K) :
    IsBernoulliParameter
      (UCB.selectedPolicySuccessorEmpiricalMeanAt
        (generatedAction hK sigma2 delta margin defaultAction reward)
        reward omega t arm) := by
  apply successorArmEmpiricalMean_isBernoulliParameter_of_rewards_mem_Icc
  · exact successorArmPullCount_generatedAction_pos_of_K_le
      hK sigma2 delta margin defaultAction reward omega arm t ht
  · exact hraw

theorem successorArmEmpiricalMean_isBernoulliParameter_of_rewards_mem_Icc'
    {Action : Type} [DecidableEq Action]
    (action : ActionTrace Action) (reward : RewardTrace Rat)
    (arm : Action) (n : Nat)
    (hraw : forall i : Nat, (((reward i : Rat) : Real)) ∈ Set.Icc (0 : Real) 1) :
    IsBernoulliParameter
      (ConditionalExpectationReward.successorArmEmpiricalMean action reward arm n) := by
  by_cases hzero : ConditionalExpectationReward.successorArmPullCount action arm n = 0
  · unfold ConditionalExpectationReward.successorArmEmpiricalMean
    rw [hzero]
    simp [IsBernoulliParameter]
  · exact successorArmEmpiricalMean_isBernoulliParameter_of_rewards_mem_Icc
      action reward arm n (Nat.pos_of_ne_zero hzero) hraw

theorem generatedEmpiricalMean_isBernoulliParameter_of_rewards_mem_Icc'
    {Omega : Type} {K : Nat} (hK : 0 < K)
    (sigma2 : NNReal) (delta margin : Real) (defaultAction : Fin K)
    (reward : Omega -> RewardTrace Rat) (omega : Omega)
    (hraw : forall i : Nat, (((reward omega i : Rat) : Real)) ∈ Set.Icc (0 : Real) 1)
    (t : Nat) (arm : Fin K) :
    IsBernoulliParameter
      (UCB.selectedPolicySuccessorEmpiricalMeanAt
        (generatedAction hK sigma2 delta margin defaultAction reward)
        reward omega t arm) := by
  exact successorArmEmpiricalMean_isBernoulliParameter_of_rewards_mem_Icc'
    _ _ arm (t + 1) hraw

theorem measure_pullCount_gt_threshold_le_of_allTimeConfidence
    {Omega : Type} [MeasurableSpace Omega] {K : Nat} (hK : 0 < K)
    (mu : Measure Omega)
    (reward : Omega -> RewardTrace Rat) (armMean : Fin K -> Rat)
    (sigma2 : NNReal) (delta margin : Real)
    (hdelta : 0 < delta) (hmargin0 : 0 < margin)
    (hmarginHalf : margin <= 1 / 2)
    (hmean : forall arm : Fin K,
      (armMean arm : Real) ∈ Set.Icc margin (1 - margin))
    (hraw : ∀ᵐ omega ∂mu, forall i,
      (((reward omega i : Rat) : Real)) ∈ Set.Icc (0 : Real) 1)
    (defaultAction best chosen : Fin K) (T : Nat)
    (hbest : forall arm : Fin K, (armMean arm : Real) <= (armMean best : Real))
    (hgap : 0 < UCB.meanGap (fun arm => (armMean arm : Real)) best chosen)
    (hconfidence :
      mu (ConditionalExpectationReward.successorArmEmpiricalMeanFintypeTelescopingAllTimeBadEvent
        (generatedAction hK sigma2 delta margin defaultAction reward)
        reward armMean sigma2 delta) <= ENNReal.ofReal delta) :
    mu {omega | pullThreshold K sigma2 T delta margin
          (UCB.meanGap (fun arm => (armMean arm : Real)) best chosen) <
        ConditionalExpectationReward.successorArmPullCount
          (generatedAction hK sigma2 delta margin defaultAction reward omega)
          chosen (T + 1)} <= ENNReal.ofReal delta := by
  refine (measure_mono_ae ?_).trans hconfidence
  filter_upwards [hraw] with omega hrawOmega
  intro htail
  by_contra hgood
  have hcount := pullCount_le_of_not_badEvent hK reward armMean sigma2 delta
    margin hdelta hmargin0 hmarginHalf hmean defaultAction best chosen omega T
    hbest
    (fun t arm => generatedEmpiricalMean_isBernoulliParameter_of_rewards_mem_Icc'
      hK sigma2 delta margin defaultAction reward omega hrawOmega t arm)
    hgap hgood
  exact (not_lt_of_ge hcount) htail

theorem lintegral_pullCount_le_of_allTimeConfidence
    {Omega : Type} [MeasurableSpace Omega] {K : Nat} (hK : 0 < K)
    (mu : Measure Omega) [IsProbabilityMeasure mu]
    (reward : Omega -> RewardTrace Rat)
    (hreward : forall t : Nat, Measurable (fun omega : Omega => reward omega t))
    (armMean : Fin K -> Rat) (sigma2 : NNReal) (delta margin : Real)
    (hdelta : 0 < delta) (hmargin0 : 0 < margin)
    (hmarginHalf : margin <= 1 / 2)
    (hmean : forall arm : Fin K,
      (armMean arm : Real) ∈ Set.Icc margin (1 - margin))
    (hraw : ∀ᵐ omega ∂mu, forall i,
      (((reward omega i : Rat) : Real)) ∈ Set.Icc (0 : Real) 1)
    (defaultAction best chosen : Fin K) (T : Nat)
    (hbest : forall arm : Fin K, (armMean arm : Real) <= (armMean best : Real))
    (hgap : 0 < UCB.meanGap (fun arm => (armMean arm : Real)) best chosen)
    (hconfidence :
      mu (ConditionalExpectationReward.successorArmEmpiricalMeanFintypeTelescopingAllTimeBadEvent
        (generatedAction hK sigma2 delta margin defaultAction reward)
        reward armMean sigma2 delta) <= ENNReal.ofReal delta) :
    ∫⁻ omega, (ConditionalExpectationReward.successorArmPullCount
        (generatedAction hK sigma2 delta margin defaultAction reward omega)
        chosen (T + 1) : ENNReal) ∂mu <=
      (pullThreshold K sigma2 T delta margin
        (UCB.meanGap (fun arm => (armMean arm : Real)) best chosen) : ENNReal) +
        (T : ENNReal) * ENNReal.ofReal delta := by
  let action := generatedAction hK sigma2 delta margin defaultAction reward
  let count : Omega -> Nat := fun omega =>
    ConditionalExpectationReward.successorArmPullCount
      (action omega) chosen (T + 1)
  let threshold := pullThreshold K sigma2 T delta margin
    (UCB.meanGap (fun arm => (armMean arm : Real)) best chosen)
  have haction : forall t : Nat, Measurable (fun omega => action omega t) := by
    intro t
    exact ConditionalExpectationReward.generatedActionFromRewardHistory_measurable
      (policy := historyPolicy hK sigma2 delta margin defaultAction)
      (state := historyState hK sigma2 delta margin defaultAction)
      (defaultAction := defaultAction) (reward := reward) hreward
      (measurable_historyState hK sigma2 delta margin defaultAction) t
  have hcountMeas : Measurable count := by
    unfold count ConditionalExpectationReward.successorArmPullCount
    exact measurable_pullCount (fun omega i => action omega (i + 1))
      (fun i => haction (i + 1)) chosen (T + 1 - 1)
  have hcountLe : forall omega, count omega <= T := by
    intro omega
    unfold count ConditionalExpectationReward.successorArmPullCount
    simp only [Nat.add_sub_cancel]
    exact pullCount_le_time (fun i => action omega (i + 1)) chosen T
  have htail : mu {omega | threshold < count omega} <= ENNReal.ofReal delta := by
    simpa [threshold, count, action] using
      measure_pullCount_gt_threshold_le_of_allTimeConfidence hK mu reward armMean
        sigma2 delta margin hdelta hmargin0 hmarginHalf hmean hraw defaultAction
        best chosen T hbest hgap hconfidence
  simpa [threshold, count, action] using
    UCB.lintegral_natCast_le_threshold_add_bound_mul_of_measure_gt
      mu count hcountMeas threshold T hcountLe (ENNReal.ofReal delta) htail

/-- Regret-time shift of the canonical generated KL-UCB action. -/
def generatedRegretAction
    {Omega : Type} {K : Nat} (hK : 0 < K)
    (sigma2 : NNReal) (delta margin : Real) (defaultAction : Fin K)
    (reward : Omega -> RewardTrace Rat) : Omega -> ActionTrace (Fin K) :=
  fun omega t => generatedAction hK sigma2 delta margin defaultAction reward
    omega (t + 1)

theorem measurable_generatedRegretAction
    {Omega : Type} [MeasurableSpace Omega]
    {K : Nat} (hK : 0 < K) (sigma2 : NNReal) (delta margin : Real)
    (defaultAction : Fin K) (reward : Omega -> RewardTrace Rat)
    (hreward : forall t : Nat, Measurable (fun omega : Omega => reward omega t))
    (t : Nat) :
    Measurable (fun omega => generatedRegretAction hK sigma2 delta margin
      defaultAction reward omega t) := by
  exact ConditionalExpectationReward.generatedActionFromRewardHistory_measurable
    (policy := historyPolicy hK sigma2 delta margin defaultAction)
    (state := historyState hK sigma2 delta margin defaultAction)
    (defaultAction := defaultAction) (reward := reward) hreward
    (measurable_historyState hK sigma2 delta margin defaultAction) (t + 1)

theorem pullCount_generatedRegretAction_eq
    {Omega : Type} {K : Nat} (hK : 0 < K)
    (sigma2 : NNReal) (delta margin : Real) (defaultAction : Fin K)
    (reward : Omega -> RewardTrace Rat) (omega : Omega)
    (arm : Fin K) (T : Nat) :
    pullCount (generatedRegretAction hK sigma2 delta margin defaultAction
        reward omega) arm T =
      ConditionalExpectationReward.successorArmPullCount
        (generatedAction hK sigma2 delta margin defaultAction reward omega)
        arm (T + 1) := by
  unfold ConditionalExpectationReward.successorArmPullCount generatedRegretAction
  rw [Nat.add_sub_cancel]

/-- Finite-time expected pseudo-regret of the actual generated KL-UCB policy.
The `T * delta` failure-event term is explicit; this theorem makes no
asymptotic-optimality or leading-constant claim. -/
theorem lintegral_ofReal_pseudoRegret_generatedKLUCBBounded_le
    {Omega : Type} [MeasurableSpace Omega] {K : Nat}
    (mu : Measure Omega) [IsProbabilityMeasure mu]
    (model : FiniteBanditModel K)
    (reward : Omega -> RewardTrace Rat)
    (hreward : forall t : Nat, Measurable (fun omega : Omega => reward omega t))
    (sigma2 : NNReal) (delta margin : Real)
    (hdelta : 0 < delta) (hmargin0 : 0 < margin)
    (hmarginHalf : margin <= 1 / 2)
    (hmean : forall arm : Fin K,
      (model.mean arm : Real) ∈ Set.Icc margin (1 - margin))
    (hraw : ∀ᵐ omega ∂mu, forall i,
      (((reward omega i : Rat) : Real)) ∈ Set.Icc (0 : Real) 1)
    (defaultAction : Fin K) (T : Nat)
    (hconfidence :
      mu (ConditionalExpectationReward.successorArmEmpiricalMeanFintypeTelescopingAllTimeBadEvent
        (generatedAction model.hK sigma2 delta margin defaultAction reward)
        reward model.mean sigma2 delta) <= ENNReal.ofReal delta) :
    ∫⁻ omega, ENNReal.ofReal
        (((pseudoRegret model
          (generatedRegretAction model.hK sigma2 delta margin defaultAction
            reward omega) T : Rat) : Real)) ∂mu <=
      (Finset.univ : Finset (Fin K)).sum (fun arm =>
        ENNReal.ofReal (((model.gap arm : Rat) : Real)) *
          ((pullThreshold K sigma2 T delta margin
              (((model.gap arm : Rat) : Real)) : Nat) : ENNReal) +
        ENNReal.ofReal (((model.gap arm : Rat) : Real)) *
          ((T : ENNReal) * ENNReal.ofReal delta)) := by
  let action := generatedRegretAction model.hK sigma2 delta margin
    defaultAction reward
  simp_rw [← mul_add]
  apply UCB.lintegral_ofReal_pseudoRegret_le_sum_gap_mul_bound_of_positiveGap_pullCount
    mu model action
    (measurable_generatedRegretAction model.hK sigma2 delta margin
      defaultAction reward hreward)
    T
    (fun arm =>
      (pullThreshold K sigma2 T delta margin
        (((model.gap arm : Rat) : Real)) : ENNReal) +
        (T : ENNReal) * ENNReal.ofReal delta)
  intro arm hgap
  have hgapEq := UCB.modelMeanGap_bestArm_eq_realGap model arm
  have hmeanGap : 0 < UCB.meanGap
      (fun a => ((model.mean a : Rat) : Real)) model.bestArm arm := by
    rw [hgapEq]
    exact hgap
  have hbest : forall a : Fin K,
      (model.mean a : Real) <= (model.mean model.bestArm : Real) := by
    intro a
    exact_mod_cast FiniteBanditModel.mean_le_bestArm_mean model a
  have hcount := lintegral_pullCount_le_of_allTimeConfidence
    model.hK mu reward hreward model.mean sigma2 delta margin hdelta hmargin0
    hmarginHalf hmean hraw defaultAction model.bestArm arm T hbest hmeanGap
    hconfidence
  rw [hgapEq] at hcount
  simpa [action, pullCount_generatedRegretAction_eq] using hcount

/-- One good generated sample controls every finite horizon and positive-gap
arm for the same KL-UCB policy. -/
theorem allHorizonPullCount_of_not_badEvent
    {Omega : Type} {K : Nat} (hK : 0 < K)
    (reward : Omega -> RewardTrace Rat) (armMean : Fin K -> Rat)
    (sigma2 : NNReal) (delta margin : Real)
    (hdelta : 0 < delta) (hmargin0 : 0 < margin)
    (hmarginHalf : margin <= 1 / 2)
    (hmean : forall arm : Fin K,
      (armMean arm : Real) ∈ Set.Icc margin (1 - margin))
    (defaultAction best : Fin K) (omega : Omega)
    (hraw : forall i : Nat, (((reward omega i : Rat) : Real)) ∈ Set.Icc (0 : Real) 1)
    (hbest : forall arm : Fin K, (armMean arm : Real) <= (armMean best : Real))
    (hgood : omega ∉
      ConditionalExpectationReward.successorArmEmpiricalMeanFintypeTelescopingAllTimeBadEvent
        (generatedAction hK sigma2 delta margin defaultAction reward)
        reward armMean sigma2 delta) :
    forall T : Nat, forall chosen : Fin K,
      0 < UCB.meanGap (fun arm => (armMean arm : Real)) best chosen ->
        ConditionalExpectationReward.successorArmPullCount
            (generatedAction hK sigma2 delta margin defaultAction reward omega)
            chosen (T + 1) <=
          pullThreshold K sigma2 T delta margin
            (UCB.meanGap (fun arm => (armMean arm : Real)) best chosen) := by
  intro T chosen hgap
  exact pullCount_le_of_not_badEvent hK reward armMean sigma2 delta margin
    hdelta hmargin0 hmarginHalf hmean defaultAction best chosen omega T hbest
    (fun t arm => generatedEmpiricalMean_isBernoulliParameter_of_rewards_mem_Icc'
      hK sigma2 delta margin defaultAction reward omega hraw t arm)
    hgap hgood

/-- Canonical action/reward trajectory measure of the KL-UCB policy. -/
def actionRewardTrajMeasure
    {Context : Type} {K : Nat} [MeasurableSpace Context]
    (hK : 0 < K) (mu0 : Measure (Prod (Fin K) Rat))
    (rewardKernel : RewardKernel.MarkovRewardKernel (Prod Context (Fin K)) Rat)
    (context : (n : Nat) -> ((j : Finset.Iic n) -> Rat) -> Context)
    (hcontext : forall n : Nat, Measurable (context n))
    (sigma2 : NNReal) (delta margin : Real) (defaultAction : Fin K) :
    Measure (Nat -> Prod (Fin K) Rat) :=
  let policy := historyPolicy hK sigma2 delta margin defaultAction
  let state := historyState hK sigma2 delta margin defaultAction
  let pairContext :
      (i : Nat) -> ((j : Finset.Iic i) -> Prod (Fin K) Rat) -> Context :=
    fun i history => context i (History.pairHistoryRewardProjection history)
  let pairState :
      (i : Nat) -> ((j : Finset.Iic i) -> Prod (Fin K) Rat) ->
        UCB.SelectedPolicySuccessorFiniteHistoryState K :=
    fun i history => state i (History.pairHistoryRewardProjection history)
  let hpairContext : forall i : Nat, Measurable (pairContext i) := fun i =>
    (hcontext i).comp (History.measurable_pairHistoryRewardProjection
      (Action := Fin K) (Reward := Rat) i)
  let hpairState : forall i : Nat, Measurable (pairState i) := fun i =>
    (measurable_historyState hK sigma2 delta margin defaultAction i).comp
      (History.measurable_pairHistoryRewardProjection
        (Action := Fin K) (Reward := Rat) i)
  let stepKernel := RewardKernel.actionRewardHistoryStepKernelFamily
    rewardKernel policy pairContext pairState hpairContext hpairState
  ProbabilityTheory.Kernel.trajMeasure
    (X := fun _ : Nat => Prod (Fin K) Rat) mu0 stepKernel

theorem measure_allTimeBadEvent_le_trajMeasure
    {Context : Type} {K : Nat} [MeasurableSpace Context]
    (hK : 0 < K)
    (mu0 : Measure (Prod (Fin K) Rat)) [IsProbabilityMeasure mu0]
    (rewardKernel : RewardKernel.MarkovRewardKernel (Prod Context (Fin K)) Rat)
    (context : (n : Nat) -> ((j : Finset.Iic n) -> Rat) -> Context)
    (mean : Context -> Fin K -> Rat)
    (varianceProxy : Context -> Fin K -> NNReal)
    (defaultAction : Fin K) (armMean : Fin K -> Rat)
    (sigma2 : NNReal) (delta margin : Real)
    (hcontext : forall n : Nat, Measurable (context n))
    (hmean : Measurable (fun pair : Prod Context (Fin K) => mean pair.1 pair.2))
    (law : RewardKernel.CenteredRewardKernelLaw rewardKernel mean varianceProxy)
    (hvariance : forall i : Nat,
      forall history : ((j : Finset.Iic i) -> Rat),
        varianceProxy (context i history)
            ((historyPolicy hK sigma2 delta margin defaultAction i).action
              (historyState hK sigma2 delta margin defaultAction i history)) <= sigma2)
    (harmMean : forall i : Nat,
      forall history : ((j : Finset.Iic i) -> Rat), forall arm : Fin K,
        mean (context i history) arm = armMean arm)
    (hsigma2 : 0 < (((sigma2 : NNReal) : Real))) (hdelta : 0 < delta) :
    let mu := actionRewardTrajMeasure hK mu0 rewardKernel context hcontext
      sigma2 delta margin defaultAction
    let reward : (Nat -> Prod (Fin K) Rat) -> RewardTrace Rat :=
      fun trajectory t => (trajectory t).2
    let action := generatedAction hK sigma2 delta margin defaultAction reward
    mu (ConditionalExpectationReward.successorArmEmpiricalMeanFintypeTelescopingAllTimeBadEvent
      action reward armMean sigma2 delta) <= ENNReal.ofReal delta := by
  simpa [actionRewardTrajMeasure] using
    (actionRewardHistoryStepKernelFamily_allTimeConfidence hK mu0 rewardKernel
      context mean varianceProxy defaultAction armMean sigma2 delta margin
      hcontext hmean law hvariance harmMean hsigma2 hdelta)

theorem measure_generatedKLAllTimeBadEvent_le_trajMeasure
    {Context : Type} {K : Nat} [MeasurableSpace Context]
    (hK : 0 < K)
    (mu0 : Measure (Prod (Fin K) Rat)) [IsProbabilityMeasure mu0]
    (rewardKernel : RewardKernel.MarkovRewardKernel (Prod Context (Fin K)) Rat)
    (context : (n : Nat) -> ((j : Finset.Iic n) -> Rat) -> Context)
    (mean : Context -> Fin K -> Rat)
    (varianceProxy : Context -> Fin K -> NNReal)
    (defaultAction : Fin K) (armMean : Fin K -> Rat)
    (sigma2 : NNReal) (delta margin : Real)
    (hmargin0 : 0 < margin) (hmarginHalf : margin <= 1 / 2)
    (harmMargin : forall arm : Fin K,
      (armMean arm : Real) ∈ Set.Icc margin (1 - margin))
    (hcontext : forall n : Nat, Measurable (context n))
    (hraw : ∀ᵐ trajectory ∂(actionRewardTrajMeasure hK mu0 rewardKernel
        context hcontext sigma2 delta margin defaultAction), forall i : Nat,
      ((((trajectory i).2 : Rat) : Real)) ∈ Set.Icc (0 : Real) 1)
    (hmean : Measurable (fun pair : Prod Context (Fin K) => mean pair.1 pair.2))
    (law : RewardKernel.CenteredRewardKernelLaw rewardKernel mean varianceProxy)
    (hvariance : forall i : Nat,
      forall history : ((j : Finset.Iic i) -> Rat),
        varianceProxy (context i history)
            ((historyPolicy hK sigma2 delta margin defaultAction i).action
              (historyState hK sigma2 delta margin defaultAction i history)) <= sigma2)
    (harmMean : forall i : Nat,
      forall history : ((j : Finset.Iic i) -> Rat), forall arm : Fin K,
        mean (context i history) arm = armMean arm)
    (hsigma2 : 0 < (((sigma2 : NNReal) : Real))) (hdelta : 0 < delta) :
    let mu := actionRewardTrajMeasure hK mu0 rewardKernel context hcontext
      sigma2 delta margin defaultAction
    let reward : (Nat -> Prod (Fin K) Rat) -> RewardTrace Rat :=
      fun trajectory t => (trajectory t).2
    let action := generatedAction hK sigma2 delta margin defaultAction reward
    mu (generatedKLAllTimeBadEvent action reward armMean sigma2 delta margin) <=
      ENNReal.ofReal delta := by
  let mu := actionRewardTrajMeasure hK mu0 rewardKernel context hcontext
    sigma2 delta margin defaultAction
  let reward : (Nat -> Prod (Fin K) Rat) -> RewardTrace Rat :=
    fun trajectory t => (trajectory t).2
  let action := generatedAction hK sigma2 delta margin defaultAction reward
  have habs := measure_allTimeBadEvent_le_trajMeasure hK mu0 rewardKernel
    context mean varianceProxy defaultAction armMean sigma2 delta margin
    hcontext hmean law hvariance harmMean hsigma2 hdelta
  have hempAE : ∀ᵐ trajectory ∂mu, forall t arm, IsBernoulliParameter
      (UCB.selectedPolicySuccessorEmpiricalMeanAt action reward trajectory t arm) := by
    have hraw' : ∀ᵐ trajectory ∂mu, forall i : Nat,
        ((((trajectory i).2 : Rat) : Real)) ∈ Set.Icc (0 : Real) 1 := by
      simpa [mu] using hraw
    filter_upwards [hraw'] with trajectory htrajectory
    intro t arm
    exact generatedEmpiricalMean_isBernoulliParameter_of_rewards_mem_Icc'
      hK sigma2 delta margin defaultAction reward trajectory htrajectory t arm
  exact measure_generatedKLAllTimeBadEvent_le mu action reward armMean sigma2
    delta margin hmargin0 hmarginHalf harmMargin
    hempAE
    (by simpa [mu, action, reward] using habs)

/-- Canonical generated-policy KL-UCB regret theorem on the very trajectory
measure built from the same measurable KL policy and reward kernel. -/
theorem lintegral_ofReal_pseudoRegret_generatedKLUCBBounded_le_trajMeasure
    {Context : Type} {K : Nat} [MeasurableSpace Context]
    (model : FiniteBanditModel K)
    (mu0 : Measure (Prod (Fin K) Rat)) [IsProbabilityMeasure mu0]
    (rewardKernel : RewardKernel.MarkovRewardKernel (Prod Context (Fin K)) Rat)
    (context : (n : Nat) -> ((j : Finset.Iic n) -> Rat) -> Context)
    (mean : Context -> Fin K -> Rat)
    (varianceProxy : Context -> Fin K -> NNReal)
    (defaultAction : Fin K) (sigma2 : NNReal) (delta margin : Real) (T : Nat)
    (hdelta : 0 < delta) (hmargin0 : 0 < margin)
    (hmarginHalf : margin <= 1 / 2)
    (harmMargin : forall arm : Fin K,
      (model.mean arm : Real) ∈ Set.Icc margin (1 - margin))
    (hcontext : forall n : Nat, Measurable (context n))
    (hraw : ∀ᵐ trajectory ∂(actionRewardTrajMeasure model.hK mu0 rewardKernel
        context hcontext sigma2 delta margin defaultAction), forall i : Nat,
      ((((trajectory i).2 : Rat) : Real)) ∈ Set.Icc (0 : Real) 1)
    (hmean : Measurable (fun pair : Prod Context (Fin K) => mean pair.1 pair.2))
    (law : RewardKernel.CenteredRewardKernelLaw rewardKernel mean varianceProxy)
    (hvariance : forall i : Nat,
      forall history : ((j : Finset.Iic i) -> Rat),
        varianceProxy (context i history)
            ((historyPolicy model.hK sigma2 delta margin defaultAction i).action
              (historyState model.hK sigma2 delta margin defaultAction i history)) <= sigma2)
    (harmMean : forall i : Nat,
      forall history : ((j : Finset.Iic i) -> Rat), forall arm : Fin K,
        mean (context i history) arm = model.mean arm)
    (hsigma2 : 0 < (((sigma2 : NNReal) : Real))) :
    let mu := actionRewardTrajMeasure model.hK mu0 rewardKernel context hcontext
      sigma2 delta margin defaultAction
    let reward : (Nat -> Prod (Fin K) Rat) -> RewardTrace Rat :=
      fun trajectory t => (trajectory t).2
    let action := generatedRegretAction model.hK sigma2 delta margin
      defaultAction reward
    ∫⁻ trajectory, ENNReal.ofReal
        (((pseudoRegret model (action trajectory) T : Rat) : Real)) ∂mu <=
      (Finset.univ : Finset (Fin K)).sum (fun arm =>
        ENNReal.ofReal (((model.gap arm : Rat) : Real)) *
          ((pullThreshold K sigma2 T delta margin
              (((model.gap arm : Rat) : Real)) : Nat) : ENNReal) +
        ENNReal.ofReal (((model.gap arm : Rat) : Real)) *
          ((T : ENNReal) * ENNReal.ofReal delta)) := by
  let mu := actionRewardTrajMeasure model.hK mu0 rewardKernel context hcontext
    sigma2 delta margin defaultAction
  letI : IsProbabilityMeasure mu := by
    dsimp [mu, actionRewardTrajMeasure]
    infer_instance
  let reward : (Nat -> Prod (Fin K) Rat) -> RewardTrace Rat :=
    fun trajectory t => (trajectory t).2
  have hreward : forall t : Nat,
      Measurable (fun trajectory : Nat -> Prod (Fin K) Rat => reward trajectory t) := by
    intro t
    exact measurable_snd.comp (measurable_pi_apply t)
  have hconfidence := measure_allTimeBadEvent_le_trajMeasure model.hK mu0
    rewardKernel context mean varianceProxy defaultAction model.mean sigma2 delta
    margin hcontext hmean law hvariance harmMean hsigma2 hdelta
  simpa [mu, reward] using
    (lintegral_ofReal_pseudoRegret_generatedKLUCBBounded_le mu model reward
      hreward sigma2 delta margin hdelta hmargin0 hmarginHalf harmMargin
      (by simpa [mu, reward] using hraw) defaultAction T
      (by simpa [mu, reward] using hconfidence))

theorem measurable_generatedAction
    {Omega : Type} [MeasurableSpace Omega]
    {K : Nat} (hK : 0 < K) (sigma2 : NNReal) (delta margin : Real)
    (defaultAction : Fin K) (reward : Omega -> RewardTrace Rat)
    (hreward : forall t : Nat, Measurable (fun omega : Omega => reward omega t))
    (t : Nat) :
    Measurable (fun omega =>
      generatedAction hK sigma2 delta margin defaultAction reward omega t) := by
  exact ConditionalExpectationReward.generatedActionFromRewardHistory_measurable
    (policy := historyPolicy hK sigma2 delta margin defaultAction)
    (state := historyState hK sigma2 delta margin defaultAction)
    (defaultAction := defaultAction) (reward := reward) hreward
    (measurable_historyState hK sigma2 delta margin defaultAction) t

end
end KLUCB
end BanditRLProof
