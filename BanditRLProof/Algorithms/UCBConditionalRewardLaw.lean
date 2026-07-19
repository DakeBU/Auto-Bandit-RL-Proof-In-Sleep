import BanditRLProof.Algorithms.UCB
import BanditRLProof.ConditionalRewardLawSource

/-!
# UCB score consumers for the practical conditional reward law

This module connects the selected-policy simultaneous empirical-mean event to
the deterministic UCB score algebra.  Its confidence width depends on the
realized pull count, so it deliberately does not use the older
`UCB.finiteHorizonConfidenceBadEvent`, whose radius is deterministic in the
sample point.
-/

namespace BanditRLProof
namespace UCB

open MeasureTheory

universe u v w

/-- Successor empirical mean at the positive horizon `t + 1`. -/
noncomputable def selectedPolicySuccessorEmpiricalMeanAt
    {Omega : Type u} {Action : Type} [DecidableEq Action]
    (action : Omega -> ActionTrace Action)
    (reward : Omega -> RewardTrace Rat)
    (omega : Omega) (t : Nat) (arm : Action) : Real :=
  ConditionalExpectationReward.successorArmEmpiricalMean
    (action omega) (reward omega) arm (t + 1)

/-- Realized-count confidence width used at one arm/time pair. -/
noncomputable def selectedPolicySuccessorRadiusAt
    {Omega : Type u} {Action : Type} [DecidableEq Action]
    (action : Omega -> ActionTrace Action)
    (sigma2 : NNReal) (arms : Finset Action) (T : Nat) (delta : Real)
    (omega : Omega) (t : Nat) (arm : Action) : Real :=
  ConditionalExpectationReward.successorArmEmpiricalMeanFiniteArmTimePeelingRadius
    sigma2
    (ConditionalExpectationReward.successorArmPullCount
      (action omega) arm (t + 1))
    (t + 1) arms T delta

/-- Practical UCB index with a sample-dependent realized-count width. -/
noncomputable def selectedPolicySuccessorIndexAt
    {Omega : Type u} {Action : Type} [DecidableEq Action]
    (action : Omega -> ActionTrace Action)
    (reward : Omega -> RewardTrace Rat)
    (sigma2 : NNReal) (arms : Finset Action) (T : Nat) (delta : Real)
    (omega : Omega) (t : Nat) (arm : Action) : Real :=
  confidenceScore
    (fun candidate =>
      selectedPolicySuccessorEmpiricalMeanAt action reward omega t candidate)
    (fun candidate =>
      selectedPolicySuccessorRadiusAt action sigma2 arms T delta
        omega t candidate)
    arm

/--
Initialization and score-maximality contract for the finite set of charged UCB
times.  The time set may omit initialization rounds; every retained time must
lie below `T`, and both the designated best arm and the selected arm must have
positive realized successor pull counts.
-/
structure SelectedPolicySuccessorInitializedScoreMaxSource
    {Omega : Type u} {Action : Type} [DecidableEq Action]
    (action : Omega -> ActionTrace Action)
    (reward : Omega -> RewardTrace Rat)
    (arms : Finset Action) (armMean : Action -> Rat)
    (sigma2 : NNReal) (T : Nat) (delta : Real) where
  times : Finset Nat
  best : Action
  chosen : Omega -> Nat -> Action
  times_lt : forall t, t ∈ times -> t < T
  best_mem : best ∈ arms
  chosen_mem : forall omega t, t ∈ times -> chosen omega t ∈ arms
  best_count_pos : forall omega t, t ∈ times ->
    0 < ConditionalExpectationReward.successorArmPullCount
      (action omega) best (t + 1)
  chosen_count_pos : forall omega t, t ∈ times ->
    0 < ConditionalExpectationReward.successorArmPullCount
      (action omega) (chosen omega t) (t + 1)
  score_max : forall omega t, t ∈ times ->
    selectedPolicySuccessorIndexAt action reward sigma2 arms T delta
        omega t best <=
      selectedPolicySuccessorIndexAt action reward sigma2 arms T delta
        omega t (chosen omega t)

/-- Large-gap selected-time event charged by the practical confidence event. -/
noncomputable def selectedPolicySuccessorLargeGapEvent
    {Omega : Type u} {Action : Type} [DecidableEq Action]
    {action : Omega -> ActionTrace Action}
    {reward : Omega -> RewardTrace Rat}
    {arms : Finset Action} {armMean : Action -> Rat}
    {sigma2 : NNReal} {T : Nat} {delta : Real}
    (source : SelectedPolicySuccessorInitializedScoreMaxSource
      action reward arms armMean sigma2 T delta) : Set Omega :=
  {omega | exists t, t ∈ source.times ∧
    2 * selectedPolicySuccessorRadiusAt action sigma2 arms T delta
          omega t (source.chosen omega t) <
      meanGap (fun arm => (armMean arm : Real))
        source.best (source.chosen omega t)}

/--
Outside the practical simultaneous confidence event, score maximality implies
the standard UCB gap bound at every initialized charged time.
-/
theorem SelectedPolicySuccessorInitializedScoreMaxSource.meanGap_le_two_radius_of_not_badEvent
    {Omega : Type u} {Action : Type} [DecidableEq Action]
    {action : Omega -> ActionTrace Action}
    {reward : Omega -> RewardTrace Rat}
    {arms : Finset Action} {armMean : Action -> Rat}
    {sigma2 : NNReal} {T : Nat} {delta : Real}
    (source : SelectedPolicySuccessorInitializedScoreMaxSource
      action reward arms armMean sigma2 T delta)
    (omega : Omega) (t : Nat) (ht : t ∈ source.times)
    (hgood : omega ∉
      ConditionalExpectationReward.successorArmEmpiricalMeanFiniteArmTimeBadEvent
        action reward arms armMean sigma2 T delta) :
    meanGap (fun arm => (armMean arm : Real))
        source.best (source.chosen omega t) <=
      2 * selectedPolicySuccessorRadiusAt action sigma2 arms T delta
        omega t (source.chosen omega t) := by
  let empiricalMean : Action -> Real := fun arm =>
    selectedPolicySuccessorEmpiricalMeanAt action reward omega t arm
  let radius : Action -> Real := fun arm =>
    selectedPolicySuccessorRadiusAt action sigma2 arms T delta omega t arm
  have hpair (arm : Action) (harm : arm ∈ arms)
      (hcount : 0 < ConditionalExpectationReward.successorArmPullCount
        (action omega) arm (t + 1))
      (hdeviation : radius arm <=
        |empiricalMean arm - (armMean arm : Real)|) :
      omega ∈
        ConditionalExpectationReward.successorArmEmpiricalMeanFiniteArmTimeBadEvent
          action reward arms armMean sigma2 T delta := by
    unfold ConditionalExpectationReward.successorArmEmpiricalMeanFiniteArmTimeBadEvent
    exact Set.mem_iUnion.mpr
      ⟨(arm, t), Set.mem_iUnion.mpr
        ⟨Finset.mem_product.mpr
          ⟨harm, Finset.mem_range.mpr (source.times_lt t ht)⟩,
          by simpa [empiricalMean, radius,
            selectedPolicySuccessorEmpiricalMeanAt,
            selectedPolicySuccessorRadiusAt] using
              And.intro hcount hdeviation⟩⟩
  have hbestAbs :
      |empiricalMean source.best - (armMean source.best : Real)| <
        radius source.best := by
    by_contra hnot
    exact hgood (hpair source.best source.best_mem
      (source.best_count_pos omega t ht) (le_of_not_gt hnot))
  have hchosenAbs :
      |empiricalMean (source.chosen omega t) -
          (armMean (source.chosen omega t) : Real)| <
        radius (source.chosen omega t) := by
    by_contra hnot
    exact hgood (hpair (source.chosen omega t)
      (source.chosen_mem omega t ht)
      (source.chosen_count_pos omega t ht) (le_of_not_gt hnot))
  have hbestUpper :
      (armMean source.best : Real) <=
        confidenceScore empiricalMean radius source.best := by
    have hneg :=
      neg_le_abs (empiricalMean source.best - (armMean source.best : Real))
    simp only [confidenceScore]
    linarith
  have hchosenLower :
      empiricalMean (source.chosen omega t) -
          radius (source.chosen omega t) <=
        (armMean (source.chosen omega t) : Real) := by
    have hself := le_abs_self
      (empiricalMean (source.chosen omega t) -
        (armMean (source.chosen omega t) : Real))
    linarith
  have hscore :
      confidenceScore empiricalMean radius source.best <=
        confidenceScore empiricalMean radius (source.chosen omega t) := by
    simpa [empiricalMean, radius, selectedPolicySuccessorIndexAt] using
      source.score_max omega t ht
  simpa [radius] using
    (meanGap_le_two_radius_of_confidenceScore_max
      (fun arm => (armMean arm : Real)) empiricalMean radius
      source.best (source.chosen omega t) hbestUpper hchosenLower hscore)

/--
Practical selected-policy UCB large-gap event bound on initialized times.

The simultaneous empirical-mean theorem supplies the probability bound.  The
source contract turns any large-gap score-maximal selection outside that event
into a contradiction via the deterministic UCB confidence algebra.
-/
theorem measure_selectedPolicySuccessorLargeGapEvent_le_ennreal_delta_of_reward_map_eq_selected_policy_definitionalRawRangeMeasurableMeanRangeHistoryVarianceBounded
    {Omega : Type u} {Context : Type v} {State : Type w} {Action : Type}
    [mOmega : MeasurableSpace Omega] [StandardBorelSpace Omega]
    [MeasurableSpace Context] [MeasurableSpace State]
    [MeasurableSpace Action] [MeasurableSingletonClass Action]
    [Countable Action] [DecidableEq Action]
    (mu : Measure Omega) [IsProbabilityMeasure mu]
    (rewardKernel : RewardKernel.MarkovRewardKernel (Prod Context Action) Rat)
    (policy : Nat -> Policy.MeasurablePolicy State Action)
    (context : (n : Nat) -> ((j : Finset.Iic n) -> Rat) -> Context)
    (state : (n : Nat) -> ((j : Finset.Iic n) -> Rat) -> State)
    (mean : Context -> Action -> Rat)
    (varianceProxy : Context -> Action -> NNReal)
    (defaultAction : Action)
    (arms : Finset Action) (harms : arms.Nonempty)
    (armMean : Action -> Rat)
    (reward : Omega -> RewardTrace Rat)
    (hreward : forall t : Nat,
      Measurable (fun omega : Omega => reward omega t))
    (rewardLo rewardHi meanLo meanHi : Nat -> Real)
    (sigma2 : NNReal)
    (hcontext : forall n : Nat, Measurable (context n))
    (hstate : forall n : Nat, Measurable (state n))
    (hmean : Measurable (fun pair : Prod Context Action => mean pair.1 pair.2))
    (hkernel : RewardKernel.CenteredRewardKernelLaw rewardKernel mean varianceProxy)
    (hraw : forall i : Nat, forall omega : Omega,
      Set.Icc (rewardLo i) (rewardHi i)
        (((reward omega (i + 1) : Rat) : Real)))
    (hmean_range : forall i : Nat, forall context : Context,
      forall action : Action,
        Set.Icc (meanLo i) (meanHi i)
          (((mean context action : Rat) : Real)))
    (hvariance : forall i : Nat,
      forall history : ((j : Finset.Iic i) -> Rat),
        varianceProxy (context i history)
          ((policy i).action (state i history)) <= sigma2)
    (harmMean : forall i : Nat,
      forall history : ((j : Finset.Iic i) -> Rat),
        forall arm, arm ∈ arms ->
          mean (context i history) arm = armMean arm)
    (h_reward_map_eq_policy : forall i : Nat,
      Filter.Eventually
        (fun omega : Omega =>
          @Measure.map Omega Rat mOmega inferInstance
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
        (ae
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
    (T : Nat) (hT : 0 < T)
    (hsigma2 : 0 < (((sigma2 : NNReal) : Real)))
    (delta : Real) (hdelta : 0 < delta)
    (source : SelectedPolicySuccessorInitializedScoreMaxSource
      (ConditionalExpectationReward.generatedActionFromRewardHistory
        policy state defaultAction reward)
      reward arms armMean sigma2 T delta) :
    mu (selectedPolicySuccessorLargeGapEvent source) <=
      ENNReal.ofReal delta := by
  let action :=
    ConditionalExpectationReward.generatedActionFromRewardHistory
      policy state defaultAction reward
  have htail :=
    ConditionalExpectationReward.successorArmEmpiricalMean_simultaneous_finiteArmTime_abs_tail_ennreal_delta_of_reward_map_eq_selected_policy_definitionalRawRangeMeasurableMeanRangeHistoryVarianceBounded
      (mu := mu)
      (rewardKernel := rewardKernel)
      (policy := policy)
      (context := context)
      (state := state)
      (mean := mean)
      (varianceProxy := varianceProxy)
      (defaultAction := defaultAction)
      (arms := arms) harms
      (armMean := armMean)
      (reward := reward)
      (hreward := hreward)
      (rewardLo := rewardLo)
      (rewardHi := rewardHi)
      (meanLo := meanLo)
      (meanHi := meanHi)
      (sigma2 := sigma2)
      (hcontext := hcontext)
      (hstate := hstate)
      (hmean := hmean)
      (hkernel := hkernel)
      (hraw := hraw)
      (hmean_range := hmean_range)
      (hvariance := hvariance)
      (harmMean := harmMean)
      (h_reward_map_eq_policy := h_reward_map_eq_policy)
      T hT hsigma2 delta hdelta
  refine (measure_mono ?_).trans (by simpa [action] using htail)
  intro omega homega
  rcases homega with ⟨t, ht, hlarge⟩
  by_contra hgood
  have hgap := source.meanGap_le_two_radius_of_not_badEvent
    omega t ht hgood
  exact (not_lt_of_ge hgap) hlarge

end UCB
end BanditRLProof
