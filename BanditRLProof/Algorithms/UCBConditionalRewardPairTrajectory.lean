import BanditRLProof.Algorithms.UCBConditionalRewardLaw
import BanditRLProof.Algorithms.UCBConditionalRewardLawPolicy
import BanditRLProof.Algorithms.UCBConditionalRewardLawRegret
import BanditRLProof.ConditionalRewardPartialTrajectoryMaskedLaw

/-!
# Canonical pair-trajectory UCB confidence consumer

This module consumes the canonical action/reward trajectory simultaneous
empirical-mean event in the random-width UCB score algebra. It proves a
fixed finite-arm/time large-gap event bound, a positive-gap chosen-arm
explicit-threshold tail/ENNReal expected pull-count bound, and the resulting
finite-arm explicit-threshold and textbook positive-gap ENNReal pseudo-regret
sums. It requires a `CenteredRewardKernelLaw`, but no caller selected-reward
trajectory law or reward-range premise. It does not prove anytime confidence,
an asymptotic normalization, or a Real/Bochner expectation endpoint.
-/

universe u v

namespace BanditRLProof
namespace UCB

open MeasureTheory ProbabilityTheory

/-
Canonical pair-trajectory random-width UCB large-gap event bound.

The score source is expressed directly with the sampled action and reward
coordinates. The canonical history-step trajectory measure supplies the
simultaneous confidence theorem, while the source supplies initialization and
score maximality on its charged times.
-/
theorem measure_actionRewardHistoryStepKernelFamily_selectedPolicySuccessorLargeGapEvent_le_ennreal_delta_trajMeasure
    {Context : Type u} {State : Type v} {Action : Type}
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
    (delta : Real) (hdelta : 0 < delta)
    (source : SelectedPolicySuccessorInitializedScoreMaxSource
      (fun trajectory : Nat -> Prod Action Rat => fun t => (trajectory t).1)
      (fun trajectory : Nat -> Prod Action Rat => fun t => (trajectory t).2)
      arms armMean sigma2 T delta) :
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
    mu (selectedPolicySuccessorLargeGapEvent source) <= ENNReal.ofReal delta := by
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
  let bad :=
    ConditionalExpectationReward.successorArmEmpiricalMeanFiniteArmTimeBadEvent
      (fun trajectory : Nat -> Prod Action Rat => fun t => (trajectory t).1)
      (fun trajectory : Nat -> Prod Action Rat => fun t => (trajectory t).2)
      arms armMean sigma2 T delta
  have htail :=
    ConditionalExpectationReward.actionRewardHistoryStepKernelFamily_successorArmEmpiricalMean_simultaneous_finiteArmTime_abs_tail_ennreal_delta_trajMeasure
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
      (arms := arms) harms
      (armMean := armMean)
      (sigma2 := sigma2)
      (T := T)
      (hvariance := hvariance)
      (harmMean := harmMean)
      hT hsigma2 delta hdelta
  have htail' : mu bad <= ENNReal.ofReal delta := by
    simpa [pairContext, pairState, hpairContext, hpairState, stepKernel, mu,
      bad] using htail
  have hsubset : selectedPolicySuccessorLargeGapEvent source ⊆ bad := by
    intro trajectory hlargeEvent
    rcases hlargeEvent with ⟨t, ht, hlarge⟩
    by_contra hgood
    have hgap := source.meanGap_le_two_radius_of_not_badEvent
      trajectory t ht (by simpa [bad] using hgood)
    exact (not_lt_of_ge hgap) hlarge
  have hresult :
      mu (selectedPolicySuccessorLargeGapEvent source) <=
        ENNReal.ofReal delta :=
    (measure_mono hsubset).trans htail'
  simpa [pairContext, pairState, hpairContext, hpairState, stepKernel, mu]
    using hresult

/-
Concrete generated-UCB large-gap event bound on the canonical pair trajectory.

The generated UCB source is defined from the reward coordinate. Its action
trace agrees with the sampled pair action only almost everywhere; the proof
therefore transports the full generated confidence event on that a.e. set
before applying the sampled-coordinate simultaneous theorem.
-/
theorem measure_selectedPolicySuccessorLargeGapEvent_generatedUCB_le_ennreal_delta_actionRewardTrajMeasure_centeredKernel
    {Context : Type u} {K : Nat} [MeasurableSpace Context]
    (hK : 0 < K)
    (mu0 : Measure (Prod (Fin K) Rat)) [IsProbabilityMeasure mu0]
    (rewardKernel : RewardKernel.MarkovRewardKernel (Prod Context (Fin K)) Rat)
    (context : (n : Nat) -> ((j : Finset.Iic n) -> Rat) -> Context)
    (mean : Context -> Fin K -> Rat)
    (varianceProxy : Context -> Fin K -> NNReal)
    (defaultAction best : Fin K)
    (armMean : Fin K -> Rat) (sigma2 : NNReal) (T : Nat) (delta : Real)
    (hcontext : forall n : Nat, Measurable (context n))
    (hmean : Measurable (fun pair : Prod Context (Fin K) =>
      mean pair.1 pair.2))
    (law : RewardKernel.CenteredRewardKernelLaw rewardKernel mean varianceProxy)
    (hvariance : forall i : Nat, i < T - 1 ->
      forall history : ((j : Finset.Iic i) -> Rat),
        varianceProxy (context i history)
            ((selectedPolicySuccessorHistoryPolicy
              hK sigma2 T delta defaultAction i).action
              (selectedPolicySuccessorHistoryState
                hK sigma2 T delta defaultAction i history)) <=
          sigma2)
    (harmMean : forall i : Nat,
      forall history : ((j : Finset.Iic i) -> Rat),
        forall arm : Fin K,
          mean (context i history) arm = armMean arm)
    (hT : 0 < T) (hsigma2 : 0 < (((sigma2 : NNReal) : Real)))
    (hdelta : 0 < delta) :
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
    let source :=
      selectedPolicySuccessorGeneratedUCBInitializedScoreMaxSource
        hK reward armMean sigma2 T delta defaultAction best
    mu (selectedPolicySuccessorLargeGapEvent source) <=
      ENNReal.ofReal delta := by
  classical
  letI : Nonempty (Fin K) := ⟨Fin.mk 0 hK⟩
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
  let source :=
    selectedPolicySuccessorGeneratedUCBInitializedScoreMaxSource
      hK reward armMean sigma2 T delta defaultAction best
  let sampledBad :=
    ConditionalExpectationReward.successorArmEmpiricalMeanFiniteArmTimeBadEvent
      sampledAction reward (Finset.univ : Finset (Fin K)) armMean sigma2 T delta
  let generatedBad :=
    ConditionalExpectationReward.successorArmEmpiricalMeanFiniteArmTimeBadEvent
      generatedAction reward (Finset.univ : Finset (Fin K)) armMean sigma2 T delta
  have htail :=
    ConditionalExpectationReward.actionRewardHistoryStepKernelFamily_successorArmEmpiricalMean_simultaneous_finiteArmTime_abs_tail_ennreal_delta_trajMeasure
      (mu0 := mu0)
      (rewardKernel := rewardKernel)
      (policy := policy)
      (context := context)
      (state := state)
      (hcontext := hcontext)
      (hstate := measurable_selectedPolicySuccessorHistoryState
        hK sigma2 T delta defaultAction)
      (mean := mean)
      (varianceProxy := varianceProxy)
      (law := law)
      (hmean := hmean)
      (arms := (Finset.univ : Finset (Fin K)))
      (by exact ⟨defaultAction, Finset.mem_univ _⟩)
      (armMean := armMean)
      (sigma2 := sigma2)
      (T := T)
      (hvariance := hvariance)
      (harmMean := by
        intro i history arm _harm
        exact harmMean i history arm)
      hT hsigma2 delta hdelta
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
      selectedPolicySuccessorGeneratedUCBAction,
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
      ConditionalExpectationReward.successorArmEmpiricalMeanFiniteArmTimeBadEvent,
      ConditionalExpectationReward.successorArmEmpiricalMean,
      ConditionalExpectationReward.successorArmRewardSum,
      ConditionalExpectationReward.successorArmPullCount, hshift] using hbad
  have hlarge_to_generatedBad :
      selectedPolicySuccessorLargeGapEvent source ⊆ generatedBad := by
    intro trajectory hlargeEvent
    rcases hlargeEvent with ⟨t, ht, hlarge⟩
    by_contra hgood
    have hgap := source.meanGap_le_two_radius_of_not_badEvent
      trajectory t ht (by
        simpa [source, generatedAction, generatedBad] using hgood)
    exact (not_lt_of_ge hgap) hlarge
  have hsubset : ∀ᵐ trajectory ∂mu,
      trajectory ∈ selectedPolicySuccessorLargeGapEvent source ->
        trajectory ∈ sampledBad := by
    filter_upwards [hgeneratedBad_to_sampledBad] with trajectory htransport
    intro hlarge
    exact htransport (hlarge_to_generatedBad hlarge)
  have hresult :
      mu (selectedPolicySuccessorLargeGapEvent source) <=
        ENNReal.ofReal delta :=
    (measure_mono_ae hsubset).trans htail'
  simpa [policy, state, pairContext, pairState, hpairContext, hpairState,
    stepKernel, mu, reward, source] using hresult

/-
Concrete generated-UCB pull-count tail on the canonical pair trajectory.

The preceding theorem supplies the only probabilistic premise. The existing
generated-policy consumer discharges the random-radius inversion at the
explicit one-more-than-ceiling threshold.
-/
theorem measure_successorArmPullCount_selectedPolicySuccessorGeneratedUCBAction_gt_explicitPullThreshold_le_ennreal_delta_actionRewardTrajMeasure_centeredKernel
    {Context : Type u} {K : Nat} [MeasurableSpace Context]
    (hK : 0 < K)
    (mu0 : Measure (Prod (Fin K) Rat)) [IsProbabilityMeasure mu0]
    (rewardKernel : RewardKernel.MarkovRewardKernel (Prod Context (Fin K)) Rat)
    (context : (n : Nat) -> ((j : Finset.Iic n) -> Rat) -> Context)
    (mean : Context -> Fin K -> Rat)
    (varianceProxy : Context -> Fin K -> NNReal)
    (defaultAction best chosen : Fin K)
    (armMean : Fin K -> Rat) (sigma2 : NNReal) (T : Nat) (delta : Real)
    (hcontext : forall n : Nat, Measurable (context n))
    (hmean : Measurable (fun pair : Prod Context (Fin K) =>
      mean pair.1 pair.2))
    (law : RewardKernel.CenteredRewardKernelLaw rewardKernel mean varianceProxy)
    (hvariance : forall i : Nat, i < T - 1 ->
      forall history : ((j : Finset.Iic i) -> Rat),
        varianceProxy (context i history)
            ((selectedPolicySuccessorHistoryPolicy
              hK sigma2 T delta defaultAction i).action
              (selectedPolicySuccessorHistoryState
                hK sigma2 T delta defaultAction i history)) <=
          sigma2)
    (harmMean : forall i : Nat,
      forall history : ((j : Finset.Iic i) -> Rat),
        forall arm : Fin K,
          mean (context i history) arm = armMean arm)
    (hT : 0 < T) (hsigma2 : 0 < (((sigma2 : NNReal) : Real)))
    (hdelta : 0 < delta)
    (hgap : 0 < meanGap (fun arm => (armMean arm : Real)) best chosen) :
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
    let generatedAction := selectedPolicySuccessorGeneratedUCBAction
      hK sigma2 T delta defaultAction reward
    let gap := meanGap (fun arm => (armMean arm : Real)) best chosen
    mu {trajectory |
        selectedPolicySuccessorPullThreshold K sigma2 T delta gap <
          ConditionalExpectationReward.successorArmPullCount
            (generatedAction trajectory) chosen (T + 1)} <=
      ENNReal.ofReal delta := by
  classical
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
  let generatedAction := selectedPolicySuccessorGeneratedUCBAction
    hK sigma2 T delta defaultAction reward
  let gap := meanGap (fun arm => (armMean arm : Real)) best chosen
  have hlarge :=
    measure_selectedPolicySuccessorLargeGapEvent_generatedUCB_le_ennreal_delta_actionRewardTrajMeasure_centeredKernel
      hK mu0 rewardKernel context mean varianceProxy defaultAction best armMean
        sigma2 T delta hcontext hmean law hvariance harmMean hT hsigma2 hdelta
  have hlarge' :
      mu (selectedPolicySuccessorLargeGapEvent
        (selectedPolicySuccessorGeneratedUCBInitializedScoreMaxSource
          hK reward armMean sigma2 T delta defaultAction best)) <=
        ENNReal.ofReal delta := by
    simpa [policy, state, pairContext, pairState, hpairContext, hpairState,
      stepKernel, mu, reward] using hlarge
  have htail :=
    measure_successorArmPullCount_selectedPolicySuccessorGeneratedUCBAction_gt_explicitPullThreshold_le_of_largeGap
      hK mu reward armMean sigma2 T hT delta hdelta defaultAction best chosen
        hgap hlarge'
  simpa [generatedAction, gap] using htail

/-
Concrete generated-UCB ENNReal expected pull-count bound on the canonical pair
trajectory. Reward-coordinate measurability is automatic from the product
trajectory space; generated-action/count measurability and the finite-horizon
tail integration are discharged by the existing consumer.
-/
theorem lintegral_successorArmPullCount_selectedPolicySuccessorGeneratedUCBAction_le_explicitPullThreshold_add_horizon_mul_delta_actionRewardTrajMeasure_centeredKernel
    {Context : Type u} {K : Nat} [MeasurableSpace Context]
    (hK : 0 < K)
    (mu0 : Measure (Prod (Fin K) Rat)) [IsProbabilityMeasure mu0]
    (rewardKernel : RewardKernel.MarkovRewardKernel (Prod Context (Fin K)) Rat)
    (context : (n : Nat) -> ((j : Finset.Iic n) -> Rat) -> Context)
    (mean : Context -> Fin K -> Rat)
    (varianceProxy : Context -> Fin K -> NNReal)
    (defaultAction best chosen : Fin K)
    (armMean : Fin K -> Rat) (sigma2 : NNReal) (T : Nat) (delta : Real)
    (hcontext : forall n : Nat, Measurable (context n))
    (hmean : Measurable (fun pair : Prod Context (Fin K) =>
      mean pair.1 pair.2))
    (law : RewardKernel.CenteredRewardKernelLaw rewardKernel mean varianceProxy)
    (hvariance : forall i : Nat, i < T - 1 ->
      forall history : ((j : Finset.Iic i) -> Rat),
        varianceProxy (context i history)
            ((selectedPolicySuccessorHistoryPolicy
              hK sigma2 T delta defaultAction i).action
              (selectedPolicySuccessorHistoryState
                hK sigma2 T delta defaultAction i history)) <=
          sigma2)
    (harmMean : forall i : Nat,
      forall history : ((j : Finset.Iic i) -> Rat),
        forall arm : Fin K,
          mean (context i history) arm = armMean arm)
    (hT : 0 < T) (hsigma2 : 0 < (((sigma2 : NNReal) : Real)))
    (hdelta : 0 < delta)
    (hgap : 0 < meanGap (fun arm => (armMean arm : Real)) best chosen) :
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
    let generatedAction := selectedPolicySuccessorGeneratedUCBAction
      hK sigma2 T delta defaultAction reward
    let gap := meanGap (fun arm => (armMean arm : Real)) best chosen
    ∫⁻ trajectory,
        (ConditionalExpectationReward.successorArmPullCount
          (generatedAction trajectory) chosen (T + 1) : ENNReal) ∂mu <=
      (selectedPolicySuccessorPullThreshold K sigma2 T delta gap : ENNReal) +
        (T : ENNReal) * ENNReal.ofReal delta := by
  classical
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
  let generatedAction := selectedPolicySuccessorGeneratedUCBAction
    hK sigma2 T delta defaultAction reward
  let gap := meanGap (fun arm => (armMean arm : Real)) best chosen
  have hreward : forall t : Nat,
      Measurable (fun trajectory : Nat -> Prod (Fin K) Rat =>
        reward trajectory t) := by
    intro t
    exact measurable_snd.comp (measurable_pi_apply t)
  have hlarge :=
    measure_selectedPolicySuccessorLargeGapEvent_generatedUCB_le_ennreal_delta_actionRewardTrajMeasure_centeredKernel
      hK mu0 rewardKernel context mean varianceProxy defaultAction best armMean
        sigma2 T delta hcontext hmean law hvariance harmMean hT hsigma2 hdelta
  have hlarge' :
      mu (selectedPolicySuccessorLargeGapEvent
        (selectedPolicySuccessorGeneratedUCBInitializedScoreMaxSource
          hK reward armMean sigma2 T delta defaultAction best)) <=
        ENNReal.ofReal delta := by
    simpa [policy, state, pairContext, pairState, hpairContext, hpairState,
      stepKernel, mu, reward] using hlarge
  have hcount :=
    lintegral_successorArmPullCount_selectedPolicySuccessorGeneratedUCBAction_le_explicitPullThreshold_add_horizon_mul_delta_of_largeGap
      hK mu reward hreward armMean sigma2 T hT delta hdelta
        defaultAction best chosen hgap hlarge'
  simpa [generatedAction, gap] using hcount

/-
Finite-arm ENNReal pseudo-regret assembly on the canonical action/reward pair
trajectory. The generic consumer requests the preceding expected-count bound
only for positive-gap arms; zero-gap terms vanish after weighting.
-/
theorem lintegral_ofReal_pseudoRegret_selectedPolicySuccessorGeneratedUCBRegretAction_le_explicitThresholdSum_actionRewardTrajMeasure_centeredKernel
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
    let reward : (Nat -> Prod (Fin K) Rat) -> RewardTrace Rat :=
      fun trajectory t => (trajectory t).2
    let action := selectedPolicySuccessorGeneratedUCBRegretAction
      model.hK sigma2 T delta defaultAction reward
    ∫⁻ trajectory,
        ENNReal.ofReal
          (((pseudoRegret model (action trajectory) T : Rat) : Real)) ∂mu <=
      (Finset.univ : Finset (Fin K)).sum (fun arm =>
        ENNReal.ofReal (((model.gap arm : Rat) : Real)) *
          ((selectedPolicySuccessorPullThreshold K sigma2 T delta
              (((model.gap arm : Rat) : Real)) : Nat) : ENNReal) +
            ENNReal.ofReal (((model.gap arm : Rat) : Real)) *
              ((T : ENNReal) * ENNReal.ofReal delta)) := by
  classical
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
  let action := selectedPolicySuccessorGeneratedUCBRegretAction
    model.hK sigma2 T delta defaultAction reward
  let bound : Fin K -> ENNReal := fun arm =>
    (selectedPolicySuccessorPullThreshold K sigma2 T delta
        (((model.gap arm : Rat) : Real)) : ENNReal) +
      (T : ENNReal) * ENNReal.ofReal delta
  have hreward : forall t : Nat,
      Measurable (fun trajectory : Nat -> Prod (Fin K) Rat =>
        reward trajectory t) := by
    intro t
    exact measurable_snd.comp (measurable_pi_apply t)
  have hbase :=
    lintegral_ofReal_pseudoRegret_le_sum_gap_mul_bound_of_positiveGap_pullCount
      mu model action
      (fun t =>
        measurable_selectedPolicySuccessorGeneratedUCBRegretAction
          model.hK sigma2 T delta defaultAction reward hreward t)
      T bound
  have hcount : forall arm : Fin K,
      0 < (((model.gap arm : Rat) : Real)) ->
        ∫⁻ trajectory,
            ((pullCount (action trajectory) arm T : Nat) : ENNReal) ∂mu <=
          bound arm := by
    intro arm hgap
    have hmeanGap :
        0 < meanGap (fun a => ((model.mean a : Rat) : Real))
          model.bestArm arm := by
      rwa [modelMeanGap_bestArm_eq_realGap]
    have harm :=
      lintegral_successorArmPullCount_selectedPolicySuccessorGeneratedUCBAction_le_explicitPullThreshold_add_horizon_mul_delta_actionRewardTrajMeasure_centeredKernel
        (hK := model.hK)
        (mu0 := mu0)
        (rewardKernel := rewardKernel)
        (context := context)
        (mean := mean)
        (varianceProxy := varianceProxy)
        (defaultAction := defaultAction)
        (best := model.bestArm)
        (chosen := arm)
        (armMean := model.mean)
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
        (hdelta := hdelta)
        (hgap := hmeanGap)
    simpa only [policy, state, pairContext, pairState, hpairContext, hpairState,
      stepKernel, mu, reward, action, bound,
      modelMeanGap_bestArm_eq_realGap,
      pullCount_selectedPolicySuccessorGeneratedUCBRegretAction_eq] using harm
  refine (hbase hcount).trans_eq ?_
  apply Finset.sum_congr rfl
  intro arm _harm
  simp only [bound, mul_add]

/-
Canonical pair-trajectory textbook gap-sum endpoint. The preceding theorem
supplies the exact gap-weighted explicit thresholds; the compiled finite-arm
algebra filters positive gaps and removes one gap power.
-/
theorem lintegral_ofReal_pseudoRegret_selectedPolicySuccessorGeneratedUCBRegretAction_le_textbookGapSum_actionRewardTrajMeasure_centeredKernel
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
    let reward : (Nat -> Prod (Fin K) Rat) -> RewardTrace Rat :=
      fun trajectory t => (trajectory t).2
    let action := selectedPolicySuccessorGeneratedUCBRegretAction
      model.hK sigma2 T delta defaultAction reward
    ∫⁻ trajectory,
        ENNReal.ofReal
          (((pseudoRegret model (action trajectory) T : Rat) : Real)) ∂mu <=
      ((Finset.univ : Finset (Fin K)).filter (fun arm =>
        0 < (((model.gap arm : Rat) : Real)))).sum (fun arm =>
          ENNReal.ofReal
              (selectedPolicySuccessorTextbookGapBudget K sigma2 T delta
                (((model.gap arm : Rat) : Real))) +
            ENNReal.ofReal (((model.gap arm : Rat) : Real)) *
              ((T : ENNReal) * ENNReal.ofReal delta)) := by
  refine
    (lintegral_ofReal_pseudoRegret_selectedPolicySuccessorGeneratedUCBRegretAction_le_explicitThresholdSum_actionRewardTrajMeasure_centeredKernel
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
      (hdelta := hdelta)).trans ?_
  exact sum_gap_mul_explicitThreshold_add_failure_le_textbookGapSum
    model sigma2 T delta

end UCB
end BanditRLProof
