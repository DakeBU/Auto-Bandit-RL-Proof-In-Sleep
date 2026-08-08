import BanditRLProof.RL.FiniteHorizonNaturalCausalInverseSqrtThresholdCappedUnboundedHittingAfterStoppedAverageSampledReturnExpectedOptimality

/-!
# Stopped sampled-return and successor-policy expected-return consistency

This module gives a literal policy-value interpretation to the stopped
sampled-return theorem.  At coordinate `t`, the successor policy is the actual
exploratory policy selected from the dependent prefix through `t`; its expected
return is the integral of cumulative reward under its generated trajectory
law.  These literal policy returns are averaged over the same natural prefix
as the sampled-return and regret processes, with the optimal initial expected
return at the empty prefix.

The exact same-prefix identity says that sampled return minus successor-policy
expected return is the normalized return deviation.  It is transported to the
capped first-passage approximation and the genuine uncapped `hittingAfter`
prefix, then through Bochner integration.  No expectation is interchanged with
a random stopping index, and no optional-stopping theorem is used.
-/

open Filter MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal ProbabilityTheory Topology BigOperators

namespace BanditRLProof.FiniteHorizonRL

universe u v w

variable {State : Type u} {Action : Type v}
    [MeasurableSpace State] [MeasurableSpace Action]
    [Fintype State] [Fintype Action]
    [DecidableEq State] [DecidableEq Action]
    [MeasurableSingletonClass State] [MeasurableSingletonClass Action]
    [Nonempty State] [Nonempty Action]

namespace HeterogeneousAdaptiveStochasticEpisodeBatchSource

/-- Literal expected cumulative reward of the successor policy selected from
the dependent prefix through `t`. -/
noncomputable def naturalSuccessorPolicyExpectedReturn
    {mdp : MDP State Action} {initialState : Measure State}
    [IsProbabilityMeasure initialState] {episodes : Nat -> Nat}
    (source : HeterogeneousAdaptiveStochasticEpisodeBatchSource
      mdp initialState episodes)
    (trajectory : HeterogeneousStochasticEpisodeBatchTrajectory mdp episodes)
    (t : Nat) : Real :=
  integral
    ((source.successorPolicyAt trajectory t).trajectoryMeasure initialState)
    mdp.cumulativeReward

omit [DecidableEq State] [DecidableEq Action]
    [MeasurableSingletonClass State] [MeasurableSingletonClass Action]
    [Nonempty State] in
/-- The literal successor-policy return is optimal value minus that policy's
expected regret. -/
theorem naturalSuccessorPolicyExpectedReturn_eq_optimal_sub_expectedRegret
    {mdp : MDP State Action} {initialState : Measure State}
    [IsProbabilityMeasure initialState] {episodes : Nat -> Nat}
    (source : HeterogeneousAdaptiveStochasticEpisodeBatchSource
      mdp initialState episodes)
    (trajectory : HeterogeneousStochasticEpisodeBatchTrajectory mdp episodes)
    (t : Nat) :
    source.naturalSuccessorPolicyExpectedReturn trajectory t =
      AdaptiveStochasticEpisodeBatchSource.optimalInitialExpectedReturn
          mdp initialState -
        (source.successorPolicyAt trajectory t).expectedRegret initialState := by
  unfold naturalSuccessorPolicyExpectedReturn MarkovPolicy.expectedRegret
    AdaptiveStochasticEpisodeBatchSource.optimalInitialExpectedReturn
  ring

/-- Equal-round average of literal successor-policy expected returns.  The
empty prefix uses the optimal initial expected return. -/
noncomputable def naturalAverageSuccessorPolicyExpectedReturn
    {mdp : MDP State Action} {initialState : Measure State}
    [IsProbabilityMeasure initialState] {episodes : Nat -> Nat}
    (source : HeterogeneousAdaptiveStochasticEpisodeBatchSource
      mdp initialState episodes)
    (trajectory : HeterogeneousStochasticEpisodeBatchTrajectory mdp episodes)
    (rounds : Nat) : Real :=
  if rounds = 0 then
    AdaptiveStochasticEpisodeBatchSource.optimalInitialExpectedReturn
      mdp initialState
  else
    (∑ t ∈ Finset.range rounds,
      source.naturalSuccessorPolicyExpectedReturn trajectory t) /
        (rounds : Real)

omit [DecidableEq State] [DecidableEq Action]
    [MeasurableSingletonClass State] [MeasurableSingletonClass Action]
    [Nonempty State] in
/-- At every prefix, the literal policy-return average is optimal value minus
the average successor-policy expected regret. -/
theorem naturalAverageSuccessorPolicyExpectedReturn_eq_optimal_sub_expectedRegret
    {mdp : MDP State Action} {initialState : Measure State}
    [IsProbabilityMeasure initialState] {episodes : Nat -> Nat}
    (source : HeterogeneousAdaptiveStochasticEpisodeBatchSource
      mdp initialState episodes)
    (trajectory : HeterogeneousStochasticEpisodeBatchTrajectory mdp episodes)
    (rounds : Nat) :
    source.naturalAverageSuccessorPolicyExpectedReturn trajectory rounds =
      AdaptiveStochasticEpisodeBatchSource.optimalInitialExpectedReturn
          mdp initialState -
        (∑ t ∈ Finset.range rounds,
          (source.successorPolicyAt trajectory t).expectedRegret initialState) /
            (rounds : Real) := by
  by_cases hrounds : rounds = 0
  · subst rounds
    simp [naturalAverageSuccessorPolicyExpectedReturn]
  · have hroundsReal : (rounds : Real) ≠ 0 := by
      exact_mod_cast hrounds
    simp only [naturalAverageSuccessorPolicyExpectedReturn, hrounds, if_false]
    rw [show (∑ t ∈ Finset.range rounds,
        source.naturalSuccessorPolicyExpectedReturn trajectory t) =
          ∑ t ∈ Finset.range rounds,
            (AdaptiveStochasticEpisodeBatchSource.optimalInitialExpectedReturn
                mdp initialState -
              (source.successorPolicyAt trajectory t).expectedRegret
                initialState) by
      apply Finset.sum_congr rfl
      intro t _
      exact source.naturalSuccessorPolicyExpectedReturn_eq_optimal_sub_expectedRegret
        trajectory t]
    rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range,
      nsmul_eq_mul, sub_div, mul_div_cancel_left₀ _ hroundsReal]

end HeterogeneousAdaptiveStochasticEpisodeBatchSource

namespace AdaptiveStochasticSampledEmpiricalOptimisticSource

/-- Natural-prefix average of literal expected returns of the actual
successor policies selected by the self-consistent causal source. -/
noncomputable def
    selfConsistentScheduledNaturalCausalAverageSuccessorPolicyExpectedReturnProcess
    (mdp : MDP State Action) (initialState : Measure State)
    [IsProbabilityMeasure initialState]
    (rewardSource : mdp.MeanCompatibleRewardKernel)
    (initialTable : DeterministicMarkovPolicyTable mdp)
    (defaultState : State) (varianceProxy : NNReal)
    (baseVisitFloor : Real) (rounds : Nat) :
    HeterogeneousStochasticEpisodeBatchTrajectory mdp
        (fun t =>
          AdaptiveStochasticEpisodeBatchSource.selfConsistentScheduledEpisodes
            mdp varianceProxy baseVisitFloor t) -> Real :=
  let source := selfConsistentScheduledCausalSource mdp initialState
    rewardSource initialTable defaultState varianceProxy baseVisitFloor
  fun trajectory =>
    source.naturalAverageSuccessorPolicyExpectedReturn trajectory rounds

/-- The literal prefix policy return is the complement of the existing
average behavior expected-regret process. -/
theorem
    selfConsistentScheduledNaturalCausalAverageSuccessorPolicyExpectedReturnProcess_eq_optimal_sub_behaviorExpected
    (mdp : MDP State Action) (initialState : Measure State)
    [IsProbabilityMeasure initialState]
    (rewardSource : mdp.MeanCompatibleRewardKernel)
    (initialTable : DeterministicMarkovPolicyTable mdp)
    (defaultState : State) (varianceProxy : NNReal)
    (baseVisitFloor : Real) (rounds : Nat) (trajectory) :
    selfConsistentScheduledNaturalCausalAverageSuccessorPolicyExpectedReturnProcess
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor rounds trajectory =
      AdaptiveStochasticEpisodeBatchSource.optimalInitialExpectedReturn
          mdp initialState -
        selfConsistentScheduledNaturalCausalAverageBehaviorExpectedRegretProcess
          mdp initialState rewardSource initialTable defaultState varianceProxy
            baseVisitFloor rounds trajectory := by
  let source := selfConsistentScheduledCausalSource mdp initialState
    rewardSource initialTable defaultState varianceProxy baseVisitFloor
  simpa [
    selfConsistentScheduledNaturalCausalAverageSuccessorPolicyExpectedReturnProcess,
    selfConsistentScheduledNaturalCausalAverageBehaviorExpectedRegretProcess,
    selfConsistentScheduledNaturalCausalCumulativeBehaviorExpectedRegretProcess,
    selfConsistentScheduledNaturalCausalSuccessorPolicyExpectedRegretProcess,
    source] using
      source.naturalAverageSuccessorPolicyExpectedReturn_eq_optimal_sub_expectedRegret
        trajectory rounds

/-- Every deterministic-prefix literal policy-return coordinate is
measurable. -/
theorem
    measurable_selfConsistentScheduledNaturalCausalAverageSuccessorPolicyExpectedReturnProcess
    (mdp : MDP State Action) (initialState : Measure State)
    [IsProbabilityMeasure initialState]
    (rewardSource : mdp.MeanCompatibleRewardKernel)
    (initialTable : DeterministicMarkovPolicyTable mdp)
    (defaultState : State) (varianceProxy : NNReal)
    (baseVisitFloor : Real) (rounds : Nat) :
    Measurable
      (selfConsistentScheduledNaturalCausalAverageSuccessorPolicyExpectedReturnProcess
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor rounds) := by
  rw [show
      selfConsistentScheduledNaturalCausalAverageSuccessorPolicyExpectedReturnProcess
          mdp initialState rewardSource initialTable defaultState varianceProxy
            baseVisitFloor rounds =
        fun trajectory =>
          AdaptiveStochasticEpisodeBatchSource.optimalInitialExpectedReturn
              mdp initialState -
            selfConsistentScheduledNaturalCausalAverageBehaviorExpectedRegretProcess
              mdp initialState rewardSource initialTable defaultState
                varianceProxy baseVisitFloor rounds trajectory by
    funext trajectory
    exact
      selfConsistentScheduledNaturalCausalAverageSuccessorPolicyExpectedReturnProcess_eq_optimal_sub_behaviorExpected
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor rounds trajectory]
  exact measurable_const.sub
    (measurable_selfConsistentScheduledNaturalCausalAverageBehaviorExpectedRegretProcess
      mdp initialState rewardSource initialTable defaultState varianceProxy
        baseVisitFloor rounds)

/-- Literal average successor-policy expected return evaluated at a
`WithTop Nat` stopping prefix. -/
noncomputable def
    selfConsistentScheduledNaturalCausalStoppingTimeAverageSuccessorPolicyExpectedReturnProcess
    (mdp : MDP State Action) (initialState : Measure State)
    [IsProbabilityMeasure initialState]
    (rewardSource : mdp.MeanCompatibleRewardKernel)
    (initialTable : DeterministicMarkovPolicyTable mdp)
    (defaultState : State) (varianceProxy : NNReal)
    (baseVisitFloor : Real)
    (stoppingPrefix : Nat ->
      HeterogeneousStochasticEpisodeBatchTrajectory mdp
        (fun t =>
          AdaptiveStochasticEpisodeBatchSource.selfConsistentScheduledEpisodes
            mdp varianceProxy baseVisitFloor t) -> WithTop Nat)
    (scheduleIndex : Nat) :
    HeterogeneousStochasticEpisodeBatchTrajectory mdp
        (fun t =>
          AdaptiveStochasticEpisodeBatchSource.selfConsistentScheduledEpisodes
            mdp varianceProxy baseVisitFloor t) -> Real :=
  stoppedValue
    (selfConsistentScheduledNaturalCausalAverageSuccessorPolicyExpectedReturnProcess
      mdp initialState rewardSource initialTable defaultState varianceProxy
        baseVisitFloor)
    (stoppingPrefix scheduleIndex)

@[simp]
theorem
    selfConsistentScheduledNaturalCausalStoppingTimeAverageSuccessorPolicyExpectedReturnProcess_apply
    (mdp : MDP State Action) (initialState : Measure State)
    [IsProbabilityMeasure initialState]
    (rewardSource : mdp.MeanCompatibleRewardKernel)
    (initialTable : DeterministicMarkovPolicyTable mdp)
    (defaultState : State) (varianceProxy : NNReal)
    (baseVisitFloor : Real)
    (stoppingPrefix : Nat ->
      HeterogeneousStochasticEpisodeBatchTrajectory mdp
        (fun t =>
          AdaptiveStochasticEpisodeBatchSource.selfConsistentScheduledEpisodes
            mdp varianceProxy baseVisitFloor t) -> WithTop Nat)
    (scheduleIndex : Nat) (trajectory) :
    selfConsistentScheduledNaturalCausalStoppingTimeAverageSuccessorPolicyExpectedReturnProcess
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor stoppingPrefix scheduleIndex trajectory =
      selfConsistentScheduledNaturalCausalAverageSuccessorPolicyExpectedReturnProcess
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor (stoppingPrefix scheduleIndex trajectory).untopA
            trajectory :=
  rfl

/-- Stopping preserves the exact literal policy-return/behavior-regret
complement. -/
theorem
    selfConsistentScheduledNaturalCausalStoppingTimeAverageSuccessorPolicyExpectedReturnProcess_eq_optimal_sub_behaviorExpected
    (mdp : MDP State Action) (initialState : Measure State)
    [IsProbabilityMeasure initialState]
    (rewardSource : mdp.MeanCompatibleRewardKernel)
    (initialTable : DeterministicMarkovPolicyTable mdp)
    (defaultState : State) (varianceProxy : NNReal)
    (baseVisitFloor : Real)
    (stoppingPrefix : Nat ->
      HeterogeneousStochasticEpisodeBatchTrajectory mdp
        (fun t =>
          AdaptiveStochasticEpisodeBatchSource.selfConsistentScheduledEpisodes
            mdp varianceProxy baseVisitFloor t) -> WithTop Nat)
    (scheduleIndex : Nat) (trajectory) :
    selfConsistentScheduledNaturalCausalStoppingTimeAverageSuccessorPolicyExpectedReturnProcess
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor stoppingPrefix scheduleIndex trajectory =
      AdaptiveStochasticEpisodeBatchSource.optimalInitialExpectedReturn
          mdp initialState -
        selfConsistentScheduledNaturalCausalStoppingTimeAverageBehaviorExpectedRegretProcess
          mdp initialState rewardSource initialTable defaultState varianceProxy
            baseVisitFloor stoppingPrefix scheduleIndex trajectory := by
  simp only [
    selfConsistentScheduledNaturalCausalStoppingTimeAverageSuccessorPolicyExpectedReturnProcess_apply,
    selfConsistentScheduledNaturalCausalStoppingTimeAverageBehaviorExpectedRegretProcess_apply]
  exact
    selfConsistentScheduledNaturalCausalAverageSuccessorPolicyExpectedReturnProcess_eq_optimal_sub_behaviorExpected
      mdp initialState rewardSource initialTable defaultState varianceProxy
        baseVisitFloor _ trajectory

/-- A stopping time gives a measurable stopped literal policy-return
coordinate. -/
theorem
    measurable_selfConsistentScheduledNaturalCausalStoppingTimeAverageSuccessorPolicyExpectedReturnProcess
    (mdp : MDP State Action) (initialState : Measure State)
    [IsProbabilityMeasure initialState]
    (rewardSource : mdp.MeanCompatibleRewardKernel)
    (initialTable : DeterministicMarkovPolicyTable mdp)
    (defaultState : State) (varianceProxy : NNReal)
    (baseVisitFloor : Real)
    (stoppingPrefix : Nat ->
      HeterogeneousStochasticEpisodeBatchTrajectory mdp
        (fun t =>
          AdaptiveStochasticEpisodeBatchSource.selfConsistentScheduledEpisodes
            mdp varianceProxy baseVisitFloor t) -> WithTop Nat)
    (scheduleIndex : Nat)
    (hstopping : IsStoppingTime
      (selfConsistentScheduledNaturalCausalTrajectoryFiltration mdp initialState
        rewardSource initialTable defaultState varianceProxy baseVisitFloor)
      (stoppingPrefix scheduleIndex)) :
    Measurable
      (selfConsistentScheduledNaturalCausalStoppingTimeAverageSuccessorPolicyExpectedReturnProcess
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor stoppingPrefix scheduleIndex) := by
  rw [show
      selfConsistentScheduledNaturalCausalStoppingTimeAverageSuccessorPolicyExpectedReturnProcess
          mdp initialState rewardSource initialTable defaultState varianceProxy
            baseVisitFloor stoppingPrefix scheduleIndex =
        fun trajectory =>
          AdaptiveStochasticEpisodeBatchSource.optimalInitialExpectedReturn
              mdp initialState -
            selfConsistentScheduledNaturalCausalStoppingTimeAverageBehaviorExpectedRegretProcess
              mdp initialState rewardSource initialTable defaultState
                varianceProxy baseVisitFloor stoppingPrefix scheduleIndex
                  trajectory by
    funext trajectory
    exact
      selfConsistentScheduledNaturalCausalStoppingTimeAverageSuccessorPolicyExpectedReturnProcess_eq_optimal_sub_behaviorExpected
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor stoppingPrefix scheduleIndex trajectory]
  exact measurable_const.sub
    (measurable_selfConsistentScheduledNaturalCausalStoppingTimeAverageBehaviorExpectedRegretProcess
      mdp initialState rewardSource initialTable defaultState varianceProxy
        baseVisitFloor stoppingPrefix scheduleIndex hstopping)

/-- Integrability transfers from a stopped behavior expected-regret process to
its literal policy-return complement. -/
theorem integrable_stoppedSuccessorPolicyExpectedReturn_of_integrable_behavior
    {Omega : Type w} [MeasurableSpace Omega] (mu : Measure Omega)
    [IsFiniteMeasure mu]
    (optimal : Real) (policyReturn behaviorRegret : Omega -> Real)
    (hpoint : forall omega, policyReturn omega = optimal - behaviorRegret omega)
    (hbehavior : Integrable behaviorRegret mu) :
    Integrable policyReturn mu := by
  rw [show policyReturn = fun omega => optimal - behaviorRegret omega by
    funext omega
    exact hpoint omega]
  exact (integrable_const optimal).sub hbehavior

/-- The expectation of a stopped literal policy return is the optimal
constant minus the expected behavior regret. -/
theorem integral_stoppedSuccessorPolicyExpectedReturn_eq_optimal_sub_behavior
    {Omega : Type w} [MeasurableSpace Omega] (mu : Measure Omega)
    [IsProbabilityMeasure mu]
    (optimal : Real) (policyReturn behaviorRegret : Omega -> Real)
    (hpoint : forall omega, policyReturn omega = optimal - behaviorRegret omega)
    (hbehavior : Integrable behaviorRegret mu) :
    integral mu policyReturn = optimal - integral mu behaviorRegret := by
  rw [show policyReturn = fun omega => optimal - behaviorRegret omega by
    funext omega
    exact hpoint omega]
  rw [integral_sub (integrable_const optimal) hbehavior, integral_const]
  simp

/-- At any common stopping prefix, observed sampled return minus the literal
successor-policy expected return is exactly the normalized return deviation. -/
theorem
    selfConsistentScheduledNaturalCausalStoppingTimeAverageSampledReturn_sub_successorPolicyExpectedReturn_eq_returnDeviation
    (mdp : MDP State Action) (initialState : Measure State)
    [IsProbabilityMeasure initialState]
    (rewardSource : mdp.MeanCompatibleRewardKernel)
    (initialTable : DeterministicMarkovPolicyTable mdp)
    (defaultState : State) (varianceProxy : NNReal)
    (baseVisitFloor : Real)
    (stoppingPrefix : Nat ->
      HeterogeneousStochasticEpisodeBatchTrajectory mdp
        (fun t =>
          AdaptiveStochasticEpisodeBatchSource.selfConsistentScheduledEpisodes
            mdp varianceProxy baseVisitFloor t) -> WithTop Nat)
    (scheduleIndex : Nat) (trajectory) :
    selfConsistentScheduledNaturalCausalStoppingTimeAverageSampledReturnProcess
          mdp initialState rewardSource initialTable defaultState varianceProxy
            baseVisitFloor stoppingPrefix scheduleIndex trajectory -
        selfConsistentScheduledNaturalCausalStoppingTimeAverageSuccessorPolicyExpectedReturnProcess
          mdp initialState rewardSource initialTable defaultState varianceProxy
            baseVisitFloor stoppingPrefix scheduleIndex trajectory =
      selfConsistentScheduledNaturalCausalStoppingTimeAverageReturnDeviationProcess
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor stoppingPrefix scheduleIndex trajectory := by
  rw [
    selfConsistentScheduledNaturalCausalStoppingTimeAverageSampledReturnProcess_eq_optimal_sub_realized,
    selfConsistentScheduledNaturalCausalStoppingTimeAverageSuccessorPolicyExpectedReturnProcess_eq_optimal_sub_behaviorExpected,
    selfConsistentScheduledNaturalCausalStoppingTimeAverageRealizedBehaviorRegretProcess_eq_behaviorExpected_sub_returnDeviation]
  ring

/-- Every capped stopped literal successor-policy expected-return coordinate
is measurable. -/
theorem
    measurable_selfConsistentScheduledNaturalCausalInverseSqrtThresholdCappedStoppedAverageSuccessorPolicyExpectedReturn
    (mdp : MDP State Action) (initialState : Measure State)
    [IsProbabilityMeasure initialState]
    (rewardSource : mdp.MeanCompatibleRewardKernel)
    (initialTable : DeterministicMarkovPolicyTable mdp)
    (defaultState : State) (varianceProxy : NNReal)
    (baseVisitFloor : Real) (scheduleIndex : Nat) :
    Measurable
      (selfConsistentScheduledNaturalCausalStoppingTimeAverageSuccessorPolicyExpectedReturnProcess
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor
          (selfConsistentScheduledNaturalCausalInverseSqrtThresholdCappedDoubleLinearRawWindowFirstPassageStoppingPrefix
            mdp initialState rewardSource initialTable defaultState varianceProxy
              baseVisitFloor)
          scheduleIndex) := by
  exact
    measurable_selfConsistentScheduledNaturalCausalStoppingTimeAverageSuccessorPolicyExpectedReturnProcess
      mdp initialState rewardSource initialTable defaultState varianceProxy
        baseVisitFloor _ scheduleIndex (by
          simpa [
            selfConsistentScheduledNaturalCausalInverseSqrtThresholdCappedDoubleLinearRawWindowFirstPassageStoppingPrefix] using
            (selfConsistentScheduledNaturalCausalCappedDoubleLinearRawWindowFirstPassageStoppingPrefix_isStoppingTime
              mdp initialState rewardSource initialTable defaultState
                varianceProxy baseVisitFloor
                  selfConsistentScheduledNaturalCausalInverseSqrtFirstPassageThreshold
                    scheduleIndex))

/-- Every genuine uncapped stopped literal successor-policy expected-return
coordinate is measurable. -/
theorem
    measurable_selfConsistentScheduledNaturalCausalInverseSqrtThresholdUnboundedHittingAfterStoppedAverageSuccessorPolicyExpectedReturn
    (mdp : MDP State Action) (initialState : Measure State)
    [IsProbabilityMeasure initialState]
    (rewardSource : mdp.MeanCompatibleRewardKernel)
    (initialTable : DeterministicMarkovPolicyTable mdp)
    (defaultState : State) (varianceProxy : NNReal)
    (baseVisitFloor : Real) (scheduleIndex : Nat) :
    Measurable
      (selfConsistentScheduledNaturalCausalStoppingTimeAverageSuccessorPolicyExpectedReturnProcess
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor
          (selfConsistentScheduledNaturalCausalInverseSqrtThresholdUnboundedHittingAfterStoppingPrefix
            mdp initialState rewardSource initialTable defaultState varianceProxy
              baseVisitFloor)
          scheduleIndex) := by
  exact
    measurable_selfConsistentScheduledNaturalCausalStoppingTimeAverageSuccessorPolicyExpectedReturnProcess
      mdp initialState rewardSource initialTable defaultState varianceProxy
        baseVisitFloor _ scheduleIndex
        (selfConsistentScheduledNaturalCausalInverseSqrtThresholdUnboundedHittingAfterStoppingPrefix_isStoppingTime
          mdp initialState rewardSource initialTable defaultState varianceProxy
            baseVisitFloor scheduleIndex)

/-- The capped stopped literal successor-policy expected return is
integrable. -/
theorem
    integrable_selfConsistentScheduledNaturalCausalInverseSqrtThresholdCappedStoppedAverageSuccessorPolicyExpectedReturn
    (mdp : MDP State Action) (initialState : Measure State)
    [IsProbabilityMeasure initialState]
    (rewardSource : mdp.MeanCompatibleRewardKernel)
    (initialTable : DeterministicMarkovPolicyTable mdp)
    (defaultState : State) (varianceProxy : NNReal)
    (baseVisitFloor : Real)
    (hrewardBound : forall state action, |mdp.reward state action| <= 1)
    (scheduleIndex : Nat) :
    let source := selfConsistentScheduledCausalSource mdp initialState
      rewardSource initialTable defaultState varianceProxy baseVisitFloor
    let stoppingPrefix :=
      selfConsistentScheduledNaturalCausalInverseSqrtThresholdCappedDoubleLinearRawWindowFirstPassageStoppingPrefix
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor
    let policyReturn :=
      selfConsistentScheduledNaturalCausalStoppingTimeAverageSuccessorPolicyExpectedReturnProcess
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor stoppingPrefix
    Integrable (policyReturn scheduleIndex) source.trajectoryMeasure := by
  dsimp only
  apply
    integrable_stoppedSuccessorPolicyExpectedReturn_of_integrable_behavior
      (selfConsistentScheduledCausalSource mdp initialState rewardSource
        initialTable defaultState varianceProxy baseVisitFloor).trajectoryMeasure
      (AdaptiveStochasticEpisodeBatchSource.optimalInitialExpectedReturn
        mdp initialState)
      (selfConsistentScheduledNaturalCausalStoppingTimeAverageSuccessorPolicyExpectedReturnProcess
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor
          (selfConsistentScheduledNaturalCausalInverseSqrtThresholdCappedDoubleLinearRawWindowFirstPassageStoppingPrefix
            mdp initialState rewardSource initialTable defaultState varianceProxy
              baseVisitFloor) scheduleIndex)
      (selfConsistentScheduledNaturalCausalStoppingTimeAverageBehaviorExpectedRegretProcess
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor
          (selfConsistentScheduledNaturalCausalInverseSqrtThresholdCappedDoubleLinearRawWindowFirstPassageStoppingPrefix
            mdp initialState rewardSource initialTable defaultState varianceProxy
              baseVisitFloor) scheduleIndex)
  · intro trajectory
    exact
      selfConsistentScheduledNaturalCausalStoppingTimeAverageSuccessorPolicyExpectedReturnProcess_eq_optimal_sub_behaviorExpected
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor
          (selfConsistentScheduledNaturalCausalInverseSqrtThresholdCappedDoubleLinearRawWindowFirstPassageStoppingPrefix
            mdp initialState rewardSource initialTable defaultState varianceProxy
              baseVisitFloor) scheduleIndex trajectory
  · exact
      (memLp_one_selfConsistentScheduledNaturalCausalInverseSqrtThresholdCappedStoppedBehaviorExpectedRegret
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor hrewardBound scheduleIndex).integrable (by norm_num)

/-- The genuine uncapped stopped literal successor-policy expected return is
integrable. -/
theorem
    integrable_selfConsistentScheduledNaturalCausalInverseSqrtThresholdUnboundedHittingAfterStoppedAverageSuccessorPolicyExpectedReturn
    (mdp : MDP State Action) (initialState : Measure State)
    [IsProbabilityMeasure initialState]
    (rewardSource : mdp.MeanCompatibleRewardKernel)
    (initialTable : DeterministicMarkovPolicyTable mdp)
    (defaultState : State) (varianceProxy : NNReal)
    (baseVisitFloor : Real)
    (hrewardBound : forall state action, |mdp.reward state action| <= 1)
    (scheduleIndex : Nat) :
    let source := selfConsistentScheduledCausalSource mdp initialState
      rewardSource initialTable defaultState varianceProxy baseVisitFloor
    let stoppingPrefix :=
      selfConsistentScheduledNaturalCausalInverseSqrtThresholdUnboundedHittingAfterStoppingPrefix
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor
    let policyReturn :=
      selfConsistentScheduledNaturalCausalStoppingTimeAverageSuccessorPolicyExpectedReturnProcess
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor stoppingPrefix
    Integrable (policyReturn scheduleIndex) source.trajectoryMeasure := by
  dsimp only
  apply
    integrable_stoppedSuccessorPolicyExpectedReturn_of_integrable_behavior
      (selfConsistentScheduledCausalSource mdp initialState rewardSource
        initialTable defaultState varianceProxy baseVisitFloor).trajectoryMeasure
      (AdaptiveStochasticEpisodeBatchSource.optimalInitialExpectedReturn
        mdp initialState)
      (selfConsistentScheduledNaturalCausalStoppingTimeAverageSuccessorPolicyExpectedReturnProcess
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor
          (selfConsistentScheduledNaturalCausalInverseSqrtThresholdUnboundedHittingAfterStoppingPrefix
            mdp initialState rewardSource initialTable defaultState varianceProxy
              baseVisitFloor) scheduleIndex)
      (selfConsistentScheduledNaturalCausalStoppingTimeAverageBehaviorExpectedRegretProcess
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor
          (selfConsistentScheduledNaturalCausalInverseSqrtThresholdUnboundedHittingAfterStoppingPrefix
            mdp initialState rewardSource initialTable defaultState varianceProxy
              baseVisitFloor) scheduleIndex)
  · intro trajectory
    exact
      selfConsistentScheduledNaturalCausalStoppingTimeAverageSuccessorPolicyExpectedReturnProcess_eq_optimal_sub_behaviorExpected
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor
          (selfConsistentScheduledNaturalCausalInverseSqrtThresholdUnboundedHittingAfterStoppingPrefix
            mdp initialState rewardSource initialTable defaultState varianceProxy
              baseVisitFloor) scheduleIndex trajectory
  · exact
      (memLp_one_selfConsistentScheduledNaturalCausalInverseSqrtThresholdUnboundedHittingAfterStoppedBehaviorExpectedRegret
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor hrewardBound scheduleIndex).integrable (by norm_num)

/-- For the capped prefix, expected literal policy return is exactly optimal
value minus expected behavior regret. -/
theorem
    selfConsistentScheduledNaturalCausalInverseSqrtThresholdCappedStoppedAverageSuccessorPolicyExpectedReturnIntegral_eq_optimal_sub_behaviorExpected
    (mdp : MDP State Action) (initialState : Measure State)
    [IsProbabilityMeasure initialState]
    (rewardSource : mdp.MeanCompatibleRewardKernel)
    (initialTable : DeterministicMarkovPolicyTable mdp)
    (defaultState : State) (varianceProxy : NNReal)
    (baseVisitFloor : Real)
    (hrewardBound : forall state action, |mdp.reward state action| <= 1)
    (scheduleIndex : Nat) :
    let source := selfConsistentScheduledCausalSource mdp initialState
      rewardSource initialTable defaultState varianceProxy baseVisitFloor
    let stoppingPrefix :=
      selfConsistentScheduledNaturalCausalInverseSqrtThresholdCappedDoubleLinearRawWindowFirstPassageStoppingPrefix
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor
    let policyReturn :=
      selfConsistentScheduledNaturalCausalStoppingTimeAverageSuccessorPolicyExpectedReturnProcess
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor stoppingPrefix
    let behaviorRegret :=
      selfConsistentScheduledNaturalCausalStoppingTimeAverageBehaviorExpectedRegretProcess
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor stoppingPrefix
    integral source.trajectoryMeasure (policyReturn scheduleIndex) =
      AdaptiveStochasticEpisodeBatchSource.optimalInitialExpectedReturn
          mdp initialState -
        integral source.trajectoryMeasure (behaviorRegret scheduleIndex) := by
  dsimp only
  apply
    integral_stoppedSuccessorPolicyExpectedReturn_eq_optimal_sub_behavior
      (selfConsistentScheduledCausalSource mdp initialState rewardSource
        initialTable defaultState varianceProxy baseVisitFloor).trajectoryMeasure
      (AdaptiveStochasticEpisodeBatchSource.optimalInitialExpectedReturn
        mdp initialState)
  · intro trajectory
    exact
      selfConsistentScheduledNaturalCausalStoppingTimeAverageSuccessorPolicyExpectedReturnProcess_eq_optimal_sub_behaviorExpected
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor
          (selfConsistentScheduledNaturalCausalInverseSqrtThresholdCappedDoubleLinearRawWindowFirstPassageStoppingPrefix
            mdp initialState rewardSource initialTable defaultState varianceProxy
              baseVisitFloor) scheduleIndex trajectory
  · exact
      (memLp_one_selfConsistentScheduledNaturalCausalInverseSqrtThresholdCappedStoppedBehaviorExpectedRegret
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor hrewardBound scheduleIndex).integrable (by norm_num)

/-- For the genuine uncapped prefix, expected literal policy return is exactly
optimal value minus expected behavior regret. -/
theorem
    selfConsistentScheduledNaturalCausalInverseSqrtThresholdUnboundedHittingAfterStoppedAverageSuccessorPolicyExpectedReturnIntegral_eq_optimal_sub_behaviorExpected
    (mdp : MDP State Action) (initialState : Measure State)
    [IsProbabilityMeasure initialState]
    (rewardSource : mdp.MeanCompatibleRewardKernel)
    (initialTable : DeterministicMarkovPolicyTable mdp)
    (defaultState : State) (varianceProxy : NNReal)
    (baseVisitFloor : Real)
    (hrewardBound : forall state action, |mdp.reward state action| <= 1)
    (scheduleIndex : Nat) :
    let source := selfConsistentScheduledCausalSource mdp initialState
      rewardSource initialTable defaultState varianceProxy baseVisitFloor
    let stoppingPrefix :=
      selfConsistentScheduledNaturalCausalInverseSqrtThresholdUnboundedHittingAfterStoppingPrefix
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor
    let policyReturn :=
      selfConsistentScheduledNaturalCausalStoppingTimeAverageSuccessorPolicyExpectedReturnProcess
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor stoppingPrefix
    let behaviorRegret :=
      selfConsistentScheduledNaturalCausalStoppingTimeAverageBehaviorExpectedRegretProcess
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor stoppingPrefix
    integral source.trajectoryMeasure (policyReturn scheduleIndex) =
      AdaptiveStochasticEpisodeBatchSource.optimalInitialExpectedReturn
          mdp initialState -
        integral source.trajectoryMeasure (behaviorRegret scheduleIndex) := by
  dsimp only
  apply
    integral_stoppedSuccessorPolicyExpectedReturn_eq_optimal_sub_behavior
      (selfConsistentScheduledCausalSource mdp initialState rewardSource
        initialTable defaultState varianceProxy baseVisitFloor).trajectoryMeasure
      (AdaptiveStochasticEpisodeBatchSource.optimalInitialExpectedReturn
        mdp initialState)
  · intro trajectory
    exact
      selfConsistentScheduledNaturalCausalStoppingTimeAverageSuccessorPolicyExpectedReturnProcess_eq_optimal_sub_behaviorExpected
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor
          (selfConsistentScheduledNaturalCausalInverseSqrtThresholdUnboundedHittingAfterStoppingPrefix
            mdp initialState rewardSource initialTable defaultState varianceProxy
              baseVisitFloor) scheduleIndex trajectory
  · exact
      (memLp_one_selfConsistentScheduledNaturalCausalInverseSqrtThresholdUnboundedHittingAfterStoppedBehaviorExpectedRegret
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor hrewardBound scheduleIndex).integrable (by norm_num)

/-- At the capped prefix, the expected sampled/policy-return gap is exactly
the expected return deviation. -/
theorem
    selfConsistentScheduledNaturalCausalInverseSqrtThresholdCappedStoppedAverageSampledReturnIntegral_sub_successorPolicyExpectedReturnIntegral_eq_returnDeviationIntegral
    (mdp : MDP State Action) (initialState : Measure State)
    [IsProbabilityMeasure initialState]
    [StandardBorelSpace State] [StandardBorelSpace Action]
    (rewardSource : mdp.MeanCompatibleRewardKernel)
    (varianceProxy : NNReal) (hvarianceProxy : 0 < varianceProxy)
    (law : rewardSource.UniformSubgaussianRewardLaw varianceProxy)
    (initialTable : DeterministicMarkovPolicyTable mdp)
    (defaultState : State)
    (support : ExploratoryPathSupport mdp initialState)
    (baseVisitFloor : Real)
    (hbaseFloor : ExploratoryPathUniformVisitFloor support 1 baseVisitFloor)
    (hrewardBound : forall state action, |mdp.reward state action| <= 1)
    (hhorizon : 4 < mdp.horizon) (hbaseVisitFloor : 0 < baseVisitFloor)
    (scheduleIndex : Nat) :
    let source := selfConsistentScheduledCausalSource mdp initialState
      rewardSource initialTable defaultState varianceProxy baseVisitFloor
    let stoppingPrefix :=
      selfConsistentScheduledNaturalCausalInverseSqrtThresholdCappedDoubleLinearRawWindowFirstPassageStoppingPrefix
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor
    let sampledReturn :=
      selfConsistentScheduledNaturalCausalStoppingTimeAverageSampledReturnProcess
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor stoppingPrefix
    let policyReturn :=
      selfConsistentScheduledNaturalCausalStoppingTimeAverageSuccessorPolicyExpectedReturnProcess
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor stoppingPrefix
    let returnDeviation :=
      selfConsistentScheduledNaturalCausalStoppingTimeAverageReturnDeviationProcess
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor stoppingPrefix
    integral source.trajectoryMeasure (sampledReturn scheduleIndex) -
        integral source.trajectoryMeasure (policyReturn scheduleIndex) =
      integral source.trajectoryMeasure (returnDeviation scheduleIndex) := by
  dsimp only
  have hsampled :=
    integrable_selfConsistentScheduledNaturalCausalInverseSqrtThresholdCappedStoppedAverageSampledReturn
      mdp initialState rewardSource varianceProxy hvarianceProxy law initialTable
        defaultState support baseVisitFloor hbaseFloor hrewardBound hhorizon
          hbaseVisitFloor scheduleIndex
  have hpolicy :=
    integrable_selfConsistentScheduledNaturalCausalInverseSqrtThresholdCappedStoppedAverageSuccessorPolicyExpectedReturn
      mdp initialState rewardSource initialTable defaultState varianceProxy
        baseVisitFloor hrewardBound scheduleIndex
  rw [← integral_sub hsampled hpolicy]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun trajectory =>
    selfConsistentScheduledNaturalCausalStoppingTimeAverageSampledReturn_sub_successorPolicyExpectedReturn_eq_returnDeviation
      mdp initialState rewardSource initialTable defaultState varianceProxy
        baseVisitFloor
        (selfConsistentScheduledNaturalCausalInverseSqrtThresholdCappedDoubleLinearRawWindowFirstPassageStoppingPrefix
          mdp initialState rewardSource initialTable defaultState varianceProxy
            baseVisitFloor) scheduleIndex trajectory

/-- At the genuine uncapped prefix, the expected sampled/policy-return gap is
exactly the expected return deviation. -/
theorem
    selfConsistentScheduledNaturalCausalInverseSqrtThresholdUnboundedHittingAfterStoppedAverageSampledReturnIntegral_sub_successorPolicyExpectedReturnIntegral_eq_returnDeviationIntegral
    (mdp : MDP State Action) (initialState : Measure State)
    [IsProbabilityMeasure initialState]
    [StandardBorelSpace State] [StandardBorelSpace Action]
    (rewardSource : mdp.MeanCompatibleRewardKernel)
    (varianceProxy : NNReal) (hvarianceProxy : 0 < varianceProxy)
    (law : rewardSource.UniformSubgaussianRewardLaw varianceProxy)
    (initialTable : DeterministicMarkovPolicyTable mdp)
    (defaultState : State)
    (support : ExploratoryPathSupport mdp initialState)
    (baseVisitFloor : Real)
    (hbaseFloor : ExploratoryPathUniformVisitFloor support 1 baseVisitFloor)
    (hrewardBound : forall state action, |mdp.reward state action| <= 1)
    (hhorizon : 4 < mdp.horizon) (hbaseVisitFloor : 0 < baseVisitFloor)
    (scheduleIndex : Nat) :
    let source := selfConsistentScheduledCausalSource mdp initialState
      rewardSource initialTable defaultState varianceProxy baseVisitFloor
    let stoppingPrefix :=
      selfConsistentScheduledNaturalCausalInverseSqrtThresholdUnboundedHittingAfterStoppingPrefix
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor
    let sampledReturn :=
      selfConsistentScheduledNaturalCausalStoppingTimeAverageSampledReturnProcess
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor stoppingPrefix
    let policyReturn :=
      selfConsistentScheduledNaturalCausalStoppingTimeAverageSuccessorPolicyExpectedReturnProcess
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor stoppingPrefix
    let returnDeviation :=
      selfConsistentScheduledNaturalCausalStoppingTimeAverageReturnDeviationProcess
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor stoppingPrefix
    integral source.trajectoryMeasure (sampledReturn scheduleIndex) -
        integral source.trajectoryMeasure (policyReturn scheduleIndex) =
      integral source.trajectoryMeasure (returnDeviation scheduleIndex) := by
  dsimp only
  have hsampled :=
    integrable_selfConsistentScheduledNaturalCausalInverseSqrtThresholdUnboundedHittingAfterStoppedAverageSampledReturn
      mdp initialState rewardSource varianceProxy hvarianceProxy law initialTable
        defaultState support baseVisitFloor hbaseFloor hrewardBound hhorizon
          hbaseVisitFloor scheduleIndex
  have hpolicy :=
    integrable_selfConsistentScheduledNaturalCausalInverseSqrtThresholdUnboundedHittingAfterStoppedAverageSuccessorPolicyExpectedReturn
      mdp initialState rewardSource initialTable defaultState varianceProxy
        baseVisitFloor hrewardBound scheduleIndex
  rw [← integral_sub hsampled hpolicy]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun trajectory =>
    selfConsistentScheduledNaturalCausalStoppingTimeAverageSampledReturn_sub_successorPolicyExpectedReturn_eq_returnDeviation
      mdp initialState rewardSource initialTable defaultState varianceProxy
        baseVisitFloor
        (selfConsistentScheduledNaturalCausalInverseSqrtThresholdUnboundedHittingAfterStoppingPrefix
          mdp initialState rewardSource initialTable defaultState varianceProxy
            baseVisitFloor) scheduleIndex trajectory

/-- The capped expected sampled/policy-return gap tends to zero. -/
theorem
    selfConsistentScheduledNaturalCausalInverseSqrtThresholdCappedStoppedAverageSampledReturnSuccessorPolicyExpectedReturnGap_tendsto_zero
    (mdp : MDP State Action) (initialState : Measure State)
    [IsProbabilityMeasure initialState]
    [StandardBorelSpace State] [StandardBorelSpace Action]
    (rewardSource : mdp.MeanCompatibleRewardKernel)
    (varianceProxy : NNReal) (hvarianceProxy : 0 < varianceProxy)
    (law : rewardSource.UniformSubgaussianRewardLaw varianceProxy)
    (initialTable : DeterministicMarkovPolicyTable mdp)
    (defaultState : State)
    (support : ExploratoryPathSupport mdp initialState)
    (baseVisitFloor : Real)
    (hbaseFloor : ExploratoryPathUniformVisitFloor support 1 baseVisitFloor)
    (hrewardBound : forall state action, |mdp.reward state action| <= 1)
    (hhorizon : 4 < mdp.horizon) (hbaseVisitFloor : 0 < baseVisitFloor) :
    let source := selfConsistentScheduledCausalSource mdp initialState
      rewardSource initialTable defaultState varianceProxy baseVisitFloor
    let stoppingPrefix :=
      selfConsistentScheduledNaturalCausalInverseSqrtThresholdCappedDoubleLinearRawWindowFirstPassageStoppingPrefix
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor
    let sampledReturn :=
      selfConsistentScheduledNaturalCausalStoppingTimeAverageSampledReturnProcess
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor stoppingPrefix
    let policyReturn :=
      selfConsistentScheduledNaturalCausalStoppingTimeAverageSuccessorPolicyExpectedReturnProcess
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor stoppingPrefix
    Tendsto (fun scheduleIndex =>
      integral source.trajectoryMeasure (sampledReturn scheduleIndex) -
        integral source.trajectoryMeasure (policyReturn scheduleIndex))
      atTop (nhds 0) := by
  dsimp only
  rw [show (fun scheduleIndex =>
      integral
          (selfConsistentScheduledCausalSource mdp initialState rewardSource
            initialTable defaultState varianceProxy baseVisitFloor).trajectoryMeasure
          (selfConsistentScheduledNaturalCausalStoppingTimeAverageSampledReturnProcess
            mdp initialState rewardSource initialTable defaultState varianceProxy
              baseVisitFloor
              (selfConsistentScheduledNaturalCausalInverseSqrtThresholdCappedDoubleLinearRawWindowFirstPassageStoppingPrefix
                mdp initialState rewardSource initialTable defaultState
                  varianceProxy baseVisitFloor) scheduleIndex) -
        integral
          (selfConsistentScheduledCausalSource mdp initialState rewardSource
            initialTable defaultState varianceProxy baseVisitFloor).trajectoryMeasure
          (selfConsistentScheduledNaturalCausalStoppingTimeAverageSuccessorPolicyExpectedReturnProcess
            mdp initialState rewardSource initialTable defaultState varianceProxy
              baseVisitFloor
              (selfConsistentScheduledNaturalCausalInverseSqrtThresholdCappedDoubleLinearRawWindowFirstPassageStoppingPrefix
                mdp initialState rewardSource initialTable defaultState
                  varianceProxy baseVisitFloor) scheduleIndex)) =
      fun scheduleIndex =>
        integral
          (selfConsistentScheduledCausalSource mdp initialState rewardSource
            initialTable defaultState varianceProxy baseVisitFloor).trajectoryMeasure
          (selfConsistentScheduledNaturalCausalStoppingTimeAverageReturnDeviationProcess
            mdp initialState rewardSource initialTable defaultState varianceProxy
              baseVisitFloor
              (selfConsistentScheduledNaturalCausalInverseSqrtThresholdCappedDoubleLinearRawWindowFirstPassageStoppingPrefix
                mdp initialState rewardSource initialTable defaultState
                  varianceProxy baseVisitFloor) scheduleIndex) by
    funext scheduleIndex
    exact
      selfConsistentScheduledNaturalCausalInverseSqrtThresholdCappedStoppedAverageSampledReturnIntegral_sub_successorPolicyExpectedReturnIntegral_eq_returnDeviationIntegral
        mdp initialState rewardSource varianceProxy hvarianceProxy law initialTable
          defaultState support baseVisitFloor hbaseFloor hrewardBound hhorizon
            hbaseVisitFloor scheduleIndex]
  exact
    selfConsistentScheduledNaturalCausalInverseSqrtThresholdCappedStoppedReturnDeviationIntegral_tendsto_zero
      mdp initialState rewardSource varianceProxy hvarianceProxy law initialTable
        defaultState support baseVisitFloor hbaseFloor hrewardBound hhorizon
          hbaseVisitFloor

/-- The genuine uncapped expected sampled/policy-return gap tends to zero. -/
theorem
    selfConsistentScheduledNaturalCausalInverseSqrtThresholdUnboundedHittingAfterStoppedAverageSampledReturnSuccessorPolicyExpectedReturnGap_tendsto_zero
    (mdp : MDP State Action) (initialState : Measure State)
    [IsProbabilityMeasure initialState]
    [StandardBorelSpace State] [StandardBorelSpace Action]
    (rewardSource : mdp.MeanCompatibleRewardKernel)
    (varianceProxy : NNReal) (hvarianceProxy : 0 < varianceProxy)
    (law : rewardSource.UniformSubgaussianRewardLaw varianceProxy)
    (initialTable : DeterministicMarkovPolicyTable mdp)
    (defaultState : State)
    (support : ExploratoryPathSupport mdp initialState)
    (baseVisitFloor : Real)
    (hbaseFloor : ExploratoryPathUniformVisitFloor support 1 baseVisitFloor)
    (hrewardBound : forall state action, |mdp.reward state action| <= 1)
    (hhorizon : 4 < mdp.horizon) (hbaseVisitFloor : 0 < baseVisitFloor) :
    let source := selfConsistentScheduledCausalSource mdp initialState
      rewardSource initialTable defaultState varianceProxy baseVisitFloor
    let stoppingPrefix :=
      selfConsistentScheduledNaturalCausalInverseSqrtThresholdUnboundedHittingAfterStoppingPrefix
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor
    let sampledReturn :=
      selfConsistentScheduledNaturalCausalStoppingTimeAverageSampledReturnProcess
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor stoppingPrefix
    let policyReturn :=
      selfConsistentScheduledNaturalCausalStoppingTimeAverageSuccessorPolicyExpectedReturnProcess
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor stoppingPrefix
    Tendsto (fun scheduleIndex =>
      integral source.trajectoryMeasure (sampledReturn scheduleIndex) -
        integral source.trajectoryMeasure (policyReturn scheduleIndex))
      atTop (nhds 0) := by
  dsimp only
  rw [show (fun scheduleIndex =>
      integral
          (selfConsistentScheduledCausalSource mdp initialState rewardSource
            initialTable defaultState varianceProxy baseVisitFloor).trajectoryMeasure
          (selfConsistentScheduledNaturalCausalStoppingTimeAverageSampledReturnProcess
            mdp initialState rewardSource initialTable defaultState varianceProxy
              baseVisitFloor
              (selfConsistentScheduledNaturalCausalInverseSqrtThresholdUnboundedHittingAfterStoppingPrefix
                mdp initialState rewardSource initialTable defaultState
                  varianceProxy baseVisitFloor) scheduleIndex) -
        integral
          (selfConsistentScheduledCausalSource mdp initialState rewardSource
            initialTable defaultState varianceProxy baseVisitFloor).trajectoryMeasure
          (selfConsistentScheduledNaturalCausalStoppingTimeAverageSuccessorPolicyExpectedReturnProcess
            mdp initialState rewardSource initialTable defaultState varianceProxy
              baseVisitFloor
              (selfConsistentScheduledNaturalCausalInverseSqrtThresholdUnboundedHittingAfterStoppingPrefix
                mdp initialState rewardSource initialTable defaultState
                  varianceProxy baseVisitFloor) scheduleIndex)) =
      fun scheduleIndex =>
        integral
          (selfConsistentScheduledCausalSource mdp initialState rewardSource
            initialTable defaultState varianceProxy baseVisitFloor).trajectoryMeasure
          (selfConsistentScheduledNaturalCausalStoppingTimeAverageReturnDeviationProcess
            mdp initialState rewardSource initialTable defaultState varianceProxy
              baseVisitFloor
              (selfConsistentScheduledNaturalCausalInverseSqrtThresholdUnboundedHittingAfterStoppingPrefix
                mdp initialState rewardSource initialTable defaultState
                  varianceProxy baseVisitFloor) scheduleIndex) by
    funext scheduleIndex
    exact
      selfConsistentScheduledNaturalCausalInverseSqrtThresholdUnboundedHittingAfterStoppedAverageSampledReturnIntegral_sub_successorPolicyExpectedReturnIntegral_eq_returnDeviationIntegral
        mdp initialState rewardSource varianceProxy hvarianceProxy law initialTable
          defaultState support baseVisitFloor hbaseFloor hrewardBound hhorizon
            hbaseVisitFloor scheduleIndex]
  exact
    selfConsistentScheduledNaturalCausalInverseSqrtThresholdUnboundedHittingAfterStoppedReturnDeviationIntegral_tendsto_zero
      mdp initialState rewardSource varianceProxy hvarianceProxy law initialTable
        defaultState support baseVisitFloor hbaseFloor hrewardBound hhorizon
          hbaseVisitFloor

/-- The absolute capped expected sampled/policy-return gap tends to zero. -/
theorem
    selfConsistentScheduledNaturalCausalInverseSqrtThresholdCappedStoppedAverageSampledReturnSuccessorPolicyExpectedReturnAbsGap_tendsto_zero
    (mdp : MDP State Action) (initialState : Measure State)
    [IsProbabilityMeasure initialState]
    [StandardBorelSpace State] [StandardBorelSpace Action]
    (rewardSource : mdp.MeanCompatibleRewardKernel)
    (varianceProxy : NNReal) (hvarianceProxy : 0 < varianceProxy)
    (law : rewardSource.UniformSubgaussianRewardLaw varianceProxy)
    (initialTable : DeterministicMarkovPolicyTable mdp)
    (defaultState : State)
    (support : ExploratoryPathSupport mdp initialState)
    (baseVisitFloor : Real)
    (hbaseFloor : ExploratoryPathUniformVisitFloor support 1 baseVisitFloor)
    (hrewardBound : forall state action, |mdp.reward state action| <= 1)
    (hhorizon : 4 < mdp.horizon) (hbaseVisitFloor : 0 < baseVisitFloor) :
    let source := selfConsistentScheduledCausalSource mdp initialState
      rewardSource initialTable defaultState varianceProxy baseVisitFloor
    let stoppingPrefix :=
      selfConsistentScheduledNaturalCausalInverseSqrtThresholdCappedDoubleLinearRawWindowFirstPassageStoppingPrefix
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor
    let sampledReturn :=
      selfConsistentScheduledNaturalCausalStoppingTimeAverageSampledReturnProcess
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor stoppingPrefix
    let policyReturn :=
      selfConsistentScheduledNaturalCausalStoppingTimeAverageSuccessorPolicyExpectedReturnProcess
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor stoppingPrefix
    Tendsto (fun scheduleIndex =>
      |integral source.trajectoryMeasure (sampledReturn scheduleIndex) -
        integral source.trajectoryMeasure (policyReturn scheduleIndex)|)
      atTop (nhds 0) := by
  simpa only [abs_zero] using
    (selfConsistentScheduledNaturalCausalInverseSqrtThresholdCappedStoppedAverageSampledReturnSuccessorPolicyExpectedReturnGap_tendsto_zero
      mdp initialState rewardSource varianceProxy hvarianceProxy law initialTable
        defaultState support baseVisitFloor hbaseFloor hrewardBound hhorizon
          hbaseVisitFloor).abs

/-- The absolute genuine uncapped expected sampled/policy-return gap tends to
zero. -/
theorem
    selfConsistentScheduledNaturalCausalInverseSqrtThresholdUnboundedHittingAfterStoppedAverageSampledReturnSuccessorPolicyExpectedReturnAbsGap_tendsto_zero
    (mdp : MDP State Action) (initialState : Measure State)
    [IsProbabilityMeasure initialState]
    [StandardBorelSpace State] [StandardBorelSpace Action]
    (rewardSource : mdp.MeanCompatibleRewardKernel)
    (varianceProxy : NNReal) (hvarianceProxy : 0 < varianceProxy)
    (law : rewardSource.UniformSubgaussianRewardLaw varianceProxy)
    (initialTable : DeterministicMarkovPolicyTable mdp)
    (defaultState : State)
    (support : ExploratoryPathSupport mdp initialState)
    (baseVisitFloor : Real)
    (hbaseFloor : ExploratoryPathUniformVisitFloor support 1 baseVisitFloor)
    (hrewardBound : forall state action, |mdp.reward state action| <= 1)
    (hhorizon : 4 < mdp.horizon) (hbaseVisitFloor : 0 < baseVisitFloor) :
    let source := selfConsistentScheduledCausalSource mdp initialState
      rewardSource initialTable defaultState varianceProxy baseVisitFloor
    let stoppingPrefix :=
      selfConsistentScheduledNaturalCausalInverseSqrtThresholdUnboundedHittingAfterStoppingPrefix
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor
    let sampledReturn :=
      selfConsistentScheduledNaturalCausalStoppingTimeAverageSampledReturnProcess
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor stoppingPrefix
    let policyReturn :=
      selfConsistentScheduledNaturalCausalStoppingTimeAverageSuccessorPolicyExpectedReturnProcess
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor stoppingPrefix
    Tendsto (fun scheduleIndex =>
      |integral source.trajectoryMeasure (sampledReturn scheduleIndex) -
        integral source.trajectoryMeasure (policyReturn scheduleIndex)|)
      atTop (nhds 0) := by
  simpa only [abs_zero] using
    (selfConsistentScheduledNaturalCausalInverseSqrtThresholdUnboundedHittingAfterStoppedAverageSampledReturnSuccessorPolicyExpectedReturnGap_tendsto_zero
      mdp initialState rewardSource varianceProxy hvarianceProxy law initialTable
        defaultState support baseVisitFloor hbaseFloor hrewardBound hhorizon
          hbaseVisitFloor).abs

/-- Expected literal successor-policy return at the capped prefix converges to
the optimal initial expected return. -/
theorem
    selfConsistentScheduledNaturalCausalInverseSqrtThresholdCappedStoppedAverageSuccessorPolicyExpectedReturnIntegral_tendsto_optimal
    (mdp : MDP State Action) (initialState : Measure State)
    [IsProbabilityMeasure initialState]
    [StandardBorelSpace State] [StandardBorelSpace Action]
    (rewardSource : mdp.MeanCompatibleRewardKernel)
    (varianceProxy : NNReal) (hvarianceProxy : 0 < varianceProxy)
    (law : rewardSource.UniformSubgaussianRewardLaw varianceProxy)
    (initialTable : DeterministicMarkovPolicyTable mdp)
    (defaultState : State)
    (support : ExploratoryPathSupport mdp initialState)
    (baseVisitFloor : Real)
    (hbaseFloor : ExploratoryPathUniformVisitFloor support 1 baseVisitFloor)
    (hrewardBound : forall state action, |mdp.reward state action| <= 1)
    (hhorizon : 4 < mdp.horizon) (hbaseVisitFloor : 0 < baseVisitFloor) :
    let source := selfConsistentScheduledCausalSource mdp initialState
      rewardSource initialTable defaultState varianceProxy baseVisitFloor
    let stoppingPrefix :=
      selfConsistentScheduledNaturalCausalInverseSqrtThresholdCappedDoubleLinearRawWindowFirstPassageStoppingPrefix
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor
    let policyReturn :=
      selfConsistentScheduledNaturalCausalStoppingTimeAverageSuccessorPolicyExpectedReturnProcess
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor stoppingPrefix
    Tendsto (fun scheduleIndex =>
      integral source.trajectoryMeasure (policyReturn scheduleIndex)) atTop
      (nhds (AdaptiveStochasticEpisodeBatchSource.optimalInitialExpectedReturn
        mdp initialState)) := by
  dsimp only
  rw [show (fun scheduleIndex =>
      integral
        (selfConsistentScheduledCausalSource mdp initialState rewardSource
          initialTable defaultState varianceProxy baseVisitFloor).trajectoryMeasure
        (selfConsistentScheduledNaturalCausalStoppingTimeAverageSuccessorPolicyExpectedReturnProcess
          mdp initialState rewardSource initialTable defaultState varianceProxy
            baseVisitFloor
            (selfConsistentScheduledNaturalCausalInverseSqrtThresholdCappedDoubleLinearRawWindowFirstPassageStoppingPrefix
              mdp initialState rewardSource initialTable defaultState varianceProxy
                baseVisitFloor) scheduleIndex)) =
      fun scheduleIndex =>
        AdaptiveStochasticEpisodeBatchSource.optimalInitialExpectedReturn
            mdp initialState -
          integral
            (selfConsistentScheduledCausalSource mdp initialState rewardSource
              initialTable defaultState varianceProxy baseVisitFloor).trajectoryMeasure
            (selfConsistentScheduledNaturalCausalStoppingTimeAverageBehaviorExpectedRegretProcess
              mdp initialState rewardSource initialTable defaultState varianceProxy
                baseVisitFloor
                (selfConsistentScheduledNaturalCausalInverseSqrtThresholdCappedDoubleLinearRawWindowFirstPassageStoppingPrefix
                  mdp initialState rewardSource initialTable defaultState
                    varianceProxy baseVisitFloor) scheduleIndex) by
    funext scheduleIndex
    exact
      selfConsistentScheduledNaturalCausalInverseSqrtThresholdCappedStoppedAverageSuccessorPolicyExpectedReturnIntegral_eq_optimal_sub_behaviorExpected
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor hrewardBound scheduleIndex]
  simpa using
    (selfConsistentScheduledNaturalCausalInverseSqrtThresholdCappedStoppedBehaviorExpectedRegretIntegral_tendsto_zero
      mdp initialState rewardSource varianceProxy hvarianceProxy law initialTable
        defaultState support baseVisitFloor hbaseFloor hrewardBound (by omega)
          hbaseVisitFloor).const_sub
      (AdaptiveStochasticEpisodeBatchSource.optimalInitialExpectedReturn
        mdp initialState)

/-- Expected literal successor-policy return at the genuine uncapped prefix
converges to the optimal initial expected return. -/
theorem
    selfConsistentScheduledNaturalCausalInverseSqrtThresholdUnboundedHittingAfterStoppedAverageSuccessorPolicyExpectedReturnIntegral_tendsto_optimal
    (mdp : MDP State Action) (initialState : Measure State)
    [IsProbabilityMeasure initialState]
    [StandardBorelSpace State] [StandardBorelSpace Action]
    (rewardSource : mdp.MeanCompatibleRewardKernel)
    (varianceProxy : NNReal) (hvarianceProxy : 0 < varianceProxy)
    (law : rewardSource.UniformSubgaussianRewardLaw varianceProxy)
    (initialTable : DeterministicMarkovPolicyTable mdp)
    (defaultState : State)
    (support : ExploratoryPathSupport mdp initialState)
    (baseVisitFloor : Real)
    (hbaseFloor : ExploratoryPathUniformVisitFloor support 1 baseVisitFloor)
    (hrewardBound : forall state action, |mdp.reward state action| <= 1)
    (hhorizon : 4 < mdp.horizon) (hbaseVisitFloor : 0 < baseVisitFloor) :
    let source := selfConsistentScheduledCausalSource mdp initialState
      rewardSource initialTable defaultState varianceProxy baseVisitFloor
    let stoppingPrefix :=
      selfConsistentScheduledNaturalCausalInverseSqrtThresholdUnboundedHittingAfterStoppingPrefix
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor
    let policyReturn :=
      selfConsistentScheduledNaturalCausalStoppingTimeAverageSuccessorPolicyExpectedReturnProcess
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor stoppingPrefix
    Tendsto (fun scheduleIndex =>
      integral source.trajectoryMeasure (policyReturn scheduleIndex)) atTop
      (nhds (AdaptiveStochasticEpisodeBatchSource.optimalInitialExpectedReturn
        mdp initialState)) := by
  dsimp only
  rw [show (fun scheduleIndex =>
      integral
        (selfConsistentScheduledCausalSource mdp initialState rewardSource
          initialTable defaultState varianceProxy baseVisitFloor).trajectoryMeasure
        (selfConsistentScheduledNaturalCausalStoppingTimeAverageSuccessorPolicyExpectedReturnProcess
          mdp initialState rewardSource initialTable defaultState varianceProxy
            baseVisitFloor
            (selfConsistentScheduledNaturalCausalInverseSqrtThresholdUnboundedHittingAfterStoppingPrefix
              mdp initialState rewardSource initialTable defaultState varianceProxy
                baseVisitFloor) scheduleIndex)) =
      fun scheduleIndex =>
        AdaptiveStochasticEpisodeBatchSource.optimalInitialExpectedReturn
            mdp initialState -
          integral
            (selfConsistentScheduledCausalSource mdp initialState rewardSource
              initialTable defaultState varianceProxy baseVisitFloor).trajectoryMeasure
            (selfConsistentScheduledNaturalCausalStoppingTimeAverageBehaviorExpectedRegretProcess
              mdp initialState rewardSource initialTable defaultState varianceProxy
                baseVisitFloor
                (selfConsistentScheduledNaturalCausalInverseSqrtThresholdUnboundedHittingAfterStoppingPrefix
                  mdp initialState rewardSource initialTable defaultState
                    varianceProxy baseVisitFloor) scheduleIndex) by
    funext scheduleIndex
    exact
      selfConsistentScheduledNaturalCausalInverseSqrtThresholdUnboundedHittingAfterStoppedAverageSuccessorPolicyExpectedReturnIntegral_eq_optimal_sub_behaviorExpected
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor hrewardBound scheduleIndex]
  simpa using
    (selfConsistentScheduledNaturalCausalInverseSqrtThresholdUnboundedHittingAfterStoppedBehaviorExpectedRegretIntegral_tendsto_zero
      mdp initialState rewardSource varianceProxy hvarianceProxy law initialTable
        defaultState support baseVisitFloor hbaseFloor hrewardBound (by omega)
          hbaseVisitFloor).const_sub
      (AdaptiveStochasticEpisodeBatchSource.optimalInitialExpectedReturn
        mdp initialState)

/-- Terminal literal policy-return semantics and stopped expected-consistency
package for the capped approximation and genuine uncapped stopping prefix. -/
theorem
    selfConsistentScheduledCausalSource_inverseSqrtThresholdCappedUnboundedHittingAfter_stoppedSampledReturn_and_successorPolicyExpectedReturn_consistency
    (mdp : MDP State Action) (initialState : Measure State)
    [IsProbabilityMeasure initialState]
    [StandardBorelSpace State] [StandardBorelSpace Action]
    (rewardSource : mdp.MeanCompatibleRewardKernel)
    (varianceProxy : NNReal) (hvarianceProxy : 0 < varianceProxy)
    (law : rewardSource.UniformSubgaussianRewardLaw varianceProxy)
    (initialTable : DeterministicMarkovPolicyTable mdp)
    (defaultState : State)
    (support : ExploratoryPathSupport mdp initialState)
    (baseVisitFloor : Real)
    (hbaseFloor : ExploratoryPathUniformVisitFloor support 1 baseVisitFloor)
    (hrewardBound : forall state action, |mdp.reward state action| <= 1)
    (hhorizon : 4 < mdp.horizon) (hbaseVisitFloor : 0 < baseVisitFloor) :
    let source := selfConsistentScheduledCausalSource mdp initialState
      rewardSource initialTable defaultState varianceProxy baseVisitFloor
    let cappedStoppingPrefix :=
      selfConsistentScheduledNaturalCausalInverseSqrtThresholdCappedDoubleLinearRawWindowFirstPassageStoppingPrefix
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor
    let uncappedStoppingPrefix :=
      selfConsistentScheduledNaturalCausalInverseSqrtThresholdUnboundedHittingAfterStoppingPrefix
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor
    let cappedSampledReturn :=
      selfConsistentScheduledNaturalCausalStoppingTimeAverageSampledReturnProcess
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor cappedStoppingPrefix
    let uncappedSampledReturn :=
      selfConsistentScheduledNaturalCausalStoppingTimeAverageSampledReturnProcess
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor uncappedStoppingPrefix
    let cappedPolicyReturn :=
      selfConsistentScheduledNaturalCausalStoppingTimeAverageSuccessorPolicyExpectedReturnProcess
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor cappedStoppingPrefix
    let uncappedPolicyReturn :=
      selfConsistentScheduledNaturalCausalStoppingTimeAverageSuccessorPolicyExpectedReturnProcess
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor uncappedStoppingPrefix
    let cappedReturnDeviation :=
      selfConsistentScheduledNaturalCausalStoppingTimeAverageReturnDeviationProcess
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor cappedStoppingPrefix
    let uncappedReturnDeviation :=
      selfConsistentScheduledNaturalCausalStoppingTimeAverageReturnDeviationProcess
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor uncappedStoppingPrefix
    let cappedBehaviorRegret :=
      selfConsistentScheduledNaturalCausalStoppingTimeAverageBehaviorExpectedRegretProcess
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor cappedStoppingPrefix
    let uncappedBehaviorRegret :=
      selfConsistentScheduledNaturalCausalStoppingTimeAverageBehaviorExpectedRegretProcess
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor uncappedStoppingPrefix
    (forall scheduleIndex trajectory,
      cappedPolicyReturn scheduleIndex trajectory =
          AdaptiveStochasticEpisodeBatchSource.optimalInitialExpectedReturn
              mdp initialState - cappedBehaviorRegret scheduleIndex trajectory /\
        uncappedPolicyReturn scheduleIndex trajectory =
          AdaptiveStochasticEpisodeBatchSource.optimalInitialExpectedReturn
              mdp initialState - uncappedBehaviorRegret scheduleIndex trajectory /\
        cappedSampledReturn scheduleIndex trajectory -
            cappedPolicyReturn scheduleIndex trajectory =
              cappedReturnDeviation scheduleIndex trajectory /\
        uncappedSampledReturn scheduleIndex trajectory -
          uncappedPolicyReturn scheduleIndex trajectory =
            uncappedReturnDeviation scheduleIndex trajectory) /\
      (forall scheduleIndex,
        Measurable (cappedPolicyReturn scheduleIndex) /\
        Measurable (uncappedPolicyReturn scheduleIndex) /\
        Integrable (cappedPolicyReturn scheduleIndex) source.trajectoryMeasure /\
        Integrable (uncappedPolicyReturn scheduleIndex) source.trajectoryMeasure /\
        integral source.trajectoryMeasure (cappedPolicyReturn scheduleIndex) =
          AdaptiveStochasticEpisodeBatchSource.optimalInitialExpectedReturn
              mdp initialState -
            integral source.trajectoryMeasure
              (cappedBehaviorRegret scheduleIndex) /\
        integral source.trajectoryMeasure (uncappedPolicyReturn scheduleIndex) =
          AdaptiveStochasticEpisodeBatchSource.optimalInitialExpectedReturn
              mdp initialState -
            integral source.trajectoryMeasure
              (uncappedBehaviorRegret scheduleIndex) /\
        integral source.trajectoryMeasure (cappedSampledReturn scheduleIndex) -
            integral source.trajectoryMeasure (cappedPolicyReturn scheduleIndex) =
          integral source.trajectoryMeasure
            (cappedReturnDeviation scheduleIndex) /\
        integral source.trajectoryMeasure (uncappedSampledReturn scheduleIndex) -
            integral source.trajectoryMeasure (uncappedPolicyReturn scheduleIndex) =
          integral source.trajectoryMeasure
            (uncappedReturnDeviation scheduleIndex)) /\
      Tendsto (fun scheduleIndex =>
        integral source.trajectoryMeasure (cappedSampledReturn scheduleIndex) -
          integral source.trajectoryMeasure (cappedPolicyReturn scheduleIndex))
        atTop (nhds 0) /\
      Tendsto (fun scheduleIndex =>
        integral source.trajectoryMeasure (uncappedSampledReturn scheduleIndex) -
          integral source.trajectoryMeasure (uncappedPolicyReturn scheduleIndex))
        atTop (nhds 0) /\
      Tendsto (fun scheduleIndex =>
        |integral source.trajectoryMeasure (cappedSampledReturn scheduleIndex) -
          integral source.trajectoryMeasure (cappedPolicyReturn scheduleIndex)|)
        atTop (nhds 0) /\
      Tendsto (fun scheduleIndex =>
        |integral source.trajectoryMeasure (uncappedSampledReturn scheduleIndex) -
          integral source.trajectoryMeasure (uncappedPolicyReturn scheduleIndex)|)
        atTop (nhds 0) /\
      Tendsto (fun scheduleIndex =>
        integral source.trajectoryMeasure (cappedPolicyReturn scheduleIndex))
        atTop
        (nhds (AdaptiveStochasticEpisodeBatchSource.optimalInitialExpectedReturn
          mdp initialState)) /\
      Tendsto (fun scheduleIndex =>
        integral source.trajectoryMeasure (uncappedPolicyReturn scheduleIndex))
        atTop
        (nhds (AdaptiveStochasticEpisodeBatchSource.optimalInitialExpectedReturn
          mdp initialState)) := by
  dsimp only
  constructor
  · intro scheduleIndex trajectory
    exact
      ⟨selfConsistentScheduledNaturalCausalStoppingTimeAverageSuccessorPolicyExpectedReturnProcess_eq_optimal_sub_behaviorExpected
          mdp initialState rewardSource initialTable defaultState varianceProxy
            baseVisitFloor
            (selfConsistentScheduledNaturalCausalInverseSqrtThresholdCappedDoubleLinearRawWindowFirstPassageStoppingPrefix
              mdp initialState rewardSource initialTable defaultState varianceProxy
                baseVisitFloor) scheduleIndex trajectory,
        selfConsistentScheduledNaturalCausalStoppingTimeAverageSuccessorPolicyExpectedReturnProcess_eq_optimal_sub_behaviorExpected
          mdp initialState rewardSource initialTable defaultState varianceProxy
            baseVisitFloor
            (selfConsistentScheduledNaturalCausalInverseSqrtThresholdUnboundedHittingAfterStoppingPrefix
              mdp initialState rewardSource initialTable defaultState varianceProxy
                baseVisitFloor) scheduleIndex trajectory,
        selfConsistentScheduledNaturalCausalStoppingTimeAverageSampledReturn_sub_successorPolicyExpectedReturn_eq_returnDeviation
          mdp initialState rewardSource initialTable defaultState varianceProxy
            baseVisitFloor
            (selfConsistentScheduledNaturalCausalInverseSqrtThresholdCappedDoubleLinearRawWindowFirstPassageStoppingPrefix
              mdp initialState rewardSource initialTable defaultState varianceProxy
                baseVisitFloor) scheduleIndex trajectory,
        selfConsistentScheduledNaturalCausalStoppingTimeAverageSampledReturn_sub_successorPolicyExpectedReturn_eq_returnDeviation
          mdp initialState rewardSource initialTable defaultState varianceProxy
            baseVisitFloor
            (selfConsistentScheduledNaturalCausalInverseSqrtThresholdUnboundedHittingAfterStoppingPrefix
              mdp initialState rewardSource initialTable defaultState varianceProxy
                baseVisitFloor) scheduleIndex trajectory⟩
  constructor
  · intro scheduleIndex
    exact
      ⟨measurable_selfConsistentScheduledNaturalCausalInverseSqrtThresholdCappedStoppedAverageSuccessorPolicyExpectedReturn
          mdp initialState rewardSource initialTable defaultState varianceProxy
            baseVisitFloor scheduleIndex,
        measurable_selfConsistentScheduledNaturalCausalInverseSqrtThresholdUnboundedHittingAfterStoppedAverageSuccessorPolicyExpectedReturn
          mdp initialState rewardSource initialTable defaultState varianceProxy
            baseVisitFloor scheduleIndex,
        integrable_selfConsistentScheduledNaturalCausalInverseSqrtThresholdCappedStoppedAverageSuccessorPolicyExpectedReturn
          mdp initialState rewardSource initialTable defaultState varianceProxy
            baseVisitFloor hrewardBound scheduleIndex,
        integrable_selfConsistentScheduledNaturalCausalInverseSqrtThresholdUnboundedHittingAfterStoppedAverageSuccessorPolicyExpectedReturn
          mdp initialState rewardSource initialTable defaultState varianceProxy
            baseVisitFloor hrewardBound scheduleIndex,
        selfConsistentScheduledNaturalCausalInverseSqrtThresholdCappedStoppedAverageSuccessorPolicyExpectedReturnIntegral_eq_optimal_sub_behaviorExpected
          mdp initialState rewardSource initialTable defaultState varianceProxy
            baseVisitFloor hrewardBound scheduleIndex,
        selfConsistentScheduledNaturalCausalInverseSqrtThresholdUnboundedHittingAfterStoppedAverageSuccessorPolicyExpectedReturnIntegral_eq_optimal_sub_behaviorExpected
          mdp initialState rewardSource initialTable defaultState varianceProxy
            baseVisitFloor hrewardBound scheduleIndex,
        selfConsistentScheduledNaturalCausalInverseSqrtThresholdCappedStoppedAverageSampledReturnIntegral_sub_successorPolicyExpectedReturnIntegral_eq_returnDeviationIntegral
          mdp initialState rewardSource varianceProxy hvarianceProxy law initialTable
            defaultState support baseVisitFloor hbaseFloor hrewardBound hhorizon
              hbaseVisitFloor scheduleIndex,
        selfConsistentScheduledNaturalCausalInverseSqrtThresholdUnboundedHittingAfterStoppedAverageSampledReturnIntegral_sub_successorPolicyExpectedReturnIntegral_eq_returnDeviationIntegral
          mdp initialState rewardSource varianceProxy hvarianceProxy law initialTable
            defaultState support baseVisitFloor hbaseFloor hrewardBound hhorizon
              hbaseVisitFloor scheduleIndex⟩
  constructor
  · exact
      selfConsistentScheduledNaturalCausalInverseSqrtThresholdCappedStoppedAverageSampledReturnSuccessorPolicyExpectedReturnGap_tendsto_zero
        mdp initialState rewardSource varianceProxy hvarianceProxy law initialTable
          defaultState support baseVisitFloor hbaseFloor hrewardBound hhorizon
            hbaseVisitFloor
  constructor
  · exact
      selfConsistentScheduledNaturalCausalInverseSqrtThresholdUnboundedHittingAfterStoppedAverageSampledReturnSuccessorPolicyExpectedReturnGap_tendsto_zero
        mdp initialState rewardSource varianceProxy hvarianceProxy law initialTable
          defaultState support baseVisitFloor hbaseFloor hrewardBound hhorizon
            hbaseVisitFloor
  constructor
  · exact
      selfConsistentScheduledNaturalCausalInverseSqrtThresholdCappedStoppedAverageSampledReturnSuccessorPolicyExpectedReturnAbsGap_tendsto_zero
        mdp initialState rewardSource varianceProxy hvarianceProxy law initialTable
          defaultState support baseVisitFloor hbaseFloor hrewardBound hhorizon
            hbaseVisitFloor
  constructor
  · exact
      selfConsistentScheduledNaturalCausalInverseSqrtThresholdUnboundedHittingAfterStoppedAverageSampledReturnSuccessorPolicyExpectedReturnAbsGap_tendsto_zero
        mdp initialState rewardSource varianceProxy hvarianceProxy law initialTable
          defaultState support baseVisitFloor hbaseFloor hrewardBound hhorizon
            hbaseVisitFloor
  exact
    ⟨selfConsistentScheduledNaturalCausalInverseSqrtThresholdCappedStoppedAverageSuccessorPolicyExpectedReturnIntegral_tendsto_optimal
        mdp initialState rewardSource varianceProxy hvarianceProxy law initialTable
          defaultState support baseVisitFloor hbaseFloor hrewardBound hhorizon
            hbaseVisitFloor,
      selfConsistentScheduledNaturalCausalInverseSqrtThresholdUnboundedHittingAfterStoppedAverageSuccessorPolicyExpectedReturnIntegral_tendsto_optimal
        mdp initialState rewardSource varianceProxy hvarianceProxy law initialTable
          defaultState support baseVisitFloor hbaseFloor hrewardBound hhorizon
            hbaseVisitFloor⟩

end AdaptiveStochasticSampledEmpiricalOptimisticSource

end BanditRLProof.FiniteHorizonRL
