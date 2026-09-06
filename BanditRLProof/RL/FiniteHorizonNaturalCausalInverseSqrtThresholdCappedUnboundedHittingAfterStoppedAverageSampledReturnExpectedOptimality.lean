import BanditRLProof.RL.FiniteHorizonNaturalCausalInverseSqrtThresholdCappedUnboundedHittingAfterStoppedRealizedBehaviorRegretAndPolicyValueExpectedConsistency

/-!
# Expected optimality of stopped average sampled return

This module exposes the observed successor-batch sample means whose complement
from the optimal initial value is the natural average realized-regret process.
The empty prefix is assigned the optimal value, so the complement identity is
total and remains valid at the `WithTop.untopA` fallback. The identity is then
transported through the capped and genuine uncapped stopping prefixes and
through Bochner integration. No expectation/stopping-index interchange or
optional-stopping theorem is used.
-/

open Filter MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal ProbabilityTheory Topology

namespace BanditRLProof.FiniteHorizonRL

universe u v w

variable {State : Type u} {Action : Type v}
    [MeasurableSpace State] [MeasurableSpace Action]
    [Fintype State] [Fintype Action]
    [DecidableEq State] [DecidableEq Action]
    [MeasurableSingletonClass State] [MeasurableSingletonClass Action]
    [Nonempty State] [Nonempty Action]

namespace HeterogeneousAdaptiveStochasticEpisodeBatchSource

/-- Observed sample mean in successor batch `t + 1`.

Lean's division on `Real` is total, so a zero-size successor batch gives zero.
The self-consistent scheduled source used below has positive batch sizes. -/
noncomputable def naturalSuccessorBatchAverageSampledReturn
    {mdp : MDP State Action} {initialState : Measure State}
    [IsProbabilityMeasure initialState] {episodes : Nat -> Nat}
    (_source : HeterogeneousAdaptiveStochasticEpisodeBatchSource
      mdp initialState episodes)
    (trajectory : HeterogeneousStochasticEpisodeBatchTrajectory mdp episodes)
    (t : Nat) : Real :=
  mdp.sampledCumulativeRewardSum (episodes (t + 1)) (trajectory (t + 1)) /
    (episodes (t + 1) : Real)

/-- Average of observed successor-batch sample means over a natural prefix.
At the empty prefix it uses the optimal initial expected return. -/
noncomputable def naturalAverageSampledReturn
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
      source.naturalSuccessorBatchAverageSampledReturn trajectory t) /
        (rounds : Real)

omit [DecidableEq State] [DecidableEq Action]
    [MeasurableSingletonClass State] [MeasurableSingletonClass Action]
    [Nonempty State] in
/-- At every prefix, observed average return is optimal value minus realized
regret. The empty-prefix convention makes the identity valid at zero. -/
theorem naturalAverageSampledReturn_eq_optimal_sub_naturalAverageRealizedBehaviorRegret
    {mdp : MDP State Action} {initialState : Measure State}
    [IsProbabilityMeasure initialState] {episodes : Nat -> Nat}
    (source : HeterogeneousAdaptiveStochasticEpisodeBatchSource
      mdp initialState episodes)
    (trajectory : HeterogeneousStochasticEpisodeBatchTrajectory mdp episodes)
    (rounds : Nat) :
    source.naturalAverageSampledReturn trajectory rounds =
      AdaptiveStochasticEpisodeBatchSource.optimalInitialExpectedReturn
          mdp initialState -
        source.naturalAverageRealizedBehaviorRegret trajectory rounds := by
  by_cases hrounds : rounds = 0
  · subst rounds
    simp [naturalAverageSampledReturn, naturalAverageRealizedBehaviorRegret,
      naturalCumulativeRealizedBehaviorRegret]
  · have hroundsReal : (rounds : Real) ≠ 0 := by
      exact_mod_cast hrounds
    simp only [naturalAverageSampledReturn, hrounds, if_false,
      naturalAverageRealizedBehaviorRegret,
      naturalCumulativeRealizedBehaviorRegret,
      naturalSuccessorBatchAverageRealizedRegret,
      naturalSuccessorBatchAverageSampledReturn]
    rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range,
      nsmul_eq_mul, sub_div, mul_div_cancel_left₀ _ hroundsReal]
    ring

omit [DecidableEq State] [DecidableEq Action]
    [MeasurableSingletonClass State] [MeasurableSingletonClass Action]
    [Nonempty State] in
/-- A fixed-prefix average sampled-return coordinate is measurable. -/
theorem measurable_naturalAverageSampledReturn
    {mdp : MDP State Action} {initialState : Measure State}
    [IsProbabilityMeasure initialState] {episodes : Nat -> Nat}
    (source : HeterogeneousAdaptiveStochasticEpisodeBatchSource
      mdp initialState episodes) (rounds : Nat) :
    Measurable (fun trajectory =>
      source.naturalAverageSampledReturn trajectory rounds) := by
  rw [show (fun trajectory =>
      source.naturalAverageSampledReturn trajectory rounds) =
        fun trajectory =>
          AdaptiveStochasticEpisodeBatchSource.optimalInitialExpectedReturn
              mdp initialState -
            source.naturalAverageRealizedBehaviorRegret trajectory rounds by
    funext trajectory
    exact source.naturalAverageSampledReturn_eq_optimal_sub_naturalAverageRealizedBehaviorRegret
      trajectory rounds]
  exact measurable_const.sub
    (source.measurable_naturalAverageRealizedBehaviorRegret rounds)

omit [DecidableEq State] [DecidableEq Action]
    [MeasurableSingletonClass State] [MeasurableSingletonClass Action]
    [Nonempty State] in
/-- A fixed-prefix average sampled return is measurable at its natural
filtration level. -/
theorem measurable_naturalAverageSampledReturn_naturalTrajectoryFiltration
    {mdp : MDP State Action} {initialState : Measure State}
    [IsProbabilityMeasure initialState] {episodes : Nat -> Nat}
    (source : HeterogeneousAdaptiveStochasticEpisodeBatchSource
      mdp initialState episodes) (rounds : Nat) :
    @Measurable
      (HeterogeneousStochasticEpisodeBatchTrajectory mdp episodes) Real
      (source.naturalTrajectoryFiltration rounds) inferInstance
      (fun trajectory =>
        source.naturalAverageSampledReturn trajectory rounds) := by
  rw [show (fun trajectory =>
      source.naturalAverageSampledReturn trajectory rounds) =
        fun trajectory =>
          AdaptiveStochasticEpisodeBatchSource.optimalInitialExpectedReturn
              mdp initialState -
            source.naturalAverageRealizedBehaviorRegret trajectory rounds by
    funext trajectory
    exact source.naturalAverageSampledReturn_eq_optimal_sub_naturalAverageRealizedBehaviorRegret
      trajectory rounds]
  exact measurable_const.sub
    (source.measurable_naturalAverageRealizedBehaviorRegret_naturalTrajectoryFiltration
      rounds)

omit [DecidableEq State] [DecidableEq Action]
    [MeasurableSingletonClass State] [MeasurableSingletonClass Action]
    [Nonempty State] in
/-- The natural average sampled-return process is strongly adapted. -/
theorem naturalAverageSampledReturn_stronglyAdapted_naturalTrajectoryFiltration
    {mdp : MDP State Action} {initialState : Measure State}
    [IsProbabilityMeasure initialState] {episodes : Nat -> Nat}
    (source : HeterogeneousAdaptiveStochasticEpisodeBatchSource
      mdp initialState episodes) :
    StronglyAdapted source.naturalTrajectoryFiltration
      (fun rounds trajectory =>
        source.naturalAverageSampledReturn trajectory rounds) := by
  intro rounds
  exact
    (source.measurable_naturalAverageSampledReturn_naturalTrajectoryFiltration
      rounds).stronglyMeasurable

end HeterogeneousAdaptiveStochasticEpisodeBatchSource

namespace AdaptiveStochasticSampledEmpiricalOptimisticSource

/-- Natural-prefix average of the observed successor-batch sample means for
the self-consistent causal source. -/
noncomputable def selfConsistentScheduledNaturalCausalAverageSampledReturnProcess
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
  fun trajectory => source.naturalAverageSampledReturn trajectory rounds

/-- The project-specific sampled-return process is exactly the complement of
the average realized-regret process. -/
theorem selfConsistentScheduledNaturalCausalAverageSampledReturnProcess_eq_optimal_sub_realized
    (mdp : MDP State Action) (initialState : Measure State)
    [IsProbabilityMeasure initialState]
    (rewardSource : mdp.MeanCompatibleRewardKernel)
    (initialTable : DeterministicMarkovPolicyTable mdp)
    (defaultState : State) (varianceProxy : NNReal)
    (baseVisitFloor : Real) (rounds : Nat) (trajectory) :
    selfConsistentScheduledNaturalCausalAverageSampledReturnProcess
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor rounds trajectory =
      AdaptiveStochasticEpisodeBatchSource.optimalInitialExpectedReturn
          mdp initialState -
        selfConsistentScheduledNaturalCausalAverageRealizedBehaviorRegretProcess
          mdp initialState rewardSource initialTable defaultState varianceProxy
            baseVisitFloor rounds trajectory := by
  let source := selfConsistentScheduledCausalSource mdp initialState
    rewardSource initialTable defaultState varianceProxy baseVisitFloor
  simpa [selfConsistentScheduledNaturalCausalAverageSampledReturnProcess,
    selfConsistentScheduledNaturalCausalAverageRealizedBehaviorRegretProcess,
    source] using
      source.naturalAverageSampledReturn_eq_optimal_sub_naturalAverageRealizedBehaviorRegret
        trajectory rounds

/-- The self-consistent sampled-return process is strongly adapted to the
exact natural trajectory filtration. -/
theorem selfConsistentScheduledNaturalCausalAverageSampledReturnProcess_stronglyAdapted
    (mdp : MDP State Action) (initialState : Measure State)
    [IsProbabilityMeasure initialState]
    (rewardSource : mdp.MeanCompatibleRewardKernel)
    (initialTable : DeterministicMarkovPolicyTable mdp)
    (defaultState : State) (varianceProxy : NNReal)
    (baseVisitFloor : Real) :
    StronglyAdapted
      (selfConsistentScheduledNaturalCausalTrajectoryFiltration mdp initialState
        rewardSource initialTable defaultState varianceProxy baseVisitFloor)
      (selfConsistentScheduledNaturalCausalAverageSampledReturnProcess
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor) := by
  let source := selfConsistentScheduledCausalSource mdp initialState
    rewardSource initialTable defaultState varianceProxy baseVisitFloor
  simpa [selfConsistentScheduledNaturalCausalTrajectoryFiltration,
    selfConsistentScheduledNaturalCausalAverageSampledReturnProcess, source] using
      source.naturalAverageSampledReturn_stronglyAdapted_naturalTrajectoryFiltration

/-- Average sampled return evaluated at a `WithTop Nat` stopping prefix. -/
noncomputable def selfConsistentScheduledNaturalCausalStoppingTimeAverageSampledReturnProcess
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
    (selfConsistentScheduledNaturalCausalAverageSampledReturnProcess
      mdp initialState rewardSource initialTable defaultState varianceProxy
        baseVisitFloor)
    (stoppingPrefix scheduleIndex)

@[simp]
theorem selfConsistentScheduledNaturalCausalStoppingTimeAverageSampledReturnProcess_apply
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
          baseVisitFloor stoppingPrefix scheduleIndex trajectory =
      selfConsistentScheduledNaturalCausalAverageSampledReturnProcess
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor (stoppingPrefix scheduleIndex trajectory).untopA trajectory :=
  rfl

/-- Stopping preserves the exact sampled-return/realized-regret complement. -/
theorem selfConsistentScheduledNaturalCausalStoppingTimeAverageSampledReturnProcess_eq_optimal_sub_realized
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
          baseVisitFloor stoppingPrefix scheduleIndex trajectory =
      AdaptiveStochasticEpisodeBatchSource.optimalInitialExpectedReturn
          mdp initialState -
        selfConsistentScheduledNaturalCausalStoppingTimeAverageRealizedBehaviorRegretProcess
          mdp initialState rewardSource initialTable defaultState varianceProxy
            baseVisitFloor stoppingPrefix scheduleIndex trajectory := by
  simp only [
    selfConsistentScheduledNaturalCausalStoppingTimeAverageSampledReturnProcess_apply,
    selfConsistentScheduledNaturalCausalStoppingTimeAverageRealizedBehaviorRegretProcess_apply]
  exact selfConsistentScheduledNaturalCausalAverageSampledReturnProcess_eq_optimal_sub_realized
    mdp initialState rewardSource initialTable defaultState varianceProxy
      baseVisitFloor _ trajectory

/-- Mathlib stopped-value measurability for the sampled-return process. -/
theorem measurable_selfConsistentScheduledNaturalCausalStoppingTimeAverageSampledReturnProcess
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
      (selfConsistentScheduledNaturalCausalStoppingTimeAverageSampledReturnProcess
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor stoppingPrefix scheduleIndex) := by
  have hprogressive :
      ProgMeasurable
        (selfConsistentScheduledNaturalCausalTrajectoryFiltration mdp initialState
          rewardSource initialTable defaultState varianceProxy baseVisitFloor)
        (selfConsistentScheduledNaturalCausalAverageSampledReturnProcess
          mdp initialState rewardSource initialTable defaultState varianceProxy
            baseVisitFloor) :=
    (selfConsistentScheduledNaturalCausalAverageSampledReturnProcess_stronglyAdapted
      mdp initialState rewardSource initialTable defaultState varianceProxy
        baseVisitFloor).progMeasurable_of_discrete
  exact
    (measurable_stoppedValue hprogressive hstopping).mono
      hstopping.measurableSpace_le le_rfl

/-- Integrability of stopped realized regret transfers to stopped sampled
return under any finite measure. -/
theorem integrable_selfConsistentScheduledNaturalCausalStoppingTimeAverageSampledReturnProcess_of_integrable_realized
    {Omega : Type w} [MeasurableSpace Omega] (mu : Measure Omega)
    [IsFiniteMeasure mu]
    (optimal : Real) (sampledReturn realizedRegret : Omega -> Real)
    (hpoint : forall omega, sampledReturn omega = optimal - realizedRegret omega)
    (hrealized : Integrable realizedRegret mu) :
    Integrable sampledReturn mu := by
  rw [show sampledReturn = fun omega => optimal - realizedRegret omega by
    funext omega
    exact hpoint omega]
  exact (integrable_const optimal).sub hrealized

/-- The corresponding Bochner expectation is the optimal constant minus the
expected realized regret. -/
theorem integral_selfConsistentScheduledNaturalCausalStoppingTimeAverageSampledReturnProcess_eq_optimal_sub_realized
    {Omega : Type w} [MeasurableSpace Omega] (mu : Measure Omega)
    [IsProbabilityMeasure mu]
    (optimal : Real) (sampledReturn realizedRegret : Omega -> Real)
    (hpoint : forall omega, sampledReturn omega = optimal - realizedRegret omega)
    (hrealized : Integrable realizedRegret mu) :
    integral mu sampledReturn = optimal - integral mu realizedRegret := by
  rw [show sampledReturn = fun omega => optimal - realizedRegret omega by
    funext omega
    exact hpoint omega]
  rw [integral_sub (integrable_const optimal) hrealized, integral_const]
  simp

/-- The capped inverse-sqrt first-passage sampled-return coordinate is
integrable. -/
theorem integrable_selfConsistentScheduledNaturalCausalInverseSqrtThresholdCappedStoppedAverageSampledReturn
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
    Integrable (sampledReturn scheduleIndex) source.trajectoryMeasure := by
  dsimp only
  apply
    integrable_selfConsistentScheduledNaturalCausalStoppingTimeAverageSampledReturnProcess_of_integrable_realized
      (selfConsistentScheduledCausalSource mdp initialState rewardSource
        initialTable defaultState varianceProxy baseVisitFloor).trajectoryMeasure
      (AdaptiveStochasticEpisodeBatchSource.optimalInitialExpectedReturn
        mdp initialState)
      (selfConsistentScheduledNaturalCausalStoppingTimeAverageSampledReturnProcess
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor
          (selfConsistentScheduledNaturalCausalInverseSqrtThresholdCappedDoubleLinearRawWindowFirstPassageStoppingPrefix
            mdp initialState rewardSource initialTable defaultState varianceProxy
              baseVisitFloor) scheduleIndex)
      (selfConsistentScheduledNaturalCausalStoppingTimeAverageRealizedBehaviorRegretProcess
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor
          (selfConsistentScheduledNaturalCausalInverseSqrtThresholdCappedDoubleLinearRawWindowFirstPassageStoppingPrefix
            mdp initialState rewardSource initialTable defaultState varianceProxy
              baseVisitFloor) scheduleIndex)
  · intro trajectory
    exact
      selfConsistentScheduledNaturalCausalStoppingTimeAverageSampledReturnProcess_eq_optimal_sub_realized
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor
          (selfConsistentScheduledNaturalCausalInverseSqrtThresholdCappedDoubleLinearRawWindowFirstPassageStoppingPrefix
            mdp initialState rewardSource initialTable defaultState varianceProxy
              baseVisitFloor) scheduleIndex trajectory
  · exact
      (memLp_one_selfConsistentScheduledNaturalCausalInverseSqrtThresholdCappedStoppedAverageRealizedBehaviorRegret
        mdp initialState rewardSource varianceProxy hvarianceProxy law initialTable
          defaultState support baseVisitFloor hbaseFloor hrewardBound (by omega)
            hbaseVisitFloor scheduleIndex).integrable (by norm_num)

/-- The genuine uncapped `hittingAfter` sampled-return coordinate is
integrable. -/
theorem integrable_selfConsistentScheduledNaturalCausalInverseSqrtThresholdUnboundedHittingAfterStoppedAverageSampledReturn
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
    Integrable (sampledReturn scheduleIndex) source.trajectoryMeasure := by
  dsimp only
  apply
    integrable_selfConsistentScheduledNaturalCausalStoppingTimeAverageSampledReturnProcess_of_integrable_realized
      (selfConsistentScheduledCausalSource mdp initialState rewardSource
        initialTable defaultState varianceProxy baseVisitFloor).trajectoryMeasure
      (AdaptiveStochasticEpisodeBatchSource.optimalInitialExpectedReturn
        mdp initialState)
      (selfConsistentScheduledNaturalCausalStoppingTimeAverageSampledReturnProcess
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor
          (selfConsistentScheduledNaturalCausalInverseSqrtThresholdUnboundedHittingAfterStoppingPrefix
            mdp initialState rewardSource initialTable defaultState varianceProxy
              baseVisitFloor) scheduleIndex)
      (selfConsistentScheduledNaturalCausalStoppingTimeAverageRealizedBehaviorRegretProcess
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor
          (selfConsistentScheduledNaturalCausalInverseSqrtThresholdUnboundedHittingAfterStoppingPrefix
            mdp initialState rewardSource initialTable defaultState varianceProxy
              baseVisitFloor) scheduleIndex)
  · intro trajectory
    exact
      selfConsistentScheduledNaturalCausalStoppingTimeAverageSampledReturnProcess_eq_optimal_sub_realized
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor
          (selfConsistentScheduledNaturalCausalInverseSqrtThresholdUnboundedHittingAfterStoppingPrefix
            mdp initialState rewardSource initialTable defaultState varianceProxy
              baseVisitFloor) scheduleIndex trajectory
  · exact
      (memLp_one_selfConsistentScheduledNaturalCausalInverseSqrtThresholdUnboundedHittingAfterStoppedAverageRealizedBehaviorRegret
        mdp initialState rewardSource varianceProxy hvarianceProxy law initialTable
          defaultState support baseVisitFloor hbaseFloor hrewardBound hhorizon
            hbaseVisitFloor scheduleIndex).integrable (by norm_num)

/-- For the capped prefix, expected sampled return is exactly optimal value
minus expected realized regret. -/
theorem selfConsistentScheduledNaturalCausalInverseSqrtThresholdCappedStoppedAverageSampledReturnIntegral_eq_optimal_sub_realized
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
    let realizedRegret :=
      selfConsistentScheduledNaturalCausalStoppingTimeAverageRealizedBehaviorRegretProcess
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor stoppingPrefix
    integral source.trajectoryMeasure (sampledReturn scheduleIndex) =
      AdaptiveStochasticEpisodeBatchSource.optimalInitialExpectedReturn
          mdp initialState -
        integral source.trajectoryMeasure (realizedRegret scheduleIndex) := by
  dsimp only
  apply
    integral_selfConsistentScheduledNaturalCausalStoppingTimeAverageSampledReturnProcess_eq_optimal_sub_realized
      (selfConsistentScheduledCausalSource mdp initialState rewardSource
        initialTable defaultState varianceProxy baseVisitFloor).trajectoryMeasure
      (AdaptiveStochasticEpisodeBatchSource.optimalInitialExpectedReturn
        mdp initialState)
  · intro trajectory
    exact
      selfConsistentScheduledNaturalCausalStoppingTimeAverageSampledReturnProcess_eq_optimal_sub_realized
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor
          (selfConsistentScheduledNaturalCausalInverseSqrtThresholdCappedDoubleLinearRawWindowFirstPassageStoppingPrefix
            mdp initialState rewardSource initialTable defaultState varianceProxy
              baseVisitFloor) scheduleIndex trajectory
  · exact
      (memLp_one_selfConsistentScheduledNaturalCausalInverseSqrtThresholdCappedStoppedAverageRealizedBehaviorRegret
        mdp initialState rewardSource varianceProxy hvarianceProxy law initialTable
          defaultState support baseVisitFloor hbaseFloor hrewardBound (by omega)
            hbaseVisitFloor scheduleIndex).integrable (by norm_num)

/-- For the uncapped prefix, expected sampled return is exactly optimal value
minus expected realized regret. -/
theorem selfConsistentScheduledNaturalCausalInverseSqrtThresholdUnboundedHittingAfterStoppedAverageSampledReturnIntegral_eq_optimal_sub_realized
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
    let realizedRegret :=
      selfConsistentScheduledNaturalCausalStoppingTimeAverageRealizedBehaviorRegretProcess
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor stoppingPrefix
    integral source.trajectoryMeasure (sampledReturn scheduleIndex) =
      AdaptiveStochasticEpisodeBatchSource.optimalInitialExpectedReturn
          mdp initialState -
        integral source.trajectoryMeasure (realizedRegret scheduleIndex) := by
  dsimp only
  apply
    integral_selfConsistentScheduledNaturalCausalStoppingTimeAverageSampledReturnProcess_eq_optimal_sub_realized
      (selfConsistentScheduledCausalSource mdp initialState rewardSource
        initialTable defaultState varianceProxy baseVisitFloor).trajectoryMeasure
      (AdaptiveStochasticEpisodeBatchSource.optimalInitialExpectedReturn
        mdp initialState)
  · intro trajectory
    exact
      selfConsistentScheduledNaturalCausalStoppingTimeAverageSampledReturnProcess_eq_optimal_sub_realized
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor
          (selfConsistentScheduledNaturalCausalInverseSqrtThresholdUnboundedHittingAfterStoppingPrefix
            mdp initialState rewardSource initialTable defaultState varianceProxy
              baseVisitFloor) scheduleIndex trajectory
  · exact
      (memLp_one_selfConsistentScheduledNaturalCausalInverseSqrtThresholdUnboundedHittingAfterStoppedAverageRealizedBehaviorRegret
        mdp initialState rewardSource varianceProxy hvarianceProxy law initialTable
          defaultState support baseVisitFloor hbaseFloor hrewardBound hhorizon
            hbaseVisitFloor scheduleIndex).integrable (by norm_num)

/-- Expected sampled return at the capped prefix converges to the optimal
initial expected return. -/
theorem selfConsistentScheduledNaturalCausalInverseSqrtThresholdCappedStoppedAverageSampledReturnIntegral_tendsto_optimal
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
    Tendsto (fun scheduleIndex =>
      integral source.trajectoryMeasure (sampledReturn scheduleIndex)) atTop
      (nhds (AdaptiveStochasticEpisodeBatchSource.optimalInitialExpectedReturn
        mdp initialState)) := by
  dsimp only
  rw [show (fun scheduleIndex =>
      integral
        (selfConsistentScheduledCausalSource mdp initialState rewardSource
          initialTable defaultState varianceProxy baseVisitFloor).trajectoryMeasure
        (selfConsistentScheduledNaturalCausalStoppingTimeAverageSampledReturnProcess
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
            (selfConsistentScheduledNaturalCausalStoppingTimeAverageRealizedBehaviorRegretProcess
              mdp initialState rewardSource initialTable defaultState varianceProxy
                baseVisitFloor
                (selfConsistentScheduledNaturalCausalInverseSqrtThresholdCappedDoubleLinearRawWindowFirstPassageStoppingPrefix
                  mdp initialState rewardSource initialTable defaultState varianceProxy
                    baseVisitFloor) scheduleIndex) by
    funext scheduleIndex
    exact
      selfConsistentScheduledNaturalCausalInverseSqrtThresholdCappedStoppedAverageSampledReturnIntegral_eq_optimal_sub_realized
        mdp initialState rewardSource varianceProxy hvarianceProxy law initialTable
          defaultState support baseVisitFloor hbaseFloor hrewardBound hhorizon
            hbaseVisitFloor scheduleIndex]
  simpa using
    (selfConsistentScheduledNaturalCausalInverseSqrtThresholdCappedStoppedAverageRealizedBehaviorRegretIntegral_tendsto_zero
      mdp initialState rewardSource varianceProxy hvarianceProxy law initialTable
        defaultState support baseVisitFloor hbaseFloor hrewardBound hhorizon
          hbaseVisitFloor).const_sub
      (AdaptiveStochasticEpisodeBatchSource.optimalInitialExpectedReturn
        mdp initialState)

/-- Expected sampled return at the genuine uncapped `hittingAfter` prefix
converges to the optimal initial expected return. -/
theorem selfConsistentScheduledNaturalCausalInverseSqrtThresholdUnboundedHittingAfterStoppedAverageSampledReturnIntegral_tendsto_optimal
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
    Tendsto (fun scheduleIndex =>
      integral source.trajectoryMeasure (sampledReturn scheduleIndex)) atTop
      (nhds (AdaptiveStochasticEpisodeBatchSource.optimalInitialExpectedReturn
        mdp initialState)) := by
  dsimp only
  rw [show (fun scheduleIndex =>
      integral
        (selfConsistentScheduledCausalSource mdp initialState rewardSource
          initialTable defaultState varianceProxy baseVisitFloor).trajectoryMeasure
        (selfConsistentScheduledNaturalCausalStoppingTimeAverageSampledReturnProcess
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
            (selfConsistentScheduledNaturalCausalStoppingTimeAverageRealizedBehaviorRegretProcess
              mdp initialState rewardSource initialTable defaultState varianceProxy
                baseVisitFloor
                (selfConsistentScheduledNaturalCausalInverseSqrtThresholdUnboundedHittingAfterStoppingPrefix
                  mdp initialState rewardSource initialTable defaultState varianceProxy
                    baseVisitFloor) scheduleIndex) by
    funext scheduleIndex
    exact
      selfConsistentScheduledNaturalCausalInverseSqrtThresholdUnboundedHittingAfterStoppedAverageSampledReturnIntegral_eq_optimal_sub_realized
        mdp initialState rewardSource varianceProxy hvarianceProxy law initialTable
          defaultState support baseVisitFloor hbaseFloor hrewardBound hhorizon
            hbaseVisitFloor scheduleIndex]
  simpa using
    (selfConsistentScheduledNaturalCausalInverseSqrtThresholdUnboundedHittingAfterStoppedAverageRealizedBehaviorRegretIntegral_tendsto_zero
      mdp initialState rewardSource varianceProxy hvarianceProxy law initialTable
        defaultState support baseVisitFloor hbaseFloor hrewardBound hhorizon
          hbaseVisitFloor).const_sub
      (AdaptiveStochasticEpisodeBatchSource.optimalInitialExpectedReturn
        mdp initialState)

/-- Terminal sampled-return semantics and expected-optimality package for the
capped approximation and the genuine uncapped stopping prefix. -/
theorem selfConsistentScheduledCausalSource_inverseSqrtThresholdCappedUnboundedHittingAfter_stoppedAverageSampledReturn_expected_optimality
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
    let cappedRealizedRegret :=
      selfConsistentScheduledNaturalCausalStoppingTimeAverageRealizedBehaviorRegretProcess
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor cappedStoppingPrefix
    let uncappedRealizedRegret :=
      selfConsistentScheduledNaturalCausalStoppingTimeAverageRealizedBehaviorRegretProcess
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor uncappedStoppingPrefix
    (forall scheduleIndex trajectory,
      cappedSampledReturn scheduleIndex trajectory =
          AdaptiveStochasticEpisodeBatchSource.optimalInitialExpectedReturn
              mdp initialState - cappedRealizedRegret scheduleIndex trajectory /\
        uncappedSampledReturn scheduleIndex trajectory =
          AdaptiveStochasticEpisodeBatchSource.optimalInitialExpectedReturn
              mdp initialState - uncappedRealizedRegret scheduleIndex trajectory) /\
    (forall scheduleIndex,
      Integrable (cappedSampledReturn scheduleIndex) source.trajectoryMeasure /\
        Integrable (uncappedSampledReturn scheduleIndex) source.trajectoryMeasure) /\
    (forall scheduleIndex,
      integral source.trajectoryMeasure (cappedSampledReturn scheduleIndex) =
          AdaptiveStochasticEpisodeBatchSource.optimalInitialExpectedReturn
              mdp initialState -
            integral source.trajectoryMeasure
              (cappedRealizedRegret scheduleIndex) /\
        integral source.trajectoryMeasure (uncappedSampledReturn scheduleIndex) =
          AdaptiveStochasticEpisodeBatchSource.optimalInitialExpectedReturn
              mdp initialState -
            integral source.trajectoryMeasure
              (uncappedRealizedRegret scheduleIndex)) /\
    Tendsto (fun scheduleIndex =>
      integral source.trajectoryMeasure (cappedSampledReturn scheduleIndex))
      atTop (nhds
        (AdaptiveStochasticEpisodeBatchSource.optimalInitialExpectedReturn
          mdp initialState)) /\
    Tendsto (fun scheduleIndex =>
      integral source.trajectoryMeasure (uncappedSampledReturn scheduleIndex))
      atTop (nhds
        (AdaptiveStochasticEpisodeBatchSource.optimalInitialExpectedReturn
          mdp initialState)) := by
  dsimp only
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro scheduleIndex trajectory
    exact ⟨
      selfConsistentScheduledNaturalCausalStoppingTimeAverageSampledReturnProcess_eq_optimal_sub_realized
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor
          (selfConsistentScheduledNaturalCausalInverseSqrtThresholdCappedDoubleLinearRawWindowFirstPassageStoppingPrefix
            mdp initialState rewardSource initialTable defaultState varianceProxy
              baseVisitFloor) scheduleIndex trajectory,
      selfConsistentScheduledNaturalCausalStoppingTimeAverageSampledReturnProcess_eq_optimal_sub_realized
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor
          (selfConsistentScheduledNaturalCausalInverseSqrtThresholdUnboundedHittingAfterStoppingPrefix
            mdp initialState rewardSource initialTable defaultState varianceProxy
              baseVisitFloor) scheduleIndex trajectory⟩
  · intro scheduleIndex
    exact ⟨
      integrable_selfConsistentScheduledNaturalCausalInverseSqrtThresholdCappedStoppedAverageSampledReturn
        mdp initialState rewardSource varianceProxy hvarianceProxy law initialTable
          defaultState support baseVisitFloor hbaseFloor hrewardBound hhorizon
            hbaseVisitFloor scheduleIndex,
      integrable_selfConsistentScheduledNaturalCausalInverseSqrtThresholdUnboundedHittingAfterStoppedAverageSampledReturn
        mdp initialState rewardSource varianceProxy hvarianceProxy law initialTable
          defaultState support baseVisitFloor hbaseFloor hrewardBound hhorizon
            hbaseVisitFloor scheduleIndex⟩
  · intro scheduleIndex
    exact ⟨
      selfConsistentScheduledNaturalCausalInverseSqrtThresholdCappedStoppedAverageSampledReturnIntegral_eq_optimal_sub_realized
        mdp initialState rewardSource varianceProxy hvarianceProxy law initialTable
          defaultState support baseVisitFloor hbaseFloor hrewardBound hhorizon
            hbaseVisitFloor scheduleIndex,
      selfConsistentScheduledNaturalCausalInverseSqrtThresholdUnboundedHittingAfterStoppedAverageSampledReturnIntegral_eq_optimal_sub_realized
        mdp initialState rewardSource varianceProxy hvarianceProxy law initialTable
          defaultState support baseVisitFloor hbaseFloor hrewardBound hhorizon
            hbaseVisitFloor scheduleIndex⟩
  · exact
      selfConsistentScheduledNaturalCausalInverseSqrtThresholdCappedStoppedAverageSampledReturnIntegral_tendsto_optimal
        mdp initialState rewardSource varianceProxy hvarianceProxy law initialTable
          defaultState support baseVisitFloor hbaseFloor hrewardBound hhorizon
            hbaseVisitFloor
  · exact
      selfConsistentScheduledNaturalCausalInverseSqrtThresholdUnboundedHittingAfterStoppedAverageSampledReturnIntegral_tendsto_optimal
        mdp initialState rewardSource varianceProxy hvarianceProxy law initialTable
          defaultState support baseVisitFloor hbaseFloor hrewardBound hhorizon
            hbaseVisitFloor

end AdaptiveStochasticSampledEmpiricalOptimisticSource

end BanditRLProof.FiniteHorizonRL
