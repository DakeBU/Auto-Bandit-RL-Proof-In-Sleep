import BanditRLProof.RL.FiniteHorizonNaturalCausalInverseSqrtThresholdCappedUnboundedHittingAfterStoppedSampledAndSuccessorPolicyReturnL1Optimality

/-!
# Stopped sampled and successor-policy return convergence modes

This module upgrades the exact capped and uncapped stopped-return `L1` route
to literal convergence in measure and almost-sure convergence.  The sampled
return and the trajectory-law expected return of the actually selected
successor policies converge to the optimal initial expected return, while
their same-prefix difference converges to zero.

The proof only transports already compiled process identities, `L1` limits,
and almost-sure regret limits.  It does not interchange expectation with a
random stopping index and does not use optional stopping.
-/

open Filter MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal ProbabilityTheory Topology BigOperators

namespace BanditRLProof.FiniteHorizonRL

universe u v

variable {State : Type u} {Action : Type v}
    [MeasurableSpace State] [MeasurableSpace Action]
    [Fintype State] [Fintype Action]
    [DecidableEq State] [DecidableEq Action]
    [MeasurableSingletonClass State] [MeasurableSingletonClass Action]
    [Nonempty State] [Nonempty Action]

namespace AdaptiveStochasticSampledEmpiricalOptimisticSource

/-- The capped stopped realized-regret process inherits the genuine uncapped
almost-sure limit because the two processes are eventually equal almost
surely. -/
theorem
    selfConsistentScheduledCausalSource_inverseSqrtThresholdCapped_stoppedAverageRealizedBehaviorRegret_tendstoAlmostEverywhere_zero
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
    (hhorizon : 0 < mdp.horizon) (hbaseVisitFloor : 0 < baseVisitFloor) :
    let source := selfConsistentScheduledCausalSource mdp initialState
      rewardSource initialTable defaultState varianceProxy baseVisitFloor
    let cappedStoppingPrefix :=
      selfConsistentScheduledNaturalCausalInverseSqrtThresholdCappedDoubleLinearRawWindowFirstPassageStoppingPrefix
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor
    let cappedProcess :=
      selfConsistentScheduledNaturalCausalStoppingTimeAverageRealizedBehaviorRegretProcess
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor cappedStoppingPrefix
    ∀ᵐ trajectory ∂source.trajectoryMeasure,
      Tendsto (fun scheduleIndex => cappedProcess scheduleIndex trajectory)
        atTop (nhds 0) := by
  dsimp only
  have huncapped :=
    (selfConsistentScheduledCausalSource_inverseSqrtThresholdUnboundedHittingAfter_stoppedProcess_tendstoAlmostEverywhere_zero
      mdp initialState rewardSource varianceProxy hvarianceProxy law initialTable
        defaultState support baseVisitFloor hbaseFloor hrewardBound hhorizon
          hbaseVisitFloor).2.2
  have heventuallyEq :=
    ae_eventually_selfConsistentScheduledNaturalCausalInverseSqrtThresholdCappedStoppedAverageRealizedBehaviorRegret_eq_unboundedHittingAfter
      mdp initialState rewardSource varianceProxy hvarianceProxy law initialTable
        defaultState support baseVisitFloor hbaseFloor hrewardBound hhorizon
          hbaseVisitFloor
  filter_upwards [huncapped, heventuallyEq] with trajectory hlimit heq
  apply hlimit.congr'
  filter_upwards [heq] with scheduleIndex hscheduleIndex
  exact hscheduleIndex.symm

/-- The stopped return deviation is behavior expected regret minus realized
behavior regret, pointwise at any common stopping prefix. -/
theorem
    selfConsistentScheduledNaturalCausalStoppingTimeAverageReturnDeviationProcess_eq_behaviorExpected_sub_realized
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
    selfConsistentScheduledNaturalCausalStoppingTimeAverageReturnDeviationProcess
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor stoppingPrefix scheduleIndex =
      fun trajectory =>
        selfConsistentScheduledNaturalCausalStoppingTimeAverageBehaviorExpectedRegretProcess
              mdp initialState rewardSource initialTable defaultState varianceProxy
                baseVisitFloor stoppingPrefix scheduleIndex trajectory -
          selfConsistentScheduledNaturalCausalStoppingTimeAverageRealizedBehaviorRegretProcess
            mdp initialState rewardSource initialTable defaultState varianceProxy
              baseVisitFloor stoppingPrefix scheduleIndex trajectory := by
  funext trajectory
  have hdecomposition :=
    selfConsistentScheduledNaturalCausalStoppingTimeAverageRealizedBehaviorRegretProcess_eq_behaviorExpected_sub_returnDeviation
      mdp initialState rewardSource initialTable defaultState varianceProxy
        baseVisitFloor stoppingPrefix scheduleIndex trajectory
  linarith

/-- The literal capped stopped sampled return converges in measure to the
optimal initial expected return. -/
theorem
    selfConsistentScheduledNaturalCausalInverseSqrtThresholdCappedStoppedAverageSampledReturn_tendstoInMeasure_optimal
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
    TendstoInMeasure source.trajectoryMeasure sampledReturn atTop
      (fun _ => AdaptiveStochasticEpisodeBatchSource.optimalInitialExpectedReturn
        mdp initialState) := by
  dsimp only
  apply tendstoInMeasure_of_tendsto_eLpNorm one_ne_zero
  · intro scheduleIndex
    exact
      (integrable_selfConsistentScheduledNaturalCausalInverseSqrtThresholdCappedStoppedAverageSampledReturn
        mdp initialState rewardSource varianceProxy hvarianceProxy law initialTable
          defaultState support baseVisitFloor hbaseFloor hrewardBound hhorizon
            hbaseVisitFloor scheduleIndex).aestronglyMeasurable
  · fun_prop
  · simpa only [Pi.sub_apply,
      selfConsistentScheduledNaturalCausalStoppingTimeAverageSampledReturnOptimalityErrorProcess] using
      (eLpNorm_one_selfConsistentScheduledNaturalCausalInverseSqrtThresholdCappedStoppedSampledReturnOptimalityError_tendsto_zero
        mdp initialState rewardSource varianceProxy hvarianceProxy law initialTable
          defaultState support baseVisitFloor hbaseFloor hrewardBound (by omega)
            hbaseVisitFloor)

/-- The literal uncapped stopped sampled return converges in measure to the
optimal initial expected return. -/
theorem
    selfConsistentScheduledNaturalCausalInverseSqrtThresholdUnboundedHittingAfterStoppedAverageSampledReturn_tendstoInMeasure_optimal
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
    TendstoInMeasure source.trajectoryMeasure sampledReturn atTop
      (fun _ => AdaptiveStochasticEpisodeBatchSource.optimalInitialExpectedReturn
        mdp initialState) := by
  dsimp only
  apply tendstoInMeasure_of_tendsto_eLpNorm one_ne_zero
  · intro scheduleIndex
    exact
      (integrable_selfConsistentScheduledNaturalCausalInverseSqrtThresholdUnboundedHittingAfterStoppedAverageSampledReturn
        mdp initialState rewardSource varianceProxy hvarianceProxy law initialTable
          defaultState support baseVisitFloor hbaseFloor hrewardBound hhorizon
            hbaseVisitFloor scheduleIndex).aestronglyMeasurable
  · fun_prop
  · simpa only [Pi.sub_apply,
      selfConsistentScheduledNaturalCausalStoppingTimeAverageSampledReturnOptimalityErrorProcess] using
      (eLpNorm_one_selfConsistentScheduledNaturalCausalInverseSqrtThresholdUnboundedHittingAfterStoppedSampledReturnOptimalityError_tendsto_zero
        mdp initialState rewardSource varianceProxy hvarianceProxy law initialTable
          defaultState support baseVisitFloor hbaseFloor hrewardBound hhorizon
            hbaseVisitFloor)

/-- The literal capped stopped expected return of the selected successor
policies converges in measure to the optimal initial expected return. -/
theorem
    selfConsistentScheduledNaturalCausalInverseSqrtThresholdCappedStoppedAverageSuccessorPolicyExpectedReturn_tendstoInMeasure_optimal
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
    TendstoInMeasure source.trajectoryMeasure policyReturn atTop
      (fun _ => AdaptiveStochasticEpisodeBatchSource.optimalInitialExpectedReturn
        mdp initialState) := by
  dsimp only
  apply tendstoInMeasure_of_tendsto_eLpNorm one_ne_zero
  · intro scheduleIndex
    exact
      (integrable_selfConsistentScheduledNaturalCausalInverseSqrtThresholdCappedStoppedAverageSuccessorPolicyExpectedReturn
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor hrewardBound scheduleIndex).aestronglyMeasurable
  · fun_prop
  · simpa only [Pi.sub_apply,
      selfConsistentScheduledNaturalCausalStoppingTimeAverageSuccessorPolicyExpectedReturnOptimalityErrorProcess] using
      (eLpNorm_one_selfConsistentScheduledNaturalCausalInverseSqrtThresholdCappedStoppedSuccessorPolicyExpectedReturnOptimalityError_tendsto_zero
        mdp initialState rewardSource varianceProxy hvarianceProxy law initialTable
          defaultState support baseVisitFloor hbaseFloor hrewardBound (by omega)
            hbaseVisitFloor)

/-- The literal uncapped stopped expected return of the selected successor
policies converges in measure to the optimal initial expected return. -/
theorem
    selfConsistentScheduledNaturalCausalInverseSqrtThresholdUnboundedHittingAfterStoppedAverageSuccessorPolicyExpectedReturn_tendstoInMeasure_optimal
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
    TendstoInMeasure source.trajectoryMeasure policyReturn atTop
      (fun _ => AdaptiveStochasticEpisodeBatchSource.optimalInitialExpectedReturn
        mdp initialState) := by
  dsimp only
  apply tendstoInMeasure_of_tendsto_eLpNorm one_ne_zero
  · intro scheduleIndex
    exact
      (integrable_selfConsistentScheduledNaturalCausalInverseSqrtThresholdUnboundedHittingAfterStoppedAverageSuccessorPolicyExpectedReturn
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor hrewardBound scheduleIndex).aestronglyMeasurable
  · fun_prop
  · simpa only [Pi.sub_apply,
      selfConsistentScheduledNaturalCausalStoppingTimeAverageSuccessorPolicyExpectedReturnOptimalityErrorProcess] using
      (eLpNorm_one_selfConsistentScheduledNaturalCausalInverseSqrtThresholdUnboundedHittingAfterStoppedSuccessorPolicyExpectedReturnOptimalityError_tendsto_zero
        mdp initialState rewardSource varianceProxy hvarianceProxy law initialTable
          defaultState support baseVisitFloor hbaseFloor hrewardBound (by omega)
            hbaseVisitFloor)

/-- The capped same-prefix sampled/policy return gap converges in measure to
zero. -/
theorem
    selfConsistentScheduledNaturalCausalInverseSqrtThresholdCappedStoppedSampledPolicyExpectedReturnGap_tendstoInMeasure_zero
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
    let gapProcess :=
      selfConsistentScheduledNaturalCausalStoppingTimeAverageSampledPolicyExpectedReturnGapProcess
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor stoppingPrefix
    TendstoInMeasure source.trajectoryMeasure gapProcess atTop (fun _ => 0) := by
  dsimp only
  apply tendstoInMeasure_of_tendsto_eLpNorm one_ne_zero
  · intro scheduleIndex
    exact
      (memLp_one_selfConsistentScheduledNaturalCausalInverseSqrtThresholdCappedStoppedSampledPolicyExpectedReturnGap
        mdp initialState rewardSource varianceProxy hvarianceProxy law initialTable
          defaultState support baseVisitFloor hbaseFloor hrewardBound hhorizon
            hbaseVisitFloor scheduleIndex).aestronglyMeasurable
  · fun_prop
  · have hnorm :=
      eLpNorm_one_selfConsistentScheduledNaturalCausalInverseSqrtThresholdCappedStoppedSampledPolicyExpectedReturnGap_tendsto_zero
        mdp initialState rewardSource varianceProxy hvarianceProxy law initialTable
          defaultState support baseVisitFloor hbaseFloor hrewardBound hhorizon
            hbaseVisitFloor
    convert hnorm using 1
    funext scheduleIndex
    apply eLpNorm_congr_ae
    exact Filter.Eventually.of_forall fun trajectory => by simp

/-- The uncapped same-prefix sampled/policy return gap converges in measure to
zero. -/
theorem
    selfConsistentScheduledNaturalCausalInverseSqrtThresholdUnboundedHittingAfterStoppedSampledPolicyExpectedReturnGap_tendstoInMeasure_zero
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
    let gapProcess :=
      selfConsistentScheduledNaturalCausalStoppingTimeAverageSampledPolicyExpectedReturnGapProcess
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor stoppingPrefix
    TendstoInMeasure source.trajectoryMeasure gapProcess atTop (fun _ => 0) := by
  dsimp only
  apply tendstoInMeasure_of_tendsto_eLpNorm one_ne_zero
  · intro scheduleIndex
    exact
      (memLp_one_selfConsistentScheduledNaturalCausalInverseSqrtThresholdUnboundedHittingAfterStoppedSampledPolicyExpectedReturnGap
        mdp initialState rewardSource varianceProxy hvarianceProxy law initialTable
          defaultState support baseVisitFloor hbaseFloor hrewardBound hhorizon
            hbaseVisitFloor scheduleIndex).aestronglyMeasurable
  · fun_prop
  · have hnorm :=
      eLpNorm_one_selfConsistentScheduledNaturalCausalInverseSqrtThresholdUnboundedHittingAfterStoppedSampledPolicyExpectedReturnGap_tendsto_zero
        mdp initialState rewardSource varianceProxy hvarianceProxy law initialTable
          defaultState support baseVisitFloor hbaseFloor hrewardBound hhorizon
            hbaseVisitFloor
    convert hnorm using 1
    funext scheduleIndex
    apply eLpNorm_congr_ae
    exact Filter.Eventually.of_forall fun trajectory => by simp

/-- The literal capped stopped sampled return converges almost surely to the
optimal initial expected return. -/
theorem
    selfConsistentScheduledCausalSource_inverseSqrtThresholdCapped_stoppedAverageSampledReturn_tendstoAlmostEverywhere_optimal
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
    ∀ᵐ trajectory ∂source.trajectoryMeasure,
      Tendsto (fun scheduleIndex => sampledReturn scheduleIndex trajectory)
        atTop (nhds
          (AdaptiveStochasticEpisodeBatchSource.optimalInitialExpectedReturn
            mdp initialState)) := by
  dsimp only
  have hrealized :=
    selfConsistentScheduledCausalSource_inverseSqrtThresholdCapped_stoppedAverageRealizedBehaviorRegret_tendstoAlmostEverywhere_zero
      mdp initialState rewardSource varianceProxy hvarianceProxy law initialTable
        defaultState support baseVisitFloor hbaseFloor hrewardBound (by omega)
          hbaseVisitFloor
  filter_upwards [hrealized] with trajectory hlimit
  have hsampled : Tendsto
      (fun scheduleIndex =>
        selfConsistentScheduledNaturalCausalStoppingTimeAverageSampledReturnProcess
          mdp initialState rewardSource initialTable defaultState varianceProxy
            baseVisitFloor
            (selfConsistentScheduledNaturalCausalInverseSqrtThresholdCappedDoubleLinearRawWindowFirstPassageStoppingPrefix
              mdp initialState rewardSource initialTable defaultState varianceProxy
                baseVisitFloor) scheduleIndex trajectory)
      atTop (nhds
        (AdaptiveStochasticEpisodeBatchSource.optimalInitialExpectedReturn
          mdp initialState - 0)) := by
    apply (hlimit.const_sub
      (AdaptiveStochasticEpisodeBatchSource.optimalInitialExpectedReturn
        mdp initialState)).congr'
    filter_upwards with scheduleIndex
    exact
      (selfConsistentScheduledNaturalCausalStoppingTimeAverageSampledReturnProcess_eq_optimal_sub_realized
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor
          (selfConsistentScheduledNaturalCausalInverseSqrtThresholdCappedDoubleLinearRawWindowFirstPassageStoppingPrefix
            mdp initialState rewardSource initialTable defaultState varianceProxy
              baseVisitFloor) scheduleIndex trajectory).symm
  simpa only [sub_zero] using hsampled

/-- The literal uncapped stopped sampled return converges almost surely to the
optimal initial expected return. -/
theorem
    selfConsistentScheduledCausalSource_inverseSqrtThresholdUnboundedHittingAfter_stoppedAverageSampledReturn_tendstoAlmostEverywhere_optimal
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
    ∀ᵐ trajectory ∂source.trajectoryMeasure,
      Tendsto (fun scheduleIndex => sampledReturn scheduleIndex trajectory)
        atTop (nhds
          (AdaptiveStochasticEpisodeBatchSource.optimalInitialExpectedReturn
            mdp initialState)) := by
  dsimp only
  have hrealized :=
    (selfConsistentScheduledCausalSource_inverseSqrtThresholdUnboundedHittingAfter_stoppedProcess_tendstoAlmostEverywhere_zero
      mdp initialState rewardSource varianceProxy hvarianceProxy law initialTable
        defaultState support baseVisitFloor hbaseFloor hrewardBound (by omega)
          hbaseVisitFloor).2.2
  filter_upwards [hrealized] with trajectory hlimit
  have hsampled : Tendsto
      (fun scheduleIndex =>
        selfConsistentScheduledNaturalCausalStoppingTimeAverageSampledReturnProcess
          mdp initialState rewardSource initialTable defaultState varianceProxy
            baseVisitFloor
            (selfConsistentScheduledNaturalCausalInverseSqrtThresholdUnboundedHittingAfterStoppingPrefix
              mdp initialState rewardSource initialTable defaultState varianceProxy
                baseVisitFloor) scheduleIndex trajectory)
      atTop (nhds
        (AdaptiveStochasticEpisodeBatchSource.optimalInitialExpectedReturn
          mdp initialState - 0)) := by
    apply (hlimit.const_sub
      (AdaptiveStochasticEpisodeBatchSource.optimalInitialExpectedReturn
        mdp initialState)).congr'
    filter_upwards with scheduleIndex
    exact
      (selfConsistentScheduledNaturalCausalStoppingTimeAverageSampledReturnProcess_eq_optimal_sub_realized
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor
          (selfConsistentScheduledNaturalCausalInverseSqrtThresholdUnboundedHittingAfterStoppingPrefix
            mdp initialState rewardSource initialTable defaultState varianceProxy
              baseVisitFloor) scheduleIndex trajectory).symm
  simpa only [sub_zero] using hsampled

/-- The literal capped stopped expected return of the selected successor
policies converges almost surely to the optimal initial expected return. -/
theorem
    selfConsistentScheduledCausalSource_inverseSqrtThresholdCapped_stoppedAverageSuccessorPolicyExpectedReturn_tendstoAlmostEverywhere_optimal
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
    ∀ᵐ trajectory ∂source.trajectoryMeasure,
      Tendsto (fun scheduleIndex => policyReturn scheduleIndex trajectory)
        atTop (nhds
          (AdaptiveStochasticEpisodeBatchSource.optimalInitialExpectedReturn
            mdp initialState)) := by
  dsimp only
  have hbehavior :=
    selfConsistentScheduledCausalSource_inverseSqrtThresholdCapped_stoppedBehaviorExpectedRegret_tendstoAlmostEverywhere_zero
      mdp initialState rewardSource varianceProxy hvarianceProxy law initialTable
        defaultState support baseVisitFloor hbaseFloor hrewardBound (by omega)
          hbaseVisitFloor
  filter_upwards [hbehavior] with trajectory hlimit
  have hpolicy : Tendsto
      (fun scheduleIndex =>
        selfConsistentScheduledNaturalCausalStoppingTimeAverageSuccessorPolicyExpectedReturnProcess
          mdp initialState rewardSource initialTable defaultState varianceProxy
            baseVisitFloor
            (selfConsistentScheduledNaturalCausalInverseSqrtThresholdCappedDoubleLinearRawWindowFirstPassageStoppingPrefix
              mdp initialState rewardSource initialTable defaultState varianceProxy
                baseVisitFloor) scheduleIndex trajectory)
      atTop (nhds
        (AdaptiveStochasticEpisodeBatchSource.optimalInitialExpectedReturn
          mdp initialState - 0)) := by
    apply (hlimit.const_sub
      (AdaptiveStochasticEpisodeBatchSource.optimalInitialExpectedReturn
        mdp initialState)).congr'
    filter_upwards with scheduleIndex
    exact
      (selfConsistentScheduledNaturalCausalStoppingTimeAverageSuccessorPolicyExpectedReturnProcess_eq_optimal_sub_behaviorExpected
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor
          (selfConsistentScheduledNaturalCausalInverseSqrtThresholdCappedDoubleLinearRawWindowFirstPassageStoppingPrefix
            mdp initialState rewardSource initialTable defaultState varianceProxy
              baseVisitFloor) scheduleIndex trajectory).symm
  simpa only [sub_zero] using hpolicy

/-- The literal uncapped stopped expected return of the selected successor
policies converges almost surely to the optimal initial expected return. -/
theorem
    selfConsistentScheduledCausalSource_inverseSqrtThresholdUnboundedHittingAfter_stoppedAverageSuccessorPolicyExpectedReturn_tendstoAlmostEverywhere_optimal
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
    ∀ᵐ trajectory ∂source.trajectoryMeasure,
      Tendsto (fun scheduleIndex => policyReturn scheduleIndex trajectory)
        atTop (nhds
          (AdaptiveStochasticEpisodeBatchSource.optimalInitialExpectedReturn
            mdp initialState)) := by
  dsimp only
  have hbehavior :=
    selfConsistentScheduledCausalSource_inverseSqrtThresholdUnboundedHittingAfter_stoppedBehaviorExpectedRegret_tendstoAlmostEverywhere_zero
      mdp initialState rewardSource varianceProxy hvarianceProxy law initialTable
        defaultState support baseVisitFloor hbaseFloor hrewardBound (by omega)
          hbaseVisitFloor
  filter_upwards [hbehavior] with trajectory hlimit
  have hpolicy : Tendsto
      (fun scheduleIndex =>
        selfConsistentScheduledNaturalCausalStoppingTimeAverageSuccessorPolicyExpectedReturnProcess
          mdp initialState rewardSource initialTable defaultState varianceProxy
            baseVisitFloor
            (selfConsistentScheduledNaturalCausalInverseSqrtThresholdUnboundedHittingAfterStoppingPrefix
              mdp initialState rewardSource initialTable defaultState varianceProxy
                baseVisitFloor) scheduleIndex trajectory)
      atTop (nhds
        (AdaptiveStochasticEpisodeBatchSource.optimalInitialExpectedReturn
          mdp initialState - 0)) := by
    apply (hlimit.const_sub
      (AdaptiveStochasticEpisodeBatchSource.optimalInitialExpectedReturn
        mdp initialState)).congr'
    filter_upwards with scheduleIndex
    exact
      (selfConsistentScheduledNaturalCausalStoppingTimeAverageSuccessorPolicyExpectedReturnProcess_eq_optimal_sub_behaviorExpected
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor
          (selfConsistentScheduledNaturalCausalInverseSqrtThresholdUnboundedHittingAfterStoppingPrefix
            mdp initialState rewardSource initialTable defaultState varianceProxy
              baseVisitFloor) scheduleIndex trajectory).symm
  simpa only [sub_zero] using hpolicy

/-- The capped same-prefix sampled/policy return gap converges almost surely to
zero. -/
theorem
    selfConsistentScheduledCausalSource_inverseSqrtThresholdCapped_stoppedSampledPolicyExpectedReturnGap_tendstoAlmostEverywhere_zero
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
    let gapProcess :=
      selfConsistentScheduledNaturalCausalStoppingTimeAverageSampledPolicyExpectedReturnGapProcess
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor stoppingPrefix
    ∀ᵐ trajectory ∂source.trajectoryMeasure,
      Tendsto (fun scheduleIndex => gapProcess scheduleIndex trajectory)
        atTop (nhds 0) := by
  dsimp only
  have hbehavior :=
    selfConsistentScheduledCausalSource_inverseSqrtThresholdCapped_stoppedBehaviorExpectedRegret_tendstoAlmostEverywhere_zero
      mdp initialState rewardSource varianceProxy hvarianceProxy law initialTable
        defaultState support baseVisitFloor hbaseFloor hrewardBound (by omega)
          hbaseVisitFloor
  have hrealized :=
    selfConsistentScheduledCausalSource_inverseSqrtThresholdCapped_stoppedAverageRealizedBehaviorRegret_tendstoAlmostEverywhere_zero
      mdp initialState rewardSource varianceProxy hvarianceProxy law initialTable
        defaultState support baseVisitFloor hbaseFloor hrewardBound (by omega)
          hbaseVisitFloor
  filter_upwards [hbehavior, hrealized] with trajectory hbehaviorLimit hrealizedLimit
  have hgap : Tendsto
      (fun scheduleIndex =>
        selfConsistentScheduledNaturalCausalStoppingTimeAverageSampledPolicyExpectedReturnGapProcess
          mdp initialState rewardSource initialTable defaultState varianceProxy
            baseVisitFloor
            (selfConsistentScheduledNaturalCausalInverseSqrtThresholdCappedDoubleLinearRawWindowFirstPassageStoppingPrefix
              mdp initialState rewardSource initialTable defaultState varianceProxy
                baseVisitFloor) scheduleIndex trajectory)
      atTop (nhds (0 - 0)) := by
    apply (hbehaviorLimit.sub hrealizedLimit).congr'
    filter_upwards with scheduleIndex
    calc
      _ = selfConsistentScheduledNaturalCausalStoppingTimeAverageReturnDeviationProcess
            mdp initialState rewardSource initialTable defaultState varianceProxy
              baseVisitFloor
              (selfConsistentScheduledNaturalCausalInverseSqrtThresholdCappedDoubleLinearRawWindowFirstPassageStoppingPrefix
                mdp initialState rewardSource initialTable defaultState varianceProxy
                  baseVisitFloor) scheduleIndex trajectory :=
        (congrFun
          (selfConsistentScheduledNaturalCausalStoppingTimeAverageReturnDeviationProcess_eq_behaviorExpected_sub_realized
            mdp initialState rewardSource initialTable defaultState varianceProxy
              baseVisitFloor
              (selfConsistentScheduledNaturalCausalInverseSqrtThresholdCappedDoubleLinearRawWindowFirstPassageStoppingPrefix
                mdp initialState rewardSource initialTable defaultState varianceProxy
                  baseVisitFloor) scheduleIndex) trajectory).symm
      _ = _ :=
        (congrFun
          (selfConsistentScheduledNaturalCausalStoppingTimeAverageSampledPolicyExpectedReturnGapProcess_eq_returnDeviation
            mdp initialState rewardSource initialTable defaultState varianceProxy
              baseVisitFloor
              (selfConsistentScheduledNaturalCausalInverseSqrtThresholdCappedDoubleLinearRawWindowFirstPassageStoppingPrefix
                mdp initialState rewardSource initialTable defaultState varianceProxy
                  baseVisitFloor) scheduleIndex) trajectory).symm
  simpa only [sub_zero] using hgap

/-- The uncapped same-prefix sampled/policy return gap converges almost surely
to zero. -/
theorem
    selfConsistentScheduledCausalSource_inverseSqrtThresholdUnboundedHittingAfter_stoppedSampledPolicyExpectedReturnGap_tendstoAlmostEverywhere_zero
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
    let gapProcess :=
      selfConsistentScheduledNaturalCausalStoppingTimeAverageSampledPolicyExpectedReturnGapProcess
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor stoppingPrefix
    ∀ᵐ trajectory ∂source.trajectoryMeasure,
      Tendsto (fun scheduleIndex => gapProcess scheduleIndex trajectory)
        atTop (nhds 0) := by
  dsimp only
  have hbehavior :=
    selfConsistentScheduledCausalSource_inverseSqrtThresholdUnboundedHittingAfter_stoppedBehaviorExpectedRegret_tendstoAlmostEverywhere_zero
      mdp initialState rewardSource varianceProxy hvarianceProxy law initialTable
        defaultState support baseVisitFloor hbaseFloor hrewardBound (by omega)
          hbaseVisitFloor
  have hrealized :=
    (selfConsistentScheduledCausalSource_inverseSqrtThresholdUnboundedHittingAfter_stoppedProcess_tendstoAlmostEverywhere_zero
      mdp initialState rewardSource varianceProxy hvarianceProxy law initialTable
        defaultState support baseVisitFloor hbaseFloor hrewardBound (by omega)
          hbaseVisitFloor).2.2
  filter_upwards [hbehavior, hrealized] with trajectory hbehaviorLimit hrealizedLimit
  have hgap : Tendsto
      (fun scheduleIndex =>
        selfConsistentScheduledNaturalCausalStoppingTimeAverageSampledPolicyExpectedReturnGapProcess
          mdp initialState rewardSource initialTable defaultState varianceProxy
            baseVisitFloor
            (selfConsistentScheduledNaturalCausalInverseSqrtThresholdUnboundedHittingAfterStoppingPrefix
              mdp initialState rewardSource initialTable defaultState varianceProxy
                baseVisitFloor) scheduleIndex trajectory)
      atTop (nhds (0 - 0)) := by
    apply (hbehaviorLimit.sub hrealizedLimit).congr'
    filter_upwards with scheduleIndex
    calc
      _ = selfConsistentScheduledNaturalCausalStoppingTimeAverageReturnDeviationProcess
            mdp initialState rewardSource initialTable defaultState varianceProxy
              baseVisitFloor
              (selfConsistentScheduledNaturalCausalInverseSqrtThresholdUnboundedHittingAfterStoppingPrefix
                mdp initialState rewardSource initialTable defaultState varianceProxy
                  baseVisitFloor) scheduleIndex trajectory :=
        (congrFun
          (selfConsistentScheduledNaturalCausalStoppingTimeAverageReturnDeviationProcess_eq_behaviorExpected_sub_realized
            mdp initialState rewardSource initialTable defaultState varianceProxy
              baseVisitFloor
              (selfConsistentScheduledNaturalCausalInverseSqrtThresholdUnboundedHittingAfterStoppingPrefix
                mdp initialState rewardSource initialTable defaultState varianceProxy
                  baseVisitFloor) scheduleIndex) trajectory).symm
      _ = _ :=
        (congrFun
          (selfConsistentScheduledNaturalCausalStoppingTimeAverageSampledPolicyExpectedReturnGapProcess_eq_returnDeviation
            mdp initialState rewardSource initialTable defaultState varianceProxy
              baseVisitFloor
              (selfConsistentScheduledNaturalCausalInverseSqrtThresholdUnboundedHittingAfterStoppingPrefix
                mdp initialState rewardSource initialTable defaultState varianceProxy
                  baseVisitFloor) scheduleIndex) trajectory).symm
  simpa only [sub_zero] using hgap

/-- Terminal convergence-mode package for literal stopped sampled return, the
literal expected return of the actually selected successor policies, and their
same-prefix gap at the capped and genuine uncapped stopping prefixes. -/
theorem
    selfConsistentScheduledCausalSource_inverseSqrtThresholdCappedUnboundedHittingAfter_stoppedSampledReturn_and_successorPolicyExpectedReturn_inMeasure_and_almostSure_optimality
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
    let cappedGap :=
      selfConsistentScheduledNaturalCausalStoppingTimeAverageSampledPolicyExpectedReturnGapProcess
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor cappedStoppingPrefix
    let uncappedGap :=
      selfConsistentScheduledNaturalCausalStoppingTimeAverageSampledPolicyExpectedReturnGapProcess
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor uncappedStoppingPrefix
    let optimal :=
      AdaptiveStochasticEpisodeBatchSource.optimalInitialExpectedReturn
        mdp initialState
    TendstoInMeasure source.trajectoryMeasure cappedSampledReturn atTop
      (fun _ => optimal) /\
    TendstoInMeasure source.trajectoryMeasure uncappedSampledReturn atTop
      (fun _ => optimal) /\
    TendstoInMeasure source.trajectoryMeasure cappedPolicyReturn atTop
      (fun _ => optimal) /\
    TendstoInMeasure source.trajectoryMeasure uncappedPolicyReturn atTop
      (fun _ => optimal) /\
    TendstoInMeasure source.trajectoryMeasure cappedGap atTop (fun _ => 0) /\
    TendstoInMeasure source.trajectoryMeasure uncappedGap atTop (fun _ => 0) /\
    (∀ᵐ trajectory ∂source.trajectoryMeasure,
      Tendsto (fun scheduleIndex => cappedSampledReturn scheduleIndex trajectory)
        atTop (nhds optimal)) /\
    (∀ᵐ trajectory ∂source.trajectoryMeasure,
      Tendsto (fun scheduleIndex => uncappedSampledReturn scheduleIndex trajectory)
        atTop (nhds optimal)) /\
    (∀ᵐ trajectory ∂source.trajectoryMeasure,
      Tendsto (fun scheduleIndex => cappedPolicyReturn scheduleIndex trajectory)
        atTop (nhds optimal)) /\
    (∀ᵐ trajectory ∂source.trajectoryMeasure,
      Tendsto (fun scheduleIndex => uncappedPolicyReturn scheduleIndex trajectory)
        atTop (nhds optimal)) /\
    (∀ᵐ trajectory ∂source.trajectoryMeasure,
      Tendsto (fun scheduleIndex => cappedGap scheduleIndex trajectory)
        atTop (nhds 0)) /\
    (∀ᵐ trajectory ∂source.trajectoryMeasure,
      Tendsto (fun scheduleIndex => uncappedGap scheduleIndex trajectory)
        atTop (nhds 0)) := by
  dsimp only
  exact
    ⟨selfConsistentScheduledNaturalCausalInverseSqrtThresholdCappedStoppedAverageSampledReturn_tendstoInMeasure_optimal
        mdp initialState rewardSource varianceProxy hvarianceProxy law initialTable
          defaultState support baseVisitFloor hbaseFloor hrewardBound hhorizon
            hbaseVisitFloor,
      selfConsistentScheduledNaturalCausalInverseSqrtThresholdUnboundedHittingAfterStoppedAverageSampledReturn_tendstoInMeasure_optimal
        mdp initialState rewardSource varianceProxy hvarianceProxy law initialTable
          defaultState support baseVisitFloor hbaseFloor hrewardBound hhorizon
            hbaseVisitFloor,
      selfConsistentScheduledNaturalCausalInverseSqrtThresholdCappedStoppedAverageSuccessorPolicyExpectedReturn_tendstoInMeasure_optimal
        mdp initialState rewardSource varianceProxy hvarianceProxy law initialTable
          defaultState support baseVisitFloor hbaseFloor hrewardBound hhorizon
            hbaseVisitFloor,
      selfConsistentScheduledNaturalCausalInverseSqrtThresholdUnboundedHittingAfterStoppedAverageSuccessorPolicyExpectedReturn_tendstoInMeasure_optimal
        mdp initialState rewardSource varianceProxy hvarianceProxy law initialTable
          defaultState support baseVisitFloor hbaseFloor hrewardBound hhorizon
            hbaseVisitFloor,
      selfConsistentScheduledNaturalCausalInverseSqrtThresholdCappedStoppedSampledPolicyExpectedReturnGap_tendstoInMeasure_zero
        mdp initialState rewardSource varianceProxy hvarianceProxy law initialTable
          defaultState support baseVisitFloor hbaseFloor hrewardBound hhorizon
            hbaseVisitFloor,
      selfConsistentScheduledNaturalCausalInverseSqrtThresholdUnboundedHittingAfterStoppedSampledPolicyExpectedReturnGap_tendstoInMeasure_zero
        mdp initialState rewardSource varianceProxy hvarianceProxy law initialTable
          defaultState support baseVisitFloor hbaseFloor hrewardBound hhorizon
            hbaseVisitFloor,
      selfConsistentScheduledCausalSource_inverseSqrtThresholdCapped_stoppedAverageSampledReturn_tendstoAlmostEverywhere_optimal
        mdp initialState rewardSource varianceProxy hvarianceProxy law initialTable
          defaultState support baseVisitFloor hbaseFloor hrewardBound hhorizon
            hbaseVisitFloor,
      selfConsistentScheduledCausalSource_inverseSqrtThresholdUnboundedHittingAfter_stoppedAverageSampledReturn_tendstoAlmostEverywhere_optimal
        mdp initialState rewardSource varianceProxy hvarianceProxy law initialTable
          defaultState support baseVisitFloor hbaseFloor hrewardBound hhorizon
            hbaseVisitFloor,
      selfConsistentScheduledCausalSource_inverseSqrtThresholdCapped_stoppedAverageSuccessorPolicyExpectedReturn_tendstoAlmostEverywhere_optimal
        mdp initialState rewardSource varianceProxy hvarianceProxy law initialTable
          defaultState support baseVisitFloor hbaseFloor hrewardBound hhorizon
            hbaseVisitFloor,
      selfConsistentScheduledCausalSource_inverseSqrtThresholdUnboundedHittingAfter_stoppedAverageSuccessorPolicyExpectedReturn_tendstoAlmostEverywhere_optimal
        mdp initialState rewardSource varianceProxy hvarianceProxy law initialTable
          defaultState support baseVisitFloor hbaseFloor hrewardBound hhorizon
            hbaseVisitFloor,
      selfConsistentScheduledCausalSource_inverseSqrtThresholdCapped_stoppedSampledPolicyExpectedReturnGap_tendstoAlmostEverywhere_zero
        mdp initialState rewardSource varianceProxy hvarianceProxy law initialTable
          defaultState support baseVisitFloor hbaseFloor hrewardBound hhorizon
            hbaseVisitFloor,
      selfConsistentScheduledCausalSource_inverseSqrtThresholdUnboundedHittingAfter_stoppedSampledPolicyExpectedReturnGap_tendstoAlmostEverywhere_zero
        mdp initialState rewardSource varianceProxy hvarianceProxy law initialTable
          defaultState support baseVisitFloor hbaseFloor hrewardBound hhorizon
            hbaseVisitFloor⟩

end AdaptiveStochasticSampledEmpiricalOptimisticSource

end BanditRLProof.FiniteHorizonRL
