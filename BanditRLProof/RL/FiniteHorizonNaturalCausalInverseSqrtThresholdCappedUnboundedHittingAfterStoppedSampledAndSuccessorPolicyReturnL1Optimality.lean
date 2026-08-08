import BanditRLProof.RL.FiniteHorizonNaturalCausalInverseSqrtThresholdCappedUnboundedHittingAfterStoppedSampledReturnAndSuccessorPolicyExpectedReturnConsistency

/-!
# Stopped sampled and successor-policy return L1 optimality

This module upgrades the stopped expectation-level consistency theorem to
actual `L1` convergence.  The sampled-return optimality error is exactly the
negative realized behavior regret, the literal successor-policy return error
is exactly the negative behavior expected regret, and their same-prefix gap is
exactly the return deviation.  The already compiled capped and genuine
uncapped `hittingAfter` `L1` results therefore transport to all three return
processes.

The successor-policy process remains the literal trajectory-law expected
return of the policy selected from the dependent prefix.  No expectation is
interchanged with a random stopping index, and no optional-stopping theorem is
used.
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

/-- Eta-expanded negation has the same `eLpNorm`.  This small wrapper keeps the
return-process transport proofs independent of the syntactic representation of
pointwise negation. -/
theorem eLpNorm_fun_neg {Omega : Type*} [MeasurableSpace Omega]
    (f : Omega -> Real) (p : ENNReal) (mu : Measure Omega) :
    eLpNorm (fun omega => -f omega) p mu = eLpNorm f p mu := by
  change eLpNorm (-f) p mu = eLpNorm f p mu
  exact eLpNorm_neg f p mu

/-- Sampled return centered at the optimal initial expected return. -/
noncomputable def
    selfConsistentScheduledNaturalCausalStoppingTimeAverageSampledReturnOptimalityErrorProcess
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
  fun trajectory =>
    selfConsistentScheduledNaturalCausalStoppingTimeAverageSampledReturnProcess
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor stoppingPrefix scheduleIndex trajectory -
      AdaptiveStochasticEpisodeBatchSource.optimalInitialExpectedReturn
        mdp initialState

/-- Literal successor-policy expected return centered at the optimal initial
expected return. -/
noncomputable def
    selfConsistentScheduledNaturalCausalStoppingTimeAverageSuccessorPolicyExpectedReturnOptimalityErrorProcess
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
  fun trajectory =>
    selfConsistentScheduledNaturalCausalStoppingTimeAverageSuccessorPolicyExpectedReturnProcess
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor stoppingPrefix scheduleIndex trajectory -
      AdaptiveStochasticEpisodeBatchSource.optimalInitialExpectedReturn
        mdp initialState

/-- Same-prefix sampled return minus literal successor-policy expected return. -/
noncomputable def
    selfConsistentScheduledNaturalCausalStoppingTimeAverageSampledPolicyExpectedReturnGapProcess
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
  fun trajectory =>
    selfConsistentScheduledNaturalCausalStoppingTimeAverageSampledReturnProcess
          mdp initialState rewardSource initialTable defaultState varianceProxy
            baseVisitFloor stoppingPrefix scheduleIndex trajectory -
      selfConsistentScheduledNaturalCausalStoppingTimeAverageSuccessorPolicyExpectedReturnProcess
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor stoppingPrefix scheduleIndex trajectory

/-- The stopped sampled-return optimality error is the negative stopped
realized behavior regret, pointwise and before integration. -/
theorem
    selfConsistentScheduledNaturalCausalStoppingTimeAverageSampledReturnOptimalityErrorProcess_eq_neg_realized
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
    selfConsistentScheduledNaturalCausalStoppingTimeAverageSampledReturnOptimalityErrorProcess
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor stoppingPrefix scheduleIndex =
      fun trajectory =>
        -selfConsistentScheduledNaturalCausalStoppingTimeAverageRealizedBehaviorRegretProcess
          mdp initialState rewardSource initialTable defaultState varianceProxy
            baseVisitFloor stoppingPrefix scheduleIndex trajectory := by
  funext trajectory
  rw [selfConsistentScheduledNaturalCausalStoppingTimeAverageSampledReturnOptimalityErrorProcess]
  rw [selfConsistentScheduledNaturalCausalStoppingTimeAverageSampledReturnProcess_eq_optimal_sub_realized]
  ring

/-- The stopped literal successor-policy return optimality error is the
negative stopped behavior expected regret. -/
theorem
    selfConsistentScheduledNaturalCausalStoppingTimeAverageSuccessorPolicyExpectedReturnOptimalityErrorProcess_eq_neg_behaviorExpected
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
    selfConsistentScheduledNaturalCausalStoppingTimeAverageSuccessorPolicyExpectedReturnOptimalityErrorProcess
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor stoppingPrefix scheduleIndex =
      fun trajectory =>
        -selfConsistentScheduledNaturalCausalStoppingTimeAverageBehaviorExpectedRegretProcess
          mdp initialState rewardSource initialTable defaultState varianceProxy
            baseVisitFloor stoppingPrefix scheduleIndex trajectory := by
  funext trajectory
  rw [selfConsistentScheduledNaturalCausalStoppingTimeAverageSuccessorPolicyExpectedReturnOptimalityErrorProcess]
  rw [selfConsistentScheduledNaturalCausalStoppingTimeAverageSuccessorPolicyExpectedReturnProcess_eq_optimal_sub_behaviorExpected]
  ring

/-- The stopped sampled/policy return gap is exactly the stopped return
deviation. -/
theorem
    selfConsistentScheduledNaturalCausalStoppingTimeAverageSampledPolicyExpectedReturnGapProcess_eq_returnDeviation
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
    selfConsistentScheduledNaturalCausalStoppingTimeAverageSampledPolicyExpectedReturnGapProcess
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor stoppingPrefix scheduleIndex =
      selfConsistentScheduledNaturalCausalStoppingTimeAverageReturnDeviationProcess
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor stoppingPrefix scheduleIndex := by
  funext trajectory
  exact
    selfConsistentScheduledNaturalCausalStoppingTimeAverageSampledReturn_sub_successorPolicyExpectedReturn_eq_returnDeviation
      mdp initialState rewardSource initialTable defaultState varianceProxy
        baseVisitFloor stoppingPrefix scheduleIndex trajectory

/-- Every capped stopped sampled-return optimality error belongs to `L1`. -/
theorem
    memLp_one_selfConsistentScheduledNaturalCausalInverseSqrtThresholdCappedStoppedSampledReturnOptimalityError
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
    (hhorizon : 0 < mdp.horizon) (hbaseVisitFloor : 0 < baseVisitFloor)
    (scheduleIndex : Nat) :
    let source := selfConsistentScheduledCausalSource mdp initialState
      rewardSource initialTable defaultState varianceProxy baseVisitFloor
    let stoppingPrefix :=
      selfConsistentScheduledNaturalCausalInverseSqrtThresholdCappedDoubleLinearRawWindowFirstPassageStoppingPrefix
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor
    let errorProcess :=
      selfConsistentScheduledNaturalCausalStoppingTimeAverageSampledReturnOptimalityErrorProcess
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor stoppingPrefix
    MemLp (errorProcess scheduleIndex) 1 source.trajectoryMeasure := by
  dsimp only
  rw [selfConsistentScheduledNaturalCausalStoppingTimeAverageSampledReturnOptimalityErrorProcess_eq_neg_realized]
  exact
    (memLp_one_selfConsistentScheduledNaturalCausalInverseSqrtThresholdCappedStoppedAverageRealizedBehaviorRegret
      mdp initialState rewardSource varianceProxy hvarianceProxy law initialTable
        defaultState support baseVisitFloor hbaseFloor hrewardBound hhorizon
          hbaseVisitFloor scheduleIndex).neg

/-- The capped sampled-return optimality error converges to zero in `L1`. -/
theorem
    eLpNorm_one_selfConsistentScheduledNaturalCausalInverseSqrtThresholdCappedStoppedSampledReturnOptimalityError_tendsto_zero
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
    let stoppingPrefix :=
      selfConsistentScheduledNaturalCausalInverseSqrtThresholdCappedDoubleLinearRawWindowFirstPassageStoppingPrefix
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor
    let errorProcess :=
      selfConsistentScheduledNaturalCausalStoppingTimeAverageSampledReturnOptimalityErrorProcess
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor stoppingPrefix
    Tendsto
      (fun scheduleIndex =>
        eLpNorm (errorProcess scheduleIndex) 1 source.trajectoryMeasure)
      atTop (nhds 0) := by
  dsimp only
  simpa only [
    selfConsistentScheduledNaturalCausalStoppingTimeAverageSampledReturnOptimalityErrorProcess_eq_neg_realized,
    eLpNorm_fun_neg] using
    (eLpNorm_one_selfConsistentScheduledNaturalCausalInverseSqrtThresholdCappedStoppedAverageRealizedBehaviorRegret_tendsto_zero
      mdp initialState rewardSource varianceProxy hvarianceProxy law initialTable
        defaultState support baseVisitFloor hbaseFloor hrewardBound hhorizon
          hbaseVisitFloor)

/-- Every uncapped `hittingAfter` stopped sampled-return optimality error
belongs to `L1`. -/
theorem
    memLp_one_selfConsistentScheduledNaturalCausalInverseSqrtThresholdUnboundedHittingAfterStoppedSampledReturnOptimalityError
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
    let errorProcess :=
      selfConsistentScheduledNaturalCausalStoppingTimeAverageSampledReturnOptimalityErrorProcess
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor stoppingPrefix
    MemLp (errorProcess scheduleIndex) 1 source.trajectoryMeasure := by
  dsimp only
  rw [selfConsistentScheduledNaturalCausalStoppingTimeAverageSampledReturnOptimalityErrorProcess_eq_neg_realized]
  exact
    (memLp_one_selfConsistentScheduledNaturalCausalInverseSqrtThresholdUnboundedHittingAfterStoppedAverageRealizedBehaviorRegret
      mdp initialState rewardSource varianceProxy hvarianceProxy law initialTable
        defaultState support baseVisitFloor hbaseFloor hrewardBound hhorizon
          hbaseVisitFloor scheduleIndex).neg

/-- The genuine uncapped stopped sampled-return optimality error converges to
zero in `L1`. -/
theorem
    eLpNorm_one_selfConsistentScheduledNaturalCausalInverseSqrtThresholdUnboundedHittingAfterStoppedSampledReturnOptimalityError_tendsto_zero
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
    let errorProcess :=
      selfConsistentScheduledNaturalCausalStoppingTimeAverageSampledReturnOptimalityErrorProcess
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor stoppingPrefix
    Tendsto
      (fun scheduleIndex =>
        eLpNorm (errorProcess scheduleIndex) 1 source.trajectoryMeasure)
      atTop (nhds 0) := by
  dsimp only
  simpa only [
    selfConsistentScheduledNaturalCausalStoppingTimeAverageSampledReturnOptimalityErrorProcess_eq_neg_realized,
    eLpNorm_fun_neg] using
    (eLpNorm_one_selfConsistentScheduledNaturalCausalInverseSqrtThresholdUnboundedHittingAfterStoppedAverageRealizedBehaviorRegret_tendsto_zero
      mdp initialState rewardSource varianceProxy hvarianceProxy law initialTable
        defaultState support baseVisitFloor hbaseFloor hrewardBound hhorizon
          hbaseVisitFloor)

/-- Every capped stopped literal successor-policy return optimality error
belongs to `L1`. -/
theorem
    memLp_one_selfConsistentScheduledNaturalCausalInverseSqrtThresholdCappedStoppedSuccessorPolicyExpectedReturnOptimalityError
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
    let errorProcess :=
      selfConsistentScheduledNaturalCausalStoppingTimeAverageSuccessorPolicyExpectedReturnOptimalityErrorProcess
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor stoppingPrefix
    MemLp (errorProcess scheduleIndex) 1 source.trajectoryMeasure := by
  dsimp only
  rw [selfConsistentScheduledNaturalCausalStoppingTimeAverageSuccessorPolicyExpectedReturnOptimalityErrorProcess_eq_neg_behaviorExpected]
  exact
    (memLp_one_selfConsistentScheduledNaturalCausalInverseSqrtThresholdCappedStoppedBehaviorExpectedRegret
      mdp initialState rewardSource initialTable defaultState varianceProxy
        baseVisitFloor hrewardBound scheduleIndex).neg

/-- The capped literal successor-policy return optimality error converges to
zero in `L1`. -/
theorem
    eLpNorm_one_selfConsistentScheduledNaturalCausalInverseSqrtThresholdCappedStoppedSuccessorPolicyExpectedReturnOptimalityError_tendsto_zero
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
    let stoppingPrefix :=
      selfConsistentScheduledNaturalCausalInverseSqrtThresholdCappedDoubleLinearRawWindowFirstPassageStoppingPrefix
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor
    let errorProcess :=
      selfConsistentScheduledNaturalCausalStoppingTimeAverageSuccessorPolicyExpectedReturnOptimalityErrorProcess
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor stoppingPrefix
    Tendsto
      (fun scheduleIndex =>
        eLpNorm (errorProcess scheduleIndex) 1 source.trajectoryMeasure)
      atTop (nhds 0) := by
  dsimp only
  simpa only [
    selfConsistentScheduledNaturalCausalStoppingTimeAverageSuccessorPolicyExpectedReturnOptimalityErrorProcess_eq_neg_behaviorExpected,
    eLpNorm_fun_neg] using
    (eLpNorm_one_selfConsistentScheduledNaturalCausalInverseSqrtThresholdCappedStoppedBehaviorExpectedRegret_tendsto_zero
      mdp initialState rewardSource varianceProxy hvarianceProxy law initialTable
        defaultState support baseVisitFloor hbaseFloor hrewardBound hhorizon
          hbaseVisitFloor)

/-- Every genuine uncapped stopped literal successor-policy return optimality
error belongs to `L1`. -/
theorem
    memLp_one_selfConsistentScheduledNaturalCausalInverseSqrtThresholdUnboundedHittingAfterStoppedSuccessorPolicyExpectedReturnOptimalityError
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
    let errorProcess :=
      selfConsistentScheduledNaturalCausalStoppingTimeAverageSuccessorPolicyExpectedReturnOptimalityErrorProcess
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor stoppingPrefix
    MemLp (errorProcess scheduleIndex) 1 source.trajectoryMeasure := by
  dsimp only
  rw [selfConsistentScheduledNaturalCausalStoppingTimeAverageSuccessorPolicyExpectedReturnOptimalityErrorProcess_eq_neg_behaviorExpected]
  exact
    (memLp_one_selfConsistentScheduledNaturalCausalInverseSqrtThresholdUnboundedHittingAfterStoppedBehaviorExpectedRegret
      mdp initialState rewardSource initialTable defaultState varianceProxy
        baseVisitFloor hrewardBound scheduleIndex).neg

/-- The genuine uncapped literal successor-policy return optimality error
converges to zero in `L1`. -/
theorem
    eLpNorm_one_selfConsistentScheduledNaturalCausalInverseSqrtThresholdUnboundedHittingAfterStoppedSuccessorPolicyExpectedReturnOptimalityError_tendsto_zero
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
    let stoppingPrefix :=
      selfConsistentScheduledNaturalCausalInverseSqrtThresholdUnboundedHittingAfterStoppingPrefix
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor
    let errorProcess :=
      selfConsistentScheduledNaturalCausalStoppingTimeAverageSuccessorPolicyExpectedReturnOptimalityErrorProcess
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor stoppingPrefix
    Tendsto
      (fun scheduleIndex =>
        eLpNorm (errorProcess scheduleIndex) 1 source.trajectoryMeasure)
      atTop (nhds 0) := by
  dsimp only
  simpa only [
    selfConsistentScheduledNaturalCausalStoppingTimeAverageSuccessorPolicyExpectedReturnOptimalityErrorProcess_eq_neg_behaviorExpected,
    eLpNorm_fun_neg] using
    (eLpNorm_one_selfConsistentScheduledNaturalCausalInverseSqrtThresholdUnboundedHittingAfterStoppedBehaviorExpectedRegret_tendsto_zero
      mdp initialState rewardSource varianceProxy hvarianceProxy law initialTable
        defaultState support baseVisitFloor hbaseFloor hrewardBound hhorizon
          hbaseVisitFloor)

/-- Every capped stopped sampled/policy return gap belongs to `L1`. -/
theorem
    memLp_one_selfConsistentScheduledNaturalCausalInverseSqrtThresholdCappedStoppedSampledPolicyExpectedReturnGap
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
    let gapProcess :=
      selfConsistentScheduledNaturalCausalStoppingTimeAverageSampledPolicyExpectedReturnGapProcess
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor stoppingPrefix
    MemLp (gapProcess scheduleIndex) 1 source.trajectoryMeasure := by
  dsimp only
  rw [selfConsistentScheduledNaturalCausalStoppingTimeAverageSampledPolicyExpectedReturnGapProcess_eq_returnDeviation]
  exact
    memLp_one_selfConsistentScheduledNaturalCausalInverseSqrtThresholdCappedStoppedReturnDeviation
      mdp initialState rewardSource varianceProxy hvarianceProxy law initialTable
        defaultState support baseVisitFloor hbaseFloor hrewardBound hhorizon
          hbaseVisitFloor scheduleIndex

/-- The capped stopped sampled/policy return gap converges to zero in `L1`. -/
theorem
    eLpNorm_one_selfConsistentScheduledNaturalCausalInverseSqrtThresholdCappedStoppedSampledPolicyExpectedReturnGap_tendsto_zero
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
    Tendsto
      (fun scheduleIndex =>
        eLpNorm (gapProcess scheduleIndex) 1 source.trajectoryMeasure)
      atTop (nhds 0) := by
  dsimp only
  simpa only [
    selfConsistentScheduledNaturalCausalStoppingTimeAverageSampledPolicyExpectedReturnGapProcess_eq_returnDeviation] using
    (eLpNorm_one_selfConsistentScheduledNaturalCausalInverseSqrtThresholdCappedStoppedReturnDeviation_tendsto_zero
      mdp initialState rewardSource varianceProxy hvarianceProxy law initialTable
        defaultState support baseVisitFloor hbaseFloor hrewardBound hhorizon
          hbaseVisitFloor)

/-- Every genuine uncapped stopped sampled/policy return gap belongs to `L1`. -/
theorem
    memLp_one_selfConsistentScheduledNaturalCausalInverseSqrtThresholdUnboundedHittingAfterStoppedSampledPolicyExpectedReturnGap
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
    let gapProcess :=
      selfConsistentScheduledNaturalCausalStoppingTimeAverageSampledPolicyExpectedReturnGapProcess
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor stoppingPrefix
    MemLp (gapProcess scheduleIndex) 1 source.trajectoryMeasure := by
  dsimp only
  rw [selfConsistentScheduledNaturalCausalStoppingTimeAverageSampledPolicyExpectedReturnGapProcess_eq_returnDeviation]
  exact
    memLp_one_selfConsistentScheduledNaturalCausalInverseSqrtThresholdUnboundedHittingAfterStoppedReturnDeviation
      mdp initialState rewardSource varianceProxy hvarianceProxy law initialTable
        defaultState support baseVisitFloor hbaseFloor hrewardBound hhorizon
          hbaseVisitFloor scheduleIndex

/-- The genuine uncapped stopped sampled/policy return gap converges to zero in
`L1`. -/
theorem
    eLpNorm_one_selfConsistentScheduledNaturalCausalInverseSqrtThresholdUnboundedHittingAfterStoppedSampledPolicyExpectedReturnGap_tendsto_zero
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
    Tendsto
      (fun scheduleIndex =>
        eLpNorm (gapProcess scheduleIndex) 1 source.trajectoryMeasure)
      atTop (nhds 0) := by
  dsimp only
  simpa only [
    selfConsistentScheduledNaturalCausalStoppingTimeAverageSampledPolicyExpectedReturnGapProcess_eq_returnDeviation] using
    (eLpNorm_one_selfConsistentScheduledNaturalCausalInverseSqrtThresholdUnboundedHittingAfterStoppedReturnDeviation_tendsto_zero
      mdp initialState rewardSource varianceProxy hvarianceProxy law initialTable
        defaultState support baseVisitFloor hbaseFloor hrewardBound hhorizon
          hbaseVisitFloor)

/-- Terminal true-`L1` package for stopped sampled return, the literal return
of the actually selected successor policies, and their same-prefix gap at both
the capped first-passage approximation and genuine uncapped `hittingAfter`. -/
theorem
    selfConsistentScheduledCausalSource_inverseSqrtThresholdCappedUnboundedHittingAfter_stoppedSampledReturn_and_successorPolicyExpectedReturn_L1_optimality
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
    let cappedSampledError :=
      selfConsistentScheduledNaturalCausalStoppingTimeAverageSampledReturnOptimalityErrorProcess
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor cappedStoppingPrefix
    let uncappedSampledError :=
      selfConsistentScheduledNaturalCausalStoppingTimeAverageSampledReturnOptimalityErrorProcess
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor uncappedStoppingPrefix
    let cappedPolicyError :=
      selfConsistentScheduledNaturalCausalStoppingTimeAverageSuccessorPolicyExpectedReturnOptimalityErrorProcess
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor cappedStoppingPrefix
    let uncappedPolicyError :=
      selfConsistentScheduledNaturalCausalStoppingTimeAverageSuccessorPolicyExpectedReturnOptimalityErrorProcess
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
    (forall scheduleIndex,
      MemLp (cappedSampledError scheduleIndex) 1 source.trajectoryMeasure) /\
    (forall scheduleIndex,
      MemLp (uncappedSampledError scheduleIndex) 1 source.trajectoryMeasure) /\
    (forall scheduleIndex,
      MemLp (cappedPolicyError scheduleIndex) 1 source.trajectoryMeasure) /\
    (forall scheduleIndex,
      MemLp (uncappedPolicyError scheduleIndex) 1 source.trajectoryMeasure) /\
    (forall scheduleIndex,
      MemLp (cappedGap scheduleIndex) 1 source.trajectoryMeasure) /\
    (forall scheduleIndex,
      MemLp (uncappedGap scheduleIndex) 1 source.trajectoryMeasure) /\
    Tendsto
      (fun scheduleIndex =>
        eLpNorm (cappedSampledError scheduleIndex) 1 source.trajectoryMeasure)
      atTop (nhds 0) /\
    Tendsto
      (fun scheduleIndex =>
        eLpNorm (uncappedSampledError scheduleIndex) 1 source.trajectoryMeasure)
      atTop (nhds 0) /\
    Tendsto
      (fun scheduleIndex =>
        eLpNorm (cappedPolicyError scheduleIndex) 1 source.trajectoryMeasure)
      atTop (nhds 0) /\
    Tendsto
      (fun scheduleIndex =>
        eLpNorm (uncappedPolicyError scheduleIndex) 1 source.trajectoryMeasure)
      atTop (nhds 0) /\
    Tendsto
      (fun scheduleIndex =>
        eLpNorm (cappedGap scheduleIndex) 1 source.trajectoryMeasure)
      atTop (nhds 0) /\
    Tendsto
      (fun scheduleIndex =>
        eLpNorm (uncappedGap scheduleIndex) 1 source.trajectoryMeasure)
      atTop (nhds 0) := by
  dsimp only
  exact
    ⟨fun scheduleIndex =>
        memLp_one_selfConsistentScheduledNaturalCausalInverseSqrtThresholdCappedStoppedSampledReturnOptimalityError
          mdp initialState rewardSource varianceProxy hvarianceProxy law
            initialTable defaultState support baseVisitFloor hbaseFloor
              hrewardBound (lt_trans (by decide : 0 < 4) hhorizon)
                hbaseVisitFloor scheduleIndex,
      fun scheduleIndex =>
        memLp_one_selfConsistentScheduledNaturalCausalInverseSqrtThresholdUnboundedHittingAfterStoppedSampledReturnOptimalityError
          mdp initialState rewardSource varianceProxy hvarianceProxy law
            initialTable defaultState support baseVisitFloor hbaseFloor
              hrewardBound hhorizon hbaseVisitFloor scheduleIndex,
      fun scheduleIndex =>
        memLp_one_selfConsistentScheduledNaturalCausalInverseSqrtThresholdCappedStoppedSuccessorPolicyExpectedReturnOptimalityError
          mdp initialState rewardSource initialTable defaultState varianceProxy
            baseVisitFloor hrewardBound scheduleIndex,
      fun scheduleIndex =>
        memLp_one_selfConsistentScheduledNaturalCausalInverseSqrtThresholdUnboundedHittingAfterStoppedSuccessorPolicyExpectedReturnOptimalityError
          mdp initialState rewardSource initialTable defaultState varianceProxy
            baseVisitFloor hrewardBound scheduleIndex,
      fun scheduleIndex =>
        memLp_one_selfConsistentScheduledNaturalCausalInverseSqrtThresholdCappedStoppedSampledPolicyExpectedReturnGap
          mdp initialState rewardSource varianceProxy hvarianceProxy law
            initialTable defaultState support baseVisitFloor hbaseFloor
              hrewardBound hhorizon hbaseVisitFloor scheduleIndex,
      fun scheduleIndex =>
        memLp_one_selfConsistentScheduledNaturalCausalInverseSqrtThresholdUnboundedHittingAfterStoppedSampledPolicyExpectedReturnGap
          mdp initialState rewardSource varianceProxy hvarianceProxy law
            initialTable defaultState support baseVisitFloor hbaseFloor
              hrewardBound hhorizon hbaseVisitFloor scheduleIndex,
      eLpNorm_one_selfConsistentScheduledNaturalCausalInverseSqrtThresholdCappedStoppedSampledReturnOptimalityError_tendsto_zero
        mdp initialState rewardSource varianceProxy hvarianceProxy law initialTable
          defaultState support baseVisitFloor hbaseFloor hrewardBound
            (lt_trans (by decide : 0 < 4) hhorizon) hbaseVisitFloor,
      eLpNorm_one_selfConsistentScheduledNaturalCausalInverseSqrtThresholdUnboundedHittingAfterStoppedSampledReturnOptimalityError_tendsto_zero
        mdp initialState rewardSource varianceProxy hvarianceProxy law initialTable
          defaultState support baseVisitFloor hbaseFloor hrewardBound hhorizon
            hbaseVisitFloor,
      eLpNorm_one_selfConsistentScheduledNaturalCausalInverseSqrtThresholdCappedStoppedSuccessorPolicyExpectedReturnOptimalityError_tendsto_zero
        mdp initialState rewardSource varianceProxy hvarianceProxy law initialTable
          defaultState support baseVisitFloor hbaseFloor hrewardBound
            (lt_trans (by decide : 0 < 4) hhorizon) hbaseVisitFloor,
      eLpNorm_one_selfConsistentScheduledNaturalCausalInverseSqrtThresholdUnboundedHittingAfterStoppedSuccessorPolicyExpectedReturnOptimalityError_tendsto_zero
        mdp initialState rewardSource varianceProxy hvarianceProxy law initialTable
          defaultState support baseVisitFloor hbaseFloor hrewardBound
            (lt_trans (by decide : 0 < 4) hhorizon) hbaseVisitFloor,
      eLpNorm_one_selfConsistentScheduledNaturalCausalInverseSqrtThresholdCappedStoppedSampledPolicyExpectedReturnGap_tendsto_zero
        mdp initialState rewardSource varianceProxy hvarianceProxy law initialTable
          defaultState support baseVisitFloor hbaseFloor hrewardBound hhorizon
            hbaseVisitFloor,
      eLpNorm_one_selfConsistentScheduledNaturalCausalInverseSqrtThresholdUnboundedHittingAfterStoppedSampledPolicyExpectedReturnGap_tendsto_zero
        mdp initialState rewardSource varianceProxy hvarianceProxy law initialTable
          defaultState support baseVisitFloor hbaseFloor hrewardBound hhorizon
            hbaseVisitFloor⟩

end AdaptiveStochasticSampledEmpiricalOptimisticSource

end BanditRLProof.FiniteHorizonRL
