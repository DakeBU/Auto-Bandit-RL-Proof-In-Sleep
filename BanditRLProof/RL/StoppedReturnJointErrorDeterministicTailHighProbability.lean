import BanditRLProof.RL.FiniteHorizonNaturalCausalInverseSqrtThresholdCappedUnboundedHittingAfterStoppedSampledAndSuccessorPolicyReturnDeterministicTailHighProbabilityOptimality

/-!
# Scalar joint-error deterministic-tail stopped-return optimality

This module replaces the six-coordinate conjunction-only confidence surface by
one measurable scalar random variable: the maximum of the capped/uncapped
sampled-return, actual successor-policy-return, and same-prefix-gap errors.
The accepted deterministic-tail certificate then transports to direct strict
sublevel and weak superlevel events for this joint error.

The cutoff remains existential and noncomputable. No convergence rate,
independence, delta upper bound, or optional-stopping argument is introduced.
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

/-- The maximum of the six literal capped/uncapped stopped-return errors at
one schedule index. -/
noncomputable def
    selfConsistentScheduledNaturalCausalInverseSqrtThresholdCappedUnboundedHittingAfterStoppedReturnJointError
    (mdp : MDP State Action) (initialState : Measure State)
    [IsProbabilityMeasure initialState]
    (rewardSource : mdp.MeanCompatibleRewardKernel)
    (initialTable : DeterministicMarkovPolicyTable mdp)
    (defaultState : State) (varianceProxy : NNReal)
    (baseVisitFloor : Real) (scheduleIndex : Nat) :
    HeterogeneousStochasticEpisodeBatchTrajectory mdp
      (fun t =>
        AdaptiveStochasticEpisodeBatchSource.selfConsistentScheduledEpisodes
          mdp varianceProxy baseVisitFloor t) → Real :=
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
  fun trajectory =>
    max
      (max
        (max
          (max
            (max
              (dist (cappedSampledReturn scheduleIndex trajectory) optimal)
              (dist (uncappedSampledReturn scheduleIndex trajectory) optimal))
            (dist (cappedPolicyReturn scheduleIndex trajectory) optimal))
          (dist (uncappedPolicyReturn scheduleIndex trajectory) optimal))
        (dist (cappedGap scheduleIndex trajectory) 0))
      (dist (uncappedGap scheduleIndex trajectory) 0)

/-- The scalar joint error is nonnegative. -/
theorem
    selfConsistentScheduledNaturalCausalInverseSqrtThresholdCappedUnboundedHittingAfterStoppedReturnJointError_nonneg
    (mdp : MDP State Action) (initialState : Measure State)
    [IsProbabilityMeasure initialState]
    (rewardSource : mdp.MeanCompatibleRewardKernel)
    (initialTable : DeterministicMarkovPolicyTable mdp)
    (defaultState : State) (varianceProxy : NNReal)
    (baseVisitFloor : Real) (scheduleIndex : Nat)
    (trajectory : HeterogeneousStochasticEpisodeBatchTrajectory mdp
      (fun t =>
        AdaptiveStochasticEpisodeBatchSource.selfConsistentScheduledEpisodes
          mdp varianceProxy baseVisitFloor t)) :
    0 ≤
      selfConsistentScheduledNaturalCausalInverseSqrtThresholdCappedUnboundedHittingAfterStoppedReturnJointError
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor scheduleIndex trajectory := by
  simp only [
    selfConsistentScheduledNaturalCausalInverseSqrtThresholdCappedUnboundedHittingAfterStoppedReturnJointError]
  positivity

/-- Every schedule-index coordinate of the scalar joint error is measurable. -/
theorem
    measurable_selfConsistentScheduledNaturalCausalInverseSqrtThresholdCappedUnboundedHittingAfterStoppedReturnJointError
    (mdp : MDP State Action) (initialState : Measure State)
    [IsProbabilityMeasure initialState]
    (rewardSource : mdp.MeanCompatibleRewardKernel)
    (initialTable : DeterministicMarkovPolicyTable mdp)
    (defaultState : State) (varianceProxy : NNReal)
    (baseVisitFloor : Real) (scheduleIndex : Nat) :
    Measurable
      (selfConsistentScheduledNaturalCausalInverseSqrtThresholdCappedUnboundedHittingAfterStoppedReturnJointError
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor scheduleIndex) := by
  let hCappedSampled :=
    measurable_selfConsistentScheduledNaturalCausalInverseSqrtThresholdCappedStoppedAverageSampledReturn
      mdp initialState rewardSource initialTable defaultState varianceProxy
        baseVisitFloor scheduleIndex
  let hUncappedSampled :=
    measurable_selfConsistentScheduledNaturalCausalInverseSqrtThresholdUnboundedHittingAfterStoppedAverageSampledReturn
      mdp initialState rewardSource initialTable defaultState varianceProxy
        baseVisitFloor scheduleIndex
  let hCappedPolicy :=
    measurable_selfConsistentScheduledNaturalCausalInverseSqrtThresholdCappedStoppedAverageSuccessorPolicyExpectedReturn
      mdp initialState rewardSource initialTable defaultState varianceProxy
        baseVisitFloor scheduleIndex
  let hUncappedPolicy :=
    measurable_selfConsistentScheduledNaturalCausalInverseSqrtThresholdUnboundedHittingAfterStoppedAverageSuccessorPolicyExpectedReturn
      mdp initialState rewardSource initialTable defaultState varianceProxy
        baseVisitFloor scheduleIndex
  let hCappedGap :=
    measurable_selfConsistentScheduledNaturalCausalInverseSqrtThresholdCappedStoppedSampledPolicyExpectedReturnGap
      mdp initialState rewardSource initialTable defaultState varianceProxy
        baseVisitFloor scheduleIndex
  let hUncappedGap :=
    measurable_selfConsistentScheduledNaturalCausalInverseSqrtThresholdUnboundedHittingAfterStoppedSampledPolicyExpectedReturnGap
      mdp initialState rewardSource initialTable defaultState varianceProxy
        baseVisitFloor scheduleIndex
  let optimal :=
    AdaptiveStochasticEpisodeBatchSource.optimalInitialExpectedReturn
      mdp initialState
  let hOptimal : Measurable
      (fun _ : HeterogeneousStochasticEpisodeBatchTrajectory mdp
        (fun t =>
          AdaptiveStochasticEpisodeBatchSource.selfConsistentScheduledEpisodes
            mdp varianceProxy baseVisitFloor t) => optimal) :=
    measurable_const
  let hZero : Measurable
      (fun _ : HeterogeneousStochasticEpisodeBatchTrajectory mdp
        (fun t =>
          AdaptiveStochasticEpisodeBatchSource.selfConsistentScheduledEpisodes
            mdp varianceProxy baseVisitFloor t) => (0 : Real)) :=
    measurable_const
  simpa [
    selfConsistentScheduledNaturalCausalInverseSqrtThresholdCappedUnboundedHittingAfterStoppedReturnJointError,
    optimal] using
    (((((hCappedSampled.dist hOptimal).max
              (hUncappedSampled.dist hOptimal)).max
            (hCappedPolicy.dist hOptimal)).max
          (hUncappedPolicy.dist hOptimal)).max
        (hCappedGap.dist hZero)).max
      (hUncappedGap.dist hZero)

/-- A strict scalar joint-error bound is exactly the conjunction of the same
six literal stopped-return bounds. -/
theorem
    selfConsistentScheduledNaturalCausalInverseSqrtThresholdCappedUnboundedHittingAfterStoppedReturnJointError_lt_iff
    (mdp : MDP State Action) (initialState : Measure State)
    [IsProbabilityMeasure initialState]
    (rewardSource : mdp.MeanCompatibleRewardKernel)
    (initialTable : DeterministicMarkovPolicyTable mdp)
    (defaultState : State) (varianceProxy : NNReal)
    (baseVisitFloor epsilon : Real) (scheduleIndex : Nat)
    (trajectory : HeterogeneousStochasticEpisodeBatchTrajectory mdp
      (fun t =>
        AdaptiveStochasticEpisodeBatchSource.selfConsistentScheduledEpisodes
          mdp varianceProxy baseVisitFloor t)) :
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
    selfConsistentScheduledNaturalCausalInverseSqrtThresholdCappedUnboundedHittingAfterStoppedReturnJointError
          mdp initialState rewardSource initialTable defaultState varianceProxy
            baseVisitFloor scheduleIndex trajectory < epsilon ↔
      dist (cappedSampledReturn scheduleIndex trajectory) optimal < epsilon ∧
      dist (uncappedSampledReturn scheduleIndex trajectory) optimal < epsilon ∧
      dist (cappedPolicyReturn scheduleIndex trajectory) optimal < epsilon ∧
      dist (uncappedPolicyReturn scheduleIndex trajectory) optimal < epsilon ∧
      dist (cappedGap scheduleIndex trajectory) 0 < epsilon ∧
      dist (uncappedGap scheduleIndex trajectory) 0 < epsilon := by
  simp only [
    selfConsistentScheduledNaturalCausalInverseSqrtThresholdCappedUnboundedHittingAfterStoppedReturnJointError,
    max_lt_iff]
  tauto

/-- The accepted named weak-bad event is exactly the scalar joint-error weak
superlevel set. -/
theorem
    selfConsistentScheduledNaturalCausalInverseSqrtThresholdCappedUnboundedHittingAfterStoppedReturnJointViolationSet_eq_jointError_ge
    (mdp : MDP State Action) (initialState : Measure State)
    [IsProbabilityMeasure initialState]
    (rewardSource : mdp.MeanCompatibleRewardKernel)
    (initialTable : DeterministicMarkovPolicyTable mdp)
    (defaultState : State) (varianceProxy : NNReal)
    (baseVisitFloor epsilon : Real) (scheduleIndex : Nat) :
    selfConsistentScheduledNaturalCausalInverseSqrtThresholdCappedUnboundedHittingAfterStoppedReturnJointViolationSet
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor epsilon scheduleIndex =
      {trajectory |
        epsilon ≤
          selfConsistentScheduledNaturalCausalInverseSqrtThresholdCappedUnboundedHittingAfterStoppedReturnJointError
            mdp initialState rewardSource initialTable defaultState
              varianceProxy baseVisitFloor scheduleIndex trajectory} := by
  ext trajectory
  simp only [
    selfConsistentScheduledNaturalCausalInverseSqrtThresholdCappedUnboundedHittingAfterStoppedReturnJointViolationSet,
    selfConsistentScheduledNaturalCausalInverseSqrtThresholdCappedUnboundedHittingAfterStoppedReturnJointError,
    Set.mem_union, Set.mem_setOf_eq, le_max_iff]

/-- The accepted named strict-good event is exactly the scalar joint-error
strict sublevel set. -/
theorem
    selfConsistentScheduledNaturalCausalInverseSqrtThresholdCappedUnboundedHittingAfterStoppedReturnJointGoodSet_eq_jointError_lt
    (mdp : MDP State Action) (initialState : Measure State)
    [IsProbabilityMeasure initialState]
    (rewardSource : mdp.MeanCompatibleRewardKernel)
    (initialTable : DeterministicMarkovPolicyTable mdp)
    (defaultState : State) (varianceProxy : NNReal)
    (baseVisitFloor epsilon : Real) (scheduleIndex : Nat) :
    selfConsistentScheduledNaturalCausalInverseSqrtThresholdCappedUnboundedHittingAfterStoppedReturnJointGoodSet
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor epsilon scheduleIndex =
      {trajectory |
        selfConsistentScheduledNaturalCausalInverseSqrtThresholdCappedUnboundedHittingAfterStoppedReturnJointError
            mdp initialState rewardSource initialTable defaultState
              varianceProxy baseVisitFloor scheduleIndex trajectory < epsilon} := by
  ext trajectory
  simp only [Set.mem_setOf_eq]
  exact
    (mem_selfConsistentScheduledNaturalCausalInverseSqrtThresholdCappedUnboundedHittingAfterStoppedReturnJointGoodSet_iff
      mdp initialState rewardSource initialTable defaultState varianceProxy
        baseVisitFloor epsilon scheduleIndex trajectory).trans
      (selfConsistentScheduledNaturalCausalInverseSqrtThresholdCappedUnboundedHittingAfterStoppedReturnJointError_lt_iff
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor epsilon scheduleIndex trajectory).symm

/-- Terminal scalar deterministic-tail confidence certificate. One
noncomputable cutoff works for every later schedule index. -/
theorem
    selfConsistentScheduledCausalSource_inverseSqrtThresholdCappedUnboundedHittingAfter_stoppedSampledReturn_and_successorPolicyExpectedReturn_jointError_deterministicTailHighProbability_optimality
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
    let source :=
      selfConsistentScheduledCausalSource mdp initialState rewardSource
        initialTable defaultState varianceProxy baseVisitFloor
    let jointError :=
      selfConsistentScheduledNaturalCausalInverseSqrtThresholdCappedUnboundedHittingAfterStoppedReturnJointError
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor
    ∀ epsilon delta, 0 < epsilon → 0 < delta →
      ∃ tailStart : Nat, ∀ scheduleIndex, tailStart ≤ scheduleIndex →
        Measurable (jointError scheduleIndex) ∧
        MeasurableSet
          {trajectory | jointError scheduleIndex trajectory < epsilon} ∧
        source.trajectoryMeasure
            {trajectory | epsilon ≤ jointError scheduleIndex trajectory} <
          ENNReal.ofReal delta ∧
        1 - delta < source.trajectoryMeasure.real
          {trajectory | jointError scheduleIndex trajectory < epsilon} ∧
        ∀ trajectory, jointError scheduleIndex trajectory < epsilon ↔
          let cappedStoppingPrefix :=
            selfConsistentScheduledNaturalCausalInverseSqrtThresholdCappedDoubleLinearRawWindowFirstPassageStoppingPrefix
              mdp initialState rewardSource initialTable defaultState
                varianceProxy baseVisitFloor
          let uncappedStoppingPrefix :=
            selfConsistentScheduledNaturalCausalInverseSqrtThresholdUnboundedHittingAfterStoppingPrefix
              mdp initialState rewardSource initialTable defaultState
                varianceProxy baseVisitFloor
          let cappedSampledReturn :=
            selfConsistentScheduledNaturalCausalStoppingTimeAverageSampledReturnProcess
              mdp initialState rewardSource initialTable defaultState
                varianceProxy baseVisitFloor cappedStoppingPrefix
          let uncappedSampledReturn :=
            selfConsistentScheduledNaturalCausalStoppingTimeAverageSampledReturnProcess
              mdp initialState rewardSource initialTable defaultState
                varianceProxy baseVisitFloor uncappedStoppingPrefix
          let cappedPolicyReturn :=
            selfConsistentScheduledNaturalCausalStoppingTimeAverageSuccessorPolicyExpectedReturnProcess
              mdp initialState rewardSource initialTable defaultState
                varianceProxy baseVisitFloor cappedStoppingPrefix
          let uncappedPolicyReturn :=
            selfConsistentScheduledNaturalCausalStoppingTimeAverageSuccessorPolicyExpectedReturnProcess
              mdp initialState rewardSource initialTable defaultState
                varianceProxy baseVisitFloor uncappedStoppingPrefix
          let cappedGap :=
            selfConsistentScheduledNaturalCausalStoppingTimeAverageSampledPolicyExpectedReturnGapProcess
              mdp initialState rewardSource initialTable defaultState
                varianceProxy baseVisitFloor cappedStoppingPrefix
          let uncappedGap :=
            selfConsistentScheduledNaturalCausalStoppingTimeAverageSampledPolicyExpectedReturnGapProcess
              mdp initialState rewardSource initialTable defaultState
                varianceProxy baseVisitFloor uncappedStoppingPrefix
          let optimal :=
            AdaptiveStochasticEpisodeBatchSource.optimalInitialExpectedReturn
              mdp initialState
          dist (cappedSampledReturn scheduleIndex trajectory) optimal < epsilon ∧
          dist (uncappedSampledReturn scheduleIndex trajectory) optimal < epsilon ∧
          dist (cappedPolicyReturn scheduleIndex trajectory) optimal < epsilon ∧
          dist (uncappedPolicyReturn scheduleIndex trajectory) optimal < epsilon ∧
          dist (cappedGap scheduleIndex trajectory) 0 < epsilon ∧
          dist (uncappedGap scheduleIndex trajectory) 0 < epsilon := by
  dsimp only
  intro epsilon delta hepsilon hdelta
  obtain ⟨tailStart, htail⟩ :=
    (selfConsistentScheduledCausalSource_inverseSqrtThresholdCappedUnboundedHittingAfter_stoppedSampledReturn_and_successorPolicyExpectedReturn_deterministicTailHighProbability_optimality
      mdp initialState rewardSource varianceProxy hvarianceProxy law initialTable
        defaultState support baseVisitFloor hbaseFloor hrewardBound hhorizon
          hbaseVisitFloor) epsilon delta hepsilon hdelta
  refine ⟨tailStart, ?_⟩
  intro scheduleIndex hscheduleIndex
  rcases htail scheduleIndex hscheduleIndex with
    ⟨hBadMeasurable, hBadMass, hGoodMass, hGoodSemantics⟩
  let hJointMeasurable :=
    measurable_selfConsistentScheduledNaturalCausalInverseSqrtThresholdCappedUnboundedHittingAfterStoppedReturnJointError
      mdp initialState rewardSource initialTable defaultState varianceProxy
        baseVisitFloor scheduleIndex
  have hBadEq :=
    selfConsistentScheduledNaturalCausalInverseSqrtThresholdCappedUnboundedHittingAfterStoppedReturnJointViolationSet_eq_jointError_ge
      mdp initialState rewardSource initialTable defaultState varianceProxy
        baseVisitFloor epsilon scheduleIndex
  have hGoodEq :=
    selfConsistentScheduledNaturalCausalInverseSqrtThresholdCappedUnboundedHittingAfterStoppedReturnJointGoodSet_eq_jointError_lt
      mdp initialState rewardSource initialTable defaultState varianceProxy
        baseVisitFloor epsilon scheduleIndex
  refine ⟨hJointMeasurable,
    measurableSet_lt hJointMeasurable measurable_const, ?_, ?_, ?_⟩
  · rwa [← hBadEq]
  · rwa [← hGoodEq]
  · exact
      selfConsistentScheduledNaturalCausalInverseSqrtThresholdCappedUnboundedHittingAfterStoppedReturnJointError_lt_iff
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor epsilon scheduleIndex

end AdaptiveStochasticSampledEmpiricalOptimisticSource
end BanditRLProof.FiniteHorizonRL
