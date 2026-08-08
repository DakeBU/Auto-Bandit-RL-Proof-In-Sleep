import BanditRLProof.RL.FiniteHorizonNaturalCausalInverseSqrtThresholdCappedUnboundedHittingAfterStoppedSampledAndSuccessorPolicyReturnInMeasureAlmostSureOptimality

/-!
# Simultaneous high-probability stopped-return optimality

This module combines the six literal capped/uncapped stopped-return
convergence-in-measure endpoints into one measurable violation event at a
common schedule index. Its probability tends to zero, so every positive
accuracy and confidence budget is eventually satisfied simultaneously.

This is a qualitative finite-union consequence. It assumes no independence,
introduces no convergence rate, and does not use optional stopping.
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

/-- Every capped stopped sampled-return coordinate is measurable. -/
theorem
    measurable_selfConsistentScheduledNaturalCausalInverseSqrtThresholdCappedStoppedAverageSampledReturn
    (mdp : MDP State Action) (initialState : Measure State)
    [IsProbabilityMeasure initialState]
    (rewardSource : mdp.MeanCompatibleRewardKernel)
    (initialTable : DeterministicMarkovPolicyTable mdp)
    (defaultState : State) (varianceProxy : NNReal)
    (baseVisitFloor : Real) (scheduleIndex : Nat) :
    Measurable
      (selfConsistentScheduledNaturalCausalStoppingTimeAverageSampledReturnProcess
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor
          (selfConsistentScheduledNaturalCausalInverseSqrtThresholdCappedDoubleLinearRawWindowFirstPassageStoppingPrefix
            mdp initialState rewardSource initialTable defaultState varianceProxy
              baseVisitFloor)
          scheduleIndex) := by
  exact
    measurable_selfConsistentScheduledNaturalCausalStoppingTimeAverageSampledReturnProcess
      mdp initialState rewardSource initialTable defaultState varianceProxy
        baseVisitFloor _ scheduleIndex (by
          simpa [
            selfConsistentScheduledNaturalCausalInverseSqrtThresholdCappedDoubleLinearRawWindowFirstPassageStoppingPrefix] using
            (selfConsistentScheduledNaturalCausalCappedDoubleLinearRawWindowFirstPassageStoppingPrefix_isStoppingTime
              mdp initialState rewardSource initialTable defaultState
                varianceProxy baseVisitFloor
                  selfConsistentScheduledNaturalCausalInverseSqrtFirstPassageThreshold
                    scheduleIndex))

/-- Every genuine uncapped stopped sampled-return coordinate is measurable. -/
theorem
    measurable_selfConsistentScheduledNaturalCausalInverseSqrtThresholdUnboundedHittingAfterStoppedAverageSampledReturn
    (mdp : MDP State Action) (initialState : Measure State)
    [IsProbabilityMeasure initialState]
    (rewardSource : mdp.MeanCompatibleRewardKernel)
    (initialTable : DeterministicMarkovPolicyTable mdp)
    (defaultState : State) (varianceProxy : NNReal)
    (baseVisitFloor : Real) (scheduleIndex : Nat) :
    Measurable
      (selfConsistentScheduledNaturalCausalStoppingTimeAverageSampledReturnProcess
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor
          (selfConsistentScheduledNaturalCausalInverseSqrtThresholdUnboundedHittingAfterStoppingPrefix
            mdp initialState rewardSource initialTable defaultState varianceProxy
              baseVisitFloor)
          scheduleIndex) := by
  exact
    measurable_selfConsistentScheduledNaturalCausalStoppingTimeAverageSampledReturnProcess
      mdp initialState rewardSource initialTable defaultState varianceProxy
        baseVisitFloor _ scheduleIndex
        (selfConsistentScheduledNaturalCausalInverseSqrtThresholdUnboundedHittingAfterStoppingPrefix_isStoppingTime
          mdp initialState rewardSource initialTable defaultState varianceProxy
            baseVisitFloor scheduleIndex)

/-- Every capped stopped sampled-minus-policy-return gap is measurable. -/
theorem
    measurable_selfConsistentScheduledNaturalCausalInverseSqrtThresholdCappedStoppedSampledPolicyExpectedReturnGap
    (mdp : MDP State Action) (initialState : Measure State)
    [IsProbabilityMeasure initialState]
    (rewardSource : mdp.MeanCompatibleRewardKernel)
    (initialTable : DeterministicMarkovPolicyTable mdp)
    (defaultState : State) (varianceProxy : NNReal)
    (baseVisitFloor : Real) (scheduleIndex : Nat) :
    Measurable
      (selfConsistentScheduledNaturalCausalStoppingTimeAverageSampledPolicyExpectedReturnGapProcess
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor
          (selfConsistentScheduledNaturalCausalInverseSqrtThresholdCappedDoubleLinearRawWindowFirstPassageStoppingPrefix
            mdp initialState rewardSource initialTable defaultState varianceProxy
              baseVisitFloor)
          scheduleIndex) := by
  simpa [
    selfConsistentScheduledNaturalCausalStoppingTimeAverageSampledPolicyExpectedReturnGapProcess] using
    (measurable_selfConsistentScheduledNaturalCausalInverseSqrtThresholdCappedStoppedAverageSampledReturn
      mdp initialState rewardSource initialTable defaultState varianceProxy
        baseVisitFloor scheduleIndex).sub
      (measurable_selfConsistentScheduledNaturalCausalInverseSqrtThresholdCappedStoppedAverageSuccessorPolicyExpectedReturn
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor scheduleIndex)

/-- Every genuine uncapped stopped sampled-minus-policy-return gap is measurable. -/
theorem
    measurable_selfConsistentScheduledNaturalCausalInverseSqrtThresholdUnboundedHittingAfterStoppedSampledPolicyExpectedReturnGap
    (mdp : MDP State Action) (initialState : Measure State)
    [IsProbabilityMeasure initialState]
    (rewardSource : mdp.MeanCompatibleRewardKernel)
    (initialTable : DeterministicMarkovPolicyTable mdp)
    (defaultState : State) (varianceProxy : NNReal)
    (baseVisitFloor : Real) (scheduleIndex : Nat) :
    Measurable
      (selfConsistentScheduledNaturalCausalStoppingTimeAverageSampledPolicyExpectedReturnGapProcess
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor
          (selfConsistentScheduledNaturalCausalInverseSqrtThresholdUnboundedHittingAfterStoppingPrefix
            mdp initialState rewardSource initialTable defaultState varianceProxy
              baseVisitFloor)
          scheduleIndex) := by
  simpa [
    selfConsistentScheduledNaturalCausalStoppingTimeAverageSampledPolicyExpectedReturnGapProcess] using
    (measurable_selfConsistentScheduledNaturalCausalInverseSqrtThresholdUnboundedHittingAfterStoppedAverageSampledReturn
      mdp initialState rewardSource initialTable defaultState varianceProxy
        baseVisitFloor scheduleIndex).sub
      (measurable_selfConsistentScheduledNaturalCausalInverseSqrtThresholdUnboundedHittingAfterStoppedAverageSuccessorPolicyExpectedReturn
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor scheduleIndex)

/-- At one schedule index, at least one of the six literal capped/uncapped
stopped-return errors is at least `epsilon`. -/
noncomputable def
    selfConsistentScheduledNaturalCausalInverseSqrtThresholdCappedUnboundedHittingAfterStoppedReturnJointViolationSet
    (mdp : MDP State Action) (initialState : Measure State)
    [IsProbabilityMeasure initialState]
    (rewardSource : mdp.MeanCompatibleRewardKernel)
    (initialTable : DeterministicMarkovPolicyTable mdp)
    (defaultState : State) (varianceProxy : NNReal)
    (baseVisitFloor epsilon : Real) (scheduleIndex : Nat) :
    Set (HeterogeneousStochasticEpisodeBatchTrajectory mdp
      (fun t =>
        AdaptiveStochasticEpisodeBatchSource.selfConsistentScheduledEpisodes
          mdp varianceProxy baseVisitFloor t)) :=
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
  ((((({trajectory |
          epsilon <= dist (cappedSampledReturn scheduleIndex trajectory) optimal} ∪
        {trajectory |
          epsilon <= dist (uncappedSampledReturn scheduleIndex trajectory) optimal}) ∪
      {trajectory |
        epsilon <= dist (cappedPolicyReturn scheduleIndex trajectory) optimal}) ∪
    {trajectory |
      epsilon <= dist (uncappedPolicyReturn scheduleIndex trajectory) optimal}) ∪
  {trajectory | epsilon <= dist (cappedGap scheduleIndex trajectory) 0}) ∪
  {trajectory | epsilon <= dist (uncappedGap scheduleIndex trajectory) 0})

/-- The six-way stopped-return violation event is measurable. -/
theorem
    measurableSet_selfConsistentScheduledNaturalCausalInverseSqrtThresholdCappedUnboundedHittingAfterStoppedReturnJointViolationSet
    (mdp : MDP State Action) (initialState : Measure State)
    [IsProbabilityMeasure initialState]
    (rewardSource : mdp.MeanCompatibleRewardKernel)
    (initialTable : DeterministicMarkovPolicyTable mdp)
    (defaultState : State) (varianceProxy : NNReal)
    (baseVisitFloor epsilon : Real) (scheduleIndex : Nat) :
    MeasurableSet
      (selfConsistentScheduledNaturalCausalInverseSqrtThresholdCappedUnboundedHittingAfterStoppedReturnJointViolationSet
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor epsilon scheduleIndex) := by
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
  exact
    (((((measurableSet_le measurable_const
                (hCappedSampled.dist measurable_const)).union
            (measurableSet_le measurable_const
              (hUncappedSampled.dist measurable_const))).union
          (measurableSet_le measurable_const
            (hCappedPolicy.dist measurable_const))).union
        (measurableSet_le measurable_const
          (hUncappedPolicy.dist measurable_const))).union
      (measurableSet_le measurable_const
        (hCappedGap.dist measurable_const))).union
      (measurableSet_le measurable_const
        (hUncappedGap.dist measurable_const))

/-- Outside the joint violation event, all six literal errors are strictly
smaller than the same accuracy threshold. -/
theorem
    not_mem_selfConsistentScheduledNaturalCausalInverseSqrtThresholdCappedUnboundedHittingAfterStoppedReturnJointViolationSet_iff
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
    trajectory ∉
        selfConsistentScheduledNaturalCausalInverseSqrtThresholdCappedUnboundedHittingAfterStoppedReturnJointViolationSet
          mdp initialState rewardSource initialTable defaultState varianceProxy
            baseVisitFloor epsilon scheduleIndex ↔
      dist (cappedSampledReturn scheduleIndex trajectory) optimal < epsilon ∧
      dist (uncappedSampledReturn scheduleIndex trajectory) optimal < epsilon ∧
      dist (cappedPolicyReturn scheduleIndex trajectory) optimal < epsilon ∧
      dist (uncappedPolicyReturn scheduleIndex trajectory) optimal < epsilon ∧
      dist (cappedGap scheduleIndex trajectory) 0 < epsilon ∧
      dist (uncappedGap scheduleIndex trajectory) 0 < epsilon := by
  simp only [
    selfConsistentScheduledNaturalCausalInverseSqrtThresholdCappedUnboundedHittingAfterStoppedReturnJointViolationSet,
    Set.mem_union, Set.mem_setOf_eq, not_or, not_le]
  tauto

/-- Probability of the six-way simultaneous stopped-return violation event. -/
noncomputable def
    selfConsistentScheduledNaturalCausalInverseSqrtThresholdCappedUnboundedHittingAfterStoppedReturnJointViolationProbability
    (mdp : MDP State Action) (initialState : Measure State)
    [IsProbabilityMeasure initialState]
    (rewardSource : mdp.MeanCompatibleRewardKernel)
    (initialTable : DeterministicMarkovPolicyTable mdp)
    (defaultState : State) (varianceProxy : NNReal)
    (baseVisitFloor epsilon : Real) (scheduleIndex : Nat) : ENNReal :=
  (selfConsistentScheduledCausalSource mdp initialState rewardSource
      initialTable defaultState varianceProxy baseVisitFloor).trajectoryMeasure
    (selfConsistentScheduledNaturalCausalInverseSqrtThresholdCappedUnboundedHittingAfterStoppedReturnJointViolationSet
      mdp initialState rewardSource initialTable defaultState varianceProxy
        baseVisitFloor epsilon scheduleIndex)

/-- The simultaneous six-way violation probability tends to zero. -/
theorem
    selfConsistentScheduledNaturalCausalInverseSqrtThresholdCappedUnboundedHittingAfterStoppedReturnJointViolationProbability_tendsto_zero
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
    (epsilon : Real) (hepsilon : 0 < epsilon) :
    Tendsto
      (selfConsistentScheduledNaturalCausalInverseSqrtThresholdCappedUnboundedHittingAfterStoppedReturnJointViolationProbability
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor epsilon)
      atTop (nhds 0) := by
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
  let A := fun scheduleIndex =>
    {trajectory | epsilon <=
      dist (cappedSampledReturn scheduleIndex trajectory) optimal}
  let B := fun scheduleIndex =>
    {trajectory | epsilon <=
      dist (uncappedSampledReturn scheduleIndex trajectory) optimal}
  let C := fun scheduleIndex =>
    {trajectory | epsilon <=
      dist (cappedPolicyReturn scheduleIndex trajectory) optimal}
  let D := fun scheduleIndex =>
    {trajectory | epsilon <=
      dist (uncappedPolicyReturn scheduleIndex trajectory) optimal}
  let E := fun scheduleIndex =>
    {trajectory | epsilon <= dist (cappedGap scheduleIndex trajectory) 0}
  let F := fun scheduleIndex =>
    {trajectory | epsilon <= dist (uncappedGap scheduleIndex trajectory) 0}
  have hterminal :=
    selfConsistentScheduledCausalSource_inverseSqrtThresholdCappedUnboundedHittingAfter_stoppedSampledReturn_and_successorPolicyExpectedReturn_inMeasure_and_almostSure_optimality
      mdp initialState rewardSource varianceProxy hvarianceProxy law initialTable
        defaultState support baseVisitFloor hbaseFloor hrewardBound hhorizon
          hbaseVisitFloor
  dsimp only at hterminal
  rcases hterminal with
    ⟨hCappedSampled, hUncappedSampled, hCappedPolicy, hUncappedPolicy,
      hCappedGap, hUncappedGap, _⟩
  have hA : Tendsto (fun n => source.trajectoryMeasure (A n)) atTop (nhds 0) := by
    simpa [A, source, cappedSampledReturn, optimal] using
      (tendstoInMeasure_iff_dist.mp hCappedSampled epsilon hepsilon)
  have hB : Tendsto (fun n => source.trajectoryMeasure (B n)) atTop (nhds 0) := by
    simpa [B, source, uncappedSampledReturn, optimal] using
      (tendstoInMeasure_iff_dist.mp hUncappedSampled epsilon hepsilon)
  have hC : Tendsto (fun n => source.trajectoryMeasure (C n)) atTop (nhds 0) := by
    simpa [C, source, cappedPolicyReturn, optimal] using
      (tendstoInMeasure_iff_dist.mp hCappedPolicy epsilon hepsilon)
  have hD : Tendsto (fun n => source.trajectoryMeasure (D n)) atTop (nhds 0) := by
    simpa [D, source, uncappedPolicyReturn, optimal] using
      (tendstoInMeasure_iff_dist.mp hUncappedPolicy epsilon hepsilon)
  have hE : Tendsto (fun n => source.trajectoryMeasure (E n)) atTop (nhds 0) := by
    simpa [E, source, cappedGap] using
      (tendstoInMeasure_iff_dist.mp hCappedGap epsilon hepsilon)
  have hF : Tendsto (fun n => source.trajectoryMeasure (F n)) atTop (nhds 0) := by
    simpa [F, source, uncappedGap] using
      (tendstoInMeasure_iff_dist.mp hUncappedGap epsilon hepsilon)
  have hsum :
      Tendsto
        (fun n =>
          (((((source.trajectoryMeasure (A n) + source.trajectoryMeasure (B n)) +
            source.trajectoryMeasure (C n)) + source.trajectoryMeasure (D n)) +
            source.trajectoryMeasure (E n)) + source.trajectoryMeasure (F n)))
        atTop (nhds 0) := by
    simpa using (((((hA.add hB).add hC).add hD).add hE).add hF)
  change Tendsto
    (fun n => source.trajectoryMeasure
      (((((A n ∪ B n) ∪ C n) ∪ D n) ∪ E n) ∪ F n)) atTop (nhds 0)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hsum
    (fun _ => zero_le _) ?_
  intro n
  calc
    source.trajectoryMeasure (((((A n ∪ B n) ∪ C n) ∪ D n) ∪ E n) ∪ F n) <=
        source.trajectoryMeasure ((((A n ∪ B n) ∪ C n) ∪ D n) ∪ E n) +
          source.trajectoryMeasure (F n) := measure_union_le _ _
    _ <=
        ((((source.trajectoryMeasure (A n) + source.trajectoryMeasure (B n)) +
          source.trajectoryMeasure (C n)) + source.trajectoryMeasure (D n)) +
          source.trajectoryMeasure (E n)) + source.trajectoryMeasure (F n) := by
      gcongr
      calc
        source.trajectoryMeasure ((((A n ∪ B n) ∪ C n) ∪ D n) ∪ E n) <=
            source.trajectoryMeasure (((A n ∪ B n) ∪ C n) ∪ D n) +
              source.trajectoryMeasure (E n) := measure_union_le _ _
        _ <=
            (((source.trajectoryMeasure (A n) + source.trajectoryMeasure (B n)) +
              source.trajectoryMeasure (C n)) + source.trajectoryMeasure (D n)) +
              source.trajectoryMeasure (E n) := by
          gcongr
          calc
            source.trajectoryMeasure (((A n ∪ B n) ∪ C n) ∪ D n) <=
                source.trajectoryMeasure ((A n ∪ B n) ∪ C n) +
                  source.trajectoryMeasure (D n) := measure_union_le _ _
            _ <=
                ((source.trajectoryMeasure (A n) + source.trajectoryMeasure (B n)) +
                  source.trajectoryMeasure (C n)) + source.trajectoryMeasure (D n) := by
              gcongr
              calc
                source.trajectoryMeasure ((A n ∪ B n) ∪ C n) <=
                    source.trajectoryMeasure (A n ∪ B n) +
                      source.trajectoryMeasure (C n) := measure_union_le _ _
                _ <=
                    (source.trajectoryMeasure (A n) + source.trajectoryMeasure (B n)) +
                      source.trajectoryMeasure (C n) := by
                  gcongr
                  exact measure_union_le _ _

/-- Every positive accuracy and confidence budget is eventually met
simultaneously by all six stopped-return coordinates. -/
theorem
    eventually_selfConsistentScheduledNaturalCausalInverseSqrtThresholdCappedUnboundedHittingAfterStoppedReturnJointViolationProbability_lt
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
    (epsilon delta : Real) (hepsilon : 0 < epsilon) (hdelta : 0 < delta) :
    ∀ᶠ scheduleIndex in atTop,
      selfConsistentScheduledNaturalCausalInverseSqrtThresholdCappedUnboundedHittingAfterStoppedReturnJointViolationProbability
          mdp initialState rewardSource initialTable defaultState varianceProxy
            baseVisitFloor epsilon scheduleIndex < ENNReal.ofReal delta := by
  exact
    (tendsto_order.1
      (selfConsistentScheduledNaturalCausalInverseSqrtThresholdCappedUnboundedHittingAfterStoppedReturnJointViolationProbability_tendsto_zero
        mdp initialState rewardSource varianceProxy hvarianceProxy law initialTable
          defaultState support baseVisitFloor hbaseFloor hrewardBound hhorizon
            hbaseVisitFloor epsilon hepsilon)).2
      (ENNReal.ofReal delta) (ENNReal.ofReal_pos.mpr hdelta)

/-- Terminal simultaneous high-probability certificate for literal stopped
sampled return, actual successor-policy return, and their same-prefix gap at
the capped and genuine uncapped inverse-square-root first-passage prefixes. -/
theorem
    selfConsistentScheduledCausalSource_inverseSqrtThresholdCappedUnboundedHittingAfter_stoppedSampledReturn_and_successorPolicyExpectedReturn_simultaneousHighProbability_optimality
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
    let violationSet :=
      selfConsistentScheduledNaturalCausalInverseSqrtThresholdCappedUnboundedHittingAfterStoppedReturnJointViolationSet
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor
    let violationProbability :=
      selfConsistentScheduledNaturalCausalInverseSqrtThresholdCappedUnboundedHittingAfterStoppedReturnJointViolationProbability
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor
    (forall epsilon scheduleIndex, MeasurableSet (violationSet epsilon scheduleIndex)) ∧
    (forall epsilon scheduleIndex trajectory,
      trajectory ∉ violationSet epsilon scheduleIndex ↔
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
        dist (cappedSampledReturn scheduleIndex trajectory) optimal < epsilon ∧
        dist (uncappedSampledReturn scheduleIndex trajectory) optimal < epsilon ∧
        dist (cappedPolicyReturn scheduleIndex trajectory) optimal < epsilon ∧
        dist (uncappedPolicyReturn scheduleIndex trajectory) optimal < epsilon ∧
        dist (cappedGap scheduleIndex trajectory) 0 < epsilon ∧
        dist (uncappedGap scheduleIndex trajectory) 0 < epsilon) ∧
    (forall epsilon, 0 < epsilon ->
      Tendsto (violationProbability epsilon) atTop (nhds 0)) ∧
    (forall epsilon delta, 0 < epsilon -> 0 < delta ->
      ∀ᶠ scheduleIndex in atTop,
        violationProbability epsilon scheduleIndex < ENNReal.ofReal delta) := by
  dsimp only
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact fun epsilon scheduleIndex =>
      measurableSet_selfConsistentScheduledNaturalCausalInverseSqrtThresholdCappedUnboundedHittingAfterStoppedReturnJointViolationSet
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor epsilon scheduleIndex
  · exact fun epsilon scheduleIndex trajectory =>
      not_mem_selfConsistentScheduledNaturalCausalInverseSqrtThresholdCappedUnboundedHittingAfterStoppedReturnJointViolationSet_iff
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor epsilon scheduleIndex trajectory
  · exact fun epsilon hepsilon =>
      selfConsistentScheduledNaturalCausalInverseSqrtThresholdCappedUnboundedHittingAfterStoppedReturnJointViolationProbability_tendsto_zero
        mdp initialState rewardSource varianceProxy hvarianceProxy law initialTable
          defaultState support baseVisitFloor hbaseFloor hrewardBound hhorizon
            hbaseVisitFloor epsilon hepsilon
  · exact fun epsilon delta hepsilon hdelta =>
      eventually_selfConsistentScheduledNaturalCausalInverseSqrtThresholdCappedUnboundedHittingAfterStoppedReturnJointViolationProbability_lt
        mdp initialState rewardSource varianceProxy hvarianceProxy law initialTable
          defaultState support baseVisitFloor hbaseFloor hrewardBound hhorizon
            hbaseVisitFloor epsilon delta hepsilon hdelta

end AdaptiveStochasticSampledEmpiricalOptimisticSource

end BanditRLProof.FiniteHorizonRL
