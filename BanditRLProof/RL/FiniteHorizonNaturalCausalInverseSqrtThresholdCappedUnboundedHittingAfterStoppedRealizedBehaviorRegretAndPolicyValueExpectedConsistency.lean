import BanditRLProof.RL.FiniteHorizonNaturalCausalInverseSqrtThresholdCappedUnboundedHittingAfterStoppedBehaviorExpectedRegretAndReturnDeviationExpectedTruncationReplacement

/-!
# Expected consistency of stopped realized regret and policy value

This module identifies the expected gap between stopped average realized
behavior regret and its successor-policy value-gap coordinate with the
negative expected return deviation. It proves that gap vanishes for both the
capped first-passage approximation and the genuine uncapped `hittingAfter`
prefix, then combines those vertical limits with the accepted horizontal
truncation limits. It does not exchange expectation with a stopping index.
-/

open Filter MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal ProbabilityTheory Topology

namespace BanditRLProof.FiniteHorizonRL

universe u v

variable {State : Type u} {Action : Type v}
    [MeasurableSpace State] [MeasurableSpace Action]
    [Fintype State] [Fintype Action]
    [DecidableEq State] [DecidableEq Action]
    [MeasurableSingletonClass State] [MeasurableSingletonClass Action]
    [Nonempty State] [Nonempty Action]

namespace AdaptiveStochasticSampledEmpiricalOptimisticSource

/-- For the capped prefix, the expected realized-minus-policy-value gap is
exactly the negative expected return deviation. -/
theorem
    selfConsistentScheduledNaturalCausalInverseSqrtThresholdCappedStoppedAverageRealizedBehaviorRegretIntegral_sub_behaviorExpectedRegretIntegral_eq_neg_returnDeviationIntegral
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
    let behaviorProcess :=
      selfConsistentScheduledNaturalCausalStoppingTimeAverageBehaviorExpectedRegretProcess
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor stoppingPrefix
    let realizedProcess :=
      selfConsistentScheduledNaturalCausalStoppingTimeAverageRealizedBehaviorRegretProcess
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor stoppingPrefix
    let returnProcess :=
      selfConsistentScheduledNaturalCausalStoppingTimeAverageReturnDeviationProcess
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor stoppingPrefix
    integral source.trajectoryMeasure (realizedProcess scheduleIndex) -
        integral source.trajectoryMeasure (behaviorProcess scheduleIndex) =
      -integral source.trajectoryMeasure (returnProcess scheduleIndex) := by
  dsimp only
  rw [selfConsistentScheduledNaturalCausalInverseSqrtThresholdCappedStoppedAverageRealizedBehaviorRegretIntegral_eq_behaviorExpected_sub_returnDeviation
    mdp initialState rewardSource varianceProxy hvarianceProxy law initialTable
      defaultState support baseVisitFloor hbaseFloor hrewardBound hhorizon
        hbaseVisitFloor scheduleIndex]
  ring

/-- For the genuine uncapped `hittingAfter` prefix, the expected
realized-minus-policy-value gap is exactly the negative expected return
deviation. -/
theorem
    selfConsistentScheduledNaturalCausalInverseSqrtThresholdUnboundedHittingAfterStoppedAverageRealizedBehaviorRegretIntegral_sub_behaviorExpectedRegretIntegral_eq_neg_returnDeviationIntegral
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
    let behaviorProcess :=
      selfConsistentScheduledNaturalCausalStoppingTimeAverageBehaviorExpectedRegretProcess
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor stoppingPrefix
    let realizedProcess :=
      selfConsistentScheduledNaturalCausalStoppingTimeAverageRealizedBehaviorRegretProcess
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor stoppingPrefix
    let returnProcess :=
      selfConsistentScheduledNaturalCausalStoppingTimeAverageReturnDeviationProcess
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor stoppingPrefix
    integral source.trajectoryMeasure (realizedProcess scheduleIndex) -
        integral source.trajectoryMeasure (behaviorProcess scheduleIndex) =
      -integral source.trajectoryMeasure (returnProcess scheduleIndex) := by
  dsimp only
  rw [selfConsistentScheduledNaturalCausalInverseSqrtThresholdUnboundedHittingAfterStoppedAverageRealizedBehaviorRegretIntegral_eq_behaviorExpected_sub_returnDeviation
    mdp initialState rewardSource varianceProxy hvarianceProxy law initialTable
      defaultState support baseVisitFloor hbaseFloor hrewardBound hhorizon
        hbaseVisitFloor scheduleIndex]
  ring

/-- The capped expected realized-minus-policy-value gap tends to zero. -/
theorem
    selfConsistentScheduledNaturalCausalInverseSqrtThresholdCappedStoppedAverageRealizedBehaviorRegretPolicyValueExpectedGap_tendsto_zero
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
    let behaviorProcess :=
      selfConsistentScheduledNaturalCausalStoppingTimeAverageBehaviorExpectedRegretProcess
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor stoppingPrefix
    let realizedProcess :=
      selfConsistentScheduledNaturalCausalStoppingTimeAverageRealizedBehaviorRegretProcess
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor stoppingPrefix
    Tendsto
      (fun scheduleIndex =>
        integral source.trajectoryMeasure (realizedProcess scheduleIndex) -
          integral source.trajectoryMeasure (behaviorProcess scheduleIndex))
      atTop (nhds 0) := by
  dsimp only
  let source := selfConsistentScheduledCausalSource mdp initialState
    rewardSource initialTable defaultState varianceProxy baseVisitFloor
  let stoppingPrefix :=
    selfConsistentScheduledNaturalCausalInverseSqrtThresholdCappedDoubleLinearRawWindowFirstPassageStoppingPrefix
      mdp initialState rewardSource initialTable defaultState varianceProxy
        baseVisitFloor
  let behaviorProcess :=
    selfConsistentScheduledNaturalCausalStoppingTimeAverageBehaviorExpectedRegretProcess
      mdp initialState rewardSource initialTable defaultState varianceProxy
        baseVisitFloor stoppingPrefix
  let realizedProcess :=
    selfConsistentScheduledNaturalCausalStoppingTimeAverageRealizedBehaviorRegretProcess
      mdp initialState rewardSource initialTable defaultState varianceProxy
        baseVisitFloor stoppingPrefix
  let returnProcess :=
    selfConsistentScheduledNaturalCausalStoppingTimeAverageReturnDeviationProcess
      mdp initialState rewardSource initialTable defaultState varianceProxy
        baseVisitFloor stoppingPrefix
  have hreturn :
      Tendsto
        (fun scheduleIndex =>
          integral source.trajectoryMeasure (returnProcess scheduleIndex))
        atTop (nhds 0) :=
    selfConsistentScheduledNaturalCausalInverseSqrtThresholdCappedStoppedReturnDeviationIntegral_tendsto_zero
      mdp initialState rewardSource varianceProxy hvarianceProxy law initialTable
        defaultState support baseVisitFloor hbaseFloor hrewardBound hhorizon
          hbaseVisitFloor
  have hsequence :
      (fun scheduleIndex =>
        integral source.trajectoryMeasure (realizedProcess scheduleIndex) -
          integral source.trajectoryMeasure (behaviorProcess scheduleIndex)) =
        (fun scheduleIndex =>
          -integral source.trajectoryMeasure (returnProcess scheduleIndex)) := by
    funext scheduleIndex
    exact
      selfConsistentScheduledNaturalCausalInverseSqrtThresholdCappedStoppedAverageRealizedBehaviorRegretIntegral_sub_behaviorExpectedRegretIntegral_eq_neg_returnDeviationIntegral
        mdp initialState rewardSource varianceProxy hvarianceProxy law initialTable
          defaultState support baseVisitFloor hbaseFloor hrewardBound hhorizon
            hbaseVisitFloor scheduleIndex
  rw [hsequence]
  simpa only [neg_zero] using hreturn.neg

/-- The absolute capped expected realized-minus-policy-value gap tends to
zero. -/
theorem
    selfConsistentScheduledNaturalCausalInverseSqrtThresholdCappedStoppedAverageRealizedBehaviorRegretPolicyValueExpectedGapAbs_tendsto_zero
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
    let behaviorProcess :=
      selfConsistentScheduledNaturalCausalStoppingTimeAverageBehaviorExpectedRegretProcess
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor stoppingPrefix
    let realizedProcess :=
      selfConsistentScheduledNaturalCausalStoppingTimeAverageRealizedBehaviorRegretProcess
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor stoppingPrefix
    Tendsto
      (fun scheduleIndex =>
        |integral source.trajectoryMeasure (realizedProcess scheduleIndex) -
          integral source.trajectoryMeasure (behaviorProcess scheduleIndex)|)
      atTop (nhds 0) := by
  dsimp only
  have hgap :=
    selfConsistentScheduledNaturalCausalInverseSqrtThresholdCappedStoppedAverageRealizedBehaviorRegretPolicyValueExpectedGap_tendsto_zero
      mdp initialState rewardSource varianceProxy hvarianceProxy law initialTable
        defaultState support baseVisitFloor hbaseFloor hrewardBound hhorizon
          hbaseVisitFloor
  simpa only [abs_zero] using (continuous_abs.tendsto 0).comp hgap

/-- The genuine uncapped expected realized-minus-policy-value gap tends to
zero. -/
theorem
    selfConsistentScheduledNaturalCausalInverseSqrtThresholdUnboundedHittingAfterStoppedAverageRealizedBehaviorRegretPolicyValueExpectedGap_tendsto_zero
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
    let behaviorProcess :=
      selfConsistentScheduledNaturalCausalStoppingTimeAverageBehaviorExpectedRegretProcess
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor stoppingPrefix
    let realizedProcess :=
      selfConsistentScheduledNaturalCausalStoppingTimeAverageRealizedBehaviorRegretProcess
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor stoppingPrefix
    Tendsto
      (fun scheduleIndex =>
        integral source.trajectoryMeasure (realizedProcess scheduleIndex) -
          integral source.trajectoryMeasure (behaviorProcess scheduleIndex))
      atTop (nhds 0) := by
  dsimp only
  let source := selfConsistentScheduledCausalSource mdp initialState
    rewardSource initialTable defaultState varianceProxy baseVisitFloor
  let stoppingPrefix :=
    selfConsistentScheduledNaturalCausalInverseSqrtThresholdUnboundedHittingAfterStoppingPrefix
      mdp initialState rewardSource initialTable defaultState varianceProxy
        baseVisitFloor
  let behaviorProcess :=
    selfConsistentScheduledNaturalCausalStoppingTimeAverageBehaviorExpectedRegretProcess
      mdp initialState rewardSource initialTable defaultState varianceProxy
        baseVisitFloor stoppingPrefix
  let realizedProcess :=
    selfConsistentScheduledNaturalCausalStoppingTimeAverageRealizedBehaviorRegretProcess
      mdp initialState rewardSource initialTable defaultState varianceProxy
        baseVisitFloor stoppingPrefix
  let returnProcess :=
    selfConsistentScheduledNaturalCausalStoppingTimeAverageReturnDeviationProcess
      mdp initialState rewardSource initialTable defaultState varianceProxy
        baseVisitFloor stoppingPrefix
  have hreturn :
      Tendsto
        (fun scheduleIndex =>
          integral source.trajectoryMeasure (returnProcess scheduleIndex))
        atTop (nhds 0) :=
    selfConsistentScheduledNaturalCausalInverseSqrtThresholdUnboundedHittingAfterStoppedReturnDeviationIntegral_tendsto_zero
      mdp initialState rewardSource varianceProxy hvarianceProxy law initialTable
        defaultState support baseVisitFloor hbaseFloor hrewardBound hhorizon
          hbaseVisitFloor
  have hsequence :
      (fun scheduleIndex =>
        integral source.trajectoryMeasure (realizedProcess scheduleIndex) -
          integral source.trajectoryMeasure (behaviorProcess scheduleIndex)) =
        (fun scheduleIndex =>
          -integral source.trajectoryMeasure (returnProcess scheduleIndex)) := by
    funext scheduleIndex
    exact
      selfConsistentScheduledNaturalCausalInverseSqrtThresholdUnboundedHittingAfterStoppedAverageRealizedBehaviorRegretIntegral_sub_behaviorExpectedRegretIntegral_eq_neg_returnDeviationIntegral
        mdp initialState rewardSource varianceProxy hvarianceProxy law initialTable
          defaultState support baseVisitFloor hbaseFloor hrewardBound hhorizon
            hbaseVisitFloor scheduleIndex
  rw [hsequence]
  simpa only [neg_zero] using hreturn.neg

/-- The absolute genuine uncapped expected realized-minus-policy-value gap
tends to zero. -/
theorem
    selfConsistentScheduledNaturalCausalInverseSqrtThresholdUnboundedHittingAfterStoppedAverageRealizedBehaviorRegretPolicyValueExpectedGapAbs_tendsto_zero
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
    let behaviorProcess :=
      selfConsistentScheduledNaturalCausalStoppingTimeAverageBehaviorExpectedRegretProcess
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor stoppingPrefix
    let realizedProcess :=
      selfConsistentScheduledNaturalCausalStoppingTimeAverageRealizedBehaviorRegretProcess
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor stoppingPrefix
    Tendsto
      (fun scheduleIndex =>
        |integral source.trajectoryMeasure (realizedProcess scheduleIndex) -
          integral source.trajectoryMeasure (behaviorProcess scheduleIndex)|)
      atTop (nhds 0) := by
  dsimp only
  have hgap :=
    selfConsistentScheduledNaturalCausalInverseSqrtThresholdUnboundedHittingAfterStoppedAverageRealizedBehaviorRegretPolicyValueExpectedGap_tendsto_zero
      mdp initialState rewardSource varianceProxy hvarianceProxy law initialTable
        defaultState support baseVisitFloor hbaseFloor hrewardBound hhorizon
          hbaseVisitFloor
  simpa only [abs_zero] using (continuous_abs.tendsto 0).comp hgap

/-- Terminal expected-consistency square for capped and genuine uncapped
first-passage prefixes. The horizontal edges replace capped expectations by
uncapped expectations, while the vertical edges replace successor-policy
value gaps by realized regret expectations. -/
theorem
    selfConsistentScheduledCausalSource_inverseSqrtThresholdCappedUnboundedHittingAfter_stoppedRealizedBehaviorRegret_and_policyValue_expected_consistency
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
    let cappedBehavior :=
      selfConsistentScheduledNaturalCausalStoppingTimeAverageBehaviorExpectedRegretProcess
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor cappedStoppingPrefix
    let uncappedBehavior :=
      selfConsistentScheduledNaturalCausalStoppingTimeAverageBehaviorExpectedRegretProcess
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor uncappedStoppingPrefix
    let cappedRealized :=
      selfConsistentScheduledNaturalCausalStoppingTimeAverageRealizedBehaviorRegretProcess
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor cappedStoppingPrefix
    let uncappedRealized :=
      selfConsistentScheduledNaturalCausalStoppingTimeAverageRealizedBehaviorRegretProcess
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor uncappedStoppingPrefix
    let cappedReturn :=
      selfConsistentScheduledNaturalCausalStoppingTimeAverageReturnDeviationProcess
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor cappedStoppingPrefix
    let uncappedReturn :=
      selfConsistentScheduledNaturalCausalStoppingTimeAverageReturnDeviationProcess
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor uncappedStoppingPrefix
    (forall scheduleIndex,
      integral source.trajectoryMeasure (cappedRealized scheduleIndex) =
          integral source.trajectoryMeasure (cappedBehavior scheduleIndex) -
            integral source.trajectoryMeasure (cappedReturn scheduleIndex) /\
        integral source.trajectoryMeasure (uncappedRealized scheduleIndex) =
          integral source.trajectoryMeasure (uncappedBehavior scheduleIndex) -
            integral source.trajectoryMeasure (uncappedReturn scheduleIndex)) /\
      (forall scheduleIndex,
        integral source.trajectoryMeasure (cappedRealized scheduleIndex) -
            integral source.trajectoryMeasure (cappedBehavior scheduleIndex) =
              -integral source.trajectoryMeasure (cappedReturn scheduleIndex) /\
          integral source.trajectoryMeasure (uncappedRealized scheduleIndex) -
            integral source.trajectoryMeasure (uncappedBehavior scheduleIndex) =
              -integral source.trajectoryMeasure (uncappedReturn scheduleIndex)) /\
      (forall scheduleIndex,
        (integral source.trajectoryMeasure (uncappedBehavior scheduleIndex) -
              integral source.trajectoryMeasure (cappedBehavior scheduleIndex)) +
            (integral source.trajectoryMeasure (uncappedRealized scheduleIndex) -
              integral source.trajectoryMeasure (uncappedBehavior scheduleIndex)) =
          (integral source.trajectoryMeasure (cappedRealized scheduleIndex) -
              integral source.trajectoryMeasure (cappedBehavior scheduleIndex)) +
            (integral source.trajectoryMeasure (uncappedRealized scheduleIndex) -
              integral source.trajectoryMeasure (cappedRealized scheduleIndex))) /\
      Tendsto
        (fun scheduleIndex =>
          integral source.trajectoryMeasure (uncappedBehavior scheduleIndex) -
            integral source.trajectoryMeasure (cappedBehavior scheduleIndex))
        atTop (nhds 0) /\
      Tendsto
        (fun scheduleIndex =>
          |integral source.trajectoryMeasure (uncappedBehavior scheduleIndex) -
            integral source.trajectoryMeasure (cappedBehavior scheduleIndex)|)
        atTop (nhds 0) /\
      Tendsto
        (fun scheduleIndex =>
          integral source.trajectoryMeasure (uncappedRealized scheduleIndex) -
            integral source.trajectoryMeasure (cappedRealized scheduleIndex))
        atTop (nhds 0) /\
      Tendsto
        (fun scheduleIndex =>
          |integral source.trajectoryMeasure (uncappedRealized scheduleIndex) -
            integral source.trajectoryMeasure (cappedRealized scheduleIndex)|)
        atTop (nhds 0) /\
      Tendsto
        (fun scheduleIndex =>
          integral source.trajectoryMeasure (cappedRealized scheduleIndex) -
            integral source.trajectoryMeasure (cappedBehavior scheduleIndex))
        atTop (nhds 0) /\
      Tendsto
        (fun scheduleIndex =>
          |integral source.trajectoryMeasure (cappedRealized scheduleIndex) -
            integral source.trajectoryMeasure (cappedBehavior scheduleIndex)|)
        atTop (nhds 0) /\
      Tendsto
        (fun scheduleIndex =>
          integral source.trajectoryMeasure (uncappedRealized scheduleIndex) -
            integral source.trajectoryMeasure (uncappedBehavior scheduleIndex))
        atTop (nhds 0) /\
      Tendsto
        (fun scheduleIndex =>
          |integral source.trajectoryMeasure (uncappedRealized scheduleIndex) -
            integral source.trajectoryMeasure (uncappedBehavior scheduleIndex)|)
        atTop (nhds 0) := by
  dsimp only
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro scheduleIndex
    exact
      ⟨selfConsistentScheduledNaturalCausalInverseSqrtThresholdCappedStoppedAverageRealizedBehaviorRegretIntegral_eq_behaviorExpected_sub_returnDeviation
          mdp initialState rewardSource varianceProxy hvarianceProxy law initialTable
            defaultState support baseVisitFloor hbaseFloor hrewardBound hhorizon
              hbaseVisitFloor scheduleIndex,
        selfConsistentScheduledNaturalCausalInverseSqrtThresholdUnboundedHittingAfterStoppedAverageRealizedBehaviorRegretIntegral_eq_behaviorExpected_sub_returnDeviation
          mdp initialState rewardSource varianceProxy hvarianceProxy law initialTable
            defaultState support baseVisitFloor hbaseFloor hrewardBound hhorizon
              hbaseVisitFloor scheduleIndex⟩
  · intro scheduleIndex
    exact
      ⟨selfConsistentScheduledNaturalCausalInverseSqrtThresholdCappedStoppedAverageRealizedBehaviorRegretIntegral_sub_behaviorExpectedRegretIntegral_eq_neg_returnDeviationIntegral
          mdp initialState rewardSource varianceProxy hvarianceProxy law initialTable
            defaultState support baseVisitFloor hbaseFloor hrewardBound hhorizon
              hbaseVisitFloor scheduleIndex,
        selfConsistentScheduledNaturalCausalInverseSqrtThresholdUnboundedHittingAfterStoppedAverageRealizedBehaviorRegretIntegral_sub_behaviorExpectedRegretIntegral_eq_neg_returnDeviationIntegral
          mdp initialState rewardSource varianceProxy hvarianceProxy law initialTable
            defaultState support baseVisitFloor hbaseFloor hrewardBound hhorizon
              hbaseVisitFloor scheduleIndex⟩
  · intro scheduleIndex
    ring
  · exact
      selfConsistentScheduledNaturalCausalInverseSqrtThresholdCappedUnboundedHittingAfterStoppedBehaviorExpectedRegretExpectedGap_tendsto_zero
        mdp initialState rewardSource varianceProxy hvarianceProxy law initialTable
          defaultState support baseVisitFloor hbaseFloor hrewardBound hhorizon
            hbaseVisitFloor
  · exact
      selfConsistentScheduledNaturalCausalInverseSqrtThresholdCappedUnboundedHittingAfterStoppedBehaviorExpectedRegretExpectedGapAbs_tendsto_zero
        mdp initialState rewardSource varianceProxy hvarianceProxy law initialTable
          defaultState support baseVisitFloor hbaseFloor hrewardBound hhorizon
            hbaseVisitFloor
  · exact
      selfConsistentScheduledNaturalCausalInverseSqrtThresholdCappedUnboundedHittingAfterStoppedAverageRealizedBehaviorRegretExpectedGap_tendsto_zero
        mdp initialState rewardSource varianceProxy hvarianceProxy law initialTable
          defaultState support baseVisitFloor hbaseFloor hrewardBound hhorizon
            hbaseVisitFloor
  · exact
      selfConsistentScheduledNaturalCausalInverseSqrtThresholdCappedUnboundedHittingAfterStoppedAverageRealizedBehaviorRegretExpectedGapAbs_tendsto_zero
        mdp initialState rewardSource varianceProxy hvarianceProxy law initialTable
          defaultState support baseVisitFloor hbaseFloor hrewardBound hhorizon
            hbaseVisitFloor
  · exact
      selfConsistentScheduledNaturalCausalInverseSqrtThresholdCappedStoppedAverageRealizedBehaviorRegretPolicyValueExpectedGap_tendsto_zero
        mdp initialState rewardSource varianceProxy hvarianceProxy law initialTable
          defaultState support baseVisitFloor hbaseFloor hrewardBound hhorizon
            hbaseVisitFloor
  · exact
      selfConsistentScheduledNaturalCausalInverseSqrtThresholdCappedStoppedAverageRealizedBehaviorRegretPolicyValueExpectedGapAbs_tendsto_zero
        mdp initialState rewardSource varianceProxy hvarianceProxy law initialTable
          defaultState support baseVisitFloor hbaseFloor hrewardBound hhorizon
            hbaseVisitFloor
  · exact
      selfConsistentScheduledNaturalCausalInverseSqrtThresholdUnboundedHittingAfterStoppedAverageRealizedBehaviorRegretPolicyValueExpectedGap_tendsto_zero
        mdp initialState rewardSource varianceProxy hvarianceProxy law initialTable
          defaultState support baseVisitFloor hbaseFloor hrewardBound hhorizon
            hbaseVisitFloor
  · exact
      selfConsistentScheduledNaturalCausalInverseSqrtThresholdUnboundedHittingAfterStoppedAverageRealizedBehaviorRegretPolicyValueExpectedGapAbs_tendsto_zero
        mdp initialState rewardSource varianceProxy hvarianceProxy law initialTable
          defaultState support baseVisitFloor hbaseFloor hrewardBound hhorizon
            hbaseVisitFloor

end AdaptiveStochasticSampledEmpiricalOptimisticSource

end BanditRLProof.FiniteHorizonRL
