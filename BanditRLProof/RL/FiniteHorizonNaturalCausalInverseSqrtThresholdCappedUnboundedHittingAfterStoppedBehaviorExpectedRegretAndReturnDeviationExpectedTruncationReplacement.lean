import BanditRLProof.RL.FiniteHorizonNaturalCausalInverseSqrtThresholdCappedUnboundedHittingAfterExpectedRegretTruncationReplacement
import BanditRLProof.RL.FiniteHorizonNaturalCausalInverseSqrtThresholdCappedUnboundedHittingAfterStoppedBehaviorExpectedRegretAndReturnDeviationL1TruncationEquivalence

/-!
# Expected truncation replacement for stopped behavior and return coordinates

This module transports the accepted componentwise `L1` truncation theorem
through the Bochner integral. It compares capped and genuine uncapped
successor-policy value gaps and return deviations on the same generated
trajectory law, and preserves the exact expected realized-regret
decomposition. It does not exchange expectation with a stopping index.
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

/-- The signed expectation gap between the uncapped and capped stopped
behavior expected-regret coordinates tends to zero. -/
theorem
    selfConsistentScheduledNaturalCausalInverseSqrtThresholdCappedUnboundedHittingAfterStoppedBehaviorExpectedRegretExpectedGap_tendsto_zero
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
    Tendsto
      (fun scheduleIndex =>
        integral source.trajectoryMeasure (uncappedBehavior scheduleIndex) -
          integral source.trajectoryMeasure (cappedBehavior scheduleIndex))
      atTop (nhds 0) := by
  dsimp only
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
  have huncapped : forall scheduleIndex,
      Integrable (uncappedBehavior scheduleIndex) source.trajectoryMeasure :=
    fun scheduleIndex =>
      (memLp_one_selfConsistentScheduledNaturalCausalInverseSqrtThresholdUnboundedHittingAfterStoppedBehaviorExpectedRegret
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor hrewardBound scheduleIndex).integrable le_rfl
  have hcapped : forall scheduleIndex,
      Integrable (cappedBehavior scheduleIndex) source.trajectoryMeasure :=
    fun scheduleIndex =>
      (memLp_one_selfConsistentScheduledNaturalCausalInverseSqrtThresholdCappedStoppedBehaviorExpectedRegret
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor hrewardBound scheduleIndex).integrable le_rfl
  have hdiff :
      Tendsto
        (fun scheduleIndex => integral source.trajectoryMeasure
          (uncappedBehavior scheduleIndex - cappedBehavior scheduleIndex))
        atTop (nhds 0) := by
    simpa only [source, cappedStoppingPrefix, uncappedStoppingPrefix,
      cappedBehavior, uncappedBehavior] using
      (selfConsistentScheduledNaturalCausalInverseSqrtThresholdCappedUnboundedHittingAfterStoppedBehaviorExpectedRegretDifferenceIntegral_tendsto_zero
        mdp initialState rewardSource varianceProxy hvarianceProxy law initialTable
          defaultState support baseVisitFloor hbaseFloor hrewardBound
            (lt_trans (by decide : 0 < 4) hhorizon) hbaseVisitFloor)
  have hfun :
      (fun scheduleIndex => integral source.trajectoryMeasure
        (uncappedBehavior scheduleIndex - cappedBehavior scheduleIndex)) =
      (fun scheduleIndex =>
        integral source.trajectoryMeasure (uncappedBehavior scheduleIndex) -
          integral source.trajectoryMeasure (cappedBehavior scheduleIndex)) := by
    funext scheduleIndex
    exact integral_sub (huncapped scheduleIndex) (hcapped scheduleIndex)
  rw [hfun] at hdiff
  simpa only [source, cappedStoppingPrefix, uncappedStoppingPrefix,
    cappedBehavior, uncappedBehavior] using hdiff

/-- The absolute expectation gap between the uncapped and capped stopped
behavior expected-regret coordinates tends to zero. -/
theorem
    selfConsistentScheduledNaturalCausalInverseSqrtThresholdCappedUnboundedHittingAfterStoppedBehaviorExpectedRegretExpectedGapAbs_tendsto_zero
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
    Tendsto
      (fun scheduleIndex =>
        |integral source.trajectoryMeasure (uncappedBehavior scheduleIndex) -
          integral source.trajectoryMeasure (cappedBehavior scheduleIndex)|)
      atTop (nhds 0) := by
  dsimp only
  have hgap :=
    selfConsistentScheduledNaturalCausalInverseSqrtThresholdCappedUnboundedHittingAfterStoppedBehaviorExpectedRegretExpectedGap_tendsto_zero
      mdp initialState rewardSource varianceProxy hvarianceProxy law initialTable
        defaultState support baseVisitFloor hbaseFloor hrewardBound hhorizon
          hbaseVisitFloor
  simpa only [abs_zero] using (continuous_abs.tendsto 0).comp hgap

/-- The signed expectation gap between the uncapped and capped stopped
return-deviation coordinates tends to zero. -/
theorem
    selfConsistentScheduledNaturalCausalInverseSqrtThresholdCappedUnboundedHittingAfterStoppedReturnDeviationExpectedGap_tendsto_zero
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
    let cappedReturn :=
      selfConsistentScheduledNaturalCausalStoppingTimeAverageReturnDeviationProcess
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor cappedStoppingPrefix
    let uncappedReturn :=
      selfConsistentScheduledNaturalCausalStoppingTimeAverageReturnDeviationProcess
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor uncappedStoppingPrefix
    Tendsto
      (fun scheduleIndex =>
        integral source.trajectoryMeasure (uncappedReturn scheduleIndex) -
          integral source.trajectoryMeasure (cappedReturn scheduleIndex))
      atTop (nhds 0) := by
  dsimp only
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
  let cappedReturn :=
    selfConsistentScheduledNaturalCausalStoppingTimeAverageReturnDeviationProcess
      mdp initialState rewardSource initialTable defaultState varianceProxy
        baseVisitFloor cappedStoppingPrefix
  let uncappedReturn :=
    selfConsistentScheduledNaturalCausalStoppingTimeAverageReturnDeviationProcess
      mdp initialState rewardSource initialTable defaultState varianceProxy
        baseVisitFloor uncappedStoppingPrefix
  have huncapped : forall scheduleIndex,
      Integrable (uncappedReturn scheduleIndex) source.trajectoryMeasure :=
    fun scheduleIndex =>
      (memLp_one_selfConsistentScheduledNaturalCausalInverseSqrtThresholdUnboundedHittingAfterStoppedReturnDeviation
        mdp initialState rewardSource varianceProxy hvarianceProxy law initialTable
          defaultState support baseVisitFloor hbaseFloor hrewardBound hhorizon
            hbaseVisitFloor scheduleIndex).integrable le_rfl
  have hcapped : forall scheduleIndex,
      Integrable (cappedReturn scheduleIndex) source.trajectoryMeasure :=
    fun scheduleIndex =>
      (memLp_one_selfConsistentScheduledNaturalCausalInverseSqrtThresholdCappedStoppedReturnDeviation
        mdp initialState rewardSource varianceProxy hvarianceProxy law initialTable
          defaultState support baseVisitFloor hbaseFloor hrewardBound hhorizon
            hbaseVisitFloor scheduleIndex).integrable le_rfl
  have hdiff :
      Tendsto
        (fun scheduleIndex => integral source.trajectoryMeasure
          (uncappedReturn scheduleIndex - cappedReturn scheduleIndex))
        atTop (nhds 0) := by
    simpa only [source, cappedStoppingPrefix, uncappedStoppingPrefix,
      cappedReturn, uncappedReturn] using
      (selfConsistentScheduledNaturalCausalInverseSqrtThresholdCappedUnboundedHittingAfterStoppedReturnDeviationDifferenceIntegral_tendsto_zero
        mdp initialState rewardSource varianceProxy hvarianceProxy law initialTable
          defaultState support baseVisitFloor hbaseFloor hrewardBound hhorizon
            hbaseVisitFloor)
  have hfun :
      (fun scheduleIndex => integral source.trajectoryMeasure
        (uncappedReturn scheduleIndex - cappedReturn scheduleIndex)) =
      (fun scheduleIndex =>
        integral source.trajectoryMeasure (uncappedReturn scheduleIndex) -
          integral source.trajectoryMeasure (cappedReturn scheduleIndex)) := by
    funext scheduleIndex
    exact integral_sub (huncapped scheduleIndex) (hcapped scheduleIndex)
  rw [hfun] at hdiff
  simpa only [source, cappedStoppingPrefix, uncappedStoppingPrefix,
    cappedReturn, uncappedReturn] using hdiff

/-- The absolute expectation gap between the uncapped and capped stopped
return-deviation coordinates tends to zero. -/
theorem
    selfConsistentScheduledNaturalCausalInverseSqrtThresholdCappedUnboundedHittingAfterStoppedReturnDeviationExpectedGapAbs_tendsto_zero
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
    let cappedReturn :=
      selfConsistentScheduledNaturalCausalStoppingTimeAverageReturnDeviationProcess
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor cappedStoppingPrefix
    let uncappedReturn :=
      selfConsistentScheduledNaturalCausalStoppingTimeAverageReturnDeviationProcess
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor uncappedStoppingPrefix
    Tendsto
      (fun scheduleIndex =>
        |integral source.trajectoryMeasure (uncappedReturn scheduleIndex) -
          integral source.trajectoryMeasure (cappedReturn scheduleIndex)|)
      atTop (nhds 0) := by
  dsimp only
  have hgap :=
    selfConsistentScheduledNaturalCausalInverseSqrtThresholdCappedUnboundedHittingAfterStoppedReturnDeviationExpectedGap_tendsto_zero
      mdp initialState rewardSource varianceProxy hvarianceProxy law initialTable
        defaultState support baseVisitFloor hbaseFloor hrewardBound hhorizon
          hbaseVisitFloor
  simpa only [abs_zero] using (continuous_abs.tendsto 0).comp hgap

/-- Exact expected decomposition for the capped first-passage prefix. -/
theorem
    selfConsistentScheduledNaturalCausalInverseSqrtThresholdCappedStoppedAverageRealizedBehaviorRegretIntegral_eq_behaviorExpected_sub_returnDeviation
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
    integral source.trajectoryMeasure (realizedProcess scheduleIndex) =
      integral source.trajectoryMeasure (behaviorProcess scheduleIndex) -
        integral source.trajectoryMeasure (returnProcess scheduleIndex) := by
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
  have hbehavior : Integrable (behaviorProcess scheduleIndex)
      source.trajectoryMeasure :=
    (memLp_one_selfConsistentScheduledNaturalCausalInverseSqrtThresholdCappedStoppedBehaviorExpectedRegret
      mdp initialState rewardSource initialTable defaultState varianceProxy
        baseVisitFloor hrewardBound scheduleIndex).integrable le_rfl
  have hreturn : Integrable (returnProcess scheduleIndex)
      source.trajectoryMeasure :=
    (memLp_one_selfConsistentScheduledNaturalCausalInverseSqrtThresholdCappedStoppedReturnDeviation
      mdp initialState rewardSource varianceProxy hvarianceProxy law initialTable
        defaultState support baseVisitFloor hbaseFloor hrewardBound hhorizon
          hbaseVisitFloor scheduleIndex).integrable le_rfl
  have heq : realizedProcess scheduleIndex =
      behaviorProcess scheduleIndex - returnProcess scheduleIndex := by
    funext trajectory
    exact
      selfConsistentScheduledNaturalCausalStoppingTimeAverageRealizedBehaviorRegretProcess_eq_behaviorExpected_sub_returnDeviation
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor stoppingPrefix scheduleIndex trajectory
  change integral source.trajectoryMeasure (realizedProcess scheduleIndex) =
    integral source.trajectoryMeasure (behaviorProcess scheduleIndex) -
      integral source.trajectoryMeasure (returnProcess scheduleIndex)
  rw [heq]
  exact integral_sub hbehavior hreturn

/-- Exact expected decomposition for the genuine uncapped `hittingAfter`
prefix. -/
theorem
    selfConsistentScheduledNaturalCausalInverseSqrtThresholdUnboundedHittingAfterStoppedAverageRealizedBehaviorRegretIntegral_eq_behaviorExpected_sub_returnDeviation
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
    integral source.trajectoryMeasure (realizedProcess scheduleIndex) =
      integral source.trajectoryMeasure (behaviorProcess scheduleIndex) -
        integral source.trajectoryMeasure (returnProcess scheduleIndex) := by
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
  have hbehavior : Integrable (behaviorProcess scheduleIndex)
      source.trajectoryMeasure :=
    (memLp_one_selfConsistentScheduledNaturalCausalInverseSqrtThresholdUnboundedHittingAfterStoppedBehaviorExpectedRegret
      mdp initialState rewardSource initialTable defaultState varianceProxy
        baseVisitFloor hrewardBound scheduleIndex).integrable le_rfl
  have hreturn : Integrable (returnProcess scheduleIndex)
      source.trajectoryMeasure :=
    (memLp_one_selfConsistentScheduledNaturalCausalInverseSqrtThresholdUnboundedHittingAfterStoppedReturnDeviation
      mdp initialState rewardSource varianceProxy hvarianceProxy law initialTable
        defaultState support baseVisitFloor hbaseFloor hrewardBound hhorizon
          hbaseVisitFloor scheduleIndex).integrable le_rfl
  have heq : realizedProcess scheduleIndex =
      behaviorProcess scheduleIndex - returnProcess scheduleIndex := by
    funext trajectory
    exact
      selfConsistentScheduledNaturalCausalStoppingTimeAverageRealizedBehaviorRegretProcess_eq_behaviorExpected_sub_returnDeviation
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor stoppingPrefix scheduleIndex trajectory
  change integral source.trajectoryMeasure (realizedProcess scheduleIndex) =
    integral source.trajectoryMeasure (behaviorProcess scheduleIndex) -
      integral source.trajectoryMeasure (returnProcess scheduleIndex)
  rw [heq]
  exact integral_sub hbehavior hreturn

/-- Terminal expected semantic replacement package for the capped and genuine
uncapped first-passage prefixes. -/
theorem
    selfConsistentScheduledCausalSource_inverseSqrtThresholdCappedUnboundedHittingAfter_stoppedBehaviorExpectedRegret_and_returnDeviation_expected_truncation_replacement
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
      Integrable (cappedBehavior scheduleIndex) source.trajectoryMeasure /\
        Integrable (uncappedBehavior scheduleIndex) source.trajectoryMeasure /\
        Integrable (cappedRealized scheduleIndex) source.trajectoryMeasure /\
        Integrable (uncappedRealized scheduleIndex) source.trajectoryMeasure /\
        Integrable (cappedReturn scheduleIndex) source.trajectoryMeasure /\
        Integrable (uncappedReturn scheduleIndex) source.trajectoryMeasure) /\
      (forall scheduleIndex,
        integral source.trajectoryMeasure (cappedRealized scheduleIndex) =
            integral source.trajectoryMeasure (cappedBehavior scheduleIndex) -
              integral source.trajectoryMeasure (cappedReturn scheduleIndex) /\
          integral source.trajectoryMeasure (uncappedRealized scheduleIndex) =
            integral source.trajectoryMeasure (uncappedBehavior scheduleIndex) -
              integral source.trajectoryMeasure (uncappedReturn scheduleIndex)) /\
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
          integral source.trajectoryMeasure (uncappedReturn scheduleIndex) -
            integral source.trajectoryMeasure (cappedReturn scheduleIndex))
        atTop (nhds 0) /\
      Tendsto
        (fun scheduleIndex =>
          |integral source.trajectoryMeasure (uncappedReturn scheduleIndex) -
            integral source.trajectoryMeasure (cappedReturn scheduleIndex)|)
        atTop (nhds 0) /\
      (Tendsto
          (fun scheduleIndex =>
            integral source.trajectoryMeasure (cappedBehavior scheduleIndex))
          atTop (nhds 0) /\
        Tendsto
          (fun scheduleIndex =>
            integral source.trajectoryMeasure (uncappedBehavior scheduleIndex))
          atTop (nhds 0) /\
        Tendsto
          (fun scheduleIndex =>
            integral source.trajectoryMeasure (cappedReturn scheduleIndex))
          atTop (nhds 0) /\
        Tendsto
          (fun scheduleIndex =>
            integral source.trajectoryMeasure (uncappedReturn scheduleIndex))
          atTop (nhds 0)) := by
  dsimp only
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
  have hcappedBehavior : forall scheduleIndex,
      Integrable (cappedBehavior scheduleIndex) source.trajectoryMeasure :=
    fun scheduleIndex =>
      (memLp_one_selfConsistentScheduledNaturalCausalInverseSqrtThresholdCappedStoppedBehaviorExpectedRegret
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor hrewardBound scheduleIndex).integrable le_rfl
  have huncappedBehavior : forall scheduleIndex,
      Integrable (uncappedBehavior scheduleIndex) source.trajectoryMeasure :=
    fun scheduleIndex =>
      (memLp_one_selfConsistentScheduledNaturalCausalInverseSqrtThresholdUnboundedHittingAfterStoppedBehaviorExpectedRegret
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor hrewardBound scheduleIndex).integrable le_rfl
  have hcappedRealized : forall scheduleIndex,
      Integrable (cappedRealized scheduleIndex) source.trajectoryMeasure :=
    fun scheduleIndex =>
      (memLp_one_selfConsistentScheduledNaturalCausalInverseSqrtThresholdCappedStoppedAverageRealizedBehaviorRegret
        mdp initialState rewardSource varianceProxy hvarianceProxy law initialTable
          defaultState support baseVisitFloor hbaseFloor hrewardBound
            (lt_trans (by decide : 0 < 4) hhorizon) hbaseVisitFloor
              scheduleIndex).integrable le_rfl
  have huncappedRealized : forall scheduleIndex,
      Integrable (uncappedRealized scheduleIndex) source.trajectoryMeasure :=
    fun scheduleIndex =>
      (memLp_one_selfConsistentScheduledNaturalCausalInverseSqrtThresholdUnboundedHittingAfterStoppedAverageRealizedBehaviorRegret
        mdp initialState rewardSource varianceProxy hvarianceProxy law initialTable
          defaultState support baseVisitFloor hbaseFloor hrewardBound hhorizon
            hbaseVisitFloor scheduleIndex).integrable le_rfl
  have hcappedReturn : forall scheduleIndex,
      Integrable (cappedReturn scheduleIndex) source.trajectoryMeasure :=
    fun scheduleIndex =>
      (memLp_one_selfConsistentScheduledNaturalCausalInverseSqrtThresholdCappedStoppedReturnDeviation
        mdp initialState rewardSource varianceProxy hvarianceProxy law initialTable
          defaultState support baseVisitFloor hbaseFloor hrewardBound hhorizon
            hbaseVisitFloor scheduleIndex).integrable le_rfl
  have huncappedReturn : forall scheduleIndex,
      Integrable (uncappedReturn scheduleIndex) source.trajectoryMeasure :=
    fun scheduleIndex =>
      (memLp_one_selfConsistentScheduledNaturalCausalInverseSqrtThresholdUnboundedHittingAfterStoppedReturnDeviation
        mdp initialState rewardSource varianceProxy hvarianceProxy law initialTable
          defaultState support baseVisitFloor hbaseFloor hrewardBound hhorizon
            hbaseVisitFloor scheduleIndex).integrable le_rfl
  refine ⟨fun scheduleIndex =>
      ⟨hcappedBehavior scheduleIndex, huncappedBehavior scheduleIndex,
        hcappedRealized scheduleIndex, huncappedRealized scheduleIndex,
        hcappedReturn scheduleIndex, huncappedReturn scheduleIndex⟩,
    ?_, ?_, ?_, ?_, ?_, ?_⟩
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
      selfConsistentScheduledNaturalCausalInverseSqrtThresholdCappedUnboundedHittingAfterStoppedReturnDeviationExpectedGap_tendsto_zero
        mdp initialState rewardSource varianceProxy hvarianceProxy law initialTable
          defaultState support baseVisitFloor hbaseFloor hrewardBound hhorizon
            hbaseVisitFloor
  · exact
      selfConsistentScheduledNaturalCausalInverseSqrtThresholdCappedUnboundedHittingAfterStoppedReturnDeviationExpectedGapAbs_tendsto_zero
        mdp initialState rewardSource varianceProxy hvarianceProxy law initialTable
          defaultState support baseVisitFloor hbaseFloor hrewardBound hhorizon
            hbaseVisitFloor
  · exact
      ⟨selfConsistentScheduledNaturalCausalInverseSqrtThresholdCappedStoppedBehaviorExpectedRegretIntegral_tendsto_zero
          mdp initialState rewardSource varianceProxy hvarianceProxy law initialTable
            defaultState support baseVisitFloor hbaseFloor hrewardBound
              (lt_trans (by decide : 0 < 4) hhorizon) hbaseVisitFloor,
        selfConsistentScheduledNaturalCausalInverseSqrtThresholdUnboundedHittingAfterStoppedBehaviorExpectedRegretIntegral_tendsto_zero
          mdp initialState rewardSource varianceProxy hvarianceProxy law initialTable
            defaultState support baseVisitFloor hbaseFloor hrewardBound
              (lt_trans (by decide : 0 < 4) hhorizon) hbaseVisitFloor,
        selfConsistentScheduledNaturalCausalInverseSqrtThresholdCappedStoppedReturnDeviationIntegral_tendsto_zero
          mdp initialState rewardSource varianceProxy hvarianceProxy law initialTable
            defaultState support baseVisitFloor hbaseFloor hrewardBound hhorizon
              hbaseVisitFloor,
        selfConsistentScheduledNaturalCausalInverseSqrtThresholdUnboundedHittingAfterStoppedReturnDeviationIntegral_tendsto_zero
          mdp initialState rewardSource varianceProxy hvarianceProxy law initialTable
            defaultState support baseVisitFloor hbaseFloor hrewardBound hhorizon
              hbaseVisitFloor⟩

end AdaptiveStochasticSampledEmpiricalOptimisticSource

end BanditRLProof.FiniteHorizonRL
