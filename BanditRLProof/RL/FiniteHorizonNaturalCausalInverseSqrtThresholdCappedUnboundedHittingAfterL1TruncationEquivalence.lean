import BanditRLProof.RL.FiniteHorizonNaturalCausalInverseSqrtThresholdCappedDoubleLinearRawWindowFirstPassageSummableDelayAndEventualImmediateStoppingL1Consistency
import BanditRLProof.RL.FiniteHorizonNaturalCausalInverseSqrtThresholdUnboundedHittingAfterLpConsistency

/-!
# L1 truncation equivalence for capped and uncapped inverse-sqrt first passage

The capped double-linear scan and the genuine uncapped `hittingAfter` rule use
the same deterministic base. Outside the existing capped delayed set, both
rules stop exactly at that base and their stopped regret coordinates agree.
Their difference also converges to zero in `L1`, in the named `Lp Real 1`
space, and in measure.

The capped delayed set is only used as a support certificate for possible
mismatch. It is not identified with an uncapped delayed event.
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

/-- Outside the capped delayed set, the capped and uncapped inverse-square-root
first-passage rules both stop at the common deterministic base, so their
stopped regret coordinates agree pointwise. -/
theorem
    selfConsistentScheduledNaturalCausalInverseSqrtThresholdCappedUnboundedHittingAfterStoppingPrefixes_eq_base_of_not_mem_delayedSet
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
    let cappedStoppingPrefix :=
      selfConsistentScheduledNaturalCausalInverseSqrtThresholdCappedDoubleLinearRawWindowFirstPassageStoppingPrefix
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor
    let uncappedStoppingPrefix :=
      selfConsistentScheduledNaturalCausalInverseSqrtThresholdUnboundedHittingAfterStoppingPrefix
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor
    let cappedProcess :=
      selfConsistentScheduledNaturalCausalStoppingTimeAverageRealizedBehaviorRegretProcess
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor cappedStoppingPrefix
    let uncappedProcess :=
      selfConsistentScheduledNaturalCausalStoppingTimeAverageRealizedBehaviorRegretProcess
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor uncappedStoppingPrefix
    let delayedSet :=
      selfConsistentScheduledNaturalCausalInverseSqrtThresholdCappedDoubleLinearRawWindowFirstPassageDelayedSet
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor
    trajectory ∉ delayedSet scheduleIndex ->
      cappedStoppingPrefix scheduleIndex trajectory =
          (explicitHighProbabilityRounds scheduleIndex : WithTop Nat) /\
        uncappedStoppingPrefix scheduleIndex trajectory =
          (explicitHighProbabilityRounds scheduleIndex : WithTop Nat) /\
        cappedProcess scheduleIndex trajectory =
          uncappedProcess scheduleIndex trajectory := by
  dsimp only
  intro hnotDelay
  have hcappedUpper :
      selfConsistentScheduledNaturalCausalInverseSqrtThresholdCappedDoubleLinearRawWindowFirstPassageStoppingPrefix
          mdp initialState rewardSource initialTable defaultState varianceProxy
            baseVisitFloor scheduleIndex trajectory <=
        (explicitHighProbabilityRounds scheduleIndex : WithTop Nat) := by
    exact not_lt.mp (by
      simpa only [
        selfConsistentScheduledNaturalCausalInverseSqrtThresholdCappedDoubleLinearRawWindowFirstPassageDelayedSet,
        Set.mem_setOf_eq] using hnotDelay)
  have hcapped :
      selfConsistentScheduledNaturalCausalInverseSqrtThresholdCappedDoubleLinearRawWindowFirstPassageStoppingPrefix
          mdp initialState rewardSource initialTable defaultState varianceProxy
            baseVisitFloor scheduleIndex trajectory =
        (explicitHighProbabilityRounds scheduleIndex : WithTop Nat) :=
    le_antisymm hcappedUpper
      (selfConsistentScheduledNaturalCausalCappedDoubleLinearRawWindowFirstPassageStoppingPrefix_lower
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor
            selfConsistentScheduledNaturalCausalInverseSqrtFirstPassageThreshold
              scheduleIndex trajectory)
  have hprocess :
      selfConsistentScheduledNaturalCausalAverageRealizedBehaviorRegretProcess
          mdp initialState rewardSource initialTable defaultState varianceProxy
            baseVisitFloor (explicitHighProbabilityRounds scheduleIndex)
              trajectory <=
        selfConsistentScheduledNaturalCausalInverseSqrtFirstPassageThreshold
          scheduleIndex :=
    le_of_not_gt <| by
      simpa only [
        selfConsistentScheduledNaturalCausalInverseSqrtThresholdCappedDoubleLinearRawWindowFirstPassageDelayedSet_eq,
        Set.mem_setOf_eq] using hnotDelay
  have huncapped :=
    selfConsistentScheduledNaturalCausalInverseSqrtThresholdUnboundedHittingAfterStoppingPrefix_eq_base_of_process_le
      mdp initialState rewardSource initialTable defaultState varianceProxy
        baseVisitFloor scheduleIndex trajectory hprocess
  refine ⟨hcapped, huncapped, ?_⟩
  simp only [
    selfConsistentScheduledNaturalCausalStoppingTimeAverageRealizedBehaviorRegretProcess_apply,
    hcapped, huncapped]

/-- Almost every trajectory eventually sees exact equality between the capped
and uncapped stopped processes. This follows from summable avoidance of the
capped delayed set and the pointwise support theorem above. -/
theorem
    ae_eventually_selfConsistentScheduledNaturalCausalInverseSqrtThresholdCappedStoppedAverageRealizedBehaviorRegret_eq_unboundedHittingAfter
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
    let uncappedStoppingPrefix :=
      selfConsistentScheduledNaturalCausalInverseSqrtThresholdUnboundedHittingAfterStoppingPrefix
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor
    let cappedProcess :=
      selfConsistentScheduledNaturalCausalStoppingTimeAverageRealizedBehaviorRegretProcess
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor cappedStoppingPrefix
    let uncappedProcess :=
      selfConsistentScheduledNaturalCausalStoppingTimeAverageRealizedBehaviorRegretProcess
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor uncappedStoppingPrefix
    ∀ᵐ trajectory ∂source.trajectoryMeasure,
      ∀ᶠ scheduleIndex in atTop,
        cappedProcess scheduleIndex trajectory =
          uncappedProcess scheduleIndex trajectory := by
  dsimp only
  have hnotDelay :=
    ae_eventually_not_mem_selfConsistentScheduledNaturalCausalInverseSqrtThresholdCappedDoubleLinearRawWindowFirstPassageDelayedSet
      mdp initialState rewardSource varianceProxy hvarianceProxy law initialTable
        defaultState support baseVisitFloor hbaseFloor hrewardBound hhorizon
          hbaseVisitFloor
  filter_upwards [hnotDelay] with trajectory htrajectory
  filter_upwards [htrajectory] with scheduleIndex hnot
  exact
    (selfConsistentScheduledNaturalCausalInverseSqrtThresholdCappedUnboundedHittingAfterStoppingPrefixes_eq_base_of_not_mem_delayedSet
      mdp initialState rewardSource initialTable defaultState varianceProxy
        baseVisitFloor scheduleIndex trajectory hnot).2.2

/-- Every coordinate of the exact capped inverse-square-root stopped process
belongs to `L1`. -/
theorem
    memLp_one_selfConsistentScheduledNaturalCausalInverseSqrtThresholdCappedStoppedAverageRealizedBehaviorRegret
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
    let stoppedProcess :=
      selfConsistentScheduledNaturalCausalStoppingTimeAverageRealizedBehaviorRegretProcess
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor stoppingPrefix
    MemLp (stoppedProcess scheduleIndex) 1 source.trajectoryMeasure := by
  dsimp only
  have hparent :=
    selfConsistentScheduledCausalSource_cappedDoubleLinearRawWindowFirstPassageStoppingTimeNaturalAverageRealizedBehaviorRegret_L1_consistency
      mdp initialState rewardSource varianceProxy hvarianceProxy law initialTable
        defaultState support baseVisitFloor hbaseFloor hrewardBound hhorizon
          hbaseVisitFloor
            selfConsistentScheduledNaturalCausalInverseSqrtFirstPassageThreshold
  rcases hparent with ⟨_, _, _, hmem, _, _, _, _, _, _, _⟩
  simpa only [
    selfConsistentScheduledNaturalCausalInverseSqrtThresholdCappedDoubleLinearRawWindowFirstPassageStoppingPrefix]
    using hmem scheduleIndex

/-- The exponent-one norm of the exact capped inverse-square-root stopped
process tends to zero. -/
theorem
    eLpNorm_one_selfConsistentScheduledNaturalCausalInverseSqrtThresholdCappedStoppedAverageRealizedBehaviorRegret_tendsto_zero
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
    let stoppedProcess :=
      selfConsistentScheduledNaturalCausalStoppingTimeAverageRealizedBehaviorRegretProcess
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor stoppingPrefix
    Tendsto
      (fun scheduleIndex =>
        eLpNorm (stoppedProcess scheduleIndex) 1 source.trajectoryMeasure)
      atTop (nhds 0) := by
  dsimp only
  have hparent :=
    selfConsistentScheduledCausalSource_cappedDoubleLinearRawWindowFirstPassageStoppingTimeNaturalAverageRealizedBehaviorRegret_L1_consistency
      mdp initialState rewardSource varianceProxy hvarianceProxy law initialTable
        defaultState support baseVisitFloor hbaseFloor hrewardBound hhorizon
          hbaseVisitFloor
            selfConsistentScheduledNaturalCausalInverseSqrtFirstPassageThreshold
  rcases hparent with ⟨_, _, _, _, _, _, _, _, hnorm, _, _⟩
  have hnorm' :
      Tendsto
        (fun scheduleIndex => eLpNorm
          (selfConsistentScheduledNaturalCausalStoppingTimeAverageRealizedBehaviorRegretProcess
              mdp initialState rewardSource initialTable defaultState varianceProxy
                baseVisitFloor
                  (selfConsistentScheduledNaturalCausalInverseSqrtThresholdCappedDoubleLinearRawWindowFirstPassageStoppingPrefix
                    mdp initialState rewardSource initialTable defaultState
                      varianceProxy baseVisitFloor)
                    scheduleIndex -
            (fun _ => 0))
          1
          (selfConsistentScheduledCausalSource mdp initialState rewardSource
            initialTable defaultState varianceProxy baseVisitFloor).trajectoryMeasure)
        atTop (nhds 0) := by
    simpa only [
      selfConsistentScheduledNaturalCausalInverseSqrtThresholdCappedDoubleLinearRawWindowFirstPassageStoppingPrefix]
      using hnorm
  convert hnorm' using 1
  funext scheduleIndex
  apply eLpNorm_congr_ae
  exact Filter.Eventually.of_forall fun trajectory => by simp

/-- Each uncapped-minus-capped stopped-process coordinate belongs to `L1`. -/
theorem
    memLp_one_selfConsistentScheduledNaturalCausalInverseSqrtThresholdCappedUnboundedHittingAfterStoppedAverageRealizedBehaviorRegretDifference
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
    let cappedStoppingPrefix :=
      selfConsistentScheduledNaturalCausalInverseSqrtThresholdCappedDoubleLinearRawWindowFirstPassageStoppingPrefix
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor
    let uncappedStoppingPrefix :=
      selfConsistentScheduledNaturalCausalInverseSqrtThresholdUnboundedHittingAfterStoppingPrefix
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor
    let cappedProcess :=
      selfConsistentScheduledNaturalCausalStoppingTimeAverageRealizedBehaviorRegretProcess
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor cappedStoppingPrefix
    let uncappedProcess :=
      selfConsistentScheduledNaturalCausalStoppingTimeAverageRealizedBehaviorRegretProcess
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor uncappedStoppingPrefix
    MemLp (uncappedProcess scheduleIndex - cappedProcess scheduleIndex) 1
      source.trajectoryMeasure := by
  dsimp only
  exact
    (memLp_one_selfConsistentScheduledNaturalCausalInverseSqrtThresholdUnboundedHittingAfterStoppedAverageRealizedBehaviorRegret
      mdp initialState rewardSource varianceProxy hvarianceProxy law initialTable
        defaultState support baseVisitFloor hbaseFloor hrewardBound hhorizon
          hbaseVisitFloor scheduleIndex).sub
      (memLp_one_selfConsistentScheduledNaturalCausalInverseSqrtThresholdCappedStoppedAverageRealizedBehaviorRegret
        mdp initialState rewardSource varianceProxy hvarianceProxy law initialTable
          defaultState support baseVisitFloor hbaseFloor hrewardBound
            (lt_trans (by decide : 0 < 4) hhorizon) hbaseVisitFloor scheduleIndex)

/-- The `L1` norm of the uncapped-minus-capped truncation error tends to zero. -/
theorem
    eLpNorm_one_selfConsistentScheduledNaturalCausalInverseSqrtThresholdCappedUnboundedHittingAfterStoppedAverageRealizedBehaviorRegretDifference_tendsto_zero
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
    let cappedProcess :=
      selfConsistentScheduledNaturalCausalStoppingTimeAverageRealizedBehaviorRegretProcess
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor cappedStoppingPrefix
    let uncappedProcess :=
      selfConsistentScheduledNaturalCausalStoppingTimeAverageRealizedBehaviorRegretProcess
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor uncappedStoppingPrefix
    Tendsto
      (fun scheduleIndex => eLpNorm
        (uncappedProcess scheduleIndex - cappedProcess scheduleIndex) 1
          source.trajectoryMeasure)
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
  let cappedProcess :=
    selfConsistentScheduledNaturalCausalStoppingTimeAverageRealizedBehaviorRegretProcess
      mdp initialState rewardSource initialTable defaultState varianceProxy
        baseVisitFloor cappedStoppingPrefix
  let uncappedProcess :=
    selfConsistentScheduledNaturalCausalStoppingTimeAverageRealizedBehaviorRegretProcess
      mdp initialState rewardSource initialTable defaultState varianceProxy
        baseVisitFloor uncappedStoppingPrefix
  have huncappedNorm :
      Tendsto
        (fun scheduleIndex =>
          eLpNorm (uncappedProcess scheduleIndex) 1 source.trajectoryMeasure)
        atTop (nhds 0) := by
    simpa only [source, uncappedStoppingPrefix, uncappedProcess] using
      (eLpNorm_one_selfConsistentScheduledNaturalCausalInverseSqrtThresholdUnboundedHittingAfterStoppedAverageRealizedBehaviorRegret_tendsto_zero
        mdp initialState rewardSource varianceProxy hvarianceProxy law initialTable
          defaultState support baseVisitFloor hbaseFloor hrewardBound hhorizon
            hbaseVisitFloor)
  have hcappedNorm :
      Tendsto
        (fun scheduleIndex =>
          eLpNorm (cappedProcess scheduleIndex) 1 source.trajectoryMeasure)
        atTop (nhds 0) := by
    simpa only [source, cappedStoppingPrefix, cappedProcess] using
      (eLpNorm_one_selfConsistentScheduledNaturalCausalInverseSqrtThresholdCappedStoppedAverageRealizedBehaviorRegret_tendsto_zero
        mdp initialState rewardSource varianceProxy hvarianceProxy law initialTable
          defaultState support baseVisitFloor hbaseFloor hrewardBound
            (lt_trans (by decide : 0 < 4) hhorizon) hbaseVisitFloor)
  have hsum :
      Tendsto
        (fun scheduleIndex =>
          eLpNorm (uncappedProcess scheduleIndex) 1 source.trajectoryMeasure +
            eLpNorm (cappedProcess scheduleIndex) 1 source.trajectoryMeasure)
        atTop (nhds 0) := by
    simpa only [zero_add] using huncappedNorm.add hcappedNorm
  have huncappedMem : forall scheduleIndex,
      MemLp (uncappedProcess scheduleIndex) 1 source.trajectoryMeasure :=
    fun scheduleIndex => by
      simpa only [source, uncappedStoppingPrefix, uncappedProcess] using
        (memLp_one_selfConsistentScheduledNaturalCausalInverseSqrtThresholdUnboundedHittingAfterStoppedAverageRealizedBehaviorRegret
          mdp initialState rewardSource varianceProxy hvarianceProxy law initialTable
            defaultState support baseVisitFloor hbaseFloor hrewardBound hhorizon
              hbaseVisitFloor scheduleIndex)
  have hcappedMem : forall scheduleIndex,
      MemLp (cappedProcess scheduleIndex) 1 source.trajectoryMeasure :=
    fun scheduleIndex => by
      simpa only [source, cappedStoppingPrefix, cappedProcess] using
        (memLp_one_selfConsistentScheduledNaturalCausalInverseSqrtThresholdCappedStoppedAverageRealizedBehaviorRegret
          mdp initialState rewardSource varianceProxy hvarianceProxy law initialTable
            defaultState support baseVisitFloor hbaseFloor hrewardBound
              (lt_trans (by decide : 0 < 4) hhorizon) hbaseVisitFloor scheduleIndex)
  have hdiff :
      Tendsto
        (fun scheduleIndex => eLpNorm
          (uncappedProcess scheduleIndex - cappedProcess scheduleIndex) 1
            source.trajectoryMeasure)
        atTop (nhds 0) := by
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le'
      tendsto_const_nhds hsum
      (Filter.Eventually.of_forall fun _ => bot_le)
      (Filter.Eventually.of_forall fun scheduleIndex =>
        eLpNorm_sub_le
          (huncappedMem scheduleIndex).aestronglyMeasurable
          (hcappedMem scheduleIndex).aestronglyMeasurable (by norm_num))
  simpa only [source, cappedStoppingPrefix, uncappedStoppingPrefix,
    cappedProcess, uncappedProcess] using hdiff

/-- The uncapped-minus-capped stopped truncation error as an `Lp Real 1`
value. -/
noncomputable def
    selfConsistentScheduledNaturalCausalInverseSqrtThresholdCappedUnboundedHittingAfterStoppedAverageRealizedBehaviorRegretDifferenceLp
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
    Lp Real 1
      (selfConsistentScheduledCausalSource mdp initialState rewardSource
        initialTable defaultState varianceProxy baseVisitFloor).trajectoryMeasure :=
  let cappedStoppingPrefix :=
    selfConsistentScheduledNaturalCausalInverseSqrtThresholdCappedDoubleLinearRawWindowFirstPassageStoppingPrefix
      mdp initialState rewardSource initialTable defaultState varianceProxy
        baseVisitFloor
  let uncappedStoppingPrefix :=
    selfConsistentScheduledNaturalCausalInverseSqrtThresholdUnboundedHittingAfterStoppingPrefix
      mdp initialState rewardSource initialTable defaultState varianceProxy
        baseVisitFloor
  let cappedProcess :=
    selfConsistentScheduledNaturalCausalStoppingTimeAverageRealizedBehaviorRegretProcess
      mdp initialState rewardSource initialTable defaultState varianceProxy
        baseVisitFloor cappedStoppingPrefix scheduleIndex
  let uncappedProcess :=
    selfConsistentScheduledNaturalCausalStoppingTimeAverageRealizedBehaviorRegretProcess
      mdp initialState rewardSource initialTable defaultState varianceProxy
        baseVisitFloor uncappedStoppingPrefix scheduleIndex
  (memLp_one_selfConsistentScheduledNaturalCausalInverseSqrtThresholdCappedUnboundedHittingAfterStoppedAverageRealizedBehaviorRegretDifference
    mdp initialState rewardSource varianceProxy hvarianceProxy law initialTable
      defaultState support baseVisitFloor hbaseFloor hrewardBound hhorizon
        hbaseVisitFloor scheduleIndex).toLp (uncappedProcess - cappedProcess)

/-- The named capped/uncapped truncation error converges to zero in
`Lp Real 1`. -/
theorem
    selfConsistentScheduledNaturalCausalInverseSqrtThresholdCappedUnboundedHittingAfterStoppedAverageRealizedBehaviorRegretDifferenceLp_tendsto_zero
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
    Tendsto
      (selfConsistentScheduledNaturalCausalInverseSqrtThresholdCappedUnboundedHittingAfterStoppedAverageRealizedBehaviorRegretDifferenceLp
        mdp initialState rewardSource varianceProxy hvarianceProxy law initialTable
          defaultState support baseVisitFloor hbaseFloor hrewardBound hhorizon
            hbaseVisitFloor)
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
  let difference := fun scheduleIndex =>
    selfConsistentScheduledNaturalCausalStoppingTimeAverageRealizedBehaviorRegretProcess
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor uncappedStoppingPrefix scheduleIndex -
      selfConsistentScheduledNaturalCausalStoppingTimeAverageRealizedBehaviorRegretProcess
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor cappedStoppingPrefix scheduleIndex
  have hmem : forall scheduleIndex,
      MemLp (difference scheduleIndex) 1 source.trajectoryMeasure :=
    fun scheduleIndex => by
      simpa only [source, cappedStoppingPrefix, uncappedStoppingPrefix,
        difference] using
        (memLp_one_selfConsistentScheduledNaturalCausalInverseSqrtThresholdCappedUnboundedHittingAfterStoppedAverageRealizedBehaviorRegretDifference
          mdp initialState rewardSource varianceProxy hvarianceProxy law initialTable
            defaultState support baseVisitFloor hbaseFloor hrewardBound hhorizon
              hbaseVisitFloor scheduleIndex)
  have hzero : MemLp
      (fun _ : HeterogeneousStochasticEpisodeBatchTrajectory mdp
        (fun t =>
          AdaptiveStochasticEpisodeBatchSource.selfConsistentScheduledEpisodes
            mdp varianceProxy baseVisitFloor t) => (0 : Real))
      1 source.trajectoryMeasure := MemLp.zero'
  have hnorm :=
    eLpNorm_one_selfConsistentScheduledNaturalCausalInverseSqrtThresholdCappedUnboundedHittingAfterStoppedAverageRealizedBehaviorRegretDifference_tendsto_zero
      mdp initialState rewardSource varianceProxy hvarianceProxy law initialTable
        defaultState support baseVisitFloor hbaseFloor hrewardBound hhorizon
          hbaseVisitFloor
  have hnormZero :
      Tendsto
        (fun scheduleIndex => eLpNorm
          (difference scheduleIndex - (fun _ => 0)) 1
            source.trajectoryMeasure)
        atTop (nhds 0) := by
    have hnorm' :
        Tendsto
          (fun scheduleIndex =>
            eLpNorm (difference scheduleIndex) 1 source.trajectoryMeasure)
          atTop (nhds 0) := by
      simpa only [source, cappedStoppingPrefix, uncappedStoppingPrefix,
        difference] using hnorm
    convert hnorm' using 1
    funext scheduleIndex
    apply eLpNorm_congr_ae
    exact Filter.Eventually.of_forall fun trajectory => by simp
  have hLp :=
    (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' difference hmem (fun _ => (0 : Real))
      hzero).2 hnormZero
  simpa [
    selfConsistentScheduledNaturalCausalInverseSqrtThresholdCappedUnboundedHittingAfterStoppedAverageRealizedBehaviorRegretDifferenceLp,
    difference, cappedStoppingPrefix, uncappedStoppingPrefix, source] using hLp

/-- The raw truncation-error representatives converge to zero in measure. -/
theorem
    selfConsistentScheduledNaturalCausalInverseSqrtThresholdCappedUnboundedHittingAfterStoppedAverageRealizedBehaviorRegretDifference_tendstoInMeasure_zero
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
    let difference := fun scheduleIndex =>
      selfConsistentScheduledNaturalCausalStoppingTimeAverageRealizedBehaviorRegretProcess
          mdp initialState rewardSource initialTable defaultState varianceProxy
            baseVisitFloor uncappedStoppingPrefix scheduleIndex -
        selfConsistentScheduledNaturalCausalStoppingTimeAverageRealizedBehaviorRegretProcess
          mdp initialState rewardSource initialTable defaultState varianceProxy
            baseVisitFloor cappedStoppingPrefix scheduleIndex
    TendstoInMeasure source.trajectoryMeasure difference atTop (fun _ => 0) := by
  dsimp only
  apply tendstoInMeasure_of_tendsto_eLpNorm one_ne_zero
  · intro scheduleIndex
    exact
      (memLp_one_selfConsistentScheduledNaturalCausalInverseSqrtThresholdCappedUnboundedHittingAfterStoppedAverageRealizedBehaviorRegretDifference
        mdp initialState rewardSource varianceProxy hvarianceProxy law initialTable
          defaultState support baseVisitFloor hbaseFloor hrewardBound hhorizon
            hbaseVisitFloor scheduleIndex).aestronglyMeasurable
  · have hzero : MemLp
        (fun _ : HeterogeneousStochasticEpisodeBatchTrajectory mdp
          (fun t =>
            AdaptiveStochasticEpisodeBatchSource.selfConsistentScheduledEpisodes
              mdp varianceProxy baseVisitFloor t) => (0 : Real))
        1
        (selfConsistentScheduledCausalSource mdp initialState rewardSource
          initialTable defaultState varianceProxy baseVisitFloor).trajectoryMeasure :=
      MemLp.zero'
    exact hzero.aestronglyMeasurable
  · have hnorm :=
      eLpNorm_one_selfConsistentScheduledNaturalCausalInverseSqrtThresholdCappedUnboundedHittingAfterStoppedAverageRealizedBehaviorRegretDifference_tendsto_zero
        mdp initialState rewardSource varianceProxy hvarianceProxy law initialTable
          defaultState support baseVisitFloor hbaseFloor hrewardBound hhorizon
            hbaseVisitFloor
    convert hnorm using 1
    funext scheduleIndex
    apply eLpNorm_congr_ae
    exact Filter.Eventually.of_forall fun trajectory => by simp

/- Terminal pointwise, almost-everywhere, L1, Lp, and in-measure truncation
equivalence package. -/
theorem
    selfConsistentScheduledCausalSource_inverseSqrtThresholdCappedUnboundedHittingAfter_stoppedAverageRealizedBehaviorRegret_L1_truncation_equivalence
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
    let cappedProcess :=
      selfConsistentScheduledNaturalCausalStoppingTimeAverageRealizedBehaviorRegretProcess
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor cappedStoppingPrefix
    let uncappedProcess :=
      selfConsistentScheduledNaturalCausalStoppingTimeAverageRealizedBehaviorRegretProcess
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor uncappedStoppingPrefix
    let delayedSet :=
      selfConsistentScheduledNaturalCausalInverseSqrtThresholdCappedDoubleLinearRawWindowFirstPassageDelayedSet
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor
    (forall scheduleIndex trajectory,
      trajectory ∉ delayedSet scheduleIndex ->
        cappedStoppingPrefix scheduleIndex trajectory =
            (explicitHighProbabilityRounds scheduleIndex : WithTop Nat) /\
          uncappedStoppingPrefix scheduleIndex trajectory =
            (explicitHighProbabilityRounds scheduleIndex : WithTop Nat) /\
          cappedProcess scheduleIndex trajectory =
            uncappedProcess scheduleIndex trajectory) /\
      (∀ᵐ trajectory ∂source.trajectoryMeasure,
        ∀ᶠ scheduleIndex in atTop,
          cappedProcess scheduleIndex trajectory =
            uncappedProcess scheduleIndex trajectory) /\
      (forall scheduleIndex,
        MemLp (uncappedProcess scheduleIndex - cappedProcess scheduleIndex) 1
          source.trajectoryMeasure) /\
      Tendsto
        (fun scheduleIndex => eLpNorm
          (uncappedProcess scheduleIndex - cappedProcess scheduleIndex) 1
            source.trajectoryMeasure)
        atTop (nhds 0) /\
      Tendsto
        (selfConsistentScheduledNaturalCausalInverseSqrtThresholdCappedUnboundedHittingAfterStoppedAverageRealizedBehaviorRegretDifferenceLp
          mdp initialState rewardSource varianceProxy hvarianceProxy law
            initialTable defaultState support baseVisitFloor hbaseFloor
              hrewardBound hhorizon hbaseVisitFloor)
        atTop (nhds 0) /\
      TendstoInMeasure source.trajectoryMeasure
        (fun scheduleIndex =>
          uncappedProcess scheduleIndex - cappedProcess scheduleIndex)
        atTop (fun _ => 0) := by
  dsimp only
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact fun scheduleIndex trajectory hnot =>
      selfConsistentScheduledNaturalCausalInverseSqrtThresholdCappedUnboundedHittingAfterStoppingPrefixes_eq_base_of_not_mem_delayedSet
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor scheduleIndex trajectory hnot
  · exact
      ae_eventually_selfConsistentScheduledNaturalCausalInverseSqrtThresholdCappedStoppedAverageRealizedBehaviorRegret_eq_unboundedHittingAfter
        mdp initialState rewardSource varianceProxy hvarianceProxy law initialTable
          defaultState support baseVisitFloor hbaseFloor hrewardBound
            (lt_trans (by decide : 0 < 4) hhorizon) hbaseVisitFloor
  · exact fun scheduleIndex =>
      memLp_one_selfConsistentScheduledNaturalCausalInverseSqrtThresholdCappedUnboundedHittingAfterStoppedAverageRealizedBehaviorRegretDifference
        mdp initialState rewardSource varianceProxy hvarianceProxy law initialTable
          defaultState support baseVisitFloor hbaseFloor hrewardBound hhorizon
            hbaseVisitFloor scheduleIndex
  · exact
      eLpNorm_one_selfConsistentScheduledNaturalCausalInverseSqrtThresholdCappedUnboundedHittingAfterStoppedAverageRealizedBehaviorRegretDifference_tendsto_zero
        mdp initialState rewardSource varianceProxy hvarianceProxy law initialTable
          defaultState support baseVisitFloor hbaseFloor hrewardBound hhorizon
            hbaseVisitFloor
  · exact
      selfConsistentScheduledNaturalCausalInverseSqrtThresholdCappedUnboundedHittingAfterStoppedAverageRealizedBehaviorRegretDifferenceLp_tendsto_zero
        mdp initialState rewardSource varianceProxy hvarianceProxy law initialTable
          defaultState support baseVisitFloor hbaseFloor hrewardBound hhorizon
            hbaseVisitFloor
  · exact
      selfConsistentScheduledNaturalCausalInverseSqrtThresholdCappedUnboundedHittingAfterStoppedAverageRealizedBehaviorRegretDifference_tendstoInMeasure_zero
        mdp initialState rewardSource varianceProxy hvarianceProxy law initialTable
          defaultState support baseVisitFloor hbaseFloor hrewardBound hhorizon
            hbaseVisitFloor

end AdaptiveStochasticSampledEmpiricalOptimisticSource

end BanditRLProof.FiniteHorizonRL
