import BanditRLProof.RL.FiniteHorizonNaturalCausalInverseSqrtThresholdCappedUnboundedHittingAfterL1TruncationEquivalence
import BanditRLProof.RL.FiniteHorizonNaturalCausalInverseSqrtThresholdUnboundedHittingAfterUniformIntegrabilityExpectedConsistency

/-!
# Expected-regret replacement for capped and uncapped hittingAfter rules

This module transports the accepted capped/uncapped `L1` truncation
equivalence through the Bochner integral. The result compares signed expected
stopped average realized behavior regret on the same generated trajectory law.
It is not an optional-stopping or policy-value identity.
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

namespace AdaptiveStochasticSampledEmpiricalOptimisticSource

/-- Exponent-one norm convergence to zero implies convergence of signed
Bochner integrals to zero. -/
theorem integral_tendsto_zero_of_memLp_one_of_eLpNorm_tendsto_zero
    {Omega : Type w} [MeasurableSpace Omega] {mu : Measure Omega}
    {f : Nat -> Omega -> Real}
    (hf : forall n, MemLp (f n) 1 mu)
    (hnorm : Tendsto (fun n => eLpNorm (f n) 1 mu) atTop (nhds 0)) :
    Tendsto (fun n => integral mu (f n)) atTop (nhds 0) := by
  have hnormZero :
      Tendsto
        (fun n => eLpNorm (f n - (fun _ => 0)) 1 mu)
        atTop (nhds 0) := by
    convert hnorm using 1
    funext n
    apply eLpNorm_congr_ae
    exact Filter.Eventually.of_forall fun omega => by simp
  simpa only [integral_zero] using
    (tendsto_integral_of_L1'
      (fun _ : Omega => (0 : Real))
      (integrable_zero Omega Real mu)
      (Filter.Eventually.of_forall fun n =>
        memLp_one_iff_integrable.mp (hf n))
      hnormZero)

/-- The signed integral of the exact uncapped-minus-capped truncation error
tends to zero. -/
theorem
    selfConsistentScheduledNaturalCausalInverseSqrtThresholdCappedUnboundedHittingAfterStoppedAverageRealizedBehaviorRegretIntegralDifference_tendsto_zero
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
      (fun scheduleIndex => integral source.trajectoryMeasure
        (uncappedProcess scheduleIndex - cappedProcess scheduleIndex))
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
  let cappedProcess :=
    selfConsistentScheduledNaturalCausalStoppingTimeAverageRealizedBehaviorRegretProcess
      mdp initialState rewardSource initialTable defaultState varianceProxy
        baseVisitFloor cappedStoppingPrefix
  let uncappedProcess :=
    selfConsistentScheduledNaturalCausalStoppingTimeAverageRealizedBehaviorRegretProcess
      mdp initialState rewardSource initialTable defaultState varianceProxy
        baseVisitFloor uncappedStoppingPrefix
  have hmem : forall scheduleIndex,
      MemLp (uncappedProcess scheduleIndex - cappedProcess scheduleIndex) 1
        source.trajectoryMeasure := fun scheduleIndex => by
    simpa only [source, cappedStoppingPrefix, uncappedStoppingPrefix,
      cappedProcess, uncappedProcess] using
      (memLp_one_selfConsistentScheduledNaturalCausalInverseSqrtThresholdCappedUnboundedHittingAfterStoppedAverageRealizedBehaviorRegretDifference
        mdp initialState rewardSource varianceProxy hvarianceProxy law initialTable
          defaultState support baseVisitFloor hbaseFloor hrewardBound hhorizon
            hbaseVisitFloor scheduleIndex)
  have hnorm :
      Tendsto
        (fun scheduleIndex => eLpNorm
          (uncappedProcess scheduleIndex - cappedProcess scheduleIndex) 1
            source.trajectoryMeasure)
        atTop (nhds 0) := by
    simpa only [source, cappedStoppingPrefix, uncappedStoppingPrefix,
      cappedProcess, uncappedProcess] using
      (eLpNorm_one_selfConsistentScheduledNaturalCausalInverseSqrtThresholdCappedUnboundedHittingAfterStoppedAverageRealizedBehaviorRegretDifference_tendsto_zero
        mdp initialState rewardSource varianceProxy hvarianceProxy law initialTable
          defaultState support baseVisitFloor hbaseFloor hrewardBound hhorizon
            hbaseVisitFloor)
  exact integral_tendsto_zero_of_memLp_one_of_eLpNorm_tendsto_zero hmem hnorm

/-- The signed difference between the uncapped and capped stopped-process
expectations tends to zero. -/
theorem
    selfConsistentScheduledNaturalCausalInverseSqrtThresholdCappedUnboundedHittingAfterStoppedAverageRealizedBehaviorRegretExpectedGap_tendsto_zero
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
      (fun scheduleIndex =>
        integral source.trajectoryMeasure (uncappedProcess scheduleIndex) -
          integral source.trajectoryMeasure (cappedProcess scheduleIndex))
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
  let cappedProcess :=
    selfConsistentScheduledNaturalCausalStoppingTimeAverageRealizedBehaviorRegretProcess
      mdp initialState rewardSource initialTable defaultState varianceProxy
        baseVisitFloor cappedStoppingPrefix
  let uncappedProcess :=
    selfConsistentScheduledNaturalCausalStoppingTimeAverageRealizedBehaviorRegretProcess
      mdp initialState rewardSource initialTable defaultState varianceProxy
        baseVisitFloor uncappedStoppingPrefix
  have huncapped : forall scheduleIndex,
      Integrable (uncappedProcess scheduleIndex) source.trajectoryMeasure :=
    fun scheduleIndex =>
      (memLp_one_selfConsistentScheduledNaturalCausalInverseSqrtThresholdUnboundedHittingAfterStoppedAverageRealizedBehaviorRegret
        mdp initialState rewardSource varianceProxy hvarianceProxy law initialTable
          defaultState support baseVisitFloor hbaseFloor hrewardBound hhorizon
            hbaseVisitFloor scheduleIndex).integrable le_rfl
  have hcapped : forall scheduleIndex,
      Integrable (cappedProcess scheduleIndex) source.trajectoryMeasure :=
    fun scheduleIndex =>
      (memLp_one_selfConsistentScheduledNaturalCausalInverseSqrtThresholdCappedStoppedAverageRealizedBehaviorRegret
        mdp initialState rewardSource varianceProxy hvarianceProxy law initialTable
          defaultState support baseVisitFloor hbaseFloor hrewardBound
            (lt_trans (by decide : 0 < 4) hhorizon) hbaseVisitFloor
              scheduleIndex).integrable le_rfl
  have hdiff :
      Tendsto
        (fun scheduleIndex => integral source.trajectoryMeasure
          (uncappedProcess scheduleIndex - cappedProcess scheduleIndex))
        atTop (nhds 0) := by
    simpa only [source, cappedStoppingPrefix, uncappedStoppingPrefix,
      cappedProcess, uncappedProcess] using
      (selfConsistentScheduledNaturalCausalInverseSqrtThresholdCappedUnboundedHittingAfterStoppedAverageRealizedBehaviorRegretIntegralDifference_tendsto_zero
        mdp initialState rewardSource varianceProxy hvarianceProxy law initialTable
          defaultState support baseVisitFloor hbaseFloor hrewardBound hhorizon
            hbaseVisitFloor)
  have hfun :
      (fun scheduleIndex => integral source.trajectoryMeasure
        (uncappedProcess scheduleIndex - cappedProcess scheduleIndex)) =
      (fun scheduleIndex =>
        integral source.trajectoryMeasure (uncappedProcess scheduleIndex) -
          integral source.trajectoryMeasure (cappedProcess scheduleIndex)) := by
    funext scheduleIndex
    exact integral_sub (huncapped scheduleIndex) (hcapped scheduleIndex)
  rw [hfun] at hdiff
  simpa only [source, cappedStoppingPrefix, uncappedStoppingPrefix,
    cappedProcess, uncappedProcess] using hdiff

/-- The absolute gap between the uncapped and capped stopped-process
expectations tends to zero. -/
theorem
    selfConsistentScheduledNaturalCausalInverseSqrtThresholdCappedUnboundedHittingAfterStoppedAverageRealizedBehaviorRegretExpectedGapAbs_tendsto_zero
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
      (fun scheduleIndex =>
        |integral source.trajectoryMeasure (uncappedProcess scheduleIndex) -
          integral source.trajectoryMeasure (cappedProcess scheduleIndex)|)
      atTop (nhds 0) := by
  dsimp only
  have hgap :=
    selfConsistentScheduledNaturalCausalInverseSqrtThresholdCappedUnboundedHittingAfterStoppedAverageRealizedBehaviorRegretExpectedGap_tendsto_zero
      mdp initialState rewardSource varianceProxy hvarianceProxy law initialTable
        defaultState support baseVisitFloor hbaseFloor hrewardBound hhorizon
          hbaseVisitFloor
  simpa only [abs_zero] using (continuous_abs.tendsto 0).comp hgap

/-- The capped stopped-process signed expectation tends to zero. -/
theorem
    selfConsistentScheduledNaturalCausalInverseSqrtThresholdCappedStoppedAverageRealizedBehaviorRegretIntegral_tendsto_zero
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
    let cappedProcess :=
      selfConsistentScheduledNaturalCausalStoppingTimeAverageRealizedBehaviorRegretProcess
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor cappedStoppingPrefix
    Tendsto
      (fun scheduleIndex =>
        integral source.trajectoryMeasure (cappedProcess scheduleIndex))
      atTop (nhds 0) := by
  dsimp only
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
  have hmem : forall scheduleIndex,
      MemLp (cappedProcess scheduleIndex) 1 source.trajectoryMeasure :=
    fun scheduleIndex => by
      simpa only [source, cappedStoppingPrefix, cappedProcess] using
        (memLp_one_selfConsistentScheduledNaturalCausalInverseSqrtThresholdCappedStoppedAverageRealizedBehaviorRegret
          mdp initialState rewardSource varianceProxy hvarianceProxy law initialTable
            defaultState support baseVisitFloor hbaseFloor hrewardBound
              (lt_trans (by decide : 0 < 4) hhorizon) hbaseVisitFloor
                scheduleIndex)
  have hnorm :
      Tendsto
        (fun scheduleIndex =>
          eLpNorm (cappedProcess scheduleIndex) 1 source.trajectoryMeasure)
        atTop (nhds 0) := by
    simpa only [source, cappedStoppingPrefix, cappedProcess] using
      (eLpNorm_one_selfConsistentScheduledNaturalCausalInverseSqrtThresholdCappedStoppedAverageRealizedBehaviorRegret_tendsto_zero
        mdp initialState rewardSource varianceProxy hvarianceProxy law initialTable
          defaultState support baseVisitFloor hbaseFloor hrewardBound
            (lt_trans (by decide : 0 < 4) hhorizon) hbaseVisitFloor)
  exact integral_tendsto_zero_of_memLp_one_of_eLpNorm_tendsto_zero hmem hnorm

/- Terminal integrability, exact decomposition, expected-gap, and signed
expectation replacement package. -/
theorem
    selfConsistentScheduledCausalSource_inverseSqrtThresholdCappedUnboundedHittingAfter_stoppedAverageRealizedBehaviorRegret_expected_truncation_replacement
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
    (forall scheduleIndex,
      Integrable (cappedProcess scheduleIndex) source.trajectoryMeasure /\
        Integrable (uncappedProcess scheduleIndex) source.trajectoryMeasure /\
        integral source.trajectoryMeasure
            (uncappedProcess scheduleIndex - cappedProcess scheduleIndex) =
          integral source.trajectoryMeasure (uncappedProcess scheduleIndex) -
            integral source.trajectoryMeasure (cappedProcess scheduleIndex)) /\
      Tendsto
        (fun scheduleIndex => integral source.trajectoryMeasure
          (uncappedProcess scheduleIndex - cappedProcess scheduleIndex))
        atTop (nhds 0) /\
      Tendsto
        (fun scheduleIndex =>
          integral source.trajectoryMeasure (uncappedProcess scheduleIndex) -
            integral source.trajectoryMeasure (cappedProcess scheduleIndex))
        atTop (nhds 0) /\
      Tendsto
        (fun scheduleIndex =>
          |integral source.trajectoryMeasure (uncappedProcess scheduleIndex) -
            integral source.trajectoryMeasure (cappedProcess scheduleIndex)|)
        atTop (nhds 0) /\
      Tendsto
        (fun scheduleIndex =>
          integral source.trajectoryMeasure (cappedProcess scheduleIndex))
        atTop (nhds 0) /\
      Tendsto
        (fun scheduleIndex =>
          integral source.trajectoryMeasure (uncappedProcess scheduleIndex))
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
  let cappedProcess :=
    selfConsistentScheduledNaturalCausalStoppingTimeAverageRealizedBehaviorRegretProcess
      mdp initialState rewardSource initialTable defaultState varianceProxy
        baseVisitFloor cappedStoppingPrefix
  let uncappedProcess :=
    selfConsistentScheduledNaturalCausalStoppingTimeAverageRealizedBehaviorRegretProcess
      mdp initialState rewardSource initialTable defaultState varianceProxy
        baseVisitFloor uncappedStoppingPrefix
  have hcapped : forall scheduleIndex,
      Integrable (cappedProcess scheduleIndex) source.trajectoryMeasure :=
    fun scheduleIndex =>
      (memLp_one_selfConsistentScheduledNaturalCausalInverseSqrtThresholdCappedStoppedAverageRealizedBehaviorRegret
        mdp initialState rewardSource varianceProxy hvarianceProxy law initialTable
          defaultState support baseVisitFloor hbaseFloor hrewardBound
            (lt_trans (by decide : 0 < 4) hhorizon) hbaseVisitFloor
              scheduleIndex).integrable le_rfl
  have huncapped : forall scheduleIndex,
      Integrable (uncappedProcess scheduleIndex) source.trajectoryMeasure :=
    fun scheduleIndex =>
      (memLp_one_selfConsistentScheduledNaturalCausalInverseSqrtThresholdUnboundedHittingAfterStoppedAverageRealizedBehaviorRegret
        mdp initialState rewardSource varianceProxy hvarianceProxy law initialTable
          defaultState support baseVisitFloor hbaseFloor hrewardBound hhorizon
            hbaseVisitFloor scheduleIndex).integrable le_rfl
  refine ⟨fun scheduleIndex =>
      ⟨hcapped scheduleIndex, huncapped scheduleIndex,
        integral_sub (huncapped scheduleIndex) (hcapped scheduleIndex)⟩,
    ?_, ?_, ?_, ?_, ?_⟩
  · exact
      selfConsistentScheduledNaturalCausalInverseSqrtThresholdCappedUnboundedHittingAfterStoppedAverageRealizedBehaviorRegretIntegralDifference_tendsto_zero
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
      selfConsistentScheduledNaturalCausalInverseSqrtThresholdCappedStoppedAverageRealizedBehaviorRegretIntegral_tendsto_zero
        mdp initialState rewardSource varianceProxy hvarianceProxy law initialTable
          defaultState support baseVisitFloor hbaseFloor hrewardBound hhorizon
            hbaseVisitFloor
  · exact
      selfConsistentScheduledNaturalCausalInverseSqrtThresholdUnboundedHittingAfterStoppedAverageRealizedBehaviorRegretIntegral_tendsto_zero
        mdp initialState rewardSource varianceProxy hvarianceProxy law initialTable
          defaultState support baseVisitFloor hbaseFloor hrewardBound hhorizon
            hbaseVisitFloor

end AdaptiveStochasticSampledEmpiricalOptimisticSource

end BanditRLProof.FiniteHorizonRL
