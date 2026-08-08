import BanditRLProof.RL.FiniteHorizonNaturalCausalInverseSqrtThresholdUnboundedHittingAfterUniformAbsoluteContinuity
import BanditRLProof.RL.FiniteHorizonNaturalCausalInverseSqrtThresholdCappedDoubleLinearRawWindowFirstPassageSummableDelayAndEventualImmediateStoppingL1Consistency

/-!
# Delayed-event contribution at the uncapped inverse-sqrt hitting time

This module combines the accepted uniform-integrability interface for the
exact uncapped stopped-regret process with the compiled vanishing probability
of the capped first-passage delayed event. The absolute and signed expected
contributions on that concrete rare event both vanish.
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

/-- A uniformly integrable Real family has vanishing restricted L1 mass on a
measurable sequence of events whose measures tend to zero. -/
theorem tendsto_integral_abs_restrict_of_uniformIntegrable_one_of_measure_tendsto_zero
    {Omega : Type w} [MeasurableSpace Omega] {mu : Measure Omega}
    {f : Nat -> Omega -> Real} {event : Nat -> Set Omega}
    (hui : UniformIntegrable f 1 mu)
    (hevent : forall n, MeasurableSet (event n))
    (hmeasure : Tendsto (fun n => mu (event n)) atTop (nhds 0)) :
    Tendsto
      (fun n =>
        integral (mu.restrict (event n)) (fun omega => |f n omega|))
      atTop (nhds 0) := by
  rw [Metric.tendsto_atTop]
  intro epsilon hepsilon
  obtain ⟨delta, hdelta, hsmall⟩ :=
    integral_abs_restrict_le_of_uniformIntegrable_one hui
      (epsilon / 2) (half_pos hepsilon)
  have hdeltaENNReal : 0 < ENNReal.ofReal delta := ENNReal.ofReal_pos.2 hdelta
  have hmass :
      Filter.Eventually (fun n => mu (event n) < ENNReal.ofReal delta) atTop :=
    hmeasure.eventually (Iio_mem_nhds hdeltaENNReal)
  obtain ⟨N, hN⟩ := eventually_atTop.1 hmass
  refine ⟨N, ?_⟩
  intro n hnN
  have hn := hN n hnN
  have hnonneg :
      0 <= integral (mu.restrict (event n)) (fun omega => |f n omega|) :=
    integral_nonneg (fun _ => abs_nonneg _)
  simpa only [Real.dist_eq, sub_zero, abs_of_nonneg hnonneg] using
    (lt_of_le_of_lt
      (hsmall n (event n) (hevent n) hn.le)
      (half_lt_self hepsilon))

/-- The signed restricted integrals also vanish, by domination with the
restricted integral of the absolute value. -/
theorem tendsto_abs_integral_restrict_of_uniformIntegrable_one_of_measure_tendsto_zero
    {Omega : Type w} [MeasurableSpace Omega] {mu : Measure Omega}
    {f : Nat -> Omega -> Real} {event : Nat -> Set Omega}
    (hui : UniformIntegrable f 1 mu)
    (hevent : forall n, MeasurableSet (event n))
    (hmeasure : Tendsto (fun n => mu (event n)) atTop (nhds 0)) :
    Tendsto
      (fun n => |integral (mu.restrict (event n)) (f n)|)
      atTop (nhds 0) := by
  have habsolute :=
    tendsto_integral_abs_restrict_of_uniformIntegrable_one_of_measure_tendsto_zero
      hui hevent hmeasure
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le'
    tendsto_const_nhds habsolute
    (Filter.Eventually.of_forall fun _ => abs_nonneg _)
    (Filter.Eventually.of_forall fun _ => abs_integral_le_integral_abs)

/-- The existing inverse-square-root delayed event has vanishing expected
contribution for the exact uncapped `hittingAfter` stopped average realized
behavior-regret process. The event comes from the capped first-passage route,
but the integrated process and stopping prefix remain genuinely uncapped. -/
theorem
    selfConsistentScheduledCausalSource_inverseSqrtThresholdUnboundedHittingAfter_delayedEvent_expectedContribution_tendsto_zero
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
    let stoppedProcess :=
      selfConsistentScheduledNaturalCausalStoppingTimeAverageRealizedBehaviorRegretProcess
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor stoppingPrefix
    let delayedSet :=
      selfConsistentScheduledNaturalCausalInverseSqrtThresholdCappedDoubleLinearRawWindowFirstPassageDelayedSet
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor
    (forall scheduleIndex, MeasurableSet (delayedSet scheduleIndex)) /\
      Tendsto
        (fun scheduleIndex => source.trajectoryMeasure (delayedSet scheduleIndex))
        atTop (nhds 0) /\
      Tendsto
        (fun scheduleIndex =>
          integral (source.trajectoryMeasure.restrict (delayedSet scheduleIndex))
            (fun trajectory => |stoppedProcess scheduleIndex trajectory|))
        atTop (nhds 0) /\
      Tendsto
        (fun scheduleIndex =>
          |integral (source.trajectoryMeasure.restrict (delayedSet scheduleIndex))
            (stoppedProcess scheduleIndex)|)
        atTop (nhds 0) := by
  dsimp only
  let source := selfConsistentScheduledCausalSource mdp initialState
    rewardSource initialTable defaultState varianceProxy baseVisitFloor
  let stoppingPrefix :=
    selfConsistentScheduledNaturalCausalInverseSqrtThresholdUnboundedHittingAfterStoppingPrefix
      mdp initialState rewardSource initialTable defaultState varianceProxy
        baseVisitFloor
  let stoppedProcess :=
    selfConsistentScheduledNaturalCausalStoppingTimeAverageRealizedBehaviorRegretProcess
      mdp initialState rewardSource initialTable defaultState varianceProxy
        baseVisitFloor stoppingPrefix
  let delayedSet :=
    selfConsistentScheduledNaturalCausalInverseSqrtThresholdCappedDoubleLinearRawWindowFirstPassageDelayedSet
      mdp initialState rewardSource initialTable defaultState varianceProxy
        baseVisitFloor
  have hevent : forall scheduleIndex, MeasurableSet (delayedSet scheduleIndex) :=
    fun scheduleIndex => by
      simpa only [delayedSet] using
        measurableSet_selfConsistentScheduledNaturalCausalInverseSqrtThresholdCappedDoubleLinearRawWindowFirstPassageDelayedSet
          mdp initialState rewardSource initialTable defaultState varianceProxy
            baseVisitFloor scheduleIndex
  have hmeasure :
      Tendsto
        (fun scheduleIndex => source.trajectoryMeasure (delayedSet scheduleIndex))
        atTop (nhds 0) := by
    simpa only [source, delayedSet,
      selfConsistentScheduledNaturalCausalInverseSqrtThresholdCappedDoubleLinearRawWindowFirstPassageDelayedProbability]
      using
        (selfConsistentScheduledNaturalCausalInverseSqrtThresholdCappedDoubleLinearRawWindowFirstPassageDelayedProbability_tendsto_zero
          mdp initialState rewardSource varianceProxy hvarianceProxy law initialTable
            defaultState support baseVisitFloor hbaseFloor hrewardBound
              (lt_trans (by decide : 0 < 4) hhorizon) hbaseVisitFloor)
  have hui : UniformIntegrable stoppedProcess 1 source.trajectoryMeasure := by
    simpa only [source, stoppingPrefix, stoppedProcess] using
      uniformIntegrable_selfConsistentScheduledNaturalCausalInverseSqrtThresholdUnboundedHittingAfterStoppedAverageRealizedBehaviorRegret
        mdp initialState rewardSource varianceProxy hvarianceProxy law initialTable
          defaultState support baseVisitFloor hbaseFloor hrewardBound hhorizon
            hbaseVisitFloor
  have habsolute :=
    tendsto_integral_abs_restrict_of_uniformIntegrable_one_of_measure_tendsto_zero
      hui hevent hmeasure
  have hsigned :=
    tendsto_abs_integral_restrict_of_uniformIntegrable_one_of_measure_tendsto_zero
      hui hevent hmeasure
  exact ⟨hevent, hmeasure, habsolute, hsigned⟩

end AdaptiveStochasticSampledEmpiricalOptimisticSource

end BanditRLProof.FiniteHorizonRL
