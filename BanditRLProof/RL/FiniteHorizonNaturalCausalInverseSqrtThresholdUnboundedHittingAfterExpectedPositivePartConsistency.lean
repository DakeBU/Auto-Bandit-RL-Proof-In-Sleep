import BanditRLProof.RL.FiniteHorizonNaturalCausalInverseSqrtThresholdUnboundedHittingAfterIntegrableExpectedUpperBound

/-!
# Expected positive-part consistency at an uncapped inverse-sqrt hitting time

The exact stopped average realized behavior regret can be negative. This file
isolates its one-sided excess, proves that its expectation is bounded by the
hit threshold, and sends that threshold to zero. The argument uses the exact
at-hit inequality and finite-measure integration, not optional stopping.
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

/-- Expected positive part of the exact stopped average realized behavior
regret as a function of the threshold schedule index. -/
noncomputable def
    selfConsistentScheduledNaturalCausalInverseSqrtThresholdUnboundedHittingAfterStoppedAverageRealizedBehaviorRegretExpectedPositivePart
    (mdp : MDP State Action) (initialState : Measure State)
    [IsProbabilityMeasure initialState]
    (rewardSource : mdp.MeanCompatibleRewardKernel)
    (initialTable : DeterministicMarkovPolicyTable mdp)
    (defaultState : State) (varianceProxy : NNReal)
    (baseVisitFloor : Real) (scheduleIndex : Nat) : Real :=
  let source := selfConsistentScheduledCausalSource mdp initialState
    rewardSource initialTable defaultState varianceProxy baseVisitFloor
  let stoppingPrefix :=
    selfConsistentScheduledNaturalCausalInverseSqrtThresholdUnboundedHittingAfterStoppingPrefix
      mdp initialState rewardSource initialTable defaultState varianceProxy
        baseVisitFloor
  let stoppedProcess :=
    selfConsistentScheduledNaturalCausalStoppingTimeAverageRealizedBehaviorRegretProcess
      mdp initialState rewardSource initialTable defaultState varianceProxy
        baseVisitFloor stoppingPrefix scheduleIndex
  integral source.trajectoryMeasure
    (fun trajectory => max (stoppedProcess trajectory) 0)

/-- The expected positive part of the exact stopped process is nonnegative. -/
theorem
    selfConsistentScheduledNaturalCausalInverseSqrtThresholdUnboundedHittingAfterStoppedAverageRealizedBehaviorRegretExpectedPositivePart_nonneg
    (mdp : MDP State Action) (initialState : Measure State)
    [IsProbabilityMeasure initialState]
    (rewardSource : mdp.MeanCompatibleRewardKernel)
    (initialTable : DeterministicMarkovPolicyTable mdp)
    (defaultState : State) (varianceProxy : NNReal)
    (baseVisitFloor : Real) (scheduleIndex : Nat) :
    0 <=
      selfConsistentScheduledNaturalCausalInverseSqrtThresholdUnboundedHittingAfterStoppedAverageRealizedBehaviorRegretExpectedPositivePart
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor scheduleIndex := by
  unfold
    selfConsistentScheduledNaturalCausalInverseSqrtThresholdUnboundedHittingAfterStoppedAverageRealizedBehaviorRegretExpectedPositivePart
  apply integral_nonneg
  intro trajectory
  exact le_max_right _ _

/-- At every fixed threshold index, the positive part of the exact stopped
average realized behavior regret is integrable and its expectation is bounded
by the inverse-square-root hit threshold. -/
theorem
    selfConsistentScheduledCausalSource_inverseSqrtThresholdUnboundedHittingAfter_stoppedAverageRealizedBehaviorRegretPositivePart_integrable_and_integral_le_threshold
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
    let stoppedProcess :=
      selfConsistentScheduledNaturalCausalStoppingTimeAverageRealizedBehaviorRegretProcess
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor stoppingPrefix scheduleIndex
    Integrable (fun trajectory => max (stoppedProcess trajectory) 0)
        source.trajectoryMeasure /\
      integral source.trajectoryMeasure
          (fun trajectory => max (stoppedProcess trajectory) 0) <=
        selfConsistentScheduledNaturalCausalInverseSqrtFirstPassageThreshold
          scheduleIndex := by
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
        baseVisitFloor stoppingPrefix scheduleIndex
  have hstoppedIntegrable :
      Integrable stoppedProcess source.trajectoryMeasure := by
    simpa only [source, stoppingPrefix, stoppedProcess] using
      (selfConsistentScheduledCausalSource_inverseSqrtThresholdUnboundedHittingAfter_stoppedAverageRealizedBehaviorRegret_integrable_and_integral_le_threshold
        mdp initialState rewardSource varianceProxy hvarianceProxy law initialTable
          defaultState support baseVisitFloor hbaseFloor hrewardBound hhorizon
            hbaseVisitFloor scheduleIndex).1
  have hstoppedMeasurable : Measurable stoppedProcess := by
    simpa only [stoppedProcess] using
      measurable_selfConsistentScheduledNaturalCausalStoppingTimeAverageRealizedBehaviorRegretProcess
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor stoppingPrefix scheduleIndex
          (selfConsistentScheduledNaturalCausalInverseSqrtThresholdUnboundedHittingAfterStoppingPrefix_isStoppingTime
            mdp initialState rewardSource initialTable defaultState varianceProxy
              baseVisitFloor scheduleIndex)
  have hpositiveIntegrable :
      Integrable (fun trajectory => max (stoppedProcess trajectory) 0)
        source.trajectoryMeasure := by
    refine hstoppedIntegrable.abs.mono'
      ((hstoppedMeasurable.max measurable_const).aestronglyMeasurable) ?_
    filter_upwards with trajectory
    rw [Real.norm_eq_abs, abs_of_nonneg (le_max_right _ _)]
    exact max_le (le_abs_self _) (abs_nonneg _)
  have hstop : BanditRLProof.OFUL.SquareIntegrableFiniteStoppingTime
      source.trajectoryMeasure (stoppingPrefix scheduleIndex) := by
    simpa only [source, stoppingPrefix] using
      selfConsistentScheduledCausalSource_inverseSqrtThresholdUnboundedHittingAfter_squareIntegrableFiniteStoppingTime
        mdp initialState rewardSource varianceProxy hvarianceProxy law initialTable
          defaultState support baseVisitFloor hbaseFloor hrewardBound hhorizon
            hbaseVisitFloor scheduleIndex
  have hpoint : ∀ᵐ trajectory ∂source.trajectoryMeasure,
      max (stoppedProcess trajectory) 0 <=
        selfConsistentScheduledNaturalCausalInverseSqrtFirstPassageThreshold
          scheduleIndex := by
    filter_upwards [hstop.finite_ae] with trajectory hfinite
    apply max_le
    · simpa only [stoppedProcess, stoppingPrefix,
        selfConsistentScheduledNaturalCausalStoppingTimeAverageRealizedBehaviorRegretProcess_apply] using
        selfConsistentScheduledNaturalCausalAverageRealizedBehaviorRegretProcess_untopA_unboundedHittingAfter_le_threshold
          mdp initialState rewardSource initialTable defaultState varianceProxy
            baseVisitFloor scheduleIndex trajectory hfinite
    · exact le_of_lt
        (selfConsistentScheduledNaturalCausalInverseSqrtFirstPassageThreshold_pos
          scheduleIndex)
  refine ⟨hpositiveIntegrable, ?_⟩
  calc
    integral source.trajectoryMeasure
        (fun trajectory => max (stoppedProcess trajectory) 0) <=
      integral source.trajectoryMeasure
        (fun _ =>
          selfConsistentScheduledNaturalCausalInverseSqrtFirstPassageThreshold
            scheduleIndex) :=
      integral_mono_ae hpositiveIntegrable (integrable_const _) hpoint
    _ = selfConsistentScheduledNaturalCausalInverseSqrtFirstPassageThreshold
          scheduleIndex := by simp

/-- The expected positive part of the exact stopped average realized behavior
regret tends to zero with the inverse-square-root threshold schedule. -/
theorem
    selfConsistentScheduledCausalSource_inverseSqrtThresholdUnboundedHittingAfter_stoppedAverageRealizedBehaviorRegretExpectedPositivePart_tendsto_zero
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
      (selfConsistentScheduledNaturalCausalInverseSqrtThresholdUnboundedHittingAfterStoppedAverageRealizedBehaviorRegretExpectedPositivePart
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor)
      atTop (nhds 0) := by
  apply squeeze_zero
  · intro scheduleIndex
    exact
      selfConsistentScheduledNaturalCausalInverseSqrtThresholdUnboundedHittingAfterStoppedAverageRealizedBehaviorRegretExpectedPositivePart_nonneg
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor scheduleIndex
  · intro scheduleIndex
    simpa only
      [selfConsistentScheduledNaturalCausalInverseSqrtThresholdUnboundedHittingAfterStoppedAverageRealizedBehaviorRegretExpectedPositivePart] using
      (selfConsistentScheduledCausalSource_inverseSqrtThresholdUnboundedHittingAfter_stoppedAverageRealizedBehaviorRegretPositivePart_integrable_and_integral_le_threshold
        mdp initialState rewardSource varianceProxy hvarianceProxy law initialTable
          defaultState support baseVisitFloor hbaseFloor hrewardBound hhorizon
            hbaseVisitFloor scheduleIndex).2
  · exact
      selfConsistentScheduledNaturalCausalInverseSqrtFirstPassageThreshold_tendsto_zero

end AdaptiveStochasticSampledEmpiricalOptimisticSource

end BanditRLProof.FiniteHorizonRL
