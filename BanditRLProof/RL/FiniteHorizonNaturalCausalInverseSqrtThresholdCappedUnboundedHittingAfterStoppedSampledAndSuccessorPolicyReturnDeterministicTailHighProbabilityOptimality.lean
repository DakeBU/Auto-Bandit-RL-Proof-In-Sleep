import BanditRLProof.RL.FiniteHorizonNaturalCausalInverseSqrtThresholdCappedUnboundedHittingAfterStoppedSampledAndSuccessorPolicyReturnSimultaneousHighProbabilityOptimality

/-!
# Deterministic-tail high-probability stopped-return optimality

This module extracts a deterministic tail start from the qualitative
simultaneous stopped-return probability limit. At every later schedule index,
the complement of the existing six-way violation event has real probability
strictly greater than `1 - delta` and is exactly the event on which all six
literal errors are strictly below `epsilon`.

The tail start is existential and noncomputable. No convergence rate,
independence, or optional-stopping argument is introduced.
-/

open Filter MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal ProbabilityTheory Topology BigOperators

namespace BanditRLProof.FiniteHorizonRL

universe u v w

/-- A strict `ENNReal` upper bound on a measurable bad event gives the
corresponding strict real-probability lower bound on its complement. -/
theorem probReal_compl_gt_one_sub_of_measure_lt_ofReal
    {Omega : Type w} [MeasurableSpace Omega]
    (mu : Measure Omega) [IsProbabilityMeasure mu]
    {event : Set Omega} (hevent : MeasurableSet event)
    {delta : Real} (hdelta : 0 < delta)
    (htail : mu event < ENNReal.ofReal delta) :
    1 - delta < mu.real event.compl := by
  have htailReal : mu.real event < delta := by
    change (mu event).toReal < delta
    have htoReal :
        (mu event).toReal < (ENNReal.ofReal delta).toReal :=
      (ENNReal.toReal_lt_toReal (measure_ne_top mu event)
        ENNReal.ofReal_ne_top).2 htail
    simpa [ENNReal.toReal_ofReal hdelta.le] using htoReal
  change 1 - delta < mu.real (eventᶜ)
  rw [MeasureTheory.probReal_compl_eq_one_sub hevent]
  linarith

variable {State : Type u} {Action : Type v}
    [MeasurableSpace State] [MeasurableSpace Action]
    [Fintype State] [Fintype Action]
    [DecidableEq State] [DecidableEq Action]
    [MeasurableSingletonClass State] [MeasurableSingletonClass Action]
    [Nonempty State] [Nonempty Action]

namespace AdaptiveStochasticSampledEmpiricalOptimisticSource

/-- The simultaneous six-coordinate stopped-return good event is exactly the
complement of the existing joint violation event. -/
noncomputable def
    selfConsistentScheduledNaturalCausalInverseSqrtThresholdCappedUnboundedHittingAfterStoppedReturnJointGoodSet
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
  (selfConsistentScheduledNaturalCausalInverseSqrtThresholdCappedUnboundedHittingAfterStoppedReturnJointViolationSet
    mdp initialState rewardSource initialTable defaultState varianceProxy
      baseVisitFloor epsilon scheduleIndex)ᶜ

/-- The named six-coordinate good event is measurable at every schedule
index. -/
theorem
    measurableSet_selfConsistentScheduledNaturalCausalInverseSqrtThresholdCappedUnboundedHittingAfterStoppedReturnJointGoodSet
    (mdp : MDP State Action) (initialState : Measure State)
    [IsProbabilityMeasure initialState]
    (rewardSource : mdp.MeanCompatibleRewardKernel)
    (initialTable : DeterministicMarkovPolicyTable mdp)
    (defaultState : State) (varianceProxy : NNReal)
    (baseVisitFloor epsilon : Real) (scheduleIndex : Nat) :
    MeasurableSet
      (selfConsistentScheduledNaturalCausalInverseSqrtThresholdCappedUnboundedHittingAfterStoppedReturnJointGoodSet
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor epsilon scheduleIndex) := by
  exact
    (measurableSet_selfConsistentScheduledNaturalCausalInverseSqrtThresholdCappedUnboundedHittingAfterStoppedReturnJointViolationSet
      mdp initialState rewardSource initialTable defaultState varianceProxy
        baseVisitFloor epsilon scheduleIndex).compl

/-- Membership in the named good event is equivalent to all six literal
stopped-return errors being strictly below the same threshold. -/
theorem
    mem_selfConsistentScheduledNaturalCausalInverseSqrtThresholdCappedUnboundedHittingAfterStoppedReturnJointGoodSet_iff
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
    trajectory ∈
        selfConsistentScheduledNaturalCausalInverseSqrtThresholdCappedUnboundedHittingAfterStoppedReturnJointGoodSet
          mdp initialState rewardSource initialTable defaultState varianceProxy
            baseVisitFloor epsilon scheduleIndex ↔
      dist (cappedSampledReturn scheduleIndex trajectory) optimal < epsilon ∧
      dist (uncappedSampledReturn scheduleIndex trajectory) optimal < epsilon ∧
      dist (cappedPolicyReturn scheduleIndex trajectory) optimal < epsilon ∧
      dist (uncappedPolicyReturn scheduleIndex trajectory) optimal < epsilon ∧
      dist (cappedGap scheduleIndex trajectory) 0 < epsilon ∧
      dist (uncappedGap scheduleIndex trajectory) 0 < epsilon := by
  simpa only [
    selfConsistentScheduledNaturalCausalInverseSqrtThresholdCappedUnboundedHittingAfterStoppedReturnJointGoodSet,
    Set.mem_compl_iff] using
    (not_mem_selfConsistentScheduledNaturalCausalInverseSqrtThresholdCappedUnboundedHittingAfterStoppedReturnJointViolationSet_iff
      mdp initialState rewardSource initialTable defaultState varianceProxy
        baseVisitFloor epsilon scheduleIndex trajectory)

/-- A strict mass bound for the named bad event yields the corresponding real
probability lower bound for the named good event. -/
theorem
    selfConsistentScheduledNaturalCausalInverseSqrtThresholdCappedUnboundedHittingAfterStoppedReturnJointGoodSet_probReal_gt_one_sub
    (mdp : MDP State Action) (initialState : Measure State)
    [IsProbabilityMeasure initialState]
    (rewardSource : mdp.MeanCompatibleRewardKernel)
    (initialTable : DeterministicMarkovPolicyTable mdp)
    (defaultState : State) (varianceProxy : NNReal)
    (baseVisitFloor epsilon delta : Real) (scheduleIndex : Nat)
    (hdelta : 0 < delta)
    (htail :
      selfConsistentScheduledNaturalCausalInverseSqrtThresholdCappedUnboundedHittingAfterStoppedReturnJointViolationProbability
          mdp initialState rewardSource initialTable defaultState varianceProxy
            baseVisitFloor epsilon scheduleIndex < ENNReal.ofReal delta) :
    let source :=
      selfConsistentScheduledCausalSource mdp initialState rewardSource
        initialTable defaultState varianceProxy baseVisitFloor
    1 - delta < source.trajectoryMeasure.real
      (selfConsistentScheduledNaturalCausalInverseSqrtThresholdCappedUnboundedHittingAfterStoppedReturnJointGoodSet
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor epsilon scheduleIndex) := by
  let source :=
    selfConsistentScheduledCausalSource mdp initialState rewardSource
      initialTable defaultState varianceProxy baseVisitFloor
  let bad :=
    selfConsistentScheduledNaturalCausalInverseSqrtThresholdCappedUnboundedHittingAfterStoppedReturnJointViolationSet
      mdp initialState rewardSource initialTable defaultState varianceProxy
        baseVisitFloor epsilon scheduleIndex
  have hbadMeasurable : MeasurableSet bad := by
    exact
      measurableSet_selfConsistentScheduledNaturalCausalInverseSqrtThresholdCappedUnboundedHittingAfterStoppedReturnJointViolationSet
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor epsilon scheduleIndex
  have hbadMass : source.trajectoryMeasure bad < ENNReal.ofReal delta := by
    simpa [source, bad,
      selfConsistentScheduledNaturalCausalInverseSqrtThresholdCappedUnboundedHittingAfterStoppedReturnJointViolationProbability] using
      htail
  have hgoodMass :=
    probReal_compl_gt_one_sub_of_measure_lt_ofReal source.trajectoryMeasure
      hbadMeasurable hdelta hbadMass
  simpa [source, bad,
    selfConsistentScheduledNaturalCausalInverseSqrtThresholdCappedUnboundedHittingAfterStoppedReturnJointGoodSet] using
    hgoodMass

/-- The qualitative eventual confidence theorem has one deterministic natural
tail start that controls every later schedule index. -/
theorem
    exists_tailStart_selfConsistentScheduledNaturalCausalInverseSqrtThresholdCappedUnboundedHittingAfterStoppedReturnJointViolationProbability_lt
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
    ∃ tailStart : Nat, ∀ scheduleIndex, tailStart ≤ scheduleIndex →
      selfConsistentScheduledNaturalCausalInverseSqrtThresholdCappedUnboundedHittingAfterStoppedReturnJointViolationProbability
          mdp initialState rewardSource initialTable defaultState varianceProxy
            baseVisitFloor epsilon scheduleIndex < ENNReal.ofReal delta := by
  exact eventually_atTop.1
    (eventually_selfConsistentScheduledNaturalCausalInverseSqrtThresholdCappedUnboundedHittingAfterStoppedReturnJointViolationProbability_lt
      mdp initialState rewardSource varianceProxy hvarianceProxy law initialTable
        defaultState support baseVisitFloor hbaseFloor hrewardBound hhorizon
          hbaseVisitFloor epsilon delta hepsilon hdelta)

/-- Terminal deterministic-tail confidence certificate. One noncomputable
cutoff works for every later schedule index, and the named good event combines
real probability mass with the six literal stopped-return error bounds. -/
theorem
    selfConsistentScheduledCausalSource_inverseSqrtThresholdCappedUnboundedHittingAfter_stoppedSampledReturn_and_successorPolicyExpectedReturn_deterministicTailHighProbability_optimality
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
    ∀ epsilon delta, 0 < epsilon → 0 < delta →
      ∃ tailStart : Nat, ∀ scheduleIndex, tailStart ≤ scheduleIndex →
        let bad :=
          selfConsistentScheduledNaturalCausalInverseSqrtThresholdCappedUnboundedHittingAfterStoppedReturnJointViolationSet
            mdp initialState rewardSource initialTable defaultState varianceProxy
              baseVisitFloor epsilon scheduleIndex
        let good :=
          selfConsistentScheduledNaturalCausalInverseSqrtThresholdCappedUnboundedHittingAfterStoppedReturnJointGoodSet
            mdp initialState rewardSource initialTable defaultState varianceProxy
              baseVisitFloor epsilon scheduleIndex
        MeasurableSet bad ∧
        source.trajectoryMeasure bad < ENNReal.ofReal delta ∧
        1 - delta < source.trajectoryMeasure.real good ∧
        ∀ trajectory, trajectory ∈ good ↔
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
          dist (uncappedGap scheduleIndex trajectory) 0 < epsilon := by
  dsimp only
  intro epsilon delta hepsilon hdelta
  obtain ⟨tailStart, htailStart⟩ :=
    exists_tailStart_selfConsistentScheduledNaturalCausalInverseSqrtThresholdCappedUnboundedHittingAfterStoppedReturnJointViolationProbability_lt
      mdp initialState rewardSource varianceProxy hvarianceProxy law initialTable
        defaultState support baseVisitFloor hbaseFloor hrewardBound hhorizon
          hbaseVisitFloor epsilon delta hepsilon hdelta
  refine ⟨tailStart, ?_⟩
  intro scheduleIndex hscheduleIndex
  have htail := htailStart scheduleIndex hscheduleIndex
  refine ⟨?_, htail, ?_, ?_⟩
  · exact
      measurableSet_selfConsistentScheduledNaturalCausalInverseSqrtThresholdCappedUnboundedHittingAfterStoppedReturnJointViolationSet
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor epsilon scheduleIndex
  · exact
      selfConsistentScheduledNaturalCausalInverseSqrtThresholdCappedUnboundedHittingAfterStoppedReturnJointGoodSet_probReal_gt_one_sub
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor epsilon delta scheduleIndex hdelta htail
  · exact fun trajectory =>
      mem_selfConsistentScheduledNaturalCausalInverseSqrtThresholdCappedUnboundedHittingAfterStoppedReturnJointGoodSet_iff
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor epsilon scheduleIndex trajectory

end AdaptiveStochasticSampledEmpiricalOptimisticSource

end BanditRLProof.FiniteHorizonRL
