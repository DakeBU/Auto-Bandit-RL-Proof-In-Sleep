import BanditRLProof.RL.FiniteHorizonNaturalCausalBehaviorExpectedRegretLogRate

/-!
# Fixed-prefix high-probability logarithmic behavior expected regret

This module upgrades the natural-prefix pathwise process to a fixed-prefix
high-probability statement on the genuine heterogeneous dependent causal
source.  The probability is inherited from the existing finite union of
selected count-and-reward empirical-model events; no new independence, MGF,
or concentration claim is introduced here.

Outside the named model event, every actual exploratory successor policy is
bounded by the compiled causal planning rate.  Summing those coordinate bounds
and reusing the explicit finite-sum logarithmic envelope yields a measurable
one-sided violation event whose probability is at most the exact accumulated
model-confidence budget.

Regularity: the probabilistic consumer retains finite nonempty Standard Borel
State/Action, a probability initial law, positive reward proxy, horizon, and
base visit floor, bounded mean rewards, uniform mean-compatible selected-reward
sub-Gaussianity, and exploratory path support.  Failure policy preserves the
actual exploratory behavior, one dependent source, actual sampled batches,
the natural `t` to successor-batch `t + 1` convention, scheduled budgets, and
behavior/recommendation separation.  This is fixed-prefix control of a random
behavior expected-regret process, not an anytime theorem or realized-return
regret.
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

/-- Natural-prefix sum of the causal planning-rate coordinates. -/
noncomputable def selfConsistentScheduledNaturalCausalCumulativePlanningRate
    (mdp : MDP State Action) (rounds : Nat) : Real :=
  (Finset.range rounds).sum fun t =>
    selfConsistentScheduledCausalPlanningRateAt mdp t

omit [DecidableEq State] [DecidableEq Action]
    [MeasurableSingletonClass State] [MeasurableSingletonClass Action]
    [Nonempty State] [Nonempty Action] in
/-- The pathwise planning sum is dominated by the integrated finite-prefix sum. -/
theorem selfConsistentScheduledNaturalCausalCumulativePlanningRate_le_integrated
    (mdp : MDP State Action) (rounds : Nat) :
    selfConsistentScheduledNaturalCausalCumulativePlanningRate mdp rounds <=
      selfConsistentScheduledNaturalCausalCumulativeIntegratedBehaviorExpectedRegretRate
        mdp rounds := by
  unfold selfConsistentScheduledNaturalCausalCumulativePlanningRate
    selfConsistentScheduledNaturalCausalCumulativeIntegratedBehaviorExpectedRegretRate
  apply Finset.sum_le_sum
  intro t _ht
  unfold selfConsistentScheduledNaturalCausalIntegratedBehaviorExpectedRegretRateAt
  apply le_add_of_nonneg_right
  rw [selfConsistentScheduledLocalDelta_eq_inv_pow]
  positivity

omit [DecidableEq State] [DecidableEq Action]
    [MeasurableSingletonClass State] [MeasurableSingletonClass Action]
    [Nonempty State] [Nonempty Action] in
/-- The natural-prefix planning sum has the existing explicit logarithmic envelope. -/
theorem selfConsistentScheduledNaturalCausalCumulativePlanningRate_le_logarithmic
    (mdp : MDP State Action) (rounds : Nat) :
    selfConsistentScheduledNaturalCausalCumulativePlanningRate mdp rounds <=
      selfConsistentScheduledNaturalCausalLogarithmicCumulativeIntegratedBehaviorExpectedRegretRate
        mdp rounds :=
  (selfConsistentScheduledNaturalCausalCumulativePlanningRate_le_integrated
    mdp rounds).trans
      (selfConsistentScheduledNaturalCausalCumulativeIntegratedBehaviorExpectedRegretRate_le_logarithmic
        mdp rounds)

omit [DecidableEq State] [DecidableEq Action]
    [MeasurableSingletonClass State] [MeasurableSingletonClass Action]
    [Nonempty State] [Nonempty Action] in
/-- The accumulated prefix budget is exactly the finite sum of both model shares. -/
theorem selfConsistentScheduledCausalModelFailureBudget_eq_fin_sum
    (mdp : MDP State Action) (rounds : Nat) :
    selfConsistentScheduledCausalModelFailureBudget mdp rounds =
      ∑ round : Fin rounds,
        (ENNReal.ofReal
            (AdaptiveStochasticEpisodeBatchSource.selfConsistentScheduledLocalDelta
              mdp round) +
          ENNReal.ofReal
            (AdaptiveStochasticEpisodeBatchSource.selfConsistentScheduledLocalDelta
              mdp round)) := by
  rfl

/-- Avoiding the prefix event implies avoiding every coordinate event in it. -/
theorem not_mem_selfConsistentScheduledCausalModelRoundBadEvent_of_not_mem_prefix
    (mdp : MDP State Action) (initialState : Measure State)
    [IsProbabilityMeasure initialState]
    (rewardSource : mdp.MeanCompatibleRewardKernel)
    (initialTable : DeterministicMarkovPolicyTable mdp)
    (defaultState : State) (varianceProxy : NNReal)
    (baseVisitFloor : Real)
    (trajectory : HeterogeneousStochasticEpisodeBatchTrajectory mdp
      (fun s =>
        AdaptiveStochasticEpisodeBatchSource.selfConsistentScheduledEpisodes
          mdp varianceProxy baseVisitFloor s))
    {rounds t : Nat} (ht : t < rounds)
    (hprefix : trajectory ∉
      selfConsistentScheduledCausalModelBadEvent mdp initialState rewardSource
        initialTable defaultState varianceProxy baseVisitFloor rounds) :
    trajectory ∉
      selfConsistentScheduledCausalModelRoundBadEvent mdp initialState
        rewardSource initialTable defaultState varianceProxy baseVisitFloor t := by
  let localDelta :=
    AdaptiveStochasticEpisodeBatchSource.selfConsistentScheduledLocalDelta mdp
  let source := selfConsistentScheduledCausalSource mdp initialState
    rewardSource initialTable defaultState varianceProxy baseVisitFloor
  change trajectory ∉
    HeterogeneousAdaptiveStochasticEpisodeBatchSource.finiteHorizonBadEvent rounds
      (source.initialAllCoordinateEmpiricalModelBadEvent varianceProxy
        localDelta localDelta)
      (source.successorAllCoordinateEmpiricalModelBadEvent varianceProxy
        localDelta localDelta) at hprefix
  change trajectory ∉
    HeterogeneousAdaptiveStochasticEpisodeBatchSource.roundBadEvent
      (source.initialAllCoordinateEmpiricalModelBadEvent varianceProxy
        localDelta localDelta)
      (source.successorAllCoordinateEmpiricalModelBadEvent varianceProxy
        localDelta localDelta) t
  intro hround
  exact hprefix (Set.mem_iUnion_of_mem ⟨t, ht⟩ hround)

/-- The random natural-prefix cumulative behavior expected-regret process is measurable. -/
theorem measurable_selfConsistentScheduledNaturalCausalCumulativeBehaviorExpectedRegretProcess
    (mdp : MDP State Action) (initialState : Measure State)
    [IsProbabilityMeasure initialState]
    (rewardSource : mdp.MeanCompatibleRewardKernel)
    (initialTable : DeterministicMarkovPolicyTable mdp)
    (defaultState : State) (varianceProxy : NNReal)
    (baseVisitFloor : Real) (rounds : Nat) :
    Measurable
      (selfConsistentScheduledNaturalCausalCumulativeBehaviorExpectedRegretProcess
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor rounds) := by
  unfold selfConsistentScheduledNaturalCausalCumulativeBehaviorExpectedRegretProcess
  exact Finset.measurable_sum (Finset.range rounds) fun t _ht =>
    measurable_selfConsistentScheduledNaturalCausalSuccessorPolicyExpectedRegretProcess
      mdp initialState rewardSource initialTable defaultState varianceProxy
        baseVisitFloor t

/-- Off the finite-prefix model event, the actual process obeys the planning sum. -/
theorem selfConsistentScheduledNaturalCausalCumulativeBehaviorExpectedRegretProcess_le_planning_of_not_mem_modelBadEvent
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
    (rounds : Nat)
    (trajectory : HeterogeneousStochasticEpisodeBatchTrajectory mdp
      (fun s =>
        AdaptiveStochasticEpisodeBatchSource.selfConsistentScheduledEpisodes
          mdp varianceProxy baseVisitFloor s))
    (htrajectory : trajectory ∉
      selfConsistentScheduledCausalModelBadEvent mdp initialState rewardSource
        initialTable defaultState varianceProxy baseVisitFloor rounds) :
    selfConsistentScheduledNaturalCausalCumulativeBehaviorExpectedRegretProcess
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor rounds trajectory <=
      selfConsistentScheduledNaturalCausalCumulativePlanningRate mdp rounds := by
  unfold selfConsistentScheduledNaturalCausalCumulativeBehaviorExpectedRegretProcess
    selfConsistentScheduledNaturalCausalCumulativePlanningRate
  apply Finset.sum_le_sum
  intro t ht
  have hnot :=
    not_mem_selfConsistentScheduledCausalModelRoundBadEvent_of_not_mem_prefix
      mdp initialState rewardSource initialTable defaultState varianceProxy
        baseVisitFloor trajectory (Finset.mem_range.mp ht) htrajectory
  simpa [selfConsistentScheduledNaturalCausalSuccessorPolicyExpectedRegretProcess] using
    (selfConsistentScheduledCausalSource_successorPolicyAt_expectedRegret_le_rateAt_of_not_mem_modelRoundBadEvent
      mdp initialState rewardSource varianceProxy hvarianceProxy law
        initialTable defaultState support baseVisitFloor hbaseFloor
          hrewardBound hhorizon hbaseVisitFloor trajectory t hnot)

/-- Off the finite-prefix model event, the actual process obeys the log envelope. -/
theorem selfConsistentScheduledNaturalCausalCumulativeBehaviorExpectedRegretProcess_le_logarithmic_of_not_mem_modelBadEvent
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
    (rounds : Nat)
    (trajectory : HeterogeneousStochasticEpisodeBatchTrajectory mdp
      (fun s =>
        AdaptiveStochasticEpisodeBatchSource.selfConsistentScheduledEpisodes
          mdp varianceProxy baseVisitFloor s))
    (htrajectory : trajectory ∉
      selfConsistentScheduledCausalModelBadEvent mdp initialState rewardSource
        initialTable defaultState varianceProxy baseVisitFloor rounds) :
    selfConsistentScheduledNaturalCausalCumulativeBehaviorExpectedRegretProcess
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor rounds trajectory <=
      selfConsistentScheduledNaturalCausalLogarithmicCumulativeIntegratedBehaviorExpectedRegretRate
        mdp rounds :=
  (selfConsistentScheduledNaturalCausalCumulativeBehaviorExpectedRegretProcess_le_planning_of_not_mem_modelBadEvent
    mdp initialState rewardSource varianceProxy hvarianceProxy law initialTable
      defaultState support baseVisitFloor hbaseFloor hrewardBound hhorizon
        hbaseVisitFloor rounds trajectory htrajectory).trans
    (selfConsistentScheduledNaturalCausalCumulativePlanningRate_le_logarithmic
      mdp rounds)

/-- One-sided fixed-prefix violation event for the random cumulative process. -/
noncomputable def selfConsistentScheduledNaturalCausalCumulativeBehaviorExpectedRegretLogarithmicViolationSet
    (mdp : MDP State Action) (initialState : Measure State)
    [IsProbabilityMeasure initialState]
    (rewardSource : mdp.MeanCompatibleRewardKernel)
    (initialTable : DeterministicMarkovPolicyTable mdp)
    (defaultState : State) (varianceProxy : NNReal)
    (baseVisitFloor : Real) (rounds : Nat) :
    Set (HeterogeneousStochasticEpisodeBatchTrajectory mdp
      (fun s =>
        AdaptiveStochasticEpisodeBatchSource.selfConsistentScheduledEpisodes
          mdp varianceProxy baseVisitFloor s)) :=
  {trajectory |
    selfConsistentScheduledNaturalCausalLogarithmicCumulativeIntegratedBehaviorExpectedRegretRate
        mdp rounds <
      selfConsistentScheduledNaturalCausalCumulativeBehaviorExpectedRegretProcess
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor rounds trajectory}

/-- The fixed-prefix logarithmic violation event is measurable. -/
theorem measurableSet_selfConsistentScheduledNaturalCausalCumulativeBehaviorExpectedRegretLogarithmicViolationSet
    (mdp : MDP State Action) (initialState : Measure State)
    [IsProbabilityMeasure initialState]
    (rewardSource : mdp.MeanCompatibleRewardKernel)
    (initialTable : DeterministicMarkovPolicyTable mdp)
    (defaultState : State) (varianceProxy : NNReal)
    (baseVisitFloor : Real) (rounds : Nat) :
    MeasurableSet
      (selfConsistentScheduledNaturalCausalCumulativeBehaviorExpectedRegretLogarithmicViolationSet
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor rounds) := by
  unfold selfConsistentScheduledNaturalCausalCumulativeBehaviorExpectedRegretLogarithmicViolationSet
  exact measurableSet_lt measurable_const
    (measurable_selfConsistentScheduledNaturalCausalCumulativeBehaviorExpectedRegretProcess
      mdp initialState rewardSource initialTable defaultState varianceProxy
        baseVisitFloor rounds)

/-- Every logarithmic violation lies in the actual finite-prefix model event. -/
theorem selfConsistentScheduledNaturalCausalCumulativeBehaviorExpectedRegretLogarithmicViolationSet_subset_modelBadEvent
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
    (rounds : Nat) :
    selfConsistentScheduledNaturalCausalCumulativeBehaviorExpectedRegretLogarithmicViolationSet
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor rounds ⊆
      selfConsistentScheduledCausalModelBadEvent mdp initialState rewardSource
        initialTable defaultState varianceProxy baseVisitFloor rounds := by
  intro trajectory hviolation
  by_contra hgood
  have hbound :=
    selfConsistentScheduledNaturalCausalCumulativeBehaviorExpectedRegretProcess_le_logarithmic_of_not_mem_modelBadEvent
      mdp initialState rewardSource varianceProxy hvarianceProxy law
        initialTable defaultState support baseVisitFloor hbaseFloor
          hrewardBound hhorizon hbaseVisitFloor rounds trajectory hgood
  exact (not_lt_of_ge hbound) hviolation

/-- The one-sided logarithmic violation probability uses the exact prefix budget. -/
theorem selfConsistentScheduledCausalSource_trajectoryMeasure_cumulativeBehaviorExpectedRegretLogarithmicViolationSet_le
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
    (rounds : Nat) :
    let source := selfConsistentScheduledCausalSource mdp initialState
      rewardSource initialTable defaultState varianceProxy baseVisitFloor
    source.trajectoryMeasure
        (selfConsistentScheduledNaturalCausalCumulativeBehaviorExpectedRegretLogarithmicViolationSet
          mdp initialState rewardSource initialTable defaultState varianceProxy
            baseVisitFloor rounds) <=
      selfConsistentScheduledCausalModelFailureBudget mdp rounds := by
  dsimp only
  let source := selfConsistentScheduledCausalSource mdp initialState
    rewardSource initialTable defaultState varianceProxy baseVisitFloor
  let event := selfConsistentScheduledCausalModelBadEvent mdp initialState
    rewardSource initialTable defaultState varianceProxy baseVisitFloor rounds
  calc
    source.trajectoryMeasure
        (selfConsistentScheduledNaturalCausalCumulativeBehaviorExpectedRegretLogarithmicViolationSet
          mdp initialState rewardSource initialTable defaultState varianceProxy
            baseVisitFloor rounds) <=
        source.trajectoryMeasure event := measure_mono
          (selfConsistentScheduledNaturalCausalCumulativeBehaviorExpectedRegretLogarithmicViolationSet_subset_modelBadEvent
            mdp initialState rewardSource varianceProxy hvarianceProxy law
              initialTable defaultState support baseVisitFloor hbaseFloor
                hrewardBound hhorizon hbaseVisitFloor rounds)
    _ <= selfConsistentScheduledCausalModelFailureBudget mdp rounds := by
      have hparent :=
        selfConsistentScheduledCausalSource_trajectoryMeasure_allCoordinateConfidence_optimism_and_recommendedExpectedRegret
          mdp initialState rewardSource varianceProxy hvarianceProxy law
            initialTable defaultState support baseVisitFloor hbaseFloor
              hrewardBound hhorizon hbaseVisitFloor rounds
      simpa [source, event] using hparent.2.1

/-
Terminal fixed-prefix route: the model and violation events are measurable,
the violation is contained in the model event, both probability controls use
the exact accumulated model-confidence budget, and every model-good path has
the explicit planning-sum and logarithmic cumulative bounds.
-/
theorem selfConsistentScheduledCausalSource_fixedPrefixHighProbabilityLogarithmicCumulativeBehaviorExpectedRegret
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
    (rounds : Nat) :
    let source := selfConsistentScheduledCausalSource mdp initialState
      rewardSource initialTable defaultState varianceProxy baseVisitFloor
    let event := selfConsistentScheduledCausalModelBadEvent mdp initialState
      rewardSource initialTable defaultState varianceProxy baseVisitFloor rounds
    let violation :=
      selfConsistentScheduledNaturalCausalCumulativeBehaviorExpectedRegretLogarithmicViolationSet
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor rounds
    MeasurableSet event ∧
      MeasurableSet violation ∧
      source.trajectoryMeasure event <=
        selfConsistentScheduledCausalModelFailureBudget mdp rounds ∧
      violation ⊆ event ∧
      source.trajectoryMeasure violation <=
        selfConsistentScheduledCausalModelFailureBudget mdp rounds ∧
      ∀ trajectory, trajectory ∉ event ->
        selfConsistentScheduledNaturalCausalCumulativeBehaviorExpectedRegretProcess
            mdp initialState rewardSource initialTable defaultState varianceProxy
              baseVisitFloor rounds trajectory <=
          selfConsistentScheduledNaturalCausalCumulativePlanningRate mdp rounds ∧
        selfConsistentScheduledNaturalCausalCumulativePlanningRate mdp rounds <=
          selfConsistentScheduledNaturalCausalLogarithmicCumulativeIntegratedBehaviorExpectedRegretRate
            mdp rounds := by
  dsimp only
  let source := selfConsistentScheduledCausalSource mdp initialState
    rewardSource initialTable defaultState varianceProxy baseVisitFloor
  let event := selfConsistentScheduledCausalModelBadEvent mdp initialState
    rewardSource initialTable defaultState varianceProxy baseVisitFloor rounds
  let violation :=
    selfConsistentScheduledNaturalCausalCumulativeBehaviorExpectedRegretLogarithmicViolationSet
      mdp initialState rewardSource initialTable defaultState varianceProxy
        baseVisitFloor rounds
  have hparent :=
    selfConsistentScheduledCausalSource_trajectoryMeasure_allCoordinateConfidence_optimism_and_recommendedExpectedRegret
      mdp initialState rewardSource varianceProxy hvarianceProxy law initialTable
        defaultState support baseVisitFloor hbaseFloor hrewardBound hhorizon
          hbaseVisitFloor rounds
  refine ⟨hparent.1,
    measurableSet_selfConsistentScheduledNaturalCausalCumulativeBehaviorExpectedRegretLogarithmicViolationSet
      mdp initialState rewardSource initialTable defaultState varianceProxy
        baseVisitFloor rounds,
    hparent.2.1, ?_, ?_, ?_⟩
  · exact
      selfConsistentScheduledNaturalCausalCumulativeBehaviorExpectedRegretLogarithmicViolationSet_subset_modelBadEvent
        mdp initialState rewardSource varianceProxy hvarianceProxy law
          initialTable defaultState support baseVisitFloor hbaseFloor
            hrewardBound hhorizon hbaseVisitFloor rounds
  · exact
      selfConsistentScheduledCausalSource_trajectoryMeasure_cumulativeBehaviorExpectedRegretLogarithmicViolationSet_le
        mdp initialState rewardSource varianceProxy hvarianceProxy law
          initialTable defaultState support baseVisitFloor hbaseFloor
            hrewardBound hhorizon hbaseVisitFloor rounds
  · intro trajectory htrajectory
    exact ⟨
      selfConsistentScheduledNaturalCausalCumulativeBehaviorExpectedRegretProcess_le_planning_of_not_mem_modelBadEvent
        mdp initialState rewardSource varianceProxy hvarianceProxy law
          initialTable defaultState support baseVisitFloor hbaseFloor
            hrewardBound hhorizon hbaseVisitFloor rounds trajectory htrajectory,
      selfConsistentScheduledNaturalCausalCumulativePlanningRate_le_logarithmic
        mdp rounds⟩

end AdaptiveStochasticSampledEmpiricalOptimisticSource

end BanditRLProof.FiniteHorizonRL
