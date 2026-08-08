import BanditRLProof.RL.FiniteHorizonNaturalCausalRealizedBehaviorRegretHighProbabilityLogRate

/-!
# Burn-in tail high-probability natural causal realized behavior regret

This module repairs the nonvanishing finite-prefix model budget in the
fixed-prefix logarithmic realized-regret route.  Model failures before a
deterministic `burnin` are paid for by the uniform `2 * horizon` behavior
regret bound.  Only the infinite model tail from `burnin` onward enters the
probability event.  The return component remains the fixed-prefix sum of
successor-batch-average deviations, with each batch divided by its own
positive scheduled episode count.

The resulting event has exact budget
`tailModelFailureBudget burnin + ENNReal.ofReal returnDelta`.  No
independence between the model and return events is used.  This is a
fixed-`burnin`, fixed-`rounds` theorem.  An all-prefix consumer must still
choose a sublinear growing burn-in and a vanishing return share.
-/

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal

namespace BanditRLProof.FiniteHorizonRL

universe u v

variable {State : Type u} {Action : Type v}
    [MeasurableSpace State] [MeasurableSpace Action]
    [Fintype State] [Fintype Action]
    [DecidableEq State] [DecidableEq Action]
    [MeasurableSingletonClass State] [MeasurableSingletonClass Action]
    [Nonempty State] [Nonempty Action]

namespace AdaptiveStochasticSampledEmpiricalOptimisticSource

/-- Uniform burn-in charge plus the compiled full logarithmic planning sum. -/
noncomputable def
    selfConsistentScheduledNaturalCausalBurninCumulativeBehaviorExpectedRegretLogarithmicRate
    (mdp : MDP State Action) (burnin rounds : Nat) : Real :=
  2 * (mdp.horizon : Real) * (burnin : Real) +
    selfConsistentScheduledNaturalCausalLogarithmicCumulativeIntegratedBehaviorExpectedRegretRate
      mdp rounds

/--
Outside the infinite model tail, only the first `burnin` natural rounds need
the uniform `2 * horizon` charge.  Every later round uses its actual
coordinate model certificate.
-/
theorem
    selfConsistentScheduledNaturalCausalCumulativeBehaviorExpectedRegretProcess_le_burnin_logarithmic_of_not_mem_tailModelBadEvent
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
    (burnin rounds : Nat) (hburnin : burnin <= rounds)
    (trajectory : HeterogeneousStochasticEpisodeBatchTrajectory mdp
      (fun s =>
        AdaptiveStochasticEpisodeBatchSource.selfConsistentScheduledEpisodes
          mdp varianceProxy baseVisitFloor s))
    (htrajectory : trajectory ∉
      selfConsistentScheduledCausalTailModelBadEvent mdp initialState
        rewardSource initialTable defaultState varianceProxy baseVisitFloor
          burnin) :
    selfConsistentScheduledNaturalCausalCumulativeBehaviorExpectedRegretProcess
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor rounds trajectory <=
      selfConsistentScheduledNaturalCausalBurninCumulativeBehaviorExpectedRegretLogarithmicRate
        mdp burnin rounds := by
  let expectedAt := fun t =>
    selfConsistentScheduledNaturalCausalSuccessorPolicyExpectedRegretProcess
      mdp initialState rewardSource initialTable defaultState varianceProxy
        baseVisitFloor t trajectory
  let rateAt := fun t => selfConsistentScheduledCausalPlanningRateAt mdp t
  have hEarly :
      (Finset.range burnin).sum expectedAt <=
        (Finset.range burnin).sum
          (fun _ => 2 * (mdp.horizon : Real)) := by
    apply Finset.sum_le_sum
    intro t _ht
    simpa [expectedAt] using
      (selfConsistentScheduledNaturalCausalSuccessorPolicyExpectedRegretProcess_le_two_mul_horizon
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor hrewardBound t trajectory)
  have hTail :
      (Finset.Ico burnin rounds).sum expectedAt <=
        (Finset.Ico burnin rounds).sum rateAt := by
    apply Finset.sum_le_sum
    intro t ht
    have htBounds := Finset.mem_Ico.mp ht
    have hnotRound :=
      not_mem_selfConsistentScheduledCausalModelRoundBadEvent_of_not_mem_tail
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor burnin t htBounds.1 trajectory htrajectory
    simpa [expectedAt, rateAt,
      selfConsistentScheduledNaturalCausalSuccessorPolicyExpectedRegretProcess]
      using
        (selfConsistentScheduledCausalSource_successorPolicyAt_expectedRegret_le_rateAt_of_not_mem_modelRoundBadEvent
          mdp initialState rewardSource varianceProxy hvarianceProxy law
            initialTable defaultState support baseVisitFloor hbaseFloor
              hrewardBound hhorizon hbaseVisitFloor trajectory t hnotRound)
  have hrateNonneg : forall t, 0 <= rateAt t := by
    intro t
    dsimp [rateAt]
    unfold selfConsistentScheduledCausalPlanningRateAt
    rw [AdaptiveStochasticEpisodeBatchSource.selfConsistentScheduledTransitionBudgetRateEnvelope_eq]
    unfold exploratoryBehaviorRegretCharge
    positivity
  have htailRateLeFull :
      (Finset.Ico burnin rounds).sum rateAt <=
        (Finset.range rounds).sum rateAt := by
    have hsplit := Finset.sum_range_add_sum_Ico rateAt hburnin
    have hearlyNonneg : 0 <= (Finset.range burnin).sum rateAt :=
      Finset.sum_nonneg fun t _ => hrateNonneg t
    calc
      (Finset.Ico burnin rounds).sum rateAt <=
          (Finset.range burnin).sum rateAt +
            (Finset.Ico burnin rounds).sum rateAt :=
        le_add_of_nonneg_left hearlyNonneg
      _ = (Finset.range rounds).sum rateAt := hsplit
  have hsum :
      selfConsistentScheduledNaturalCausalCumulativeBehaviorExpectedRegretProcess
          mdp initialState rewardSource initialTable defaultState varianceProxy
            baseVisitFloor rounds trajectory <=
        2 * (mdp.horizon : Real) * (burnin : Real) +
          selfConsistentScheduledNaturalCausalCumulativePlanningRate
            mdp rounds := by
    rw [show
      selfConsistentScheduledNaturalCausalCumulativeBehaviorExpectedRegretProcess
          mdp initialState rewardSource initialTable defaultState varianceProxy
            baseVisitFloor rounds trajectory =
        (Finset.range rounds).sum expectedAt by
      rfl]
    calc
      (Finset.range rounds).sum expectedAt =
          (Finset.range burnin).sum expectedAt +
            (Finset.Ico burnin rounds).sum expectedAt :=
        (Finset.sum_range_add_sum_Ico expectedAt hburnin).symm
      _ <= (Finset.range burnin).sum
              (fun _ => 2 * (mdp.horizon : Real)) +
            (Finset.Ico burnin rounds).sum rateAt :=
        add_le_add hEarly hTail
      _ <= (Finset.range burnin).sum
              (fun _ => 2 * (mdp.horizon : Real)) +
            (Finset.range rounds).sum rateAt :=
        add_le_add (le_refl _) htailRateLeFull
      _ = 2 * (mdp.horizon : Real) * (burnin : Real) +
            selfConsistentScheduledNaturalCausalCumulativePlanningRate
              mdp rounds := by
        simp [rateAt,
          selfConsistentScheduledNaturalCausalCumulativePlanningRate]
        ring
  calc
    selfConsistentScheduledNaturalCausalCumulativeBehaviorExpectedRegretProcess
          mdp initialState rewardSource initialTable defaultState varianceProxy
            baseVisitFloor rounds trajectory <=
        2 * (mdp.horizon : Real) * (burnin : Real) +
          selfConsistentScheduledNaturalCausalCumulativePlanningRate mdp rounds :=
      hsum
    _ <= 2 * (mdp.horizon : Real) * (burnin : Real) +
          selfConsistentScheduledNaturalCausalLogarithmicCumulativeIntegratedBehaviorExpectedRegretRate
            mdp rounds :=
      add_le_add (le_refl _)
        (selfConsistentScheduledNaturalCausalCumulativePlanningRate_le_logarithmic
          mdp rounds)
    _ =
        selfConsistentScheduledNaturalCausalBurninCumulativeBehaviorExpectedRegretLogarithmicRate
          mdp burnin rounds := rfl

/--
Infinite model tail after `burnin`, union the fixed-prefix normalized return
deviation event.
-/
noncomputable def selfConsistentScheduledNaturalCausalBurninTailModelReturnBadEvent
    (mdp : MDP State Action) (initialState : Measure State)
    [IsProbabilityMeasure initialState]
    (rewardSource : mdp.MeanCompatibleRewardKernel)
    (initialTable : DeterministicMarkovPolicyTable mdp)
    (defaultState : State) (varianceProxy : NNReal)
    (baseVisitFloor : Real) (burnin rounds : Nat) (returnDelta : Real) :
    Set (HeterogeneousStochasticEpisodeBatchTrajectory mdp
      (fun t =>
        AdaptiveStochasticEpisodeBatchSource.selfConsistentScheduledEpisodes
          mdp varianceProxy baseVisitFloor t)) :=
  selfConsistentScheduledCausalTailModelBadEvent mdp initialState rewardSource
      initialTable defaultState varianceProxy baseVisitFloor burnin ∪
    selfConsistentScheduledNaturalCausalCumulativeReturnBadEvent mdp
      initialState rewardSource initialTable defaultState varianceProxy
        baseVisitFloor rounds returnDelta

/-- Exact infinite-tail model share plus caller-supplied return share. -/
noncomputable def
    selfConsistentScheduledNaturalCausalBurninTailModelReturnFailureBudget
    (mdp : MDP State Action) (burnin : Nat) (returnDelta : Real) : ENNReal :=
  selfConsistentScheduledCausalTailModelFailureBudget mdp burnin +
    ENNReal.ofReal returnDelta

/-- The joint burn-in tail event is measurable and has its exact union budget. -/
theorem
    selfConsistentScheduledCausalSource_trajectoryMeasure_naturalBurninTailModelReturnBadEvent_le
    (mdp : MDP State Action) (initialState : Measure State)
    [IsProbabilityMeasure initialState]
    [StandardBorelSpace State] [StandardBorelSpace Action]
    (rewardSource : mdp.MeanCompatibleRewardKernel)
    (varianceProxy : NNReal) (hvarianceProxy : 0 < varianceProxy)
    (law : rewardSource.UniformSubgaussianRewardLaw varianceProxy)
    (initialTable : DeterministicMarkovPolicyTable mdp)
    (defaultState : State)
    (baseVisitFloor : Real)
    (hrewardBound : forall state action, |mdp.reward state action| <= 1)
    (hhorizon : 0 < mdp.horizon)
    (burnin rounds : Nat) (hrounds : 0 < rounds)
    (returnDelta : Real) (hreturnDelta : 0 < returnDelta)
    (hreturnDelta_le_one : returnDelta <= 1) :
    let source := selfConsistentScheduledCausalSource mdp initialState
      rewardSource initialTable defaultState varianceProxy baseVisitFloor
    let event :=
      selfConsistentScheduledNaturalCausalBurninTailModelReturnBadEvent mdp
        initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor burnin rounds returnDelta
    MeasurableSet event ∧
      source.trajectoryMeasure event <=
        selfConsistentScheduledNaturalCausalBurninTailModelReturnFailureBudget
          mdp burnin returnDelta := by
  dsimp only
  let source := selfConsistentScheduledCausalSource mdp initialState
    rewardSource initialTable defaultState varianceProxy baseVisitFloor
  let modelEvent := selfConsistentScheduledCausalTailModelBadEvent mdp
    initialState rewardSource initialTable defaultState varianceProxy
      baseVisitFloor burnin
  let returnEvent :=
    selfConsistentScheduledNaturalCausalCumulativeReturnBadEvent mdp
      initialState rewardSource initialTable defaultState varianceProxy
        baseVisitFloor rounds returnDelta
  have hmodelMeasurable : MeasurableSet modelEvent := by
    simpa [modelEvent] using
      (measurableSet_selfConsistentScheduledCausalTailModelBadEvent mdp
        initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor burnin)
  have hmodelTail : source.trajectoryMeasure modelEvent <=
      selfConsistentScheduledCausalTailModelFailureBudget mdp burnin := by
    simpa [source, modelEvent] using
      (selfConsistentScheduledCausalSource_trajectoryMeasure_tailModelBadEvent_le
        mdp initialState rewardSource varianceProxy hvarianceProxy law
          initialTable defaultState baseVisitFloor burnin)
  have hreturnMeasurable : MeasurableSet returnEvent := by
    simpa [returnEvent] using
      (measurableSet_selfConsistentScheduledNaturalCausalCumulativeReturnBadEvent
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor rounds returnDelta)
  have hreturnTail : source.trajectoryMeasure returnEvent <=
      ENNReal.ofReal returnDelta := by
    simpa [source, returnEvent] using
      (selfConsistentScheduledCausalSource_trajectoryMeasure_naturalCumulativeReturnBadEvent_le
        mdp initialState rewardSource varianceProxy law initialTable
          defaultState baseVisitFloor hrewardBound hhorizon rounds hrounds
            returnDelta hreturnDelta hreturnDelta_le_one)
  refine ⟨?_, ?_⟩
  · simpa [selfConsistentScheduledNaturalCausalBurninTailModelReturnBadEvent,
      modelEvent, returnEvent] using hmodelMeasurable.union hreturnMeasurable
  · have hunion :
        source.trajectoryMeasure (modelEvent ∪ returnEvent) <=
          source.trajectoryMeasure modelEvent +
            source.trajectoryMeasure returnEvent :=
      measure_union_le modelEvent returnEvent
    have hsum := add_le_add hmodelTail hreturnTail
    simpa [selfConsistentScheduledNaturalCausalBurninTailModelReturnBadEvent,
      selfConsistentScheduledNaturalCausalBurninTailModelReturnFailureBudget,
      modelEvent, returnEvent, source] using hunion.trans hsum

/-- Burn-in expected-regret envelope plus normalized return radius. -/
noncomputable def
    selfConsistentScheduledNaturalCausalBurninRealizedCumulativeLogarithmicRate
    (mdp : MDP State Action) (varianceProxy : NNReal)
    (baseVisitFloor : Real) (burnin rounds : Nat)
    (returnDelta : Real) : Real :=
  selfConsistentScheduledNaturalCausalBurninCumulativeBehaviorExpectedRegretLogarithmicRate
      mdp burnin rounds +
    Concentration.subGaussianSumConfidenceRadius
      (selfConsistentScheduledNaturalCausalCumulativeReturnVarianceProxy
        mdp varianceProxy baseVisitFloor rounds) returnDelta

/-- Positive-round average form of the burn-in realized rate. -/
noncomputable def
    selfConsistentScheduledNaturalCausalBurninRealizedAverageLogarithmicRate
    (mdp : MDP State Action) (varianceProxy : NNReal)
    (baseVisitFloor : Real) (burnin rounds : Nat)
    (returnDelta : Real) : Real :=
  selfConsistentScheduledNaturalCausalBurninRealizedCumulativeLogarithmicRate
    mdp varianceProxy baseVisitFloor burnin rounds returnDelta /
      (rounds : Real)

/--
Outside the tail-model/return union, cumulative successor-batch-average
realized behavior regret obeys the burn-in logarithmic envelope.
-/
theorem
    selfConsistentScheduledNaturalCausalCumulativeRealizedBehaviorRegretProcess_le_burnin_logarithmic_of_not_mem_tailModelReturnBadEvent
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
    (burnin rounds : Nat) (hburnin : burnin <= rounds)
    (returnDelta : Real)
    (trajectory : HeterogeneousStochasticEpisodeBatchTrajectory mdp
      (fun t =>
        AdaptiveStochasticEpisodeBatchSource.selfConsistentScheduledEpisodes
          mdp varianceProxy baseVisitFloor t))
    (htrajectory : trajectory ∉
      selfConsistentScheduledNaturalCausalBurninTailModelReturnBadEvent mdp
        initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor burnin rounds returnDelta) :
    selfConsistentScheduledNaturalCausalCumulativeRealizedBehaviorRegretProcess
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor rounds trajectory <=
      selfConsistentScheduledNaturalCausalBurninRealizedCumulativeLogarithmicRate
        mdp varianceProxy baseVisitFloor burnin rounds returnDelta := by
  let modelEvent := selfConsistentScheduledCausalTailModelBadEvent mdp
    initialState rewardSource initialTable defaultState varianceProxy
      baseVisitFloor burnin
  let returnEvent :=
    selfConsistentScheduledNaturalCausalCumulativeReturnBadEvent mdp
      initialState rewardSource initialTable defaultState varianceProxy
        baseVisitFloor rounds returnDelta
  have hnotModel : trajectory ∉ modelEvent := by
    intro hmodel
    exact htrajectory (by
      simpa [selfConsistentScheduledNaturalCausalBurninTailModelReturnBadEvent,
        modelEvent, returnEvent] using Set.mem_union_left returnEvent hmodel)
  have hnotReturn : trajectory ∉ returnEvent := by
    intro hreturn
    exact htrajectory (by
      simpa [selfConsistentScheduledNaturalCausalBurninTailModelReturnBadEvent,
        modelEvent, returnEvent] using Set.mem_union_right modelEvent hreturn)
  have hexpected :=
    selfConsistentScheduledNaturalCausalCumulativeBehaviorExpectedRegretProcess_le_burnin_logarithmic_of_not_mem_tailModelBadEvent
      mdp initialState rewardSource varianceProxy hvarianceProxy law
        initialTable defaultState support baseVisitFloor hbaseFloor
          hrewardBound hhorizon hbaseVisitFloor burnin rounds hburnin
            trajectory (by simpa [modelEvent] using hnotModel)
  have hnotRadius :
      ¬ Concentration.subGaussianSumConfidenceRadius
          (selfConsistentScheduledNaturalCausalCumulativeReturnVarianceProxy
            mdp varianceProxy baseVisitFloor rounds) returnDelta <=
        |selfConsistentScheduledNaturalCausalCumulativeReturnDeviationProcess
          mdp initialState rewardSource initialTable defaultState varianceProxy
            baseVisitFloor rounds trajectory| := by
    simpa [returnEvent,
      selfConsistentScheduledNaturalCausalCumulativeReturnBadEvent] using
        hnotReturn
  have hnoise :
      -selfConsistentScheduledNaturalCausalCumulativeReturnDeviationProcess
          mdp initialState rewardSource initialTable defaultState varianceProxy
            baseVisitFloor rounds trajectory <=
        Concentration.subGaussianSumConfidenceRadius
          (selfConsistentScheduledNaturalCausalCumulativeReturnVarianceProxy
            mdp varianceProxy baseVisitFloor rounds) returnDelta :=
    (neg_le_abs _).trans (lt_of_not_ge hnotRadius).le
  rw [selfConsistentScheduledNaturalCausalCumulativeRealizedBehaviorRegretProcess_eq_expected_sub_deviation
    mdp initialState rewardSource initialTable defaultState varianceProxy
      baseVisitFloor rounds trajectory]
  calc
    selfConsistentScheduledNaturalCausalCumulativeBehaviorExpectedRegretProcess
          mdp initialState rewardSource initialTable defaultState varianceProxy
            baseVisitFloor rounds trajectory -
        selfConsistentScheduledNaturalCausalCumulativeReturnDeviationProcess
          mdp initialState rewardSource initialTable defaultState varianceProxy
            baseVisitFloor rounds trajectory =
      selfConsistentScheduledNaturalCausalCumulativeBehaviorExpectedRegretProcess
          mdp initialState rewardSource initialTable defaultState varianceProxy
            baseVisitFloor rounds trajectory +
        (-selfConsistentScheduledNaturalCausalCumulativeReturnDeviationProcess
          mdp initialState rewardSource initialTable defaultState varianceProxy
            baseVisitFloor rounds trajectory) := by ring
    _ <=
        selfConsistentScheduledNaturalCausalBurninCumulativeBehaviorExpectedRegretLogarithmicRate
            mdp burnin rounds +
          Concentration.subGaussianSumConfidenceRadius
            (selfConsistentScheduledNaturalCausalCumulativeReturnVarianceProxy
              mdp varianceProxy baseVisitFloor rounds) returnDelta :=
      add_le_add hexpected hnoise
    _ =
        selfConsistentScheduledNaturalCausalBurninRealizedCumulativeLogarithmicRate
          mdp varianceProxy baseVisitFloor burnin rounds returnDelta := rfl

/-- Joint-good paths also obey the positive-round average burn-in rate. -/
theorem
    selfConsistentScheduledNaturalCausalAverageRealizedBehaviorRegretProcess_le_burnin_logarithmic_of_not_mem_tailModelReturnBadEvent
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
    (burnin rounds : Nat) (hburnin : burnin <= rounds)
    (hrounds : 0 < rounds) (returnDelta : Real)
    (trajectory : HeterogeneousStochasticEpisodeBatchTrajectory mdp
      (fun t =>
        AdaptiveStochasticEpisodeBatchSource.selfConsistentScheduledEpisodes
          mdp varianceProxy baseVisitFloor t))
    (htrajectory : trajectory ∉
      selfConsistentScheduledNaturalCausalBurninTailModelReturnBadEvent mdp
        initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor burnin rounds returnDelta) :
    selfConsistentScheduledNaturalCausalAverageRealizedBehaviorRegretProcess
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor rounds trajectory <=
      selfConsistentScheduledNaturalCausalBurninRealizedAverageLogarithmicRate
        mdp varianceProxy baseVisitFloor burnin rounds returnDelta := by
  have hcumulative :=
    selfConsistentScheduledNaturalCausalCumulativeRealizedBehaviorRegretProcess_le_burnin_logarithmic_of_not_mem_tailModelReturnBadEvent
      mdp initialState rewardSource varianceProxy hvarianceProxy law
        initialTable defaultState support baseVisitFloor hbaseFloor
          hrewardBound hhorizon hbaseVisitFloor burnin rounds hburnin
            returnDelta trajectory htrajectory
  have hroundsReal : (0 : Real) < (rounds : Real) := by
    exact_mod_cast hrounds
  simpa [selfConsistentScheduledNaturalCausalAverageRealizedBehaviorRegretProcess,
    HeterogeneousAdaptiveStochasticEpisodeBatchSource.naturalAverageRealizedBehaviorRegret,
    selfConsistentScheduledNaturalCausalCumulativeRealizedBehaviorRegretProcess,
    selfConsistentScheduledNaturalCausalBurninRealizedAverageLogarithmicRate]
    using div_le_div_of_nonneg_right hcumulative hroundsReal.le

/-- One-sided cumulative burn-in realized-regret violation set. -/
noncomputable def
    selfConsistentScheduledNaturalCausalBurninCumulativeRealizedBehaviorRegretLogarithmicViolationSet
    (mdp : MDP State Action) (initialState : Measure State)
    [IsProbabilityMeasure initialState]
    (rewardSource : mdp.MeanCompatibleRewardKernel)
    (initialTable : DeterministicMarkovPolicyTable mdp)
    (defaultState : State) (varianceProxy : NNReal)
    (baseVisitFloor : Real) (burnin rounds : Nat) (returnDelta : Real) :
    Set (HeterogeneousStochasticEpisodeBatchTrajectory mdp
      (fun t =>
        AdaptiveStochasticEpisodeBatchSource.selfConsistentScheduledEpisodes
          mdp varianceProxy baseVisitFloor t)) :=
  {trajectory |
    selfConsistentScheduledNaturalCausalBurninRealizedCumulativeLogarithmicRate
        mdp varianceProxy baseVisitFloor burnin rounds returnDelta <
      selfConsistentScheduledNaturalCausalCumulativeRealizedBehaviorRegretProcess
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor rounds trajectory}

/-- One-sided average burn-in realized-regret violation set. -/
noncomputable def
    selfConsistentScheduledNaturalCausalBurninAverageRealizedBehaviorRegretLogarithmicViolationSet
    (mdp : MDP State Action) (initialState : Measure State)
    [IsProbabilityMeasure initialState]
    (rewardSource : mdp.MeanCompatibleRewardKernel)
    (initialTable : DeterministicMarkovPolicyTable mdp)
    (defaultState : State) (varianceProxy : NNReal)
    (baseVisitFloor : Real) (burnin rounds : Nat) (returnDelta : Real) :
    Set (HeterogeneousStochasticEpisodeBatchTrajectory mdp
      (fun t =>
        AdaptiveStochasticEpisodeBatchSource.selfConsistentScheduledEpisodes
          mdp varianceProxy baseVisitFloor t)) :=
  {trajectory |
    selfConsistentScheduledNaturalCausalBurninRealizedAverageLogarithmicRate
        mdp varianceProxy baseVisitFloor burnin rounds returnDelta <
      selfConsistentScheduledNaturalCausalAverageRealizedBehaviorRegretProcess
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor rounds trajectory}

/-- The cumulative burn-in violation set is measurable. -/
theorem
    measurableSet_selfConsistentScheduledNaturalCausalBurninCumulativeRealizedBehaviorRegretLogarithmicViolationSet
    (mdp : MDP State Action) (initialState : Measure State)
    [IsProbabilityMeasure initialState]
    (rewardSource : mdp.MeanCompatibleRewardKernel)
    (initialTable : DeterministicMarkovPolicyTable mdp)
    (defaultState : State) (varianceProxy : NNReal)
    (baseVisitFloor : Real) (burnin rounds : Nat) (returnDelta : Real) :
    MeasurableSet
      (selfConsistentScheduledNaturalCausalBurninCumulativeRealizedBehaviorRegretLogarithmicViolationSet
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor burnin rounds returnDelta) := by
  unfold
    selfConsistentScheduledNaturalCausalBurninCumulativeRealizedBehaviorRegretLogarithmicViolationSet
  exact measurableSet_lt measurable_const
    (measurable_selfConsistentScheduledNaturalCausalCumulativeRealizedBehaviorRegretProcess
      mdp initialState rewardSource initialTable defaultState varianceProxy
        baseVisitFloor rounds)

/-- The average burn-in violation set is measurable. -/
theorem
    measurableSet_selfConsistentScheduledNaturalCausalBurninAverageRealizedBehaviorRegretLogarithmicViolationSet
    (mdp : MDP State Action) (initialState : Measure State)
    [IsProbabilityMeasure initialState]
    (rewardSource : mdp.MeanCompatibleRewardKernel)
    (initialTable : DeterministicMarkovPolicyTable mdp)
    (defaultState : State) (varianceProxy : NNReal)
    (baseVisitFloor : Real) (burnin rounds : Nat) (returnDelta : Real) :
    MeasurableSet
      (selfConsistentScheduledNaturalCausalBurninAverageRealizedBehaviorRegretLogarithmicViolationSet
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor burnin rounds returnDelta) := by
  unfold
    selfConsistentScheduledNaturalCausalBurninAverageRealizedBehaviorRegretLogarithmicViolationSet
  exact measurableSet_lt measurable_const
    (measurable_selfConsistentScheduledNaturalCausalAverageRealizedBehaviorRegretProcess
      mdp initialState rewardSource initialTable defaultState varianceProxy
        baseVisitFloor rounds)

/-- Every cumulative burn-in violation belongs to the joint tail event. -/
theorem
    selfConsistentScheduledNaturalCausalBurninCumulativeRealizedBehaviorRegretLogarithmicViolationSet_subset_tailModelReturnBadEvent
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
    (burnin rounds : Nat) (hburnin : burnin <= rounds)
    (returnDelta : Real) :
    selfConsistentScheduledNaturalCausalBurninCumulativeRealizedBehaviorRegretLogarithmicViolationSet
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor burnin rounds returnDelta ⊆
      selfConsistentScheduledNaturalCausalBurninTailModelReturnBadEvent mdp
        initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor burnin rounds returnDelta := by
  intro trajectory hviolation
  by_contra hgood
  have hbound :=
    selfConsistentScheduledNaturalCausalCumulativeRealizedBehaviorRegretProcess_le_burnin_logarithmic_of_not_mem_tailModelReturnBadEvent
      mdp initialState rewardSource varianceProxy hvarianceProxy law
        initialTable defaultState support baseVisitFloor hbaseFloor
          hrewardBound hhorizon hbaseVisitFloor burnin rounds hburnin
            returnDelta trajectory hgood
  exact (not_lt_of_ge hbound) hviolation

/-- Every average burn-in violation belongs to the joint tail event. -/
theorem
    selfConsistentScheduledNaturalCausalBurninAverageRealizedBehaviorRegretLogarithmicViolationSet_subset_tailModelReturnBadEvent
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
    (burnin rounds : Nat) (hburnin : burnin <= rounds)
    (hrounds : 0 < rounds) (returnDelta : Real) :
    selfConsistentScheduledNaturalCausalBurninAverageRealizedBehaviorRegretLogarithmicViolationSet
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor burnin rounds returnDelta ⊆
      selfConsistentScheduledNaturalCausalBurninTailModelReturnBadEvent mdp
        initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor burnin rounds returnDelta := by
  intro trajectory hviolation
  by_contra hgood
  have hbound :=
    selfConsistentScheduledNaturalCausalAverageRealizedBehaviorRegretProcess_le_burnin_logarithmic_of_not_mem_tailModelReturnBadEvent
      mdp initialState rewardSource varianceProxy hvarianceProxy law
        initialTable defaultState support baseVisitFloor hbaseFloor
          hrewardBound hhorizon hbaseVisitFloor burnin rounds hburnin hrounds
            returnDelta trajectory hgood
  exact (not_lt_of_ge hbound) hviolation

/--
Terminal burn-in tail high-probability logarithmic cumulative and average
realized behavior-regret certificate.
-/
theorem
    selfConsistentScheduledCausalSource_burninTailHighProbabilityLogarithmicCumulativeAverageRealizedBehaviorRegret
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
    (burnin rounds : Nat) (hburnin : burnin <= rounds)
    (hrounds : 0 < rounds)
    (returnDelta : Real) (hreturnDelta : 0 < returnDelta)
    (hreturnDelta_le_one : returnDelta <= 1) :
    let source := selfConsistentScheduledCausalSource mdp initialState
      rewardSource initialTable defaultState varianceProxy baseVisitFloor
    let event :=
      selfConsistentScheduledNaturalCausalBurninTailModelReturnBadEvent mdp
        initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor burnin rounds returnDelta
    let cumulativeViolation :=
      selfConsistentScheduledNaturalCausalBurninCumulativeRealizedBehaviorRegretLogarithmicViolationSet
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor burnin rounds returnDelta
    let averageViolation :=
      selfConsistentScheduledNaturalCausalBurninAverageRealizedBehaviorRegretLogarithmicViolationSet
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor burnin rounds returnDelta
    let failureBudget :=
      selfConsistentScheduledNaturalCausalBurninTailModelReturnFailureBudget
        mdp burnin returnDelta
    MeasurableSet event ∧
      MeasurableSet cumulativeViolation ∧
      MeasurableSet averageViolation ∧
      source.trajectoryMeasure event <= failureBudget ∧
      cumulativeViolation ⊆ event ∧
      averageViolation ⊆ event ∧
      source.trajectoryMeasure cumulativeViolation <= failureBudget ∧
      source.trajectoryMeasure averageViolation <= failureBudget ∧
      (failureBudget < 1 ->
        source.trajectoryMeasure event < 1 ∧
        source.trajectoryMeasure cumulativeViolation < 1 ∧
        source.trajectoryMeasure averageViolation < 1) ∧
      forall trajectory, trajectory ∉ event ->
        selfConsistentScheduledNaturalCausalCumulativeRealizedBehaviorRegretProcess
            mdp initialState rewardSource initialTable defaultState
              varianceProxy baseVisitFloor rounds trajectory <=
          selfConsistentScheduledNaturalCausalBurninRealizedCumulativeLogarithmicRate
            mdp varianceProxy baseVisitFloor burnin rounds returnDelta ∧
        selfConsistentScheduledNaturalCausalAverageRealizedBehaviorRegretProcess
            mdp initialState rewardSource initialTable defaultState
              varianceProxy baseVisitFloor rounds trajectory <=
          selfConsistentScheduledNaturalCausalBurninRealizedAverageLogarithmicRate
            mdp varianceProxy baseVisitFloor burnin rounds returnDelta := by
  dsimp only
  let source := selfConsistentScheduledCausalSource mdp initialState
    rewardSource initialTable defaultState varianceProxy baseVisitFloor
  let event :=
    selfConsistentScheduledNaturalCausalBurninTailModelReturnBadEvent mdp
      initialState rewardSource initialTable defaultState varianceProxy
        baseVisitFloor burnin rounds returnDelta
  let cumulativeViolation :=
    selfConsistentScheduledNaturalCausalBurninCumulativeRealizedBehaviorRegretLogarithmicViolationSet
      mdp initialState rewardSource initialTable defaultState varianceProxy
        baseVisitFloor burnin rounds returnDelta
  let averageViolation :=
    selfConsistentScheduledNaturalCausalBurninAverageRealizedBehaviorRegretLogarithmicViolationSet
      mdp initialState rewardSource initialTable defaultState varianceProxy
        baseVisitFloor burnin rounds returnDelta
  let failureBudget :=
    selfConsistentScheduledNaturalCausalBurninTailModelReturnFailureBudget
      mdp burnin returnDelta
  have hevent :=
    selfConsistentScheduledCausalSource_trajectoryMeasure_naturalBurninTailModelReturnBadEvent_le
      mdp initialState rewardSource varianceProxy hvarianceProxy law
        initialTable defaultState baseVisitFloor hrewardBound hhorizon
          burnin rounds hrounds returnDelta hreturnDelta hreturnDelta_le_one
  have hcumulativeMeasurable : MeasurableSet cumulativeViolation := by
    simpa [cumulativeViolation] using
      (measurableSet_selfConsistentScheduledNaturalCausalBurninCumulativeRealizedBehaviorRegretLogarithmicViolationSet
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor burnin rounds returnDelta)
  have haverageMeasurable : MeasurableSet averageViolation := by
    simpa [averageViolation] using
      (measurableSet_selfConsistentScheduledNaturalCausalBurninAverageRealizedBehaviorRegretLogarithmicViolationSet
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor burnin rounds returnDelta)
  have hcumulativeSubset : cumulativeViolation ⊆ event := by
    simpa [cumulativeViolation, event] using
      (selfConsistentScheduledNaturalCausalBurninCumulativeRealizedBehaviorRegretLogarithmicViolationSet_subset_tailModelReturnBadEvent
        mdp initialState rewardSource varianceProxy hvarianceProxy law
          initialTable defaultState support baseVisitFloor hbaseFloor
            hrewardBound hhorizon hbaseVisitFloor burnin rounds hburnin
              returnDelta)
  have haverageSubset : averageViolation ⊆ event := by
    simpa [averageViolation, event] using
      (selfConsistentScheduledNaturalCausalBurninAverageRealizedBehaviorRegretLogarithmicViolationSet_subset_tailModelReturnBadEvent
        mdp initialState rewardSource varianceProxy hvarianceProxy law
          initialTable defaultState support baseVisitFloor hbaseFloor
            hrewardBound hhorizon hbaseVisitFloor burnin rounds hburnin
              hrounds returnDelta)
  have heventMeasure : source.trajectoryMeasure event <= failureBudget := by
    simpa [source, event, failureBudget] using hevent.2
  have hcumulativeMeasure :
      source.trajectoryMeasure cumulativeViolation <= failureBudget :=
    (measure_mono hcumulativeSubset).trans heventMeasure
  have haverageMeasure :
      source.trajectoryMeasure averageViolation <= failureBudget :=
    (measure_mono haverageSubset).trans heventMeasure
  refine ⟨?_, hcumulativeMeasurable, haverageMeasurable, heventMeasure,
    hcumulativeSubset, haverageSubset, hcumulativeMeasure, haverageMeasure,
    ?_, ?_⟩
  · simpa [event] using hevent.1
  · intro hnontrivial
    exact ⟨heventMeasure.trans_lt hnontrivial,
      hcumulativeMeasure.trans_lt hnontrivial,
      haverageMeasure.trans_lt hnontrivial⟩
  · intro trajectory htrajectory
    exact ⟨
      selfConsistentScheduledNaturalCausalCumulativeRealizedBehaviorRegretProcess_le_burnin_logarithmic_of_not_mem_tailModelReturnBadEvent
        mdp initialState rewardSource varianceProxy hvarianceProxy law
          initialTable defaultState support baseVisitFloor hbaseFloor
            hrewardBound hhorizon hbaseVisitFloor burnin rounds hburnin
              returnDelta trajectory (by simpa [event] using htrajectory),
      selfConsistentScheduledNaturalCausalAverageRealizedBehaviorRegretProcess_le_burnin_logarithmic_of_not_mem_tailModelReturnBadEvent
        mdp initialState rewardSource varianceProxy hvarianceProxy law
          initialTable defaultState support baseVisitFloor hbaseFloor
            hrewardBound hhorizon hbaseVisitFloor burnin rounds hburnin
              hrounds returnDelta trajectory (by simpa [event] using htrajectory)⟩

end AdaptiveStochasticSampledEmpiricalOptimisticSource

end BanditRLProof.FiniteHorizonRL
