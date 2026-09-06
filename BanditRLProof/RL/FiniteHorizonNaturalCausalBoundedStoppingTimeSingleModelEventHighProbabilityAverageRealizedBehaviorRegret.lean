import BanditRLProof.RL.FiniteHorizonNaturalCausalBoundedStoppingTimeHighProbabilityAverageRealizedBehaviorRegret

/-!
# Bounded stopping-time regret with one horizon model event

The finite stopped-prefix route is sharpened by charging model-confidence
failures only once at the deterministic horizon. Return deviations still use
an equal-share finite union over the possible positive stopped prefixes.

Stopping-time regularity is used only for filtered measurability. The tail
proof is event containment and finite subadditivity, without optional stopping
or independence between prefix events.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal ProbabilityTheory

namespace BanditRLProof.FiniteHorizonRL

universe u v

variable {State : Type u} {Action : Type v}
    [MeasurableSpace State] [MeasurableSpace Action]
    [Fintype State] [Fintype Action]
    [DecidableEq State] [DecidableEq Action]
    [MeasurableSingletonClass State] [MeasurableSingletonClass Action]
    [Nonempty State] [Nonempty Action]

namespace HeterogeneousAdaptiveStochasticEpisodeBatchSource

/-- A finite-horizon heterogeneous bad-event union is monotone in its outer
horizon when the underlying coordinate event family is unchanged. -/
theorem finiteHorizonBadEvent_mono
    {mdp : MDP State Action} {episodes : Nat -> Nat}
    {rounds maxRounds : Nat}
    {initialBad : Set (StochasticEpisodeBatch mdp (episodes 0))}
    {successorBad : (n : Nat) ->
      Set (HeterogeneousStochasticEpisodeBatchPrefix mdp episodes n ×
        StochasticEpisodeBatch mdp (episodes (n + 1)))}
    (hrounds : rounds <= maxRounds) :
    finiteHorizonBadEvent rounds initialBad successorBad ⊆
      finiteHorizonBadEvent maxRounds initialBad successorBad := by
  intro trajectory htrajectory
  rw [finiteHorizonBadEvent] at htrajectory ⊢
  rcases Set.mem_iUnion.mp htrajectory with ⟨round, hround⟩
  refine Set.mem_iUnion.mpr ⟨⟨round, lt_of_lt_of_le round.isLt hrounds⟩, ?_⟩
  simpa using hround

end HeterogeneousAdaptiveStochasticEpisodeBatchSource

namespace AdaptiveStochasticSampledEmpiricalOptimisticSource

/-- The actual self-consistent model-confidence event at a prefix is contained
in the corresponding event at every larger deterministic horizon. -/
theorem selfConsistentScheduledCausalModelBadEvent_mono
    (mdp : MDP State Action) (initialState : Measure State)
    [IsProbabilityMeasure initialState]
    (rewardSource : mdp.MeanCompatibleRewardKernel)
    (initialTable : DeterministicMarkovPolicyTable mdp)
    (defaultState : State) (varianceProxy : NNReal)
    (baseVisitFloor : Real) {rounds maxRounds : Nat}
    (hrounds : rounds <= maxRounds) :
    selfConsistentScheduledCausalModelBadEvent mdp initialState rewardSource
        initialTable defaultState varianceProxy baseVisitFloor rounds ⊆
      selfConsistentScheduledCausalModelBadEvent mdp initialState rewardSource
        initialTable defaultState varianceProxy baseVisitFloor maxRounds := by
  dsimp [selfConsistentScheduledCausalModelBadEvent,
    HeterogeneousAdaptiveStochasticEpisodeBatchSource.adaptiveAllCoordinateEmpiricalModelBadEvent]
  exact HeterogeneousAdaptiveStochasticEpisodeBatchSource.finiteHorizonBadEvent_mono
    hrounds

/-- Equal allocation of one global return confidence budget over the possible
positive stopped prefixes. -/
noncomputable def selfConsistentScheduledNaturalCausalBoundedStoppingEqualReturnShare
    (maxRounds : Nat) (returnDelta : Real) : Real :=
  returnDelta / ((Finset.Icc 1 maxRounds).card : Real)

/-- A positive deterministic horizon has at least one positive prefix. -/
theorem selfConsistentScheduledNaturalCausalPositivePrefixIndex_nonempty
    (maxRounds : Nat) (hmaxRounds : 0 < maxRounds) :
    (Finset.Icc 1 maxRounds).Nonempty := by
  exact ⟨1, Finset.mem_Icc.mpr ⟨le_rfl, hmaxRounds⟩⟩

/-- The equal return share is positive and at most one. -/
theorem selfConsistentScheduledNaturalCausalBoundedStoppingEqualReturnShare_spec
    (maxRounds : Nat) (hmaxRounds : 0 < maxRounds)
    (returnDelta : Real) (hreturnDelta : 0 < returnDelta)
    (hreturnDelta_le_one : returnDelta <= 1) :
    0 < selfConsistentScheduledNaturalCausalBoundedStoppingEqualReturnShare
          maxRounds returnDelta ∧
      selfConsistentScheduledNaturalCausalBoundedStoppingEqualReturnShare
          maxRounds returnDelta <= 1 := by
  have hindex :=
    selfConsistentScheduledNaturalCausalPositivePrefixIndex_nonempty
      maxRounds hmaxRounds
  have hcardNat : 0 < (Finset.Icc 1 maxRounds).card :=
    Finset.card_pos.mpr hindex
  have hcardReal : 0 < ((Finset.Icc 1 maxRounds).card : Real) :=
    Nat.cast_pos.mpr hcardNat
  have hcardOne : (1 : Real) <= ((Finset.Icc 1 maxRounds).card : Real) := by
    exact_mod_cast hcardNat
  constructor
  · exact div_pos hreturnDelta hcardReal
  · exact (div_le_one hcardReal).2 (hreturnDelta_le_one.trans hcardOne)

/-- Finite window containing only the return-deviation events at the possible
positive stopped prefixes. -/
noncomputable def selfConsistentScheduledNaturalCausalBoundedStoppingReturnBadEventWindow
    (mdp : MDP State Action) (initialState : Measure State)
    [IsProbabilityMeasure initialState]
    (rewardSource : mdp.MeanCompatibleRewardKernel)
    (initialTable : DeterministicMarkovPolicyTable mdp)
    (defaultState : State) (varianceProxy : NNReal)
    (baseVisitFloor : Real) (maxRounds : Nat) (returnDelta : Real) :
    Set (HeterogeneousStochasticEpisodeBatchTrajectory mdp
      (fun t =>
        AdaptiveStochasticEpisodeBatchSource.selfConsistentScheduledEpisodes
          mdp varianceProxy baseVisitFloor t)) :=
  ⋃ rounds ∈ Finset.Icc 1 maxRounds,
    selfConsistentScheduledNaturalCausalCumulativeReturnBadEvent mdp
      initialState rewardSource initialTable defaultState varianceProxy
        baseVisitFloor rounds
          (selfConsistentScheduledNaturalCausalBoundedStoppingEqualReturnShare
            maxRounds returnDelta)

/-- The finite return-only window is ambient measurable. -/
theorem measurableSet_selfConsistentScheduledNaturalCausalBoundedStoppingReturnBadEventWindow
    (mdp : MDP State Action) (initialState : Measure State)
    [IsProbabilityMeasure initialState]
    (rewardSource : mdp.MeanCompatibleRewardKernel)
    (initialTable : DeterministicMarkovPolicyTable mdp)
    (defaultState : State) (varianceProxy : NNReal)
    (baseVisitFloor : Real) (maxRounds : Nat) (returnDelta : Real) :
    MeasurableSet
      (selfConsistentScheduledNaturalCausalBoundedStoppingReturnBadEventWindow
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor maxRounds returnDelta) := by
  exact (Finset.Icc 1 maxRounds).measurableSet_biUnion fun rounds _ =>
    measurableSet_selfConsistentScheduledNaturalCausalCumulativeReturnBadEvent
      mdp initialState rewardSource initialTable defaultState varianceProxy
        baseVisitFloor rounds
          (selfConsistentScheduledNaturalCausalBoundedStoppingEqualReturnShare
            maxRounds returnDelta)

/-- Equal allocation bounds the finite return-deviation window by the one
global return confidence budget. -/
theorem selfConsistentScheduledCausalSource_trajectoryMeasure_boundedStoppingReturnBadEventWindow_le
    (mdp : MDP State Action) (initialState : Measure State)
    [IsProbabilityMeasure initialState]
    [StandardBorelSpace State] [StandardBorelSpace Action]
    (rewardSource : mdp.MeanCompatibleRewardKernel)
    (varianceProxy : NNReal)
    (law : rewardSource.UniformSubgaussianRewardLaw varianceProxy)
    (initialTable : DeterministicMarkovPolicyTable mdp)
    (defaultState : State) (baseVisitFloor : Real)
    (hrewardBound : forall state action, |mdp.reward state action| <= 1)
    (hhorizon : 0 < mdp.horizon)
    (maxRounds : Nat) (hmaxRounds : 0 < maxRounds)
    (returnDelta : Real) (hreturnDelta : 0 < returnDelta)
    (hreturnDelta_le_one : returnDelta <= 1) :
    let source := selfConsistentScheduledCausalSource mdp initialState
      rewardSource initialTable defaultState varianceProxy baseVisitFloor
    source.trajectoryMeasure
        (selfConsistentScheduledNaturalCausalBoundedStoppingReturnBadEventWindow
          mdp initialState rewardSource initialTable defaultState varianceProxy
            baseVisitFloor maxRounds returnDelta) <=
      ENNReal.ofReal returnDelta := by
  dsimp only
  let source := selfConsistentScheduledCausalSource mdp initialState
    rewardSource initialTable defaultState varianceProxy baseVisitFloor
  have hindex :=
    selfConsistentScheduledNaturalCausalPositivePrefixIndex_nonempty
      maxRounds hmaxRounds
  have hshare :=
    selfConsistentScheduledNaturalCausalBoundedStoppingEqualReturnShare_spec
      maxRounds hmaxRounds returnDelta hreturnDelta hreturnDelta_le_one
  have htail : forall rounds, rounds ∈ Finset.Icc 1 maxRounds ->
      source.trajectoryMeasure
          (selfConsistentScheduledNaturalCausalCumulativeReturnBadEvent mdp
            initialState rewardSource initialTable defaultState varianceProxy
              baseVisitFloor rounds
                (selfConsistentScheduledNaturalCausalBoundedStoppingEqualReturnShare
                  maxRounds returnDelta)) <=
        ENNReal.ofReal
          (returnDelta / ((Finset.Icc 1 maxRounds).card : Real)) := by
    intro rounds hrounds
    have hrounds_pos : 0 < rounds := (Finset.mem_Icc.mp hrounds).1
    simpa [source,
      selfConsistentScheduledNaturalCausalBoundedStoppingEqualReturnShare] using
      selfConsistentScheduledCausalSource_trajectoryMeasure_naturalCumulativeReturnBadEvent_le
        mdp initialState rewardSource varianceProxy law initialTable defaultState
          baseVisitFloor hrewardBound hhorizon rounds hrounds_pos
            (selfConsistentScheduledNaturalCausalBoundedStoppingEqualReturnShare
              maxRounds returnDelta) hshare.1 hshare.2
  simpa [source,
    selfConsistentScheduledNaturalCausalBoundedStoppingReturnBadEventWindow] using
    ProbabilityUnionBound.measure_biUnion_finset_le_of_uniform
      source.trajectoryMeasure (Finset.Icc 1 maxRounds) hindex returnDelta
        (fun rounds =>
          selfConsistentScheduledNaturalCausalCumulativeReturnBadEvent mdp
            initialState rewardSource initialTable defaultState varianceProxy
              baseVisitFloor rounds
                (selfConsistentScheduledNaturalCausalBoundedStoppingEqualReturnShare
                  maxRounds returnDelta)) htail

/-- One horizon model-confidence event joined with the finite return-only
window for all possible positive stopped prefixes. -/
noncomputable def selfConsistentScheduledNaturalCausalBoundedStoppingSingleModelReturnBadEvent
    (mdp : MDP State Action) (initialState : Measure State)
    [IsProbabilityMeasure initialState]
    (rewardSource : mdp.MeanCompatibleRewardKernel)
    (initialTable : DeterministicMarkovPolicyTable mdp)
    (defaultState : State) (varianceProxy : NNReal)
    (baseVisitFloor : Real) (maxRounds : Nat) (returnDelta : Real) :
    Set (HeterogeneousStochasticEpisodeBatchTrajectory mdp
      (fun t =>
        AdaptiveStochasticEpisodeBatchSource.selfConsistentScheduledEpisodes
          mdp varianceProxy baseVisitFloor t)) :=
  selfConsistentScheduledCausalModelBadEvent mdp initialState rewardSource
      initialTable defaultState varianceProxy baseVisitFloor maxRounds ∪
    selfConsistentScheduledNaturalCausalBoundedStoppingReturnBadEventWindow
      mdp initialState rewardSource initialTable defaultState varianceProxy
        baseVisitFloor maxRounds returnDelta

/-- Every positive fixed-prefix average-regret violation with the equal return
share lies in the single horizon model event or the return-only window. -/
theorem selfConsistentScheduledNaturalCausalPositivePrefixAverageRealizedBehaviorRegretViolationWindow_subset_boundedStoppingSingleModelReturnBadEvent
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
    (maxRounds : Nat) (returnDelta : Real) :
    selfConsistentScheduledNaturalCausalPositivePrefixAverageRealizedBehaviorRegretViolationWindow
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor maxRounds
            (fun _ =>
              selfConsistentScheduledNaturalCausalBoundedStoppingEqualReturnShare
                maxRounds returnDelta) ⊆
      selfConsistentScheduledNaturalCausalBoundedStoppingSingleModelReturnBadEvent
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor maxRounds returnDelta := by
  intro trajectory htrajectory
  rw [selfConsistentScheduledNaturalCausalPositivePrefixAverageRealizedBehaviorRegretViolationWindow]
    at htrajectory
  rcases Set.mem_iUnion.mp htrajectory with ⟨rounds, htrajectory⟩
  rcases Set.mem_iUnion.mp htrajectory with ⟨hrounds, hviolation⟩
  have hrange := Finset.mem_Icc.mp hrounds
  have hfixed :=
    selfConsistentScheduledNaturalCausalAverageRealizedBehaviorRegretLogarithmicViolationSet_subset_modelReturnBadEvent
      mdp initialState rewardSource varianceProxy hvarianceProxy law initialTable
        defaultState support baseVisitFloor hbaseFloor hrewardBound hhorizon
          hbaseVisitFloor rounds hrange.1
            (selfConsistentScheduledNaturalCausalBoundedStoppingEqualReturnShare
              maxRounds returnDelta) hviolation
  rw [selfConsistentScheduledNaturalCausalModelReturnBadEvent] at hfixed
  rw [selfConsistentScheduledNaturalCausalBoundedStoppingSingleModelReturnBadEvent]
  rcases hfixed with hmodel | hreturn
  · exact Or.inl
      (selfConsistentScheduledCausalModelBadEvent_mono mdp initialState
        rewardSource initialTable defaultState varianceProxy baseVisitFloor
          hrange.2 hmodel)
  · apply Or.inr
    rw [selfConsistentScheduledNaturalCausalBoundedStoppingReturnBadEventWindow]
    refine Set.mem_iUnion.mpr ⟨rounds, ?_⟩
    exact Set.mem_iUnion.mpr ⟨hrounds, hreturn⟩

/-- The single-model return event is measurable and is charged by one horizon
model budget plus the one global return budget. -/
theorem selfConsistentScheduledCausalSource_trajectoryMeasure_boundedStoppingSingleModelReturnBadEvent_le
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
    (maxRounds : Nat) (hmaxRounds : 0 < maxRounds)
    (returnDelta : Real) (hreturnDelta : 0 < returnDelta)
    (hreturnDelta_le_one : returnDelta <= 1) :
    let source := selfConsistentScheduledCausalSource mdp initialState
      rewardSource initialTable defaultState varianceProxy baseVisitFloor
    let event :=
      selfConsistentScheduledNaturalCausalBoundedStoppingSingleModelReturnBadEvent
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor maxRounds returnDelta
    MeasurableSet event ∧
      source.trajectoryMeasure event <=
        selfConsistentScheduledCausalModelFailureBudget mdp maxRounds +
          ENNReal.ofReal returnDelta := by
  dsimp only
  let source := selfConsistentScheduledCausalSource mdp initialState
    rewardSource initialTable defaultState varianceProxy baseVisitFloor
  let modelEvent := selfConsistentScheduledCausalModelBadEvent mdp initialState
    rewardSource initialTable defaultState varianceProxy baseVisitFloor maxRounds
  let returnWindow :=
    selfConsistentScheduledNaturalCausalBoundedStoppingReturnBadEventWindow
      mdp initialState rewardSource initialTable defaultState varianceProxy
        baseVisitFloor maxRounds returnDelta
  have hmodel :=
    selfConsistentScheduledCausalSource_trajectoryMeasure_allCoordinateConfidence_optimism_and_recommendedExpectedRegret
      mdp initialState rewardSource varianceProxy hvarianceProxy law initialTable
        defaultState support baseVisitFloor hbaseFloor hrewardBound hhorizon
          hbaseVisitFloor maxRounds
  have hreturnMeasurable : MeasurableSet returnWindow := by
    simpa [returnWindow] using
      measurableSet_selfConsistentScheduledNaturalCausalBoundedStoppingReturnBadEventWindow
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor maxRounds returnDelta
  have hreturnTail : source.trajectoryMeasure returnWindow <=
      ENNReal.ofReal returnDelta := by
    simpa [source, returnWindow] using
      selfConsistentScheduledCausalSource_trajectoryMeasure_boundedStoppingReturnBadEventWindow_le
        mdp initialState rewardSource varianceProxy law initialTable defaultState
          baseVisitFloor hrewardBound hhorizon maxRounds hmaxRounds returnDelta
            hreturnDelta hreturnDelta_le_one
  refine ⟨?_, ?_⟩
  · simpa [selfConsistentScheduledNaturalCausalBoundedStoppingSingleModelReturnBadEvent,
      modelEvent, returnWindow] using hmodel.1.union hreturnMeasurable
  · have hunion : source.trajectoryMeasure (modelEvent ∪ returnWindow) <=
        source.trajectoryMeasure modelEvent +
          source.trajectoryMeasure returnWindow :=
      measure_union_le modelEvent returnWindow
    have hsum := add_le_add hmodel.2.1 hreturnTail
    simpa [selfConsistentScheduledNaturalCausalBoundedStoppingSingleModelReturnBadEvent,
      modelEvent, returnWindow, source] using hunion.trans hsum

/-- The stopped violation is contained in the sharper single-model return
event. -/
theorem selfConsistentScheduledNaturalCausalBoundedStoppingTimeAverageRealizedBehaviorRegretViolationSet_subset_singleModelReturnBadEvent
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
    (tau : HeterogeneousStochasticEpisodeBatchTrajectory mdp
      (fun t =>
        AdaptiveStochasticEpisodeBatchSource.selfConsistentScheduledEpisodes
          mdp varianceProxy baseVisitFloor t) -> WithTop Nat)
    (maxRounds : Nat)
    (htau_pos : forall trajectory, (1 : WithTop Nat) <= tau trajectory)
    (htau_le : forall trajectory, tau trajectory <= (maxRounds : WithTop Nat))
    (returnDelta : Real) :
    selfConsistentScheduledNaturalCausalBoundedStoppingTimeAverageRealizedBehaviorRegretViolationSet
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor
            (fun _ =>
              selfConsistentScheduledNaturalCausalBoundedStoppingEqualReturnShare
                maxRounds returnDelta) tau ⊆
      selfConsistentScheduledNaturalCausalBoundedStoppingSingleModelReturnBadEvent
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor maxRounds returnDelta := by
  exact
    (selfConsistentScheduledNaturalCausalBoundedStoppingTimeAverageRealizedBehaviorRegretViolationSet_subset_positivePrefixWindow
      mdp initialState rewardSource initialTable defaultState varianceProxy
        baseVisitFloor
          (fun _ =>
            selfConsistentScheduledNaturalCausalBoundedStoppingEqualReturnShare
              maxRounds returnDelta) tau maxRounds htau_pos htau_le).trans
      (selfConsistentScheduledNaturalCausalPositivePrefixAverageRealizedBehaviorRegretViolationWindow_subset_boundedStoppingSingleModelReturnBadEvent
        mdp initialState rewardSource varianceProxy hvarianceProxy law initialTable
          defaultState support baseVisitFloor hbaseFloor hrewardBound hhorizon
            hbaseVisitFloor maxRounds returnDelta)

/-
Terminal bounded-stopping route with one charged model-confidence event.
The stopping-time premise proves filtered measurability; the probability bound
is inherited from pathwise finite-prefix containment.
-/
theorem selfConsistentScheduledCausalSource_boundedStoppingTimeSingleModelEventHighProbabilityAverageRealizedBehaviorRegret
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
    (tau : HeterogeneousStochasticEpisodeBatchTrajectory mdp
      (fun t =>
        AdaptiveStochasticEpisodeBatchSource.selfConsistentScheduledEpisodes
          mdp varianceProxy baseVisitFloor t) -> WithTop Nat)
    (htau : IsStoppingTime
      (selfConsistentScheduledNaturalCausalTrajectoryFiltration mdp initialState
        rewardSource initialTable defaultState varianceProxy baseVisitFloor) tau)
    (maxRounds : Nat) (hmaxRounds : 0 < maxRounds)
    (htau_pos : forall trajectory, (1 : WithTop Nat) <= tau trajectory)
    (htau_le : forall trajectory, tau trajectory <= (maxRounds : WithTop Nat))
    (returnDelta : Real) (hreturnDelta : 0 < returnDelta)
    (hreturnDelta_le_one : returnDelta <= 1) :
    let source := selfConsistentScheduledCausalSource mdp initialState
      rewardSource initialTable defaultState varianceProxy baseVisitFloor
    let returnDeltaAt := fun _ : Nat =>
      selfConsistentScheduledNaturalCausalBoundedStoppingEqualReturnShare
        maxRounds returnDelta
    let stoppedViolation :=
      selfConsistentScheduledNaturalCausalBoundedStoppingTimeAverageRealizedBehaviorRegretViolationSet
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor returnDeltaAt tau
    let event :=
      selfConsistentScheduledNaturalCausalBoundedStoppingSingleModelReturnBadEvent
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor maxRounds returnDelta
    let failureBudget :=
      selfConsistentScheduledCausalModelFailureBudget mdp maxRounds +
        ENNReal.ofReal returnDelta
    MeasurableSet[
        selfConsistentScheduledNaturalCausalTrajectoryFiltration mdp initialState
          rewardSource initialTable defaultState varianceProxy baseVisitFloor
            maxRounds] stoppedViolation ∧
      MeasurableSet event ∧
      stoppedViolation ⊆ event ∧
      source.trajectoryMeasure event <= failureBudget ∧
      source.trajectoryMeasure stoppedViolation <= failureBudget ∧
      (failureBudget < 1 -> source.trajectoryMeasure stoppedViolation < 1) ∧
      forall trajectory, trajectory ∉ event ->
        selfConsistentScheduledNaturalCausalStoppedAverageRealizedBehaviorRegret
            mdp initialState rewardSource initialTable defaultState varianceProxy
              baseVisitFloor tau trajectory <=
          selfConsistentScheduledNaturalCausalStoppedRealizedAverageLogarithmicRate
            mdp initialState rewardSource initialTable defaultState varianceProxy
              baseVisitFloor returnDeltaAt tau trajectory := by
  dsimp only
  let source := selfConsistentScheduledCausalSource mdp initialState
    rewardSource initialTable defaultState varianceProxy baseVisitFloor
  let returnDeltaAt := fun _ : Nat =>
    selfConsistentScheduledNaturalCausalBoundedStoppingEqualReturnShare
      maxRounds returnDelta
  let stoppedViolation :=
    selfConsistentScheduledNaturalCausalBoundedStoppingTimeAverageRealizedBehaviorRegretViolationSet
      mdp initialState rewardSource initialTable defaultState varianceProxy
        baseVisitFloor returnDeltaAt tau
  let event :=
    selfConsistentScheduledNaturalCausalBoundedStoppingSingleModelReturnBadEvent
      mdp initialState rewardSource initialTable defaultState varianceProxy
        baseVisitFloor maxRounds returnDelta
  let failureBudget :=
    selfConsistentScheduledCausalModelFailureBudget mdp maxRounds +
      ENNReal.ofReal returnDelta
  have hstoppedMeasurable :
      MeasurableSet[
        selfConsistentScheduledNaturalCausalTrajectoryFiltration mdp initialState
          rewardSource initialTable defaultState varianceProxy baseVisitFloor
            maxRounds] stoppedViolation := by
    simpa [stoppedViolation, returnDeltaAt] using
      measurableSet_selfConsistentScheduledNaturalCausalBoundedStoppingTimeAverageRealizedBehaviorRegretViolationSet
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor
            (fun _ : Nat =>
              selfConsistentScheduledNaturalCausalBoundedStoppingEqualReturnShare
                maxRounds returnDelta) tau htau maxRounds htau_le
  have hevent :=
    selfConsistentScheduledCausalSource_trajectoryMeasure_boundedStoppingSingleModelReturnBadEvent_le
      mdp initialState rewardSource varianceProxy hvarianceProxy law initialTable
        defaultState support baseVisitFloor hbaseFloor hrewardBound hhorizon
          hbaseVisitFloor maxRounds hmaxRounds returnDelta hreturnDelta
            hreturnDelta_le_one
  have heventMeasurable : MeasurableSet event := by
    simpa [event] using hevent.1
  have heventTail : source.trajectoryMeasure event <= failureBudget := by
    simpa [source, event, failureBudget] using hevent.2
  have hsubset : stoppedViolation ⊆ event := by
    simpa [stoppedViolation, returnDeltaAt, event] using
      selfConsistentScheduledNaturalCausalBoundedStoppingTimeAverageRealizedBehaviorRegretViolationSet_subset_singleModelReturnBadEvent
        mdp initialState rewardSource varianceProxy hvarianceProxy law initialTable
          defaultState support baseVisitFloor hbaseFloor hrewardBound hhorizon
            hbaseVisitFloor tau maxRounds htau_pos htau_le returnDelta
  have hstoppedTail : source.trajectoryMeasure stoppedViolation <= failureBudget :=
    (measure_mono hsubset).trans heventTail
  refine And.intro hstoppedMeasurable ?_
  refine And.intro heventMeasurable ?_
  refine And.intro hsubset ?_
  refine And.intro heventTail ?_
  refine And.intro hstoppedTail ?_
  refine And.intro (fun hbudget => hstoppedTail.trans_lt hbudget) ?_
  intro trajectory htrajectory
  have hnotStopped : trajectory ∉ stoppedViolation := fun h =>
    htrajectory (hsubset h)
  apply le_of_not_gt
  intro hlt
  exact hnotStopped (by simpa [stoppedViolation] using hlt)

end AdaptiveStochasticSampledEmpiricalOptimisticSource

end BanditRLProof.FiniteHorizonRL
