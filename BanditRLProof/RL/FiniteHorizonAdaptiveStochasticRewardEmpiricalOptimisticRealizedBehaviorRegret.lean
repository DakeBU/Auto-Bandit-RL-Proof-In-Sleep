import BanditRLProof.RL.FiniteHorizonAdaptiveStochasticRewardEmpiricalOptimisticProjection
import BanditRLProof.RL.FiniteHorizonAdaptiveStochasticRewardRealizedBehaviorRegret
import BanditRLProof.RL.FiniteHorizonAdaptiveCumulativeExploratoryBehaviorRegret
import BanditRLProof.RL.FiniteHorizonAdaptiveEmpiricalOptimisticOccupancyEnvelope

/-!
# Concrete stochastic empirical-optimistic realized behavior regret

This module combines the concrete stochastic known-mean empirical-transition
source with the global sampled-return transport.  The count/optimism event and
the sampled-return event retain separate confidence budgets.  The expected
regret of the exploratory behavior is charged explicitly against the projected
recommended policy before the realized-return deviation is added.

The result remains a fixed-window theorem for successor batches.  It does not
estimate stochastic reward means, include the initial batch in realized regret,
or claim an anytime, minimax, or complete UCB-VI result.
-/

open MeasureTheory
open scoped ENNReal ProbabilityTheory BigOperators

universe u v

namespace BanditRLProof
namespace FiniteHorizonRL

variable {State : Type u} {Action : Type v}
    [MeasurableSpace State] [MeasurableSpace Action]
    [Fintype State] [Fintype Action]
    [DecidableEq State] [DecidableEq Action]
    [MeasurableSingletonClass State] [MeasurableSingletonClass Action]
    [Nonempty State] [Nonempty Action]

namespace AdaptiveStochasticEpisodeBatchSource

omit [DecidableEq State] [DecidableEq Action]
    [MeasurableSingletonClass State] [MeasurableSingletonClass Action]
    [Nonempty State] in
/--
Generic two-budget version of the expected-to-realized successor-regret
transport.  The caller's event keeps `countDelta`, while the return event uses
`returnDelta`.
-/
theorem trajectoryMeasure_expected_to_realized_successor_average_regret_transport_two_delta
    {mdp : MDP State Action} {initialState : Measure State}
    [IsProbabilityMeasure initialState] {episodes : Nat}
    [StandardBorelSpace State] [StandardBorelSpace Action]
    [StandardBorelSpace (StochasticEpisodeBatch mdp episodes)]
    [Nonempty (StochasticEpisodeBatch mdp episodes)]
    [StandardBorelSpace (StochasticEpisodeBatchTrajectory mdp episodes)]
    (source : AdaptiveStochasticEpisodeBatchSource mdp initialState episodes)
    [source.GlobalReturnMeasurability]
    (rounds : Nat) (hrounds : 0 < rounds) (hepisodes : 0 < episodes)
    (rewardBound rewardVarianceProxy : NNReal)
    (hrewardBound : forall state action,
      |mdp.reward state action| <= (rewardBound : Real))
    (law : source.rewardSource.UniformSubgaussianRewardLaw rewardVarianceProxy)
    (htotal : 0 <
      ((cumulativeSuccessorGlobalReturnVarianceProxy mdp rounds episodes
        rewardBound rewardVarianceProxy : NNReal) : Real))
    (countDelta returnDelta : Real)
    (hreturnDelta : 0 < returnDelta) (hreturnDelta_le_one : returnDelta <= 1)
    (countBadEvent : Set (StochasticEpisodeBatchTrajectory mdp episodes))
    (expectedBound : Real)
    (Good : StochasticEpisodeBatchTrajectory mdp episodes -> Prop)
    (hcountMeasurable : MeasurableSet countBadEvent)
    (hcountTail : source.trajectoryMeasure countBadEvent <=
      ENNReal.ofReal countDelta)
    (hcountGood : forall trajectory, trajectory ∉ countBadEvent ->
      Good trajectory /\
        source.successorExpectedAverageRegret trajectory rounds <= expectedBound) :
    let returnBadEvent := source.successorGlobalReturnDeviationBadEvent
      rounds rewardBound rewardVarianceProxy returnDelta
    let combinedBadEvent := countBadEvent ∪ returnBadEvent
    MeasurableSet combinedBadEvent /\
      source.trajectoryMeasure combinedBadEvent <=
        ENNReal.ofReal countDelta + ENNReal.ofReal returnDelta /\
      forall trajectory, trajectory ∉ combinedBadEvent ->
        Good trajectory /\
          source.realizedSuccessorAverageRegret trajectory rounds <=
            expectedBound +
              Concentration.subGaussianSumConfidenceRadius
                  (cumulativeSuccessorGlobalReturnVarianceProxy
                    mdp rounds episodes rewardBound rewardVarianceProxy)
                  returnDelta /
                ((episodes : Real) * (rounds : Real)) := by
  let returnBadEvent := source.successorGlobalReturnDeviationBadEvent
    rounds rewardBound rewardVarianceProxy returnDelta
  let combinedBadEvent := countBadEvent ∪ returnBadEvent
  have hreturnMeasurable : MeasurableSet returnBadEvent := by
    simpa [returnBadEvent] using
      source.measurableSet_successorGlobalReturnDeviationBadEvent
        rounds rewardBound rewardVarianceProxy returnDelta
  have hreturnTail : source.trajectoryMeasure returnBadEvent <=
      ENNReal.ofReal returnDelta := by
    simpa [returnBadEvent] using
      source.trajectoryMeasure_successorGlobalReturnDeviationBadEvent_le
        rounds rewardBound rewardVarianceProxy hrewardBound law htotal
        returnDelta hreturnDelta hreturnDelta_le_one
  refine ⟨hcountMeasurable.union hreturnMeasurable, ?_, ?_⟩
  · exact (measure_union_le countBadEvent returnBadEvent).trans
      (add_le_add hcountTail hreturnTail)
  · intro trajectory htrajectory
    have hnotCount : trajectory ∉ countBadEvent := by
      exact fun hmem => htrajectory (Set.mem_union_left returnBadEvent hmem)
    have hnotReturn : trajectory ∉ returnBadEvent := by
      exact fun hmem => htrajectory (Set.mem_union_right countBadEvent hmem)
    have hgood := hcountGood trajectory hnotCount
    refine ⟨hgood.1, ?_⟩
    have hdeviation :
        |source.cumulativeSuccessorGlobalReturnDeviation rounds trajectory| <
          Concentration.subGaussianSumConfidenceRadius
            (cumulativeSuccessorGlobalReturnVarianceProxy
              mdp rounds episodes rewardBound rewardVarianceProxy)
            returnDelta := by
      exact lt_of_not_ge (by simpa [returnBadEvent,
        successorGlobalReturnDeviationBadEvent] using hnotReturn)
    have hdenom : 0 < (episodes : Real) * (rounds : Real) := by
      positivity
    rw [source.realizedSuccessorAverageRegret_eq_expected_sub_deviation
      trajectory rounds hrounds hepisodes]
    have hnoise :
        -source.cumulativeSuccessorGlobalReturnDeviation rounds trajectory /
            ((episodes : Real) * (rounds : Real)) <=
          Concentration.subGaussianSumConfidenceRadius
              (cumulativeSuccessorGlobalReturnVarianceProxy
                mdp rounds episodes rewardBound rewardVarianceProxy)
              returnDelta /
            ((episodes : Real) * (rounds : Real)) := by
      apply div_le_div_of_nonneg_right _ hdenom.le
      exact (neg_le_abs _).trans hdeviation.le
    calc
      source.successorExpectedAverageRegret trajectory rounds -
          source.cumulativeSuccessorGlobalReturnDeviation rounds trajectory /
            ((episodes : Real) * (rounds : Real)) =
        source.successorExpectedAverageRegret trajectory rounds +
          (-source.cumulativeSuccessorGlobalReturnDeviation rounds trajectory /
            ((episodes : Real) * (rounds : Real))) := by ring
      _ <= source.successorExpectedAverageRegret trajectory rounds +
          Concentration.subGaussianSumConfidenceRadius
              (cumulativeSuccessorGlobalReturnVarianceProxy
                mdp rounds episodes rewardBound rewardVarianceProxy)
              returnDelta /
            ((episodes : Real) * (rounds : Real)) := add_le_add le_rfl hnoise
      _ <= expectedBound +
          Concentration.subGaussianSumConfidenceRadius
              (cumulativeSuccessorGlobalReturnVarianceProxy
                mdp rounds episodes rewardBound rewardVarianceProxy)
              returnDelta /
            ((episodes : Real) * (rounds : Real)) := add_le_add hgood.2 le_rfl

end AdaptiveStochasticEpisodeBatchSource

namespace AdaptiveStochasticEmpiricalOptimisticSource

/-- Sum of expected regrets of the projected empirical-optimistic exploratory behaviors. -/
noncomputable def projectedExploratoryBehaviorExpectedRegret
    {mdp : MDP State Action} {initialState : Measure State}
    [IsProbabilityMeasure initialState] {episodes : Nat}
    (trajectory : EpisodeBatchTrajectory mdp episodes)
    (defaultState : State) (transitionBonus : Real)
    (explorationRate : NNReal) (hexplorationRate : explorationRate <= 1)
    (rounds : Nat) : Real :=
  ∑ round : Fin rounds,
    (((trajectory round).transitionCountSummary.optimisticPolicyTable
        mdp defaultState transitionBonus).exploratoryPolicy
          explorationRate hexplorationRate).expectedRegret initialState

/-- Average expected regret of the projected exploratory behaviors. -/
noncomputable def projectedAverageExploratoryBehaviorExpectedRegret
    {mdp : MDP State Action} {initialState : Measure State}
    [IsProbabilityMeasure initialState] {episodes : Nat}
    (trajectory : EpisodeBatchTrajectory mdp episodes)
    (defaultState : State) (transitionBonus : Real)
    (explorationRate : NNReal) (hexplorationRate : explorationRate <= 1)
    (rounds : Nat) : Real :=
  projectedExploratoryBehaviorExpectedRegret
      (initialState := initialState) trajectory defaultState transitionBonus
      explorationRate hexplorationRate rounds /
    (rounds : Real)

/-- Exploratory behavior regret is recommendation regret plus one charge per round. -/
theorem projectedExploratoryBehaviorExpectedRegret_le
    {mdp : MDP State Action} {initialState : Measure State}
    [IsProbabilityMeasure initialState] {episodes : Nat}
    (trajectory : EpisodeBatchTrajectory mdp episodes)
    (defaultState : State) (transitionBonus : Real)
    (explorationRate : NNReal) (hexplorationRate : explorationRate <= 1)
    (rewardBound : Real)
    (hrewardBound : forall state action, |mdp.reward state action| <= rewardBound)
    (rounds : Nat) :
    projectedExploratoryBehaviorExpectedRegret
        (initialState := initialState) trajectory defaultState transitionBonus
        explorationRate hexplorationRate rounds <=
      adaptiveEmpiricalOptimisticRecommendedExpectedRegret
          (initialState := initialState) trajectory defaultState transitionBonus rounds +
        (rounds : Real) *
          exploratoryBehaviorRegretCharge mdp explorationRate rewardBound := by
  unfold projectedExploratoryBehaviorExpectedRegret
    adaptiveEmpiricalOptimisticRecommendedExpectedRegret
  calc
    (∑ round : Fin rounds,
        (((trajectory round).transitionCountSummary.optimisticPolicyTable
            mdp defaultState transitionBonus).exploratoryPolicy
              explorationRate hexplorationRate).expectedRegret initialState) <=
      ∑ round : Fin rounds,
        ((adaptiveEmpiricalOptimisticPlanAt
            (mdp := mdp) (episodes := episodes) trajectory defaultState
              transitionBonus round).optimisticPolicy.expectedRegret initialState +
          exploratoryBehaviorRegretCharge mdp explorationRate rewardBound) := by
      apply Finset.sum_le_sum
      intro round _hround
      let table := (trajectory round).transitionCountSummary.optimisticPolicyTable
        mdp defaultState transitionBonus
      have htransport :=
        table.exploratoryPolicy_expectedRegret_le_toMarkovPolicy_expectedRegret_add_charge
          initialState explorationRate hexplorationRate rewardBound hrewardBound
      simpa [table, adaptiveEmpiricalOptimisticPlanAt,
        exploratoryBehaviorRegretCharge,
        TransitionCountSummary.optimisticPolicyTable_toMarkovPolicy] using htransport
    _ = (∑ round : Fin rounds,
          (adaptiveEmpiricalOptimisticPlanAt
            (mdp := mdp) (episodes := episodes) trajectory defaultState
              transitionBonus round).optimisticPolicy.expectedRegret initialState) +
        (rounds : Real) *
          exploratoryBehaviorRegretCharge mdp explorationRate rewardBound := by
      rw [Finset.sum_add_distrib]
      simp

/-- Averaging removes the repeated-round exploration factor. -/
theorem projectedAverageExploratoryBehaviorExpectedRegret_le
    {mdp : MDP State Action} {initialState : Measure State}
    [IsProbabilityMeasure initialState] {episodes : Nat}
    (trajectory : EpisodeBatchTrajectory mdp episodes)
    (defaultState : State) (transitionBonus : Real)
    (explorationRate : NNReal) (hexplorationRate : explorationRate <= 1)
    (rewardBound : Real)
    (hrewardBound : forall state action, |mdp.reward state action| <= rewardBound)
    (rounds : Nat) (hrounds : 0 < rounds) :
    projectedAverageExploratoryBehaviorExpectedRegret
        (initialState := initialState) trajectory defaultState transitionBonus
        explorationRate hexplorationRate rounds <=
      adaptiveEmpiricalOptimisticRecommendedExpectedRegret
          (initialState := initialState) trajectory defaultState transitionBonus rounds /
          (rounds : Real) +
        exploratoryBehaviorRegretCharge mdp explorationRate rewardBound := by
  unfold projectedAverageExploratoryBehaviorExpectedRegret
  have hroundsReal : (0 : Real) < rounds := by exact_mod_cast hrounds
  have hsum := projectedExploratoryBehaviorExpectedRegret_le
    (initialState := initialState) trajectory defaultState transitionBonus
      explorationRate hexplorationRate rewardBound hrewardBound rounds
  calc
    projectedExploratoryBehaviorExpectedRegret
          (initialState := initialState) trajectory defaultState transitionBonus
          explorationRate hexplorationRate rounds /
        (rounds : Real) <=
      (adaptiveEmpiricalOptimisticRecommendedExpectedRegret
          (initialState := initialState) trajectory defaultState transitionBonus rounds +
        (rounds : Real) *
          exploratoryBehaviorRegretCharge mdp explorationRate rewardBound) /
        (rounds : Real) := (div_le_div_iff_of_pos_right hroundsReal).2 hsum
    _ = adaptiveEmpiricalOptimisticRecommendedExpectedRegret
          (initialState := initialState) trajectory defaultState transitionBonus rounds /
          (rounds : Real) +
        exploratoryBehaviorRegretCharge mdp explorationRate rewardBound := by
      field_simp

omit [Nonempty State] in
/-- Dynamic global-return measurability for any finite exploratory table selector. -/
theorem measurable_selectedExploratoryGlobalReturnDeviation
    {mdp : MDP State Action} {initialState : Measure State}
    {episodes : Nat} {History : Type*} [MeasurableSpace History]
    (selector : History -> DeterministicMarkovPolicyTable mdp)
    (hselector : Measurable selector)
    (explorationRate : NNReal) (hexplorationRate : explorationRate <= 1) :
    Measurable fun pair : History × StochasticEpisodeBatch mdp episodes =>
      mdp.globalSampledCumulativeReturnDeviationSum
        ((selector pair.1).exploratoryPolicy explorationRate hexplorationRate)
        initialState episodes pair.2 := by
  classical
  let statistic := fun table : DeterministicMarkovPolicyTable mdp =>
    mdp.globalSampledCumulativeReturnDeviationSum
      (table.exploratoryPolicy explorationRate hexplorationRate)
      initialState episodes
  have hrepresentation :
      (fun pair : History × StochasticEpisodeBatch mdp episodes =>
        mdp.globalSampledCumulativeReturnDeviationSum
          ((selector pair.1).exploratoryPolicy explorationRate hexplorationRate)
          initialState episodes pair.2) =
        fun pair => ∑ table : DeterministicMarkovPolicyTable mdp,
          if selector pair.1 = table then statistic table pair.2 else 0 := by
    funext pair
    simp [statistic]
  rw [hrepresentation]
  exact Finset.measurable_sum Finset.univ fun table _ =>
    Measurable.ite
      ((hselector.comp measurable_fst) (measurableSet_singleton table))
      ((mdp.measurable_globalSampledCumulativeReturnDeviationSum
        (table.exploratoryPolicy explorationRate hexplorationRate)
          initialState episodes).comp measurable_snd)
      measurable_const

/-- The concrete projected-selector source satisfies the global-return regularity contract. -/
noncomputable instance instExploratorySourceGlobalReturnMeasurability
    {mdp : MDP State Action} {initialState : Measure State}
    [IsProbabilityMeasure initialState] {episodes : Nat}
    (rewardSource : mdp.MeanCompatibleRewardKernel)
    (initialTable : DeterministicMarkovPolicyTable mdp)
    (defaultState : State) (transitionBonus : Real)
    (explorationRate : NNReal) (hexplorationRate : explorationRate <= 1) :
    (exploratorySource mdp initialState episodes rewardSource initialTable
      defaultState transitionBonus explorationRate
        hexplorationRate).GlobalReturnMeasurability where
  measurable_successorGlobalReturnDeviation n := by
    exact measurable_selectedExploratoryGlobalReturnDeviation
      (fun history =>
        AdaptiveEmpiricalOptimisticSource.successorTable defaultState
          transitionBonus n
          (MDP.MeanCompatibleRewardKernel.knownRewardEpisodeBatchPrefix
            (mdp := mdp) episodes n history))
      ((AdaptiveEmpiricalOptimisticSource.measurable_successorTable
        defaultState transitionBonus n).comp
          (MDP.MeanCompatibleRewardKernel.measurable_knownRewardEpisodeBatchPrefix
            (mdp := mdp) episodes n))
      explorationRate hexplorationRate

omit [Nonempty State] in
/-- The concrete source's successor policies are the projected exploratory policies. -/
theorem exploratorySource_successorExpectedCumulativeRegret_eq_projected
    {mdp : MDP State Action} {initialState : Measure State}
    [IsProbabilityMeasure initialState] {episodes : Nat}
    (rewardSource : mdp.MeanCompatibleRewardKernel)
    (initialTable : DeterministicMarkovPolicyTable mdp)
    (defaultState : State) (transitionBonus : Real)
    (explorationRate : NNReal) (hexplorationRate : explorationRate <= 1)
    (trajectory : StochasticEpisodeBatchTrajectory mdp episodes) (rounds : Nat) :
    (exploratorySource mdp initialState episodes rewardSource initialTable
      defaultState transitionBonus explorationRate hexplorationRate).successorExpectedCumulativeRegret
        trajectory rounds =
      projectedExploratoryBehaviorExpectedRegret
        (initialState := initialState)
        (MDP.MeanCompatibleRewardKernel.knownRewardEpisodeBatchTrajectory
          (mdp := mdp) episodes trajectory)
        defaultState transitionBonus explorationRate hexplorationRate rounds := by
  unfold AdaptiveStochasticEpisodeBatchSource.successorExpectedCumulativeRegret
    projectedExploratoryBehaviorExpectedRegret
  apply Finset.sum_congr rfl
  intro round _hround
  unfold AdaptiveStochasticEpisodeBatchSource.successorPolicyAt
  rw [exploratorySource_successorPolicy]
  rw [MDP.MeanCompatibleRewardKernel.knownRewardEpisodeBatchPrefix_frestrictLe]
  rfl

omit [Nonempty State] in
/-- Average form of the projected successor-policy identity. -/
theorem exploratorySource_successorExpectedAverageRegret_eq_projected
    {mdp : MDP State Action} {initialState : Measure State}
    [IsProbabilityMeasure initialState] {episodes : Nat}
    (rewardSource : mdp.MeanCompatibleRewardKernel)
    (initialTable : DeterministicMarkovPolicyTable mdp)
    (defaultState : State) (transitionBonus : Real)
    (explorationRate : NNReal) (hexplorationRate : explorationRate <= 1)
    (trajectory : StochasticEpisodeBatchTrajectory mdp episodes) (rounds : Nat) :
    (exploratorySource mdp initialState episodes rewardSource initialTable
      defaultState transitionBonus explorationRate hexplorationRate).successorExpectedAverageRegret
        trajectory rounds =
      projectedAverageExploratoryBehaviorExpectedRegret
        (initialState := initialState)
        (MDP.MeanCompatibleRewardKernel.knownRewardEpisodeBatchTrajectory
          (mdp := mdp) episodes trajectory)
        defaultState transitionBonus explorationRate hexplorationRate rounds := by
  unfold AdaptiveStochasticEpisodeBatchSource.successorExpectedAverageRegret
    projectedAverageExploratoryBehaviorExpectedRegret
  rw [exploratorySource_successorExpectedCumulativeRegret_eq_projected]

/--
Concrete fixed-window route endpoint: projected count confidence and optimism,
exploratory behavior charge, and stochastic realized-return concentration hold
simultaneously with separate confidence budgets.
-/
theorem exploratorySource_trajectoryMeasure_projectedAllCoordinateConfidence_optimism_and_realizedSuccessorAverageRegret
    (mdp : MDP State Action) (initialState : Measure State)
    [IsProbabilityMeasure initialState] (episodes : Nat)
    [StandardBorelSpace State] [StandardBorelSpace Action]
    [StandardBorelSpace (EpisodeBatch mdp episodes)]
    [Nonempty (EpisodeBatch mdp episodes)]
    [StandardBorelSpace (StochasticEpisodeBatch mdp episodes)]
    [Nonempty (StochasticEpisodeBatch mdp episodes)]
    [StandardBorelSpace (StochasticEpisodeBatchTrajectory mdp episodes)]
    (rewardSource : mdp.MeanCompatibleRewardKernel)
    (initialTable : DeterministicMarkovPolicyTable mdp)
    (defaultState : State) (transitionBonus : Real)
    (explorationRate : NNReal) (hexplorationRate : explorationRate <= 1)
    (rewardBound rewardVarianceProxy : NNReal)
    (hrewardBound : forall state action,
      |mdp.reward state action| <= (rewardBound : Real))
    (htransitionBonus_nonneg : 0 <= transitionBonus)
    (law : rewardSource.UniformSubgaussianRewardLaw rewardVarianceProxy)
    (rounds : Nat) (hrounds : 0 < rounds) (hepisodes : 0 < episodes)
    (countDelta returnDelta : Real)
    (hcountDelta : 0 < countDelta) (hcountDelta_le_one : countDelta <= 1)
    (hreturnDelta : 0 < returnDelta) (hreturnDelta_le_one : returnDelta <= 1)
    (htotal : 0 <
      ((AdaptiveStochasticEpisodeBatchSource.cumulativeSuccessorGlobalReturnVarianceProxy
        mdp rounds episodes rewardBound rewardVarianceProxy : NNReal) : Real))
    (calibration :
      let deterministicSource :=
        AdaptiveEmpiricalOptimisticSource.exploratorySource mdp initialState episodes
          initialTable defaultState transitionBonus explorationRate hexplorationRate
      AdaptiveEmpiricalOptimisticSource.SourceCalibration deterministicSource
        rounds countDelta (rewardBound : Real) transitionBonus) :
    let source := exploratorySource mdp initialState episodes rewardSource initialTable
      defaultState transitionBonus explorationRate hexplorationRate
    let projection :=
      MDP.MeanCompatibleRewardKernel.knownRewardEpisodeBatchTrajectory
        (mdp := mdp) episodes
    let countBadEvent := projectedAdaptiveSimultaneousCountBadEvent
      (mdp := mdp) (initialState := initialState) (episodes := episodes)
      initialTable defaultState transitionBonus explorationRate
        hexplorationRate rounds countDelta
    let returnBadEvent := source.successorGlobalReturnDeviationBadEvent
      rounds rewardBound rewardVarianceProxy returnDelta
    let combinedBadEvent := countBadEvent ∪ returnBadEvent
    MeasurableSet combinedBadEvent /\
      source.trajectoryMeasure combinedBadEvent <=
        ENNReal.ofReal countDelta + ENNReal.ofReal returnDelta /\
      forall trajectory, trajectory ∉ combinedBadEvent ->
        (forall round : Fin rounds, forall state,
          mdp.optimalValueRemaining mdp.horizon le_rfl state <=
            (adaptiveEmpiricalOptimisticPlanAt
              (mdp := mdp) (episodes := episodes) (projection trajectory)
              defaultState transitionBonus round).upperValueRemaining
                mdp.horizon le_rfl state) /\
        source.realizedSuccessorAverageRegret trajectory rounds <=
          (mdp.horizon : Real) * (2 * transitionBonus) +
          exploratoryBehaviorRegretCharge mdp explorationRate (rewardBound : Real) +
          Concentration.subGaussianSumConfidenceRadius
              (AdaptiveStochasticEpisodeBatchSource.cumulativeSuccessorGlobalReturnVarianceProxy
                mdp rounds episodes rewardBound rewardVarianceProxy)
              returnDelta /
            ((episodes : Real) * (rounds : Real)) := by
  let source := exploratorySource mdp initialState episodes rewardSource initialTable
    defaultState transitionBonus explorationRate hexplorationRate
  let projection := MDP.MeanCompatibleRewardKernel.knownRewardEpisodeBatchTrajectory
    (mdp := mdp) episodes
  let countBadEvent := projectedAdaptiveSimultaneousCountBadEvent
    (mdp := mdp) (initialState := initialState) (episodes := episodes)
    initialTable defaultState transitionBonus explorationRate
      hexplorationRate rounds countDelta
  let returnBadEvent := source.successorGlobalReturnDeviationBadEvent
    rounds rewardBound rewardVarianceProxy returnDelta
  let combinedBadEvent := countBadEvent ∪ returnBadEvent
  let Good : StochasticEpisodeBatchTrajectory mdp episodes -> Prop := fun trajectory =>
    forall round : Fin rounds, forall state,
      mdp.optimalValueRemaining mdp.horizon le_rfl state <=
        (adaptiveEmpiricalOptimisticPlanAt
          (mdp := mdp) (episodes := episodes) (projection trajectory)
          defaultState transitionBonus round).upperValueRemaining
            mdp.horizon le_rfl state
  have hcount :=
    exploratorySource_trajectoryMeasure_projectedAllCoordinateConfidence_optimism_and_recommendedExpectedRegret
      (initialState := initialState) rewardSource initialTable defaultState
      (rewardBound : Real) transitionBonus explorationRate hexplorationRate
      hrewardBound htransitionBonus_nonneg rounds hrounds hepisodes countDelta
      hcountDelta hcountDelta_le_one calibration
  dsimp only at hcount
  rcases hcount with ⟨hcountMeasurable, hcountTail, hcountOutside⟩
  have hcountGood : forall trajectory, trajectory ∉ countBadEvent ->
      Good trajectory /\
        source.successorExpectedAverageRegret trajectory rounds <=
          (mdp.horizon : Real) * (2 * transitionBonus) +
          exploratoryBehaviorRegretCharge mdp explorationRate (rewardBound : Real) := by
    intro trajectory htrajectory
    have hgood := hcountOutside trajectory htrajectory
    refine ⟨hgood.1, ?_⟩
    calc
      source.successorExpectedAverageRegret trajectory rounds =
          projectedAverageExploratoryBehaviorExpectedRegret
            (initialState := initialState) (projection trajectory) defaultState
            transitionBonus explorationRate hexplorationRate rounds := by
        simpa [source, projection] using
          exploratorySource_successorExpectedAverageRegret_eq_projected
            (initialState := initialState) rewardSource initialTable defaultState
            transitionBonus explorationRate hexplorationRate trajectory rounds
      projectedAverageExploratoryBehaviorExpectedRegret
          (initialState := initialState) (projection trajectory) defaultState
          transitionBonus explorationRate hexplorationRate rounds <=
        adaptiveEmpiricalOptimisticRecommendedExpectedRegret
            (initialState := initialState) (projection trajectory) defaultState
            transitionBonus rounds /
              (rounds : Real) +
          exploratoryBehaviorRegretCharge mdp explorationRate (rewardBound : Real) :=
        projectedAverageExploratoryBehaviorExpectedRegret_le
          (initialState := initialState) (projection trajectory) defaultState
          transitionBonus explorationRate hexplorationRate (rewardBound : Real)
          hrewardBound rounds hrounds
      _ <= adaptiveEmpiricalOptimisticOccupancyRadiusSum
            (initialState := initialState) (projection trajectory) defaultState
            transitionBonus rounds /
              (rounds : Real) +
          exploratoryBehaviorRegretCharge mdp explorationRate (rewardBound : Real) := by
        exact add_le_add
          (div_le_div_of_nonneg_right hgood.2 (by positivity)) le_rfl
      _ = (mdp.horizon : Real) * (2 * transitionBonus) +
          exploratoryBehaviorRegretCharge mdp explorationRate (rewardBound : Real) := by
        rw [adaptiveEmpiricalOptimisticOccupancyRadiusSum_eq]
        field_simp
  have htransport :=
    source.trajectoryMeasure_expected_to_realized_successor_average_regret_transport_two_delta
      rounds hrounds hepisodes rewardBound rewardVarianceProxy hrewardBound law htotal
      countDelta returnDelta hreturnDelta hreturnDelta_le_one countBadEvent
      ((mdp.horizon : Real) * (2 * transitionBonus) +
        exploratoryBehaviorRegretCharge mdp explorationRate (rewardBound : Real))
      Good hcountMeasurable hcountTail hcountGood
  simpa [returnBadEvent, combinedBadEvent, Good, source, projection,
    add_assoc] using htransport

end AdaptiveStochasticEmpiricalOptimisticSource
end FiniteHorizonRL
end BanditRLProof
