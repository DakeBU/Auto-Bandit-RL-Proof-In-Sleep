import BanditRLProof.RL.FiniteHorizonAdaptiveStochasticRewardSampledEmpiricalOptimisticCumulativeExploratoryBehaviorRegret
import BanditRLProof.RL.FiniteHorizonAdaptiveStochasticRewardEmpiricalOptimisticRealizedBehaviorRegret

/-!
# Realized successor regret for actual sampled empirical optimism

This module combines the actual sampled-model confidence and exploratory
successor-policy route with the existing globally centered stochastic return
tail.  Model count, model reward, and realized-return failures retain three
separate confidence shares.  The result covers successor batches `1..rounds`;
the initial batch and explicit occupancy-radius rates remain downstream.
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

namespace AdaptiveStochasticSampledEmpiricalOptimisticSource

/-- The measurable sampled-table selector closes global return measurability. -/
noncomputable instance instExploratorySourceGlobalReturnMeasurability
    {mdp : MDP State Action} {initialState : Measure State}
    [IsProbabilityMeasure initialState] {episodes : Nat}
    (rewardSource : mdp.MeanCompatibleRewardKernel)
    (initialTable : DeterministicMarkovPolicyTable mdp)
    (defaultState : State) (rewardBudget transitionBudget : Real)
    (explorationRate : NNReal) (hexplorationRate : explorationRate <= 1) :
    (exploratorySource mdp initialState episodes rewardSource initialTable
      defaultState rewardBudget transitionBudget explorationRate
        hexplorationRate).GlobalReturnMeasurability where
  measurable_successorGlobalReturnDeviation n := by
    exact
      AdaptiveStochasticEmpiricalOptimisticSource.measurable_selectedExploratoryGlobalReturnDeviation
        (successorTable defaultState rewardBudget transitionBudget n)
        (measurable_successorTable
          defaultState rewardBudget transitionBudget n)
        explorationRate hexplorationRate

/-- The generic source cumulative expected regret is the named sampled-plan sum. -/
theorem exploratorySource_successorExpectedCumulativeRegret_eq_sampledPlanExploratoryBehaviorExpectedRegret
    {mdp : MDP State Action} {initialState : Measure State}
    [IsProbabilityMeasure initialState] {episodes : Nat}
    (rewardSource : mdp.MeanCompatibleRewardKernel)
    (initialTable : DeterministicMarkovPolicyTable mdp)
    (defaultState : State) (rewardBudget transitionBudget : Real)
    (explorationRate : NNReal) (hexplorationRate : explorationRate <= 1)
    (trajectory : StochasticEpisodeBatchTrajectory mdp episodes)
    (rounds : Nat) :
    (exploratorySource mdp initialState episodes rewardSource initialTable
      defaultState rewardBudget transitionBudget explorationRate
        hexplorationRate).successorExpectedCumulativeRegret trajectory rounds =
      adaptiveStochasticSampledEmpiricalOptimisticSuccessorExploratoryBehaviorExpectedRegret
        (mdp := mdp) (initialState := initialState) (episodes := episodes)
        trajectory defaultState rewardBudget transitionBudget
          explorationRate hexplorationRate rounds := by
  unfold AdaptiveStochasticEpisodeBatchSource.successorExpectedCumulativeRegret
    AdaptiveStochasticEpisodeBatchSource.successorPolicyAt
  exact
    exploratorySource_cumulativeSuccessorPolicyExpectedRegret_eq_sampledPlanExploratoryBehaviorExpectedRegret
      rewardSource initialTable defaultState rewardBudget transitionBudget
        explorationRate hexplorationRate rounds trajectory

/-- Average form of the exact sampled-plan successor-policy identity. -/
theorem exploratorySource_successorExpectedAverageRegret_eq_sampledPlanExploratoryBehaviorExpectedRegret
    {mdp : MDP State Action} {initialState : Measure State}
    [IsProbabilityMeasure initialState] {episodes : Nat}
    (rewardSource : mdp.MeanCompatibleRewardKernel)
    (initialTable : DeterministicMarkovPolicyTable mdp)
    (defaultState : State) (rewardBudget transitionBudget : Real)
    (explorationRate : NNReal) (hexplorationRate : explorationRate <= 1)
    (trajectory : StochasticEpisodeBatchTrajectory mdp episodes)
    (rounds : Nat) :
    (exploratorySource mdp initialState episodes rewardSource initialTable
      defaultState rewardBudget transitionBudget explorationRate
        hexplorationRate).successorExpectedAverageRegret trajectory rounds =
      adaptiveStochasticSampledEmpiricalOptimisticSuccessorExploratoryBehaviorExpectedRegret
          (mdp := mdp) (initialState := initialState) (episodes := episodes)
          trajectory defaultState rewardBudget transitionBudget
            explorationRate hexplorationRate rounds /
        (rounds : Real) := by
  unfold AdaptiveStochasticEpisodeBatchSource.successorExpectedAverageRegret
  rw [exploratorySource_successorExpectedCumulativeRegret_eq_sampledPlanExploratoryBehaviorExpectedRegret]

/--
Concrete three-share fixed-window endpoint for actual sampled-model planning
and realized successor behavior regret.
-/
theorem exploratorySource_trajectoryMeasure_finiteRound_allCoordinateConfidence_optimism_and_realizedSuccessorAverageRegret_of_pathSupport_explicitCalibration
    {mdp : MDP State Action} {initialState : Measure State}
    [IsProbabilityMeasure initialState] {episodes : Nat}
    [StandardBorelSpace State] [StandardBorelSpace Action]
    [StandardBorelSpace (StochasticEpisodeBatch mdp episodes)]
    [Nonempty (StochasticEpisodeBatch mdp episodes)]
    [StandardBorelSpace (StochasticEpisodeBatchTrajectory mdp episodes)]
    (rewardSource : mdp.MeanCompatibleRewardKernel)
    (initialTable : DeterministicMarkovPolicyTable mdp)
    (explorationRate : NNReal) (hexplorationRate : explorationRate <= 1)
    (rounds : Nat) (hrounds : 0 < rounds) (hepisodes : 0 < episodes)
    (varianceProxy : NNReal)
    (law : rewardSource.UniformSubgaussianRewardLaw varianceProxy)
    (hmodelTotal : 0 < ((((episodes : NNReal) * varianceProxy : NNReal) : Real)))
    (countDelta : Real) (hcountDelta : 0 < countDelta)
    (hcountDelta_le_one : countDelta <= 1)
    (rewardDelta : Real) (hrewardDelta : 0 < rewardDelta)
    (hrewardDelta_le_one : rewardDelta <= 1)
    (returnDelta : Real) (hreturnDelta : 0 < returnDelta)
    (hreturnDelta_le_one : returnDelta <= 1)
    (defaultState : State) (rewardBound : NNReal)
    (hrewardBound : forall state action,
      |mdp.reward state action| <= (rewardBound : Real))
    (support : ExploratoryPathSupport mdp initialState) (visitFloor : Real)
    (hfloor : ExploratoryPathUniformVisitFloor support explorationRate visitFloor)
    (hmargin :
      simultaneousCountConfidenceRadius mdp episodes
          (multiBatchLocalDelta rounds countDelta) <
        (episodes : Real) * visitFloor)
    (hcontraction :
      (Fintype.card State : Real) *
          uniformFloorTransitionCoordinateRadius mdp episodes
            (multiBatchLocalDelta rounds countDelta) visitFloor *
          (mdp.horizon : Real) <=
        1 / 2)
    (hreturnTotal : 0 <
      ((AdaptiveStochasticEpisodeBatchSource.cumulativeSuccessorGlobalReturnVarianceProxy
        mdp rounds episodes rewardBound varianceProxy : NNReal) : Real)) :
    let localCountDelta := multiBatchLocalDelta rounds countDelta
    let localRewardDelta := multiBatchLocalDelta rounds rewardDelta
    let rewardBudget :=
      uniformFloorStochasticRewardCoordinateRadius mdp episodes varianceProxy
        localCountDelta localRewardDelta visitFloor
    let transitionBudget :=
      uniformFloorStochasticTransitionBudget (rewardBound : Real) rewardBudget
    let source := exploratorySource mdp initialState episodes rewardSource
      initialTable defaultState rewardBudget transitionBudget
        explorationRate hexplorationRate
    let modelBadEvent := source.adaptiveAllCoordinateEmpiricalModelBadEvent
      rounds varianceProxy countDelta rewardDelta
    let returnBadEvent := source.successorGlobalReturnDeviationBadEvent
      rounds rewardBound varianceProxy returnDelta
    let combinedBadEvent := modelBadEvent ∪ returnBadEvent
    MeasurableSet combinedBadEvent ∧
      source.trajectoryMeasure combinedBadEvent <=
        (ENNReal.ofReal countDelta + ENNReal.ofReal rewardDelta) +
          ENNReal.ofReal returnDelta ∧
      forall trajectory, trajectory ∉ combinedBadEvent ->
        (forall round : Fin rounds, forall state,
          mdp.optimalValueRemaining mdp.horizon le_rfl state <=
            (adaptiveStochasticSampledEmpiricalOptimisticPlanAt trajectory
              defaultState rewardBudget transitionBudget round).upperValueRemaining
                mdp.horizon le_rfl state) ∧
          source.realizedSuccessorAverageRegret trajectory rounds <=
            (adaptiveStochasticSampledEmpiricalOptimisticOccupancyRadiusSum
                (mdp := mdp) (initialState := initialState) (episodes := episodes)
                trajectory defaultState rewardBudget transitionBudget rounds +
              (rounds : Real) *
                exploratoryBehaviorRegretCharge mdp explorationRate
                  (rewardBound : Real)) /
                (rounds : Real) +
              Concentration.subGaussianSumConfidenceRadius
                  (AdaptiveStochasticEpisodeBatchSource.cumulativeSuccessorGlobalReturnVarianceProxy
                    mdp rounds episodes rewardBound varianceProxy)
                  returnDelta /
                ((episodes : Real) * (rounds : Real)) := by
  dsimp only
  let localCountDelta := multiBatchLocalDelta rounds countDelta
  let localRewardDelta := multiBatchLocalDelta rounds rewardDelta
  let rewardBudget :=
    uniformFloorStochasticRewardCoordinateRadius mdp episodes varianceProxy
      localCountDelta localRewardDelta visitFloor
  let transitionBudget :=
    uniformFloorStochasticTransitionBudget (rewardBound : Real) rewardBudget
  let source : AdaptiveStochasticEpisodeBatchSource mdp initialState episodes :=
    exploratorySource mdp initialState episodes rewardSource
      initialTable defaultState rewardBudget transitionBudget
        explorationRate hexplorationRate
  let modelBadEvent : Set (StochasticEpisodeBatchTrajectory mdp episodes) :=
    source.adaptiveAllCoordinateEmpiricalModelBadEvent
      rounds varianceProxy countDelta rewardDelta
  let returnBadEvent : Set (StochasticEpisodeBatchTrajectory mdp episodes) :=
    source.successorGlobalReturnDeviationBadEvent
      rounds rewardBound varianceProxy returnDelta
  let combinedBadEvent : Set (StochasticEpisodeBatchTrajectory mdp episodes) :=
    modelBadEvent ∪ returnBadEvent
  have hmodel :=
    exploratorySource_trajectoryMeasure_finiteRound_allCoordinateConfidence_optimism_and_cumulativeSuccessorExploratoryBehaviorExpectedRegret_of_pathSupport_explicitCalibration
      rewardSource initialTable explorationRate hexplorationRate
        rounds hrounds hepisodes varianceProxy law hmodelTotal
        countDelta hcountDelta hcountDelta_le_one
        rewardDelta hrewardDelta hrewardDelta_le_one
        defaultState (rewardBound : Real) hrewardBound support visitFloor hfloor
        hmargin hcontraction
  have hmodel' :
      MeasurableSet modelBadEvent ∧
        source.trajectoryMeasure modelBadEvent <=
          ENNReal.ofReal countDelta + ENNReal.ofReal rewardDelta ∧
        forall trajectory, trajectory ∉ modelBadEvent ->
          (forall round : Fin rounds, forall state,
            mdp.optimalValueRemaining mdp.horizon le_rfl state <=
              (adaptiveStochasticSampledEmpiricalOptimisticPlanAt trajectory
                defaultState rewardBudget transitionBudget round).upperValueRemaining
                  mdp.horizon le_rfl state) ∧
            adaptiveStochasticSampledEmpiricalOptimisticSuccessorExploratoryBehaviorExpectedRegret
                (mdp := mdp) (initialState := initialState) (episodes := episodes)
                trajectory defaultState rewardBudget transitionBudget
                  explorationRate hexplorationRate rounds <=
              adaptiveStochasticSampledEmpiricalOptimisticOccupancyRadiusSum
                  (mdp := mdp) (initialState := initialState) (episodes := episodes)
                  trajectory defaultState rewardBudget transitionBudget rounds +
                (rounds : Real) *
                  exploratoryBehaviorRegretCharge mdp explorationRate
                    (rewardBound : Real) := by
    simpa [source, modelBadEvent, localCountDelta, localRewardDelta,
      rewardBudget, transitionBudget] using hmodel
  have hreturnMeasurable : MeasurableSet returnBadEvent := by
    simpa [returnBadEvent, source] using
      source.measurableSet_successorGlobalReturnDeviationBadEvent
        rounds rewardBound varianceProxy returnDelta
  have hreturnTail : source.trajectoryMeasure returnBadEvent <=
      ENNReal.ofReal returnDelta := by
    simpa [returnBadEvent, source] using
      source.trajectoryMeasure_successorGlobalReturnDeviationBadEvent_le
        rounds rewardBound varianceProxy hrewardBound law hreturnTotal
        returnDelta hreturnDelta hreturnDelta_le_one
  refine ⟨hmodel'.1.union hreturnMeasurable, ?_, ?_⟩
  · exact (measure_union_le modelBadEvent returnBadEvent).trans
      (add_le_add hmodel'.2.1 hreturnTail)
  · intro trajectory htrajectory
    have hnotModel : trajectory ∉ modelBadEvent := by
      exact fun hmem => htrajectory (Set.mem_union_left returnBadEvent hmem)
    have hnotReturn : trajectory ∉ returnBadEvent := by
      exact fun hmem => htrajectory (Set.mem_union_right modelBadEvent hmem)
    have hgood := hmodel'.2.2 trajectory hnotModel
    refine ⟨hgood.1, ?_⟩
    have hdeviation :
        |source.cumulativeSuccessorGlobalReturnDeviation rounds trajectory| <
          Concentration.subGaussianSumConfidenceRadius
            (AdaptiveStochasticEpisodeBatchSource.cumulativeSuccessorGlobalReturnVarianceProxy
              mdp rounds episodes rewardBound varianceProxy) returnDelta := by
      exact lt_of_not_ge (by simpa [returnBadEvent,
        AdaptiveStochasticEpisodeBatchSource.successorGlobalReturnDeviationBadEvent]
          using hnotReturn)
    have hroundsReal : 0 < (rounds : Real) := by exact_mod_cast hrounds
    have hdenom : 0 < (episodes : Real) * (rounds : Real) := by
      positivity
    have hexpected :
        source.successorExpectedAverageRegret trajectory rounds <=
          (adaptiveStochasticSampledEmpiricalOptimisticOccupancyRadiusSum
                (mdp := mdp) (initialState := initialState) (episodes := episodes)
                trajectory defaultState rewardBudget transitionBudget rounds +
              (rounds : Real) *
                exploratoryBehaviorRegretCharge mdp explorationRate
                  (rewardBound : Real)) /
            (rounds : Real) := by
      rw [show source.successorExpectedAverageRegret trajectory rounds =
          adaptiveStochasticSampledEmpiricalOptimisticSuccessorExploratoryBehaviorExpectedRegret
              (mdp := mdp) (initialState := initialState) (episodes := episodes)
              trajectory defaultState rewardBudget transitionBudget
                explorationRate hexplorationRate rounds /
            (rounds : Real) by
        simpa [source] using
          exploratorySource_successorExpectedAverageRegret_eq_sampledPlanExploratoryBehaviorExpectedRegret
            rewardSource initialTable defaultState
              rewardBudget transitionBudget explorationRate hexplorationRate
              trajectory rounds]
      exact div_le_div_of_nonneg_right hgood.2 hroundsReal.le
    have hnoise :
        -source.cumulativeSuccessorGlobalReturnDeviation rounds trajectory /
            ((episodes : Real) * (rounds : Real)) <=
          Concentration.subGaussianSumConfidenceRadius
              (AdaptiveStochasticEpisodeBatchSource.cumulativeSuccessorGlobalReturnVarianceProxy
                mdp rounds episodes rewardBound varianceProxy) returnDelta /
            ((episodes : Real) * (rounds : Real)) := by
      apply div_le_div_of_nonneg_right _ hdenom.le
      exact (neg_le_abs _).trans hdeviation.le
    rw [source.realizedSuccessorAverageRegret_eq_expected_sub_deviation
      trajectory rounds hrounds hepisodes]
    calc
      source.successorExpectedAverageRegret trajectory rounds -
          source.cumulativeSuccessorGlobalReturnDeviation rounds trajectory /
            ((episodes : Real) * (rounds : Real)) =
        source.successorExpectedAverageRegret trajectory rounds +
          (-source.cumulativeSuccessorGlobalReturnDeviation rounds trajectory /
            ((episodes : Real) * (rounds : Real))) := by ring
      _ <= (adaptiveStochasticSampledEmpiricalOptimisticOccupancyRadiusSum
                (mdp := mdp) (initialState := initialState) (episodes := episodes)
                trajectory defaultState rewardBudget transitionBudget rounds +
              (rounds : Real) *
                exploratoryBehaviorRegretCharge mdp explorationRate
                  (rewardBound : Real)) /
              (rounds : Real) +
            Concentration.subGaussianSumConfidenceRadius
                (AdaptiveStochasticEpisodeBatchSource.cumulativeSuccessorGlobalReturnVarianceProxy
                  mdp rounds episodes rewardBound varianceProxy) returnDelta /
              ((episodes : Real) * (rounds : Real)) :=
        add_le_add hexpected hnoise

end AdaptiveStochasticSampledEmpiricalOptimisticSource
end FiniteHorizonRL
end BanditRLProof
