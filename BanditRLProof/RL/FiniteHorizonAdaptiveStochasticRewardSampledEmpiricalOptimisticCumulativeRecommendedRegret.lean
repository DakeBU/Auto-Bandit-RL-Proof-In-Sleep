import BanditRLProof.RL.FiniteHorizonAdaptiveStochasticRewardSampledEmpiricalOptimisticConfidence

/-!
# Cumulative recommended regret for adaptive sampled empirical optimism

This module sums the finite-round, actual-sampled-model recommendation bounds
from the adaptive stochastic confidence route.  It does not add exploratory
behavior or realized-return costs.
-/

open MeasureTheory
open scoped ENNReal ProbabilityTheory

universe u v

namespace BanditRLProof
namespace FiniteHorizonRL

variable {State : Type u} {Action : Type v}
    [MeasurableSpace State] [MeasurableSpace Action]
    [Fintype State] [Fintype Action]
    [DecidableEq State] [DecidableEq Action]
    [MeasurableSingletonClass State] [MeasurableSingletonClass Action]
    [Nonempty State] [Nonempty Action]

/-- Empirical optimistic plan built from one actual sampled-reward batch. -/
noncomputable def adaptiveStochasticSampledEmpiricalOptimisticPlanAt
    {mdp : MDP State Action} {episodes : Nat}
    (trajectory : StochasticEpisodeBatchTrajectory mdp episodes)
    (defaultState : State) (rewardBudget transitionBudget : Real)
    (round : Nat) : mdp.EstimatedModelPlan :=
  (mdp.stochasticAllCoordinateEmpiricalFiniteBatchModel episodes
    (mdp.sampledEpisodeBatchOfStochasticTrajectories episodes
      (trajectory round))
    defaultState rewardBudget transitionBudget).plan

/-- Sum of the recommended policies' expected regrets over the sampled window. -/
noncomputable def
    adaptiveStochasticSampledEmpiricalOptimisticRecommendedExpectedRegret
    {mdp : MDP State Action} {initialState : Measure State}
    [IsProbabilityMeasure initialState] {episodes : Nat}
    (trajectory : StochasticEpisodeBatchTrajectory mdp episodes)
    (defaultState : State) (rewardBudget transitionBudget : Real)
    (rounds : Nat) : Real :=
  ∑ round : Fin rounds,
    (adaptiveStochasticSampledEmpiricalOptimisticPlanAt trajectory defaultState
      rewardBudget transitionBudget round).optimisticPolicy.expectedRegret
        initialState

/-- Sum of the occupancy selected-radius bounds over the sampled window. -/
noncomputable def
    adaptiveStochasticSampledEmpiricalOptimisticOccupancyRadiusSum
    {mdp : MDP State Action} {initialState : Measure State}
    [IsProbabilityMeasure initialState] {episodes : Nat}
    (trajectory : StochasticEpisodeBatchTrajectory mdp episodes)
    (defaultState : State) (rewardBudget transitionBudget : Real)
    (rounds : Nat) : Real :=
  ∑ round : Fin rounds,
    let plan := adaptiveStochasticSampledEmpiricalOptimisticPlanAt trajectory
      defaultState rewardBudget transitionBudget round
    plan.optimisticPolicy.occupancySumRemaining
      (fun remaining hremaining state =>
        2 * plan.selectedRadiusRemaining remaining hremaining state)
      mdp.horizon le_rfl initialState

omit [Nonempty State] in
/-- Finite summation of pointwise sampled-model optimism and regret bounds. -/
theorem adaptiveStochasticSampledEmpiricalOptimistic_optimism_and_cumulativeRecommendedExpectedRegret
    {mdp : MDP State Action} {initialState : Measure State}
    [IsProbabilityMeasure initialState] {episodes rounds : Nat}
    (trajectory : StochasticEpisodeBatchTrajectory mdp episodes)
    (defaultState : State) (rewardBudget transitionBudget : Real)
    (hround : forall round : Fin rounds,
      let plan := adaptiveStochasticSampledEmpiricalOptimisticPlanAt trajectory
        defaultState rewardBudget transitionBudget round
      (forall state,
          mdp.optimalValueRemaining mdp.horizon le_rfl state <=
            plan.upperValueRemaining mdp.horizon le_rfl state) ∧
        plan.optimisticPolicy.expectedRegret initialState <=
          plan.optimisticPolicy.occupancySumRemaining
            (fun remaining hremaining state =>
              2 * plan.selectedRadiusRemaining remaining hremaining state)
            mdp.horizon le_rfl initialState) :
    (forall round : Fin rounds, forall state,
      mdp.optimalValueRemaining mdp.horizon le_rfl state <=
        (adaptiveStochasticSampledEmpiricalOptimisticPlanAt trajectory
          defaultState rewardBudget transitionBudget round).upperValueRemaining
            mdp.horizon le_rfl state) ∧
      adaptiveStochasticSampledEmpiricalOptimisticRecommendedExpectedRegret
          (mdp := mdp) (initialState := initialState) (episodes := episodes)
          trajectory defaultState rewardBudget transitionBudget rounds <=
        adaptiveStochasticSampledEmpiricalOptimisticOccupancyRadiusSum
          (mdp := mdp) (initialState := initialState) (episodes := episodes)
          trajectory defaultState rewardBudget transitionBudget rounds := by
  constructor
  · intro round state
    exact (hround round).1 state
  · unfold adaptiveStochasticSampledEmpiricalOptimisticRecommendedExpectedRegret
      adaptiveStochasticSampledEmpiricalOptimisticOccupancyRadiusSum
    apply Finset.sum_le_sum
    intro round _hround
    exact (hround round).2

namespace AdaptiveStochasticSampledEmpiricalOptimisticSource

/--
Finite-round actual-sampled-model confidence, optimism, and cumulative
recommended-policy expected regret under explicit path-support calibration.
-/
theorem exploratorySource_trajectoryMeasure_finiteRound_allCoordinateConfidence_optimism_and_cumulativeRecommendedExpectedRegret_of_pathSupport_explicitCalibration
    [StandardBorelSpace State] [StandardBorelSpace Action]
    {mdp : MDP State Action} {initialState : Measure State}
    [IsProbabilityMeasure initialState] {episodes : Nat}
    (rewardSource : mdp.MeanCompatibleRewardKernel)
    (initialTable : DeterministicMarkovPolicyTable mdp)
    (explorationRate : NNReal) (hexplorationRate : explorationRate <= 1)
    (rounds : Nat) (hrounds : 0 < rounds) (hepisodes : 0 < episodes)
    (varianceProxy : NNReal)
    (law : rewardSource.UniformSubgaussianRewardLaw varianceProxy)
    (htotal : 0 < ((((episodes : NNReal) * varianceProxy : NNReal) : Real)))
    (countDelta : Real) (hcountDelta : 0 < countDelta)
    (hcountDelta_le_one : countDelta <= 1)
    (rewardDelta : Real) (hrewardDelta : 0 < rewardDelta)
    (hrewardDelta_le_one : rewardDelta <= 1)
    (defaultState : State) (rewardBound : Real)
    (hrewardBound : forall state action,
      |mdp.reward state action| <= rewardBound)
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
        1 / 2) :
    let localCountDelta := multiBatchLocalDelta rounds countDelta
    let localRewardDelta := multiBatchLocalDelta rounds rewardDelta
    let rewardBudget :=
      uniformFloorStochasticRewardCoordinateRadius mdp episodes varianceProxy
        localCountDelta localRewardDelta visitFloor
    let transitionBudget :=
      uniformFloorStochasticTransitionBudget rewardBound rewardBudget
    let source := exploratorySource mdp initialState episodes rewardSource
      initialTable defaultState rewardBudget transitionBudget
        explorationRate hexplorationRate
    let event := source.adaptiveAllCoordinateEmpiricalModelBadEvent
      rounds varianceProxy countDelta rewardDelta
    MeasurableSet event ∧
      source.trajectoryMeasure event <=
        ENNReal.ofReal countDelta + ENNReal.ofReal rewardDelta ∧
      forall trajectory, trajectory ∉ event ->
        (forall round : Fin rounds, forall state,
          mdp.optimalValueRemaining mdp.horizon le_rfl state <=
            (adaptiveStochasticSampledEmpiricalOptimisticPlanAt trajectory
              defaultState rewardBudget transitionBudget round).upperValueRemaining
                mdp.horizon le_rfl state) ∧
          adaptiveStochasticSampledEmpiricalOptimisticRecommendedExpectedRegret
              (mdp := mdp) (initialState := initialState) (episodes := episodes)
              trajectory defaultState rewardBudget transitionBudget rounds <=
            adaptiveStochasticSampledEmpiricalOptimisticOccupancyRadiusSum
              (mdp := mdp) (initialState := initialState) (episodes := episodes)
              trajectory defaultState rewardBudget transitionBudget rounds := by
  dsimp only
  let localCountDelta := multiBatchLocalDelta rounds countDelta
  let localRewardDelta := multiBatchLocalDelta rounds rewardDelta
  let rewardBudget :=
    uniformFloorStochasticRewardCoordinateRadius mdp episodes varianceProxy
      localCountDelta localRewardDelta visitFloor
  let transitionBudget :=
    uniformFloorStochasticTransitionBudget rewardBound rewardBudget
  let source : AdaptiveStochasticEpisodeBatchSource mdp initialState episodes :=
    exploratorySource mdp initialState episodes rewardSource
      initialTable defaultState rewardBudget transitionBudget
        explorationRate hexplorationRate
  let event : Set (StochasticEpisodeBatchTrajectory mdp episodes) :=
    source.adaptiveAllCoordinateEmpiricalModelBadEvent
      rounds varianceProxy countDelta rewardDelta
  have hparent :=
    exploratorySource_trajectoryMeasure_finiteRound_allCoordinateConfidence_optimism_and_recommendedExpectedRegret_of_pathSupport_explicitCalibration
      rewardSource initialTable explorationRate hexplorationRate
        rounds hrounds hepisodes varianceProxy law htotal
        countDelta hcountDelta hcountDelta_le_one
        rewardDelta hrewardDelta hrewardDelta_le_one
        defaultState rewardBound hrewardBound support visitFloor hfloor
        hmargin hcontraction
  have hparent' :
      MeasurableSet event ∧
        source.trajectoryMeasure event <=
          ENNReal.ofReal countDelta + ENNReal.ofReal rewardDelta ∧
        forall trajectory, trajectory ∉ event -> forall round : Fin rounds,
          let plan := adaptiveStochasticSampledEmpiricalOptimisticPlanAt
            trajectory defaultState rewardBudget transitionBudget round
          (forall state,
              mdp.optimalValueRemaining mdp.horizon le_rfl state <=
                plan.upperValueRemaining mdp.horizon le_rfl state) ∧
            plan.optimisticPolicy.expectedRegret initialState <=
              plan.optimisticPolicy.occupancySumRemaining
                (fun remaining hremaining state =>
                  2 * plan.selectedRadiusRemaining remaining hremaining state)
                mdp.horizon le_rfl initialState := by
    simpa [source, event, localCountDelta, localRewardDelta, rewardBudget,
      transitionBudget, adaptiveStochasticSampledEmpiricalOptimisticPlanAt]
      using hparent
  refine ⟨hparent'.1, hparent'.2.1, ?_⟩
  intro trajectory htrajectory
  exact
    adaptiveStochasticSampledEmpiricalOptimistic_optimism_and_cumulativeRecommendedExpectedRegret
      (mdp := mdp) (initialState := initialState) (episodes := episodes)
      trajectory defaultState rewardBudget transitionBudget
        (hparent'.2.2 trajectory htrajectory)

end AdaptiveStochasticSampledEmpiricalOptimisticSource
end FiniteHorizonRL
end BanditRLProof
