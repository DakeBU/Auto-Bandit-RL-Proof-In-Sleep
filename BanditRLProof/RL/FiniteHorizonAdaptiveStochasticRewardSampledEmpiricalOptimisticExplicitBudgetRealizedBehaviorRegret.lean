import BanditRLProof.RL.FiniteHorizonAdaptiveStochasticRewardSampledEmpiricalOptimisticRealizedBehaviorRegret

/-!
# Explicit-budget realized successor regret for actual sampled optimism

This module evaluates the selected-radius occupancy term of the actual
sampled-reward empirical optimistic plans. The resulting three-share terminal
has a deterministic planning envelope, while retaining the globally centered
sampled-return radius and excluding the initial batch.
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

omit [Nonempty State] in
/-- An actual sampled empirical plan selects its two fixed model budgets. -/
theorem adaptiveStochasticSampledEmpiricalOptimisticPlanAt_selectedRadiusRemaining
    {mdp : MDP State Action} {episodes : Nat}
    (trajectory : StochasticEpisodeBatchTrajectory mdp episodes)
    (defaultState : State) (rewardBudget transitionBudget : Real)
    (round remaining : Nat)
    (hremaining : remaining + 1 <= mdp.horizon) (state : State) :
    (adaptiveStochasticSampledEmpiricalOptimisticPlanAt trajectory defaultState
      rewardBudget transitionBudget round).selectedRadiusRemaining
        remaining hremaining state =
      rewardBudget + transitionBudget := by
  simp [adaptiveStochasticSampledEmpiricalOptimisticPlanAt,
    MDP.EstimatedModelPlan.selectedRadiusRemaining,
    MDP.stochasticAllCoordinateEmpiricalFiniteBatchModel,
    MDP.FiniteBatchModel.plan]

omit [Nonempty State] in
/-- One sampled plan's selected-radius occupancy term has a closed form. -/
theorem adaptiveStochasticSampledEmpiricalOptimisticPlanAt_occupancySelectedRadiusRemaining_eq
    {mdp : MDP State Action} {initialState : Measure State}
    [IsProbabilityMeasure initialState] {episodes : Nat}
    (trajectory : StochasticEpisodeBatchTrajectory mdp episodes)
    (defaultState : State) (rewardBudget transitionBudget : Real)
    (round : Nat) :
    let plan := adaptiveStochasticSampledEmpiricalOptimisticPlanAt trajectory
      defaultState rewardBudget transitionBudget round
    plan.optimisticPolicy.occupancySumRemaining
        (fun remaining hremaining state =>
          2 * plan.selectedRadiusRemaining remaining hremaining state)
        mdp.horizon le_rfl initialState =
      (mdp.horizon : Real) * (2 * (rewardBudget + transitionBudget)) := by
  dsimp only
  rw [show
    (fun remaining hremaining state =>
      2 * (adaptiveStochasticSampledEmpiricalOptimisticPlanAt trajectory
        defaultState rewardBudget transitionBudget round).selectedRadiusRemaining
          remaining hremaining state) =
      (fun _remaining _hremaining _state =>
        2 * (rewardBudget + transitionBudget)) by
      funext remaining hremaining state
      rw [adaptiveStochasticSampledEmpiricalOptimisticPlanAt_selectedRadiusRemaining]]
  exact MarkovPolicy.occupancySumRemaining_const
    (policy :=
      (adaptiveStochasticSampledEmpiricalOptimisticPlanAt trajectory defaultState
        rewardBudget transitionBudget round).optimisticPolicy)
    (2 * (rewardBudget + transitionBudget)) mdp.horizon le_rfl initialState

omit [Nonempty State] in
/-- The complete actual-sampled occupancy-radius sum is deterministic. -/
theorem adaptiveStochasticSampledEmpiricalOptimisticOccupancyRadiusSum_eq
    {mdp : MDP State Action} {initialState : Measure State}
    [IsProbabilityMeasure initialState] {episodes : Nat}
    (trajectory : StochasticEpisodeBatchTrajectory mdp episodes)
    (defaultState : State) (rewardBudget transitionBudget : Real)
    (rounds : Nat) :
    adaptiveStochasticSampledEmpiricalOptimisticOccupancyRadiusSum
        (mdp := mdp) (initialState := initialState) (episodes := episodes)
        trajectory defaultState rewardBudget transitionBudget rounds =
      (rounds : Real) *
        ((mdp.horizon : Real) * (2 * (rewardBudget + transitionBudget))) := by
  unfold adaptiveStochasticSampledEmpiricalOptimisticOccupancyRadiusSum
  simp_rw [adaptiveStochasticSampledEmpiricalOptimisticPlanAt_occupancySelectedRadiusRemaining_eq]
  simp

/-- Planning part of the calibrated realized average-regret certificate. -/
noncomputable def
    adaptiveStochasticSampledEmpiricalOptimisticExplicitBudgetAverageBound
    (mdp : MDP State Action) (explorationRate : NNReal)
    (rewardBound rewardBudget : Real) : Real :=
  (mdp.horizon : Real) * (2 * (rewardBound + 3 * rewardBudget)) +
    exploratoryBehaviorRegretCharge mdp explorationRate rewardBound

omit [Nonempty State] in
/-- Uniform-floor budgets close the averaged occupancy and exploration charge. -/
theorem adaptiveStochasticSampledEmpiricalOptimistic_occupancyAndChargeAverage_eq_explicitBudgetAverageBound
    {mdp : MDP State Action} {initialState : Measure State}
    [IsProbabilityMeasure initialState] {episodes : Nat}
    (trajectory : StochasticEpisodeBatchTrajectory mdp episodes)
    (defaultState : State) (rewardBudget rewardBound : Real)
    (explorationRate : NNReal) (rounds : Nat) (hrounds : 0 < rounds) :
    (adaptiveStochasticSampledEmpiricalOptimisticOccupancyRadiusSum
          (mdp := mdp) (initialState := initialState) (episodes := episodes)
          trajectory defaultState rewardBudget
            (uniformFloorStochasticTransitionBudget rewardBound rewardBudget)
            rounds +
        (rounds : Real) *
          exploratoryBehaviorRegretCharge mdp explorationRate rewardBound) /
        (rounds : Real) =
      adaptiveStochasticSampledEmpiricalOptimisticExplicitBudgetAverageBound
        mdp explorationRate rewardBound rewardBudget := by
  rw [adaptiveStochasticSampledEmpiricalOptimisticOccupancyRadiusSum_eq]
  have hroundsReal : (rounds : Real) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt hrounds
  unfold adaptiveStochasticSampledEmpiricalOptimisticExplicitBudgetAverageBound
    uniformFloorStochasticTransitionBudget
  field_simp [hroundsReal]
  ring

namespace AdaptiveStochasticSampledEmpiricalOptimisticSource

/--
Actual sampled-model confidence and globally centered return concentration
with a deterministic explicit-budget planning envelope.
-/
theorem exploratorySource_trajectoryMeasure_finiteRound_allCoordinateConfidence_optimism_and_explicitBudgetRealizedSuccessorAverageRegret_of_pathSupport_explicitCalibration
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
    MeasurableSet combinedBadEvent /\
      source.trajectoryMeasure combinedBadEvent <=
        (ENNReal.ofReal countDelta + ENNReal.ofReal rewardDelta) +
          ENNReal.ofReal returnDelta /\
      forall trajectory, trajectory ∉ combinedBadEvent ->
        (forall round : Fin rounds, forall state,
          mdp.optimalValueRemaining mdp.horizon le_rfl state <=
            (adaptiveStochasticSampledEmpiricalOptimisticPlanAt trajectory
              defaultState rewardBudget transitionBudget round).upperValueRemaining
                mdp.horizon le_rfl state) /\
          source.realizedSuccessorAverageRegret trajectory rounds <=
            adaptiveStochasticSampledEmpiricalOptimisticExplicitBudgetAverageBound
                mdp explorationRate (rewardBound : Real) rewardBudget +
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
    exploratorySource mdp initialState episodes rewardSource initialTable
      defaultState rewardBudget transitionBudget explorationRate hexplorationRate
  let modelBadEvent : Set (StochasticEpisodeBatchTrajectory mdp episodes) :=
    source.adaptiveAllCoordinateEmpiricalModelBadEvent
      rounds varianceProxy countDelta rewardDelta
  let returnBadEvent : Set (StochasticEpisodeBatchTrajectory mdp episodes) :=
    source.successorGlobalReturnDeviationBadEvent
      rounds rewardBound varianceProxy returnDelta
  let combinedBadEvent : Set (StochasticEpisodeBatchTrajectory mdp episodes) :=
    modelBadEvent ∪ returnBadEvent
  have hparent :=
    exploratorySource_trajectoryMeasure_finiteRound_allCoordinateConfidence_optimism_and_realizedSuccessorAverageRegret_of_pathSupport_explicitCalibration
      rewardSource initialTable explorationRate hexplorationRate rounds hrounds
        hepisodes varianceProxy law hmodelTotal countDelta hcountDelta
        hcountDelta_le_one rewardDelta hrewardDelta hrewardDelta_le_one
        returnDelta hreturnDelta hreturnDelta_le_one defaultState rewardBound
        hrewardBound support visitFloor hfloor hmargin hcontraction hreturnTotal
  have hparent' :
      MeasurableSet combinedBadEvent /\
        source.trajectoryMeasure combinedBadEvent <=
          (ENNReal.ofReal countDelta + ENNReal.ofReal rewardDelta) +
            ENNReal.ofReal returnDelta /\
        forall trajectory, trajectory ∉ combinedBadEvent ->
          (forall round : Fin rounds, forall state,
            mdp.optimalValueRemaining mdp.horizon le_rfl state <=
              (adaptiveStochasticSampledEmpiricalOptimisticPlanAt trajectory
                defaultState rewardBudget transitionBudget round).upperValueRemaining
                  mdp.horizon le_rfl state) /\
            source.realizedSuccessorAverageRegret trajectory rounds <=
              (adaptiveStochasticSampledEmpiricalOptimisticOccupancyRadiusSum
                    (mdp := mdp) (initialState := initialState)
                    (episodes := episodes) trajectory defaultState rewardBudget
                    transitionBudget rounds +
                  (rounds : Real) * exploratoryBehaviorRegretCharge mdp
                    explorationRate (rewardBound : Real)) /
                  (rounds : Real) +
                Concentration.subGaussianSumConfidenceRadius
                    (AdaptiveStochasticEpisodeBatchSource.cumulativeSuccessorGlobalReturnVarianceProxy
                      mdp rounds episodes rewardBound varianceProxy)
                    returnDelta /
                  ((episodes : Real) * (rounds : Real)) := by
    simpa [localCountDelta, localRewardDelta, rewardBudget, transitionBudget,
      source, modelBadEvent, returnBadEvent, combinedBadEvent] using hparent
  refine ⟨hparent'.1, hparent'.2.1, ?_⟩
  intro trajectory htrajectory
  have hgood := hparent'.2.2 trajectory htrajectory
  refine ⟨hgood.1, ?_⟩
  have hplanning :=
    adaptiveStochasticSampledEmpiricalOptimistic_occupancyAndChargeAverage_eq_explicitBudgetAverageBound
      (mdp := mdp) (initialState := initialState) (episodes := episodes)
      trajectory defaultState rewardBudget (rewardBound : Real)
        explorationRate rounds hrounds
  exact hgood.2.trans_eq (congrArg
    (fun planning => planning +
      Concentration.subGaussianSumConfidenceRadius
          (AdaptiveStochasticEpisodeBatchSource.cumulativeSuccessorGlobalReturnVarianceProxy
            mdp rounds episodes rewardBound varianceProxy)
          returnDelta /
        ((episodes : Real) * (rounds : Real))) hplanning)

end AdaptiveStochasticSampledEmpiricalOptimisticSource
end FiniteHorizonRL
end BanditRLProof
