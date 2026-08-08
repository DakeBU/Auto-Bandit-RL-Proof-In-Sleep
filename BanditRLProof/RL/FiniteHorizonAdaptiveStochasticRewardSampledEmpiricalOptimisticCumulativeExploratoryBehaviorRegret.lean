import BanditRLProof.RL.FiniteHorizonAdaptiveStochasticRewardSampledEmpiricalOptimisticCumulativeRecommendedRegret
import BanditRLProof.RL.FiniteHorizonAdaptiveCumulativeExploratoryBehaviorRegret

/-!
# Cumulative successor exploratory-behavior regret for sampled empirical optimism

This module charges uniform exploration around the actual sampled-model
recommendations.  The policy built from coordinate `round` is the adaptive
source policy for successor batch `round + 1`; the initial policy and realized
sampled returns remain outside this theorem route.
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

namespace StochasticEpisodeBatch

omit [Nonempty State] in
/-- The sampled optimistic action table represents the sampled plan's policy. -/
theorem sampledEmpiricalOptimisticPolicyTable_toMarkovPolicy
    {mdp : MDP State Action} {episodes : Nat}
    (batch : StochasticEpisodeBatch mdp episodes) (defaultState : State)
    (rewardBudget transitionBudget : Real) :
    (batch.sampledEmpiricalOptimisticPolicyTable
        defaultState rewardBudget transitionBudget).toMarkovPolicy =
      (mdp.stochasticAllCoordinateEmpiricalFiniteBatchModel episodes
        (mdp.sampledEpisodeBatchOfStochasticTrajectories episodes batch)
        defaultState rewardBudget transitionBudget).plan.optimisticPolicy := by
  rfl

end StochasticEpisodeBatch

/--
Expected regret of the actual successor exploratory policies selected from the
sampled plans in a finite window.
-/
noncomputable def
    adaptiveStochasticSampledEmpiricalOptimisticSuccessorExploratoryBehaviorExpectedRegret
    {mdp : MDP State Action} {initialState : Measure State}
    [IsProbabilityMeasure initialState] {episodes : Nat}
    (trajectory : StochasticEpisodeBatchTrajectory mdp episodes)
    (defaultState : State) (rewardBudget transitionBudget : Real)
    (explorationRate : NNReal) (hexplorationRate : explorationRate <= 1)
    (rounds : Nat) : Real :=
  ∑ round : Fin rounds,
    (((trajectory round).sampledEmpiricalOptimisticPolicyTable
        defaultState rewardBudget transitionBudget).exploratoryPolicy
      explorationRate hexplorationRate).expectedRegret initialState

namespace AdaptiveStochasticSampledEmpiricalOptimisticSource

/-- The policy selected from sampled coordinate `n` generates successor coordinate `n + 1`. -/
theorem exploratorySource_successorPolicy_frestrictLe_eq_sampledPlanExploratoryPolicy
    {mdp : MDP State Action} {initialState : Measure State}
    [IsProbabilityMeasure initialState] {episodes : Nat}
    (rewardSource : mdp.MeanCompatibleRewardKernel)
    (initialTable : DeterministicMarkovPolicyTable mdp)
    (defaultState : State) (rewardBudget transitionBudget : Real)
    (explorationRate : NNReal) (hexplorationRate : explorationRate <= 1)
    (n : Nat) (trajectory : StochasticEpisodeBatchTrajectory mdp episodes) :
    let source := exploratorySource mdp initialState episodes rewardSource
      initialTable defaultState rewardBudget transitionBudget
        explorationRate hexplorationRate
    source.successorPolicy n (Preorder.frestrictLe n trajectory) =
      ((trajectory n).sampledEmpiricalOptimisticPolicyTable
        defaultState rewardBudget transitionBudget).exploratoryPolicy
          explorationRate hexplorationRate := by
  rfl

/-- The named sampled-plan sum is the actual source successor-policy regret sum. -/
theorem exploratorySource_cumulativeSuccessorPolicyExpectedRegret_eq_sampledPlanExploratoryBehaviorExpectedRegret
    {mdp : MDP State Action} {initialState : Measure State}
    [IsProbabilityMeasure initialState] {episodes : Nat}
    (rewardSource : mdp.MeanCompatibleRewardKernel)
    (initialTable : DeterministicMarkovPolicyTable mdp)
    (defaultState : State) (rewardBudget transitionBudget : Real)
    (explorationRate : NNReal) (hexplorationRate : explorationRate <= 1)
    (rounds : Nat)
    (trajectory : StochasticEpisodeBatchTrajectory mdp episodes) :
    let source := exploratorySource mdp initialState episodes rewardSource
      initialTable defaultState rewardBudget transitionBudget
        explorationRate hexplorationRate
    (∑ round : Fin rounds,
        (source.successorPolicy (round : Nat)
          (Preorder.frestrictLe (round : Nat) trajectory)).expectedRegret
            initialState) =
      adaptiveStochasticSampledEmpiricalOptimisticSuccessorExploratoryBehaviorExpectedRegret
        (mdp := mdp) (initialState := initialState) (episodes := episodes)
        trajectory defaultState rewardBudget transitionBudget
          explorationRate hexplorationRate rounds := by
  rfl

end AdaptiveStochasticSampledEmpiricalOptimisticSource

/--
Cumulative successor exploratory-policy regret is recommendation regret plus
one explicit exploration charge per selected sampled plan.
-/
theorem adaptiveStochasticSampledEmpiricalOptimisticSuccessorExploratoryBehaviorExpectedRegret_le
    {mdp : MDP State Action} {initialState : Measure State}
    [IsProbabilityMeasure initialState] {episodes : Nat}
    (trajectory : StochasticEpisodeBatchTrajectory mdp episodes)
    (defaultState : State) (rewardBudget transitionBudget : Real)
    (explorationRate : NNReal) (hexplorationRate : explorationRate <= 1)
    (rewardBound : Real)
    (hrewardBound : forall state action,
      |mdp.reward state action| <= rewardBound)
    (rounds : Nat) :
    adaptiveStochasticSampledEmpiricalOptimisticSuccessorExploratoryBehaviorExpectedRegret
        (mdp := mdp) (initialState := initialState) (episodes := episodes)
        trajectory defaultState rewardBudget transitionBudget
          explorationRate hexplorationRate rounds <=
      adaptiveStochasticSampledEmpiricalOptimisticRecommendedExpectedRegret
          (mdp := mdp) (initialState := initialState) (episodes := episodes)
          trajectory defaultState rewardBudget transitionBudget rounds +
        (rounds : Real) *
          exploratoryBehaviorRegretCharge mdp explorationRate rewardBound := by
  unfold
    adaptiveStochasticSampledEmpiricalOptimisticSuccessorExploratoryBehaviorExpectedRegret
    adaptiveStochasticSampledEmpiricalOptimisticRecommendedExpectedRegret
  calc
    (∑ round : Fin rounds,
        (((trajectory round).sampledEmpiricalOptimisticPolicyTable
            defaultState rewardBudget transitionBudget).exploratoryPolicy
          explorationRate hexplorationRate).expectedRegret initialState) <=
        ∑ round : Fin rounds, (
          (adaptiveStochasticSampledEmpiricalOptimisticPlanAt trajectory
              defaultState rewardBudget transitionBudget round).optimisticPolicy.expectedRegret
                initialState +
            exploratoryBehaviorRegretCharge mdp explorationRate rewardBound) := by
      apply Finset.sum_le_sum
      intro round _hround
      let table := (trajectory round).sampledEmpiricalOptimisticPolicyTable
        defaultState rewardBudget transitionBudget
      have htransport :=
        table.exploratoryPolicy_expectedRegret_le_toMarkovPolicy_expectedRegret_add_charge
          initialState explorationRate hexplorationRate rewardBound hrewardBound
      simpa [table, exploratoryBehaviorRegretCharge,
        adaptiveStochasticSampledEmpiricalOptimisticPlanAt,
        StochasticEpisodeBatch.sampledEmpiricalOptimisticPolicyTable_toMarkovPolicy]
        using htransport
    _ = (∑ round : Fin rounds,
          (adaptiveStochasticSampledEmpiricalOptimisticPlanAt trajectory
            defaultState rewardBudget transitionBudget round).optimisticPolicy.expectedRegret
              initialState) +
        (rounds : Real) *
          exploratoryBehaviorRegretCharge mdp explorationRate rewardBound := by
      rw [Finset.sum_add_distrib]
      simp

/--
On sampled-model confidence, cumulative successor behavior regret is bounded by
the occupancy-radius certificate plus the explicit exploration charge.
-/
theorem adaptiveStochasticSampledEmpiricalOptimistic_optimism_and_cumulativeSuccessorExploratoryBehaviorExpectedRegret
    {mdp : MDP State Action} {initialState : Measure State}
    [IsProbabilityMeasure initialState] {episodes rounds : Nat}
    (trajectory : StochasticEpisodeBatchTrajectory mdp episodes)
    (defaultState : State) (rewardBudget transitionBudget : Real)
    (explorationRate : NNReal) (hexplorationRate : explorationRate <= 1)
    (rewardBound : Real)
    (hrewardBound : forall state action,
      |mdp.reward state action| <= rewardBound)
    (hconfidence :
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
            trajectory defaultState rewardBudget transitionBudget rounds) :
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
            exploratoryBehaviorRegretCharge mdp explorationRate rewardBound := by
  refine ⟨hconfidence.1, ?_⟩
  calc
    adaptiveStochasticSampledEmpiricalOptimisticSuccessorExploratoryBehaviorExpectedRegret
          (mdp := mdp) (initialState := initialState) (episodes := episodes)
          trajectory defaultState rewardBudget transitionBudget
            explorationRate hexplorationRate rounds <=
        adaptiveStochasticSampledEmpiricalOptimisticRecommendedExpectedRegret
            (mdp := mdp) (initialState := initialState) (episodes := episodes)
            trajectory defaultState rewardBudget transitionBudget rounds +
          (rounds : Real) *
            exploratoryBehaviorRegretCharge mdp explorationRate rewardBound :=
      adaptiveStochasticSampledEmpiricalOptimisticSuccessorExploratoryBehaviorExpectedRegret_le
        trajectory defaultState rewardBudget transitionBudget
          explorationRate hexplorationRate rewardBound hrewardBound rounds
    _ <= adaptiveStochasticSampledEmpiricalOptimisticOccupancyRadiusSum
            (mdp := mdp) (initialState := initialState) (episodes := episodes)
            trajectory defaultState rewardBudget transitionBudget rounds +
          (rounds : Real) *
            exploratoryBehaviorRegretCharge mdp explorationRate rewardBound :=
      add_le_add hconfidence.2 (le_refl _)

namespace AdaptiveStochasticSampledEmpiricalOptimisticSource

/--
Finite-round actual-sampled confidence, optimism, and cumulative expected
regret of the selected successor exploratory policies.
-/
theorem exploratorySource_trajectoryMeasure_finiteRound_allCoordinateConfidence_optimism_and_cumulativeSuccessorExploratoryBehaviorExpectedRegret_of_pathSupport_explicitCalibration
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
          adaptiveStochasticSampledEmpiricalOptimisticSuccessorExploratoryBehaviorExpectedRegret
              (mdp := mdp) (initialState := initialState) (episodes := episodes)
              trajectory defaultState rewardBudget transitionBudget
                explorationRate hexplorationRate rounds <=
            adaptiveStochasticSampledEmpiricalOptimisticOccupancyRadiusSum
                (mdp := mdp) (initialState := initialState) (episodes := episodes)
                trajectory defaultState rewardBudget transitionBudget rounds +
              (rounds : Real) *
                exploratoryBehaviorRegretCharge mdp explorationRate rewardBound := by
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
    exploratorySource_trajectoryMeasure_finiteRound_allCoordinateConfidence_optimism_and_cumulativeRecommendedExpectedRegret_of_pathSupport_explicitCalibration
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
    simpa [source, event, localCountDelta, localRewardDelta, rewardBudget,
      transitionBudget] using hparent
  refine ⟨hparent'.1, hparent'.2.1, ?_⟩
  intro trajectory htrajectory
  exact
    adaptiveStochasticSampledEmpiricalOptimistic_optimism_and_cumulativeSuccessorExploratoryBehaviorExpectedRegret
      trajectory defaultState rewardBudget transitionBudget
        explorationRate hexplorationRate rewardBound hrewardBound
        (hparent'.2.2 trajectory htrajectory)

end AdaptiveStochasticSampledEmpiricalOptimisticSource
end FiniteHorizonRL
end BanditRLProof
