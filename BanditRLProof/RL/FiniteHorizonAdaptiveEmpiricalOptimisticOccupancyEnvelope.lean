import BanditRLProof.RL.FiniteHorizonExploratoryPathSupportEpisodeThreshold

/-!
# Explicit occupancy envelope for the fixed-bonus adaptive empirical plan

The current known-reward empirical optimistic plan uses zero reward radius and
one fixed transition bonus at every coordinate. This module evaluates its
recursive occupancy-radius sum exactly and attaches that explicit envelope to
the compiled path-support episode-threshold event.

The result is linear in rounds and horizon because the bonus is fixed. It is
not a count-dependent statistical regret rate.
-/

open MeasureTheory
open scoped ENNReal ProbabilityTheory

universe u v

namespace BanditRLProof.FiniteHorizonRL

variable {State : Type u} {Action : Type v}
    [MeasurableSpace State] [MeasurableSpace Action]
    [Fintype State] [Fintype Action]
    [DecidableEq State] [DecidableEq Action]
    [MeasurableSingletonClass State] [MeasurableSingletonClass Action]
    [Nonempty Action]

omit [DecidableEq State] [DecidableEq Action]
    [MeasurableSingletonClass State] [MeasurableSingletonClass Action]
    [Nonempty Action] in
/-- A probability occupancy sum evaluates a constant stage cost exactly. -/
theorem MarkovPolicy.occupancySumRemaining_const
    {mdp : MDP State Action} (policy : MarkovPolicy mdp) (c : Real)
    (remaining : Nat) (hremaining : remaining <= mdp.horizon)
    (mu : Measure State) [IsProbabilityMeasure mu] :
    policy.occupancySumRemaining
        (fun _remaining _hremaining _state => c)
        remaining hremaining mu =
      (remaining : Real) * c := by
  induction remaining generalizing mu with
  | zero =>
      simp [MarkovPolicy.occupancySumRemaining]
  | succ remaining ih =>
      let stage : Fin mdp.horizon :=
        ⟨mdp.horizon - (remaining + 1), by omega⟩
      let nextMu : Measure State := policy.inducedStateKernel stage ∘ₘ mu
      letI : IsProbabilityMeasure nextMu := by
        dsimp [nextMu]
        infer_instance
      rw [policy.occupancySumRemaining_succ]
      have hnext := ih (by omega) nextMu
      rw [hnext]
      simp [Nat.cast_add, add_mul, add_comm]

/-- The concrete known-reward empirical plan selects its fixed transition bonus. -/
theorem adaptiveEmpiricalOptimisticPlanAt_selectedRadiusRemaining
    {mdp : MDP State Action} {episodes : Nat}
    (trajectory : EpisodeBatchTrajectory mdp episodes)
    (defaultState : State) (transitionBonus : Real) (round remaining : Nat)
    (hremaining : remaining + 1 <= mdp.horizon) (state : State) :
    (adaptiveEmpiricalOptimisticPlanAt
      (mdp := mdp) (episodes := episodes)
      trajectory defaultState transitionBonus round).selectedRadiusRemaining
        remaining hremaining state =
      transitionBonus := by
  simp [adaptiveEmpiricalOptimisticPlanAt,
    MDP.EstimatedModelPlan.selectedRadiusRemaining,
    TransitionCountSummary.optimisticPlan]

/-- Each round's selected-radius occupancy term is the horizon times the fixed cost. -/
theorem adaptiveEmpiricalOptimisticPlanAt_occupancySelectedRadiusRemaining_eq
    {mdp : MDP State Action} {initialState : Measure State}
    [IsProbabilityMeasure initialState] {episodes : Nat}
    (trajectory : EpisodeBatchTrajectory mdp episodes)
    (defaultState : State) (transitionBonus : Real) (round : Nat) :
    let plan := adaptiveEmpiricalOptimisticPlanAt
      (mdp := mdp) (episodes := episodes)
      trajectory defaultState transitionBonus round
    plan.optimisticPolicy.occupancySumRemaining
        (fun remaining hremaining state =>
          2 * plan.selectedRadiusRemaining remaining hremaining state)
        mdp.horizon le_rfl initialState =
      (mdp.horizon : Real) * (2 * transitionBonus) := by
  dsimp only
  rw [show
    (fun remaining hremaining state =>
      2 * (adaptiveEmpiricalOptimisticPlanAt
        (mdp := mdp) (episodes := episodes)
        trajectory defaultState transitionBonus round).selectedRadiusRemaining
          remaining hremaining state) =
      (fun _remaining _hremaining _state => 2 * transitionBonus) by
        funext remaining hremaining state
        rw [adaptiveEmpiricalOptimisticPlanAt_selectedRadiusRemaining]]
  exact MarkovPolicy.occupancySumRemaining_const
    (policy :=
      (adaptiveEmpiricalOptimisticPlanAt
        (mdp := mdp) (episodes := episodes)
        trajectory defaultState transitionBonus round).optimisticPolicy)
    (2 * transitionBonus) mdp.horizon le_rfl initialState

/-- The complete adaptive selected-radius occupancy sum has a closed form. -/
theorem adaptiveEmpiricalOptimisticOccupancyRadiusSum_eq
    {mdp : MDP State Action} {initialState : Measure State}
    [IsProbabilityMeasure initialState] {episodes : Nat}
    (trajectory : EpisodeBatchTrajectory mdp episodes)
    (defaultState : State) (transitionBonus : Real) (rounds : Nat) :
    adaptiveEmpiricalOptimisticOccupancyRadiusSum
        (mdp := mdp) (initialState := initialState) (episodes := episodes)
        trajectory defaultState transitionBonus rounds =
      (rounds : Real) * ((mdp.horizon : Real) * (2 * transitionBonus)) := by
  unfold adaptiveEmpiricalOptimisticOccupancyRadiusSum
  simp_rw [adaptiveEmpiricalOptimisticPlanAt_occupancySelectedRadiusRemaining_eq]
  simp

namespace AdaptiveEmpiricalOptimisticSource

/--
Route endpoint: the path-support episode threshold now yields a fully explicit
fixed-bonus bound for the recommended optimistic policies.
-/
theorem exploratorySource_trajectoryMeasure_allCoordinateConfidence_optimism_and_explicitRecommendedExpectedRegret_of_pathSupport_episodeThreshold
    {mdp : MDP State Action} {initialState : Measure State}
    [IsProbabilityMeasure initialState] {episodes : Nat}
    (initialTable : DeterministicMarkovPolicyTable mdp)
    (defaultState : State) (rewardBound : Real)
    (explorationRate : NNReal) (hexplorationRate : explorationRate <= 1)
    (hrewardBound : forall state action, |mdp.reward state action| <= rewardBound)
    (rounds : Nat) (hhorizon : 0 < mdp.horizon) (hrounds : 0 < rounds)
    (hepisodes : 0 < episodes) (delta : Real) (hdelta : 0 < delta)
    (hdelta_le_one : delta <= 1)
    (support : ExploratoryPathSupport mdp initialState)
    (visitFloor : Real) (hvisitFloor : 0 < visitFloor)
    (hfloor : ExploratoryPathUniformVisitFloor support explorationRate visitFloor)
    (hthreshold : exploratoryPathCalibrationEpisodeThreshold mdp rounds delta visitFloor <
      (episodes : Real)) :
    let behaviorSource := exploratorySource mdp initialState episodes
      initialTable defaultState rewardBound explorationRate hexplorationRate
    let bad := behaviorSource.adaptiveSimultaneousCountBadEvent rounds delta
    MeasurableSet bad /\
      behaviorSource.trajectoryMeasure bad <= ENNReal.ofReal delta /\
      forall trajectory, trajectory ∉ bad ->
        (forall round : Fin rounds, forall state,
          mdp.optimalValueRemaining mdp.horizon le_rfl state <=
            (adaptiveEmpiricalOptimisticPlanAt
              (mdp := mdp) (episodes := episodes)
              trajectory defaultState rewardBound round).upperValueRemaining
                mdp.horizon le_rfl state) /\
        adaptiveEmpiricalOptimisticRecommendedExpectedRegret
            (mdp := mdp) (initialState := initialState) (episodes := episodes)
            trajectory defaultState rewardBound rounds <=
          (rounds : Real) * ((mdp.horizon : Real) * (2 * rewardBound)) := by
  dsimp only
  obtain ⟨hmeasurable, htail, hgood⟩ :=
    exploratorySource_trajectoryMeasure_allCoordinateConfidence_optimism_and_recommendedExpectedRegret_of_pathSupport_episodeThreshold
      initialTable defaultState rewardBound explorationRate hexplorationRate
      hrewardBound rounds hhorizon hrounds hepisodes delta hdelta hdelta_le_one
      support visitFloor hvisitFloor hfloor hthreshold
  exact ⟨hmeasurable, htail, fun trajectory htrajectory =>
    ⟨(hgood trajectory htrajectory).1,
      (hgood trajectory htrajectory).2.trans_eq
        (adaptiveEmpiricalOptimisticOccupancyRadiusSum_eq
          trajectory defaultState rewardBound rounds)⟩⟩

end AdaptiveEmpiricalOptimisticSource

end BanditRLProof.FiniteHorizonRL
