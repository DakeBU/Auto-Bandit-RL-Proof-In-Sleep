import BanditRLProof.RL.FiniteHorizonIIDGeneratedEmpiricalRewardExactness

/-!
# All-coordinate finite-batch confidence for finite-horizon iid trajectories

This module turns the compiled generated reward and transition laws into an
actual `MDP.FiniteBatchModel.Confidence` producer. The construction is
noncircular: reward radius is zero, transition radius is one fixed external
budget, transition coordinate radii use genuine expected-count lower margins,
and the recursive value envelope is the explicit linear function
`remaining * (rewardBound + transitionBudget)`.
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
    [Nonempty Action]

/-- Explicit noncircular envelope for a fixed reward and transition budget. -/
def empiricalFiniteBatchValueEnvelope
    (rewardBound transitionBudget : Real) (remaining : Nat) : Real :=
  (remaining : Real) * (rewardBound + transitionBudget)

namespace MDP

/--
Canonical empirical model for the all-coordinate route: exact generated rewards
use radius zero, while every transition coordinate shares one fixed budget.
-/
noncomputable def allCoordinateEmpiricalFiniteBatchModel
    (mdp : MDP State Action) (episodes : Nat) (batch : EpisodeBatch mdp episodes)
    (defaultState : State) (transitionBudget : Real) :
    FiniteBatchModel mdp episodes where
  batch := batch
  defaultState := defaultState
  rewardRadius _stage _state _action := 0
  transitionRadius _stage _state _action := transitionBudget

end MDP

namespace MarkovPolicy

/-- Deterministic lower-margin coordinate radius based on the genuine visit mean. -/
noncomputable def expectedCountTransitionCoordinateRadius
    {mdp : MDP State Action} (policy : MarkovPolicy mdp)
    (initialState : Measure State) [IsProbabilityMeasure initialState]
    (episodes : Nat) (delta : Real) (stage : Fin mdp.horizon)
    (state : State) (action : Action) (_nextState : State) : Real :=
  let coordinate : VisitCoordinate mdp :=
    { stage := stage, state := state, action := action }
  2 * simultaneousCountConfidenceRadius mdp episodes delta /
    (coordinate.expectedCount policy initialState episodes -
      simultaneousCountConfidenceRadius mdp episodes delta)

omit [MeasurableSingletonClass State] [MeasurableSingletonClass Action]
    [Nonempty Action] in
/-- Outside the simultaneous event, realized count exceeds its deterministic lower margin. -/
theorem expectedCount_sub_radius_lt_count_of_not_mem_simultaneousCountBadEvent
    {mdp : MDP State Action} (policy : MarkovPolicy mdp)
    (initialState : Measure State) [IsProbabilityMeasure initialState]
    {episodes : Nat} {delta : Real} (batch : EpisodeBatch mdp episodes)
    (hbatch : batch ∉
      policy.simultaneousCountBadEvent initialState episodes delta)
    (coordinate : VisitCoordinate mdp) :
    coordinate.expectedCount policy initialState episodes -
        simultaneousCountConfidenceRadius mdp episodes delta <
      (coordinate.count batch : Real) := by
  have hdeviation :=
    policy.visitCount_abs_deviation_lt_of_not_mem_simultaneousCountBadEvent
      initialState batch hbatch coordinate.stage coordinate.state coordinate.action
  have hleft := (abs_lt.mp hdeviation).1
  simpa [VisitCoordinate.count, VisitCoordinate.expectedCount] using (show
    coordinate.expectedCount policy initialState episodes -
        simultaneousCountConfidenceRadius mdp episodes delta <
      (coordinate.count batch : Real) by
        dsimp [VisitCoordinate.count, VisitCoordinate.expectedCount]
        linarith)

omit [Nonempty Action] in
/--
The random-denominator transition error is bounded by the deterministic
expected-count lower-margin radius.
-/
theorem empiricalTransitionMass_abs_sub_transition_le_expectedCountRadius_of_not_mem
    {mdp : MDP State Action} (policy : MarkovPolicy mdp)
    (initialState : Measure State) [IsProbabilityMeasure initialState]
    {episodes : Nat} {delta : Real} (batch : EpisodeBatch mdp episodes)
    (hbatch : batch ∉
      policy.simultaneousCountBadEvent initialState episodes delta)
    (defaultState : State) (coordinate : VisitCoordinate mdp)
    (hmargin : simultaneousCountConfidenceRadius mdp episodes delta <
      coordinate.expectedCount policy initialState episodes)
    (nextState : State) :
    |batch.empiricalTransitionMass defaultState coordinate.stage
          coordinate.state coordinate.action nextState -
        (mdp.transition (coordinate.state, coordinate.action)).real {nextState}| ≤
      policy.expectedCountTransitionCoordinateRadius initialState episodes delta
        coordinate.stage coordinate.state coordinate.action nextState := by
  let radius := simultaneousCountConfidenceRadius mdp episodes delta
  let expected := coordinate.expectedCount policy initialState episodes
  let count : Real := coordinate.count batch
  have hradius : 0 ≤ radius := by
    exact Concentration.subGaussianSumConfidenceRadius_nonneg _ _
  have hdenominator : 0 < expected - radius := by
    dsimp [expected, radius]
    linarith
  have hlower : expected - radius < count := by
    simpa [expected, radius, count] using
      policy.expectedCount_sub_radius_lt_count_of_not_mem_simultaneousCountBadEvent
        initialState batch hbatch coordinate
  have hrandom :=
    policy.empiricalTransitionMass_abs_sub_transition_lt_of_not_mem_simultaneousCountBadEvent
      initialState batch hbatch defaultState coordinate hmargin nextState
  calc
    |batch.empiricalTransitionMass defaultState coordinate.stage
          coordinate.state coordinate.action nextState -
        (mdp.transition (coordinate.state, coordinate.action)).real {nextState}| ≤
        2 * radius / count := by
          simpa [radius, count] using le_of_lt hrandom
    _ ≤ 2 * radius / (expected - radius) :=
      div_le_div_of_nonneg_left (mul_nonneg (by norm_num) hradius)
        hdenominator (le_of_lt hlower)
    _ = policy.expectedCountTransitionCoordinateRadius initialState episodes delta
        coordinate.stage coordinate.state coordinate.action nextState := by
      rfl

omit [MeasurableSingletonClass State] [MeasurableSingletonClass Action]
    [Nonempty Action] in
/-- Full-coordinate margins make every reward-consistent empirical reward exact. -/
theorem empiricalReward_eq_of_not_mem_simultaneousCountBadEvent
    {mdp : MDP State Action} (policy : MarkovPolicy mdp)
    (initialState : Measure State) [IsProbabilityMeasure initialState]
    {episodes : Nat} {delta : Real} (batch : EpisodeBatch mdp episodes)
    (hbatch : batch ∉
      policy.simultaneousCountBadEvent initialState episodes delta)
    (hreward : batch.RewardConsistent)
    (hmargin : ∀ coordinate : VisitCoordinate mdp,
      simultaneousCountConfidenceRadius mdp episodes delta <
        coordinate.expectedCount policy initialState episodes)
    (stage : Fin mdp.horizon) (state : State) (action : Action) :
    batch.empiricalReward stage state action = mdp.reward state action := by
  let coordinate : VisitCoordinate mdp :=
    { stage := stage, state := state, action := action }
  have hcount : 0 < coordinate.count batch :=
    policy.visitCoordinate_count_pos_of_not_mem_simultaneousCountBadEvent
      initialState batch hbatch coordinate (hmargin coordinate)
  exact batch.empiricalReward_eq_reward_of_rewardConsistent hreward
    stage state action (by
      simpa [coordinate, VisitCoordinate.count] using Nat.ne_of_gt hcount)

namespace AllCoordinateConfidence

variable {mdp : MDP State Action} {episodes : Nat}
    (batch : EpisodeBatch mdp episodes) (defaultState : State)
    (transitionBudget rewardBound : Real)

/--
Exact empirical rewards and fixed nonnegative budgets give the explicit linear
absolute envelope for every recursive optimistic value.
-/
theorem upperValueRemaining_abs_le
    (hrewardExact : ∀ stage state action,
      batch.empiricalReward stage state action = mdp.reward state action)
    (hrewardBound : ∀ state action, |mdp.reward state action| ≤ rewardBound)
    (htransitionBudget_nonneg : 0 ≤ transitionBudget) :
    ∀ (remaining : Nat) (hremaining : remaining ≤ mdp.horizon) (state : State),
      |(mdp.allCoordinateEmpiricalFiniteBatchModel episodes batch defaultState
          transitionBudget).plan.upperValueRemaining remaining hremaining state| ≤
        empiricalFiniteBatchValueEnvelope rewardBound transitionBudget remaining := by
  let model := mdp.allCoordinateEmpiricalFiniteBatchModel episodes batch
    defaultState transitionBudget
  change ∀ (remaining : Nat) (hremaining : remaining ≤ mdp.horizon) (state : State),
    |model.plan.upperValueRemaining remaining hremaining state| ≤
      empiricalFiniteBatchValueEnvelope rewardBound transitionBudget remaining
  intro remaining
  induction remaining with
  | zero =>
      intro hremaining state
      simp [MDP.EstimatedModelPlan.upperValueRemaining,
        empiricalFiniteBatchValueEnvelope]
  | succ remaining ih =>
      intro hremaining state
      let stage := mdp.decisionStageRemaining remaining hremaining
      let tail := model.plan.upperValueRemaining remaining (by omega)
      let action := model.plan.optimisticAction stage tail state
      have htail : ∀ nextState, |tail nextState| ≤
          empiricalFiniteBatchValueEnvelope rewardBound transitionBudget remaining := by
        intro nextState
        exact ih (by omega) nextState
      have htransition :
          |model.plan.transitionValue stage tail state action| ≤
            empiricalFiniteBatchValueEnvelope rewardBound transitionBudget remaining := by
        rw [← Real.norm_eq_abs]
        have hnorm := norm_integral_le_of_norm_le_const
          (μ := model.plan.estimatedTransition stage (state, action))
          (C := empiricalFiniteBatchValueEnvelope rewardBound transitionBudget remaining)
          (Filter.Eventually.of_forall fun nextState => by
            rw [Real.norm_eq_abs]
            exact htail nextState)
        simpa [MDP.EstimatedModelPlan.transitionValue] using hnorm
      rw [MDP.EstimatedModelPlan.upperValueRemaining]
      change
        |batch.empiricalReward stage state action +
              model.plan.transitionValue stage tail state action +
            0 + transitionBudget| ≤
          empiricalFiniteBatchValueEnvelope rewardBound transitionBudget (remaining + 1)
      rw [hrewardExact stage state action]
      calc
        |mdp.reward state action +
              model.plan.transitionValue stage tail state action +
            0 + transitionBudget| =
            |(mdp.reward state action +
              model.plan.transitionValue stage tail state action) +
              transitionBudget| := by ring_nf
        _ ≤ |mdp.reward state action +
              model.plan.transitionValue stage tail state action| +
              |transitionBudget| := abs_add_le _ _
        _ ≤ (|mdp.reward state action| +
              |model.plan.transitionValue stage tail state action|) +
              |transitionBudget| := by
            have hsum := abs_add_le (mdp.reward state action)
              (model.plan.transitionValue stage tail state action)
            linarith
        _ ≤ rewardBound +
              empiricalFiniteBatchValueEnvelope rewardBound transitionBudget remaining +
              transitionBudget := by
            rw [abs_of_nonneg htransitionBudget_nonneg]
            linarith [hrewardBound state action, htransition]
        _ = empiricalFiniteBatchValueEnvelope rewardBound transitionBudget (remaining + 1) := by
            unfold empiricalFiniteBatchValueEnvelope
            rw [show ((remaining + 1 : Nat) : Real) =
              (remaining : Real) + 1 by norm_num]
            ring

end AllCoordinateConfidence

/--
Pathwise producer: full genuine occupancy margins, deterministic radius cover,
and reward consistency construct the complete raw finite-batch confidence object.
-/
noncomputable def allCoordinateEmpiricalFiniteBatchModelConfidence_of_not_mem
    {mdp : MDP State Action} (policy : MarkovPolicy mdp)
    (initialState : Measure State) [IsProbabilityMeasure initialState]
    {episodes : Nat} {delta : Real} (batch : EpisodeBatch mdp episodes)
    (hbatch : batch ∉
      policy.simultaneousCountBadEvent initialState episodes delta)
    (hreward : batch.RewardConsistent) (defaultState : State)
    (rewardBound transitionBudget : Real)
    (hrewardBound : ∀ state action, |mdp.reward state action| ≤ rewardBound)
    (htransitionBudget_nonneg : 0 ≤ transitionBudget)
    (hmargin : ∀ coordinate : VisitCoordinate mdp,
      simultaneousCountConfidenceRadius mdp episodes delta <
        coordinate.expectedCount policy initialState episodes)
    (hcover : ∀ (remaining : Nat)
        (hremaining : remaining + 1 ≤ mdp.horizon)
        (state : State) (action : Action),
      (∑ nextState,
          policy.expectedCountTransitionCoordinateRadius
              initialState episodes delta
              (mdp.decisionStageRemaining remaining hremaining)
              state action nextState *
            empiricalFiniteBatchValueEnvelope
              rewardBound transitionBudget remaining) ≤
        transitionBudget) :
    (mdp.allCoordinateEmpiricalFiniteBatchModel episodes batch defaultState
      transitionBudget).Confidence where
  transitionCoordinateRadius :=
    policy.expectedCountTransitionCoordinateRadius initialState episodes delta
  valueEnvelope :=
    empiricalFiniteBatchValueEnvelope rewardBound transitionBudget
  rewardError_le_radius := by
    intro stage state action
    change |batch.empiricalReward stage state action - mdp.reward state action| ≤ 0
    rw [policy.empiricalReward_eq_of_not_mem_simultaneousCountBadEvent
      initialState batch hbatch hreward hmargin stage state action]
    simp
  transitionFrequencyError_le_radius := by
    intro remaining hremaining state action nextState
    let coordinate : VisitCoordinate mdp :=
      { stage := mdp.decisionStageRemaining remaining hremaining
        state := state
        action := action }
    simpa [coordinate] using
      policy.empiricalTransitionMass_abs_sub_transition_le_expectedCountRadius_of_not_mem
        initialState batch hbatch defaultState coordinate
          (hmargin coordinate) nextState
  upperValue_abs_le_envelope := by
    intro remaining hremaining state
    exact AllCoordinateConfidence.upperValueRemaining_abs_le
      (mdp := mdp) (batch := batch) (defaultState := defaultState)
      (transitionBudget := transitionBudget) (rewardBound := rewardBound)
        (policy.empiricalReward_eq_of_not_mem_simultaneousCountBadEvent
          initialState batch hbatch hreward hmargin)
        hrewardBound htransitionBudget_nonneg
        remaining (by omega) state
  transitionRadius_cover := by
    intro remaining hremaining state action
    simpa [MDP.allCoordinateEmpiricalFiniteBatchModel] using
      hcover remaining hremaining state action

/--
Mapped-iid confidence endpoint with the unchanged simultaneous-event failure
budget. No additional reward or confidence event is introduced.
-/
theorem iidEpisodeBatch_allCoordinate_finiteBatchModel_confidence
    {mdp : MDP State Action} (policy : MarkovPolicy mdp)
    (initialState : Measure State) [IsProbabilityMeasure initialState]
    (episodes : Nat) (hepisodes : 0 < episodes)
    (delta : Real) (hdelta : 0 < delta) (hdelta_le_one : delta ≤ 1)
    (defaultState : State) (rewardBound transitionBudget : Real)
    (hrewardBound : ∀ state action, |mdp.reward state action| ≤ rewardBound)
    (htransitionBudget_nonneg : 0 ≤ transitionBudget)
    (hmargin : ∀ coordinate : VisitCoordinate mdp,
      simultaneousCountConfidenceRadius mdp episodes delta <
        coordinate.expectedCount policy initialState episodes)
    (hcover : ∀ (remaining : Nat)
        (hremaining : remaining + 1 ≤ mdp.horizon)
        (state : State) (action : Action),
      (∑ nextState,
          policy.expectedCountTransitionCoordinateRadius
              initialState episodes delta
              (mdp.decisionStageRemaining remaining hremaining)
              state action nextState *
            empiricalFiniteBatchValueEnvelope
              rewardBound transitionBudget remaining) ≤
        transitionBudget) :
    MeasurableSet
        (policy.simultaneousCountBadEvent initialState episodes delta) ∧
      (policy.iidEpisodeBatchMeasure initialState episodes)
          (policy.simultaneousCountBadEvent initialState episodes delta) ≤
        ENNReal.ofReal delta ∧
      ∀ᵐ batch ∂policy.iidEpisodeBatchMeasure initialState episodes,
        batch ∉ policy.simultaneousCountBadEvent initialState episodes delta →
          Nonempty
            (mdp.allCoordinateEmpiricalFiniteBatchModel episodes batch defaultState
              transitionBudget).Confidence := by
  refine ⟨policy.measurableSet_simultaneousCountBadEvent
      initialState episodes delta,
    policy.iidEpisodeBatch_simultaneousCountBadEvent_le
      initialState episodes hepisodes delta hdelta hdelta_le_one, ?_⟩
  filter_upwards [policy.iidEpisodeBatchMeasure_rewardConsistent_ae
    initialState episodes] with batch hreward
  intro hbatch
  exact ⟨policy.allCoordinateEmpiricalFiniteBatchModelConfidence_of_not_mem
    initialState batch hbatch hreward defaultState rewardBound transitionBudget
      hrewardBound htransitionBudget_nonneg hmargin hcover⟩

/--
The produced confidence object immediately yields global optimism and the
existing selected-radius single-episode expected-regret bound almost everywhere.
-/
theorem iidEpisodeBatch_allCoordinate_optimism_and_expectedRegret
    {mdp : MDP State Action} (policy : MarkovPolicy mdp)
    (initialState : Measure State) [IsProbabilityMeasure initialState]
    (episodes : Nat) (hepisodes : 0 < episodes)
    (delta : Real) (hdelta : 0 < delta) (hdelta_le_one : delta ≤ 1)
    (defaultState : State) (rewardBound transitionBudget : Real)
    (hrewardBound : ∀ state action, |mdp.reward state action| ≤ rewardBound)
    (htransitionBudget_nonneg : 0 ≤ transitionBudget)
    (hmargin : ∀ coordinate : VisitCoordinate mdp,
      simultaneousCountConfidenceRadius mdp episodes delta <
        coordinate.expectedCount policy initialState episodes)
    (hcover : ∀ (remaining : Nat)
        (hremaining : remaining + 1 ≤ mdp.horizon)
        (state : State) (action : Action),
      (∑ nextState,
          policy.expectedCountTransitionCoordinateRadius
              initialState episodes delta
              (mdp.decisionStageRemaining remaining hremaining)
              state action nextState *
            empiricalFiniteBatchValueEnvelope
              rewardBound transitionBudget remaining) ≤
        transitionBudget) :
    MeasurableSet
        (policy.simultaneousCountBadEvent initialState episodes delta) ∧
      (policy.iidEpisodeBatchMeasure initialState episodes)
          (policy.simultaneousCountBadEvent initialState episodes delta) ≤
        ENNReal.ofReal delta ∧
      ∀ᵐ batch ∂policy.iidEpisodeBatchMeasure initialState episodes,
        batch ∉ policy.simultaneousCountBadEvent initialState episodes delta →
          let model := mdp.allCoordinateEmpiricalFiniteBatchModel
            episodes batch defaultState transitionBudget
          (∀ state,
              mdp.optimalValueRemaining mdp.horizon le_rfl state ≤
                model.plan.upperValueRemaining mdp.horizon le_rfl state) ∧
            model.plan.optimisticPolicy.expectedRegret initialState ≤
              model.plan.optimisticPolicy.occupancySumRemaining
                (fun remaining hremaining state =>
                  2 * model.plan.selectedRadiusRemaining
                    remaining hremaining state)
                mdp.horizon le_rfl initialState := by
  obtain ⟨hmeasurable, htail, hconfidence⟩ :=
    policy.iidEpisodeBatch_allCoordinate_finiteBatchModel_confidence
      initialState episodes hepisodes delta hdelta hdelta_le_one defaultState
        rewardBound transitionBudget hrewardBound htransitionBudget_nonneg
        hmargin hcover
  refine ⟨hmeasurable, htail, ?_⟩
  filter_upwards [hconfidence] with batch hbatchConfidence
  intro hbatch
  obtain ⟨confidence⟩ := hbatchConfidence hbatch
  exact confidence
    |>.optimism_and_expectedRegret_le_two_occupancySelectedRadiusRemaining
      initialState

end MarkovPolicy
end FiniteHorizonRL
end BanditRLProof
