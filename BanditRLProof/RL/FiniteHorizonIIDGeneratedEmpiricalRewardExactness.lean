import BanditRLProof.RL.FiniteHorizonIIDTrajectoryBatch
import BanditRLProof.RL.FiniteHorizonIIDEligibleEmpiricalTransitionConfidence

/-!
# Generated empirical reward exactness for finite-horizon iid batches

The finite-horizon MDP surface has a deterministic reward function. Consequently,
records extracted from genuine trajectories have exact empirical rewards at every
visited coordinate; no reward concentration or additional failure budget is
needed. This module records that structural fact and combines it with the existing
eligible empirical-transition confidence event.
-/

open MeasureTheory
open scoped ENNReal ProbabilityTheory

universe u v

namespace BanditRLProof
namespace FiniteHorizonRL

variable {State : Type u} {Action : Type v}
    [MeasurableSpace State] [MeasurableSpace Action]
    [Fintype State] [Fintype Action]

namespace EpisodeBatch

/-- Every recorded reward agrees with the MDP reward at its recorded state and action. -/
def RewardConsistent {mdp : MDP State Action} {episodes : Nat}
    (batch : EpisodeBatch mdp episodes) : Prop :=
  ∀ episode stage,
    (batch episode stage).reward =
      mdp.reward (batch episode stage).state (batch episode stage).action

/-- Reward consistency is a measurable property of finite episode batches. -/
theorem measurableSet_rewardConsistent
    {mdp : MDP State Action} {episodes : Nat} :
    MeasurableSet {batch : EpisodeBatch mdp episodes | batch.RewardConsistent} := by
  simp only [RewardConsistent, Set.setOf_forall]
  apply MeasurableSet.iInter
  intro episode
  apply MeasurableSet.iInter
  intro stage
  have hstep : Measurable
      (fun batch : EpisodeBatch mdp episodes => batch episode stage) :=
    (measurable_pi_apply stage).comp (measurable_pi_apply episode)
  have hstate : Measurable
      (fun batch : EpisodeBatch mdp episodes => (batch episode stage).state) :=
    EpisodeStep.measurable_state.comp hstep
  have haction : Measurable
      (fun batch : EpisodeBatch mdp episodes => (batch episode stage).action) :=
    EpisodeStep.measurable_action.comp hstep
  exact measurableSet_eq_fun (EpisodeStep.measurable_reward.comp hstep)
    (mdp.measurable_reward.comp (hstate.prodMk haction))

/-- In a reward-consistent batch, the reward sum is visit count times the true reward. -/
theorem rewardSum_eq_visitCount_mul_reward_of_rewardConsistent
    [DecidableEq State] [DecidableEq Action]
    {mdp : MDP State Action} {episodes : Nat}
    (batch : EpisodeBatch mdp episodes) (hbatch : batch.RewardConsistent)
    (stage : Fin mdp.horizon) (state : State) (action : Action) :
    batch.rewardSum stage state action =
      (batch.visitCount stage state action : Real) * mdp.reward state action := by
  classical
  unfold rewardSum visitCount
  rw [Nat.cast_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro episode _
  by_cases hvisit :
      (batch episode stage).state = state ∧
        (batch episode stage).action = action
  · simp only [hvisit]
    simpa [hvisit.1, hvisit.2] using hbatch episode stage
  · simp [hvisit]

/-- Positive visits cancel the denominator, so empirical reward is exact. -/
theorem empiricalReward_eq_reward_of_rewardConsistent
    [DecidableEq State] [DecidableEq Action]
    {mdp : MDP State Action} {episodes : Nat}
    (batch : EpisodeBatch mdp episodes) (hbatch : batch.RewardConsistent)
    (stage : Fin mdp.horizon) (state : State) (action : Action)
    (hcount : batch.visitCount stage state action ≠ 0) :
    batch.empiricalReward stage state action = mdp.reward state action := by
  have hcountReal : (batch.visitCount stage state action : Real) ≠ 0 := by
    exact_mod_cast hcount
  rw [empiricalReward,
    batch.rewardSum_eq_visitCount_mul_reward_of_rewardConsistent hbatch]
  exact mul_div_cancel_left₀ _ hcountReal

end EpisodeBatch

namespace MDP

/-- Every finite episode batch extracted from genuine trajectories is reward-consistent. -/
theorem episodeBatchOfTrajectories_rewardConsistent
    (mdp : MDP State Action) (episodes : Nat)
    (trajectories : Fin episodes ->
      State × StepTrace Action State mdp.horizon) :
    (mdp.episodeBatchOfTrajectories episodes trajectories).RewardConsistent := by
  intro episode stage
  rfl

/-- Generated reward sums are exactly visit counts times deterministic MDP rewards. -/
theorem episodeBatchOfTrajectories_rewardSum_eq_visitCount_mul_reward
    [DecidableEq State] [DecidableEq Action]
    (mdp : MDP State Action) (episodes : Nat)
    (trajectories : Fin episodes ->
      State × StepTrace Action State mdp.horizon)
    (stage : Fin mdp.horizon) (state : State) (action : Action) :
    (mdp.episodeBatchOfTrajectories episodes trajectories).rewardSum
        stage state action =
      ((mdp.episodeBatchOfTrajectories episodes trajectories).visitCount
          stage state action : Real) * mdp.reward state action := by
  exact EpisodeBatch.rewardSum_eq_visitCount_mul_reward_of_rewardConsistent
    _ (mdp.episodeBatchOfTrajectories_rewardConsistent episodes trajectories)
      stage state action

/-- A generated empirical reward is exact whenever its visit count is nonzero. -/
theorem episodeBatchOfTrajectories_empiricalReward_eq_reward
    [DecidableEq State] [DecidableEq Action]
    (mdp : MDP State Action) (episodes : Nat)
    (trajectories : Fin episodes ->
      State × StepTrace Action State mdp.horizon)
    (stage : Fin mdp.horizon) (state : State) (action : Action)
    (hcount :
      (mdp.episodeBatchOfTrajectories episodes trajectories).visitCount
        stage state action ≠ 0) :
    (mdp.episodeBatchOfTrajectories episodes trajectories).empiricalReward
        stage state action = mdp.reward state action := by
  exact EpisodeBatch.empiricalReward_eq_reward_of_rewardConsistent
    _ (mdp.episodeBatchOfTrajectories_rewardConsistent episodes trajectories)
      stage state action hcount

end MDP

namespace MarkovPolicy

variable [DecidableEq State] [DecidableEq Action]
    [MeasurableSingletonClass State] [MeasurableSingletonClass Action]

omit [DecidableEq State] [DecidableEq Action] in
/-- The mapped iid episode-batch law is supported a.e. on reward-consistent records. -/
theorem iidEpisodeBatchMeasure_rewardConsistent_ae
    {mdp : MDP State Action} (policy : MarkovPolicy mdp)
    (initialState : Measure State) [IsProbabilityMeasure initialState]
    (episodes : Nat) :
    ∀ᵐ batch ∂policy.iidEpisodeBatchMeasure initialState episodes,
      batch.RewardConsistent := by
  unfold iidEpisodeBatchMeasure
  rw [ae_map_iff
    (mdp.measurable_episodeBatchOfTrajectories episodes).aemeasurable
    EpisodeBatch.measurableSet_rewardConsistent]
  exact Filter.Eventually.of_forall fun trajectories =>
    mdp.episodeBatchOfTrajectories_rewardConsistent episodes trajectories

/--
On the simultaneous good event, reward consistency gives exact empirical reward
and the existing eligible margin gives every next-state transition bound.
-/
theorem empiricalReward_eq_and_transition_lt_of_not_mem_simultaneousCountBadEvent
    {mdp : MDP State Action} (policy : MarkovPolicy mdp)
    (initialState : Measure State) [IsProbabilityMeasure initialState]
    {episodes : Nat} {delta : Real} (batch : EpisodeBatch mdp episodes)
    (hbatch : batch ∉
      policy.simultaneousCountBadEvent initialState episodes delta)
    (hreward : batch.RewardConsistent) (defaultState : State)
    (coordinate : VisitCoordinate mdp)
    (hmargin : simultaneousCountConfidenceRadius mdp episodes delta <
      coordinate.expectedCount policy initialState episodes) :
    batch.empiricalReward coordinate.stage coordinate.state coordinate.action =
        mdp.reward coordinate.state coordinate.action ∧
      ∀ nextState,
        |batch.empiricalTransitionMass defaultState coordinate.stage
              coordinate.state coordinate.action nextState -
            (mdp.transition
              (coordinate.state, coordinate.action)).real {nextState}| <
          2 * simultaneousCountConfidenceRadius mdp episodes delta /
            (coordinate.count batch : Real) := by
  have hcount : 0 < coordinate.count batch :=
    policy.visitCoordinate_count_pos_of_not_mem_simultaneousCountBadEvent
      initialState batch hbatch coordinate hmargin
  constructor
  · exact batch.empiricalReward_eq_reward_of_rewardConsistent hreward
      coordinate.stage coordinate.state coordinate.action
        (Nat.ne_of_gt hcount)
  · intro nextState
    exact policy.empiricalTransitionMass_abs_sub_transition_lt_of_not_mem_simultaneousCountBadEvent
      initialState batch hbatch defaultState coordinate hmargin nextState

/-- Generated trajectory batches satisfy the reward side of the same good-event endpoint. -/
theorem episodeBatchOfTrajectories_empiricalReward_eq_and_transition_lt
    {mdp : MDP State Action} (policy : MarkovPolicy mdp)
    (initialState : Measure State) [IsProbabilityMeasure initialState]
    {episodes : Nat} {delta : Real}
    (trajectories : Fin episodes ->
      State × StepTrace Action State mdp.horizon)
    (hbatch : mdp.episodeBatchOfTrajectories episodes trajectories ∉
      policy.simultaneousCountBadEvent initialState episodes delta)
    (defaultState : State) (coordinate : VisitCoordinate mdp)
    (hmargin : simultaneousCountConfidenceRadius mdp episodes delta <
      coordinate.expectedCount policy initialState episodes) :
    (mdp.episodeBatchOfTrajectories episodes trajectories).empiricalReward
          coordinate.stage coordinate.state coordinate.action =
        mdp.reward coordinate.state coordinate.action ∧
      ∀ nextState,
        |(mdp.episodeBatchOfTrajectories episodes trajectories).empiricalTransitionMass
              defaultState coordinate.stage coordinate.state coordinate.action nextState -
            (mdp.transition
              (coordinate.state, coordinate.action)).real {nextState}| <
          2 * simultaneousCountConfidenceRadius mdp episodes delta /
            (coordinate.count
              (mdp.episodeBatchOfTrajectories episodes trajectories) : Real) := by
  exact policy.empiricalReward_eq_and_transition_lt_of_not_mem_simultaneousCountBadEvent
    initialState _ hbatch
      (mdp.episodeBatchOfTrajectories_rewardConsistent episodes trajectories)
      defaultState coordinate hmargin

/--
Route endpoint: the existing global-delta event simultaneously controls every
eligible transition coordinate, while reward-consistent batches have zero reward
error at those same positive-count coordinates.
-/
theorem iidEpisodeBatch_eligible_empiricalReward_exact_and_transition_confidence
    {mdp : MDP State Action} (policy : MarkovPolicy mdp)
    (initialState : Measure State) [IsProbabilityMeasure initialState]
    (episodes : Nat) (hepisodes : 0 < episodes)
    (delta : Real) (hdelta : 0 < delta) (hdelta_le_one : delta ≤ 1)
    (defaultState : State) (eligible : Finset (VisitCoordinate mdp))
    (hmargin : ∀ coordinate ∈ eligible,
      simultaneousCountConfidenceRadius mdp episodes delta <
        coordinate.expectedCount policy initialState episodes) :
    MeasurableSet
        (policy.simultaneousCountBadEvent initialState episodes delta) ∧
      (policy.iidEpisodeBatchMeasure initialState episodes)
          (policy.simultaneousCountBadEvent initialState episodes delta) ≤
        ENNReal.ofReal delta ∧
      ∀ᵐ batch ∂policy.iidEpisodeBatchMeasure initialState episodes,
        batch ∉ policy.simultaneousCountBadEvent initialState episodes delta ->
          ∀ coordinate ∈ eligible,
            batch.empiricalReward coordinate.stage coordinate.state
                  coordinate.action =
                mdp.reward coordinate.state coordinate.action ∧
              ∀ nextState,
                |batch.empiricalTransitionMass defaultState coordinate.stage
                      coordinate.state coordinate.action nextState -
                    (mdp.transition
                      (coordinate.state, coordinate.action)).real {nextState}| <
                  2 * simultaneousCountConfidenceRadius mdp episodes delta /
                    (coordinate.count batch : Real) := by
  refine ⟨policy.measurableSet_simultaneousCountBadEvent
      initialState episodes delta,
    policy.iidEpisodeBatch_simultaneousCountBadEvent_le
      initialState episodes hepisodes delta hdelta hdelta_le_one, ?_⟩
  filter_upwards [policy.iidEpisodeBatchMeasure_rewardConsistent_ae
    initialState episodes] with batch hreward
  intro hbatch coordinate hcoordinate
  exact policy.empiricalReward_eq_and_transition_lt_of_not_mem_simultaneousCountBadEvent
    initialState batch hbatch hreward defaultState coordinate
      (hmargin coordinate hcoordinate)

end MarkovPolicy
end FiniteHorizonRL
end BanditRLProof
