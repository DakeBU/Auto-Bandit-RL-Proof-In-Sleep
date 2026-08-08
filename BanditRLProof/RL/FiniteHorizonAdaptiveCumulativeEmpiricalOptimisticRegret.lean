import BanditRLProof.RL.FiniteHorizonAdaptiveEmpiricalOptimisticOccupancyEnvelope

/-!
# Adaptive cumulative empirical optimistic regret contract

This module changes the adaptive empirical planner from a latest-batch summary
to the sum of every transition count in the observed finite prefix.  A
nonnegative antitone count-radius object makes the plan's transition radius a
function of the cumulative state-action visit count.  The cumulative selector
is measurable, so it also defines a concrete exploratory adaptive batch source.

The route terminates at optimism and recommended-policy expected regret under
one explicit global cumulative coordinate-confidence contract.  Producing that
contract from adaptive cumulative count martingales remains downstream; no
such concentration theorem is assumed to have been proved here.
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
    [Nonempty State] [Nonempty Action]

/-- A nonnegative transition radius that can only decrease as visits accumulate. -/
structure TransitionCountRadius where
  radius : Nat -> Real
  nonneg : forall count, 0 <= radius count
  antitone : Antitone radius

namespace TransitionCountRadius

/-- A finite linear-decay radius, useful as an executable shrinking-radius canary. -/
def linearDecay (budget : Nat) : TransitionCountRadius where
  radius count := (budget - count : Nat)
  nonneg count := by positivity
  antitone := by
    intro left right hle
    change ((budget - right : Nat) : Real) <= (budget - left : Nat)
    exact_mod_cast Nat.sub_le_sub_left hle budget

end TransitionCountRadius

namespace EpisodeBatchPrefix

/-- Sum all transition-count coordinates in a nonempty finite batch prefix. -/
def cumulativeTransitionCountSummary
    {mdp : MDP State Action} {episodes n : Nat}
    (history : EpisodeBatchPrefix mdp episodes n) : TransitionCountSummary mdp :=
  fun stage state action nextState =>
    ∑ i : Fin (n + 1),
      (history ⟨i, Finset.mem_Iic.mpr (Nat.le_of_lt_succ i.isLt)⟩).transitionCount
        stage state action nextState

omit [Nonempty State] [Nonempty Action] in
/-- The complete cumulative transition-count summary is history measurable. -/
theorem measurable_cumulativeTransitionCountSummary
    {mdp : MDP State Action} {episodes n : Nat} :
    Measurable
      (cumulativeTransitionCountSummary :
        EpisodeBatchPrefix mdp episodes n -> TransitionCountSummary mdp) := by
  refine measurable_pi_lambda _ fun stage => ?_
  refine measurable_pi_lambda _ fun state => ?_
  refine measurable_pi_lambda _ fun action => ?_
  refine measurable_pi_lambda _ fun nextState => ?_
  change Measurable fun history : EpisodeBatchPrefix mdp episodes n =>
    ∑ i : Fin (n + 1),
      (history ⟨i, Finset.mem_Iic.mpr (Nat.le_of_lt_succ i.isLt)⟩).transitionCount
        stage state action nextState
  refine Finset.measurable_sum Finset.univ fun i _hi => ?_
  let index : Finset.Iic n :=
    ⟨i, Finset.mem_Iic.mpr (Nat.le_of_lt_succ i.isLt)⟩
  have hsummary : Measurable fun history : EpisodeBatchPrefix mdp episodes n =>
      (history index).transitionCountSummary :=
    EpisodeBatch.measurable_transitionCountSummary.comp
      (measurable_pi_apply index)
  have hstage := (measurable_pi_apply stage).comp hsummary
  have hstate := (measurable_pi_apply state).comp hstage
  have haction := (measurable_pi_apply action).comp hstate
  have hnextState := (measurable_pi_apply nextState).comp haction
  simpa [index, EpisodeBatch.transitionCountSummary] using hnextState

omit [MeasurableSingletonClass State] [MeasurableSingletonClass Action]
    [Nonempty State] [Nonempty Action] in
/-- Cumulative next-state counts still partition the cumulative visit count. -/
theorem cumulativeTransitionCountSummary_visitCount
    {mdp : MDP State Action} {episodes n : Nat}
    (history : EpisodeBatchPrefix mdp episodes n)
    (stage : Fin mdp.horizon) (state : State) (action : Action) :
    history.cumulativeTransitionCountSummary.visitCount stage state action =
      ∑ i : Fin (n + 1),
        (history ⟨i, Finset.mem_Iic.mpr (Nat.le_of_lt_succ i.isLt)⟩).visitCount
          stage state action := by
  classical
  unfold TransitionCountSummary.visitCount cumulativeTransitionCountSummary
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _hi
  exact
    (history ⟨i, Finset.mem_Iic.mpr (Nat.le_of_lt_succ i.isLt)⟩).sum_transitionCount_eq_visitCount
      stage state action

end EpisodeBatchPrefix

/-- Cumulative count summary through trajectory coordinate `round`. -/
def cumulativeTransitionCountSummaryAt
    {mdp : MDP State Action} {episodes : Nat}
    (trajectory : EpisodeBatchTrajectory mdp episodes) (round : Nat) :
    TransitionCountSummary mdp :=
  EpisodeBatchPrefix.cumulativeTransitionCountSummary
    (Preorder.frestrictLe round trajectory)

omit [MeasurableSingletonClass State] [MeasurableSingletonClass Action]
    [Nonempty State] [Nonempty Action] in
/-- Extending the trajectory prefix adds exactly the new batch coordinate. -/
theorem cumulativeTransitionCountSummaryAt_succ
    {mdp : MDP State Action} {episodes : Nat}
    (trajectory : EpisodeBatchTrajectory mdp episodes) (round : Nat)
    (stage : Fin mdp.horizon) (state : State) (action : Action)
    (nextState : State) :
    cumulativeTransitionCountSummaryAt trajectory (round + 1)
        stage state action nextState =
      cumulativeTransitionCountSummaryAt trajectory round
          stage state action nextState +
        (trajectory (round + 1)).transitionCount
          stage state action nextState := by
  unfold cumulativeTransitionCountSummaryAt
    EpisodeBatchPrefix.cumulativeTransitionCountSummary
  rw [Fin.sum_univ_castSucc]
  rfl

omit [MeasurableSingletonClass State] [MeasurableSingletonClass Action]
    [Nonempty State] [Nonempty Action] in
/-- Every cumulative state-action visit count is monotone across rounds. -/
theorem cumulativeTransitionCountSummaryAt_visitCount_le_succ
    {mdp : MDP State Action} {episodes : Nat}
    (trajectory : EpisodeBatchTrajectory mdp episodes) (round : Nat)
    (stage : Fin mdp.horizon) (state : State) (action : Action) :
    (cumulativeTransitionCountSummaryAt trajectory round).visitCount
        stage state action <=
      (cumulativeTransitionCountSummaryAt trajectory (round + 1)).visitCount
        stage state action := by
  unfold TransitionCountSummary.visitCount
  apply Finset.sum_le_sum
  intro nextState _hnextState
  rw [cumulativeTransitionCountSummaryAt_succ]
  omega

omit [MeasurableSingletonClass State] [MeasurableSingletonClass Action]
    [Nonempty State] [Nonempty Action] in
/-- Count-antitone radii shrink along every accumulated state-action row. -/
theorem TransitionCountRadius.radius_cumulativeVisitCount_succ_le
    {mdp : MDP State Action} {episodes : Nat}
    (countRadius : TransitionCountRadius)
    (trajectory : EpisodeBatchTrajectory mdp episodes) (round : Nat)
    (stage : Fin mdp.horizon) (state : State) (action : Action) :
    countRadius.radius
        ((cumulativeTransitionCountSummaryAt trajectory (round + 1)).visitCount
          stage state action) <=
      countRadius.radius
        ((cumulativeTransitionCountSummaryAt trajectory round).visitCount
          stage state action) :=
  countRadius.antitone
    (cumulativeTransitionCountSummaryAt_visitCount_le_succ
      trajectory round stage state action)

namespace TransitionCountSummary

/-- Known-reward empirical plan with a radius selected from cumulative visits. -/
noncomputable def countRadiusOptimisticPlan
    (mdp : MDP State Action) (summary : TransitionCountSummary mdp)
    (defaultState : State) (countRadius : TransitionCountRadius) :
    mdp.EstimatedModelPlan where
  estimatedReward _stage := mdp.reward
  measurable_estimatedReward _stage := mdp.measurable_reward
  estimatedTransition stage := summary.empiricalTransitionKernel defaultState stage
  estimatedTransition_isMarkov stage :=
    summary.empiricalTransitionKernel_isMarkov defaultState stage
  rewardRadius _stage _state _action := 0
  measurable_rewardRadius _stage := measurable_const
  transitionRadius stage state action :=
    countRadius.radius (summary.visitCount stage state action)
  measurable_transitionRadius _stage := measurable_of_finite _

omit [DecidableEq Action] [Nonempty State] in
/-- Every count-radius optimistic value is controlled by the radius at zero visits. -/
theorem countRadiusOptimisticPlan_upperValueRemaining_abs_le
    (mdp : MDP State Action) (summary : TransitionCountSummary mdp)
    (defaultState : State) (countRadius : TransitionCountRadius)
    (rewardBound : Real)
    (hrewardBound : forall state action, |mdp.reward state action| <= rewardBound) :
    forall (remaining : Nat) (hremaining : remaining <= mdp.horizon)
      (state : State),
      |(summary.countRadiusOptimisticPlan mdp defaultState countRadius).upperValueRemaining
          remaining hremaining state| <=
        empiricalFiniteBatchValueEnvelope
          rewardBound (countRadius.radius 0) remaining := by
  let plan := summary.countRadiusOptimisticPlan mdp defaultState countRadius
  intro remaining
  induction remaining with
  | zero =>
      intro hremaining state
      simp [MDP.EstimatedModelPlan.upperValueRemaining,
        empiricalFiniteBatchValueEnvelope]
  | succ remaining ih =>
      intro hremaining state
      let stage := mdp.decisionStageRemaining remaining hremaining
      let tail := plan.upperValueRemaining remaining (by omega)
      let action := plan.optimisticAction stage tail state
      have htail : forall nextState,
          |tail nextState| <=
            empiricalFiniteBatchValueEnvelope
              rewardBound (countRadius.radius 0) remaining := by
        intro nextState
        exact ih (by omega) nextState
      have htransition :
          |plan.transitionValue stage tail state action| <=
            empiricalFiniteBatchValueEnvelope
              rewardBound (countRadius.radius 0) remaining := by
        rw [← Real.norm_eq_abs]
        have hnorm := norm_integral_le_of_norm_le_const
          (μ := plan.estimatedTransition stage (state, action))
          (C := empiricalFiniteBatchValueEnvelope
            rewardBound (countRadius.radius 0) remaining)
          (Filter.Eventually.of_forall fun nextState => by
            rw [Real.norm_eq_abs]
            exact htail nextState)
        simpa [MDP.EstimatedModelPlan.transitionValue] using hnorm
      have hradius :
          countRadius.radius (summary.visitCount stage state action) <=
            countRadius.radius 0 :=
        countRadius.antitone (Nat.zero_le _)
      rw [MDP.EstimatedModelPlan.upperValueRemaining]
      change
        |mdp.reward state action +
              plan.transitionValue stage tail state action +
            0 + countRadius.radius (summary.visitCount stage state action)| <=
          empiricalFiniteBatchValueEnvelope
            rewardBound (countRadius.radius 0) (remaining + 1)
      calc
        |mdp.reward state action +
              plan.transitionValue stage tail state action +
            0 + countRadius.radius (summary.visitCount stage state action)| =
            |(mdp.reward state action +
              plan.transitionValue stage tail state action) +
                countRadius.radius (summary.visitCount stage state action)| := by
              ring_nf
        _ <= |mdp.reward state action +
              plan.transitionValue stage tail state action| +
                |countRadius.radius
                  (summary.visitCount stage state action)| := abs_add_le _ _
        _ <= (|mdp.reward state action| +
              |plan.transitionValue stage tail state action|) +
                |countRadius.radius
                  (summary.visitCount stage state action)| := by
            have hsum := abs_add_le (mdp.reward state action)
              (plan.transitionValue stage tail state action)
            linarith
        _ <= rewardBound +
              empiricalFiniteBatchValueEnvelope
                rewardBound (countRadius.radius 0) remaining +
              countRadius.radius 0 := by
            rw [abs_of_nonneg (countRadius.nonneg _)]
            linarith [hrewardBound state action, htransition, hradius]
        _ = empiricalFiniteBatchValueEnvelope
              rewardBound (countRadius.radius 0) (remaining + 1) := by
            unfold empiricalFiniteBatchValueEnvelope
            rw [show ((remaining + 1 : Nat) : Real) =
              (remaining : Real) + 1 by norm_num]
            ring

omit [DecidableEq Action] [Nonempty State] in
/-- The cumulative count-radius plan selects exactly its chosen row radius. -/
theorem countRadiusOptimisticPlan_selectedRadiusRemaining
    (mdp : MDP State Action) (summary : TransitionCountSummary mdp)
    (defaultState : State) (countRadius : TransitionCountRadius)
    (remaining : Nat) (hremaining : remaining + 1 <= mdp.horizon)
    (state : State) :
    (summary.countRadiusOptimisticPlan mdp defaultState countRadius).selectedRadiusRemaining
        remaining hremaining state =
      countRadius.radius
        (summary.visitCount
          (mdp.decisionStageRemaining remaining hremaining) state
          ((summary.countRadiusOptimisticPlan mdp defaultState countRadius).optimisticAction
            (mdp.decisionStageRemaining remaining hremaining)
            ((summary.countRadiusOptimisticPlan mdp defaultState countRadius).upperValueRemaining
              remaining (by omega)) state)) := by
  simp [MDP.EstimatedModelPlan.selectedRadiusRemaining,
    countRadiusOptimisticPlan]

/-- Deterministic optimistic table selected from a cumulative count summary. -/
noncomputable def countRadiusOptimisticPolicyTable
    (mdp : MDP State Action) (summary : TransitionCountSummary mdp)
    (defaultState : State) (countRadius : TransitionCountRadius) :
    DeterministicMarkovPolicyTable mdp :=
  fun stage =>
    (summary.countRadiusOptimisticPlan mdp defaultState countRadius).optimisticActionAt stage

omit [DecidableEq Action] [Nonempty State] in
/-- The table interpretation is the cumulative count-radius plan's policy. -/
theorem countRadiusOptimisticPolicyTable_toMarkovPolicy
    (mdp : MDP State Action) (summary : TransitionCountSummary mdp)
    (defaultState : State) (countRadius : TransitionCountRadius) :
    (summary.countRadiusOptimisticPolicyTable mdp defaultState countRadius).toMarkovPolicy =
      (summary.countRadiusOptimisticPlan mdp defaultState countRadius).optimisticPolicy := by
  rfl

end TransitionCountSummary

/-- Cumulative known-reward optimistic plan recommended after one trajectory prefix. -/
noncomputable def adaptiveCumulativeEmpiricalOptimisticPlanAt
    {mdp : MDP State Action} {episodes : Nat}
    (trajectory : EpisodeBatchTrajectory mdp episodes)
    (defaultState : State) (countRadius : TransitionCountRadius) (round : Nat) :
    mdp.EstimatedModelPlan :=
  (cumulativeTransitionCountSummaryAt trajectory round).countRadiusOptimisticPlan
    mdp defaultState countRadius

/-- Sum of expected regrets of all cumulative empirical recommendations. -/
noncomputable def adaptiveCumulativeEmpiricalOptimisticRecommendedExpectedRegret
    {mdp : MDP State Action} {initialState : Measure State}
    [IsProbabilityMeasure initialState] {episodes : Nat}
    (trajectory : EpisodeBatchTrajectory mdp episodes)
    (defaultState : State) (countRadius : TransitionCountRadius)
    (rounds : Nat) : Real :=
  ∑ round : Fin rounds,
    (adaptiveCumulativeEmpiricalOptimisticPlanAt
      trajectory defaultState countRadius round).optimisticPolicy.expectedRegret initialState

namespace AdaptiveCumulativeEmpiricalOptimisticSource

/-- Cumulative optimistic table selected from every observed batch in a prefix. -/
noncomputable def successorTable
    {mdp : MDP State Action} {episodes : Nat} (defaultState : State)
    (countRadius : TransitionCountRadius) (n : Nat)
    (history : EpisodeBatchPrefix mdp episodes n) :
    DeterministicMarkovPolicyTable mdp :=
  history.cumulativeTransitionCountSummary.countRadiusOptimisticPolicyTable
    mdp defaultState countRadius

omit [Nonempty State] in
/-- The cumulative history-to-table selector is measurable. -/
theorem measurable_successorTable
    {mdp : MDP State Action} {episodes : Nat} (defaultState : State)
    (countRadius : TransitionCountRadius) (n : Nat) :
    Measurable
      (successorTable (mdp := mdp) (episodes := episodes)
        defaultState countRadius n) :=
  (measurable_of_countable
      (fun summary : TransitionCountSummary mdp =>
        summary.countRadiusOptimisticPolicyTable mdp defaultState countRadius)).comp
    EpisodeBatchPrefix.measurable_cumulativeTransitionCountSummary

/-- Exploratory behavior source centered on cumulative empirical recommendations. -/
noncomputable def exploratorySource
    (mdp : MDP State Action) (initialState : Measure State)
    [IsProbabilityMeasure initialState] (episodes : Nat)
    (initialTable : DeterministicMarkovPolicyTable mdp)
    (defaultState : State) (countRadius : TransitionCountRadius)
    (explorationRate : NNReal) (hexplorationRate : explorationRate <= 1) :
    AdaptiveEpisodeBatchSource mdp initialState episodes where
  initialPolicy := initialTable.exploratoryPolicy explorationRate hexplorationRate
  successorPolicy n history :=
    (successorTable defaultState countRadius n history).exploratoryPolicy
      explorationRate hexplorationRate
  batchKernel n :=
    (DeterministicMarkovPolicyTable.exploratoryIIDEpisodeBatchKernel
      initialState episodes explorationRate hexplorationRate).comap
        (successorTable defaultState countRadius n)
        (measurable_successorTable defaultState countRadius n)
  batchKernel_isMarkov n := by
    exact ProbabilityTheory.Kernel.IsMarkovKernel.comap _
      (measurable_successorTable defaultState countRadius n)
  batchKernel_eq_iidEpisodeBatchMeasure n history := by
    rw [ProbabilityTheory.Kernel.comap_apply]
    rfl

omit [Nonempty State] in
/-- The source's successor behavior is centered on the cumulative optimistic table. -/
theorem exploratorySource_successorPolicy
    {mdp : MDP State Action} {initialState : Measure State}
    [IsProbabilityMeasure initialState] {episodes : Nat}
    (initialTable : DeterministicMarkovPolicyTable mdp)
    (defaultState : State) (countRadius : TransitionCountRadius)
    (explorationRate : NNReal) (hexplorationRate : explorationRate <= 1)
    (n : Nat) (history : EpisodeBatchPrefix mdp episodes n) :
    (exploratorySource mdp initialState episodes initialTable defaultState
      countRadius explorationRate hexplorationRate).successorPolicy n history =
      (successorTable defaultState countRadius n history).exploratoryPolicy
        explorationRate hexplorationRate := by
  rfl

end AdaptiveCumulativeEmpiricalOptimisticSource

/--
One global event contract for cumulative empirical plans.  The missing
statistical producer must supply coordinate confidence for every cumulative
prefix plan outside `badEvent`.
-/
structure AdaptiveCumulativeCoordinateConfidenceContract
    {mdp : MDP State Action} {initialState : Measure State}
    [IsProbabilityMeasure initialState] {episodes : Nat}
    (source : AdaptiveEpisodeBatchSource mdp initialState episodes)
    (defaultState : State) (countRadius : TransitionCountRadius)
    (rounds : Nat) (delta : Real) where
  badEvent : Set (EpisodeBatchTrajectory mdp episodes)
  measurable_badEvent : MeasurableSet badEvent
  measure_badEvent_le : source.trajectoryMeasure badEvent <= ENNReal.ofReal delta
  coordinateConfidence_of_not_mem : forall trajectory, trajectory ∉ badEvent ->
    forall round : Fin rounds,
      (adaptiveCumulativeEmpiricalOptimisticPlanAt
        trajectory defaultState countRadius round).CoordinateConfidence

omit [Nonempty State] in
/--
Roundwise cumulative confidence and a selected-radius envelope imply global
optimism and the explicit finite recommendation-regret sum.
-/
theorem adaptiveCumulativeCoordinateConfidence_optimism_and_recommendedExpectedRegret
    {mdp : MDP State Action} {initialState : Measure State}
    [IsProbabilityMeasure initialState] {episodes rounds : Nat}
    (trajectory : EpisodeBatchTrajectory mdp episodes)
    (defaultState : State) (countRadius : TransitionCountRadius)
    (radiusEnvelope : Fin rounds -> Real)
    (confidence : forall round : Fin rounds,
      (adaptiveCumulativeEmpiricalOptimisticPlanAt
        trajectory defaultState countRadius round).CoordinateConfidence)
    (hradius : forall (round : Fin rounds) (remaining : Nat)
      (hremaining : remaining + 1 <= mdp.horizon) (state : State),
      (adaptiveCumulativeEmpiricalOptimisticPlanAt
        trajectory defaultState countRadius round).selectedRadiusRemaining
          remaining hremaining state <= radiusEnvelope round) :
    (forall round : Fin rounds, forall state,
      mdp.optimalValueRemaining mdp.horizon le_rfl state <=
        (adaptiveCumulativeEmpiricalOptimisticPlanAt
          trajectory defaultState countRadius round).upperValueRemaining
            mdp.horizon le_rfl state) /\
    adaptiveCumulativeEmpiricalOptimisticRecommendedExpectedRegret
        (initialState := initialState) trajectory defaultState countRadius rounds <=
      ∑ round : Fin rounds,
        (mdp.horizon : Real) * (2 * radiusEnvelope round) := by
  constructor
  · intro round state
    exact
      ((confidence round).optimism_and_expectedRegret_le_two_occupancySelectedRadiusRemaining
        initialState).1 state
  · unfold adaptiveCumulativeEmpiricalOptimisticRecommendedExpectedRegret
    apply Finset.sum_le_sum
    intro round _hround
    let plan := adaptiveCumulativeEmpiricalOptimisticPlanAt
      trajectory defaultState countRadius round
    calc
      plan.optimisticPolicy.expectedRegret initialState <=
          plan.optimisticPolicy.occupancySumRemaining
            (fun remaining hremaining state =>
              2 * plan.selectedRadiusRemaining remaining hremaining state)
            mdp.horizon le_rfl initialState :=
        ((confidence round).optimism_and_expectedRegret_le_two_occupancySelectedRadiusRemaining
          initialState).2
      _ <= plan.optimisticPolicy.occupancySumRemaining
            (fun _remaining _hremaining _state => 2 * radiusEnvelope round)
            mdp.horizon le_rfl initialState := by
        exact plan.optimisticPolicy.occupancySumRemaining_mono
          (fun remaining hremaining state =>
            mul_le_mul_of_nonneg_left
              (hradius round remaining hremaining state) (by norm_num))
          mdp.horizon le_rfl initialState
      _ = (mdp.horizon : Real) * (2 * radiusEnvelope round) :=
        MarkovPolicy.occupancySumRemaining_const
          plan.optimisticPolicy (2 * radiusEnvelope round)
            mdp.horizon le_rfl initialState

omit [Nonempty State] in
/--
Route endpoint: one measurable global cumulative-confidence event yields
global optimism and an explicit shrinking-radius recommendation-regret bound.
-/
theorem AdaptiveCumulativeCoordinateConfidenceContract.trajectoryMeasure_optimism_and_explicitRecommendedExpectedRegret
    {mdp : MDP State Action} {initialState : Measure State}
    [IsProbabilityMeasure initialState] {episodes rounds : Nat}
    (source : AdaptiveEpisodeBatchSource mdp initialState episodes)
    (defaultState : State) (countRadius : TransitionCountRadius)
    (delta : Real)
    (contract : AdaptiveCumulativeCoordinateConfidenceContract
      source defaultState countRadius rounds delta)
    (radiusEnvelope : Fin rounds -> Real)
    (hradius : forall trajectory, trajectory ∉ contract.badEvent ->
      forall (round : Fin rounds) (remaining : Nat)
        (hremaining : remaining + 1 <= mdp.horizon) (state : State),
        (adaptiveCumulativeEmpiricalOptimisticPlanAt
          trajectory defaultState countRadius round).selectedRadiusRemaining
            remaining hremaining state <= radiusEnvelope round) :
    MeasurableSet contract.badEvent /\
      source.trajectoryMeasure contract.badEvent <= ENNReal.ofReal delta /\
      forall trajectory, trajectory ∉ contract.badEvent ->
        (forall round : Fin rounds, forall state,
          mdp.optimalValueRemaining mdp.horizon le_rfl state <=
            (adaptiveCumulativeEmpiricalOptimisticPlanAt
              trajectory defaultState countRadius round).upperValueRemaining
                mdp.horizon le_rfl state) /\
        adaptiveCumulativeEmpiricalOptimisticRecommendedExpectedRegret
            (initialState := initialState) trajectory defaultState countRadius rounds <=
          ∑ round : Fin rounds,
            (mdp.horizon : Real) * (2 * radiusEnvelope round) := by
  exact ⟨contract.measurable_badEvent, contract.measure_badEvent_le,
    fun trajectory htrajectory =>
      adaptiveCumulativeCoordinateConfidence_optimism_and_recommendedExpectedRegret
        trajectory defaultState countRadius radiusEnvelope
          (contract.coordinateConfidence_of_not_mem trajectory htrajectory)
          (hradius trajectory htrajectory)⟩

end BanditRLProof.FiniteHorizonRL
