import BanditRLProof.RL.FiniteHorizonAdaptiveEmpiricalOptimisticSource
import Mathlib.Probability.Distributions.Uniform

/-!
# Adaptive empirical optimistic all-coordinate confidence

This module calibrates a latest-batch empirical-transition source whose behavior
policy uniformly explores around the latest optimistic deterministic table.
For every policy that generates a batch, a local contract records genuine
expected-visit margins and a finite-state coordinate-radius cover for the fixed
transition bonus.  Outside the existing adaptive simultaneous-count event,
those contracts produce coordinate confidence for every known-reward empirical
plan.

The compiled one-episode expected-regret inequalities are summed over the
optimistic policies recommended by the generated batches.  Behavior-policy
exploration and recommendation regret are deliberately distinct.  This remains
a latest-batch, known-reward result with assumed state-action reachability and
bonus calibration; it is not behavior-policy regret, realized online regret,
or complete UCB-VI.
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

namespace EpisodeBatch

omit [MeasurableSingletonClass State] [MeasurableSingletonClass Action]
    [Nonempty State] [Nonempty Action] in
/-- Compressing a batch preserves every visit count. -/
theorem transitionCountSummary_visitCount
    {mdp : MDP State Action} {episodes : Nat}
    (batch : EpisodeBatch mdp episodes) (stage : Fin mdp.horizon)
    (state : State) (action : Action) :
    batch.transitionCountSummary.visitCount stage state action =
      batch.visitCount stage state action := by
  simpa [transitionCountSummary, TransitionCountSummary.visitCount] using
    batch.sum_transitionCount_eq_visitCount stage state action

omit [MeasurableSingletonClass State] [MeasurableSingletonClass Action]
    [Nonempty State] [Nonempty Action] in
/-- The summary-normalized PMF is exactly the raw batch empirical PMF. -/
theorem transitionCountSummary_empiricalTransitionPMF
    {mdp : MDP State Action} {episodes : Nat}
    (batch : EpisodeBatch mdp episodes) (defaultState : State)
    (stage : Fin mdp.horizon) (state : State) (action : Action) :
    batch.transitionCountSummary.empiricalTransitionPMF
        defaultState stage state action =
      batch.empiricalTransitionPMF defaultState stage state action := by
  have hvisit :
      batch.transitionCountSummary.visitCount stage state action =
        batch.visitCount stage state action :=
    batch.transitionCountSummary_visitCount stage state action
  by_cases hzero :
      batch.transitionCountSummary.visitCount stage state action = 0
  · have hzero' : batch.visitCount stage state action = 0 := by
      rwa [hvisit] at hzero
    simp [TransitionCountSummary.empiricalTransitionPMF,
      EpisodeBatch.empiricalTransitionPMF, hzero, hzero']
  · have hzero' : batch.visitCount stage state action ≠ 0 := by
      simpa [hvisit] using hzero
    rw [TransitionCountSummary.empiricalTransitionPMF,
      EpisodeBatch.empiricalTransitionPMF]
    simp only [dif_neg hzero, dif_neg hzero']
    congr 1
    funext nextState
    simp [EpisodeBatch.transitionCountSummary, hvisit]

omit [Nonempty State] [Nonempty Action] in
/-- The summary kernel singleton mass is the named raw empirical mass. -/
theorem transitionCountSummary_empiricalTransitionKernel_real_singleton
    {mdp : MDP State Action} {episodes : Nat}
    (batch : EpisodeBatch mdp episodes) (defaultState : State)
    (stage : Fin mdp.horizon) (state : State) (action : Action)
    (nextState : State) :
    (batch.transitionCountSummary.empiricalTransitionKernel defaultState stage
        (state, action)).real {nextState} =
      batch.empiricalTransitionMass defaultState stage state action nextState := by
  change
    ((batch.transitionCountSummary.empiricalTransitionPMF
        defaultState stage state action).toMeasure).real {nextState} = _
  rw [batch.transitionCountSummary_empiricalTransitionPMF]
  simpa [EpisodeBatch.empiricalTransitionKernel_apply] using
    batch.empiricalTransitionKernel_real_singleton
      defaultState stage state action nextState

end EpisodeBatch

namespace TransitionCountSummary

omit [DecidableEq Action] [Nonempty State] in
/--
The known-reward empirical plan has the same explicit linear value envelope as
the raw empirical model when the fixed transition bonus is nonnegative.
-/
theorem optimisticPlan_upperValueRemaining_abs_le
    (mdp : MDP State Action) (summary : TransitionCountSummary mdp)
    (defaultState : State) (rewardBound transitionBonus : Real)
    (hrewardBound : forall state action,
      |mdp.reward state action| <= rewardBound)
    (htransitionBonus_nonneg : 0 <= transitionBonus) :
    forall (remaining : Nat) (hremaining : remaining <= mdp.horizon)
      (state : State),
      |(summary.optimisticPlan mdp defaultState transitionBonus).upperValueRemaining
          remaining hremaining state| <=
        empiricalFiniteBatchValueEnvelope rewardBound transitionBonus remaining := by
  let plan := summary.optimisticPlan mdp defaultState transitionBonus
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
              rewardBound transitionBonus remaining := by
        intro nextState
        exact ih (by omega) nextState
      have htransition :
          |plan.transitionValue stage tail state action| <=
            empiricalFiniteBatchValueEnvelope
              rewardBound transitionBonus remaining := by
        rw [← Real.norm_eq_abs]
        have hnorm := norm_integral_le_of_norm_le_const
          (μ := plan.estimatedTransition stage (state, action))
          (C := empiricalFiniteBatchValueEnvelope
            rewardBound transitionBonus remaining)
          (Filter.Eventually.of_forall fun nextState => by
            rw [Real.norm_eq_abs]
            exact htail nextState)
        simpa [MDP.EstimatedModelPlan.transitionValue] using hnorm
      rw [MDP.EstimatedModelPlan.upperValueRemaining]
      change
        |mdp.reward state action +
              plan.transitionValue stage tail state action +
            0 + transitionBonus| <=
          empiricalFiniteBatchValueEnvelope
            rewardBound transitionBonus (remaining + 1)
      calc
        |mdp.reward state action +
              plan.transitionValue stage tail state action +
            0 + transitionBonus| =
            |(mdp.reward state action +
              plan.transitionValue stage tail state action) +
                transitionBonus| := by ring_nf
        _ <= |mdp.reward state action +
              plan.transitionValue stage tail state action| +
                |transitionBonus| := abs_add_le _ _
        _ <= (|mdp.reward state action| +
              |plan.transitionValue stage tail state action|) +
                |transitionBonus| := by
            have hsum := abs_add_le (mdp.reward state action)
              (plan.transitionValue stage tail state action)
            linarith
        _ <= rewardBound +
              empiricalFiniteBatchValueEnvelope
                rewardBound transitionBonus remaining +
              transitionBonus := by
            rw [abs_of_nonneg htransitionBonus_nonneg]
            linarith [hrewardBound state action, htransition]
        _ = empiricalFiniteBatchValueEnvelope
              rewardBound transitionBonus (remaining + 1) := by
            unfold empiricalFiniteBatchValueEnvelope
            rw [show ((remaining + 1 : Nat) : Real) =
              (remaining : Real) + 1 by norm_num]
            ring

end TransitionCountSummary

namespace MarkovPolicy

/--
Policy-local statistical calibration needed to make the fixed transition
bonus cover all finite-state empirical transition-coordinate errors.
-/
structure EmpiricalOptimisticCalibration
    {mdp : MDP State Action} (policy : MarkovPolicy mdp)
    (initialState : Measure State) [IsProbabilityMeasure initialState]
    (episodes : Nat) (delta rewardBound transitionBonus : Real) : Prop where
  margin : forall coordinate : VisitCoordinate mdp,
    simultaneousCountConfidenceRadius mdp episodes delta <
      coordinate.expectedCount policy initialState episodes
  cover : forall (remaining : Nat)
      (hremaining : remaining + 1 <= mdp.horizon)
      (state : State) (action : Action),
    (∑ nextState,
        policy.expectedCountTransitionCoordinateRadius
            initialState episodes delta
            (mdp.decisionStageRemaining remaining hremaining)
            state action nextState *
          empiricalFiniteBatchValueEnvelope
            rewardBound transitionBonus remaining) <=
      transitionBonus

/--
One good generated batch and one calibration contract produce coordinate
confidence for the exact known-reward empirical plan used by the source.
-/
noncomputable def empiricalOptimisticPlanCoordinateConfidence_of_not_mem
    {mdp : MDP State Action} (policy : MarkovPolicy mdp)
    (initialState : Measure State) [IsProbabilityMeasure initialState]
    {episodes : Nat} {delta : Real} (batch : EpisodeBatch mdp episodes)
    (hbatch : batch ∉
      policy.simultaneousCountBadEvent initialState episodes delta)
    (defaultState : State) (rewardBound transitionBonus : Real)
    (hrewardBound : forall state action,
      |mdp.reward state action| <= rewardBound)
    (htransitionBonus_nonneg : 0 <= transitionBonus)
    (calibration : policy.EmpiricalOptimisticCalibration initialState episodes
      delta rewardBound transitionBonus) :
    (batch.transitionCountSummary.optimisticPlan
      mdp defaultState transitionBonus).CoordinateConfidence where
  transitionCoordinateRadius :=
    policy.expectedCountTransitionCoordinateRadius
      initialState episodes delta
  valueEnvelope :=
    empiricalFiniteBatchValueEnvelope rewardBound transitionBonus
  rewardError_le_radius := by
    intro stage state action
    simp [TransitionCountSummary.optimisticPlan]
  transitionCoordinateError_le_radius := by
    intro remaining hremaining state action nextState
    change
      |(batch.transitionCountSummary.empiricalTransitionKernel defaultState
            (mdp.decisionStageRemaining remaining hremaining)
            (state, action)).real {nextState} -
          (mdp.transition (state, action)).real {nextState}| <=
        policy.expectedCountTransitionCoordinateRadius
          initialState episodes delta
          (mdp.decisionStageRemaining remaining hremaining)
          state action nextState
    rw [EpisodeBatch.transitionCountSummary_empiricalTransitionKernel_real_singleton]
    let coordinate : VisitCoordinate mdp :=
      { stage := mdp.decisionStageRemaining remaining hremaining
        state := state
        action := action }
    simpa [coordinate] using
      policy.empiricalTransitionMass_abs_sub_transition_le_expectedCountRadius_of_not_mem
        initialState batch hbatch defaultState coordinate
          (calibration.margin coordinate) nextState
  upperValue_abs_le_envelope := by
    intro remaining hremaining state
    exact batch.transitionCountSummary.optimisticPlan_upperValueRemaining_abs_le
      mdp defaultState rewardBound transitionBonus hrewardBound
        htransitionBonus_nonneg remaining (by omega) state
  transitionRadius_cover := by
    intro remaining hremaining state action
    simpa [TransitionCountSummary.optimisticPlan] using
      calibration.cover remaining hremaining state action

end MarkovPolicy

namespace DeterministicMarkovPolicyTable

/--
Action law that explores uniformly with the supplied probability and otherwise
uses the deterministic optimistic table action.
-/
noncomputable def exploratoryActionPMF
    {mdp : MDP State Action} (table : DeterministicMarkovPolicyTable mdp)
    (explorationRate : NNReal) (hexplorationRate : explorationRate <= 1)
    (stage : Fin mdp.horizon) (state : State) : PMF Action :=
  (PMF.bernoulli explorationRate hexplorationRate).bind fun explore =>
    if explore then PMF.uniformOfFintype Action else PMF.pure (table stage state)

omit [DecidableEq State] [DecidableEq Action]
    [MeasurableSingletonClass State] [MeasurableSingletonClass Action]
    [Nonempty State] in
/-- Every action receives at least its uniform-exploration mass. -/
theorem explorationRate_mul_inv_card_le_exploratoryActionPMF
    {mdp : MDP State Action} (table : DeterministicMarkovPolicyTable mdp)
    (explorationRate : NNReal) (hexplorationRate : explorationRate <= 1)
    (stage : Fin mdp.horizon) (state : State) (action : Action) :
    (explorationRate : ENNReal) * (Fintype.card Action : ENNReal)⁻¹ <=
      table.exploratoryActionPMF explorationRate hexplorationRate
        stage state action := by
  rw [exploratoryActionPMF, PMF.bind_apply]
  rw [tsum_fintype, Fintype.sum_bool]
  simp only [PMF.bernoulli_apply, Bool.cond_false, Bool.cond_true,
    if_true, PMF.uniformOfFintype_apply]
  exact le_add_of_nonneg_right (by positivity)

/-- Markov behavior policy obtained by uniformly exploring around one table. -/
noncomputable def exploratoryPolicy
    {mdp : MDP State Action} (table : DeterministicMarkovPolicyTable mdp)
    (explorationRate : NNReal) (hexplorationRate : explorationRate <= 1) :
    MarkovPolicy mdp where
  actionKernel stage := ProbabilityTheory.Kernel.ofFunOfCountable fun state =>
    (table.exploratoryActionPMF explorationRate hexplorationRate
      stage state).toMeasure
  actionKernel_isMarkov _stage := by
    refine ⟨fun state => ?_⟩
    change IsProbabilityMeasure
      ((table.exploratoryActionPMF explorationRate hexplorationRate
        _stage state).toMeasure)
    infer_instance

/-- Iid generated episode-batch kernel indexed by exploratory table policies. -/
noncomputable def exploratoryIIDEpisodeBatchKernel
    {mdp : MDP State Action} (initialState : Measure State)
    [IsProbabilityMeasure initialState] (episodes : Nat)
    (explorationRate : NNReal) (hexplorationRate : explorationRate <= 1) :
    ProbabilityTheory.Kernel (DeterministicMarkovPolicyTable mdp)
      (EpisodeBatch mdp episodes) :=
  ProbabilityTheory.Kernel.ofFunOfCountable fun table =>
    (table.exploratoryPolicy explorationRate hexplorationRate).iidEpisodeBatchMeasure
      initialState episodes

omit [DecidableEq State] [DecidableEq Action] [Nonempty State] in
@[simp]
theorem exploratoryIIDEpisodeBatchKernel_apply
    {mdp : MDP State Action} (initialState : Measure State)
    [IsProbabilityMeasure initialState] (episodes : Nat)
    (explorationRate : NNReal) (hexplorationRate : explorationRate <= 1)
    (table : DeterministicMarkovPolicyTable mdp) :
    exploratoryIIDEpisodeBatchKernel initialState episodes explorationRate
        hexplorationRate table =
      (table.exploratoryPolicy explorationRate hexplorationRate).iidEpisodeBatchMeasure
        initialState episodes :=
  rfl

instance instExploratoryIIDEpisodeBatchKernelIsMarkov
    {mdp : MDP State Action} (initialState : Measure State)
    [IsProbabilityMeasure initialState] (episodes : Nat)
    (explorationRate : NNReal) (hexplorationRate : explorationRate <= 1) :
    ProbabilityTheory.IsMarkovKernel
      (exploratoryIIDEpisodeBatchKernel (mdp := mdp) initialState episodes
        explorationRate hexplorationRate) where
  isProbabilityMeasure table := by
    rw [exploratoryIIDEpisodeBatchKernel_apply]
    infer_instance

end DeterministicMarkovPolicyTable

/-- The known-reward empirical plan selected from one batch coordinate. -/
noncomputable def adaptiveEmpiricalOptimisticPlanAt
    {mdp : MDP State Action} {episodes : Nat}
    (trajectory : EpisodeBatchTrajectory mdp episodes)
    (defaultState : State) (transitionBonus : Real) (round : Nat) :
    mdp.EstimatedModelPlan :=
  (trajectory round).transitionCountSummary.optimisticPlan
    mdp defaultState transitionBonus

/-- Sum of expected regrets of the optimistic policies recommended by each batch. -/
noncomputable def adaptiveEmpiricalOptimisticRecommendedExpectedRegret
    {mdp : MDP State Action} {initialState : Measure State}
    [IsProbabilityMeasure initialState] {episodes : Nat}
    (trajectory : EpisodeBatchTrajectory mdp episodes)
    (defaultState : State) (transitionBonus : Real) (rounds : Nat) : Real :=
  ∑ round : Fin rounds,
    (adaptiveEmpiricalOptimisticPlanAt
      (mdp := mdp) (episodes := episodes)
      trajectory defaultState transitionBonus round).optimisticPolicy.expectedRegret
        initialState

/-- Sum of the confidence-produced occupancy radius bounds after each batch. -/
noncomputable def adaptiveEmpiricalOptimisticOccupancyRadiusSum
    {mdp : MDP State Action} {initialState : Measure State}
    [IsProbabilityMeasure initialState] {episodes : Nat}
    (trajectory : EpisodeBatchTrajectory mdp episodes)
    (defaultState : State) (transitionBonus : Real) (rounds : Nat) : Real :=
  ∑ round : Fin rounds,
    let plan := adaptiveEmpiricalOptimisticPlanAt
      (mdp := mdp) (episodes := episodes)
      trajectory defaultState transitionBonus round
    plan.optimisticPolicy.occupancySumRemaining
      (fun remaining hremaining state =>
        2 * plan.selectedRadiusRemaining remaining hremaining state)
      mdp.horizon le_rfl initialState

namespace AdaptiveEmpiricalOptimisticSource

/--
Concrete behavior source with uniform action exploration around every
latest-batch optimistic table.
-/
noncomputable def exploratorySource
    (mdp : MDP State Action) (initialState : Measure State)
    [IsProbabilityMeasure initialState] (episodes : Nat)
    (initialTable : DeterministicMarkovPolicyTable mdp)
    (defaultState : State) (transitionBonus : Real)
    (explorationRate : NNReal) (hexplorationRate : explorationRate <= 1) :
    AdaptiveEpisodeBatchSource mdp initialState episodes where
  initialPolicy :=
    initialTable.exploratoryPolicy explorationRate hexplorationRate
  successorPolicy n history :=
    (successorTable defaultState transitionBonus n history).exploratoryPolicy
      explorationRate hexplorationRate
  batchKernel n :=
    (DeterministicMarkovPolicyTable.exploratoryIIDEpisodeBatchKernel
      initialState episodes explorationRate hexplorationRate).comap
        (successorTable defaultState transitionBonus n)
        (measurable_successorTable defaultState transitionBonus n)
  batchKernel_isMarkov n := by
    exact ProbabilityTheory.Kernel.IsMarkovKernel.comap _
      (measurable_successorTable defaultState transitionBonus n)
  batchKernel_eq_iidEpisodeBatchMeasure n history := by
    rw [ProbabilityTheory.Kernel.comap_apply]
    rfl

omit [Nonempty State] in
/-- The exploratory successor behavior is centered on the latest optimistic table. -/
theorem exploratorySource_successorPolicy
    {mdp : MDP State Action} {initialState : Measure State}
    [IsProbabilityMeasure initialState] {episodes : Nat}
    (initialTable : DeterministicMarkovPolicyTable mdp)
    (defaultState : State) (transitionBonus : Real)
    (explorationRate : NNReal) (hexplorationRate : explorationRate <= 1)
    (n : Nat) (history : EpisodeBatchPrefix mdp episodes n) :
    (exploratorySource mdp initialState episodes initialTable defaultState
      transitionBonus explorationRate hexplorationRate).successorPolicy n history =
      (successorTable defaultState transitionBonus n history).exploratoryPolicy
        explorationRate hexplorationRate := by
  rfl

omit [Nonempty State] in
/-- Measurability of finite-table-selected exploratory count events. -/
theorem measurableSet_selectedExploratorySimultaneousCountBadEvent
    {mdp : MDP State Action} {initialState : Measure State}
    [IsProbabilityMeasure initialState] {episodes : Nat}
    {History : Type*} [MeasurableSpace History]
    (selector : History -> DeterministicMarkovPolicyTable mdp)
    (hselector : Measurable selector)
    (explorationRate : NNReal) (hexplorationRate : explorationRate <= 1)
    (delta : Real) :
    MeasurableSet
      {pair : History × EpisodeBatch mdp episodes |
        pair.2 ∈
          ((selector pair.1).exploratoryPolicy explorationRate
            hexplorationRate).simultaneousCountBadEvent
              initialState episodes delta} := by
  rw [show
      {pair : History × EpisodeBatch mdp episodes |
          pair.2 ∈
            ((selector pair.1).exploratoryPolicy explorationRate
              hexplorationRate).simultaneousCountBadEvent
                initialState episodes delta} =
        ⋃ table : DeterministicMarkovPolicyTable mdp,
          (selector ⁻¹' {table}) ×ˢ
            (MarkovPolicy.simultaneousCountBadEvent
              (table.exploratoryPolicy explorationRate hexplorationRate)
              initialState episodes delta) by
    ext pair
    simp]
  exact MeasurableSet.iUnion fun table =>
    (hselector (measurableSet_singleton table)).prod
      (MarkovPolicy.measurableSet_simultaneousCountBadEvent
        (table.exploratoryPolicy explorationRate hexplorationRate)
        initialState episodes delta)

omit [Nonempty State] in
/-- Every selected successor event of the exploratory source is measurable. -/
theorem exploratorySource_measurableSet_successorSimultaneousCountBadEvent
    {mdp : MDP State Action} {initialState : Measure State}
    [IsProbabilityMeasure initialState] {episodes : Nat}
    (initialTable : DeterministicMarkovPolicyTable mdp)
    (defaultState : State) (transitionBonus : Real)
    (explorationRate : NNReal) (hexplorationRate : explorationRate <= 1)
    (rounds : Nat) (delta : Real) (n : Nat) :
    MeasurableSet
      (AdaptiveEpisodeBatchSource.successorSimultaneousCountBadEvent
        (exploratorySource mdp initialState episodes initialTable defaultState
          transitionBonus explorationRate hexplorationRate)
        rounds delta n) := by
  change MeasurableSet
    {pair : EpisodeBatchPrefix mdp episodes n × EpisodeBatch mdp episodes |
      pair.2 ∈
        ((successorTable defaultState transitionBonus n pair.1).exploratoryPolicy
          explorationRate hexplorationRate).simultaneousCountBadEvent
            initialState episodes (multiBatchLocalDelta rounds delta)}
  exact measurableSet_selectedExploratorySimultaneousCountBadEvent
    (successorTable defaultState transitionBonus n)
    (measurable_successorTable defaultState transitionBonus n)
    explorationRate hexplorationRate (multiBatchLocalDelta rounds delta)

omit [Nonempty State] in
/-- The exploratory behavior source inherits the adaptive global count event. -/
theorem exploratorySource_trajectoryMeasure_adaptiveSimultaneousCountConfidence
    {mdp : MDP State Action} {initialState : Measure State}
    [IsProbabilityMeasure initialState] {episodes : Nat}
    (initialTable : DeterministicMarkovPolicyTable mdp)
    (defaultState : State) (transitionBonus : Real)
    (explorationRate : NNReal) (hexplorationRate : explorationRate <= 1)
    (rounds : Nat) (hrounds : 0 < rounds) (hepisodes : 0 < episodes)
    (delta : Real) (hdelta : 0 < delta) (hdelta_le_one : delta <= 1) :
    let behaviorSource := exploratorySource mdp initialState episodes
      initialTable defaultState transitionBonus explorationRate hexplorationRate
    MeasurableSet
        (behaviorSource.adaptiveSimultaneousCountBadEvent rounds delta) ∧
      behaviorSource.trajectoryMeasure
          (behaviorSource.adaptiveSimultaneousCountBadEvent rounds delta) <=
        ENNReal.ofReal delta ∧
      forall trajectory,
        trajectory ∉ behaviorSource.adaptiveSimultaneousCountBadEvent rounds delta ->
        forall round : Fin rounds, forall coordinate : CountCoordinate mdp,
          |coordinate.deviation (behaviorSource.policyAt trajectory round)
              initialState (trajectory round)| <
            simultaneousCountConfidenceRadius mdp episodes
              (multiBatchLocalDelta rounds delta) := by
  dsimp only
  exact
    AdaptiveEpisodeBatchSource.trajectoryMeasure_adaptiveSimultaneousCountConfidence
      (exploratorySource mdp initialState episodes initialTable defaultState
        transitionBonus explorationRate hexplorationRate)
      rounds hrounds hepisodes delta hdelta hdelta_le_one
      (fun n _hn =>
        exploratorySource_measurableSet_successorSimultaneousCountBadEvent
          initialTable defaultState transitionBonus explorationRate
            hexplorationRate rounds delta n)

omit [Nonempty State] in
/-- The plan from batch `n` is exactly the source policy used at `n + 1`. -/
theorem source_policyAt_succ_eq_adaptiveEmpiricalOptimisticPlanAt
    {mdp : MDP State Action} {initialState : Measure State}
    [IsProbabilityMeasure initialState] {episodes : Nat}
    (initialTable : DeterministicMarkovPolicyTable mdp)
    (defaultState : State) (transitionBonus : Real)
    (trajectory : EpisodeBatchTrajectory mdp episodes) (n : Nat) :
    let concreteSource :=
      source mdp initialState episodes initialTable defaultState transitionBonus
    concreteSource.policyAt trajectory (n + 1) =
      (adaptiveEmpiricalOptimisticPlanAt
        (mdp := mdp) (episodes := episodes)
        trajectory defaultState transitionBonus n).optimisticPolicy := by
  dsimp only
  change
    (source mdp initialState episodes initialTable defaultState transitionBonus).successorPolicy
        n (Preorder.frestrictLe n trajectory) = _
  simpa [adaptiveEmpiricalOptimisticPlanAt, latestBatch] using
    source_successorPolicy_eq_optimisticPolicy
      (initialState := initialState) initialTable defaultState transitionBonus n
        (Preorder.frestrictLe n trajectory)

omit [MeasurableSingletonClass State] [MeasurableSingletonClass Action]
    [Nonempty State] [Nonempty Action] in
/-- Outside the adaptive union, every batch avoids its selected local event. -/
theorem policyAt_batch_not_mem_simultaneousCountBadEvent
    {mdp : MDP State Action} {initialState : Measure State}
    [IsProbabilityMeasure initialState] {episodes rounds : Nat}
    (source : AdaptiveEpisodeBatchSource mdp initialState episodes)
    {delta : Real} (trajectory : EpisodeBatchTrajectory mdp episodes)
    (htrajectory : trajectory ∉
      source.adaptiveSimultaneousCountBadEvent rounds delta)
    (round : Fin rounds) :
    trajectory round ∉
      (source.policyAt trajectory round).simultaneousCountBadEvent
        initialState episodes (multiBatchLocalDelta rounds delta) := by
  have hround : trajectory ∉
      AdaptiveEpisodeBatchSource.roundBadEvent
        (source.initialSimultaneousCountBadEvent rounds delta)
        (source.successorSimultaneousCountBadEvent rounds delta)
        round := by
    intro hmem
    apply htrajectory
    exact Set.mem_iUnion_of_mem round hmem
  cases round with
  | mk value hvalue =>
      cases value with
      | zero =>
          simpa [AdaptiveEpisodeBatchSource.roundBadEvent,
            AdaptiveEpisodeBatchSource.initialBadEvent,
            AdaptiveEpisodeBatchSource.policyAt,
            AdaptiveEpisodeBatchSource.initialSimultaneousCountBadEvent] using hround
      | succ n =>
          simpa [AdaptiveEpisodeBatchSource.roundBadEvent,
            AdaptiveEpisodeBatchSource.successorBadEvent,
            AdaptiveEpisodeBatchSource.policyAt,
            AdaptiveEpisodeBatchSource.successorSimultaneousCountBadEvent] using hround

/-- Calibration contract selected by the data-generating policy at each round. -/
def SourceCalibration
    {mdp : MDP State Action} {initialState : Measure State}
    [IsProbabilityMeasure initialState] {episodes : Nat}
    (source : AdaptiveEpisodeBatchSource mdp initialState episodes)
    (rounds : Nat) (delta rewardBound transitionBonus : Real) : Prop :=
  source.initialPolicy.EmpiricalOptimisticCalibration initialState episodes
      (multiBatchLocalDelta rounds delta) rewardBound transitionBonus /\
    forall n, n + 1 < rounds ->
      forall history : EpisodeBatchPrefix mdp episodes n,
        (source.successorPolicy n history).EmpiricalOptimisticCalibration
          initialState episodes (multiBatchLocalDelta rounds delta)
            rewardBound transitionBonus

/-- Every observed batch plan has coordinate confidence outside the global event. -/
noncomputable def exploratorySource_coordinateConfidenceAt_of_not_mem
    {mdp : MDP State Action} {initialState : Measure State}
    [IsProbabilityMeasure initialState] {episodes rounds : Nat}
    (initialTable : DeterministicMarkovPolicyTable mdp)
    (defaultState : State) (rewardBound transitionBonus delta : Real)
    (explorationRate : NNReal) (hexplorationRate : explorationRate <= 1)
    (hrewardBound : forall state action,
      |mdp.reward state action| <= rewardBound)
    (htransitionBonus_nonneg : 0 <= transitionBonus)
    (calibration :
      let behaviorSource := exploratorySource mdp initialState episodes initialTable
        defaultState transitionBonus explorationRate hexplorationRate
      SourceCalibration behaviorSource rounds delta rewardBound transitionBonus)
    (trajectory : EpisodeBatchTrajectory mdp episodes)
    (htrajectory : trajectory ∉
      (exploratorySource mdp initialState episodes initialTable defaultState
        transitionBonus explorationRate hexplorationRate).adaptiveSimultaneousCountBadEvent
        rounds delta)
    (round : Fin rounds) :
    (adaptiveEmpiricalOptimisticPlanAt
      (mdp := mdp) (episodes := episodes)
      trajectory defaultState transitionBonus round).CoordinateConfidence := by
  let behaviorSource := exploratorySource mdp initialState episodes initialTable
    defaultState transitionBonus explorationRate hexplorationRate
  have hbatch := policyAt_batch_not_mem_simultaneousCountBadEvent
    behaviorSource trajectory htrajectory round
  cases round with
  | mk value hvalue =>
      cases value with
      | zero =>
          exact
            MarkovPolicy.empiricalOptimisticPlanCoordinateConfidence_of_not_mem
              behaviorSource.initialPolicy initialState (trajectory 0) hbatch
                defaultState rewardBound transitionBonus hrewardBound
                  htransitionBonus_nonneg calibration.1
      | succ n =>
          exact
            MarkovPolicy.empiricalOptimisticPlanCoordinateConfidence_of_not_mem
              (behaviorSource.successorPolicy n
                (Preorder.frestrictLe n trajectory))
                initialState (trajectory (n + 1)) hbatch defaultState rewardBound
                  transitionBonus hrewardBound htransitionBonus_nonneg
                    (calibration.2 n hvalue (Preorder.frestrictLe n trajectory))

omit [Nonempty State] in
/--
Outside the one adaptive event, every batch plan is optimistic and the finite
sum of recommended optimistic-policy expected regrets is radius-controlled.
-/
theorem exploratorySource_optimism_and_recommendedExpectedRegret_of_not_mem
    {mdp : MDP State Action} {initialState : Measure State}
    [IsProbabilityMeasure initialState] {episodes rounds : Nat}
    (initialTable : DeterministicMarkovPolicyTable mdp)
    (defaultState : State) (rewardBound transitionBonus delta : Real)
    (explorationRate : NNReal) (hexplorationRate : explorationRate <= 1)
    (hrewardBound : forall state action,
      |mdp.reward state action| <= rewardBound)
    (htransitionBonus_nonneg : 0 <= transitionBonus)
    (calibration :
      let behaviorSource := exploratorySource mdp initialState episodes initialTable
        defaultState transitionBonus explorationRate hexplorationRate
      SourceCalibration behaviorSource rounds delta rewardBound transitionBonus)
    (trajectory : EpisodeBatchTrajectory mdp episodes)
    (htrajectory : trajectory ∉
      (exploratorySource mdp initialState episodes initialTable defaultState
        transitionBonus explorationRate hexplorationRate).adaptiveSimultaneousCountBadEvent
        rounds delta) :
    (forall round : Fin rounds, forall state,
      mdp.optimalValueRemaining mdp.horizon le_rfl state <=
        (adaptiveEmpiricalOptimisticPlanAt
          (mdp := mdp) (episodes := episodes)
          trajectory defaultState transitionBonus round).upperValueRemaining
            mdp.horizon le_rfl state) /\
    adaptiveEmpiricalOptimisticRecommendedExpectedRegret
        (mdp := mdp) (initialState := initialState) (episodes := episodes)
        trajectory defaultState transitionBonus rounds <=
      adaptiveEmpiricalOptimisticOccupancyRadiusSum
        (mdp := mdp) (initialState := initialState) (episodes := episodes)
        trajectory defaultState transitionBonus rounds := by
  have hconfidence : forall round : Fin rounds,
      (adaptiveEmpiricalOptimisticPlanAt
        (mdp := mdp) (episodes := episodes)
        trajectory defaultState transitionBonus round).CoordinateConfidence :=
    fun round => exploratorySource_coordinateConfidenceAt_of_not_mem
      (mdp := mdp) (initialState := initialState) (episodes := episodes)
      (rounds := rounds)
      initialTable defaultState rewardBound transitionBonus delta
        explorationRate hexplorationRate hrewardBound htransitionBonus_nonneg calibration
          trajectory htrajectory round
  constructor
  · intro round state
    exact
      ((hconfidence round).optimism_and_expectedRegret_le_two_occupancySelectedRadiusRemaining
        initialState).1 state
  · unfold adaptiveEmpiricalOptimisticRecommendedExpectedRegret
      adaptiveEmpiricalOptimisticOccupancyRadiusSum
    apply Finset.sum_le_sum
    intro round _hround
    exact
      ((hconfidence round).optimism_and_expectedRegret_le_two_occupancySelectedRadiusRemaining
        initialState).2

omit [Nonempty State] in
/--
Route endpoint: calibrated all-coordinate confidence, global optimism, and a
finite recommended-policy expected-regret sum under one global delta event.
-/
theorem exploratorySource_trajectoryMeasure_allCoordinateConfidence_optimism_and_recommendedExpectedRegret
    {mdp : MDP State Action} {initialState : Measure State}
    [IsProbabilityMeasure initialState] {episodes : Nat}
    (initialTable : DeterministicMarkovPolicyTable mdp)
    (defaultState : State) (rewardBound transitionBonus : Real)
    (explorationRate : NNReal) (hexplorationRate : explorationRate <= 1)
    (hrewardBound : forall state action,
      |mdp.reward state action| <= rewardBound)
    (htransitionBonus_nonneg : 0 <= transitionBonus)
    (rounds : Nat) (hrounds : 0 < rounds)
    (hepisodes : 0 < episodes) (delta : Real) (hdelta : 0 < delta)
    (hdelta_le_one : delta <= 1)
    (calibration :
      let behaviorSource := exploratorySource mdp initialState episodes initialTable
        defaultState transitionBonus explorationRate hexplorationRate
      SourceCalibration behaviorSource rounds delta rewardBound transitionBonus) :
    let behaviorSource := exploratorySource mdp initialState episodes initialTable
      defaultState transitionBonus explorationRate hexplorationRate
    let bad := behaviorSource.adaptiveSimultaneousCountBadEvent rounds delta
    MeasurableSet bad /\
      behaviorSource.trajectoryMeasure bad <= ENNReal.ofReal delta /\
      forall trajectory, trajectory ∉ bad ->
        (forall round : Fin rounds, forall state,
          mdp.optimalValueRemaining mdp.horizon le_rfl state <=
            (adaptiveEmpiricalOptimisticPlanAt
              (mdp := mdp) (episodes := episodes)
              trajectory defaultState transitionBonus round).upperValueRemaining
                mdp.horizon le_rfl state) /\
        adaptiveEmpiricalOptimisticRecommendedExpectedRegret
            (mdp := mdp) (initialState := initialState) (episodes := episodes)
            trajectory defaultState transitionBonus rounds <=
          adaptiveEmpiricalOptimisticOccupancyRadiusSum
            (mdp := mdp) (initialState := initialState) (episodes := episodes)
            trajectory defaultState transitionBonus rounds := by
  dsimp only
  obtain ⟨hmeasurable, htail, _hcounts⟩ :=
    exploratorySource_trajectoryMeasure_adaptiveSimultaneousCountConfidence
      (mdp := mdp) (initialState := initialState) (episodes := episodes)
      initialTable defaultState transitionBonus explorationRate hexplorationRate
        rounds hrounds hepisodes delta hdelta hdelta_le_one
  exact ⟨hmeasurable, htail, fun trajectory htrajectory =>
    exploratorySource_optimism_and_recommendedExpectedRegret_of_not_mem
      (mdp := mdp) (initialState := initialState) (episodes := episodes)
      (rounds := rounds)
      initialTable defaultState rewardBound transitionBonus delta
        explorationRate hexplorationRate hrewardBound htransitionBonus_nonneg calibration
          trajectory htrajectory⟩

end AdaptiveEmpiricalOptimisticSource
end FiniteHorizonRL
end BanditRLProof
