import BanditRLProof.RL.FiniteHorizonExploratoryReachabilityCalibration

/-!
# Exploratory path-support state reachability

This module derives a policy-independent state-probability lower envelope from
explicit initial singleton floors and one chosen predecessor transition for
each successor-stage state. Uniform exploration supplies the chosen action's
probability. The resulting envelope applies to every exploratory policy table
and therefore to every behavior policy in the adaptive empirical optimistic
source.
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

namespace MDP

omit [DecidableEq State] [DecidableEq Action]
    [MeasurableSingletonClass State] [MeasurableSingletonClass Action]
    [Nonempty Action] in
@[simp]
theorem trajectoryStateAt_zero (mdp : MDP State Action)
    (trajectory : State × StepTrace Action State mdp.horizon)
    (hhorizon : 0 < mdp.horizon) :
    mdp.trajectoryStateAt trajectory ⟨0, hhorizon⟩ = trajectory.1 := by
  simp [trajectoryStateAt]

omit [DecidableEq State] [DecidableEq Action]
    [MeasurableSingletonClass State] [MeasurableSingletonClass Action]
    [Nonempty Action] in
@[simp]
theorem episodeStepOfTrajectory_nextState_eq_trajectoryStateAt_succ
    (mdp : MDP State Action)
    (trajectory : State × StepTrace Action State mdp.horizon)
    (stage : Nat) (hstage : stage + 1 < mdp.horizon) :
    (mdp.episodeStepOfTrajectory trajectory ⟨stage, by omega⟩).nextState =
      mdp.trajectoryStateAt trajectory ⟨stage + 1, hstage⟩ := by
  simp [episodeStepOfTrajectory, trajectoryStateAt]

end MDP

namespace MarkovPolicy

omit [DecidableEq State] [DecidableEq Action] [MeasurableSingletonClass Action]
    [Nonempty Action] in
/-- The generated state mass at stage zero is the initial singleton mass. -/
theorem stageStateProbability_zero
    {mdp : MDP State Action} (policy : MarkovPolicy mdp)
    (initialState : Measure State) [IsProbabilityMeasure initialState]
    (hhorizon : 0 < mdp.horizon) (state : State) :
    policy.stageStateProbability initialState ⟨0, hhorizon⟩ state =
      initialState.real {state} := by
  rw [stageStateProbability]
  have hevent :
      {trajectory : State × StepTrace Action State mdp.horizon |
        mdp.trajectoryStateAt trajectory ⟨0, hhorizon⟩ = state} =
        Prod.fst ⁻¹' ({state} : Set State) := by
    ext trajectory
    simp
  rw [hevent]
  have hfst :
      (policy.trajectoryMeasure initialState).map Prod.fst = initialState := by
    unfold trajectoryMeasure
    rw [← Measure.fst, Measure.fst_compProd]
  unfold Measure.real
  rw [← Measure.map_apply measurable_fst (measurableSet_singleton state)]
  rw [hfst]

omit [Nonempty Action] in
/-- A selected transition event is contained in its successor state event. -/
theorem stageTransitionJointProbability_le_stageStateProbability_succ
    {mdp : MDP State Action} (policy : MarkovPolicy mdp)
    (initialState : Measure State) [IsProbabilityMeasure initialState]
    (stage : Nat) (hstage : stage + 1 < mdp.horizon)
    (state : State) (action : Action) (nextState : State) :
    policy.stageTransitionJointProbability initialState ⟨stage, by omega⟩
        state action nextState <=
      policy.stageStateProbability initialState ⟨stage + 1, hstage⟩
        nextState := by
  rw [policy.stageTransitionJointProbability_eq_measureReal]
  rw [stageStateProbability]
  exact measureReal_mono fun trajectory htrajectory => by
    have hnext := htrajectory.2.2
    simpa using hnext

end MarkovPolicy

/--
One explicit predecessor path for each successor-stage state, together with
nonnegative singleton-mass floors along those paths.
-/
structure ExploratoryPathSupport
    (mdp : MDP State Action) (initialState : Measure State) where
  initialFloor : State -> Real
  predecessorState : Fin mdp.horizon -> State -> State
  predecessorAction : Fin mdp.horizon -> State -> Action
  transitionFloor : Fin mdp.horizon -> State -> Real
  initialFloor_nonneg : forall state, 0 <= initialFloor state
  initialFloor_le : forall state, initialFloor state <= initialState.real {state}
  transitionFloor_nonneg : forall stage, 0 < stage.val -> forall state,
    0 <= transitionFloor stage state
  transitionFloor_le : forall stage, 0 < stage.val -> forall state,
    transitionFloor stage state <=
      (mdp.transition
        (predecessorState stage state, predecessorAction stage state)
          {state}).toReal

/-- Recursive state floor along the selected predecessor paths. -/
noncomputable def exploratoryPathStateLowerNat
    {mdp : MDP State Action} {initialState : Measure State}
    (support : ExploratoryPathSupport mdp initialState)
    (explorationRate : NNReal) :
    (stage : Nat) -> stage < mdp.horizon -> State -> Real
  | 0, _hstage, state => support.initialFloor state
  | stage + 1, hstage, state =>
      exploratoryPathStateLowerNat support explorationRate stage (by omega)
          (support.predecessorState ⟨stage + 1, hstage⟩ state) *
        exploratoryActionProbabilityFloor Action explorationRate *
          support.transitionFloor ⟨stage + 1, hstage⟩ state

/-- The selected-path lower envelope indexed by valid chronological stages. -/
noncomputable def exploratoryPathStateLower
    {mdp : MDP State Action} {initialState : Measure State}
    (support : ExploratoryPathSupport mdp initialState)
    (explorationRate : NNReal) (stage : Fin mdp.horizon) (state : State) : Real :=
  exploratoryPathStateLowerNat support explorationRate stage.val stage.isLt state

omit [DecidableEq State] [DecidableEq Action]
    [MeasurableSingletonClass State] [MeasurableSingletonClass Action]
    [Nonempty Action] in
/-- Every recursively constructed path-support floor is nonnegative. -/
theorem exploratoryPathStateLowerNat_nonneg
    {mdp : MDP State Action} {initialState : Measure State}
    (support : ExploratoryPathSupport mdp initialState)
    (explorationRate : NNReal) :
    forall (stage : Nat) (hstage : stage < mdp.horizon) (state : State),
      0 <= exploratoryPathStateLowerNat support explorationRate stage hstage state := by
  intro stage
  induction stage with
  | zero =>
      intro hstage state
      simpa [exploratoryPathStateLowerNat] using support.initialFloor_nonneg state
  | succ stage ih =>
      intro hstage state
      rw [exploratoryPathStateLowerNat]
      exact mul_nonneg
        (mul_nonneg
          (ih (by omega)
            (support.predecessorState ⟨stage + 1, hstage⟩ state))
          (exploratoryActionProbabilityFloor_nonneg explorationRate))
        (support.transitionFloor_nonneg ⟨stage + 1, hstage⟩ (by simp) state)

omit [DecidableEq State] [DecidableEq Action]
    [MeasurableSingletonClass State] [MeasurableSingletonClass Action]
    [Nonempty Action] in
/-- The Fin-indexed selected-path envelope is nonnegative. -/
theorem exploratoryPathStateLower_nonneg
    {mdp : MDP State Action} {initialState : Measure State}
    (support : ExploratoryPathSupport mdp initialState)
    (explorationRate : NNReal) (stage : Fin mdp.horizon) (state : State) :
    0 <= exploratoryPathStateLower support explorationRate stage state := by
  exact exploratoryPathStateLowerNat_nonneg support explorationRate
    stage.val stage.isLt state

namespace DeterministicMarkovPolicyTable

/--
Every exploratory table policy dominates the same explicit path-support state
envelope, independently of the table's deterministic center.
-/
theorem exploratoryPathStateLower_le_stageStateProbability
    {mdp : MDP State Action} (table : DeterministicMarkovPolicyTable mdp)
    (initialState : Measure State) [IsProbabilityMeasure initialState]
    (support : ExploratoryPathSupport mdp initialState)
    (explorationRate : NNReal) (hexplorationRate : explorationRate <= 1)
    (stage : Fin mdp.horizon) (state : State) :
    exploratoryPathStateLower support explorationRate stage state <=
      (table.exploratoryPolicy explorationRate hexplorationRate).stageStateProbability
        initialState stage state := by
  let policy := table.exploratoryPolicy explorationRate hexplorationRate
  have go : forall (n : Nat) (hn : n < mdp.horizon) (target : State),
      exploratoryPathStateLowerNat support explorationRate n hn target <=
        policy.stageStateProbability initialState ⟨n, hn⟩ target := by
    intro n
    induction n with
    | zero =>
        intro hn target
        rw [policy.stageStateProbability_zero initialState hn target]
        exact support.initialFloor_le target
    | succ n ih =>
        intro hn target
        let successorStage : Fin mdp.horizon := ⟨n + 1, hn⟩
        let previousStage : Fin mdp.horizon := ⟨n, by omega⟩
        let previousState := support.predecessorState successorStage target
        let action := support.predecessorAction successorStage target
        have hsuccessorStage : 0 < successorStage.val := by
          simp [successorStage]
        have hprevious :
            exploratoryPathStateLowerNat support explorationRate n (by omega)
                previousState <=
              policy.stageStateProbability initialState previousStage
                previousState :=
          ih (by omega) previousState
        have hvisit :
            exploratoryPathStateLowerNat support explorationRate n (by omega)
                  previousState *
                exploratoryActionProbabilityFloor Action explorationRate <=
              policy.stageVisitProbability initialState previousStage
                previousState action := by
          rw [policy.stageVisitProbability_eq_stageStateProbability_mul_action]
          calc
            _ <= policy.stageStateProbability initialState previousStage
                  previousState *
                exploratoryActionProbabilityFloor Action explorationRate :=
              mul_le_mul_of_nonneg_right hprevious
                (exploratoryActionProbabilityFloor_nonneg explorationRate)
            _ <= policy.stageStateProbability initialState previousStage
                  previousState *
                (policy.actionKernel previousStage previousState {action}).toReal :=
              mul_le_mul_of_nonneg_left
                (table.exploratoryActionProbabilityFloor_le_actionKernel_real
                  explorationRate hexplorationRate previousStage previousState action)
                (policy.stageStateProbability_nonneg initialState previousStage
                  previousState)
        have hjoint :
            exploratoryPathStateLowerNat support explorationRate n (by omega)
                    previousState *
                  exploratoryActionProbabilityFloor Action explorationRate *
                support.transitionFloor successorStage target <=
              policy.stageTransitionJointProbability initialState previousStage
                previousState action target := by
          rw [policy.stageTransitionJointProbability_eq_stageVisitProbability_mul_transition]
          calc
            _ <= policy.stageVisitProbability initialState previousStage
                  previousState action *
                support.transitionFloor successorStage target :=
              mul_le_mul_of_nonneg_right hvisit
                (support.transitionFloor_nonneg successorStage hsuccessorStage target)
            _ <= policy.stageVisitProbability initialState previousStage
                  previousState action *
                (mdp.transition (previousState, action) {target}).toReal :=
              mul_le_mul_of_nonneg_left
                (support.transitionFloor_le successorStage hsuccessorStage target)
                (policy.stageVisitProbability_mem_Icc initialState previousStage
                  previousState action).1
        rw [exploratoryPathStateLowerNat]
        exact le_trans hjoint
          (MarkovPolicy.stageTransitionJointProbability_le_stageStateProbability_succ
            policy
            initialState n hn previousState action target)
  exact go stage.val stage.isLt state

end DeterministicMarkovPolicyTable

namespace AdaptiveEmpiricalOptimisticSource

/-- Every policy selected by the exploratory source shares the path-support floor. -/
theorem exploratorySource_sourceStateReachability_of_pathSupport
    {mdp : MDP State Action} {initialState : Measure State}
    [IsProbabilityMeasure initialState] {episodes : Nat}
    (initialTable : DeterministicMarkovPolicyTable mdp)
    (defaultState : State) (transitionBonus : Real)
    (explorationRate : NNReal) (hexplorationRate : explorationRate <= 1)
    (rounds : Nat) (support : ExploratoryPathSupport mdp initialState) :
    let behaviorSource := exploratorySource mdp initialState episodes
      initialTable defaultState transitionBonus explorationRate hexplorationRate
    SourceStateReachability behaviorSource rounds
      (exploratoryPathStateLower support explorationRate) := by
  dsimp only
  constructor
  · intro stage state
    exact initialTable.exploratoryPathStateLower_le_stageStateProbability
      initialState support explorationRate hexplorationRate stage state
  · intro n hn history stage state
    exact
      DeterministicMarkovPolicyTable.exploratoryPathStateLower_le_stageStateProbability
        (successorTable defaultState transitionBonus n history) initialState support
        explorationRate hexplorationRate stage state

/-- Explicit path support constructs the exact adaptive source calibration. -/
theorem exploratorySource_sourceCalibration_of_pathSupport
    {mdp : MDP State Action} {initialState : Measure State}
    [IsProbabilityMeasure initialState] {episodes : Nat}
    (initialTable : DeterministicMarkovPolicyTable mdp)
    (defaultState : State) (rewardBound transitionBonus delta : Real)
    (explorationRate : NNReal) (hexplorationRate : explorationRate <= 1)
    (rounds : Nat) (support : ExploratoryPathSupport mdp initialState)
    (hmargin : ExploratoryStateCountMargin mdp episodes
      (multiBatchLocalDelta rounds delta) explorationRate
        (exploratoryPathStateLower support explorationRate))
    (hcover :
      let behaviorSource := exploratorySource mdp initialState episodes
        initialTable defaultState transitionBonus explorationRate
          hexplorationRate
      SourceTransitionBonusCover behaviorSource rounds
        (multiBatchLocalDelta rounds delta) rewardBound transitionBonus) :
    let behaviorSource := exploratorySource mdp initialState episodes
      initialTable defaultState transitionBonus explorationRate
        hexplorationRate
    SourceCalibration behaviorSource rounds delta rewardBound transitionBonus := by
  apply exploratorySource_sourceCalibration_of_stateReachability
    (mdp := mdp) (initialState := initialState) (episodes := episodes)
    initialTable defaultState rewardBound transitionBonus delta explorationRate
      hexplorationRate rounds (exploratoryPathStateLower support explorationRate)
      hmargin
  · exact exploratorySource_sourceStateReachability_of_pathSupport
      initialTable defaultState transitionBonus explorationRate
        hexplorationRate rounds support
  · exact hcover

/--
Route endpoint: explicit initial and transition path support replaces the
abstract source state-reachability premise in the adaptive global theorem.
-/
theorem exploratorySource_trajectoryMeasure_allCoordinateConfidence_optimism_and_recommendedExpectedRegret_of_pathSupport
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
    (support : ExploratoryPathSupport mdp initialState)
    (hmargin : ExploratoryStateCountMargin mdp episodes
      (multiBatchLocalDelta rounds delta) explorationRate
        (exploratoryPathStateLower support explorationRate))
    (hcover :
      let behaviorSource := exploratorySource mdp initialState episodes
        initialTable defaultState transitionBonus explorationRate
          hexplorationRate
      SourceTransitionBonusCover behaviorSource rounds
        (multiBatchLocalDelta rounds delta) rewardBound transitionBonus) :
    let behaviorSource := exploratorySource mdp initialState episodes
      initialTable defaultState transitionBonus explorationRate
        hexplorationRate
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
  apply exploratorySource_trajectoryMeasure_allCoordinateConfidence_optimism_and_recommendedExpectedRegret_of_stateReachability
    (mdp := mdp) (initialState := initialState) (episodes := episodes)
    initialTable defaultState rewardBound transitionBonus explorationRate
      hexplorationRate hrewardBound htransitionBonus_nonneg rounds hrounds
      hepisodes delta hdelta hdelta_le_one
      (exploratoryPathStateLower support explorationRate) hmargin
  · exact exploratorySource_sourceStateReachability_of_pathSupport
      initialTable defaultState transitionBonus explorationRate
        hexplorationRate rounds support
  · exact hcover

end AdaptiveEmpiricalOptimisticSource

end BanditRLProof.FiniteHorizonRL
