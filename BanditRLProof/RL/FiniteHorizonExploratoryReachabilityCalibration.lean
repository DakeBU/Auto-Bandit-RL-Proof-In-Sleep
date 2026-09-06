import BanditRLProof.RL.FiniteHorizonAdaptiveEmpiricalOptimisticConfidence
import BanditRLProof.RL.FiniteHorizonStageVisitFactorization

/-!
# Exploratory state-reachability calibration

This module turns a generated stage-state probability lower envelope into the
state/action expected-count margins needed by the adaptive empirical optimistic
confidence route.  Uniform exploration supplies only the action factor; state
reachability and the transition-bonus cover remain explicit contracts.
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

/-- Real probability floor contributed by uniform exploration. -/
noncomputable def exploratoryActionProbabilityFloor
    (Action : Type v) [Fintype Action] (explorationRate : NNReal) : Real :=
  (explorationRate : Real) * (Fintype.card Action : Real)⁻¹

omit [MeasurableSpace State] [MeasurableSpace Action]
    [DecidableEq State] [DecidableEq Action]
    [MeasurableSingletonClass State] [MeasurableSingletonClass Action]
    [Nonempty State] [Nonempty Action] in
theorem exploratoryActionProbabilityFloor_nonneg
    (explorationRate : NNReal) :
    0 <= exploratoryActionProbabilityFloor Action explorationRate := by
  exact mul_nonneg (NNReal.coe_nonneg explorationRate)
    (inv_nonneg.mpr (Nat.cast_nonneg (Fintype.card Action)))

namespace MarkovPolicy

omit [DecidableEq State] [DecidableEq Action]
    [MeasurableSingletonClass State] [MeasurableSingletonClass Action]
    [Nonempty State] [Nonempty Action] in
/-- Every generated stage-state probability is nonnegative. -/
theorem stageStateProbability_nonneg
    {mdp : MDP State Action} (policy : MarkovPolicy mdp)
    (initialState : Measure State) [IsProbabilityMeasure initialState]
    (stage : Fin mdp.horizon) (state : State) :
    0 <= policy.stageStateProbability initialState stage state := by
  rw [stageStateProbability]
  exact measureReal_nonneg

/-- The transition-coordinate cover field retained by empirical calibration. -/
def TransitionBonusCover
    {mdp : MDP State Action} (policy : MarkovPolicy mdp)
    (initialState : Measure State) [IsProbabilityMeasure initialState]
    (episodes : Nat) (delta rewardBound transitionBonus : Real) : Prop :=
  forall (remaining : Nat)
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

end MarkovPolicy

namespace DeterministicMarkovPolicyTable

omit [DecidableEq State] [DecidableEq Action]
    [MeasurableSingletonClass State] [MeasurableSingletonClass Action]
    [Nonempty State] in
/-- The ENNReal exploratory PMF floor as a Real inequality. -/
theorem exploratoryActionProbabilityFloor_le_exploratoryActionPMF_toReal
    {mdp : MDP State Action} (table : DeterministicMarkovPolicyTable mdp)
    (explorationRate : NNReal) (hexplorationRate : explorationRate <= 1)
    (stage : Fin mdp.horizon) (state : State) (action : Action) :
    exploratoryActionProbabilityFloor Action explorationRate <=
      (table.exploratoryActionPMF explorationRate hexplorationRate
        stage state action).toReal := by
  have hfloor := table.explorationRate_mul_inv_card_le_exploratoryActionPMF
    explorationRate hexplorationRate stage state action
  have hreal := ENNReal.toReal_mono
    ((table.exploratoryActionPMF explorationRate hexplorationRate
      stage state).apply_ne_top action) hfloor
  simpa [exploratoryActionProbabilityFloor, ENNReal.toReal_mul] using hreal

omit [DecidableEq State] [DecidableEq Action] [Nonempty State] in
/-- The exploratory Markov kernel inherits the Real singleton floor. -/
theorem exploratoryActionProbabilityFloor_le_actionKernel_real
    {mdp : MDP State Action} (table : DeterministicMarkovPolicyTable mdp)
    (explorationRate : NNReal) (hexplorationRate : explorationRate <= 1)
    (stage : Fin mdp.horizon) (state : State) (action : Action) :
    exploratoryActionProbabilityFloor Action explorationRate <=
      ((table.exploratoryPolicy explorationRate hexplorationRate).actionKernel
        stage state {action}).toReal := by
  change exploratoryActionProbabilityFloor Action explorationRate <=
    (((table.exploratoryActionPMF explorationRate hexplorationRate
      stage state).toMeasure) {action}).toReal
  rw [(table.exploratoryActionPMF explorationRate hexplorationRate
    stage state).toMeasure_apply_singleton action
      (measurableSet_singleton action)]
  exact table.exploratoryActionProbabilityFloor_le_exploratoryActionPMF_toReal
    explorationRate hexplorationRate stage state action

omit [Nonempty State] in
/-- State reachability times the exploratory action floor lower-bounds visits. -/
theorem stateLower_mul_exploratoryActionProbabilityFloor_le_stageVisitProbability
    {mdp : MDP State Action} (table : DeterministicMarkovPolicyTable mdp)
    (initialState : Measure State) [IsProbabilityMeasure initialState]
    (explorationRate : NNReal) (hexplorationRate : explorationRate <= 1)
    (stateLower : Fin mdp.horizon -> State -> Real)
    (hstateLower : forall stage state,
      stateLower stage state <=
        (table.exploratoryPolicy explorationRate hexplorationRate).stageStateProbability
          initialState stage state)
    (stage : Fin mdp.horizon) (state : State) (action : Action) :
    stateLower stage state *
        exploratoryActionProbabilityFloor Action explorationRate <=
      (table.exploratoryPolicy explorationRate hexplorationRate).stageVisitProbability
        initialState stage state action := by
  let policy := table.exploratoryPolicy explorationRate hexplorationRate
  rw [policy.stageVisitProbability_eq_stageStateProbability_mul_action]
  calc
    stateLower stage state *
          exploratoryActionProbabilityFloor Action explorationRate <=
        policy.stageStateProbability initialState stage state *
          exploratoryActionProbabilityFloor Action explorationRate :=
      mul_le_mul_of_nonneg_right (hstateLower stage state)
        (exploratoryActionProbabilityFloor_nonneg explorationRate)
    _ <= policy.stageStateProbability initialState stage state *
          (policy.actionKernel stage state {action}).toReal :=
      mul_le_mul_of_nonneg_left
        (table.exploratoryActionProbabilityFloor_le_actionKernel_real
          explorationRate hexplorationRate stage state action)
        (policy.stageStateProbability_nonneg initialState stage state)

omit [Nonempty State] in
/-- The state/action floor also lower-bounds the genuine expected visit count. -/
theorem stateLower_expectedCount_le
    {mdp : MDP State Action} (table : DeterministicMarkovPolicyTable mdp)
    (initialState : Measure State) [IsProbabilityMeasure initialState]
    (episodes : Nat)
    (explorationRate : NNReal) (hexplorationRate : explorationRate <= 1)
    (stateLower : Fin mdp.horizon -> State -> Real)
    (hstateLower : forall stage state,
      stateLower stage state <=
        (table.exploratoryPolicy explorationRate hexplorationRate).stageStateProbability
          initialState stage state)
    (coordinate : VisitCoordinate mdp) :
    (episodes : Real) *
        (stateLower coordinate.stage coordinate.state *
          exploratoryActionProbabilityFloor Action explorationRate) <=
      coordinate.expectedCount
        (table.exploratoryPolicy explorationRate hexplorationRate)
        initialState episodes := by
  rw [VisitCoordinate.expectedCount]
  exact mul_le_mul_of_nonneg_left
    (table.stateLower_mul_exploratoryActionProbabilityFloor_le_stageVisitProbability
      initialState explorationRate hexplorationRate stateLower
      hstateLower coordinate.stage coordinate.state coordinate.action)
    (Nat.cast_nonneg episodes)

end DeterministicMarkovPolicyTable

/-- Strict count margin implied by a state lower envelope and exploration. -/
def ExploratoryStateCountMargin
    (mdp : MDP State Action) (episodes : Nat) (delta : Real)
    (explorationRate : NNReal)
    (stateLower : Fin mdp.horizon -> State -> Real) : Prop :=
  forall coordinate : VisitCoordinate mdp,
    simultaneousCountConfidenceRadius mdp episodes delta <
      (episodes : Real) *
        (stateLower coordinate.stage coordinate.state *
          exploratoryActionProbabilityFloor Action explorationRate)

namespace MarkovPolicy

omit [Nonempty State] in
/-- Reachability plus the unchanged cover constructs policy-local calibration. -/
def empiricalOptimisticCalibration_exploratoryPolicy_of_stateReachability
    {mdp : MDP State Action} (table : DeterministicMarkovPolicyTable mdp)
    (initialState : Measure State) [IsProbabilityMeasure initialState]
    (episodes : Nat) (delta rewardBound transitionBonus : Real)
    (explorationRate : NNReal) (hexplorationRate : explorationRate <= 1)
    (stateLower : Fin mdp.horizon -> State -> Real)
    (hstateLower : forall stage state,
      stateLower stage state <=
        (table.exploratoryPolicy explorationRate hexplorationRate).stageStateProbability
          initialState stage state)
    (hmargin : ExploratoryStateCountMargin mdp episodes delta
      explorationRate stateLower)
    (hcover : (table.exploratoryPolicy explorationRate hexplorationRate).TransitionBonusCover
      initialState episodes delta rewardBound
        transitionBonus) :
    (table.exploratoryPolicy explorationRate hexplorationRate).EmpiricalOptimisticCalibration
      initialState episodes delta rewardBound
        transitionBonus where
  margin coordinate := lt_of_lt_of_le (hmargin coordinate)
    (table.stateLower_expectedCount_le initialState episodes explorationRate
      hexplorationRate stateLower hstateLower coordinate)
  cover := hcover

end MarkovPolicy

namespace AdaptiveEmpiricalOptimisticSource

/-- State-only reachability envelope for every batch-generating source policy. -/
def SourceStateReachability
    {mdp : MDP State Action} {initialState : Measure State}
    [IsProbabilityMeasure initialState] {episodes : Nat}
    (source : AdaptiveEpisodeBatchSource mdp initialState episodes)
    (rounds : Nat) (stateLower : Fin mdp.horizon -> State -> Real) : Prop :=
  (forall stage state,
      stateLower stage state <=
        source.initialPolicy.stageStateProbability initialState stage state) /\
    forall n, n + 1 < rounds ->
      forall history : EpisodeBatchPrefix mdp episodes n, forall stage state,
        stateLower stage state <=
          (source.successorPolicy n history).stageStateProbability
            initialState stage state

/-- Transition-bonus cover for every batch-generating source policy. -/
def SourceTransitionBonusCover
    {mdp : MDP State Action} {initialState : Measure State}
    [IsProbabilityMeasure initialState] {episodes : Nat}
    (source : AdaptiveEpisodeBatchSource mdp initialState episodes)
    (rounds : Nat) (delta rewardBound transitionBonus : Real) : Prop :=
  source.initialPolicy.TransitionBonusCover initialState episodes delta
      rewardBound transitionBonus /\
    forall n, n + 1 < rounds ->
      forall history : EpisodeBatchPrefix mdp episodes n,
        (source.successorPolicy n history).TransitionBonusCover initialState
          episodes delta rewardBound transitionBonus

omit [Nonempty State] in
/--
State reachability and exploration discharge every expected-count margin in the
exact adaptive calibration contract; the transition-bonus cover is preserved.
-/
theorem exploratorySource_sourceCalibration_of_stateReachability
    {mdp : MDP State Action} {initialState : Measure State}
    [IsProbabilityMeasure initialState] {episodes : Nat}
    (initialTable : DeterministicMarkovPolicyTable mdp)
    (defaultState : State) (rewardBound transitionBonus delta : Real)
    (explorationRate : NNReal) (hexplorationRate : explorationRate <= 1)
    (rounds : Nat) (stateLower : Fin mdp.horizon -> State -> Real)
    (hmargin : ExploratoryStateCountMargin mdp episodes
      (multiBatchLocalDelta rounds delta) explorationRate stateLower)
    (hreachability :
      let behaviorSource := exploratorySource mdp initialState episodes
        initialTable defaultState transitionBonus explorationRate
          hexplorationRate
      SourceStateReachability behaviorSource rounds stateLower)
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
  dsimp only at hreachability hcover ⊢
  rcases hreachability with ⟨hinitialReachability, hsuccessorReachability⟩
  rcases hcover with ⟨hinitialCover, hsuccessorCover⟩
  constructor
  · exact MarkovPolicy.empiricalOptimisticCalibration_exploratoryPolicy_of_stateReachability
      initialTable initialState episodes (multiBatchLocalDelta rounds delta)
        rewardBound transitionBonus explorationRate hexplorationRate stateLower
        hinitialReachability hmargin hinitialCover
  · intro n hn history
    exact MarkovPolicy.empiricalOptimisticCalibration_exploratoryPolicy_of_stateReachability
      (successorTable defaultState transitionBonus n history)
      initialState episodes (multiBatchLocalDelta rounds delta)
        rewardBound transitionBonus explorationRate hexplorationRate stateLower
        (hsuccessorReachability n hn history) hmargin
        (hsuccessorCover n hn history)

omit [Nonempty State] in
/--
Route endpoint: state reachability plus uniform exploration discharges the
calibration premise of the adaptive confidence, optimism, and recommended
expected-regret theorem.
-/
theorem exploratorySource_trajectoryMeasure_allCoordinateConfidence_optimism_and_recommendedExpectedRegret_of_stateReachability
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
    (stateLower : Fin mdp.horizon -> State -> Real)
    (hmargin : ExploratoryStateCountMargin mdp episodes
      (multiBatchLocalDelta rounds delta) explorationRate stateLower)
    (hreachability :
      let behaviorSource := exploratorySource mdp initialState episodes
        initialTable defaultState transitionBonus explorationRate
          hexplorationRate
      SourceStateReachability behaviorSource rounds stateLower)
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
  have hcalibration :=
    exploratorySource_sourceCalibration_of_stateReachability
      (mdp := mdp) (initialState := initialState) (episodes := episodes)
      initialTable defaultState rewardBound transitionBonus delta
      explorationRate hexplorationRate rounds stateLower hmargin
      hreachability hcover
  exact
    exploratorySource_trajectoryMeasure_allCoordinateConfidence_optimism_and_recommendedExpectedRegret
      (mdp := mdp) (initialState := initialState) (episodes := episodes)
      initialTable defaultState rewardBound transitionBonus explorationRate
      hexplorationRate hrewardBound htransitionBonus_nonneg rounds hrounds
      hepisodes delta hdelta hdelta_le_one hcalibration

end AdaptiveEmpiricalOptimisticSource

end BanditRLProof.FiniteHorizonRL
