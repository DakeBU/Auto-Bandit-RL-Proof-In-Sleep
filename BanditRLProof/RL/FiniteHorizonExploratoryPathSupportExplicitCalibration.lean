import BanditRLProof.RL.FiniteHorizonExploratoryPathSupportReachability

/-!
# Explicit count and bonus calibration from exploratory path support

This module removes the two remaining abstract calibration inputs from the
path-support endpoint. A common state-action visit floor controls every
expected-count denominator. If the resulting finite-state, finite-horizon
transition coefficient is at most one half, the deterministic reward bound
itself is a sufficient transition bonus.
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

/--
Uniform transition-coordinate radius obtained from one common expected-count
floor. The denominator is useful when the count radius is strictly smaller
than `episodes * visitFloor`.
-/
noncomputable def uniformFloorTransitionCoordinateRadius
    (mdp : MDP State Action) (episodes : Nat) (delta visitFloor : Real) : Real :=
  2 * simultaneousCountConfidenceRadius mdp episodes delta /
    ((episodes : Real) * visitFloor -
      simultaneousCountConfidenceRadius mdp episodes delta)

omit [DecidableEq State] [DecidableEq Action]
    [MeasurableSingletonClass State] [MeasurableSingletonClass Action]
    [Nonempty Action] in
/-- A positive common denominator makes the uniform coordinate radius nonnegative. -/
theorem uniformFloorTransitionCoordinateRadius_nonneg
    {mdp : MDP State Action} {episodes : Nat} {delta visitFloor : Real}
    (hmargin : simultaneousCountConfidenceRadius mdp episodes delta <
      (episodes : Real) * visitFloor) :
    0 <= uniformFloorTransitionCoordinateRadius mdp episodes delta visitFloor := by
  apply div_nonneg
  · exact mul_nonneg (by norm_num)
      (Concentration.subGaussianSumConfidenceRadius_nonneg _ _)
  · linarith

namespace MarkovPolicy

omit [MeasurableSingletonClass State] [MeasurableSingletonClass Action]
    [Nonempty Action] in
/--
A common expected-count floor bounds every deterministic transition-coordinate
radius by the corresponding uniform-denominator radius.
-/
theorem expectedCountTransitionCoordinateRadius_le_uniformFloor
    {mdp : MDP State Action} (policy : MarkovPolicy mdp)
    (initialState : Measure State) [IsProbabilityMeasure initialState]
    (episodes : Nat) (delta visitFloor : Real)
    (hmargin : simultaneousCountConfidenceRadius mdp episodes delta <
      (episodes : Real) * visitFloor)
    (hcountFloor : forall coordinate : VisitCoordinate mdp,
      (episodes : Real) * visitFloor <=
        coordinate.expectedCount policy initialState episodes)
    (stage : Fin mdp.horizon) (state : State) (action : Action)
    (nextState : State) :
    policy.expectedCountTransitionCoordinateRadius initialState episodes delta
        stage state action nextState <=
      uniformFloorTransitionCoordinateRadius mdp episodes delta visitFloor := by
  let coordinate : VisitCoordinate mdp :=
    { stage := stage, state := state, action := action }
  have hradius : 0 <= simultaneousCountConfidenceRadius mdp episodes delta :=
    Concentration.subGaussianSumConfidenceRadius_nonneg _ _
  have hdenominator :
      0 < (episodes : Real) * visitFloor -
        simultaneousCountConfidenceRadius mdp episodes delta := by
    linarith
  have hdenominator_le :
      (episodes : Real) * visitFloor -
          simultaneousCountConfidenceRadius mdp episodes delta <=
        coordinate.expectedCount policy initialState episodes -
          simultaneousCountConfidenceRadius mdp episodes delta := by
    linarith [hcountFloor coordinate]
  exact div_le_div_of_nonneg_left (mul_nonneg (by norm_num) hradius)
    hdenominator hdenominator_le

end MarkovPolicy

/-- One state-action floor shared by every stage and target state on the path certificate. -/
def ExploratoryPathUniformVisitFloor
    {mdp : MDP State Action} {initialState : Measure State}
    (support : ExploratoryPathSupport mdp initialState)
    (explorationRate : NNReal) (visitFloor : Real) : Prop :=
  forall stage state,
    visitFloor <=
      exploratoryPathStateLower support explorationRate stage state *
        exploratoryActionProbabilityFloor Action explorationRate

omit [DecidableEq State] [DecidableEq Action]
    [MeasurableSingletonClass State] [MeasurableSingletonClass Action]
    [Nonempty Action] in
/-- A strict scalar count inequality discharges the full exploratory margin. -/
theorem ExploratoryPathUniformVisitFloor.exploratoryStateCountMargin
    {mdp : MDP State Action} {initialState : Measure State}
    {episodes : Nat} {delta : Real}
    (support : ExploratoryPathSupport mdp initialState)
    (explorationRate : NNReal) (visitFloor : Real)
    (hfloor : ExploratoryPathUniformVisitFloor support explorationRate visitFloor)
    (hmargin : simultaneousCountConfidenceRadius mdp episodes delta <
      (episodes : Real) * visitFloor) :
    ExploratoryStateCountMargin mdp episodes delta explorationRate
      (exploratoryPathStateLower support explorationRate) := by
  intro coordinate
  exact lt_of_lt_of_le hmargin
    (mul_le_mul_of_nonneg_left (hfloor coordinate.stage coordinate.state)
      (Nat.cast_nonneg episodes))

namespace DeterministicMarkovPolicyTable

/-- Every exploratory table inherits the common expected-count floor. -/
theorem uniformVisitFloor_expectedCount_le
    {mdp : MDP State Action} (table : DeterministicMarkovPolicyTable mdp)
    (initialState : Measure State) [IsProbabilityMeasure initialState]
    (episodes : Nat) (support : ExploratoryPathSupport mdp initialState)
    (explorationRate : NNReal) (hexplorationRate : explorationRate <= 1)
    (visitFloor : Real)
    (hfloor : ExploratoryPathUniformVisitFloor support explorationRate visitFloor)
    (coordinate : VisitCoordinate mdp) :
    (episodes : Real) * visitFloor <=
      coordinate.expectedCount
        (table.exploratoryPolicy explorationRate hexplorationRate)
        initialState episodes := by
  calc
    (episodes : Real) * visitFloor <=
        (episodes : Real) *
          (exploratoryPathStateLower support explorationRate
              coordinate.stage coordinate.state *
            exploratoryActionProbabilityFloor Action explorationRate) :=
      mul_le_mul_of_nonneg_left
        (hfloor coordinate.stage coordinate.state) (Nat.cast_nonneg episodes)
    _ <= coordinate.expectedCount
          (table.exploratoryPolicy explorationRate hexplorationRate)
          initialState episodes :=
      table.stateLower_expectedCount_le initialState episodes explorationRate
        hexplorationRate (exploratoryPathStateLower support explorationRate)
        (table.exploratoryPathStateLower_le_stageStateProbability
          initialState support explorationRate hexplorationRate) coordinate

end DeterministicMarkovPolicyTable

namespace MarkovPolicy

omit [MeasurableSingletonClass State] [MeasurableSingletonClass Action]
    [Nonempty Action] in
/--
If the uniform transition coefficient is at most one half, `rewardBound`
covers every transition-radius/value-envelope sum when it is used as the
transition bonus.
-/
theorem transitionBonusCover_rewardBound_of_uniformExpectedCountFloor
    {mdp : MDP State Action} (policy : MarkovPolicy mdp)
    (initialState : Measure State) [IsProbabilityMeasure initialState]
    (episodes : Nat) (delta visitFloor rewardBound : Real)
    (hmargin : simultaneousCountConfidenceRadius mdp episodes delta <
      (episodes : Real) * visitFloor)
    (hcountFloor : forall coordinate : VisitCoordinate mdp,
      (episodes : Real) * visitFloor <=
        coordinate.expectedCount policy initialState episodes)
    (hrewardBound_nonneg : 0 <= rewardBound)
    (hcontraction :
      (Fintype.card State : Real) *
          uniformFloorTransitionCoordinateRadius mdp episodes delta visitFloor *
          (mdp.horizon : Real) <=
        1 / 2) :
    policy.TransitionBonusCover initialState episodes delta rewardBound rewardBound := by
  intro remaining hremaining state action
  have huniform_nonneg :
      0 <= uniformFloorTransitionCoordinateRadius mdp episodes delta visitFloor :=
    uniformFloorTransitionCoordinateRadius_nonneg hmargin
  have henvelope_nonneg :
      0 <= empiricalFiniteBatchValueEnvelope rewardBound rewardBound remaining := by
    unfold empiricalFiniteBatchValueEnvelope
    positivity
  have hremaining_le : (remaining : Real) <= (mdp.horizon : Real) := by
    exact_mod_cast (show remaining <= mdp.horizon by omega)
  calc
    (∑ nextState,
        policy.expectedCountTransitionCoordinateRadius initialState episodes delta
            (mdp.decisionStageRemaining remaining hremaining)
            state action nextState *
          empiricalFiniteBatchValueEnvelope rewardBound rewardBound remaining) <=
        ∑ _nextState : State,
          uniformFloorTransitionCoordinateRadius mdp episodes delta visitFloor *
            empiricalFiniteBatchValueEnvelope rewardBound rewardBound remaining := by
      apply Finset.sum_le_sum
      intro nextState _hnextState
      exact mul_le_mul_of_nonneg_right
        (policy.expectedCountTransitionCoordinateRadius_le_uniformFloor
          initialState episodes delta visitFloor hmargin hcountFloor
          (mdp.decisionStageRemaining remaining hremaining)
          state action nextState)
        henvelope_nonneg
    _ = ((Fintype.card State : Real) *
          uniformFloorTransitionCoordinateRadius mdp episodes delta visitFloor *
          (remaining : Real)) * (2 * rewardBound) := by
      simp [empiricalFiniteBatchValueEnvelope]
      ring
    _ <= ((Fintype.card State : Real) *
          uniformFloorTransitionCoordinateRadius mdp episodes delta visitFloor *
          (mdp.horizon : Real)) * (2 * rewardBound) := by
      gcongr
    _ <= (1 / 2 : Real) * (2 * rewardBound) := by
      exact mul_le_mul_of_nonneg_right hcontraction (mul_nonneg (by norm_num) hrewardBound_nonneg)
    _ = rewardBound := by ring

end MarkovPolicy

namespace AdaptiveEmpiricalOptimisticSource

/-- The scalar path-support conditions construct the source-wide bonus cover. -/
theorem exploratorySource_sourceTransitionBonusCover_of_pathSupport_explicitCalibration
    {mdp : MDP State Action} {initialState : Measure State}
    [IsProbabilityMeasure initialState] {episodes : Nat}
    (initialTable : DeterministicMarkovPolicyTable mdp)
    (defaultState : State) (rewardBound delta : Real)
    (explorationRate : NNReal) (hexplorationRate : explorationRate <= 1)
    (rounds : Nat) (support : ExploratoryPathSupport mdp initialState)
    (visitFloor : Real)
    (hfloor : ExploratoryPathUniformVisitFloor support explorationRate visitFloor)
    (hmargin : simultaneousCountConfidenceRadius mdp episodes
        (multiBatchLocalDelta rounds delta) <
      (episodes : Real) * visitFloor)
    (hrewardBound_nonneg : 0 <= rewardBound)
    (hcontraction :
      (Fintype.card State : Real) *
          uniformFloorTransitionCoordinateRadius mdp episodes
            (multiBatchLocalDelta rounds delta) visitFloor *
          (mdp.horizon : Real) <=
        1 / 2) :
    let behaviorSource := exploratorySource mdp initialState episodes
      initialTable defaultState rewardBound explorationRate hexplorationRate
    SourceTransitionBonusCover behaviorSource rounds
      (multiBatchLocalDelta rounds delta) rewardBound rewardBound := by
  dsimp only
  constructor
  · exact
      MarkovPolicy.transitionBonusCover_rewardBound_of_uniformExpectedCountFloor
          (initialTable.exploratoryPolicy explorationRate hexplorationRate)
          initialState episodes (multiBatchLocalDelta rounds delta) visitFloor
          rewardBound hmargin
          (initialTable.uniformVisitFloor_expectedCount_le initialState episodes
            support explorationRate hexplorationRate visitFloor hfloor)
          hrewardBound_nonneg hcontraction
  · intro n hn history
    let table := successorTable defaultState rewardBound n history
    exact
      MarkovPolicy.transitionBonusCover_rewardBound_of_uniformExpectedCountFloor
          (table.exploratoryPolicy explorationRate hexplorationRate)
          initialState episodes (multiBatchLocalDelta rounds delta) visitFloor
          rewardBound hmargin
          (table.uniformVisitFloor_expectedCount_le initialState episodes support
            explorationRate hexplorationRate visitFloor hfloor)
          hrewardBound_nonneg hcontraction

/-- Explicit path support and scalar rate conditions construct `SourceCalibration`. -/
theorem exploratorySource_sourceCalibration_of_pathSupport_explicitCalibration
    {mdp : MDP State Action} {initialState : Measure State}
    [IsProbabilityMeasure initialState] {episodes : Nat}
    (initialTable : DeterministicMarkovPolicyTable mdp)
    (defaultState : State) (rewardBound delta : Real)
    (explorationRate : NNReal) (hexplorationRate : explorationRate <= 1)
    (rounds : Nat) (support : ExploratoryPathSupport mdp initialState)
    (visitFloor : Real)
    (hfloor : ExploratoryPathUniformVisitFloor support explorationRate visitFloor)
    (hmargin : simultaneousCountConfidenceRadius mdp episodes
        (multiBatchLocalDelta rounds delta) <
      (episodes : Real) * visitFloor)
    (hrewardBound_nonneg : 0 <= rewardBound)
    (hcontraction :
      (Fintype.card State : Real) *
          uniformFloorTransitionCoordinateRadius mdp episodes
            (multiBatchLocalDelta rounds delta) visitFloor *
          (mdp.horizon : Real) <=
        1 / 2) :
    let behaviorSource := exploratorySource mdp initialState episodes
      initialTable defaultState rewardBound explorationRate hexplorationRate
    SourceCalibration behaviorSource rounds delta rewardBound rewardBound := by
  apply exploratorySource_sourceCalibration_of_pathSupport
    (mdp := mdp) (initialState := initialState) (episodes := episodes)
    initialTable defaultState rewardBound rewardBound delta explorationRate
      hexplorationRate rounds support
  · exact hfloor.exploratoryStateCountMargin support explorationRate visitFloor hmargin
  · exact exploratorySource_sourceTransitionBonusCover_of_pathSupport_explicitCalibration
      initialTable defaultState rewardBound delta explorationRate hexplorationRate
      rounds support visitFloor hfloor hmargin hrewardBound_nonneg hcontraction

/--
Route endpoint: path support plus explicit scalar count and half-contraction
conditions yield the adaptive global confidence, optimism, and recommended
expected-regret theorem with `transitionBonus = rewardBound`.
-/
theorem exploratorySource_trajectoryMeasure_allCoordinateConfidence_optimism_and_recommendedExpectedRegret_of_pathSupport_explicitCalibration
    {mdp : MDP State Action} {initialState : Measure State}
    [IsProbabilityMeasure initialState] {episodes : Nat}
    (initialTable : DeterministicMarkovPolicyTable mdp)
    (defaultState : State) (rewardBound : Real)
    (explorationRate : NNReal) (hexplorationRate : explorationRate <= 1)
    (hrewardBound : forall state action, |mdp.reward state action| <= rewardBound)
    (rounds : Nat) (hrounds : 0 < rounds)
    (hepisodes : 0 < episodes) (delta : Real) (hdelta : 0 < delta)
    (hdelta_le_one : delta <= 1)
    (support : ExploratoryPathSupport mdp initialState)
    (visitFloor : Real)
    (hfloor : ExploratoryPathUniformVisitFloor support explorationRate visitFloor)
    (hmargin : simultaneousCountConfidenceRadius mdp episodes
        (multiBatchLocalDelta rounds delta) <
      (episodes : Real) * visitFloor)
    (hcontraction :
      (Fintype.card State : Real) *
          uniformFloorTransitionCoordinateRadius mdp episodes
            (multiBatchLocalDelta rounds delta) visitFloor *
          (mdp.horizon : Real) <=
        1 / 2) :
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
          adaptiveEmpiricalOptimisticOccupancyRadiusSum
            (mdp := mdp) (initialState := initialState) (episodes := episodes)
            trajectory defaultState rewardBound rounds := by
  have hrewardBound_nonneg : 0 <= rewardBound := by
    let action : Action := Classical.choice inferInstance
    linarith [abs_nonneg (mdp.reward defaultState action),
      hrewardBound defaultState action]
  apply exploratorySource_trajectoryMeasure_allCoordinateConfidence_optimism_and_recommendedExpectedRegret_of_pathSupport
    (mdp := mdp) (initialState := initialState) (episodes := episodes)
    initialTable defaultState rewardBound rewardBound explorationRate
      hexplorationRate hrewardBound hrewardBound_nonneg rounds hrounds
      hepisodes delta hdelta hdelta_le_one support
  · exact hfloor.exploratoryStateCountMargin support explorationRate visitFloor hmargin
  · exact exploratorySource_sourceTransitionBonusCover_of_pathSupport_explicitCalibration
      initialTable defaultState rewardBound delta explorationRate hexplorationRate
      rounds support visitFloor hfloor hmargin hrewardBound_nonneg hcontraction

end AdaptiveEmpiricalOptimisticSource

end BanditRLProof.FiniteHorizonRL
