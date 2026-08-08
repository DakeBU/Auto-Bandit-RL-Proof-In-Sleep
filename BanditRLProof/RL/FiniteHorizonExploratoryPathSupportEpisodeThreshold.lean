import BanditRLProof.RL.FiniteHorizonExploratoryPathSupportExplicitCalibration

/-!
# Episode-threshold calibration from exploratory path support

This module solves the scalar square-root/logarithm obligations left by the
explicit path-support calibration route. A closed-form lower bound on the
number of episodes implies both the strict count margin and the finite-state,
finite-horizon half contraction, then recovers the same adaptive confidence,
optimism, and recommended-policy expected-regret endpoint.
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

/-- Dimension factor sufficient to turn a radius margin into the half contraction. -/
noncomputable def exploratoryPathCalibrationDimensionFactor
    (mdp : MDP State Action) : Real :=
  4 * (Fintype.card State : Real) * (mdp.horizon : Real) + 1

omit [DecidableEq State] [DecidableEq Action]
    [MeasurableSingletonClass State] [MeasurableSingletonClass Action]
    [Nonempty Action] in
/-- The calibration dimension factor is at least one. -/
theorem one_le_exploratoryPathCalibrationDimensionFactor
    (mdp : MDP State Action) :
    1 <= exploratoryPathCalibrationDimensionFactor mdp := by
  unfold exploratoryPathCalibrationDimensionFactor
  have hproduct :
      0 <= 4 * (Fintype.card State : Real) * (mdp.horizon : Real) := by
    positivity
  linarith

/--
Closed-form Real episode threshold for the local simultaneous-count budget.
Its denominator is positive when `visitFloor` is positive.
-/
noncomputable def exploratoryPathCalibrationEpisodeThreshold
    (mdp : MDP State Action) (rounds : Nat)
    (delta visitFloor : Real) : Real :=
  (exploratoryPathCalibrationDimensionFactor mdp) ^ 2 *
      Real.log
        (2 / simultaneousCountDelta mdp (multiBatchLocalDelta rounds delta)) /
    (2 * visitFloor ^ 2)

omit [DecidableEq State] [DecidableEq Action]
    [MeasurableSingletonClass State] [MeasurableSingletonClass Action] in
/--
Above the explicit episode threshold, the simultaneous count radius is less
than the common expected-count floor divided by the calibration dimension
factor.
-/
theorem simultaneousCountConfidenceRadius_lt_episodes_mul_visitFloor_div_dimensionFactor_of_threshold
    (mdp : MDP State Action) (witnessState : State)
    {rounds episodes : Nat} {delta visitFloor : Real}
    (hhorizon : 0 < mdp.horizon) (hrounds : 0 < rounds)
    (hepisodes : 0 < episodes) (hdelta : 0 < delta)
    (hdelta_le_one : delta <= 1) (hvisitFloor : 0 < visitFloor)
    (hthreshold : exploratoryPathCalibrationEpisodeThreshold mdp rounds delta visitFloor <
      (episodes : Real)) :
    simultaneousCountConfidenceRadius mdp episodes
        (multiBatchLocalDelta rounds delta) <
      (episodes : Real) * visitFloor /
        exploratoryPathCalibrationDimensionFactor mdp := by
  let witnessAction : Action := Classical.choice inferInstance
  have hcoordinate : Nonempty (CountCoordinate mdp) :=
    ⟨CountCoordinate.visit ⟨0, hhorizon⟩ witnessState witnessAction⟩
  have hroundsReal : (0 : Real) < rounds := by exact_mod_cast hrounds
  have hlocalDeltaPos : 0 < multiBatchLocalDelta rounds delta := by
    exact div_pos hdelta hroundsReal
  have hroundsOne : (1 : Real) <= rounds := by exact_mod_cast hrounds
  have hlocalDeltaLeOne : multiBatchLocalDelta rounds delta <= 1 := by
    exact (div_le_self (le_of_lt hdelta) hroundsOne).trans hdelta_le_one
  have hcoordinateDeltaPos :
      0 < simultaneousCountDelta mdp (multiBatchLocalDelta rounds delta) :=
    MarkovPolicy.simultaneousCountDelta_pos hcoordinate hlocalDeltaPos
  have hcoordinateDeltaLeOne :
      simultaneousCountDelta mdp (multiBatchLocalDelta rounds delta) <= 1 :=
    MarkovPolicy.simultaneousCountDelta_le_one hcoordinate
      hlocalDeltaPos hlocalDeltaLeOne
  let q := exploratoryPathCalibrationDimensionFactor mdp
  let radius := simultaneousCountConfidenceRadius mdp episodes
    (multiBatchLocalDelta rounds delta)
  let logarithm := Real.log
    (2 / simultaneousCountDelta mdp (multiBatchLocalDelta rounds delta))
  have hqOne : (1 : Real) <= q := by
    exact one_le_exploratoryPathCalibrationDimensionFactor mdp
  have hqPos : 0 < q := zero_lt_one.trans_le hqOne
  have hepisodesReal : (0 : Real) < episodes := by exact_mod_cast hepisodes
  have hradiusNonneg : 0 <= radius :=
    Concentration.subGaussianSumConfidenceRadius_nonneg _ _
  have hradiusSq : radius ^ 2 = (episodes : Real) / 2 * logarithm := by
    change
      (Concentration.subGaussianSumConfidenceRadius
          (MarkovPolicy.iidBernoulliVarianceProxy episodes)
          (simultaneousCountDelta mdp (multiBatchLocalDelta rounds delta))) ^ 2 =
        (episodes : Real) / 2 * logarithm
    rw [Concentration.subGaussianSumConfidenceRadius_sq _ _
      hcoordinateDeltaPos hcoordinateDeltaLeOne]
    rw [MarkovPolicy.iidBernoulliVarianceProxy_eq]
    dsimp [logarithm]
    push_cast
    ring
  have hthresholdProduct :
      q ^ 2 * logarithm <
        (episodes : Real) * (2 * visitFloor ^ 2) := by
    have hdenominator : 0 < 2 * visitFloor ^ 2 := by positivity
    exact (div_lt_iff₀ hdenominator).mp (by
      simpa [exploratoryPathCalibrationEpisodeThreshold, q, logarithm]
        using hthreshold)
  have hsquare :
      (q * radius) ^ 2 < ((episodes : Real) * visitFloor) ^ 2 := by
    rw [mul_pow, hradiusSq]
    nlinarith
  have hscaled : q * radius < (episodes : Real) * visitFloor :=
    (sq_lt_sq₀ (mul_nonneg (le_of_lt hqPos) hradiusNonneg)
      (mul_nonneg (le_of_lt hepisodesReal) (le_of_lt hvisitFloor))).mp hsquare
  exact (lt_div_iff₀ hqPos).2 (by simpa [mul_comm] using hscaled)

omit [DecidableEq State] [DecidableEq Action]
    [MeasurableSingletonClass State] [MeasurableSingletonClass Action] in
/--
The episode threshold simultaneously discharges the strict count margin and
the half-contraction premise of the explicit path-support calibration route.
-/
theorem episodeThreshold_countMargin_and_halfContraction
    (mdp : MDP State Action) (witnessState : State)
    {rounds episodes : Nat} {delta visitFloor : Real}
    (hhorizon : 0 < mdp.horizon) (hrounds : 0 < rounds)
    (hepisodes : 0 < episodes) (hdelta : 0 < delta)
    (hdelta_le_one : delta <= 1) (hvisitFloor : 0 < visitFloor)
    (hthreshold : exploratoryPathCalibrationEpisodeThreshold mdp rounds delta visitFloor <
      (episodes : Real)) :
    simultaneousCountConfidenceRadius mdp episodes
        (multiBatchLocalDelta rounds delta) <
        (episodes : Real) * visitFloor /\
      (Fintype.card State : Real) *
          uniformFloorTransitionCoordinateRadius mdp episodes
            (multiBatchLocalDelta rounds delta) visitFloor *
          (mdp.horizon : Real) <=
        1 / 2 := by
  let q := exploratoryPathCalibrationDimensionFactor mdp
  let radius := simultaneousCountConfidenceRadius mdp episodes
    (multiBatchLocalDelta rounds delta)
  have hqOne : (1 : Real) <= q :=
    one_le_exploratoryPathCalibrationDimensionFactor mdp
  have hqPos : 0 < q := zero_lt_one.trans_le hqOne
  have hepisodesReal : (0 : Real) < episodes := by exact_mod_cast hepisodes
  have hradiusNonneg : 0 <= radius :=
    Concentration.subGaussianSumConfidenceRadius_nonneg _ _
  have hratio : radius < (episodes : Real) * visitFloor / q :=
    simultaneousCountConfidenceRadius_lt_episodes_mul_visitFloor_div_dimensionFactor_of_threshold
      mdp witnessState hhorizon hrounds hepisodes hdelta hdelta_le_one
      hvisitFloor hthreshold
  have hmargin : radius < (episodes : Real) * visitFloor :=
    hratio.trans_le
      (div_le_self
        (mul_nonneg (le_of_lt hepisodesReal) (le_of_lt hvisitFloor)) hqOne)
  refine ⟨hmargin, ?_⟩
  have hscaled : q * radius < (episodes : Real) * visitFloor := by
    have hradiusScaled : radius * q < (episodes : Real) * visitFloor :=
      (lt_div_iff₀ hqPos).mp hratio
    simpa [mul_comm] using hradiusScaled
  have hdenominator : 0 < (episodes : Real) * visitFloor - radius := by
    linarith
  have hnumerator :
      2 * (Fintype.card State : Real) * (mdp.horizon : Real) * radius <=
        (1 / 2 : Real) * ((episodes : Real) * visitFloor - radius) := by
    dsimp [q, exploratoryPathCalibrationDimensionFactor] at hscaled
    nlinarith
  rw [uniformFloorTransitionCoordinateRadius]
  calc
    (Fintype.card State : Real) *
          (2 * radius / ((episodes : Real) * visitFloor - radius)) *
          (mdp.horizon : Real) =
        (2 * (Fintype.card State : Real) * (mdp.horizon : Real) * radius) /
          ((episodes : Real) * visitFloor - radius) := by ring
    _ <= 1 / 2 := (div_le_iff₀ hdenominator).2 (by
      simpa [mul_comm, mul_left_comm, mul_assoc] using hnumerator)

namespace AdaptiveEmpiricalOptimisticSource

/-- The closed-form episode threshold constructs the source-wide transition cover. -/
theorem exploratorySource_sourceTransitionBonusCover_of_pathSupport_episodeThreshold
    {mdp : MDP State Action} {initialState : Measure State}
    [IsProbabilityMeasure initialState] {episodes : Nat}
    (initialTable : DeterministicMarkovPolicyTable mdp)
    (defaultState : State) (rewardBound delta : Real)
    (explorationRate : NNReal) (hexplorationRate : explorationRate <= 1)
    (rounds : Nat) (hhorizon : 0 < mdp.horizon) (hrounds : 0 < rounds)
    (hepisodes : 0 < episodes) (hdelta : 0 < delta)
    (hdelta_le_one : delta <= 1)
    (support : ExploratoryPathSupport mdp initialState)
    (visitFloor : Real) (hvisitFloor : 0 < visitFloor)
    (hfloor : ExploratoryPathUniformVisitFloor support explorationRate visitFloor)
    (hthreshold : exploratoryPathCalibrationEpisodeThreshold mdp rounds delta visitFloor <
      (episodes : Real))
    (hrewardBound_nonneg : 0 <= rewardBound) :
    let behaviorSource := exploratorySource mdp initialState episodes
      initialTable defaultState rewardBound explorationRate hexplorationRate
    SourceTransitionBonusCover behaviorSource rounds
      (multiBatchLocalDelta rounds delta) rewardBound rewardBound := by
  obtain ⟨hmargin, hcontraction⟩ :=
    episodeThreshold_countMargin_and_halfContraction mdp defaultState
      hhorizon hrounds hepisodes hdelta hdelta_le_one hvisitFloor hthreshold
  exact exploratorySource_sourceTransitionBonusCover_of_pathSupport_explicitCalibration
    initialTable defaultState rewardBound delta explorationRate hexplorationRate
    rounds support visitFloor hfloor hmargin hrewardBound_nonneg hcontraction

/-- The closed-form episode threshold constructs the full source calibration. -/
theorem exploratorySource_sourceCalibration_of_pathSupport_episodeThreshold
    {mdp : MDP State Action} {initialState : Measure State}
    [IsProbabilityMeasure initialState] {episodes : Nat}
    (initialTable : DeterministicMarkovPolicyTable mdp)
    (defaultState : State) (rewardBound delta : Real)
    (explorationRate : NNReal) (hexplorationRate : explorationRate <= 1)
    (rounds : Nat) (hhorizon : 0 < mdp.horizon) (hrounds : 0 < rounds)
    (hepisodes : 0 < episodes) (hdelta : 0 < delta)
    (hdelta_le_one : delta <= 1)
    (support : ExploratoryPathSupport mdp initialState)
    (visitFloor : Real) (hvisitFloor : 0 < visitFloor)
    (hfloor : ExploratoryPathUniformVisitFloor support explorationRate visitFloor)
    (hthreshold : exploratoryPathCalibrationEpisodeThreshold mdp rounds delta visitFloor <
      (episodes : Real))
    (hrewardBound_nonneg : 0 <= rewardBound) :
    let behaviorSource := exploratorySource mdp initialState episodes
      initialTable defaultState rewardBound explorationRate hexplorationRate
    SourceCalibration behaviorSource rounds delta rewardBound rewardBound := by
  obtain ⟨hmargin, hcontraction⟩ :=
    episodeThreshold_countMargin_and_halfContraction mdp defaultState
      hhorizon hrounds hepisodes hdelta hdelta_le_one hvisitFloor hthreshold
  exact exploratorySource_sourceCalibration_of_pathSupport_explicitCalibration
    initialTable defaultState rewardBound delta explorationRate hexplorationRate
    rounds support visitFloor hfloor hmargin hrewardBound_nonneg hcontraction

/--
Route endpoint: path support and one explicit episode threshold imply global
adaptive count confidence, roundwise optimism, and recommended expected regret.
-/
theorem exploratorySource_trajectoryMeasure_allCoordinateConfidence_optimism_and_recommendedExpectedRegret_of_pathSupport_episodeThreshold
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
          adaptiveEmpiricalOptimisticOccupancyRadiusSum
            (mdp := mdp) (initialState := initialState) (episodes := episodes)
            trajectory defaultState rewardBound rounds := by
  obtain ⟨hmargin, hcontraction⟩ :=
    episodeThreshold_countMargin_and_halfContraction mdp defaultState
      hhorizon hrounds hepisodes hdelta hdelta_le_one hvisitFloor hthreshold
  exact exploratorySource_trajectoryMeasure_allCoordinateConfidence_optimism_and_recommendedExpectedRegret_of_pathSupport_explicitCalibration
    initialTable defaultState rewardBound explorationRate hexplorationRate
    hrewardBound rounds hrounds hepisodes delta hdelta hdelta_le_one support
    visitFloor hfloor hmargin hcontraction

end AdaptiveEmpiricalOptimisticSource

end BanditRLProof.FiniteHorizonRL
