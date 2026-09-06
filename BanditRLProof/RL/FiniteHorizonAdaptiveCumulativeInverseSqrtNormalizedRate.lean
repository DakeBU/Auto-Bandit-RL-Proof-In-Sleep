import BanditRLProof.RL.FiniteHorizonAdaptiveCumulativeInverseSqrtExplicitRate

/-!
# Normalized adaptive cumulative inverse-square-root rate

This module specializes the explicit two-scale calibration to rewards bounded
in absolute value by one.  It fixes the zero-count budget to one, chooses the
inverse-square-root scale from the logarithmic factor and visit floor, and
replaces both scalar calibration premises by one episode threshold.
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

namespace AdaptiveEpisodeBatchSource

/-- Canonical statistical scale for rewards and zero-count budget bounded by one. -/
noncomputable def normalizedCumulativeInverseSqrtScale
    (mdp : MDP State Action) (rounds : Nat)
    (delta visitFloor : Real) : Real :=
  4 * (Fintype.card State : Real) * (mdp.horizon : Real) *
      Real.sqrt (cumulativeInverseSqrtLogFactor mdp rounds delta) /
    Real.sqrt visitFloor

/-- One sufficient episode threshold for the normalized scale choice. -/
noncomputable def normalizedCumulativeInverseSqrtEpisodeThreshold
    (mdp : MDP State Action) (rounds : Nat)
    (delta visitFloor : Real) : Real :=
  32 * (Fintype.card State : Real) ^ 2 * (mdp.horizon : Real) ^ 2 *
      cumulativeInverseSqrtLogFactor mdp rounds delta /
    visitFloor ^ 2

/-- The normalized capped count radius used by the concrete source. -/
noncomputable def normalizedCumulativeInverseSqrtCountRadius
    (mdp : MDP State Action) (rounds : Nat)
    (delta visitFloor : Real) : TransitionCountRadius :=
  TransitionCountRadius.cappedInverseSqrt 1
    (normalizedCumulativeInverseSqrtScale mdp rounds delta visitFloor)
    (by norm_num) (by
      unfold normalizedCumulativeInverseSqrtScale
      positivity)

/-- Closed recommendation-regret bound after fixing budget and scale. -/
noncomputable def normalizedCumulativeInverseSqrtRecommendedExpectedRegretBound
    (mdp : MDP State Action) (episodes rounds : Nat)
    (delta visitFloor : Real) : Real :=
  cumulativeInverseSqrtRecommendedExpectedRegretBound mdp episodes rounds
    visitFloor 1
    (normalizedCumulativeInverseSqrtScale mdp rounds delta visitFloor)

omit [DecidableEq State] [DecidableEq Action]
    [MeasurableSingletonClass State] [MeasurableSingletonClass Action]
    [Nonempty Action] in
/-- The normalized scale is nonnegative without additional scalar premises. -/
theorem normalizedCumulativeInverseSqrtScale_nonneg
    (mdp : MDP State Action) (rounds : Nat)
    (delta visitFloor : Real) :
    0 <= normalizedCumulativeInverseSqrtScale mdp rounds delta visitFloor := by
  unfold normalizedCumulativeInverseSqrtScale
  positivity

/-- The normalized scale exactly covers the explicit two-scale coefficient. -/
theorem normalizedCumulativeInverseSqrtScale_cover
    (mdp : MDP State Action) {rounds : Nat}
    (hhorizon : 0 < mdp.horizon) (hrounds : 0 < rounds)
    {delta visitFloor : Real} (hdelta : 0 < delta)
    (hdelta_le_one : delta <= 1) (hvisitFloor : 0 < visitFloor) :
    (cumulativeInverseSqrtCoverCoefficient mdp 1 1) ^ 2 *
        cumulativeInverseSqrtLogFactor mdp rounds delta <=
      (normalizedCumulativeInverseSqrtScale mdp rounds delta visitFloor) ^ 2 *
        visitFloor := by
  have hlog : 0 <= cumulativeInverseSqrtLogFactor mdp rounds delta :=
    cumulativeInverseSqrtLogFactor_nonneg mdp hhorizon hrounds
      hdelta hdelta_le_one
  have hsqrtVisit : 0 < Real.sqrt visitFloor := Real.sqrt_pos.2 hvisitFloor
  rw [normalizedCumulativeInverseSqrtScale]
  apply le_of_eq
  calc
    (cumulativeInverseSqrtCoverCoefficient mdp 1 1) ^ 2 *
          cumulativeInverseSqrtLogFactor mdp rounds delta =
        (4 * (Fintype.card State : Real) * (mdp.horizon : Real)) ^ 2 *
          cumulativeInverseSqrtLogFactor mdp rounds delta := by
            unfold cumulativeInverseSqrtCoverCoefficient
            ring
    _ = (4 * (Fintype.card State : Real) * (mdp.horizon : Real)) ^ 2 *
          (Real.sqrt (cumulativeInverseSqrtLogFactor mdp rounds delta)) ^ 2 := by
            rw [Real.sq_sqrt hlog]
    _ = (4 * (Fintype.card State : Real) * (mdp.horizon : Real) *
            Real.sqrt (cumulativeInverseSqrtLogFactor mdp rounds delta) /
              Real.sqrt visitFloor) ^ 2 * visitFloor := by
            rw [div_pow, Real.sq_sqrt hvisitFloor.le]
            field_simp

/-- The old max threshold is bounded by the single normalized threshold. -/
theorem cumulativeInverseSqrtCalibrationEpisodeThreshold_le_normalized
    (mdp : MDP State Action) {rounds : Nat}
    (hhorizon : 0 < mdp.horizon) (hrounds : 0 < rounds)
    {delta visitFloor : Real} (hdelta : 0 < delta)
    (hdelta_le_one : delta <= 1) (hvisitFloor : 0 < visitFloor) :
    cumulativeInverseSqrtCalibrationEpisodeThreshold mdp rounds delta
        visitFloor 1 1 <=
      normalizedCumulativeInverseSqrtEpisodeThreshold mdp rounds delta
        visitFloor := by
  have hlog : 0 <= cumulativeInverseSqrtLogFactor mdp rounds delta :=
    cumulativeInverseSqrtLogFactor_nonneg mdp hhorizon hrounds
      hdelta hdelta_le_one
  have hcardNat : 0 < Fintype.card State := Fintype.card_pos
  have hcard : (1 : Real) <= Fintype.card State := by exact_mod_cast hcardNat
  have hhorizonReal : (1 : Real) <= mdp.horizon := by exact_mod_cast hhorizon
  have hcardSq : (1 : Real) <= (Fintype.card State : Real) ^ 2 := by
    nlinarith
  have hhorizonSq : (1 : Real) <= (mdp.horizon : Real) ^ 2 := by
    nlinarith
  have hproduct : (1 : Real) <=
      (Fintype.card State : Real) ^ 2 * (mdp.horizon : Real) ^ 2 :=
    by simpa using
      (mul_le_mul hcardSq hhorizonSq (by positivity) (by positivity))
  have hcoefficient : (2 : Real) <=
      32 * (Fintype.card State : Real) ^ 2 * (mdp.horizon : Real) ^ 2 := by
    nlinarith
  have hvisitFloorSq : 0 < visitFloor ^ 2 := sq_pos_of_pos hvisitFloor
  unfold cumulativeInverseSqrtCalibrationEpisodeThreshold
  apply max_le
  · unfold normalizedCumulativeInverseSqrtEpisodeThreshold
    apply (div_le_div_iff_of_pos_right hvisitFloorSq).2
    exact mul_le_mul_of_nonneg_right hcoefficient hlog
  · apply le_of_eq
    unfold normalizedCumulativeInverseSqrtEpisodeThreshold
    unfold cumulativeInverseSqrtCoverCoefficient
    norm_num
    ring

/-- A strict normalized threshold implies the exact parent threshold. -/
theorem cumulativeInverseSqrtCalibrationEpisodeThreshold_lt_of_normalizedThreshold
    (mdp : MDP State Action) {episodes rounds : Nat}
    (hhorizon : 0 < mdp.horizon) (hrounds : 0 < rounds)
    {delta visitFloor : Real} (hdelta : 0 < delta)
    (hdelta_le_one : delta <= 1) (hvisitFloor : 0 < visitFloor)
    (hthreshold :
      normalizedCumulativeInverseSqrtEpisodeThreshold mdp rounds delta
          visitFloor < (episodes : Real)) :
    cumulativeInverseSqrtCalibrationEpisodeThreshold mdp rounds delta
        visitFloor 1 1 < (episodes : Real) :=
  lt_of_le_of_lt
    (cumulativeInverseSqrtCalibrationEpisodeThreshold_le_normalized mdp
      hhorizon hrounds hdelta hdelta_le_one hvisitFloor)
    hthreshold

/-- The single normalized threshold constructs the complete parent calibration. -/
theorem normalizedCumulativeInverseSqrtPathCalibration_of_episodeThreshold
    (mdp : MDP State Action) {episodes rounds : Nat}
    (hhorizon : 0 < mdp.horizon) (hrounds : 0 < rounds)
    (hepisodes : 0 < episodes) {delta visitFloor : Real}
    (hdelta : 0 < delta) (hdelta_le_one : delta <= 1)
    (hvisitFloor : 0 < visitFloor)
    (hthreshold :
      normalizedCumulativeInverseSqrtEpisodeThreshold mdp rounds delta
          visitFloor < (episodes : Real)) :
    CumulativeInverseSqrtPathCalibration mdp episodes rounds delta visitFloor
      1 1 (normalizedCumulativeInverseSqrtScale mdp rounds delta visitFloor) := by
  exact cumulativeInverseSqrtPathCalibration_of_episodeThreshold
    mdp hhorizon hrounds hepisodes hdelta hdelta_le_one hvisitFloor
    (by norm_num) (by norm_num)
    (normalizedCumulativeInverseSqrtScale_nonneg mdp rounds delta visitFloor)
    (normalizedCumulativeInverseSqrtScale_cover mdp hhorizon hrounds
      hdelta hdelta_le_one hvisitFloor)
    (cumulativeInverseSqrtCalibrationEpisodeThreshold_lt_of_normalizedThreshold
      mdp hhorizon hrounds hdelta hdelta_le_one hvisitFloor hthreshold)

omit [DecidableEq State] [DecidableEq Action]
    [MeasurableSingletonClass State] [MeasurableSingletonClass Action]
    [Nonempty State] [Nonempty Action] in
/-- Explicit expansion of the normalized recommendation-regret bound. -/
theorem normalizedCumulativeInverseSqrtRecommendedExpectedRegretBound_eq
    (mdp : MDP State Action) (episodes rounds : Nat)
    (delta visitFloor : Real) :
    normalizedCumulativeInverseSqrtRecommendedExpectedRegretBound mdp episodes
        rounds delta visitFloor =
      2 * (mdp.horizon : Real) *
        min (rounds : Real)
          (8 * (Fintype.card State : Real) * (mdp.horizon : Real) *
              Real.sqrt (cumulativeInverseSqrtLogFactor mdp rounds delta) /
              Real.sqrt visitFloor * Real.sqrt (rounds : Real) /
            Real.sqrt ((episodes : Real) * visitFloor / 2)) := by
  unfold normalizedCumulativeInverseSqrtRecommendedExpectedRegretBound
  unfold cumulativeInverseSqrtRecommendedExpectedRegretBound
  unfold cumulativeInverseSqrtEnvelopeSumBound
  unfold normalizedCumulativeInverseSqrtScale
  have hinner :
      2 * (4 * (Fintype.card State : Real) * (mdp.horizon : Real) *
            Real.sqrt (cumulativeInverseSqrtLogFactor mdp rounds delta) /
              Real.sqrt visitFloor) * Real.sqrt (rounds : Real) /
          Real.sqrt ((episodes : Real) * visitFloor / 2) =
        8 * (Fintype.card State : Real) * (mdp.horizon : Real) *
            Real.sqrt (cumulativeInverseSqrtLogFactor mdp rounds delta) /
              Real.sqrt visitFloor * Real.sqrt (rounds : Real) /
          Real.sqrt ((episodes : Real) * visitFloor / 2) := by
    ring
  rw [hinner]
  norm_num

end AdaptiveEpisodeBatchSource

namespace AdaptiveCumulativeEmpiricalOptimisticSource

/--
Normalized deterministic-reward endpoint with one episode threshold and no
caller-visible budget or statistical scale.
-/
theorem exploratorySource_trajectoryMeasure_cumulativeInverseSqrtPathSupport_optimism_and_normalizedRecommendedExpectedRegret
    (mdp : MDP State Action) (initialState : Measure State)
    [IsProbabilityMeasure initialState] (episodes rounds : Nat)
    [StandardBorelSpace (EpisodeBatch mdp episodes)]
    [StandardBorelSpace (EpisodeBatchTrajectory mdp episodes)]
    (initialTable : DeterministicMarkovPolicyTable mdp)
    (defaultState : State)
    (explorationRate : NNReal) (hexplorationRate : explorationRate <= 1)
    (support : ExploratoryPathSupport mdp initialState) (visitFloor : Real)
    (hfloor : ExploratoryPathUniformVisitFloor support explorationRate visitFloor)
    (hrewardBound : forall state action, |mdp.reward state action| <= 1)
    (hhorizon : 0 < mdp.horizon) (hrounds : 0 < rounds)
    (hepisodes : 0 < episodes)
    (delta : Real) (hdelta : 0 < delta) (hdelta_le_one : delta <= 1)
    (hvisitFloor : 0 < visitFloor)
    (hthreshold :
      AdaptiveEpisodeBatchSource.normalizedCumulativeInverseSqrtEpisodeThreshold
          mdp rounds delta visitFloor < (episodes : Real)) :
    let countRadius :=
      AdaptiveEpisodeBatchSource.normalizedCumulativeInverseSqrtCountRadius
        mdp rounds delta visitFloor
    let source := exploratorySource mdp initialState episodes initialTable
      defaultState countRadius explorationRate hexplorationRate
    MeasurableSet (source.adaptiveCumulativeCountBadEvent rounds delta) /\
      source.trajectoryMeasure
          (source.adaptiveCumulativeCountBadEvent rounds delta) <=
        ENNReal.ofReal delta /\
      forall trajectory,
        trajectory ∉ source.adaptiveCumulativeCountBadEvent rounds delta ->
        (forall round : Fin rounds, forall state,
          mdp.optimalValueRemaining mdp.horizon le_rfl state <=
            (adaptiveCumulativeEmpiricalOptimisticPlanAt
              trajectory defaultState countRadius round).upperValueRemaining
                mdp.horizon le_rfl state) /\
        adaptiveCumulativeEmpiricalOptimisticRecommendedExpectedRegret
            (initialState := initialState) trajectory defaultState countRadius rounds <=
          AdaptiveEpisodeBatchSource.normalizedCumulativeInverseSqrtRecommendedExpectedRegretBound
            mdp episodes rounds delta visitFloor := by
  let scale :=
    AdaptiveEpisodeBatchSource.normalizedCumulativeInverseSqrtScale
      mdp rounds delta visitFloor
  have hscale : 0 <= scale :=
    AdaptiveEpisodeBatchSource.normalizedCumulativeInverseSqrtScale_nonneg
      mdp rounds delta visitFloor
  have hscaleCover :=
    AdaptiveEpisodeBatchSource.normalizedCumulativeInverseSqrtScale_cover
      mdp hhorizon hrounds hdelta hdelta_le_one hvisitFloor
  have hexactThreshold :=
    AdaptiveEpisodeBatchSource.cumulativeInverseSqrtCalibrationEpisodeThreshold_lt_of_normalizedThreshold
      mdp hhorizon hrounds hdelta hdelta_le_one hvisitFloor hthreshold
  have hparent :=
    exploratorySource_trajectoryMeasure_cumulativeInverseSqrtPathSupport_optimism_and_closedFormRecommendedExpectedRegret
      mdp initialState episodes rounds initialTable defaultState explorationRate
      hexplorationRate support visitFloor hfloor 1 1 scale hrewardBound
      (by norm_num) hscale hhorizon hrounds hepisodes delta hdelta hdelta_le_one
      hvisitFloor hscaleCover hexactThreshold
  simpa [scale,
    AdaptiveEpisodeBatchSource.normalizedCumulativeInverseSqrtCountRadius,
    AdaptiveEpisodeBatchSource.normalizedCumulativeInverseSqrtRecommendedExpectedRegretBound]
    using hparent

end AdaptiveCumulativeEmpiricalOptimisticSource

end BanditRLProof.FiniteHorizonRL
