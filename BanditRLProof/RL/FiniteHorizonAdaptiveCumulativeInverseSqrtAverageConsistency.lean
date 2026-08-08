import BanditRLProof.RL.FiniteHorizonAdaptiveCumulativeInverseSqrtAverageRate

/-!
# Scheduled average consistency for adaptive cumulative inverse-square-root recommendations

This module chooses an explicit natural number of exploratory episodes per
batch.  The schedule simultaneously clears the normalized calibration
threshold and places the logarithmic factor below one batch's visit mass.
The resulting scalar average recommendation-regret bound is at most a fixed
constant times `1 / sqrt(rounds)` and therefore tends to zero.

The source theorem remains a separate finite-window statement because the
episode-batch trajectory type changes with the scheduled batch size.
-/

open Filter MeasureTheory
open scoped ENNReal ProbabilityTheory Topology

universe u v

namespace BanditRLProof.FiniteHorizonRL

variable {State : Type u} {Action : Type v}
    [MeasurableSpace State] [MeasurableSpace Action]
    [Fintype State] [Fintype Action]
    [DecidableEq State] [DecidableEq Action]
    [MeasurableSingletonClass State] [MeasurableSingletonClass Action]
    [Nonempty State] [Nonempty Action]

namespace AdaptiveEpisodeBatchSource

/--
Real-valued batch-size target that clears both normalized calibration and the
one-batch logarithmic visit-mass requirement.
-/
noncomputable def normalizedCumulativeInverseSqrtScheduledEpisodeThreshold
    (mdp : MDP State Action) (rounds : Nat)
    (delta visitFloor : Real) : Real :=
  max
    (normalizedCumulativeInverseSqrtEpisodeThreshold mdp rounds delta visitFloor)
    (2 * cumulativeInverseSqrtLogFactor mdp rounds delta / visitFloor)

/-- Explicit positive natural batch size associated with the scheduled target. -/
noncomputable def normalizedCumulativeInverseSqrtScheduledEpisodes
    (mdp : MDP State Action) (rounds : Nat)
    (delta visitFloor : Real) : Nat :=
  Nat.ceil
      (normalizedCumulativeInverseSqrtScheduledEpisodeThreshold
        mdp rounds delta visitFloor) +
    1

/-- The inverse-square-root envelope for the scheduled average bound. -/
noncomputable def normalizedCumulativeInverseSqrtScheduledAverageEnvelope
    (mdp : MDP State Action) (rounds : Nat) (visitFloor : Real) : Real :=
  16 * (Fintype.card State : Real) * (mdp.horizon : Real) ^ 2 /
      Real.sqrt visitFloor /
    Real.sqrt (rounds : Real)

/-- The valid global confidence budget makes the shared logarithm strict. -/
theorem cumulativeInverseSqrtLogFactor_pos
    (mdp : MDP State Action) {rounds : Nat}
    (hhorizon : 0 < mdp.horizon) (hrounds : 0 < rounds)
    {delta : Real} (hdelta : 0 < delta) (hdelta_le_one : delta <= 1) :
    0 < cumulativeInverseSqrtLogFactor mdp rounds delta := by
  letI : Nonempty (Fin rounds × CountCoordinate mdp) :=
    cumulativeCountIndex_nonempty hhorizon hrounds
  have hlocalPos : 0 < cumulativeCountLocalDelta mdp rounds delta :=
    cumulativeCountLocalDelta_pos inferInstance hdelta
  have hlocalLeOne : cumulativeCountLocalDelta mdp rounds delta <= 1 :=
    cumulativeCountLocalDelta_le_one inferInstance hdelta hdelta_le_one
  unfold cumulativeInverseSqrtLogFactor
  apply Real.log_pos
  rw [one_lt_div₀ hlocalPos]
  linarith

/-- The scheduled real-valued target is nonnegative under valid parameters. -/
theorem normalizedCumulativeInverseSqrtScheduledEpisodeThreshold_nonneg
    (mdp : MDP State Action) {rounds : Nat}
    (hhorizon : 0 < mdp.horizon) (hrounds : 0 < rounds)
    {delta visitFloor : Real} (hdelta : 0 < delta)
    (hdelta_le_one : delta <= 1) (hvisitFloor : 0 < visitFloor) :
    0 <= normalizedCumulativeInverseSqrtScheduledEpisodeThreshold
      mdp rounds delta visitFloor := by
  have hlog : 0 <= cumulativeInverseSqrtLogFactor mdp rounds delta :=
    (cumulativeInverseSqrtLogFactor_pos mdp hhorizon hrounds
      hdelta hdelta_le_one).le
  unfold normalizedCumulativeInverseSqrtScheduledEpisodeThreshold
  apply le_trans ?_ (le_max_left _ _)
  unfold normalizedCumulativeInverseSqrtEpisodeThreshold
  positivity

omit [DecidableEq State] [DecidableEq Action]
    [MeasurableSingletonClass State] [MeasurableSingletonClass Action]
    [Nonempty State] [Nonempty Action] in
/-- Every scheduled batch size is positive. -/
theorem normalizedCumulativeInverseSqrtScheduledEpisodes_pos
    (mdp : MDP State Action) (rounds : Nat)
    (delta visitFloor : Real) :
    0 < normalizedCumulativeInverseSqrtScheduledEpisodes
      mdp rounds delta visitFloor := by
  unfold normalizedCumulativeInverseSqrtScheduledEpisodes
  omega

omit [DecidableEq State] [DecidableEq Action]
    [MeasurableSingletonClass State] [MeasurableSingletonClass Action]
    [Nonempty State] [Nonempty Action] in
/-- The real-valued target is strictly below the scheduled natural batch size. -/
theorem normalizedCumulativeInverseSqrtScheduledEpisodeThreshold_lt_episodes
    (mdp : MDP State Action) (rounds : Nat)
    (delta visitFloor : Real) :
    normalizedCumulativeInverseSqrtScheduledEpisodeThreshold
        mdp rounds delta visitFloor <
      (normalizedCumulativeInverseSqrtScheduledEpisodes
        mdp rounds delta visitFloor : Real) := by
  have hceil :
      normalizedCumulativeInverseSqrtScheduledEpisodeThreshold
          mdp rounds delta visitFloor <=
        (Nat.ceil
          (normalizedCumulativeInverseSqrtScheduledEpisodeThreshold
            mdp rounds delta visitFloor) : Real) :=
    Nat.le_ceil _
  unfold normalizedCumulativeInverseSqrtScheduledEpisodes
  push_cast
  linarith

omit [DecidableEq State] [DecidableEq Action]
    [MeasurableSingletonClass State] [MeasurableSingletonClass Action]
    [Nonempty State] [Nonempty Action] in
/-- The schedule strictly clears the parent normalized calibration threshold. -/
theorem normalizedCumulativeInverseSqrtEpisodeThreshold_lt_scheduledEpisodes
    (mdp : MDP State Action) (rounds : Nat)
    (delta visitFloor : Real) :
    normalizedCumulativeInverseSqrtEpisodeThreshold
        mdp rounds delta visitFloor <
      (normalizedCumulativeInverseSqrtScheduledEpisodes
        mdp rounds delta visitFloor : Real) :=
  lt_of_le_of_lt
    (le_max_left _ _)
    (normalizedCumulativeInverseSqrtScheduledEpisodeThreshold_lt_episodes
      mdp rounds delta visitFloor)

omit [DecidableEq State] [DecidableEq Action]
    [MeasurableSingletonClass State] [MeasurableSingletonClass Action]
    [Nonempty State] [Nonempty Action] in
/-- One scheduled batch has strictly more visit mass than the log factor. -/
theorem cumulativeInverseSqrtLogFactor_lt_scheduledEpisodeVisitMass
    (mdp : MDP State Action) (rounds : Nat)
    (delta : Real) {visitFloor : Real} (hvisitFloor : 0 < visitFloor) :
    cumulativeInverseSqrtLogFactor mdp rounds delta <
      (normalizedCumulativeInverseSqrtScheduledEpisodes
          mdp rounds delta visitFloor : Real) * visitFloor / 2 := by
  have hschedule :
      2 * cumulativeInverseSqrtLogFactor mdp rounds delta / visitFloor <
        (normalizedCumulativeInverseSqrtScheduledEpisodes
          mdp rounds delta visitFloor : Real) :=
    lt_of_le_of_lt (le_max_right _ _)
      (normalizedCumulativeInverseSqrtScheduledEpisodeThreshold_lt_episodes
        mdp rounds delta visitFloor)
  have hmul := (div_lt_iff₀ hvisitFloor).1 hschedule
  linarith

/-- The normalized scheduled average bound is nonnegative. -/
theorem normalizedCumulativeInverseSqrtScheduledAverageBound_nonneg
    (mdp : MDP State Action) {rounds : Nat}
    (hhorizon : 0 < mdp.horizon) (hrounds : 0 < rounds)
    {delta visitFloor : Real} (hdelta : 0 < delta)
    (hdelta_le_one : delta <= 1) (hvisitFloor : 0 < visitFloor) :
    0 <= normalizedCumulativeInverseSqrtAverageRecommendedExpectedRegretBound
      mdp
      (normalizedCumulativeInverseSqrtScheduledEpisodes
        mdp rounds delta visitFloor)
      rounds delta visitFloor := by
  rw [normalizedCumulativeInverseSqrtAverageRecommendedExpectedRegretBound_eq_totalEpisodes mdp
    (normalizedCumulativeInverseSqrtScheduledEpisodes_pos
      mdp rounds delta visitFloor) hrounds delta hvisitFloor]
  have hlog : 0 <= cumulativeInverseSqrtLogFactor mdp rounds delta :=
    (cumulativeInverseSqrtLogFactor_pos mdp hhorizon hrounds
      hdelta hdelta_le_one).le
  positivity

/-- The scheduled average bound is controlled by a pure inverse-square-root rate. -/
theorem normalizedCumulativeInverseSqrtScheduledAverageBound_le_envelope
    (mdp : MDP State Action) {rounds : Nat}
    (hhorizon : 0 < mdp.horizon) (hrounds : 0 < rounds)
    {delta visitFloor : Real} (hdelta : 0 < delta)
    (hdelta_le_one : delta <= 1) (hvisitFloor : 0 < visitFloor) :
    normalizedCumulativeInverseSqrtAverageRecommendedExpectedRegretBound
        mdp
        (normalizedCumulativeInverseSqrtScheduledEpisodes
          mdp rounds delta visitFloor)
        rounds delta visitFloor <=
      normalizedCumulativeInverseSqrtScheduledAverageEnvelope
        mdp rounds visitFloor := by
  let episodes := normalizedCumulativeInverseSqrtScheduledEpisodes
    mdp rounds delta visitFloor
  have hepisodes : 0 < episodes :=
    normalizedCumulativeInverseSqrtScheduledEpisodes_pos
      mdp rounds delta visitFloor
  have hepisodesReal : 0 < (episodes : Real) := by exact_mod_cast hepisodes
  have hroundsReal : 0 < (rounds : Real) := by exact_mod_cast hrounds
  have hlog : 0 < cumulativeInverseSqrtLogFactor mdp rounds delta :=
    cumulativeInverseSqrtLogFactor_pos mdp hhorizon hrounds
      hdelta hdelta_le_one
  have hbatchMass : 0 < (episodes : Real) * visitFloor / 2 := by positivity
  have hlogLeBatch :
      cumulativeInverseSqrtLogFactor mdp rounds delta <=
        (episodes : Real) * visitFloor / 2 := by
    exact (cumulativeInverseSqrtLogFactor_lt_scheduledEpisodeVisitMass
      mdp rounds delta hvisitFloor).le
  have hsqrtLogLeBatch :
      Real.sqrt (cumulativeInverseSqrtLogFactor mdp rounds delta) <=
        Real.sqrt ((episodes : Real) * visitFloor / 2) :=
    Real.sqrt_le_sqrt hlogLeBatch
  have hsqrtVisit : 0 < Real.sqrt visitFloor := Real.sqrt_pos.2 hvisitFloor
  have hsqrtBatch : 0 < Real.sqrt ((episodes : Real) * visitFloor / 2) :=
    Real.sqrt_pos.2 hbatchMass
  have hsqrtRounds : 0 < Real.sqrt (rounds : Real) :=
    Real.sqrt_pos.2 hroundsReal
  have htotalMass :
      (((cumulativeExploratoryEpisodeCount episodes rounds : Nat) : Real) *
          visitFloor / 2) =
        ((episodes : Real) * visitFloor / 2) * (rounds : Real) := by
    unfold cumulativeExploratoryEpisodeCount
    push_cast
    ring
  have hsqrtTotalMass :
      Real.sqrt
          (((cumulativeExploratoryEpisodeCount episodes rounds : Nat) : Real) *
            visitFloor / 2) =
        Real.sqrt ((episodes : Real) * visitFloor / 2) *
          Real.sqrt (rounds : Real) := by
    rw [htotalMass, Real.sqrt_mul hbatchMass.le]
  have hinner :
      8 * (Fintype.card State : Real) * (mdp.horizon : Real) *
              Real.sqrt (cumulativeInverseSqrtLogFactor mdp rounds delta) /
              Real.sqrt visitFloor /
            (Real.sqrt ((episodes : Real) * visitFloor / 2) *
              Real.sqrt (rounds : Real)) <=
        8 * (Fintype.card State : Real) * (mdp.horizon : Real) /
            Real.sqrt visitFloor /
          Real.sqrt (rounds : Real) := by
    calc
      8 * (Fintype.card State : Real) * (mdp.horizon : Real) *
              Real.sqrt (cumulativeInverseSqrtLogFactor mdp rounds delta) /
              Real.sqrt visitFloor /
            (Real.sqrt ((episodes : Real) * visitFloor / 2) *
              Real.sqrt (rounds : Real)) =
          (8 * (Fintype.card State : Real) * (mdp.horizon : Real) /
              Real.sqrt visitFloor /
            Real.sqrt (rounds : Real)) *
          (Real.sqrt (cumulativeInverseSqrtLogFactor mdp rounds delta) /
            Real.sqrt ((episodes : Real) * visitFloor / 2)) := by
              field_simp [ne_of_gt hsqrtVisit, ne_of_gt hsqrtBatch,
                ne_of_gt hsqrtRounds]
      _ <= (8 * (Fintype.card State : Real) * (mdp.horizon : Real) /
              Real.sqrt visitFloor /
            Real.sqrt (rounds : Real)) * 1 := by
              exact mul_le_mul_of_nonneg_left
                ((div_le_one hsqrtBatch).2 hsqrtLogLeBatch) (by positivity)
      _ = 8 * (Fintype.card State : Real) * (mdp.horizon : Real) /
              Real.sqrt visitFloor /
            Real.sqrt (rounds : Real) := by ring
  rw [show normalizedCumulativeInverseSqrtScheduledEpisodes
      mdp rounds delta visitFloor = episodes from rfl]
  rw [normalizedCumulativeInverseSqrtAverageRecommendedExpectedRegretBound_eq_totalEpisodes mdp
    hepisodes hrounds delta hvisitFloor]
  rw [hsqrtTotalMass]
  calc
    2 * (mdp.horizon : Real) *
          min 1
            (8 * (Fintype.card State : Real) * (mdp.horizon : Real) *
                Real.sqrt (cumulativeInverseSqrtLogFactor mdp rounds delta) /
                Real.sqrt visitFloor /
              (Real.sqrt ((episodes : Real) * visitFloor / 2) *
                Real.sqrt (rounds : Real))) <=
        2 * (mdp.horizon : Real) *
          (8 * (Fintype.card State : Real) * (mdp.horizon : Real) *
              Real.sqrt (cumulativeInverseSqrtLogFactor mdp rounds delta) /
              Real.sqrt visitFloor /
            (Real.sqrt ((episodes : Real) * visitFloor / 2) *
              Real.sqrt (rounds : Real))) := by
            exact mul_le_mul_of_nonneg_left (min_le_right _ _) (by positivity)
    _ <= 2 * (mdp.horizon : Real) *
          (8 * (Fintype.card State : Real) * (mdp.horizon : Real) /
              Real.sqrt visitFloor /
            Real.sqrt (rounds : Real)) :=
      mul_le_mul_of_nonneg_left hinner (by positivity)
    _ = normalizedCumulativeInverseSqrtScheduledAverageEnvelope
          mdp rounds visitFloor := by
      unfold normalizedCumulativeInverseSqrtScheduledAverageEnvelope
      ring

omit [DecidableEq State] [DecidableEq Action]
    [MeasurableSingletonClass State] [MeasurableSingletonClass Action]
    [Nonempty State] [Nonempty Action] in
/-- The deterministic inverse-square-root envelope tends to zero. -/
theorem normalizedCumulativeInverseSqrtScheduledAverageEnvelope_tendsto_zero
    (mdp : MDP State Action) (visitFloor : Real) :
    Tendsto
      (fun n : Nat =>
        normalizedCumulativeInverseSqrtScheduledAverageEnvelope
          mdp (n + 1) visitFloor)
      atTop (nhds 0) := by
  have hrounds :
      Tendsto (fun n : Nat => (((n + 1 : Nat) : Real))) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1)
  have hsqrt :
      Tendsto (fun n : Nat => Real.sqrt (((n + 1 : Nat) : Real)))
        atTop atTop :=
    Real.tendsto_sqrt_atTop.comp hrounds
  simpa [normalizedCumulativeInverseSqrtScheduledAverageEnvelope] using
    (tendsto_const_nhds.div_atTop hsqrt)

/-- The scheduled scalar average recommendation-regret bound tends to zero. -/
theorem normalizedCumulativeInverseSqrtScheduledAverageBound_tendsto_zero
    (mdp : MDP State Action) (hhorizon : 0 < mdp.horizon)
    (delta visitFloor : Real) (hdelta : 0 < delta)
    (hdelta_le_one : delta <= 1) (hvisitFloor : 0 < visitFloor) :
    Tendsto
      (fun n : Nat =>
        normalizedCumulativeInverseSqrtAverageRecommendedExpectedRegretBound
          mdp
          (normalizedCumulativeInverseSqrtScheduledEpisodes
            mdp (n + 1) delta visitFloor)
          (n + 1) delta visitFloor)
      atTop (nhds 0) := by
  apply squeeze_zero
  · intro n
    exact normalizedCumulativeInverseSqrtScheduledAverageBound_nonneg
      mdp hhorizon (by omega) hdelta hdelta_le_one hvisitFloor
  · intro n
    exact normalizedCumulativeInverseSqrtScheduledAverageBound_le_envelope
      mdp hhorizon (by omega) hdelta hdelta_le_one hvisitFloor
  · exact normalizedCumulativeInverseSqrtScheduledAverageEnvelope_tendsto_zero
      mdp visitFloor

end AdaptiveEpisodeBatchSource

namespace AdaptiveCumulativeEmpiricalOptimisticSource

/--
At every positive finite window, the explicit schedule discharges calibration
and preserves the parent's measurable event, delta tail, optimism, and average
recommended-policy expected-regret conclusion.
-/
theorem exploratorySource_trajectoryMeasure_cumulativeInverseSqrtPathSupport_optimism_and_scheduledAverageRecommendedExpectedRegret
    (mdp : MDP State Action) (initialState : Measure State)
    [IsProbabilityMeasure initialState]
    (rounds : Nat) (delta visitFloor : Real)
    [StandardBorelSpace
      (EpisodeBatch mdp
        (AdaptiveEpisodeBatchSource.normalizedCumulativeInverseSqrtScheduledEpisodes
          mdp rounds delta visitFloor))]
    [StandardBorelSpace
      (EpisodeBatchTrajectory mdp
        (AdaptiveEpisodeBatchSource.normalizedCumulativeInverseSqrtScheduledEpisodes
          mdp rounds delta visitFloor))]
    (initialTable : DeterministicMarkovPolicyTable mdp)
    (defaultState : State)
    (explorationRate : NNReal) (hexplorationRate : explorationRate <= 1)
    (support : ExploratoryPathSupport mdp initialState)
    (hfloor : ExploratoryPathUniformVisitFloor support explorationRate visitFloor)
    (hrewardBound : forall state action, |mdp.reward state action| <= 1)
    (hhorizon : 0 < mdp.horizon) (hrounds : 0 < rounds)
    (hdelta : 0 < delta) (hdelta_le_one : delta <= 1)
    (hvisitFloor : 0 < visitFloor) :
    let episodes :=
      AdaptiveEpisodeBatchSource.normalizedCumulativeInverseSqrtScheduledEpisodes
        mdp rounds delta visitFloor
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
        adaptiveCumulativeEmpiricalOptimisticAverageRecommendedExpectedRegret
            (initialState := initialState) trajectory defaultState countRadius rounds <=
          AdaptiveEpisodeBatchSource.normalizedCumulativeInverseSqrtAverageRecommendedExpectedRegretBound
            mdp episodes rounds delta visitFloor := by
  exact
    exploratorySource_trajectoryMeasure_cumulativeInverseSqrtPathSupport_optimism_and_normalizedAverageRecommendedExpectedRegret
      mdp initialState
      (AdaptiveEpisodeBatchSource.normalizedCumulativeInverseSqrtScheduledEpisodes
        mdp rounds delta visitFloor)
      rounds initialTable defaultState explorationRate hexplorationRate support
      visitFloor hfloor hrewardBound hhorizon hrounds
      (AdaptiveEpisodeBatchSource.normalizedCumulativeInverseSqrtScheduledEpisodes_pos
        mdp rounds delta visitFloor)
      delta hdelta hdelta_le_one hvisitFloor
      (AdaptiveEpisodeBatchSource.normalizedCumulativeInverseSqrtEpisodeThreshold_lt_scheduledEpisodes
        mdp rounds delta visitFloor)

end AdaptiveCumulativeEmpiricalOptimisticSource

end BanditRLProof.FiniteHorizonRL
