import BanditRLProof.RL.FiniteHorizonAdaptiveCumulativeInverseSqrtNormalizedRate

/-!
# Average adaptive cumulative inverse-square-root rate

This module divides the normalized cumulative recommendation-regret endpoint
by a positive number of recommendation rounds.  It rewrites the statistical
term using the total number of exploratory episodes across all batches while
preserving the parent event, probability tail, and optimism statement.
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

/-- Total exploratory episodes in `rounds` batches of size `episodes`. -/
def cumulativeExploratoryEpisodeCount (episodes rounds : Nat) : Nat :=
  episodes * rounds

/-- The normalized cumulative recommendation-regret bound per recommendation. -/
noncomputable def normalizedCumulativeInverseSqrtAverageRecommendedExpectedRegretBound
    (mdp : MDP State Action) (episodes rounds : Nat)
    (delta visitFloor : Real) : Real :=
  normalizedCumulativeInverseSqrtRecommendedExpectedRegretBound
      mdp episodes rounds delta visitFloor /
    (rounds : Real)

omit [DecidableEq State] [DecidableEq Action]
    [MeasurableSingletonClass State] [MeasurableSingletonClass Action]
    [Nonempty State] [Nonempty Action] in
/--
The normalized average bound exposes the square-root rate in the total number
of exploratory episodes.
-/
theorem normalizedCumulativeInverseSqrtAverageRecommendedExpectedRegretBound_eq_totalEpisodes
    (mdp : MDP State Action) {episodes rounds : Nat}
    (hepisodes : 0 < episodes) (hrounds : 0 < rounds)
    (delta : Real) {visitFloor : Real} (hvisitFloor : 0 < visitFloor) :
    normalizedCumulativeInverseSqrtAverageRecommendedExpectedRegretBound
        mdp episodes rounds delta visitFloor =
      2 * (mdp.horizon : Real) *
        min 1
          (8 * (Fintype.card State : Real) * (mdp.horizon : Real) *
              Real.sqrt (cumulativeInverseSqrtLogFactor mdp rounds delta) /
              Real.sqrt visitFloor /
            Real.sqrt
              ((cumulativeExploratoryEpisodeCount episodes rounds : Nat) *
                visitFloor / 2)) := by
  have hepisodesReal : 0 < (episodes : Real) := by exact_mod_cast hepisodes
  have hroundsReal : 0 < (rounds : Real) := by exact_mod_cast hrounds
  have hbatchMass : 0 < (episodes : Real) * visitFloor / 2 := by positivity
  have hsqrtRounds : 0 < Real.sqrt (rounds : Real) :=
    Real.sqrt_pos.2 hroundsReal
  have hsqrtBatchMass : 0 <
      Real.sqrt ((episodes : Real) * visitFloor / 2) :=
    Real.sqrt_pos.2 hbatchMass
  have htotalMass :
      ((cumulativeExploratoryEpisodeCount episodes rounds : Nat) : Real) *
            visitFloor / 2 =
        (rounds : Real) * ((episodes : Real) * visitFloor / 2) := by
    unfold cumulativeExploratoryEpisodeCount
    push_cast
    ring
  have hsqrtTotalMass :
      Real.sqrt
          (((cumulativeExploratoryEpisodeCount episodes rounds : Nat) : Real) *
            visitFloor / 2) =
        Real.sqrt (rounds : Real) *
          Real.sqrt ((episodes : Real) * visitFloor / 2) := by
    rw [htotalMass, Real.sqrt_mul hroundsReal.le]
  have hstatistical :
      (8 * (Fintype.card State : Real) * (mdp.horizon : Real) *
              Real.sqrt (cumulativeInverseSqrtLogFactor mdp rounds delta) /
              Real.sqrt visitFloor * Real.sqrt (rounds : Real) /
            Real.sqrt ((episodes : Real) * visitFloor / 2)) /
          (rounds : Real) =
        8 * (Fintype.card State : Real) * (mdp.horizon : Real) *
              Real.sqrt (cumulativeInverseSqrtLogFactor mdp rounds delta) /
              Real.sqrt visitFloor /
            Real.sqrt
              (((cumulativeExploratoryEpisodeCount episodes rounds : Nat) : Real) *
                visitFloor / 2) := by
    rw [hsqrtTotalMass]
    have hsqrtRoundsNe : Real.sqrt (rounds : Real) ≠ 0 := ne_of_gt hsqrtRounds
    have hsqrtBatchMassNe :
        Real.sqrt ((episodes : Real) * visitFloor / 2) ≠ 0 :=
      ne_of_gt hsqrtBatchMass
    field_simp [hsqrtRoundsNe, hsqrtBatchMassNe]
    ring_nf
    rw [Real.sq_sqrt hroundsReal.le]
  have hmin (x : Real) :
      min (rounds : Real) x / (rounds : Real) =
        min 1 (x / (rounds : Real)) := by
    rw [← min_div_div_right hroundsReal.le]
    rw [div_self hroundsReal.ne']
  unfold normalizedCumulativeInverseSqrtAverageRecommendedExpectedRegretBound
  rw [normalizedCumulativeInverseSqrtRecommendedExpectedRegretBound_eq]
  rw [mul_div_assoc]
  rw [hmin]
  rw [hstatistical]

end AdaptiveEpisodeBatchSource

/-- Average expected regret of the cumulative empirical recommendations. -/
noncomputable def adaptiveCumulativeEmpiricalOptimisticAverageRecommendedExpectedRegret
    {mdp : MDP State Action} {initialState : Measure State}
    [IsProbabilityMeasure initialState] {episodes : Nat}
    (trajectory : EpisodeBatchTrajectory mdp episodes)
    (defaultState : State) (countRadius : TransitionCountRadius)
    (rounds : Nat) : Real :=
  adaptiveCumulativeEmpiricalOptimisticRecommendedExpectedRegret
      (initialState := initialState) trajectory defaultState countRadius rounds /
    (rounds : Real)

namespace AdaptiveCumulativeEmpiricalOptimisticSource

/--
Normalized average-recommendation endpoint expressed through all exploratory
episodes, with the exact parent event and optimism conclusion unchanged.
-/
theorem exploratorySource_trajectoryMeasure_cumulativeInverseSqrtPathSupport_optimism_and_normalizedAverageRecommendedExpectedRegret
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
        adaptiveCumulativeEmpiricalOptimisticAverageRecommendedExpectedRegret
            (initialState := initialState) trajectory defaultState countRadius rounds <=
          AdaptiveEpisodeBatchSource.normalizedCumulativeInverseSqrtAverageRecommendedExpectedRegretBound
            mdp episodes rounds delta visitFloor := by
  have hparent :=
    exploratorySource_trajectoryMeasure_cumulativeInverseSqrtPathSupport_optimism_and_normalizedRecommendedExpectedRegret
      mdp initialState episodes rounds initialTable defaultState explorationRate
      hexplorationRate support visitFloor hfloor hrewardBound hhorizon hrounds
      hepisodes delta hdelta hdelta_le_one hvisitFloor hthreshold
  refine ⟨hparent.1, hparent.2.1, ?_⟩
  intro trajectory htrajectory
  refine ⟨(hparent.2.2 trajectory htrajectory).1, ?_⟩
  unfold adaptiveCumulativeEmpiricalOptimisticAverageRecommendedExpectedRegret
  unfold AdaptiveEpisodeBatchSource.normalizedCumulativeInverseSqrtAverageRecommendedExpectedRegretBound
  exact (div_le_div_iff_of_pos_right (by exact_mod_cast hrounds)).2
    (hparent.2.2 trajectory htrajectory).2

end AdaptiveCumulativeEmpiricalOptimisticSource

end BanditRLProof.FiniteHorizonRL
