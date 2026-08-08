import BanditRLProof.RL.FiniteHorizonAdaptiveCumulativeInverseSqrtAverageConsistency

/-!
# Vanishing-delta high-probability average consistency

This module specializes the scheduled average recommendation-regret route to
the confidence budget `delta_n = 1 / (n + 2)`.  Both the failure budget and
the deterministic average-regret certificate tend to zero.

The source-level statements remain a dependent family of finite-window
certificates.  The scheduled episode count, and hence the trajectory sample
space, changes with `n`; no fixed-process convergence-in-probability claim is
made here.
-/

open Filter MeasureTheory Set
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

/-- The confidence budget used at finite window `n`. -/
noncomputable def vanishingAverageConfidenceDelta (n : Nat) : Real :=
  1 / ((n + 2 : Nat) : Real)

/-- The scheduled batch size at finite window `n`, with `n + 1` rounds. -/
noncomputable def vanishingDeltaScheduledEpisodes
    (mdp : MDP State Action) (n : Nat) (visitFloor : Real) : Nat :=
  normalizedCumulativeInverseSqrtScheduledEpisodes mdp (n + 1)
    (vanishingAverageConfidenceDelta n) visitFloor

/-- The finite-window average recommendation-regret certificate. -/
noncomputable def vanishingDeltaScheduledAverageRecommendedExpectedRegretBound
    (mdp : MDP State Action) (n : Nat) (visitFloor : Real) : Real :=
  normalizedCumulativeInverseSqrtAverageRecommendedExpectedRegretBound mdp
    (vanishingDeltaScheduledEpisodes mdp n visitFloor) (n + 1)
    (vanishingAverageConfidenceDelta n) visitFloor

omit [MeasurableSpace State] [MeasurableSpace Action]
    [Fintype State] [Fintype Action]
    [DecidableEq State] [DecidableEq Action]
    [MeasurableSingletonClass State] [MeasurableSingletonClass Action]
    [Nonempty State] [Nonempty Action] in
/-- Every confidence budget in the schedule is strictly positive. -/
theorem vanishingAverageConfidenceDelta_pos (n : Nat) :
    0 < vanishingAverageConfidenceDelta n := by
  unfold vanishingAverageConfidenceDelta
  positivity

omit [MeasurableSpace State] [MeasurableSpace Action]
    [Fintype State] [Fintype Action]
    [DecidableEq State] [DecidableEq Action]
    [MeasurableSingletonClass State] [MeasurableSingletonClass Action]
    [Nonempty State] [Nonempty Action] in
/-- Every confidence budget in the schedule is at most one. -/
theorem vanishingAverageConfidenceDelta_le_one (n : Nat) :
    vanishingAverageConfidenceDelta n <= 1 := by
  unfold vanishingAverageConfidenceDelta
  rw [div_le_one (by positivity : (0 : Real) < ((n + 2 : Nat) : Real))]
  have hn : (0 : Real) <= n := by positivity
  norm_num
  linarith

omit [MeasurableSpace State] [MeasurableSpace Action]
    [Fintype State] [Fintype Action]
    [DecidableEq State] [DecidableEq Action]
    [MeasurableSingletonClass State] [MeasurableSingletonClass Action]
    [Nonempty State] [Nonempty Action] in
/-- The real-valued confidence budget tends to zero. -/
theorem vanishingAverageConfidenceDelta_tendsto_zero :
    Tendsto vanishingAverageConfidenceDelta atTop (nhds 0) := by
  change Tendsto (fun n : Nat => 1 / ((n + 2 : Nat) : Real)) atTop (nhds 0)
  convert
    (tendsto_const_div_atTop_nhds_zero_nat (𝕜 := Real) 1).comp
      (tendsto_add_atTop_nat 2) using 1

omit [MeasurableSpace State] [MeasurableSpace Action]
    [Fintype State] [Fintype Action]
    [DecidableEq State] [DecidableEq Action]
    [MeasurableSingletonClass State] [MeasurableSingletonClass Action]
    [Nonempty State] [Nonempty Action] in
/-- The `ENNReal` failure budget used by measure bounds tends to zero. -/
theorem vanishingAverageConfidenceDelta_ennreal_tendsto_zero :
    Tendsto (fun n => ENNReal.ofReal (vanishingAverageConfidenceDelta n))
      atTop (nhds 0) := by
  simpa using
    (ENNReal.continuous_ofReal.tendsto 0).comp
      vanishingAverageConfidenceDelta_tendsto_zero

/-- The varying-delta finite-window certificate is nonnegative. -/
theorem vanishingDeltaScheduledAverageBound_nonneg
    (mdp : MDP State Action) (hhorizon : 0 < mdp.horizon)
    (n : Nat) {visitFloor : Real} (hvisitFloor : 0 < visitFloor) :
    0 <= vanishingDeltaScheduledAverageRecommendedExpectedRegretBound
      mdp n visitFloor := by
  exact normalizedCumulativeInverseSqrtScheduledAverageBound_nonneg mdp
    hhorizon (by omega) (vanishingAverageConfidenceDelta_pos n)
    (vanishingAverageConfidenceDelta_le_one n) hvisitFloor

/-- The varying-delta certificate is controlled by the same pure rate. -/
theorem vanishingDeltaScheduledAverageBound_le_envelope
    (mdp : MDP State Action) (hhorizon : 0 < mdp.horizon)
    (n : Nat) {visitFloor : Real} (hvisitFloor : 0 < visitFloor) :
    vanishingDeltaScheduledAverageRecommendedExpectedRegretBound
        mdp n visitFloor <=
      normalizedCumulativeInverseSqrtScheduledAverageEnvelope
        mdp (n + 1) visitFloor := by
  exact normalizedCumulativeInverseSqrtScheduledAverageBound_le_envelope mdp
    hhorizon (by omega) (vanishingAverageConfidenceDelta_pos n)
    (vanishingAverageConfidenceDelta_le_one n) hvisitFloor

/-- The varying-delta average recommendation-regret certificate tends to zero. -/
theorem vanishingDeltaScheduledAverageBound_tendsto_zero
    (mdp : MDP State Action) (hhorizon : 0 < mdp.horizon)
    (visitFloor : Real) (hvisitFloor : 0 < visitFloor) :
    Tendsto
      (fun n =>
        vanishingDeltaScheduledAverageRecommendedExpectedRegretBound
          mdp n visitFloor)
      atTop (nhds 0) := by
  apply squeeze_zero
  · intro n
    exact vanishingDeltaScheduledAverageBound_nonneg mdp hhorizon n hvisitFloor
  · intro n
    exact vanishingDeltaScheduledAverageBound_le_envelope mdp hhorizon n hvisitFloor
  · exact normalizedCumulativeInverseSqrtScheduledAverageEnvelope_tendsto_zero
      mdp visitFloor

/-- Failure budget and deterministic certificate jointly tend to `(0, 0)`. -/
theorem vanishingDeltaAndScheduledAverageBound_tendsto_zero
    (mdp : MDP State Action) (hhorizon : 0 < mdp.horizon)
    (visitFloor : Real) (hvisitFloor : 0 < visitFloor) :
    Tendsto
      (fun n =>
        (ENNReal.ofReal (vanishingAverageConfidenceDelta n),
          vanishingDeltaScheduledAverageRecommendedExpectedRegretBound
            mdp n visitFloor))
      atTop (nhds (0, 0)) := by
  rw [nhds_prod_eq]
  exact vanishingAverageConfidenceDelta_ennreal_tendsto_zero.prodMk
    (vanishingDeltaScheduledAverageBound_tendsto_zero
      mdp hhorizon visitFloor hvisitFloor)

end AdaptiveEpisodeBatchSource

namespace AdaptiveCumulativeEmpiricalOptimisticSource

/--
The trajectories whose average recommendation-regret exceeds the
vanishing-delta finite-window certificate.
-/
noncomputable def vanishingDeltaScheduledAverageRegretViolationSet
    (mdp : MDP State Action) (initialState : Measure State)
    [IsProbabilityMeasure initialState]
    (defaultState : State) (n : Nat) (visitFloor : Real) :
    Set
      (EpisodeBatchTrajectory mdp
        (AdaptiveEpisodeBatchSource.vanishingDeltaScheduledEpisodes
          mdp n visitFloor)) :=
  {trajectory |
    AdaptiveEpisodeBatchSource.vanishingDeltaScheduledAverageRecommendedExpectedRegretBound
        mdp n visitFloor <
      adaptiveCumulativeEmpiricalOptimisticAverageRecommendedExpectedRegret
        (initialState := initialState) trajectory defaultState
        (AdaptiveEpisodeBatchSource.normalizedCumulativeInverseSqrtCountRadius
          mdp (n + 1)
            (AdaptiveEpisodeBatchSource.vanishingAverageConfidenceDelta n)
            visitFloor)
        (n + 1)}

/--
At one finite window, the average-regret violation set is contained in the
measurable simultaneous count bad event and inherits its vanishing confidence
budget as an outer-measure bound.  No measurability claim is made for the
violation set itself.  Outside the measurable bad event, optimism and the
explicit average certificate both hold.
-/
theorem exploratorySource_trajectoryMeasure_cumulativeInverseSqrtPathSupport_optimism_and_vanishingDeltaScheduledAverageRecommendedExpectedRegret
    (mdp : MDP State Action) (initialState : Measure State)
    [IsProbabilityMeasure initialState]
    (n : Nat) (visitFloor : Real)
    [StandardBorelSpace
      (EpisodeBatch mdp
        (AdaptiveEpisodeBatchSource.vanishingDeltaScheduledEpisodes
          mdp n visitFloor))]
    [StandardBorelSpace
      (EpisodeBatchTrajectory mdp
        (AdaptiveEpisodeBatchSource.vanishingDeltaScheduledEpisodes
          mdp n visitFloor))]
    (initialTable : DeterministicMarkovPolicyTable mdp)
    (defaultState : State)
    (explorationRate : NNReal) (hexplorationRate : explorationRate <= 1)
    (support : ExploratoryPathSupport mdp initialState)
    (hfloor : ExploratoryPathUniformVisitFloor support explorationRate visitFloor)
    (hrewardBound : forall state action, |mdp.reward state action| <= 1)
    (hhorizon : 0 < mdp.horizon) (hvisitFloor : 0 < visitFloor) :
    let episodes :=
      AdaptiveEpisodeBatchSource.vanishingDeltaScheduledEpisodes
        mdp n visitFloor
    let delta :=
      AdaptiveEpisodeBatchSource.vanishingAverageConfidenceDelta n
    let countRadius :=
      AdaptiveEpisodeBatchSource.normalizedCumulativeInverseSqrtCountRadius
        mdp (n + 1) delta visitFloor
    let source := exploratorySource mdp initialState episodes initialTable
      defaultState countRadius explorationRate hexplorationRate
    let violationSet :=
      vanishingDeltaScheduledAverageRegretViolationSet
        mdp initialState defaultState n visitFloor
    MeasurableSet (source.adaptiveCumulativeCountBadEvent (n + 1) delta) /\
      source.trajectoryMeasure
          (source.adaptiveCumulativeCountBadEvent (n + 1) delta) <=
        ENNReal.ofReal delta /\
      violationSet ⊆ source.adaptiveCumulativeCountBadEvent (n + 1) delta /\
      source.trajectoryMeasure violationSet <= ENNReal.ofReal delta /\
      forall trajectory,
        trajectory ∉ source.adaptiveCumulativeCountBadEvent (n + 1) delta ->
        (forall round : Fin (n + 1), forall state,
          mdp.optimalValueRemaining mdp.horizon le_rfl state <=
            (adaptiveCumulativeEmpiricalOptimisticPlanAt
              trajectory defaultState countRadius round).upperValueRemaining
                mdp.horizon le_rfl state) /\
        adaptiveCumulativeEmpiricalOptimisticAverageRecommendedExpectedRegret
            (initialState := initialState) trajectory defaultState countRadius
            (n + 1) <=
          AdaptiveEpisodeBatchSource.vanishingDeltaScheduledAverageRecommendedExpectedRegretBound
            mdp n visitFloor := by
  let episodes :=
    AdaptiveEpisodeBatchSource.vanishingDeltaScheduledEpisodes
      mdp n visitFloor
  let delta := AdaptiveEpisodeBatchSource.vanishingAverageConfidenceDelta n
  let countRadius :=
    AdaptiveEpisodeBatchSource.normalizedCumulativeInverseSqrtCountRadius
      mdp (n + 1) delta visitFloor
  let source := exploratorySource mdp initialState episodes initialTable
    defaultState countRadius explorationRate hexplorationRate
  let violationSet := vanishingDeltaScheduledAverageRegretViolationSet
    mdp initialState defaultState n visitFloor
  letI : StandardBorelSpace
      (EpisodeBatch mdp
        (AdaptiveEpisodeBatchSource.normalizedCumulativeInverseSqrtScheduledEpisodes
          mdp (n + 1)
            (AdaptiveEpisodeBatchSource.vanishingAverageConfidenceDelta n)
            visitFloor)) := by
    change StandardBorelSpace
      (EpisodeBatch mdp
        (AdaptiveEpisodeBatchSource.vanishingDeltaScheduledEpisodes
          mdp n visitFloor))
    infer_instance
  letI : StandardBorelSpace
      (EpisodeBatchTrajectory mdp
        (AdaptiveEpisodeBatchSource.normalizedCumulativeInverseSqrtScheduledEpisodes
          mdp (n + 1)
            (AdaptiveEpisodeBatchSource.vanishingAverageConfidenceDelta n)
            visitFloor)) := by
    change StandardBorelSpace
      (EpisodeBatchTrajectory mdp
        (AdaptiveEpisodeBatchSource.vanishingDeltaScheduledEpisodes
          mdp n visitFloor))
    infer_instance
  have hterminal :=
    exploratorySource_trajectoryMeasure_cumulativeInverseSqrtPathSupport_optimism_and_scheduledAverageRecommendedExpectedRegret
      mdp initialState (n + 1)
      (AdaptiveEpisodeBatchSource.vanishingAverageConfidenceDelta n)
      visitFloor initialTable defaultState
      explorationRate hexplorationRate support hfloor hrewardBound hhorizon
      (by omega) (AdaptiveEpisodeBatchSource.vanishingAverageConfidenceDelta_pos n)
      (AdaptiveEpisodeBatchSource.vanishingAverageConfidenceDelta_le_one n)
      hvisitFloor
  dsimp only at hterminal
  rcases hterminal with ⟨hmeasurable, hbadTail, houtside⟩
  have hsubset :
      violationSet ⊆ source.adaptiveCumulativeCountBadEvent (n + 1) delta := by
    intro trajectory hviolation
    by_contra houtsideBad
    have hbound := (houtside trajectory houtsideBad).2
    have hviolation' :
        AdaptiveEpisodeBatchSource.vanishingDeltaScheduledAverageRecommendedExpectedRegretBound
            mdp n visitFloor <
          adaptiveCumulativeEmpiricalOptimisticAverageRecommendedExpectedRegret
            (initialState := initialState) trajectory defaultState
            (AdaptiveEpisodeBatchSource.normalizedCumulativeInverseSqrtCountRadius
              mdp (n + 1)
                (AdaptiveEpisodeBatchSource.vanishingAverageConfidenceDelta n)
                visitFloor)
            (n + 1) := by
      exact hviolation
    exact (not_lt_of_ge hbound) hviolation'
  have hviolationTail :
      source.trajectoryMeasure violationSet <= ENNReal.ofReal delta :=
    (measure_mono hsubset).trans hbadTail
  exact ⟨hmeasurable, hbadTail, hsubset, hviolationTail, houtside⟩

/--
Dependent family of all finite-window high-probability certificates.  The two
standard-Borel assumptions are themselves indexed by the changing scheduled
sample space.
-/
theorem exploratorySource_trajectoryMeasure_cumulativeInverseSqrtPathSupport_optimism_and_vanishingDeltaScheduledAverageRecommendedExpectedRegret_allWindows
    (mdp : MDP State Action) (initialState : Measure State)
    [IsProbabilityMeasure initialState]
    (visitFloor : Real)
    (hbatchBorel : forall n, StandardBorelSpace
      (EpisodeBatch mdp
        (AdaptiveEpisodeBatchSource.vanishingDeltaScheduledEpisodes
          mdp n visitFloor)))
    (htrajectoryBorel : forall n, StandardBorelSpace
      (EpisodeBatchTrajectory mdp
        (AdaptiveEpisodeBatchSource.vanishingDeltaScheduledEpisodes
          mdp n visitFloor)))
    (initialTable : DeterministicMarkovPolicyTable mdp)
    (defaultState : State)
    (explorationRate : NNReal) (hexplorationRate : explorationRate <= 1)
    (support : ExploratoryPathSupport mdp initialState)
    (hfloor : ExploratoryPathUniformVisitFloor support explorationRate visitFloor)
    (hrewardBound : forall state action, |mdp.reward state action| <= 1)
    (hhorizon : 0 < mdp.horizon) (hvisitFloor : 0 < visitFloor) :
    forall n,
      letI : StandardBorelSpace
          (EpisodeBatch mdp
            (AdaptiveEpisodeBatchSource.vanishingDeltaScheduledEpisodes
              mdp n visitFloor)) := hbatchBorel n
      letI : StandardBorelSpace
          (EpisodeBatchTrajectory mdp
            (AdaptiveEpisodeBatchSource.vanishingDeltaScheduledEpisodes
              mdp n visitFloor)) := htrajectoryBorel n
      let episodes :=
        AdaptiveEpisodeBatchSource.vanishingDeltaScheduledEpisodes
          mdp n visitFloor
      let delta :=
        AdaptiveEpisodeBatchSource.vanishingAverageConfidenceDelta n
      let countRadius :=
        AdaptiveEpisodeBatchSource.normalizedCumulativeInverseSqrtCountRadius
          mdp (n + 1) delta visitFloor
      let source := exploratorySource mdp initialState episodes initialTable
        defaultState countRadius explorationRate hexplorationRate
      let violationSet :=
        vanishingDeltaScheduledAverageRegretViolationSet
          mdp initialState defaultState n visitFloor
      MeasurableSet (source.adaptiveCumulativeCountBadEvent (n + 1) delta) /\
        source.trajectoryMeasure
            (source.adaptiveCumulativeCountBadEvent (n + 1) delta) <=
          ENNReal.ofReal delta /\
        violationSet ⊆ source.adaptiveCumulativeCountBadEvent (n + 1) delta /\
        source.trajectoryMeasure violationSet <= ENNReal.ofReal delta /\
        forall trajectory,
          trajectory ∉ source.adaptiveCumulativeCountBadEvent (n + 1) delta ->
          (forall round : Fin (n + 1), forall state,
            mdp.optimalValueRemaining mdp.horizon le_rfl state <=
              (adaptiveCumulativeEmpiricalOptimisticPlanAt
                trajectory defaultState countRadius round).upperValueRemaining
                  mdp.horizon le_rfl state) /\
          adaptiveCumulativeEmpiricalOptimisticAverageRecommendedExpectedRegret
              (initialState := initialState) trajectory defaultState countRadius
              (n + 1) <=
            AdaptiveEpisodeBatchSource.vanishingDeltaScheduledAverageRecommendedExpectedRegretBound
              mdp n visitFloor := by
  intro n
  letI := hbatchBorel n
  letI := htrajectoryBorel n
  exact
    exploratorySource_trajectoryMeasure_cumulativeInverseSqrtPathSupport_optimism_and_vanishingDeltaScheduledAverageRecommendedExpectedRegret
      mdp initialState n visitFloor initialTable defaultState explorationRate
      hexplorationRate support hfloor hrewardBound hhorizon hvisitFloor

end AdaptiveCumulativeEmpiricalOptimisticSource

end BanditRLProof.FiniteHorizonRL
