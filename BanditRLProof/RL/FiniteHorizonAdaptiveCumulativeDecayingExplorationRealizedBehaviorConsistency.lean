import BanditRLProof.RL.FiniteHorizonAdaptiveCumulativeRealizedBehaviorRegret

/-!
# Decaying-exploration realized behavior consistency

This module closes the scalar asymptotic boundary left by the finite-window
realized-regret transport.  The coarse whole-batch return proxy simplifies
exactly, so the scheduled normalized return radius is bounded by
`2 * horizon / (n + 2)` and tends to zero independently of the scheduled batch
size.  Adding this radius to the compiled exploratory-behavior expected-regret
certificate yields a realized certificate tending to zero, while the union of
the count and return events has a two-share failure budget tending to zero.

The terminal theorem is a dependent family of finite-window certificates.  Its
sample space and trajectory measure may change with `n`; it does not claim one
common process, convergence in probability, an almost-sure result, or an
anytime theorem.
-/

open MeasureTheory Filter
open scoped ENNReal NNReal Topology

namespace BanditRLProof.FiniteHorizonRL

universe u v

variable {State : Type u} {Action : Type v}
    [MeasurableSpace State] [MeasurableSpace Action]
    [Fintype State] [Fintype Action]
    [DecidableEq State] [DecidableEq Action]
    [MeasurableSingletonClass State] [MeasurableSingletonClass Action]
    [Nonempty State] [Nonempty Action]

namespace MarkovPolicy

omit [DecidableEq State] [DecidableEq Action]
    [MeasurableSingletonClass State] [MeasurableSingletonClass Action]
    [Nonempty State] [Nonempty Action] in
/-- The coarse bounded-return proxy is exactly the square of the batch range. -/
theorem batchReturnVarianceProxy_coe
    (mdp : MDP State Action) (episodes : Nat) :
    ((batchReturnVarianceProxy mdp episodes : NNReal) : Real) =
      ((episodes : Real) * (mdp.horizon : Real)) ^ 2 := by
  simp [batchReturnVarianceProxy, Concentration.intervalVarianceProxy,
    Real.norm_eq_abs]
  rw [abs_of_nonneg (by positivity)]
  ring

end MarkovPolicy

namespace AdaptiveEpisodeBatchSource

omit [DecidableEq State] [DecidableEq Action]
    [MeasurableSingletonClass State] [MeasurableSingletonClass Action]
    [Nonempty State] [Nonempty Action] in
/-- The successor-return proxy contains exactly `rounds` nonzero batch terms. -/
theorem cumulativeSuccessorReturnVarianceProxy_coe
    (mdp : MDP State Action) (episodes rounds : Nat) :
    ((cumulativeSuccessorReturnVarianceProxy mdp episodes rounds : NNReal) : Real) =
      (rounds : Real) *
        ((episodes : Real) * (mdp.horizon : Real)) ^ 2 := by
  rw [cumulativeSuccessorReturnVarianceProxy]
  induction rounds with
  | zero => simp
  | succ rounds ih =>
      rw [Nat.cast_succ]
      rw [Finset.sum_range_succ, NNReal.coe_add, ih]
      simp only [MarkovPolicy.batchReturnVarianceProxy,
        Concentration.intervalVarianceProxy, NNReal.coe_pow, NNReal.coe_div,
        coe_nnnorm]
      norm_num
      rw [abs_of_nonneg (by positivity)]
      ring

/-- Return-deviation radius after normalization by all successor episodes. -/
noncomputable def normalizedSuccessorReturnConfidenceRadius
    (mdp : MDP State Action) (episodes rounds : Nat) (delta : Real) : Real :=
  Concentration.subGaussianSumConfidenceRadius
      (cumulativeSuccessorReturnVarianceProxy mdp episodes rounds) delta /
    ((episodes : Real) * (rounds : Real))

omit [DecidableEq State] [DecidableEq Action]
    [MeasurableSingletonClass State] [MeasurableSingletonClass Action]
    [Nonempty State] [Nonempty Action] in
theorem normalizedSuccessorReturnConfidenceRadius_nonneg
    (mdp : MDP State Action) (episodes rounds : Nat) (delta : Real) :
    0 <= normalizedSuccessorReturnConfidenceRadius
      mdp episodes rounds delta := by
  unfold normalizedSuccessorReturnConfidenceRadius
  exact div_nonneg
    (Concentration.subGaussianSumConfidenceRadius_nonneg _ _)
    (mul_nonneg (by positivity) (by positivity))

omit [DecidableEq State] [DecidableEq Action]
    [MeasurableSingletonClass State] [MeasurableSingletonClass Action]
    [Nonempty State] [Nonempty Action] in
/-- The scheduled batch size cancels exactly from the normalized radius. -/
theorem normalizedSuccessorReturnConfidenceRadius_eq
    (mdp : MDP State Action) (episodes rounds : Nat) (delta : Real)
    (hepisodes : 0 < episodes) (hrounds : 0 < rounds)
    (hdelta : 0 < delta) (hdelta_le_one : delta <= 1) :
    normalizedSuccessorReturnConfidenceRadius mdp episodes rounds delta =
      (mdp.horizon : Real) *
        Real.sqrt (2 * Real.log (2 / delta) / (rounds : Real)) := by
  have hepisodesReal : 0 < (episodes : Real) := by exact_mod_cast hepisodes
  have hroundsReal : 0 < (rounds : Real) := by exact_mod_cast hrounds
  have hlog : 0 <= Real.log (2 / delta) := by
    apply Real.log_nonneg
    rw [le_div_iff₀ hdelta]
    linarith
  have hradiusSq :=
    Concentration.subGaussianSumConfidenceRadius_sq
      (cumulativeSuccessorReturnVarianceProxy mdp episodes rounds)
      delta hdelta hdelta_le_one
  rw [cumulativeSuccessorReturnVarianceProxy_coe] at hradiusSq
  have hsqrtSq :
      (Real.sqrt (2 * Real.log (2 / delta) / (rounds : Real))) ^ 2 =
        2 * Real.log (2 / delta) / (rounds : Real) := by
    rw [Real.sq_sqrt]
    positivity
  have hlhsNonneg :
      0 <= normalizedSuccessorReturnConfidenceRadius
        mdp episodes rounds delta :=
    normalizedSuccessorReturnConfidenceRadius_nonneg _ _ _ _
  have hrhsNonneg :
      0 <= (mdp.horizon : Real) *
        Real.sqrt (2 * Real.log (2 / delta) / (rounds : Real)) :=
    mul_nonneg (by positivity) (Real.sqrt_nonneg _)
  have hsq :
      (normalizedSuccessorReturnConfidenceRadius
          mdp episodes rounds delta) ^ 2 =
        ((mdp.horizon : Real) *
          Real.sqrt (2 * Real.log (2 / delta) / (rounds : Real))) ^ 2 := by
    unfold normalizedSuccessorReturnConfidenceRadius
    rw [div_pow, hradiusSq]
    simp only [mul_pow]
    rw [hsqrtSq]
    field_simp [ne_of_gt hepisodesReal, ne_of_gt hroundsReal]
  nlinarith

/-- Elementary deterministic envelope for the normalized return radius. -/
noncomputable def decayingExplorationReturnRadiusEnvelope
    (mdp : MDP State Action) (n : Nat) : Real :=
  2 * (mdp.horizon : Real) / (decayingExplorationScale n : Real)

omit [DecidableEq State] [DecidableEq Action]
    [MeasurableSingletonClass State] [MeasurableSingletonClass Action]
    [Nonempty State] [Nonempty Action] in
/-- The decaying schedule dominates the normalized logarithmic return radius. -/
theorem normalizedSuccessorReturnConfidenceRadius_le_decayingEnvelope
    (mdp : MDP State Action) (episodes : Nat) (n : Nat)
    (hepisodes : 0 < episodes) :
    normalizedSuccessorReturnConfidenceRadius mdp episodes
        (decayingExplorationRounds mdp n) (vanishingAverageConfidenceDelta n) <=
      decayingExplorationReturnRadiusEnvelope mdp n := by
  have hrounds := decayingExplorationRounds_pos mdp n
  rw [normalizedSuccessorReturnConfidenceRadius_eq mdp episodes
    (decayingExplorationRounds mdp n) (vanishingAverageConfidenceDelta n)
    hepisodes hrounds (vanishingAverageConfidenceDelta_pos n)
    (vanishingAverageConfidenceDelta_le_one n)]
  unfold decayingExplorationReturnRadiusEnvelope
  rw [show 2 * (mdp.horizon : Real) /
      (decayingExplorationScale n : Real) =
      (mdp.horizon : Real) *
        (2 / (decayingExplorationScale n : Real)) by ring]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  have hscalePos : 0 < (decayingExplorationScale n : Real) := by
    exact_mod_cast decayingExplorationScale_pos n
  have hscaleOne : 1 <= (decayingExplorationScale n : Real) := by
    exact_mod_cast (show 1 <= decayingExplorationScale n by
      simp [decayingExplorationScale])
  have hdeltaRewrite :
      2 / vanishingAverageConfidenceDelta n =
        2 * (decayingExplorationScale n : Real) := by
    unfold vanishingAverageConfidenceDelta decayingExplorationScale
    field_simp
  have hroundsCast :
      ((decayingExplorationRounds mdp n : Nat) : Real) =
        (decayingExplorationScale n : Real) ^ (mdp.horizon + 4) := by
    simp [decayingExplorationRounds]
  rw [hdeltaRewrite, hroundsCast]
  apply Real.sqrt_le_iff.mpr
  constructor
  · positivity
  · have hlogUpper :
        Real.log (2 * (decayingExplorationScale n : Real)) <=
          2 * (decayingExplorationScale n : Real) := by
      exact (Real.log_le_sub_one_of_pos (by positivity)).trans (by linarith)
    have hpow :
        (decayingExplorationScale n : Real) <=
          (decayingExplorationScale n : Real) ^ (mdp.horizon + 2) := by
      simpa using pow_le_pow_right₀ hscaleOne
        (show 1 <= mdp.horizon + 2 by omega)
    have hfactor :
        (decayingExplorationScale n : Real) ^ (mdp.horizon + 4) =
          (decayingExplorationScale n : Real) ^ (mdp.horizon + 2) *
            (decayingExplorationScale n : Real) ^ 2 := by
      rw [<- pow_add]
    rw [hfactor, div_pow]
    apply (div_le_iff₀
      (mul_pos (pow_pos hscalePos _) (pow_pos hscalePos _))).2
    field_simp [ne_of_gt hscalePos]
    nlinarith

omit [DecidableEq State] [DecidableEq Action]
    [MeasurableSingletonClass State] [MeasurableSingletonClass Action]
    [Nonempty State] [Nonempty Action] in
theorem decayingExplorationScheduledEpisodes_pos
    (mdp : MDP State Action) (baseVisitFloor : Real) (n : Nat) :
    0 < decayingExplorationScheduledEpisodes mdp baseVisitFloor n := by
  unfold decayingExplorationScheduledEpisodes
  exact normalizedCumulativeInverseSqrtScheduledEpisodes_pos _ _ _ _

omit [DecidableEq State] [DecidableEq Action]
    [MeasurableSingletonClass State] [MeasurableSingletonClass Action]
    [Nonempty State] [Nonempty Action] in
theorem decayingExplorationReturnRadiusEnvelope_tendsto_zero
    (mdp : MDP State Action) :
    Tendsto (decayingExplorationReturnRadiusEnvelope mdp)
      atTop (nhds 0) := by
  have hscale :
      Tendsto (fun n : Nat => (decayingExplorationScale n : Real))
        atTop atTop := by
    change Tendsto (fun n : Nat => (((n + 2 : Nat) : Real))) atTop atTop
    exact tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 2)
  simpa [decayingExplorationReturnRadiusEnvelope] using
    (tendsto_const_nhds.div_atTop hscale :
      Tendsto
        (fun n : Nat =>
          (2 * (mdp.horizon : Real)) /
            (decayingExplorationScale n : Real)) atTop (nhds 0))

omit [DecidableEq State] [DecidableEq Action]
    [MeasurableSingletonClass State] [MeasurableSingletonClass Action]
    [Nonempty State] [Nonempty Action] in
theorem decayingExplorationNormalizedReturnRadius_tendsto_zero
    (mdp : MDP State Action) (baseVisitFloor : Real) :
    Tendsto
      (fun n =>
        normalizedSuccessorReturnConfidenceRadius mdp
          (decayingExplorationScheduledEpisodes mdp baseVisitFloor n)
          (decayingExplorationRounds mdp n)
          (vanishingAverageConfidenceDelta n))
      atTop (nhds 0) := by
  apply squeeze_zero
  · intro n
    exact normalizedSuccessorReturnConfidenceRadius_nonneg _ _ _ _
  · intro n
    exact normalizedSuccessorReturnConfidenceRadius_le_decayingEnvelope
      mdp (decayingExplorationScheduledEpisodes mdp baseVisitFloor n) n
      (decayingExplorationScheduledEpisodes_pos mdp baseVisitFloor n)
  · exact decayingExplorationReturnRadiusEnvelope_tendsto_zero mdp

/-- Deterministic realized-behavior certificate at schedule index `n`. -/
noncomputable def decayingExplorationAverageRealizedBehaviorRegretBound
    (mdp : MDP State Action) (baseVisitFloor : Real) (n : Nat) : Real :=
  decayingExplorationAverageExploratoryBehaviorExpectedRegretBound
      mdp baseVisitFloor n +
    normalizedSuccessorReturnConfidenceRadius mdp
      (decayingExplorationScheduledEpisodes mdp baseVisitFloor n)
      (decayingExplorationRounds mdp n)
      (vanishingAverageConfidenceDelta n)

/-- Count and return deviations each consume one scheduled confidence share. -/
noncomputable def decayingExplorationRealizedFailureBudget
    (n : Nat) : ENNReal :=
  ENNReal.ofReal (vanishingAverageConfidenceDelta n) +
    ENNReal.ofReal (vanishingAverageConfidenceDelta n)

theorem decayingExplorationAverageRealizedBehaviorRegretBound_nonneg
    (mdp : MDP State Action) (hhorizon : 0 < mdp.horizon)
    (baseVisitFloor : Real) (hbaseVisitFloor : 0 < baseVisitFloor) (n : Nat) :
    0 <= decayingExplorationAverageRealizedBehaviorRegretBound
      mdp baseVisitFloor n := by
  unfold decayingExplorationAverageRealizedBehaviorRegretBound
  exact add_nonneg
    (by
      unfold decayingExplorationAverageExploratoryBehaviorExpectedRegretBound
        decayingExplorationAverageRecommendedExpectedRegretBound
        decayingExplorationScheduledEpisodes
      exact add_nonneg
        (normalizedCumulativeInverseSqrtScheduledAverageBound_nonneg mdp
          hhorizon (decayingExplorationRounds_pos mdp n)
          (vanishingAverageConfidenceDelta_pos n)
          (vanishingAverageConfidenceDelta_le_one n)
          (decayingExplorationVisitFloor_pos mdp hbaseVisitFloor n))
        (by unfold exploratoryBehaviorRegretCharge; positivity))
    (normalizedSuccessorReturnConfidenceRadius_nonneg _ _ _ _)

theorem decayingExplorationAverageRealizedBehaviorRegretBound_tendsto_zero
    (mdp : MDP State Action) (hhorizon : 0 < mdp.horizon)
    (baseVisitFloor : Real) (hbaseVisitFloor : 0 < baseVisitFloor) :
    Tendsto
      (decayingExplorationAverageRealizedBehaviorRegretBound
        mdp baseVisitFloor) atTop (nhds 0) := by
  simpa [decayingExplorationAverageRealizedBehaviorRegretBound] using
    (decayingExplorationAverageExploratoryBehaviorBound_tendsto_zero
      mdp hhorizon baseVisitFloor hbaseVisitFloor).add
      (decayingExplorationNormalizedReturnRadius_tendsto_zero
        mdp baseVisitFloor)

omit [DecidableEq State] [DecidableEq Action]
    [MeasurableSingletonClass State] [MeasurableSingletonClass Action]
    [Nonempty State] [Nonempty Action] in
theorem decayingExplorationRealizedFailureBudget_tendsto_zero :
    Tendsto decayingExplorationRealizedFailureBudget atTop (nhds 0) := by
  simpa [decayingExplorationRealizedFailureBudget] using
    vanishingAverageConfidenceDelta_ennreal_tendsto_zero.add
      vanishingAverageConfidenceDelta_ennreal_tendsto_zero

theorem decayingExplorationRealizedFailureAndRegretBound_tendsto_zero
    (mdp : MDP State Action) (hhorizon : 0 < mdp.horizon)
    (baseVisitFloor : Real) (hbaseVisitFloor : 0 < baseVisitFloor) :
    Tendsto
      (fun n =>
        (decayingExplorationRealizedFailureBudget n,
          decayingExplorationAverageRealizedBehaviorRegretBound
            mdp baseVisitFloor n))
      atTop (nhds (0, 0)) := by
  rw [nhds_prod_eq]
  exact decayingExplorationRealizedFailureBudget_tendsto_zero.prodMk
    (decayingExplorationAverageRealizedBehaviorRegretBound_tendsto_zero
      mdp hhorizon baseVisitFloor hbaseVisitFloor)

end AdaptiveEpisodeBatchSource

namespace AdaptiveCumulativeEmpiricalOptimisticSource

/-- Realized-regret violation set for one decaying-exploration window. -/
noncomputable def decayingExplorationAverageRealizedBehaviorRegretViolationSet
    (mdp : MDP State Action) (initialState : Measure State)
    [IsProbabilityMeasure initialState]
    (initialTable : DeterministicMarkovPolicyTable mdp)
    (defaultState : State) (baseVisitFloor : Real) (n : Nat) :
    Set
      (EpisodeBatchTrajectory mdp
        (AdaptiveEpisodeBatchSource.decayingExplorationScheduledEpisodes
          mdp baseVisitFloor n)) := by
  let rounds := AdaptiveEpisodeBatchSource.decayingExplorationRounds mdp n
  let delta := AdaptiveEpisodeBatchSource.vanishingAverageConfidenceDelta n
  let explorationRate := AdaptiveEpisodeBatchSource.decayingExplorationRate n
  let visitFloor := AdaptiveEpisodeBatchSource.decayingExplorationVisitFloor
    mdp baseVisitFloor n
  let episodes := AdaptiveEpisodeBatchSource.decayingExplorationScheduledEpisodes
    mdp baseVisitFloor n
  let countRadius :=
    AdaptiveEpisodeBatchSource.normalizedCumulativeInverseSqrtCountRadius
      mdp rounds delta visitFloor
  let source := exploratorySource mdp initialState episodes initialTable
    defaultState countRadius explorationRate
      (AdaptiveEpisodeBatchSource.decayingExplorationRate_le_one n)
  exact {trajectory |
    AdaptiveEpisodeBatchSource.decayingExplorationAverageRealizedBehaviorRegretBound
        mdp baseVisitFloor n <
      source.realizedSuccessorAverageRegret trajectory rounds}

/--
One finite window: the realized violation set is covered by the measurable
count/return union, whose tail is the two-share scheduled budget.
-/
theorem exploratorySource_trajectoryMeasure_cumulativeInverseSqrtPathSupport_optimism_and_decayingExplorationAverageRealizedBehaviorConsistency
    (mdp : MDP State Action) (initialState : Measure State)
    [IsProbabilityMeasure initialState]
    (baseVisitFloor : Real) (n : Nat)
    [StandardBorelSpace
      (EpisodeBatch mdp
        (AdaptiveEpisodeBatchSource.decayingExplorationScheduledEpisodes
          mdp baseVisitFloor n))]
    [StandardBorelSpace
      (EpisodeBatchTrajectory mdp
        (AdaptiveEpisodeBatchSource.decayingExplorationScheduledEpisodes
          mdp baseVisitFloor n))]
    (initialTable : DeterministicMarkovPolicyTable mdp)
    (defaultState : State)
    (support : ExploratoryPathSupport mdp initialState)
    (hbaseFloor : ExploratoryPathUniformVisitFloor support 1 baseVisitFloor)
    (hrewardBound : forall state action, |mdp.reward state action| <= 1)
    (hhorizon : 0 < mdp.horizon) (hbaseVisitFloor : 0 < baseVisitFloor) :
    let rounds := AdaptiveEpisodeBatchSource.decayingExplorationRounds mdp n
    let delta := AdaptiveEpisodeBatchSource.vanishingAverageConfidenceDelta n
    let explorationRate := AdaptiveEpisodeBatchSource.decayingExplorationRate n
    let visitFloor := AdaptiveEpisodeBatchSource.decayingExplorationVisitFloor
      mdp baseVisitFloor n
    let episodes :=
      AdaptiveEpisodeBatchSource.decayingExplorationScheduledEpisodes
        mdp baseVisitFloor n
    let countRadius :=
      AdaptiveEpisodeBatchSource.normalizedCumulativeInverseSqrtCountRadius
        mdp rounds delta visitFloor
    let source := exploratorySource mdp initialState episodes initialTable
      defaultState countRadius explorationRate
        (AdaptiveEpisodeBatchSource.decayingExplorationRate_le_one n)
    let countBadEvent := source.adaptiveCumulativeCountBadEvent rounds delta
    let returnBadEvent := source.successorReturnDeviationBadEvent rounds delta
    let combinedBadEvent := countBadEvent ∪ returnBadEvent
    let violationSet :=
      decayingExplorationAverageRealizedBehaviorRegretViolationSet
        mdp initialState initialTable defaultState baseVisitFloor n
    MeasurableSet combinedBadEvent /\
      source.trajectoryMeasure combinedBadEvent <=
        AdaptiveEpisodeBatchSource.decayingExplorationRealizedFailureBudget n /\
      violationSet ⊆ combinedBadEvent /\
      source.trajectoryMeasure violationSet <=
        AdaptiveEpisodeBatchSource.decayingExplorationRealizedFailureBudget n /\
      forall trajectory, trajectory ∉ combinedBadEvent ->
        (forall round : Fin rounds, forall state,
          mdp.optimalValueRemaining mdp.horizon le_rfl state <=
            (adaptiveCumulativeEmpiricalOptimisticPlanAt
              trajectory defaultState countRadius round).upperValueRemaining
                mdp.horizon le_rfl state) /\
        source.realizedSuccessorAverageRegret trajectory rounds <=
          AdaptiveEpisodeBatchSource.decayingExplorationAverageRealizedBehaviorRegretBound
            mdp baseVisitFloor n := by
  let rounds := AdaptiveEpisodeBatchSource.decayingExplorationRounds mdp n
  let delta := AdaptiveEpisodeBatchSource.vanishingAverageConfidenceDelta n
  let explorationRate := AdaptiveEpisodeBatchSource.decayingExplorationRate n
  let visitFloor := AdaptiveEpisodeBatchSource.decayingExplorationVisitFloor
    mdp baseVisitFloor n
  let episodes := AdaptiveEpisodeBatchSource.decayingExplorationScheduledEpisodes
    mdp baseVisitFloor n
  let countRadius :=
    AdaptiveEpisodeBatchSource.normalizedCumulativeInverseSqrtCountRadius
      mdp rounds delta visitFloor
  let source := exploratorySource mdp initialState episodes initialTable
    defaultState countRadius explorationRate
      (AdaptiveEpisodeBatchSource.decayingExplorationRate_le_one n)
  let countBadEvent := source.adaptiveCumulativeCountBadEvent rounds delta
  let returnBadEvent := source.successorReturnDeviationBadEvent rounds delta
  let combinedBadEvent := countBadEvent ∪ returnBadEvent
  let violationSet :=
    decayingExplorationAverageRealizedBehaviorRegretViolationSet
      mdp initialState initialTable defaultState baseVisitFloor n
  have hterminal :=
    exploratorySource_trajectoryMeasure_cumulativeInverseSqrtPathSupport_optimism_and_decayingExplorationAverageRealizedBehaviorRegret
      mdp initialState baseVisitFloor n initialTable defaultState support
      hbaseFloor hrewardBound hhorizon hbaseVisitFloor
  dsimp only at hterminal
  rcases hterminal with ⟨hmeasurable, htail, houtside⟩
  have htail' :
      source.trajectoryMeasure combinedBadEvent <=
        AdaptiveEpisodeBatchSource.decayingExplorationRealizedFailureBudget n := by
    simpa [AdaptiveEpisodeBatchSource.decayingExplorationRealizedFailureBudget]
      using htail
  have houtside' : forall trajectory, trajectory ∉ combinedBadEvent ->
      (forall round : Fin rounds, forall state,
        mdp.optimalValueRemaining mdp.horizon le_rfl state <=
          (adaptiveCumulativeEmpiricalOptimisticPlanAt
            trajectory defaultState countRadius round).upperValueRemaining
              mdp.horizon le_rfl state) /\
      source.realizedSuccessorAverageRegret trajectory rounds <=
        AdaptiveEpisodeBatchSource.decayingExplorationAverageRealizedBehaviorRegretBound
          mdp baseVisitFloor n := by
    intro trajectory htrajectory
    have h := houtside trajectory htrajectory
    exact ⟨h.1, by
      simpa [AdaptiveEpisodeBatchSource.decayingExplorationAverageRealizedBehaviorRegretBound,
        AdaptiveEpisodeBatchSource.normalizedSuccessorReturnConfidenceRadius]
        using h.2⟩
  have hsubset : violationSet ⊆ combinedBadEvent := by
    intro trajectory hviolation
    by_contra htrajectory
    have hbound := (houtside' trajectory htrajectory).2
    have hviolation' :
        AdaptiveEpisodeBatchSource.decayingExplorationAverageRealizedBehaviorRegretBound
            mdp baseVisitFloor n <
          source.realizedSuccessorAverageRegret trajectory rounds := by
      simpa [violationSet,
        decayingExplorationAverageRealizedBehaviorRegretViolationSet,
        rounds, delta, explorationRate, visitFloor, episodes, countRadius,
        source] using hviolation
    exact (not_lt_of_ge hbound) hviolation'
  have hviolationTail :
      source.trajectoryMeasure violationSet <=
        AdaptiveEpisodeBatchSource.decayingExplorationRealizedFailureBudget n :=
    (measure_mono hsubset).trans htail'
  exact ⟨hmeasurable, htail', hsubset, hviolationTail, houtside'⟩

/--
All finite windows plus the joint scalar limit.  The indexed Borel witnesses
make the changing sample spaces explicit and prevent a common-space reading.
-/
theorem exploratorySource_trajectoryMeasure_cumulativeInverseSqrtPathSupport_decayingExplorationAverageRealizedBehaviorConsistency_allWindows
    (mdp : MDP State Action) (initialState : Measure State)
    [IsProbabilityMeasure initialState]
    (baseVisitFloor : Real)
    (hbatchBorel : forall n, StandardBorelSpace
      (EpisodeBatch mdp
        (AdaptiveEpisodeBatchSource.decayingExplorationScheduledEpisodes
          mdp baseVisitFloor n)))
    (htrajectoryBorel : forall n, StandardBorelSpace
      (EpisodeBatchTrajectory mdp
        (AdaptiveEpisodeBatchSource.decayingExplorationScheduledEpisodes
          mdp baseVisitFloor n)))
    (initialTable : DeterministicMarkovPolicyTable mdp)
    (defaultState : State)
    (support : ExploratoryPathSupport mdp initialState)
    (hbaseFloor : ExploratoryPathUniformVisitFloor support 1 baseVisitFloor)
    (hrewardBound : forall state action, |mdp.reward state action| <= 1)
    (hhorizon : 0 < mdp.horizon) (hbaseVisitFloor : 0 < baseVisitFloor) :
    Tendsto
        (fun n =>
          (AdaptiveEpisodeBatchSource.decayingExplorationRealizedFailureBudget n,
            AdaptiveEpisodeBatchSource.decayingExplorationAverageRealizedBehaviorRegretBound
              mdp baseVisitFloor n))
        atTop (nhds (0, 0)) /\
      forall n,
        letI : StandardBorelSpace
            (EpisodeBatch mdp
              (AdaptiveEpisodeBatchSource.decayingExplorationScheduledEpisodes
                mdp baseVisitFloor n)) := hbatchBorel n
        letI : StandardBorelSpace
            (EpisodeBatchTrajectory mdp
              (AdaptiveEpisodeBatchSource.decayingExplorationScheduledEpisodes
                mdp baseVisitFloor n)) := htrajectoryBorel n
        let rounds := AdaptiveEpisodeBatchSource.decayingExplorationRounds mdp n
        let delta := AdaptiveEpisodeBatchSource.vanishingAverageConfidenceDelta n
        let explorationRate := AdaptiveEpisodeBatchSource.decayingExplorationRate n
        let visitFloor := AdaptiveEpisodeBatchSource.decayingExplorationVisitFloor
          mdp baseVisitFloor n
        let episodes :=
          AdaptiveEpisodeBatchSource.decayingExplorationScheduledEpisodes
            mdp baseVisitFloor n
        let countRadius :=
          AdaptiveEpisodeBatchSource.normalizedCumulativeInverseSqrtCountRadius
            mdp rounds delta visitFloor
        let source := exploratorySource mdp initialState episodes initialTable
          defaultState countRadius explorationRate
            (AdaptiveEpisodeBatchSource.decayingExplorationRate_le_one n)
        let countBadEvent := source.adaptiveCumulativeCountBadEvent rounds delta
        let returnBadEvent := source.successorReturnDeviationBadEvent rounds delta
        let combinedBadEvent := countBadEvent ∪ returnBadEvent
        let violationSet :=
          decayingExplorationAverageRealizedBehaviorRegretViolationSet
            mdp initialState initialTable defaultState baseVisitFloor n
        MeasurableSet combinedBadEvent /\
          source.trajectoryMeasure combinedBadEvent <=
            AdaptiveEpisodeBatchSource.decayingExplorationRealizedFailureBudget n /\
          violationSet ⊆ combinedBadEvent /\
          source.trajectoryMeasure violationSet <=
            AdaptiveEpisodeBatchSource.decayingExplorationRealizedFailureBudget n /\
          forall trajectory, trajectory ∉ combinedBadEvent ->
            (forall round : Fin rounds, forall state,
              mdp.optimalValueRemaining mdp.horizon le_rfl state <=
                (adaptiveCumulativeEmpiricalOptimisticPlanAt
                  trajectory defaultState countRadius round).upperValueRemaining
                    mdp.horizon le_rfl state) /\
            source.realizedSuccessorAverageRegret trajectory rounds <=
              AdaptiveEpisodeBatchSource.decayingExplorationAverageRealizedBehaviorRegretBound
                mdp baseVisitFloor n := by
  constructor
  · exact
      AdaptiveEpisodeBatchSource.decayingExplorationRealizedFailureAndRegretBound_tendsto_zero
        mdp hhorizon baseVisitFloor hbaseVisitFloor
  · intro n
    letI := hbatchBorel n
    letI := htrajectoryBorel n
    exact
      exploratorySource_trajectoryMeasure_cumulativeInverseSqrtPathSupport_optimism_and_decayingExplorationAverageRealizedBehaviorConsistency
        mdp initialState baseVisitFloor n initialTable defaultState support
        hbaseFloor hrewardBound hhorizon hbaseVisitFloor

end AdaptiveCumulativeEmpiricalOptimisticSource

end BanditRLProof.FiniteHorizonRL
