import BanditRLProof.RL.FiniteHorizonAdaptiveCumulativeEpisodewiseRealizedBehaviorConsistency
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.Probability.ProductMeasure

/-!
# Common-space episodewise realized behavior consistency

The preceding episodewise route gives one sharp certificate for every scheduled
finite window, but those windows have different trajectory types.  This module
places the finite-window laws on one dependent infinite product.  Coordinate
`n` therefore has exactly the compiled adaptive trajectory law for schedule
`n`, and the scheduled realized-regret coordinates form one random process.

The coupling is intentionally the independent-coordinate product coupling.  It
is sufficient for a mathematically literal convergence-in-probability theorem,
but it is not a nested coupling of one online algorithm across schedules and
does not imply pathwise, almost-sure, or anytime behavior.
-/

open Filter MeasureTheory
open scoped ENNReal NNReal ProbabilityTheory Topology

universe u v

namespace BanditRLProof.FiniteHorizonRL

variable {State : Type u} {Action : Type v}
    [MeasurableSpace State] [MeasurableSpace Action]
    [Fintype State] [Fintype Action]
    [DecidableEq State] [DecidableEq Action]
    [MeasurableSingletonClass State] [MeasurableSingletonClass Action]
    [Nonempty State] [Nonempty Action]

namespace AdaptiveEpisodeBatchSource

/-- Realized cumulative successor regret is measurable in the finite trajectory. -/
theorem measurable_realizedSuccessorCumulativeRegret
    {mdp : MDP State Action} {initialState : Measure State}
    [IsProbabilityMeasure initialState] {episodes : Nat}
    (source : AdaptiveEpisodeBatchSource mdp initialState episodes)
    (rounds : Nat) :
    Measurable (fun trajectory =>
      source.realizedSuccessorCumulativeRegret trajectory rounds) := by
  unfold realizedSuccessorCumulativeRegret
  refine Finset.measurable_sum Finset.univ fun round _ => ?_
  exact measurable_const.sub
    (EpisodeBatch.measurable_totalReturn.comp
      (measurable_pi_apply ((round : Nat) + 1)))

/-- Realized average successor regret is measurable in the finite trajectory. -/
theorem measurable_realizedSuccessorAverageRegret
    {mdp : MDP State Action} {initialState : Measure State}
    [IsProbabilityMeasure initialState] {episodes : Nat}
    (source : AdaptiveEpisodeBatchSource mdp initialState episodes)
    (rounds : Nat) :
    Measurable (fun trajectory =>
      source.realizedSuccessorAverageRegret trajectory rounds) := by
  unfold realizedSuccessorAverageRegret
  exact (source.measurable_realizedSuccessorCumulativeRegret rounds).div_const _

omit [DecidableEq State] [DecidableEq Action]
    [MeasurableSingletonClass Action] [Nonempty State] in
/-- A finite sum of policy expected regrets is nonnegative. -/
theorem successorExpectedCumulativeRegret_nonneg
    {mdp : MDP State Action} {initialState : Measure State}
    [IsProbabilityMeasure initialState] {episodes : Nat}
    (source : AdaptiveEpisodeBatchSource mdp initialState episodes)
    (trajectory : EpisodeBatchTrajectory mdp episodes) (rounds : Nat) :
    0 <= source.successorExpectedCumulativeRegret trajectory rounds := by
  unfold successorExpectedCumulativeRegret
  exact Finset.sum_nonneg fun round _ =>
    (source.policyAt trajectory ((round : Nat) + 1)).expectedRegret_nonneg initialState

omit [DecidableEq State] [DecidableEq Action]
    [MeasurableSingletonClass Action] [Nonempty State] in
/-- The average of successor policy expected regrets is nonnegative. -/
theorem successorExpectedAverageRegret_nonneg
    {mdp : MDP State Action} {initialState : Measure State}
    [IsProbabilityMeasure initialState] {episodes : Nat}
    (source : AdaptiveEpisodeBatchSource mdp initialState episodes)
    (trajectory : EpisodeBatchTrajectory mdp episodes) (rounds : Nat) :
    0 <= source.successorExpectedAverageRegret trajectory rounds := by
  unfold successorExpectedAverageRegret
  exact div_nonneg
    (source.successorExpectedCumulativeRegret_nonneg trajectory rounds)
    (by positivity)

/--
An expected-regret upper bound and a two-sided return-deviation bound control
the absolute realized average regret.
-/
theorem abs_realizedSuccessorAverageRegret_le_of_expected_le_of_deviation_abs_le
    {mdp : MDP State Action} {initialState : Measure State}
    [IsProbabilityMeasure initialState] {episodes : Nat}
    (source : AdaptiveEpisodeBatchSource mdp initialState episodes)
    (trajectory : EpisodeBatchTrajectory mdp episodes)
    (rounds : Nat) (hrounds : 0 < rounds) (hepisodes : 0 < episodes)
    (expectedBound deviationBound : Real)
    (hexpected :
      source.successorExpectedAverageRegret trajectory rounds <= expectedBound)
    (hdeviation :
      |source.cumulativeSuccessorReturnDeviation rounds trajectory| <= deviationBound) :
    |source.realizedSuccessorAverageRegret trajectory rounds| <=
      expectedBound + deviationBound / ((episodes : Real) * (rounds : Real)) := by
  have hdenom : 0 < (episodes : Real) * (rounds : Real) := by positivity
  rw [source.realizedSuccessorAverageRegret_eq_expected_sub_deviation
    trajectory rounds hrounds hepisodes]
  calc
    |source.successorExpectedAverageRegret trajectory rounds -
        source.cumulativeSuccessorReturnDeviation rounds trajectory /
          ((episodes : Real) * (rounds : Real))| <=
        |source.successorExpectedAverageRegret trajectory rounds| +
          |source.cumulativeSuccessorReturnDeviation rounds trajectory /
            ((episodes : Real) * (rounds : Real))| :=
      abs_sub _ _
    _ = source.successorExpectedAverageRegret trajectory rounds +
          |source.cumulativeSuccessorReturnDeviation rounds trajectory| /
            ((episodes : Real) * (rounds : Real)) := by
      rw [abs_of_nonneg
        (source.successorExpectedAverageRegret_nonneg trajectory rounds),
        abs_div, abs_of_pos hdenom]
    _ <= expectedBound +
          deviationBound / ((episodes : Real) * (rounds : Real)) :=
      add_le_add hexpected
        (div_le_div_of_nonneg_right hdeviation hdenom.le)

end AdaptiveEpisodeBatchSource

namespace AdaptiveCumulativeEmpiricalOptimisticSource

/--
The sharp finite-window certificate controls the absolute realized regret, not
only its upper tail.  This is the finite-window input needed by convergence in
probability.
-/
theorem exploratorySource_trajectoryMeasure_cumulativeInverseSqrtPathSupport_optimism_and_decayingExplorationEpisodewiseAverageAbsoluteRealizedBehaviorConsistency
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
    let returnBadEvent :=
      source.episodewiseSuccessorReturnDeviationBadEvent rounds delta
    let combinedBadEvent := countBadEvent ∪ returnBadEvent
    MeasurableSet combinedBadEvent /\
      source.trajectoryMeasure combinedBadEvent <=
        AdaptiveEpisodeBatchSource.decayingExplorationRealizedFailureBudget n /\
      forall trajectory, trajectory ∉ combinedBadEvent ->
        (forall round : Fin rounds, forall state,
          mdp.optimalValueRemaining mdp.horizon le_rfl state <=
            (adaptiveCumulativeEmpiricalOptimisticPlanAt
              trajectory defaultState countRadius round).upperValueRemaining
                mdp.horizon le_rfl state) /\
        |source.realizedSuccessorAverageRegret trajectory rounds| <=
          AdaptiveEpisodeBatchSource.decayingExplorationEpisodewiseAverageRealizedBehaviorRegretBound
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
  let returnBadEvent :=
    source.episodewiseSuccessorReturnDeviationBadEvent rounds delta
  let combinedBadEvent := countBadEvent ∪ returnBadEvent
  have hfinite :=
    exploratorySource_trajectoryMeasure_cumulativeInverseSqrtPathSupport_optimism_and_decayingExplorationEpisodewiseAverageRealizedBehaviorConsistency
      mdp initialState baseVisitFloor n initialTable defaultState support
      hbaseFloor hrewardBound hhorizon hbaseVisitFloor
  dsimp only at hfinite
  rcases hfinite with
    ⟨hmeasurable, htail, _hsubset, _hviolationTail, houtsideFinite⟩
  have hparent :=
    exploratorySource_trajectoryMeasure_cumulativeInverseSqrtPathSupport_optimism_and_decayingExplorationAverageExploratoryBehaviorExpectedRegret
      mdp initialState baseVisitFloor n initialTable defaultState support
      hbaseFloor hrewardBound hhorizon hbaseVisitFloor
  dsimp only at hparent
  rcases hparent with
    ⟨_hcountMeasurable, _hcountTail, _hsubset, _hviolationTail, houtsideExpected⟩
  have hrounds : 0 < rounds :=
    AdaptiveEpisodeBatchSource.decayingExplorationRounds_pos mdp n
  have hepisodes : 0 < episodes := by
    unfold episodes AdaptiveEpisodeBatchSource.decayingExplorationScheduledEpisodes
    exact AdaptiveEpisodeBatchSource.normalizedCumulativeInverseSqrtScheduledEpisodes_pos
      mdp (AdaptiveEpisodeBatchSource.decayingExplorationRounds mdp n)
        (AdaptiveEpisodeBatchSource.vanishingAverageConfidenceDelta n)
        (AdaptiveEpisodeBatchSource.decayingExplorationVisitFloor mdp baseVisitFloor n)
  refine ⟨hmeasurable, htail, ?_⟩
  intro trajectory htrajectory
  have hnotCount : trajectory ∉ countBadEvent := by
    exact fun hmem => htrajectory (Set.mem_union_left returnBadEvent hmem)
  have hnotReturn : trajectory ∉ returnBadEvent := by
    exact fun hmem => htrajectory (Set.mem_union_right countBadEvent hmem)
  have hfiniteGood := houtsideFinite trajectory htrajectory
  have hexpectedGood := houtsideExpected trajectory hnotCount
  have hexpected :
      source.successorExpectedAverageRegret trajectory rounds <=
        AdaptiveEpisodeBatchSource.decayingExplorationAverageExploratoryBehaviorExpectedRegretBound
          mdp baseVisitFloor n := by
    rw [exploratorySource_successorExpectedAverageRegret_eq]
    exact hexpectedGood.2
  have hdeviation :
      |source.cumulativeSuccessorReturnDeviation rounds trajectory| <=
        Concentration.subGaussianSumConfidenceRadius
          (AdaptiveEpisodeBatchSource.episodewiseCumulativeSuccessorReturnVarianceProxy
            mdp episodes rounds) delta := by
    change ¬ Concentration.subGaussianSumConfidenceRadius
        (AdaptiveEpisodeBatchSource.episodewiseCumulativeSuccessorReturnVarianceProxy
          mdp episodes rounds) delta <=
      |source.cumulativeSuccessorReturnDeviation rounds trajectory| at hnotReturn
    exact (lt_of_not_ge hnotReturn).le
  refine ⟨hfiniteGood.1, ?_⟩
  have habs :=
    source.abs_realizedSuccessorAverageRegret_le_of_expected_le_of_deviation_abs_le
      trajectory rounds hrounds hepisodes
      (AdaptiveEpisodeBatchSource.decayingExplorationAverageExploratoryBehaviorExpectedRegretBound
        mdp baseVisitFloor n)
      (Concentration.subGaussianSumConfidenceRadius
        (AdaptiveEpisodeBatchSource.episodewiseCumulativeSuccessorReturnVarianceProxy
          mdp episodes rounds) delta)
      hexpected hdeviation
  simpa [AdaptiveEpisodeBatchSource.decayingExplorationEpisodewiseAverageRealizedBehaviorRegretBound,
    AdaptiveEpisodeBatchSource.episodewiseNormalizedSuccessorReturnConfidenceRadius]
    using habs

/-- The dependent sample space containing one complete scheduled experiment per coordinate. -/
abbrev DecayingExplorationEpisodewiseWindowSpace
    (mdp : MDP State Action) (baseVisitFloor : Real) :=
  (n : Nat) -> EpisodeBatchTrajectory mdp
    (AdaptiveEpisodeBatchSource.decayingExplorationScheduledEpisodes
      mdp baseVisitFloor n)

/-- The concrete adaptive source used at schedule coordinate `n`. -/
noncomputable def decayingExplorationEpisodewiseWindowSource
    (mdp : MDP State Action) (initialState : Measure State)
    [IsProbabilityMeasure initialState]
    (initialTable : DeterministicMarkovPolicyTable mdp)
    (defaultState : State) (baseVisitFloor : Real) (n : Nat) :
    AdaptiveEpisodeBatchSource mdp initialState
      (AdaptiveEpisodeBatchSource.decayingExplorationScheduledEpisodes
        mdp baseVisitFloor n) :=
  exploratorySource mdp initialState
    (AdaptiveEpisodeBatchSource.decayingExplorationScheduledEpisodes
      mdp baseVisitFloor n)
    initialTable defaultState
    (AdaptiveEpisodeBatchSource.normalizedCumulativeInverseSqrtCountRadius
      mdp (AdaptiveEpisodeBatchSource.decayingExplorationRounds mdp n)
      (AdaptiveEpisodeBatchSource.vanishingAverageConfidenceDelta n)
      (AdaptiveEpisodeBatchSource.decayingExplorationVisitFloor
        mdp baseVisitFloor n))
    (AdaptiveEpisodeBatchSource.decayingExplorationRate n)
    (AdaptiveEpisodeBatchSource.decayingExplorationRate_le_one n)

/-- The scheduled adaptive trajectory law at common-space coordinate `n`. -/
noncomputable def decayingExplorationEpisodewiseWindowMeasure
    (mdp : MDP State Action) (initialState : Measure State)
    [IsProbabilityMeasure initialState]
    (initialTable : DeterministicMarkovPolicyTable mdp)
    (defaultState : State) (baseVisitFloor : Real) (n : Nat) :
    Measure (EpisodeBatchTrajectory mdp
      (AdaptiveEpisodeBatchSource.decayingExplorationScheduledEpisodes
        mdp baseVisitFloor n)) :=
  (decayingExplorationEpisodewiseWindowSource mdp initialState initialTable
    defaultState baseVisitFloor n).trajectoryMeasure

instance instDecayingExplorationEpisodewiseWindowMeasureIsProbabilityMeasure
    (mdp : MDP State Action) (initialState : Measure State)
    [IsProbabilityMeasure initialState]
    (initialTable : DeterministicMarkovPolicyTable mdp)
    (defaultState : State) (baseVisitFloor : Real) (n : Nat) :
    IsProbabilityMeasure
      (decayingExplorationEpisodewiseWindowMeasure mdp initialState initialTable
        defaultState baseVisitFloor n) := by
  unfold decayingExplorationEpisodewiseWindowMeasure
  infer_instance

/--
Independent-coordinate coupling of all scheduled finite-window trajectory laws.
-/
noncomputable def decayingExplorationEpisodewiseCommonMeasure
    (mdp : MDP State Action) (initialState : Measure State)
    [IsProbabilityMeasure initialState]
    (initialTable : DeterministicMarkovPolicyTable mdp)
    (defaultState : State) (baseVisitFloor : Real) :
    Measure (DecayingExplorationEpisodewiseWindowSpace mdp baseVisitFloor) :=
  Measure.infinitePi fun n =>
    decayingExplorationEpisodewiseWindowMeasure mdp initialState initialTable
      defaultState baseVisitFloor n

instance instDecayingExplorationEpisodewiseCommonMeasureIsProbabilityMeasure
    (mdp : MDP State Action) (initialState : Measure State)
    [IsProbabilityMeasure initialState]
    (initialTable : DeterministicMarkovPolicyTable mdp)
    (defaultState : State) (baseVisitFloor : Real) :
    IsProbabilityMeasure
      (decayingExplorationEpisodewiseCommonMeasure mdp initialState initialTable
        defaultState baseVisitFloor) := by
  unfold decayingExplorationEpisodewiseCommonMeasure
  infer_instance

/-- Every common-space coordinate has exactly its scheduled adaptive law. -/
theorem decayingExplorationEpisodewiseCommonMeasure_map_eval
    (mdp : MDP State Action) (initialState : Measure State)
    [IsProbabilityMeasure initialState]
    (initialTable : DeterministicMarkovPolicyTable mdp)
    (defaultState : State) (baseVisitFloor : Real) (n : Nat) :
    (decayingExplorationEpisodewiseCommonMeasure mdp initialState initialTable
      defaultState baseVisitFloor).map (fun omega => omega n) =
      decayingExplorationEpisodewiseWindowMeasure mdp initialState initialTable
        defaultState baseVisitFloor n := by
  unfold decayingExplorationEpisodewiseCommonMeasure
  exact Measure.infinitePi_map_eval _ n

/-- Scheduled realized successor-average regret as one common-space process. -/
noncomputable def decayingExplorationEpisodewiseRealizedBehaviorRegretProcess
    (mdp : MDP State Action) (initialState : Measure State)
    [IsProbabilityMeasure initialState]
    (initialTable : DeterministicMarkovPolicyTable mdp)
    (defaultState : State) (baseVisitFloor : Real)
    (n : Nat) (omega : DecayingExplorationEpisodewiseWindowSpace
      mdp baseVisitFloor) : Real :=
  (decayingExplorationEpisodewiseWindowSource mdp initialState initialTable
    defaultState baseVisitFloor n).realizedSuccessorAverageRegret
      (omega n) (AdaptiveEpisodeBatchSource.decayingExplorationRounds mdp n)

/-- Every scheduled regret coordinate is a measurable real random variable. -/
theorem measurable_decayingExplorationEpisodewiseRealizedBehaviorRegretProcess
    (mdp : MDP State Action) (initialState : Measure State)
    [IsProbabilityMeasure initialState]
    (initialTable : DeterministicMarkovPolicyTable mdp)
    (defaultState : State) (baseVisitFloor : Real) (n : Nat) :
    Measurable
      (decayingExplorationEpisodewiseRealizedBehaviorRegretProcess mdp
        initialState initialTable defaultState baseVisitFloor n) := by
  unfold decayingExplorationEpisodewiseRealizedBehaviorRegretProcess
  exact
    ((decayingExplorationEpisodewiseWindowSource mdp initialState initialTable
      defaultState baseVisitFloor n).measurable_realizedSuccessorAverageRegret
        (AdaptiveEpisodeBatchSource.decayingExplorationRounds mdp n)).comp
      (measurable_pi_apply n)

/-- Pull the sharp count/return union at coordinate `n` to the common space. -/
noncomputable def decayingExplorationEpisodewiseCommonBadEvent
    (mdp : MDP State Action) (initialState : Measure State)
    [IsProbabilityMeasure initialState]
    (initialTable : DeterministicMarkovPolicyTable mdp)
    (defaultState : State) (baseVisitFloor : Real) (n : Nat) :
    Set (DecayingExplorationEpisodewiseWindowSpace mdp baseVisitFloor) :=
  let source := decayingExplorationEpisodewiseWindowSource mdp initialState
    initialTable defaultState baseVisitFloor n
  let rounds := AdaptiveEpisodeBatchSource.decayingExplorationRounds mdp n
  let delta := AdaptiveEpisodeBatchSource.vanishingAverageConfidenceDelta n
  (fun omega => omega n) ⁻¹'
    (source.adaptiveCumulativeCountBadEvent rounds delta ∪
      source.episodewiseSuccessorReturnDeviationBadEvent rounds delta)

/-- The pulled-back coordinate bad event inherits the exact finite-window budget. -/
theorem decayingExplorationEpisodewiseCommonMeasure_badEvent_le
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
    (hhorizon : 0 < mdp.horizon) (hbaseVisitFloor : 0 < baseVisitFloor)
    (n : Nat) :
    decayingExplorationEpisodewiseCommonMeasure mdp initialState initialTable
        defaultState baseVisitFloor
        (decayingExplorationEpisodewiseCommonBadEvent mdp initialState initialTable
          defaultState baseVisitFloor n) <=
      AdaptiveEpisodeBatchSource.decayingExplorationRealizedFailureBudget n := by
  letI := hbatchBorel n
  letI := htrajectoryBorel n
  have hfinite :=
    exploratorySource_trajectoryMeasure_cumulativeInverseSqrtPathSupport_optimism_and_decayingExplorationEpisodewiseAverageAbsoluteRealizedBehaviorConsistency
      mdp initialState baseVisitFloor n initialTable defaultState support
      hbaseFloor hrewardBound hhorizon hbaseVisitFloor
  dsimp only at hfinite
  rcases hfinite with ⟨hmeasurable, htail, _houtside⟩
  have hmeasurable' : MeasurableSet
      ((decayingExplorationEpisodewiseWindowSource mdp initialState initialTable
          defaultState baseVisitFloor n).adaptiveCumulativeCountBadEvent
            (AdaptiveEpisodeBatchSource.decayingExplorationRounds mdp n)
            (AdaptiveEpisodeBatchSource.vanishingAverageConfidenceDelta n) ∪
        (decayingExplorationEpisodewiseWindowSource mdp initialState initialTable
          defaultState baseVisitFloor n).episodewiseSuccessorReturnDeviationBadEvent
            (AdaptiveEpisodeBatchSource.decayingExplorationRounds mdp n)
            (AdaptiveEpisodeBatchSource.vanishingAverageConfidenceDelta n)) := by
    simpa [decayingExplorationEpisodewiseWindowSource] using hmeasurable
  unfold decayingExplorationEpisodewiseCommonBadEvent
  dsimp only
  unfold decayingExplorationEpisodewiseCommonMeasure
  rw [(measurePreserving_eval_infinitePi
    (fun k => decayingExplorationEpisodewiseWindowMeasure mdp initialState
      initialTable defaultState baseVisitFloor k) n).measure_preimage
        hmeasurable'.nullMeasurableSet]
  simpa [decayingExplorationEpisodewiseWindowMeasure,
    decayingExplorationEpisodewiseWindowSource] using htail

/-- Outside the pulled-back bad event, coordinate `n` has the sharp absolute bound. -/
theorem abs_decayingExplorationEpisodewiseRealizedBehaviorRegretProcess_le_of_not_mem_badEvent
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
    (hhorizon : 0 < mdp.horizon) (hbaseVisitFloor : 0 < baseVisitFloor)
    (n : Nat)
    (omega : DecayingExplorationEpisodewiseWindowSpace mdp baseVisitFloor)
    (homega : omega ∉
      decayingExplorationEpisodewiseCommonBadEvent mdp initialState initialTable
        defaultState baseVisitFloor n) :
    |decayingExplorationEpisodewiseRealizedBehaviorRegretProcess mdp initialState
        initialTable defaultState baseVisitFloor n omega| <=
      AdaptiveEpisodeBatchSource.decayingExplorationEpisodewiseAverageRealizedBehaviorRegretBound
        mdp baseVisitFloor n := by
  letI := hbatchBorel n
  letI := htrajectoryBorel n
  have hfinite :=
    exploratorySource_trajectoryMeasure_cumulativeInverseSqrtPathSupport_optimism_and_decayingExplorationEpisodewiseAverageAbsoluteRealizedBehaviorConsistency
      mdp initialState baseVisitFloor n initialTable defaultState support
      hbaseFloor hrewardBound hhorizon hbaseVisitFloor
  dsimp only at hfinite
  rcases hfinite with ⟨_hmeasurable, _htail, houtside⟩
  exact (houtside (omega n) (by
    simpa [decayingExplorationEpisodewiseCommonBadEvent] using homega)).2

/--
Terminal common-space theorem: measurable regret coordinates, exact scheduled
marginals, and convergence in probability of the process to zero.
-/
theorem exploratorySource_decayingExplorationEpisodewiseCommonMeasure_marginals_and_realizedBehaviorRegret_tendstoInMeasure_zero
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
    (forall n,
      Measurable
        (decayingExplorationEpisodewiseRealizedBehaviorRegretProcess mdp
          initialState initialTable defaultState baseVisitFloor n)) /\
      (forall n,
        (decayingExplorationEpisodewiseCommonMeasure mdp initialState initialTable
          defaultState baseVisitFloor).map (fun omega => omega n) =
          decayingExplorationEpisodewiseWindowMeasure mdp initialState initialTable
            defaultState baseVisitFloor n) /\
      TendstoInMeasure
        (decayingExplorationEpisodewiseCommonMeasure mdp initialState
          initialTable defaultState baseVisitFloor)
        (decayingExplorationEpisodewiseRealizedBehaviorRegretProcess mdp
          initialState initialTable defaultState baseVisitFloor)
        atTop (fun _ => 0) := by
  refine ⟨fun n =>
    measurable_decayingExplorationEpisodewiseRealizedBehaviorRegretProcess
      mdp initialState initialTable defaultState baseVisitFloor n, fun n =>
    decayingExplorationEpisodewiseCommonMeasure_map_eval mdp initialState
      initialTable defaultState baseVisitFloor n, ?_⟩
  rw [tendstoInMeasure_iff_dist]
  intro epsilon hepsilon
  have hbound :=
    AdaptiveEpisodeBatchSource.decayingExplorationEpisodewiseAverageRealizedBehaviorRegretBound_tendsto_zero
      mdp hhorizon baseVisitFloor hbaseVisitFloor
  have hboundEventually :
      ∀ᶠ n in atTop,
        AdaptiveEpisodeBatchSource.decayingExplorationEpisodewiseAverageRealizedBehaviorRegretBound
          mdp baseVisitFloor n < epsilon :=
    (tendsto_order.1 hbound).2 epsilon hepsilon
  apply ENNReal.tendsto_nhds_zero.2
  intro eta heta
  have hfailureEventually :
      ∀ᶠ n in atTop,
        AdaptiveEpisodeBatchSource.decayingExplorationRealizedFailureBudget n <= eta :=
    (ENNReal.tendsto_nhds_zero.1
      AdaptiveEpisodeBatchSource.decayingExplorationRealizedFailureBudget_tendsto_zero
      eta heta)
  filter_upwards [hboundEventually, hfailureEventually] with n hboundN hfailureN
  calc
    decayingExplorationEpisodewiseCommonMeasure mdp initialState initialTable
        defaultState baseVisitFloor
        {omega |
          epsilon <= dist
            (decayingExplorationEpisodewiseRealizedBehaviorRegretProcess mdp
              initialState initialTable defaultState baseVisitFloor n omega)
            0} <=
      decayingExplorationEpisodewiseCommonMeasure mdp initialState initialTable
        defaultState baseVisitFloor
        (decayingExplorationEpisodewiseCommonBadEvent mdp initialState
          initialTable defaultState baseVisitFloor n) := by
      apply measure_mono
      intro omega homega
      by_contra hnotBad
      have habs :=
        abs_decayingExplorationEpisodewiseRealizedBehaviorRegretProcess_le_of_not_mem_badEvent
          mdp initialState baseVisitFloor hbatchBorel htrajectoryBorel
          initialTable defaultState support hbaseFloor hrewardBound hhorizon
          hbaseVisitFloor n omega hnotBad
      have hdist :
          epsilon <=
            |decayingExplorationEpisodewiseRealizedBehaviorRegretProcess mdp
              initialState initialTable defaultState baseVisitFloor n omega| := by
        simpa [Real.dist_eq] using homega
      exact (not_le_of_gt hboundN) (hdist.trans habs)
    _ <= AdaptiveEpisodeBatchSource.decayingExplorationRealizedFailureBudget n :=
      decayingExplorationEpisodewiseCommonMeasure_badEvent_le
        mdp initialState baseVisitFloor hbatchBorel htrajectoryBorel
        initialTable defaultState support hbaseFloor hrewardBound hhorizon
        hbaseVisitFloor n
    _ <= eta := hfailureN

end AdaptiveCumulativeEmpiricalOptimisticSource

end BanditRLProof.FiniteHorizonRL
