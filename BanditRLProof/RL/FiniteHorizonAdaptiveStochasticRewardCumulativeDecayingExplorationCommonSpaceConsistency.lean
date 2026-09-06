import BanditRLProof.RL.FiniteHorizonAdaptiveStochasticRewardCumulativeDecayingExplorationRegularityClosedConsistency
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.Probability.ProductMeasure

/-!
# Stochastic common-space realized behavior consistency

The compiled stochastic cumulative route gives a sharp certificate on each
scheduled finite-window trajectory space. This module places those complete
finite-window experiments on one dependent infinite product and proves that
the scheduled stochastic realized-regret process converges to zero in measure.

The coupling is intentionally the independent-coordinate product coupling. It
has the exact scheduled laws as marginals, but it is not a nested causal stream
of one online run and yields no pathwise, almost-sure, or anytime conclusion.
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

namespace AdaptiveStochasticEpisodeBatchSource

omit [DecidableEq State] [DecidableEq Action]
    [MeasurableSingletonClass State] [MeasurableSingletonClass Action]
    [Nonempty State] in
/-- Stochastic realized cumulative successor regret is trajectory-measurable. -/
theorem measurable_realizedSuccessorCumulativeRegret
    {mdp : MDP State Action} {initialState : Measure State}
    [IsProbabilityMeasure initialState] {episodes : Nat}
    (source : AdaptiveStochasticEpisodeBatchSource mdp initialState episodes)
    (rounds : Nat) :
    Measurable (fun trajectory =>
      source.realizedSuccessorCumulativeRegret trajectory rounds) := by
  unfold realizedSuccessorCumulativeRegret
  refine Finset.measurable_sum Finset.univ fun round _ => ?_
  exact measurable_const.sub
    ((mdp.measurable_sampledCumulativeRewardSum episodes).comp
      (measurable_pi_apply ((round : Nat) + 1)))

omit [DecidableEq State] [DecidableEq Action]
    [MeasurableSingletonClass State] [MeasurableSingletonClass Action]
    [Nonempty State] in
/-- Stochastic realized average successor regret is trajectory-measurable. -/
theorem measurable_realizedSuccessorAverageRegret
    {mdp : MDP State Action} {initialState : Measure State}
    [IsProbabilityMeasure initialState] {episodes : Nat}
    (source : AdaptiveStochasticEpisodeBatchSource mdp initialState episodes)
    (rounds : Nat) :
    Measurable (fun trajectory =>
      source.realizedSuccessorAverageRegret trajectory rounds) := by
  unfold realizedSuccessorAverageRegret
  exact (source.measurable_realizedSuccessorCumulativeRegret rounds).div_const _

omit [DecidableEq State] [DecidableEq Action]
    [MeasurableSingletonClass Action] [Nonempty State] in
/-- A finite sum of selected stochastic-policy expected regrets is nonnegative. -/
theorem successorExpectedCumulativeRegret_nonneg
    {mdp : MDP State Action} {initialState : Measure State}
    [IsProbabilityMeasure initialState] {episodes : Nat}
    (source : AdaptiveStochasticEpisodeBatchSource mdp initialState episodes)
    (trajectory : StochasticEpisodeBatchTrajectory mdp episodes)
    (rounds : Nat) :
    0 <= source.successorExpectedCumulativeRegret trajectory rounds := by
  unfold successorExpectedCumulativeRegret
  exact Finset.sum_nonneg fun round _ =>
    (source.successorPolicyAt trajectory round).expectedRegret_nonneg initialState

omit [DecidableEq State] [DecidableEq Action]
    [MeasurableSingletonClass Action] [Nonempty State] in
/-- The average selected stochastic-policy expected regret is nonnegative. -/
theorem successorExpectedAverageRegret_nonneg
    {mdp : MDP State Action} {initialState : Measure State}
    [IsProbabilityMeasure initialState] {episodes : Nat}
    (source : AdaptiveStochasticEpisodeBatchSource mdp initialState episodes)
    (trajectory : StochasticEpisodeBatchTrajectory mdp episodes)
    (rounds : Nat) :
    0 <= source.successorExpectedAverageRegret trajectory rounds := by
  unfold successorExpectedAverageRegret
  exact div_nonneg
    (source.successorExpectedCumulativeRegret_nonneg trajectory rounds)
    (by positivity)

omit [DecidableEq State] [DecidableEq Action]
    [MeasurableSingletonClass Action] [Nonempty State] in
/--
An expected-regret upper bound and a two-sided global return-deviation bound
control the absolute stochastic realized average regret.
-/
theorem abs_realizedSuccessorAverageRegret_le_of_expected_le_of_deviation_abs_le
    {mdp : MDP State Action} {initialState : Measure State}
    [IsProbabilityMeasure initialState] {episodes : Nat}
    (source : AdaptiveStochasticEpisodeBatchSource mdp initialState episodes)
    (trajectory : StochasticEpisodeBatchTrajectory mdp episodes)
    (rounds : Nat) (hrounds : 0 < rounds) (hepisodes : 0 < episodes)
    (expectedBound deviationBound : Real)
    (hexpected :
      source.successorExpectedAverageRegret trajectory rounds <= expectedBound)
    (hdeviation :
      |source.cumulativeSuccessorGlobalReturnDeviation rounds trajectory| <=
        deviationBound) :
    |source.realizedSuccessorAverageRegret trajectory rounds| <=
      expectedBound + deviationBound / ((episodes : Real) * (rounds : Real)) := by
  have hdenom : 0 < (episodes : Real) * (rounds : Real) := by positivity
  rw [source.realizedSuccessorAverageRegret_eq_expected_sub_deviation
    trajectory rounds hrounds hepisodes]
  calc
    |source.successorExpectedAverageRegret trajectory rounds -
        source.cumulativeSuccessorGlobalReturnDeviation rounds trajectory /
          ((episodes : Real) * (rounds : Real))| <=
        |source.successorExpectedAverageRegret trajectory rounds| +
          |source.cumulativeSuccessorGlobalReturnDeviation rounds trajectory /
            ((episodes : Real) * (rounds : Real))| := abs_sub _ _
    _ = source.successorExpectedAverageRegret trajectory rounds +
          |source.cumulativeSuccessorGlobalReturnDeviation rounds trajectory| /
            ((episodes : Real) * (rounds : Real)) := by
      rw [abs_of_nonneg
        (source.successorExpectedAverageRegret_nonneg trajectory rounds),
        abs_div, abs_of_pos hdenom]
    _ <= expectedBound + deviationBound / ((episodes : Real) * (rounds : Real)) :=
      add_le_add hexpected (div_le_div_of_nonneg_right hdeviation hdenom.le)

end AdaptiveStochasticEpisodeBatchSource

namespace AdaptiveCumulativeStochasticEmpiricalOptimisticSource

/--
The stochastic finite-window certificate upgraded to absolute realized regret.
This is the exact finite-window input consumed by convergence in probability.
-/
theorem exploratorySource_trajectoryMeasure_projectedCumulativeInverseSqrtPathSupport_optimism_and_decayingExplorationAverageAbsoluteRealizedBehaviorConsistency_of_standardBorel
    (mdp : MDP State Action) (initialState : Measure State)
    [IsProbabilityMeasure initialState]
    (baseVisitFloor : Real) (n : Nat)
    [StandardBorelSpace State] [StandardBorelSpace Action]
    (rewardSource : mdp.MeanCompatibleRewardKernel)
    (rewardVarianceProxy : NNReal)
    (law : rewardSource.UniformSubgaussianRewardLaw rewardVarianceProxy)
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
    let episodes := AdaptiveEpisodeBatchSource.decayingExplorationScheduledEpisodes
      mdp baseVisitFloor n
    let countRadius :=
      AdaptiveEpisodeBatchSource.normalizedCumulativeInverseSqrtCountRadius
        mdp rounds delta visitFloor
    let source := exploratorySource mdp initialState episodes rewardSource
      initialTable defaultState countRadius explorationRate
        (AdaptiveEpisodeBatchSource.decayingExplorationRate_le_one n)
    let projection :=
      MDP.MeanCompatibleRewardKernel.knownRewardEpisodeBatchTrajectory
        (mdp := mdp) episodes
    let countBadEvent := projectedAdaptiveCumulativeCountBadEvent
      (mdp := mdp) (initialState := initialState) (episodes := episodes)
      initialTable defaultState countRadius explorationRate
        (AdaptiveEpisodeBatchSource.decayingExplorationRate_le_one n)
        rounds delta
    let returnBadEvent := source.successorGlobalReturnDeviationBadEvent
      rounds 1 rewardVarianceProxy delta
    let combinedBadEvent := countBadEvent ∪ returnBadEvent
    MeasurableSet combinedBadEvent /\
      source.trajectoryMeasure combinedBadEvent <=
        AdaptiveStochasticEpisodeBatchSource.decayingExplorationStochasticRealizedFailureBudget n /\
      forall trajectory, trajectory ∉ combinedBadEvent ->
        (forall round : Fin rounds, forall state,
          mdp.optimalValueRemaining mdp.horizon le_rfl state <=
            (adaptiveCumulativeEmpiricalOptimisticPlanAt
              (projection trajectory) defaultState countRadius round
              ).upperValueRemaining mdp.horizon le_rfl state) /\
        |source.realizedSuccessorAverageRegret trajectory rounds| <=
          AdaptiveStochasticEpisodeBatchSource.decayingExplorationStochasticAverageRealizedBehaviorRegretBound
            mdp baseVisitFloor rewardVarianceProxy n := by
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
  let source := exploratorySource mdp initialState episodes rewardSource
    initialTable defaultState countRadius explorationRate
      (AdaptiveEpisodeBatchSource.decayingExplorationRate_le_one n)
  let projection :=
    MDP.MeanCompatibleRewardKernel.knownRewardEpisodeBatchTrajectory
      (mdp := mdp) episodes
  let countBadEvent := projectedAdaptiveCumulativeCountBadEvent
    (mdp := mdp) (initialState := initialState) (episodes := episodes)
    initialTable defaultState countRadius explorationRate
      (AdaptiveEpisodeBatchSource.decayingExplorationRate_le_one n)
      rounds delta
  let returnBadEvent := source.successorGlobalReturnDeviationBadEvent
    rounds 1 rewardVarianceProxy delta
  let combinedBadEvent := countBadEvent ∪ returnBadEvent
  have hfinite :=
    exploratorySource_trajectoryMeasure_projectedCumulativeInverseSqrtPathSupport_optimism_and_decayingExplorationAverageRealizedBehaviorConsistency_of_standardBorel
      mdp initialState baseVisitFloor n rewardSource rewardVarianceProxy law
        initialTable defaultState support hbaseFloor hrewardBound hhorizon
          hbaseVisitFloor
  dsimp only at hfinite
  rcases hfinite with
    ⟨hmeasurable, htail, _hsubset, _hviolationTail, houtsideFinite⟩
  have hcount :=
    exploratorySource_trajectoryMeasure_projectedCumulativeInverseSqrtPathSupport_optimism_and_decayingExplorationAverageExploratoryBehaviorExpectedRegret
      mdp initialState baseVisitFloor n rewardSource initialTable defaultState
        support hbaseFloor hrewardBound hhorizon hbaseVisitFloor
  dsimp only at hcount
  rcases hcount with ⟨_hcountMeasurable, _hcountTail, hcountOutside⟩
  have hrounds : 0 < rounds :=
    AdaptiveEpisodeBatchSource.decayingExplorationRounds_pos mdp n
  have hepisodes : 0 < episodes := by
    unfold episodes AdaptiveEpisodeBatchSource.decayingExplorationScheduledEpisodes
    exact
      AdaptiveEpisodeBatchSource.normalizedCumulativeInverseSqrtScheduledEpisodes_pos
        _ _ _ _
  refine ⟨hmeasurable, htail, ?_⟩
  intro trajectory htrajectory
  have hnotCount : trajectory ∉ countBadEvent := by
    exact fun hmem => htrajectory (Set.mem_union_left returnBadEvent hmem)
  have hnotReturn : trajectory ∉ returnBadEvent := by
    exact fun hmem => htrajectory (Set.mem_union_right countBadEvent hmem)
  have hfiniteGood := houtsideFinite trajectory htrajectory
  have hcountGood := hcountOutside trajectory hnotCount
  have hdeviation :
      |source.cumulativeSuccessorGlobalReturnDeviation rounds trajectory| <=
        Concentration.subGaussianSumConfidenceRadius
          (AdaptiveStochasticEpisodeBatchSource.cumulativeSuccessorGlobalReturnVarianceProxy
            mdp rounds episodes 1 rewardVarianceProxy) delta := by
    have hdeviationLt :
        |source.cumulativeSuccessorGlobalReturnDeviation rounds trajectory| <
          Concentration.subGaussianSumConfidenceRadius
            (AdaptiveStochasticEpisodeBatchSource.cumulativeSuccessorGlobalReturnVarianceProxy
              mdp rounds episodes 1 rewardVarianceProxy) delta := by
      apply lt_of_not_ge
      intro hge
      apply hnotReturn
      simpa [returnBadEvent,
        AdaptiveStochasticEpisodeBatchSource.successorGlobalReturnDeviationBadEvent]
        using hge
    exact hdeviationLt.le
  refine ⟨hfiniteGood.1, ?_⟩
  have habs :=
    source.abs_realizedSuccessorAverageRegret_le_of_expected_le_of_deviation_abs_le
      trajectory rounds hrounds hepisodes
      (AdaptiveEpisodeBatchSource.decayingExplorationAverageExploratoryBehaviorExpectedRegretBound
        mdp baseVisitFloor n)
      (Concentration.subGaussianSumConfidenceRadius
        (AdaptiveStochasticEpisodeBatchSource.cumulativeSuccessorGlobalReturnVarianceProxy
          mdp rounds episodes 1 rewardVarianceProxy) delta)
      hcountGood.2 hdeviation
  simpa [AdaptiveStochasticEpisodeBatchSource.decayingExplorationStochasticAverageRealizedBehaviorRegretBound,
    AdaptiveStochasticEpisodeBatchSource.normalizedSuccessorGlobalReturnConfidenceRadius]
    using habs

/-- One complete scheduled stochastic experiment at every product coordinate. -/
abbrev DecayingExplorationStochasticWindowSpace
    (mdp : MDP State Action) (baseVisitFloor : Real) :=
  (n : Nat) -> StochasticEpisodeBatchTrajectory mdp
    (AdaptiveEpisodeBatchSource.decayingExplorationScheduledEpisodes
      mdp baseVisitFloor n)

/-- The stochastic adaptive source used at schedule coordinate `n`. -/
noncomputable def decayingExplorationStochasticWindowSource
    (mdp : MDP State Action) (initialState : Measure State)
    [IsProbabilityMeasure initialState]
    (rewardSource : mdp.MeanCompatibleRewardKernel)
    (initialTable : DeterministicMarkovPolicyTable mdp)
    (defaultState : State) (baseVisitFloor : Real) (n : Nat) :
    AdaptiveStochasticEpisodeBatchSource mdp initialState
      (AdaptiveEpisodeBatchSource.decayingExplorationScheduledEpisodes
        mdp baseVisitFloor n) :=
  exploratorySource mdp initialState
    (AdaptiveEpisodeBatchSource.decayingExplorationScheduledEpisodes
      mdp baseVisitFloor n)
    rewardSource initialTable defaultState
    (AdaptiveEpisodeBatchSource.normalizedCumulativeInverseSqrtCountRadius
      mdp (AdaptiveEpisodeBatchSource.decayingExplorationRounds mdp n)
      (AdaptiveEpisodeBatchSource.vanishingAverageConfidenceDelta n)
      (AdaptiveEpisodeBatchSource.decayingExplorationVisitFloor
        mdp baseVisitFloor n))
    (AdaptiveEpisodeBatchSource.decayingExplorationRate n)
    (AdaptiveEpisodeBatchSource.decayingExplorationRate_le_one n)

/-- The scheduled stochastic trajectory law at product coordinate `n`. -/
noncomputable def decayingExplorationStochasticWindowMeasure
    (mdp : MDP State Action) (initialState : Measure State)
    [IsProbabilityMeasure initialState]
    (rewardSource : mdp.MeanCompatibleRewardKernel)
    (initialTable : DeterministicMarkovPolicyTable mdp)
    (defaultState : State) (baseVisitFloor : Real) (n : Nat) :
    Measure (StochasticEpisodeBatchTrajectory mdp
      (AdaptiveEpisodeBatchSource.decayingExplorationScheduledEpisodes
        mdp baseVisitFloor n)) :=
  (decayingExplorationStochasticWindowSource mdp initialState rewardSource
    initialTable defaultState baseVisitFloor n).trajectoryMeasure

instance instDecayingExplorationStochasticWindowMeasureIsProbabilityMeasure
    (mdp : MDP State Action) (initialState : Measure State)
    [IsProbabilityMeasure initialState]
    (rewardSource : mdp.MeanCompatibleRewardKernel)
    (initialTable : DeterministicMarkovPolicyTable mdp)
    (defaultState : State) (baseVisitFloor : Real) (n : Nat) :
    IsProbabilityMeasure
      (decayingExplorationStochasticWindowMeasure mdp initialState rewardSource
        initialTable defaultState baseVisitFloor n) := by
  unfold decayingExplorationStochasticWindowMeasure
  infer_instance

/-- Independent product coupling of the complete scheduled stochastic laws. -/
noncomputable def decayingExplorationStochasticCommonMeasure
    (mdp : MDP State Action) (initialState : Measure State)
    [IsProbabilityMeasure initialState]
    (rewardSource : mdp.MeanCompatibleRewardKernel)
    (initialTable : DeterministicMarkovPolicyTable mdp)
    (defaultState : State) (baseVisitFloor : Real) :
    Measure (DecayingExplorationStochasticWindowSpace mdp baseVisitFloor) :=
  Measure.infinitePi fun n =>
    decayingExplorationStochasticWindowMeasure mdp initialState rewardSource
      initialTable defaultState baseVisitFloor n

instance instDecayingExplorationStochasticCommonMeasureIsProbabilityMeasure
    (mdp : MDP State Action) (initialState : Measure State)
    [IsProbabilityMeasure initialState]
    (rewardSource : mdp.MeanCompatibleRewardKernel)
    (initialTable : DeterministicMarkovPolicyTable mdp)
    (defaultState : State) (baseVisitFloor : Real) :
    IsProbabilityMeasure
      (decayingExplorationStochasticCommonMeasure mdp initialState rewardSource
        initialTable defaultState baseVisitFloor) := by
  unfold decayingExplorationStochasticCommonMeasure
  infer_instance

/-- Each common-space coordinate has exactly its scheduled stochastic law. -/
theorem decayingExplorationStochasticCommonMeasure_map_eval
    (mdp : MDP State Action) (initialState : Measure State)
    [IsProbabilityMeasure initialState]
    (rewardSource : mdp.MeanCompatibleRewardKernel)
    (initialTable : DeterministicMarkovPolicyTable mdp)
    (defaultState : State) (baseVisitFloor : Real) (n : Nat) :
    (decayingExplorationStochasticCommonMeasure mdp initialState rewardSource
      initialTable defaultState baseVisitFloor).map (fun omega => omega n) =
      decayingExplorationStochasticWindowMeasure mdp initialState rewardSource
        initialTable defaultState baseVisitFloor n := by
  unfold decayingExplorationStochasticCommonMeasure
  exact Measure.infinitePi_map_eval _ n

/-- Scheduled stochastic realized successor-average regret on the common space. -/
noncomputable def decayingExplorationStochasticRealizedBehaviorRegretProcess
    (mdp : MDP State Action) (initialState : Measure State)
    [IsProbabilityMeasure initialState]
    (rewardSource : mdp.MeanCompatibleRewardKernel)
    (initialTable : DeterministicMarkovPolicyTable mdp)
    (defaultState : State) (baseVisitFloor : Real)
    (n : Nat) (omega : DecayingExplorationStochasticWindowSpace
      mdp baseVisitFloor) : Real :=
  (decayingExplorationStochasticWindowSource mdp initialState rewardSource
    initialTable defaultState baseVisitFloor n).realizedSuccessorAverageRegret
      (omega n) (AdaptiveEpisodeBatchSource.decayingExplorationRounds mdp n)

/-- Every scheduled stochastic regret coordinate is measurable. -/
theorem measurable_decayingExplorationStochasticRealizedBehaviorRegretProcess
    (mdp : MDP State Action) (initialState : Measure State)
    [IsProbabilityMeasure initialState]
    (rewardSource : mdp.MeanCompatibleRewardKernel)
    (initialTable : DeterministicMarkovPolicyTable mdp)
    (defaultState : State) (baseVisitFloor : Real) (n : Nat) :
    Measurable
      (decayingExplorationStochasticRealizedBehaviorRegretProcess mdp
        initialState rewardSource initialTable defaultState baseVisitFloor n) := by
  unfold decayingExplorationStochasticRealizedBehaviorRegretProcess
  exact
    ((decayingExplorationStochasticWindowSource mdp initialState rewardSource
      initialTable defaultState baseVisitFloor n
      ).measurable_realizedSuccessorAverageRegret
        (AdaptiveEpisodeBatchSource.decayingExplorationRounds mdp n)).comp
      (measurable_pi_apply n)

/-- Pull the finite projected-count/global-return union to the common space. -/
noncomputable def decayingExplorationStochasticCommonBadEvent
    (mdp : MDP State Action) (initialState : Measure State)
    [IsProbabilityMeasure initialState]
    (rewardSource : mdp.MeanCompatibleRewardKernel)
    (initialTable : DeterministicMarkovPolicyTable mdp)
    (defaultState : State) (baseVisitFloor : Real)
    (rewardVarianceProxy : NNReal) (n : Nat) :
    Set (DecayingExplorationStochasticWindowSpace mdp baseVisitFloor) :=
  let source := decayingExplorationStochasticWindowSource mdp initialState
    rewardSource initialTable defaultState baseVisitFloor n
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
  (fun omega => omega n) ⁻¹'
    (projectedAdaptiveCumulativeCountBadEvent
      (mdp := mdp) (initialState := initialState) (episodes := episodes)
      initialTable defaultState countRadius explorationRate
        (AdaptiveEpisodeBatchSource.decayingExplorationRate_le_one n)
        rounds delta ∪
      source.successorGlobalReturnDeviationBadEvent
        rounds 1 rewardVarianceProxy delta)

/-- The pulled-back stochastic bad event inherits the finite-window budget. -/
theorem decayingExplorationStochasticCommonMeasure_badEvent_le
    (mdp : MDP State Action) (initialState : Measure State)
    [IsProbabilityMeasure initialState]
    [StandardBorelSpace State] [StandardBorelSpace Action]
    (baseVisitFloor : Real)
    (rewardSource : mdp.MeanCompatibleRewardKernel)
    (rewardVarianceProxy : NNReal)
    (law : rewardSource.UniformSubgaussianRewardLaw rewardVarianceProxy)
    (initialTable : DeterministicMarkovPolicyTable mdp)
    (defaultState : State)
    (support : ExploratoryPathSupport mdp initialState)
    (hbaseFloor : ExploratoryPathUniformVisitFloor support 1 baseVisitFloor)
    (hrewardBound : forall state action, |mdp.reward state action| <= 1)
    (hhorizon : 0 < mdp.horizon) (hbaseVisitFloor : 0 < baseVisitFloor)
    (n : Nat) :
    decayingExplorationStochasticCommonMeasure mdp initialState rewardSource
        initialTable defaultState baseVisitFloor
        (decayingExplorationStochasticCommonBadEvent mdp initialState
          rewardSource initialTable defaultState baseVisitFloor
            rewardVarianceProxy n) <=
      AdaptiveStochasticEpisodeBatchSource.decayingExplorationStochasticRealizedFailureBudget n := by
  have hfinite :=
    exploratorySource_trajectoryMeasure_projectedCumulativeInverseSqrtPathSupport_optimism_and_decayingExplorationAverageAbsoluteRealizedBehaviorConsistency_of_standardBorel
      mdp initialState baseVisitFloor n rewardSource rewardVarianceProxy law
        initialTable defaultState support hbaseFloor hrewardBound hhorizon
          hbaseVisitFloor
  dsimp only at hfinite
  rcases hfinite with ⟨hmeasurable, htail, _houtside⟩
  have hmeasurable' : MeasurableSet
      (projectedAdaptiveCumulativeCountBadEvent
          (mdp := mdp) (initialState := initialState)
          (episodes := AdaptiveEpisodeBatchSource.decayingExplorationScheduledEpisodes
            mdp baseVisitFloor n)
          initialTable defaultState
          (AdaptiveEpisodeBatchSource.normalizedCumulativeInverseSqrtCountRadius
            mdp (AdaptiveEpisodeBatchSource.decayingExplorationRounds mdp n)
            (AdaptiveEpisodeBatchSource.vanishingAverageConfidenceDelta n)
            (AdaptiveEpisodeBatchSource.decayingExplorationVisitFloor
              mdp baseVisitFloor n))
          (AdaptiveEpisodeBatchSource.decayingExplorationRate n)
          (AdaptiveEpisodeBatchSource.decayingExplorationRate_le_one n)
          (AdaptiveEpisodeBatchSource.decayingExplorationRounds mdp n)
          (AdaptiveEpisodeBatchSource.vanishingAverageConfidenceDelta n) ∪
        (decayingExplorationStochasticWindowSource mdp initialState rewardSource
          initialTable defaultState baseVisitFloor n
          ).successorGlobalReturnDeviationBadEvent
            (AdaptiveEpisodeBatchSource.decayingExplorationRounds mdp n)
            1 rewardVarianceProxy
            (AdaptiveEpisodeBatchSource.vanishingAverageConfidenceDelta n)) := by
    simpa [decayingExplorationStochasticWindowSource] using hmeasurable
  unfold decayingExplorationStochasticCommonBadEvent
  dsimp only
  unfold decayingExplorationStochasticCommonMeasure
  rw [(measurePreserving_eval_infinitePi
    (fun k => decayingExplorationStochasticWindowMeasure mdp initialState
      rewardSource initialTable defaultState baseVisitFloor k) n).measure_preimage
        hmeasurable'.nullMeasurableSet]
  simpa [decayingExplorationStochasticWindowMeasure,
    decayingExplorationStochasticWindowSource] using htail

/-- Outside the pulled-back bad event, coordinate `n` has the absolute bound. -/
theorem abs_decayingExplorationStochasticRealizedBehaviorRegretProcess_le_of_not_mem_badEvent
    (mdp : MDP State Action) (initialState : Measure State)
    [IsProbabilityMeasure initialState]
    [StandardBorelSpace State] [StandardBorelSpace Action]
    (baseVisitFloor : Real)
    (rewardSource : mdp.MeanCompatibleRewardKernel)
    (rewardVarianceProxy : NNReal)
    (law : rewardSource.UniformSubgaussianRewardLaw rewardVarianceProxy)
    (initialTable : DeterministicMarkovPolicyTable mdp)
    (defaultState : State)
    (support : ExploratoryPathSupport mdp initialState)
    (hbaseFloor : ExploratoryPathUniformVisitFloor support 1 baseVisitFloor)
    (hrewardBound : forall state action, |mdp.reward state action| <= 1)
    (hhorizon : 0 < mdp.horizon) (hbaseVisitFloor : 0 < baseVisitFloor)
    (n : Nat)
    (omega : DecayingExplorationStochasticWindowSpace mdp baseVisitFloor)
    (homega : omega ∉
      decayingExplorationStochasticCommonBadEvent mdp initialState rewardSource
        initialTable defaultState baseVisitFloor rewardVarianceProxy n) :
    |decayingExplorationStochasticRealizedBehaviorRegretProcess mdp initialState
        rewardSource initialTable defaultState baseVisitFloor n omega| <=
      AdaptiveStochasticEpisodeBatchSource.decayingExplorationStochasticAverageRealizedBehaviorRegretBound
        mdp baseVisitFloor rewardVarianceProxy n := by
  have hfinite :=
    exploratorySource_trajectoryMeasure_projectedCumulativeInverseSqrtPathSupport_optimism_and_decayingExplorationAverageAbsoluteRealizedBehaviorConsistency_of_standardBorel
      mdp initialState baseVisitFloor n rewardSource rewardVarianceProxy law
        initialTable defaultState support hbaseFloor hrewardBound hhorizon
          hbaseVisitFloor
  dsimp only at hfinite
  rcases hfinite with ⟨_hmeasurable, _htail, houtside⟩
  exact (houtside (omega n) (by
    simpa [decayingExplorationStochasticCommonBadEvent] using homega)).2

/--
Terminal theorem: exact stochastic schedule marginals and convergence in
probability of realized successor-average behavior regret to zero.
-/
theorem exploratorySource_decayingExplorationStochasticCommonMeasure_marginals_and_realizedBehaviorRegret_tendstoInMeasure_zero
    (mdp : MDP State Action) (initialState : Measure State)
    [IsProbabilityMeasure initialState]
    [StandardBorelSpace State] [StandardBorelSpace Action]
    (baseVisitFloor : Real)
    (rewardSource : mdp.MeanCompatibleRewardKernel)
    (rewardVarianceProxy : NNReal)
    (law : rewardSource.UniformSubgaussianRewardLaw rewardVarianceProxy)
    (initialTable : DeterministicMarkovPolicyTable mdp)
    (defaultState : State)
    (support : ExploratoryPathSupport mdp initialState)
    (hbaseFloor : ExploratoryPathUniformVisitFloor support 1 baseVisitFloor)
    (hrewardBound : forall state action, |mdp.reward state action| <= 1)
    (hhorizon : 0 < mdp.horizon) (hbaseVisitFloor : 0 < baseVisitFloor) :
    (forall n,
      Measurable
        (decayingExplorationStochasticRealizedBehaviorRegretProcess mdp
          initialState rewardSource initialTable defaultState baseVisitFloor n)) /\
      (forall n,
        (decayingExplorationStochasticCommonMeasure mdp initialState rewardSource
          initialTable defaultState baseVisitFloor).map (fun omega => omega n) =
          decayingExplorationStochasticWindowMeasure mdp initialState
            rewardSource initialTable defaultState baseVisitFloor n) /\
      TendstoInMeasure
        (decayingExplorationStochasticCommonMeasure mdp initialState
          rewardSource initialTable defaultState baseVisitFloor)
        (decayingExplorationStochasticRealizedBehaviorRegretProcess mdp
          initialState rewardSource initialTable defaultState baseVisitFloor)
        atTop (fun _ => 0) := by
  refine ⟨fun n =>
    measurable_decayingExplorationStochasticRealizedBehaviorRegretProcess
      mdp initialState rewardSource initialTable defaultState baseVisitFloor n,
    fun n =>
      decayingExplorationStochasticCommonMeasure_map_eval mdp initialState
        rewardSource initialTable defaultState baseVisitFloor n, ?_⟩
  rw [tendstoInMeasure_iff_dist]
  intro epsilon hepsilon
  have hbound :=
    AdaptiveStochasticEpisodeBatchSource.decayingExplorationStochasticAverageRealizedBehaviorRegretBound_tendsto_zero
      mdp hhorizon baseVisitFloor hbaseVisitFloor rewardVarianceProxy
  have hboundEventually :
      ∀ᶠ n in atTop,
        AdaptiveStochasticEpisodeBatchSource.decayingExplorationStochasticAverageRealizedBehaviorRegretBound
          mdp baseVisitFloor rewardVarianceProxy n < epsilon :=
    (tendsto_order.1 hbound).2 epsilon hepsilon
  apply ENNReal.tendsto_nhds_zero.2
  intro eta heta
  have hfailureEventually :
      ∀ᶠ n in atTop,
        AdaptiveStochasticEpisodeBatchSource.decayingExplorationStochasticRealizedFailureBudget n <= eta :=
    (ENNReal.tendsto_nhds_zero.1
      AdaptiveStochasticEpisodeBatchSource.decayingExplorationStochasticRealizedFailureBudget_tendsto_zero
      eta heta)
  filter_upwards [hboundEventually, hfailureEventually] with n hboundN hfailureN
  calc
    decayingExplorationStochasticCommonMeasure mdp initialState rewardSource
        initialTable defaultState baseVisitFloor
        {omega |
          epsilon <= dist
            (decayingExplorationStochasticRealizedBehaviorRegretProcess mdp
              initialState rewardSource initialTable defaultState
                baseVisitFloor n omega)
            0} <=
      decayingExplorationStochasticCommonMeasure mdp initialState rewardSource
        initialTable defaultState baseVisitFloor
        (decayingExplorationStochasticCommonBadEvent mdp initialState
          rewardSource initialTable defaultState baseVisitFloor
            rewardVarianceProxy n) := by
      apply measure_mono
      intro omega homega
      by_contra hnotBad
      have habs :=
        abs_decayingExplorationStochasticRealizedBehaviorRegretProcess_le_of_not_mem_badEvent
          mdp initialState baseVisitFloor rewardSource rewardVarianceProxy law
          initialTable defaultState support hbaseFloor hrewardBound hhorizon
          hbaseVisitFloor n omega hnotBad
      have hdist :
          epsilon <=
            |decayingExplorationStochasticRealizedBehaviorRegretProcess mdp
              initialState rewardSource initialTable defaultState
                baseVisitFloor n omega| := by
        simpa [Real.dist_eq] using homega
      exact (not_le_of_gt hboundN) (hdist.trans habs)
    _ <= AdaptiveStochasticEpisodeBatchSource.decayingExplorationStochasticRealizedFailureBudget n :=
      decayingExplorationStochasticCommonMeasure_badEvent_le
        mdp initialState baseVisitFloor rewardSource rewardVarianceProxy law
        initialTable defaultState support hbaseFloor hrewardBound hhorizon
        hbaseVisitFloor n
    _ <= eta := hfailureN

end AdaptiveCumulativeStochasticEmpiricalOptimisticSource

end BanditRLProof.FiniteHorizonRL
