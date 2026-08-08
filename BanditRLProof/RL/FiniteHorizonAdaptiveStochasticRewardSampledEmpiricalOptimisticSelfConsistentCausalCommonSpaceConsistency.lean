import BanditRLProof.RL.FiniteHorizonAdaptiveStochasticRewardSampledEmpiricalOptimisticSelfConsistentCausalExplicitRate
import BanditRLProof.RL.FiniteHorizonAdaptiveStochasticRewardCumulativeDecayingExplorationCommonSpaceL1Consistency
import Mathlib.Analysis.PSeries

/-!
# Natural common-space consistency for the heterogeneous causal source

Target theorem route: prove convergence in probability of realized successor-
average regret on the single infinite causal sampled trajectory, rather than
coupling separate finite-window experiments.

The proof uses four compiled surfaces: the heterogeneous trajectory law and
coordinate fibers, actual sampled-model confidence, the exact weighted
realized-regret decomposition, and the successor global-return sub-Gaussian
tail.  Its new ingredients are a summable tail model event, dilution of a
fixed burn-in prefix by the actual successor episode mass, and a return share
that vanishes slowly enough to preserve a vanishing confidence radius.

Regularity is finite nonempty measurable State/Action with measurable
singletons, Standard Borel State/Action, a probability initial law, positive
horizon, reward proxy and base visit floor, bounded mean rewards, a uniform
selected-reward sub-Gaussian law, and the existing full-exploration path floor.

Failure policy: preserve the single causal trajectory, actual coordinate
batch sizes, successor indexing, selected-policy fibers, two-sided global
return event, and exact weighted normalization.  No independence between
coordinates, almost-sure or pathwise convergence, anytime/minimax rate,
state-reachability theorem, or complete UCB-VI claim is inferred.
-/

open Filter MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal ProbabilityTheory Topology BigOperators

namespace BanditRLProof.FiniteHorizonRL

universe u v

variable {State : Type u} {Action : Type v}
    [MeasurableSpace State] [MeasurableSpace Action]
    [Fintype State] [Fintype Action]
    [DecidableEq State] [DecidableEq Action]
    [MeasurableSingletonClass State] [MeasurableSingletonClass Action]
    [Nonempty State] [Nonempty Action]

namespace HeterogeneousAdaptiveStochasticEpisodeBatchSource

omit [DecidableEq State] [DecidableEq Action]
    [MeasurableSingletonClass State] [MeasurableSingletonClass Action]
    [Nonempty State] in
/-- Realized successor cumulative regret is measurable on the causal space. -/
theorem measurable_realizedSuccessorCumulativeRegret
    {mdp : MDP State Action} {initialState : Measure State}
    [IsProbabilityMeasure initialState] {episodes : Nat -> Nat}
    (source : HeterogeneousAdaptiveStochasticEpisodeBatchSource
      mdp initialState episodes) (rounds : Nat) :
    Measurable (fun trajectory =>
      source.realizedSuccessorCumulativeRegret trajectory rounds) := by
  unfold realizedSuccessorCumulativeRegret
  refine Finset.measurable_sum Finset.univ fun round _ => ?_
  exact measurable_const.sub
    ((mdp.measurable_sampledCumulativeRewardSum
      (episodes ((round : Nat) + 1))).comp
        (measurable_pi_apply ((round : Nat) + 1)))

omit [DecidableEq State] [DecidableEq Action]
    [MeasurableSingletonClass State] [MeasurableSingletonClass Action]
    [Nonempty State] in
/-- Realized successor average regret is measurable on the causal space. -/
theorem measurable_realizedSuccessorAverageRegret
    {mdp : MDP State Action} {initialState : Measure State}
    [IsProbabilityMeasure initialState] {episodes : Nat -> Nat}
    (source : HeterogeneousAdaptiveStochasticEpisodeBatchSource
      mdp initialState episodes) (rounds : Nat) :
    Measurable (fun trajectory =>
      source.realizedSuccessorAverageRegret trajectory rounds) := by
  unfold realizedSuccessorAverageRegret
  exact (source.measurable_realizedSuccessorCumulativeRegret rounds).div_const _

omit [DecidableEq State] [DecidableEq Action]
    [MeasurableSingletonClass Action] [Nonempty State] in
/-- A positive-weight sum of selected-policy expected regrets is nonnegative. -/
theorem successorWeightedExpectedCumulativeRegret_nonneg
    {mdp : MDP State Action} {initialState : Measure State}
    [IsProbabilityMeasure initialState] {episodes : Nat -> Nat}
    (source : HeterogeneousAdaptiveStochasticEpisodeBatchSource
      mdp initialState episodes)
    (trajectory : HeterogeneousStochasticEpisodeBatchTrajectory mdp episodes)
    (rounds : Nat) :
    0 <= source.successorWeightedExpectedCumulativeRegret trajectory rounds := by
  unfold successorWeightedExpectedCumulativeRegret
  exact Finset.sum_nonneg fun round _ => mul_nonneg (by positivity)
    ((source.successorPolicyAt trajectory round).expectedRegret_nonneg
      initialState)

omit [DecidableEq State] [DecidableEq Action]
    [MeasurableSingletonClass Action] [Nonempty State] in
/-- The positive-weight successor expected average regret is nonnegative. -/
theorem successorWeightedExpectedAverageRegret_nonneg
    {mdp : MDP State Action} {initialState : Measure State}
    [IsProbabilityMeasure initialState] {episodes : Nat -> Nat}
    (source : HeterogeneousAdaptiveStochasticEpisodeBatchSource
      mdp initialState episodes)
    (trajectory : HeterogeneousStochasticEpisodeBatchTrajectory mdp episodes)
    (rounds : Nat) :
    0 <= source.successorWeightedExpectedAverageRegret trajectory rounds := by
  unfold successorWeightedExpectedAverageRegret
  exact div_nonneg
    (source.successorWeightedExpectedCumulativeRegret_nonneg trajectory rounds)
    (by
      unfold successorEpisodeMass
      exact Finset.sum_nonneg fun _ _ => by positivity)

omit [DecidableEq State] [DecidableEq Action]
    [MeasurableSingletonClass Action] [Nonempty State] in
/--
An expected-regret upper bound and a two-sided global return bound control the
absolute realized regret under the exact heterogeneous successor mass.
-/
theorem abs_realizedSuccessorAverageRegret_le_of_expected_le_of_deviation_abs_le
    {mdp : MDP State Action} {initialState : Measure State}
    [IsProbabilityMeasure initialState] {episodes : Nat -> Nat}
    (source : HeterogeneousAdaptiveStochasticEpisodeBatchSource
      mdp initialState episodes)
    (trajectory : HeterogeneousStochasticEpisodeBatchTrajectory mdp episodes)
    (rounds : Nat) (hmass : 0 < successorEpisodeMass episodes rounds)
    (expectedBound deviationBound : Real)
    (hexpected :
      source.successorWeightedExpectedAverageRegret trajectory rounds <=
        expectedBound)
    (hdeviation :
      |source.cumulativeSuccessorGlobalReturnDeviation rounds trajectory| <=
        deviationBound) :
    |source.realizedSuccessorAverageRegret trajectory rounds| <=
      expectedBound + deviationBound / successorEpisodeMass episodes rounds := by
  rw [source.realizedSuccessorAverageRegret_eq_expected_sub_deviation
    trajectory rounds hmass]
  calc
    |source.successorWeightedExpectedAverageRegret trajectory rounds -
        source.cumulativeSuccessorGlobalReturnDeviation rounds trajectory /
          successorEpisodeMass episodes rounds| <=
      |source.successorWeightedExpectedAverageRegret trajectory rounds| +
        |source.cumulativeSuccessorGlobalReturnDeviation rounds trajectory /
          successorEpisodeMass episodes rounds| := abs_sub _ _
    _ = source.successorWeightedExpectedAverageRegret trajectory rounds +
        |source.cumulativeSuccessorGlobalReturnDeviation rounds trajectory| /
          successorEpisodeMass episodes rounds := by
      rw [abs_of_nonneg
        (source.successorWeightedExpectedAverageRegret_nonneg trajectory rounds),
        abs_div, abs_of_pos hmass]
    _ <= expectedBound + deviationBound /
        successorEpisodeMass episodes rounds :=
      add_le_add hexpected (div_le_div_of_nonneg_right hdeviation hmass.le)

end HeterogeneousAdaptiveStochasticEpisodeBatchSource

namespace AdaptiveStochasticSampledEmpiricalOptimisticSource

omit [DecidableEq State] [DecidableEq Action]
    [MeasurableSingletonClass State] [MeasurableSingletonClass Action]
    [Nonempty State] [Nonempty Action] in
/-- The local count and reward share is an explicit shifted p-series term. -/
theorem selfConsistentScheduledLocalDelta_eq_inv_pow
    (mdp : MDP State Action) (t : Nat) :
    AdaptiveStochasticEpisodeBatchSource.selfConsistentScheduledLocalDelta
        mdp t =
      1 / (((t + 2 : Nat) : Real) ^ (mdp.horizon + 5)) := by
  unfold AdaptiveStochasticEpisodeBatchSource.selfConsistentScheduledLocalDelta
    multiBatchLocalDelta
    AdaptiveEpisodeBatchSource.decayingExplorationRounds
    AdaptiveEpisodeBatchSource.vanishingAverageConfidenceDelta
    AdaptiveEpisodeBatchSource.decayingExplorationScale
  push_cast
  have ht : (0 : Real) < (t : Real) + 2 := by positivity
  field_simp [ne_of_gt ht]
  ring

omit [DecidableEq State] [DecidableEq Action]
    [MeasurableSingletonClass State] [MeasurableSingletonClass Action]
    [Nonempty State] [Nonempty Action] in
/-- Coordinatewise causal model confidence shares are summable. -/
theorem summable_selfConsistentScheduledLocalDelta
    (mdp : MDP State Action) :
    Summable
      (AdaptiveStochasticEpisodeBatchSource.selfConsistentScheduledLocalDelta
        mdp) := by
  rw [show
      AdaptiveStochasticEpisodeBatchSource.selfConsistentScheduledLocalDelta
          mdp =
        fun t => 1 / (((t + 2 : Nat) : Real) ^ (mdp.horizon + 5)) by
    funext t
    exact selfConsistentScheduledLocalDelta_eq_inv_pow mdp t]
  have hp : 1 < mdp.horizon + 5 := by omega
  simpa only [Nat.cast_add, Nat.cast_ofNat] using
    ((summable_nat_add_iff (f := fun n : Nat =>
      1 / ((n : Real) ^ (mdp.horizon + 5))) 2).2
        (Real.summable_one_div_nat_pow.mpr hp))

/-- Two model-confidence shares are charged at every causal coordinate. -/
noncomputable def selfConsistentScheduledCausalCoordinateModelFailureBudget
    (mdp : MDP State Action) (t : Nat) : ENNReal :=
  ENNReal.ofReal
      (AdaptiveStochasticEpisodeBatchSource.selfConsistentScheduledLocalDelta
        mdp t) +
    ENNReal.ofReal
      (AdaptiveStochasticEpisodeBatchSource.selfConsistentScheduledLocalDelta
        mdp t)

/-- Infinite model-confidence budget after deleting a finite burn-in prefix. -/
noncomputable def selfConsistentScheduledCausalTailModelFailureBudget
    (mdp : MDP State Action) (burnin : Nat) : ENNReal :=
  ∑' t : {t // t ∉ Finset.range burnin},
    selfConsistentScheduledCausalCoordinateModelFailureBudget mdp t

omit [DecidableEq State] [DecidableEq Action]
    [MeasurableSingletonClass State] [MeasurableSingletonClass Action]
    [Nonempty State] [Nonempty Action] in
/-- The full coordinatewise model-confidence budget is finite. -/
theorem tsum_selfConsistentScheduledCausalCoordinateModelFailureBudget_ne_top
    (mdp : MDP State Action) :
    ∑' t, selfConsistentScheduledCausalCoordinateModelFailureBudget mdp t ≠ ∞ := by
  have hfinite :
      ∑' t, ENNReal.ofReal
        (AdaptiveStochasticEpisodeBatchSource.selfConsistentScheduledLocalDelta
          mdp t) ≠ ∞ :=
    (summable_selfConsistentScheduledLocalDelta mdp).tsum_ofReal_ne_top
  rw [show (fun t =>
      selfConsistentScheduledCausalCoordinateModelFailureBudget mdp t) =
      fun t =>
        ENNReal.ofReal
            (AdaptiveStochasticEpisodeBatchSource.selfConsistentScheduledLocalDelta
              mdp t) +
          ENNReal.ofReal
            (AdaptiveStochasticEpisodeBatchSource.selfConsistentScheduledLocalDelta
              mdp t) by rfl,
    ENNReal.tsum_add]
  exact ENNReal.add_ne_top.mpr ⟨hfinite, hfinite⟩

omit [DecidableEq State] [DecidableEq Action]
    [MeasurableSingletonClass State] [MeasurableSingletonClass Action]
    [Nonempty State] [Nonempty Action] in
/-- Deleting a growing finite prefix makes the infinite model tail vanish. -/
theorem selfConsistentScheduledCausalTailModelFailureBudget_tendsto_zero
    (mdp : MDP State Action) :
    Tendsto (selfConsistentScheduledCausalTailModelFailureBudget mdp)
      atTop (nhds 0) := by
  simpa [selfConsistentScheduledCausalTailModelFailureBudget] using
    (ENNReal.tendsto_tsum_compl_atTop_zero
      (tsum_selfConsistentScheduledCausalCoordinateModelFailureBudget_ne_top
        mdp)).comp Filter.tendsto_finset_range

/-- The actual sampled-model event at one coordinate of the causal source. -/
noncomputable def selfConsistentScheduledCausalModelRoundBadEvent
    (mdp : MDP State Action) (initialState : Measure State)
    [IsProbabilityMeasure initialState]
    (rewardSource : mdp.MeanCompatibleRewardKernel)
    (initialTable : DeterministicMarkovPolicyTable mdp)
    (defaultState : State) (varianceProxy : NNReal)
    (baseVisitFloor : Real) (t : Nat) :
    Set (HeterogeneousStochasticEpisodeBatchTrajectory mdp
      (fun s =>
        AdaptiveStochasticEpisodeBatchSource.selfConsistentScheduledEpisodes
          mdp varianceProxy baseVisitFloor s)) :=
  let localDelta :=
    AdaptiveStochasticEpisodeBatchSource.selfConsistentScheduledLocalDelta mdp
  let source := selfConsistentScheduledCausalSource mdp initialState
    rewardSource initialTable defaultState varianceProxy baseVisitFloor
  HeterogeneousAdaptiveStochasticEpisodeBatchSource.roundBadEvent
    (source.initialAllCoordinateEmpiricalModelBadEvent varianceProxy
      localDelta localDelta)
    (source.successorAllCoordinateEmpiricalModelBadEvent varianceProxy
      localDelta localDelta) t

/-- Union of all actual sampled-model failures after a finite burn-in. -/
noncomputable def selfConsistentScheduledCausalTailModelBadEvent
    (mdp : MDP State Action) (initialState : Measure State)
    [IsProbabilityMeasure initialState]
    (rewardSource : mdp.MeanCompatibleRewardKernel)
    (initialTable : DeterministicMarkovPolicyTable mdp)
    (defaultState : State) (varianceProxy : NNReal)
    (baseVisitFloor : Real) (burnin : Nat) :
    Set (HeterogeneousStochasticEpisodeBatchTrajectory mdp
      (fun s =>
        AdaptiveStochasticEpisodeBatchSource.selfConsistentScheduledEpisodes
          mdp varianceProxy baseVisitFloor s)) :=
  ⋃ t : {t // t ∉ Finset.range burnin},
    selfConsistentScheduledCausalModelRoundBadEvent mdp initialState
      rewardSource initialTable defaultState varianceProxy baseVisitFloor t

/-- Every concrete causal coordinate model event is measurable. -/
theorem measurableSet_selfConsistentScheduledCausalModelRoundBadEvent
    (mdp : MDP State Action) (initialState : Measure State)
    [IsProbabilityMeasure initialState]
    (rewardSource : mdp.MeanCompatibleRewardKernel)
    (initialTable : DeterministicMarkovPolicyTable mdp)
    (defaultState : State) (varianceProxy : NNReal)
    (baseVisitFloor : Real) (t : Nat) :
    MeasurableSet
      (selfConsistentScheduledCausalModelRoundBadEvent mdp initialState
        rewardSource initialTable defaultState varianceProxy baseVisitFloor t) := by
  let episodes := fun s =>
    AdaptiveStochasticEpisodeBatchSource.selfConsistentScheduledEpisodes
      mdp varianceProxy baseVisitFloor s
  let localDelta :=
    AdaptiveStochasticEpisodeBatchSource.selfConsistentScheduledLocalDelta mdp
  let source := selfConsistentScheduledCausalSource mdp initialState
    rewardSource initialTable defaultState varianceProxy baseVisitFloor
  change MeasurableSet
    (HeterogeneousAdaptiveStochasticEpisodeBatchSource.roundBadEvent
      (source.initialAllCoordinateEmpiricalModelBadEvent varianceProxy
        localDelta localDelta)
      (source.successorAllCoordinateEmpiricalModelBadEvent varianceProxy
        localDelta localDelta) t)
  cases t with
  | zero =>
      exact
        (source.measurableSet_initialAllCoordinateEmpiricalModelBadEvent
          varianceProxy localDelta localDelta).preimage (measurable_pi_apply 0)
  | succ n =>
      exact
        (heterogeneousExploratorySource_measurableSet_successorAllCoordinateEmpiricalModelBadEvent
          (episodes := episodes) rewardSource initialTable defaultState
          (fun s =>
            AdaptiveStochasticEpisodeBatchSource.selfConsistentScheduledRewardBudget
              mdp varianceProxy baseVisitFloor s)
          (fun s =>
            AdaptiveStochasticEpisodeBatchSource.selfConsistentScheduledTransitionBudget
              mdp varianceProxy baseVisitFloor s)
          AdaptiveEpisodeBatchSource.decayingExplorationRate
          AdaptiveEpisodeBatchSource.decayingExplorationRate_le_one
          varianceProxy localDelta localDelta n).preimage (by fun_prop)

/-- The infinite tail event is measurable by countable union. -/
theorem measurableSet_selfConsistentScheduledCausalTailModelBadEvent
    (mdp : MDP State Action) (initialState : Measure State)
    [IsProbabilityMeasure initialState]
    (rewardSource : mdp.MeanCompatibleRewardKernel)
    (initialTable : DeterministicMarkovPolicyTable mdp)
    (defaultState : State) (varianceProxy : NNReal)
    (baseVisitFloor : Real) (burnin : Nat) :
    MeasurableSet
      (selfConsistentScheduledCausalTailModelBadEvent mdp initialState
        rewardSource initialTable defaultState varianceProxy baseVisitFloor
          burnin) := by
  exact MeasurableSet.iUnion fun t =>
    measurableSet_selfConsistentScheduledCausalModelRoundBadEvent mdp
      initialState rewardSource initialTable defaultState varianceProxy
        baseVisitFloor t

/-- One causal coordinate receives its exact pair of local confidence shares. -/
theorem selfConsistentScheduledCausalSource_trajectoryMeasure_modelRoundBadEvent_le
    (mdp : MDP State Action) (initialState : Measure State)
    [IsProbabilityMeasure initialState]
    [StandardBorelSpace State] [StandardBorelSpace Action]
    (rewardSource : mdp.MeanCompatibleRewardKernel)
    (varianceProxy : NNReal) (hvarianceProxy : 0 < varianceProxy)
    (law : rewardSource.UniformSubgaussianRewardLaw varianceProxy)
    (initialTable : DeterministicMarkovPolicyTable mdp)
    (defaultState : State) (baseVisitFloor : Real) (t : Nat) :
    let source := selfConsistentScheduledCausalSource mdp initialState
      rewardSource initialTable defaultState varianceProxy baseVisitFloor
    source.trajectoryMeasure
        (selfConsistentScheduledCausalModelRoundBadEvent mdp initialState
          rewardSource initialTable defaultState varianceProxy baseVisitFloor t) <=
      selfConsistentScheduledCausalCoordinateModelFailureBudget mdp t := by
  dsimp only
  let episodes := fun s =>
    AdaptiveStochasticEpisodeBatchSource.selfConsistentScheduledEpisodes
      mdp varianceProxy baseVisitFloor s
  let localDelta :=
    AdaptiveStochasticEpisodeBatchSource.selfConsistentScheduledLocalDelta mdp
  let source := selfConsistentScheduledCausalSource mdp initialState
    rewardSource initialTable defaultState varianceProxy baseVisitFloor
  have hepisodes : forall s, 0 < episodes s := fun s =>
    AdaptiveStochasticEpisodeBatchSource.selfConsistentScheduledEpisodes_pos
      mdp varianceProxy baseVisitFloor s
  have hlocalDeltaPos : forall s, 0 < localDelta s := fun s =>
    AdaptiveStochasticEpisodeBatchSource.multiBatchLocalDelta_pos_of_pos
      (AdaptiveEpisodeBatchSource.decayingExplorationRounds_pos mdp s)
      (AdaptiveEpisodeBatchSource.vanishingAverageConfidenceDelta_pos s)
  have hlocalDeltaLeOne : forall s, localDelta s <= 1 := fun s =>
    AdaptiveStochasticEpisodeBatchSource.multiBatchLocalDelta_le_one_of_le_one
      (AdaptiveEpisodeBatchSource.decayingExplorationRounds_pos mdp s)
      (AdaptiveEpisodeBatchSource.vanishingAverageConfidenceDelta_le_one s)
  have htotal : forall s,
      0 < ((((episodes s : NNReal) * varianceProxy : NNReal) : Real)) := by
    intro s
    have hepisodesNN : 0 < (episodes s : NNReal) := by
      exact_mod_cast hepisodes s
    exact_mod_cast mul_pos hepisodesNN hvarianceProxy
  change source.trajectoryMeasure
      (HeterogeneousAdaptiveStochasticEpisodeBatchSource.roundBadEvent
        (source.initialAllCoordinateEmpiricalModelBadEvent varianceProxy
          localDelta localDelta)
        (source.successorAllCoordinateEmpiricalModelBadEvent varianceProxy
          localDelta localDelta) t) <=
    ENNReal.ofReal (localDelta t) + ENNReal.ofReal (localDelta t)
  cases t with
  | zero =>
      rw [HeterogeneousAdaptiveStochasticEpisodeBatchSource.roundBadEvent,
        source.trajectoryMeasure_initialBadEvent
          (source.measurableSet_initialAllCoordinateEmpiricalModelBadEvent
            varianceProxy localDelta localDelta)]
      exact source.initialAllCoordinateEmpiricalModelBadEvent_le
        (hepisodes 0) varianceProxy law (htotal 0) localDelta localDelta
        (hlocalDeltaPos 0) (hlocalDeltaLeOne 0)
        (hlocalDeltaPos 0) (hlocalDeltaLeOne 0)
  | succ n =>
      exact source.trajectoryMeasure_successorBadEvent_le n
        (by
          simpa [source, episodes, localDelta,
            selfConsistentScheduledCausalSource] using
            heterogeneousExploratorySource_measurableSet_successorAllCoordinateEmpiricalModelBadEvent
              (episodes := episodes) rewardSource initialTable defaultState
              (fun s =>
                AdaptiveStochasticEpisodeBatchSource.selfConsistentScheduledRewardBudget
                  mdp varianceProxy baseVisitFloor s)
              (fun s =>
                AdaptiveStochasticEpisodeBatchSource.selfConsistentScheduledTransitionBudget
                  mdp varianceProxy baseVisitFloor s)
              AdaptiveEpisodeBatchSource.decayingExplorationRate
              AdaptiveEpisodeBatchSource.decayingExplorationRate_le_one
              varianceProxy localDelta localDelta n)
        (ENNReal.ofReal (localDelta (n + 1)) +
          ENNReal.ofReal (localDelta (n + 1)))
        (fun history =>
          source.successorAllCoordinateEmpiricalModelBadEvent_fiber_le
            varianceProxy law localDelta localDelta n (hepisodes (n + 1))
            (htotal (n + 1)) (hlocalDeltaPos (n + 1))
            (hlocalDeltaLeOne (n + 1)) (hlocalDeltaPos (n + 1))
            (hlocalDeltaLeOne (n + 1)) history)

/-- The actual infinite tail event is controlled by the summable tail budget. -/
theorem selfConsistentScheduledCausalSource_trajectoryMeasure_tailModelBadEvent_le
    (mdp : MDP State Action) (initialState : Measure State)
    [IsProbabilityMeasure initialState]
    [StandardBorelSpace State] [StandardBorelSpace Action]
    (rewardSource : mdp.MeanCompatibleRewardKernel)
    (varianceProxy : NNReal) (hvarianceProxy : 0 < varianceProxy)
    (law : rewardSource.UniformSubgaussianRewardLaw varianceProxy)
    (initialTable : DeterministicMarkovPolicyTable mdp)
    (defaultState : State) (baseVisitFloor : Real) (burnin : Nat) :
    let source := selfConsistentScheduledCausalSource mdp initialState
      rewardSource initialTable defaultState varianceProxy baseVisitFloor
    source.trajectoryMeasure
        (selfConsistentScheduledCausalTailModelBadEvent mdp initialState
          rewardSource initialTable defaultState varianceProxy baseVisitFloor
            burnin) <=
      selfConsistentScheduledCausalTailModelFailureBudget mdp burnin := by
  dsimp only
  let source := selfConsistentScheduledCausalSource mdp initialState
    rewardSource initialTable defaultState varianceProxy baseVisitFloor
  calc
    source.trajectoryMeasure
        (selfConsistentScheduledCausalTailModelBadEvent mdp initialState
          rewardSource initialTable defaultState varianceProxy baseVisitFloor
            burnin) <=
      ∑' t : {t // t ∉ Finset.range burnin},
        source.trajectoryMeasure
          (selfConsistentScheduledCausalModelRoundBadEvent mdp initialState
            rewardSource initialTable defaultState varianceProxy baseVisitFloor
              t) := by
        unfold selfConsistentScheduledCausalTailModelBadEvent
        exact measure_iUnion_le _
    _ <= ∑' t : {t // t ∉ Finset.range burnin},
        selfConsistentScheduledCausalCoordinateModelFailureBudget mdp t :=
      ENNReal.tsum_le_tsum fun t =>
        selfConsistentScheduledCausalSource_trajectoryMeasure_modelRoundBadEvent_le
          mdp initialState rewardSource varianceProxy hvarianceProxy law
            initialTable defaultState baseVisitFloor t
    _ = selfConsistentScheduledCausalTailModelFailureBudget mdp burnin := rfl

/-- Outside the tail event, every coordinate after burn-in is model-good. -/
theorem not_mem_selfConsistentScheduledCausalModelRoundBadEvent_of_not_mem_tail
    (mdp : MDP State Action) (initialState : Measure State)
    [IsProbabilityMeasure initialState]
    (rewardSource : mdp.MeanCompatibleRewardKernel)
    (initialTable : DeterministicMarkovPolicyTable mdp)
    (defaultState : State) (varianceProxy : NNReal)
    (baseVisitFloor : Real) (burnin t : Nat) (hburnin : burnin <= t)
    (trajectory : HeterogeneousStochasticEpisodeBatchTrajectory mdp
      (fun s =>
        AdaptiveStochasticEpisodeBatchSource.selfConsistentScheduledEpisodes
          mdp varianceProxy baseVisitFloor s))
    (htrajectory : trajectory ∉
      selfConsistentScheduledCausalTailModelBadEvent mdp initialState
        rewardSource initialTable defaultState varianceProxy baseVisitFloor
          burnin) :
    trajectory ∉ selfConsistentScheduledCausalModelRoundBadEvent mdp
      initialState rewardSource initialTable defaultState varianceProxy
        baseVisitFloor t := by
  intro hmem
  apply htrajectory
  exact Set.mem_iUnion_of_mem
    ⟨t, by simpa [Finset.mem_range] using hburnin⟩ hmem

/-
The finite-prefix parent contains this proof internally, but the tail argument
needs the certificate from one coordinate without assuming that earlier
coordinates are model-good.
-/
/-- One model-good causal coordinate yields optimism and recommended regret. -/
theorem selfConsistentScheduledCausalSource_coordinateConfidence_of_not_mem_modelRoundBadEvent
    (mdp : MDP State Action) (initialState : Measure State)
    [IsProbabilityMeasure initialState]
    [StandardBorelSpace State] [StandardBorelSpace Action]
    (rewardSource : mdp.MeanCompatibleRewardKernel)
    (varianceProxy : NNReal) (hvarianceProxy : 0 < varianceProxy)
    (law : rewardSource.UniformSubgaussianRewardLaw varianceProxy)
    (initialTable : DeterministicMarkovPolicyTable mdp)
    (defaultState : State)
    (support : ExploratoryPathSupport mdp initialState)
    (baseVisitFloor : Real)
    (hbaseFloor : ExploratoryPathUniformVisitFloor support 1 baseVisitFloor)
    (hrewardBound : forall state action, |mdp.reward state action| <= 1)
    (hhorizon : 0 < mdp.horizon) (hbaseVisitFloor : 0 < baseVisitFloor)
    (trajectory : HeterogeneousStochasticEpisodeBatchTrajectory mdp
      (fun s =>
        AdaptiveStochasticEpisodeBatchSource.selfConsistentScheduledEpisodes
          mdp varianceProxy baseVisitFloor s))
    (t : Nat)
    (hnot : trajectory ∉
      selfConsistentScheduledCausalModelRoundBadEvent mdp initialState
        rewardSource initialTable defaultState varianceProxy baseVisitFloor t) :
    let episodes := fun s =>
      AdaptiveStochasticEpisodeBatchSource.selfConsistentScheduledEpisodes
        mdp varianceProxy baseVisitFloor s
    let rewardBudget := fun s =>
      AdaptiveStochasticEpisodeBatchSource.selfConsistentScheduledRewardBudget
        mdp varianceProxy baseVisitFloor s
    let transitionBudget := fun s =>
      AdaptiveStochasticEpisodeBatchSource.selfConsistentScheduledTransitionBudget
        mdp varianceProxy baseVisitFloor s
    let model := mdp.stochasticAllCoordinateEmpiricalFiniteBatchModel
      (episodes t)
      (mdp.sampledEpisodeBatchOfStochasticTrajectories
        (episodes t) (trajectory t))
      defaultState (rewardBudget t) (transitionBudget t)
    (forall state,
        mdp.optimalValueRemaining mdp.horizon le_rfl state <=
          model.plan.upperValueRemaining mdp.horizon le_rfl state) ∧
      model.plan.optimisticPolicy.expectedRegret initialState <=
        model.plan.optimisticPolicy.occupancySumRemaining
          (fun remaining hremaining state =>
            2 * model.plan.selectedRadiusRemaining remaining hremaining state)
          mdp.horizon le_rfl initialState := by
  dsimp only
  let episodes := fun s =>
    AdaptiveStochasticEpisodeBatchSource.selfConsistentScheduledEpisodes
      mdp varianceProxy baseVisitFloor s
  let localDelta :=
    AdaptiveStochasticEpisodeBatchSource.selfConsistentScheduledLocalDelta mdp
  let rewardBudget := fun s =>
    AdaptiveStochasticEpisodeBatchSource.selfConsistentScheduledRewardBudget
      mdp varianceProxy baseVisitFloor s
  let transitionBudget := fun s =>
    AdaptiveStochasticEpisodeBatchSource.selfConsistentScheduledTransitionBudget
      mdp varianceProxy baseVisitFloor s
  let source := selfConsistentScheduledCausalSource mdp initialState
    rewardSource initialTable defaultState varianceProxy baseVisitFloor
  have hepisodes : forall s, 0 < episodes s := fun s =>
    AdaptiveStochasticEpisodeBatchSource.selfConsistentScheduledEpisodes_pos
      mdp varianceProxy baseVisitFloor s
  have hlocalDeltaPos : forall s, 0 < localDelta s := fun s =>
    AdaptiveStochasticEpisodeBatchSource.multiBatchLocalDelta_pos_of_pos
      (AdaptiveEpisodeBatchSource.decayingExplorationRounds_pos mdp s)
      (AdaptiveEpisodeBatchSource.vanishingAverageConfidenceDelta_pos s)
  have hlocalDeltaLeOne : forall s, localDelta s <= 1 := fun s =>
    AdaptiveStochasticEpisodeBatchSource.multiBatchLocalDelta_le_one_of_le_one
      (AdaptiveEpisodeBatchSource.decayingExplorationRounds_pos mdp s)
      (AdaptiveEpisodeBatchSource.vanishingAverageConfidenceDelta_le_one s)
  have htotal : forall s,
      0 < ((((episodes s : NNReal) * varianceProxy : NNReal) : Real)) := by
    intro s
    have hepisodesNN : 0 < (episodes s : NNReal) := by
      exact_mod_cast hepisodes s
    exact_mod_cast mul_pos hepisodesNN hvarianceProxy
  cases t with
  | zero =>
      have hschedule :=
        AdaptiveStochasticEpisodeBatchSource.selfConsistentScheduled_countMargin_and_halfContraction
          mdp defaultState varianceProxy hhorizon hbaseVisitFloor 0
      have hfixed :=
        initialTable.exploratoryPolicy_iidStochasticTrajectoryFamilyMeasure_allCoordinate_optimism_and_expectedRegret_of_pathSupport_selfConsistentCalibration
          rewardSource initialState
          (AdaptiveEpisodeBatchSource.decayingExplorationRate 0)
          (AdaptiveEpisodeBatchSource.decayingExplorationRate_le_one 0)
          (episodes 0) (hepisodes 0) varianceProxy law (htotal 0)
          (localDelta 0) (hlocalDeltaPos 0) (hlocalDeltaLeOne 0)
          (localDelta 0) (hlocalDeltaPos 0) (hlocalDeltaLeOne 0)
          defaultState 1 hrewardBound support
          (AdaptiveEpisodeBatchSource.decayingExplorationVisitFloor
            mdp baseVisitFloor 0)
          (AdaptiveEpisodeBatchSource.decayingExplorationUniformVisitFloor
            support hbaseFloor 0)
          (by simpa [episodes, localDelta,
            AdaptiveStochasticEpisodeBatchSource.selfConsistentScheduledLocalDelta]
            using hschedule.1)
          (lt_of_le_of_lt
            (by simpa [episodes, localDelta,
              AdaptiveStochasticEpisodeBatchSource.selfConsistentScheduledLocalDelta]
              using hschedule.2)
            (by norm_num))
      have hnot' : trajectory 0 ∉
          rewardSource.stochasticAllCoordinateEmpiricalModelBadEvent
            (initialTable.exploratoryPolicy
              (AdaptiveEpisodeBatchSource.decayingExplorationRate 0)
              (AdaptiveEpisodeBatchSource.decayingExplorationRate_le_one 0))
            initialState (episodes 0) varianceProxy
              (localDelta 0) (localDelta 0) := by
        simpa [selfConsistentScheduledCausalModelRoundBadEvent,
          HeterogeneousAdaptiveStochasticEpisodeBatchSource.roundBadEvent,
          HeterogeneousAdaptiveStochasticEpisodeBatchSource.initialBadEvent,
          HeterogeneousAdaptiveStochasticEpisodeBatchSource.initialAllCoordinateEmpiricalModelBadEvent,
          source, episodes, localDelta, selfConsistentScheduledCausalSource,
          heterogeneousExploratorySource] using hnot
      simpa [episodes, rewardBudget, transitionBudget,
        AdaptiveStochasticEpisodeBatchSource.selfConsistentScheduledRewardBudget,
        AdaptiveStochasticEpisodeBatchSource.selfConsistentScheduledTransitionBudget,
        localDelta] using hfixed.2.2 (trajectory 0) hnot'
  | succ n =>
      let table := heterogeneousSuccessorTable defaultState rewardBudget
        transitionBudget n (Preorder.frestrictLe n trajectory)
      have hschedule :=
        AdaptiveStochasticEpisodeBatchSource.selfConsistentScheduled_countMargin_and_halfContraction
          mdp defaultState varianceProxy hhorizon hbaseVisitFloor (n + 1)
      have hfixed :=
        table.exploratoryPolicy_iidStochasticTrajectoryFamilyMeasure_allCoordinate_optimism_and_expectedRegret_of_pathSupport_selfConsistentCalibration
          rewardSource initialState
          (AdaptiveEpisodeBatchSource.decayingExplorationRate (n + 1))
          (AdaptiveEpisodeBatchSource.decayingExplorationRate_le_one (n + 1))
          (episodes (n + 1)) (hepisodes (n + 1)) varianceProxy law
          (htotal (n + 1))
          (localDelta (n + 1)) (hlocalDeltaPos (n + 1))
          (hlocalDeltaLeOne (n + 1))
          (localDelta (n + 1)) (hlocalDeltaPos (n + 1))
          (hlocalDeltaLeOne (n + 1)) defaultState 1 hrewardBound support
          (AdaptiveEpisodeBatchSource.decayingExplorationVisitFloor
            mdp baseVisitFloor (n + 1))
          (AdaptiveEpisodeBatchSource.decayingExplorationUniformVisitFloor
            support hbaseFloor (n + 1))
          (by simpa [episodes, localDelta,
            AdaptiveStochasticEpisodeBatchSource.selfConsistentScheduledLocalDelta]
            using hschedule.1)
          (lt_of_le_of_lt
            (by simpa [episodes, localDelta,
              AdaptiveStochasticEpisodeBatchSource.selfConsistentScheduledLocalDelta]
              using hschedule.2)
            (by norm_num))
      have hnot' : trajectory (n + 1) ∉
          rewardSource.stochasticAllCoordinateEmpiricalModelBadEvent
            (table.exploratoryPolicy
              (AdaptiveEpisodeBatchSource.decayingExplorationRate (n + 1))
              (AdaptiveEpisodeBatchSource.decayingExplorationRate_le_one
                (n + 1)))
            initialState (episodes (n + 1)) varianceProxy
              (localDelta (n + 1)) (localDelta (n + 1)) := by
        simpa [selfConsistentScheduledCausalModelRoundBadEvent,
          HeterogeneousAdaptiveStochasticEpisodeBatchSource.roundBadEvent,
          HeterogeneousAdaptiveStochasticEpisodeBatchSource.successorBadEvent,
          HeterogeneousAdaptiveStochasticEpisodeBatchSource.successorAllCoordinateEmpiricalModelBadEvent,
          source, table, episodes, rewardBudget, transitionBudget, localDelta,
          selfConsistentScheduledCausalSource, heterogeneousExploratorySource,
          HeterogeneousAdaptiveStochasticEpisodeBatchSource.policyAt] using hnot
      simpa [episodes, rewardBudget, transitionBudget,
        AdaptiveStochasticEpisodeBatchSource.selfConsistentScheduledRewardBudget,
        AdaptiveStochasticEpisodeBatchSource.selfConsistentScheduledTransitionBudget,
        localDelta] using hfixed.2.2 (trajectory (n + 1)) hnot'

/-- The exact local planning budget is bounded by the named vanishing rate. -/
theorem selfConsistentScheduledCausalLocalPlanningBound_le_rateAt
    (mdp : MDP State Action) (varianceProxy : NNReal)
    {baseVisitFloor : Real} (hhorizon : 0 < mdp.horizon)
    (hbaseVisitFloor : 0 < baseVisitFloor) (t : Nat) :
    let rewardBudget :=
      AdaptiveStochasticEpisodeBatchSource.selfConsistentScheduledRewardBudget
        mdp varianceProxy baseVisitFloor
    let transitionBudget :=
      AdaptiveStochasticEpisodeBatchSource.selfConsistentScheduledTransitionBudget
        mdp varianceProxy baseVisitFloor
    (mdp.horizon : Real) *
          (2 * (rewardBudget t + transitionBudget t)) +
        exploratoryBehaviorRegretCharge mdp
          (AdaptiveEpisodeBatchSource.decayingExplorationRate (t + 1)) 1 <=
      selfConsistentScheduledCausalPlanningRateAt mdp t := by
  dsimp only
  have hreward :
      AdaptiveStochasticEpisodeBatchSource.selfConsistentScheduledRewardBudget
          mdp varianceProxy baseVisitFloor t <=
        1 / (AdaptiveEpisodeBatchSource.decayingExplorationScale t : Real) ^ 2 :=
    (AdaptiveStochasticEpisodeBatchSource.selfConsistentScheduledRewardBudget_lt_inv_scale_sq
      mdp varianceProxy hhorizon hbaseVisitFloor t).le
  have htransition :
      AdaptiveStochasticEpisodeBatchSource.selfConsistentScheduledTransitionBudget
          mdp varianceProxy baseVisitFloor t <=
        AdaptiveStochasticEpisodeBatchSource.selfConsistentScheduledTransitionBudgetRateEnvelope
          mdp t :=
    AdaptiveStochasticEpisodeBatchSource.selfConsistentScheduledTransitionBudget_le_rateEnvelope
      mdp varianceProxy hhorizon hbaseVisitFloor t
  have hscaled := mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_left (add_le_add hreward htransition)
      (by norm_num : (0 : Real) <= 2))
    (by positivity : (0 : Real) <= (mdp.horizon : Real))
  unfold selfConsistentScheduledCausalPlanningRateAt
  exact add_le_add hscaled (le_refl _)

/-- Burn-in regret plus the full weighted causal planning-rate average. -/
noncomputable def selfConsistentScheduledCausalBurninExpectedRegretRateEnvelope
    (mdp : MDP State Action) (varianceProxy : NNReal)
    (baseVisitFloor : Real) (burnin rounds : Nat) : Real :=
  let episodes := fun t : Nat =>
    AdaptiveStochasticEpisodeBatchSource.selfConsistentScheduledEpisodes
      mdp varianceProxy baseVisitFloor t
  (2 * (mdp.horizon : Real) *
      HeterogeneousAdaptiveStochasticEpisodeBatchSource.successorEpisodeMass
        episodes burnin) /
      HeterogeneousAdaptiveStochasticEpisodeBatchSource.successorEpisodeMass
        episodes rounds +
    selfConsistentScheduledCausalWeightedPlanningRateEnvelope mdp
      varianceProxy baseVisitFloor rounds

omit [DecidableEq State] [DecidableEq Action]
    [MeasurableSingletonClass State] [MeasurableSingletonClass Action]
    [Nonempty State] [Nonempty Action] in
/-- For fixed burn-in, early regret is diluted and the tail planning rate vanishes. -/
theorem selfConsistentScheduledCausalBurninExpectedRegretRateEnvelope_tendsto_zero
    (mdp : MDP State Action) (varianceProxy : NNReal)
    (baseVisitFloor : Real) (burnin : Nat) :
    Tendsto
      (selfConsistentScheduledCausalBurninExpectedRegretRateEnvelope mdp
        varianceProxy baseVisitFloor burnin) atTop (nhds 0) := by
  let episodes := fun t =>
    AdaptiveStochasticEpisodeBatchSource.selfConsistentScheduledEpisodes
      mdp varianceProxy baseVisitFloor t
  have hmass :=
    HeterogeneousAdaptiveStochasticEpisodeBatchSource.successorEpisodeMass_tendsto_atTop
      episodes (fun t =>
        AdaptiveStochasticEpisodeBatchSource.selfConsistentScheduledEpisodes_pos
          mdp varianceProxy baseVisitFloor t)
  have hearly : Tendsto
      (fun rounds =>
        (2 * (mdp.horizon : Real) *
          HeterogeneousAdaptiveStochasticEpisodeBatchSource.successorEpisodeMass
            episodes burnin) /
          HeterogeneousAdaptiveStochasticEpisodeBatchSource.successorEpisodeMass
            episodes rounds) atTop (nhds 0) :=
    tendsto_const_nhds.div_atTop hmass
  simpa [selfConsistentScheduledCausalBurninExpectedRegretRateEnvelope,
    episodes] using
    hearly.add
      (selfConsistentScheduledCausalWeightedPlanningRateEnvelope_tendsto_zero
        mdp varianceProxy baseVisitFloor)

/-
The tail event ignores finitely many early model failures.  Their selected
policies use the deterministic `2H` mean-regret bound, while every later
coordinate uses its own model certificate and local causal planning rate.
-/
/-- Tail model confidence yields a burn-in-diluted weighted expected regret. -/
theorem selfConsistentScheduledCausalSource_weightedExpectedSuccessorAverageRegret_le_burninEnvelope
    (mdp : MDP State Action) (initialState : Measure State)
    [IsProbabilityMeasure initialState]
    [StandardBorelSpace State] [StandardBorelSpace Action]
    (rewardSource : mdp.MeanCompatibleRewardKernel)
    (varianceProxy : NNReal) (hvarianceProxy : 0 < varianceProxy)
    (law : rewardSource.UniformSubgaussianRewardLaw varianceProxy)
    (initialTable : DeterministicMarkovPolicyTable mdp)
    (defaultState : State)
    (support : ExploratoryPathSupport mdp initialState)
    (baseVisitFloor : Real)
    (hbaseFloor : ExploratoryPathUniformVisitFloor support 1 baseVisitFloor)
    (hrewardBound : forall state action, |mdp.reward state action| <= 1)
    (hhorizon : 0 < mdp.horizon) (hbaseVisitFloor : 0 < baseVisitFloor)
    (burnin rounds : Nat) (hburnin : burnin <= rounds) (hrounds : 0 < rounds)
    (trajectory : HeterogeneousStochasticEpisodeBatchTrajectory mdp
      (fun t =>
        AdaptiveStochasticEpisodeBatchSource.selfConsistentScheduledEpisodes
          mdp varianceProxy baseVisitFloor t))
    (htrajectory : trajectory ∉
      selfConsistentScheduledCausalTailModelBadEvent mdp initialState
        rewardSource initialTable defaultState varianceProxy baseVisitFloor
          burnin) :
    let source := selfConsistentScheduledCausalSource mdp initialState
      rewardSource initialTable defaultState varianceProxy baseVisitFloor
    source.successorWeightedExpectedAverageRegret trajectory rounds <=
      selfConsistentScheduledCausalBurninExpectedRegretRateEnvelope mdp
        varianceProxy baseVisitFloor burnin rounds := by
  dsimp only
  let episodes := fun t =>
    AdaptiveStochasticEpisodeBatchSource.selfConsistentScheduledEpisodes
      mdp varianceProxy baseVisitFloor t
  let rewardBudget := fun t =>
    AdaptiveStochasticEpisodeBatchSource.selfConsistentScheduledRewardBudget
      mdp varianceProxy baseVisitFloor t
  let transitionBudget := fun t =>
    AdaptiveStochasticEpisodeBatchSource.selfConsistentScheduledTransitionBudget
      mdp varianceProxy baseVisitFloor t
  let source := selfConsistentScheduledCausalSource mdp initialState
    rewardSource initialTable defaultState varianceProxy baseVisitFloor
  let expectedAt := fun t =>
    (episodes (t + 1) : Real) *
      (source.successorPolicyAt trajectory t).expectedRegret initialState
  let rateAt := fun t =>
    (episodes (t + 1) : Real) *
      selfConsistentScheduledCausalPlanningRateAt mdp t
  let earlyAt := fun t =>
    (episodes (t + 1) : Real) * (2 * (mdp.horizon : Real))
  have hepisodes : forall t, 0 < episodes t := fun t =>
    AdaptiveStochasticEpisodeBatchSource.selfConsistentScheduledEpisodes_pos
      mdp varianceProxy baseVisitFloor t
  have hmass : 0 <
      HeterogeneousAdaptiveStochasticEpisodeBatchSource.successorEpisodeMass
        episodes rounds :=
    HeterogeneousAdaptiveStochasticEpisodeBatchSource.successorEpisodeMass_pos
      episodes rounds hrounds hepisodes
  have hEarly :
      ∑ t ∈ Finset.range burnin, expectedAt t <=
        ∑ t ∈ Finset.range burnin, earlyAt t := by
    apply Finset.sum_le_sum
    intro t _ht
    exact mul_le_mul_of_nonneg_left
      (MarkovPolicy.expectedRegret_le_two_mul_horizon_of_rewardBound
        (source.successorPolicyAt trajectory t) initialState hrewardBound)
      (by positivity)
  have hTail :
      ∑ t ∈ Finset.Ico burnin rounds, expectedAt t <=
        ∑ t ∈ Finset.Ico burnin rounds, rateAt t := by
    apply Finset.sum_le_sum
    intro t ht
    have htBounds := Finset.mem_Ico.mp ht
    have hnotRound :=
      not_mem_selfConsistentScheduledCausalModelRoundBadEvent_of_not_mem_tail
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor burnin t htBounds.1 trajectory htrajectory
    have hcert :=
      selfConsistentScheduledCausalSource_coordinateConfidence_of_not_mem_modelRoundBadEvent
        mdp initialState rewardSource varianceProxy hvarianceProxy law
          initialTable defaultState support baseVisitFloor hbaseFloor
          hrewardBound hhorizon hbaseVisitFloor trajectory t hnotRound
    dsimp only at hcert
    let model := mdp.stochasticAllCoordinateEmpiricalFiniteBatchModel
      (episodes t)
      (mdp.sampledEpisodeBatchOfStochasticTrajectories
        (episodes t) (trajectory t))
      defaultState (rewardBudget t) (transitionBudget t)
    have hbehavior :
        (source.successorPolicyAt trajectory t).expectedRegret initialState <=
          model.plan.optimisticPolicy.expectedRegret initialState +
            exploratoryBehaviorRegretCharge mdp
              (AdaptiveEpisodeBatchSource.decayingExplorationRate (t + 1)) 1 := by
      simpa [source, episodes, rewardBudget, transitionBudget, model,
        selfConsistentScheduledCausalSource] using
        (heterogeneousExploratorySource_successorPolicyAt_expectedRegret_le
          (episodes := episodes) rewardSource initialTable defaultState
          rewardBudget transitionBudget
          AdaptiveEpisodeBatchSource.decayingExplorationRate
          AdaptiveEpisodeBatchSource.decayingExplorationRate_le_one
          trajectory t 1 hrewardBound)
    have hoccupancy :=
      mdp.stochasticAllCoordinateEmpiricalFiniteBatchModel_occupancySelectedRadiusRemaining_eq
        (initialState := initialState)
        (mdp.sampledEpisodeBatchOfStochasticTrajectories
          (episodes t) (trajectory t))
        defaultState (rewardBudget t) (transitionBudget t)
    have hlocal :
        (source.successorPolicyAt trajectory t).expectedRegret initialState <=
          (mdp.horizon : Real) *
              (2 * (rewardBudget t + transitionBudget t)) +
            exploratoryBehaviorRegretCharge mdp
              (AdaptiveEpisodeBatchSource.decayingExplorationRate (t + 1)) 1 := by
      calc
        (source.successorPolicyAt trajectory t).expectedRegret initialState <=
            model.plan.optimisticPolicy.expectedRegret initialState +
              exploratoryBehaviorRegretCharge mdp
                (AdaptiveEpisodeBatchSource.decayingExplorationRate (t + 1)) 1 :=
          hbehavior
        _ <= model.plan.optimisticPolicy.occupancySumRemaining
                (fun remaining hremaining state =>
                  2 * model.plan.selectedRadiusRemaining
                    remaining hremaining state)
                mdp.horizon le_rfl initialState +
              exploratoryBehaviorRegretCharge mdp
                (AdaptiveEpisodeBatchSource.decayingExplorationRate (t + 1)) 1 :=
          add_le_add hcert.2 (le_refl _)
        _ = (mdp.horizon : Real) *
                (2 * (rewardBudget t + transitionBudget t)) +
              exploratoryBehaviorRegretCharge mdp
                (AdaptiveEpisodeBatchSource.decayingExplorationRate (t + 1)) 1 := by
          simpa [model] using congrArg
            (fun value => value +
              exploratoryBehaviorRegretCharge mdp
                (AdaptiveEpisodeBatchSource.decayingExplorationRate (t + 1)) 1)
            hoccupancy
    have hrate := hlocal.trans
      (selfConsistentScheduledCausalLocalPlanningBound_le_rateAt mdp
        varianceProxy hhorizon hbaseVisitFloor t)
    exact mul_le_mul_of_nonneg_left hrate (by positivity)
  have hrateNonneg : forall t, 0 <= rateAt t := by
    intro t
    dsimp [rateAt]
    apply mul_nonneg (by positivity)
    unfold selfConsistentScheduledCausalPlanningRateAt
    rw [AdaptiveStochasticEpisodeBatchSource.selfConsistentScheduledTransitionBudgetRateEnvelope_eq]
    unfold exploratoryBehaviorRegretCharge
    positivity
  have htailRateLeFull :
      ∑ t ∈ Finset.Ico burnin rounds, rateAt t <=
        ∑ t ∈ Finset.range rounds, rateAt t := by
    have hsplit := Finset.sum_range_add_sum_Ico rateAt hburnin
    have hearlyNonneg : 0 <= ∑ t ∈ Finset.range burnin, rateAt t :=
      Finset.sum_nonneg fun t _ => hrateNonneg t
    calc
      ∑ t ∈ Finset.Ico burnin rounds, rateAt t <=
          (∑ t ∈ Finset.range burnin, rateAt t) +
            ∑ t ∈ Finset.Ico burnin rounds, rateAt t :=
        le_add_of_nonneg_left hearlyNonneg
      _ = ∑ t ∈ Finset.range rounds, rateAt t := hsplit
  have hcum :
      source.successorWeightedExpectedCumulativeRegret trajectory rounds <=
        2 * (mdp.horizon : Real) *
            HeterogeneousAdaptiveStochasticEpisodeBatchSource.successorEpisodeMass
              episodes burnin +
          ∑ t ∈ Finset.range rounds, rateAt t := by
    rw [show source.successorWeightedExpectedCumulativeRegret trajectory rounds =
        ∑ t ∈ Finset.range rounds, expectedAt t by
      unfold HeterogeneousAdaptiveStochasticEpisodeBatchSource.successorWeightedExpectedCumulativeRegret
      exact Fin.sum_univ_eq_sum_range expectedAt rounds]
    calc
      ∑ t ∈ Finset.range rounds, expectedAt t =
          (∑ t ∈ Finset.range burnin, expectedAt t) +
            ∑ t ∈ Finset.Ico burnin rounds, expectedAt t :=
        (Finset.sum_range_add_sum_Ico expectedAt hburnin).symm
      _ <= (∑ t ∈ Finset.range burnin, earlyAt t) +
            ∑ t ∈ Finset.Ico burnin rounds, rateAt t :=
        add_le_add hEarly hTail
      _ <= (∑ t ∈ Finset.range burnin, earlyAt t) +
            ∑ t ∈ Finset.range rounds, rateAt t :=
        add_le_add (le_refl _) htailRateLeFull
      _ = 2 * (mdp.horizon : Real) *
            HeterogeneousAdaptiveStochasticEpisodeBatchSource.successorEpisodeMass
              episodes burnin +
            ∑ t ∈ Finset.range rounds, rateAt t := by
        unfold earlyAt
        rw [← Finset.sum_mul,
          ← HeterogeneousAdaptiveStochasticEpisodeBatchSource.successorEpisodeMass_eq_sum_range]
        ring
  unfold
    HeterogeneousAdaptiveStochasticEpisodeBatchSource.successorWeightedExpectedAverageRegret
    selfConsistentScheduledCausalBurninExpectedRegretRateEnvelope
    selfConsistentScheduledCausalWeightedPlanningRateEnvelope
    natWeightedAverage
  dsimp only
  rw [HeterogeneousAdaptiveStochasticEpisodeBatchSource.successorEpisodeMass_eq_sum_range]
  change source.successorWeightedExpectedCumulativeRegret trajectory rounds /
      (∑ t ∈ Finset.range rounds, (episodes (t + 1) : Real)) <=
    (2 * (mdp.horizon : Real) *
        HeterogeneousAdaptiveStochasticEpisodeBatchSource.successorEpisodeMass
          episodes burnin) /
        (∑ t ∈ Finset.range rounds, (episodes (t + 1) : Real)) +
      (∑ t ∈ Finset.range rounds,
          (episodes (t + 1) : Real) *
            selfConsistentScheduledCausalPlanningRateAt mdp t) /
        (∑ t ∈ Finset.range rounds, (episodes (t + 1) : Real))
  have hdenom : 0 <
      ∑ t ∈ Finset.range rounds, (episodes (t + 1) : Real) := by
    simpa [HeterogeneousAdaptiveStochasticEpisodeBatchSource.successorEpisodeMass_eq_sum_range]
      using hmass
  calc
    source.successorWeightedExpectedCumulativeRegret trajectory rounds /
        (∑ t ∈ Finset.range rounds, (episodes (t + 1) : Real)) <=
      (2 * (mdp.horizon : Real) *
          HeterogeneousAdaptiveStochasticEpisodeBatchSource.successorEpisodeMass
            episodes burnin +
        ∑ t ∈ Finset.range rounds, rateAt t) /
          (∑ t ∈ Finset.range rounds, (episodes (t + 1) : Real)) :=
      div_le_div_of_nonneg_right hcum hdenom.le
    _ = (2 * (mdp.horizon : Real) *
          HeterogeneousAdaptiveStochasticEpisodeBatchSource.successorEpisodeMass
            episodes burnin) /
          (∑ t ∈ Finset.range rounds, (episodes (t + 1) : Real)) +
        (∑ t ∈ Finset.range rounds,
          (episodes (t + 1) : Real) *
            selfConsistentScheduledCausalPlanningRateAt mdp t) /
          (∑ t ∈ Finset.range rounds, (episodes (t + 1) : Real)) := by
      unfold rateAt
      rw [add_div]

/-- Return confidence share adapted to the actual causal successor mass. -/
noncomputable def selfConsistentScheduledCausalVanishingReturnDelta
    (mdp : MDP State Action) (varianceProxy : NNReal)
    (baseVisitFloor : Real) (rounds : Nat) : Real :=
  let episodes := fun t =>
    AdaptiveStochasticEpisodeBatchSource.selfConsistentScheduledEpisodes
      mdp varianceProxy baseVisitFloor t
  Real.exp
    (-Real.sqrt
      (HeterogeneousAdaptiveStochasticEpisodeBatchSource.successorEpisodeMass
        episodes rounds))

omit [DecidableEq State] [DecidableEq Action]
    [MeasurableSingletonClass State] [MeasurableSingletonClass Action]
    [Nonempty State] [Nonempty Action] in
theorem selfConsistentScheduledCausalVanishingReturnDelta_pos
    (mdp : MDP State Action) (varianceProxy : NNReal)
    (baseVisitFloor : Real) (rounds : Nat) :
    0 < selfConsistentScheduledCausalVanishingReturnDelta mdp varianceProxy
      baseVisitFloor rounds := by
  unfold selfConsistentScheduledCausalVanishingReturnDelta
  exact Real.exp_pos _

omit [DecidableEq State] [DecidableEq Action]
    [MeasurableSingletonClass State] [MeasurableSingletonClass Action]
    [Nonempty State] [Nonempty Action] in
theorem selfConsistentScheduledCausalVanishingReturnDelta_le_one
    (mdp : MDP State Action) (varianceProxy : NNReal)
    (baseVisitFloor : Real) (rounds : Nat) :
    selfConsistentScheduledCausalVanishingReturnDelta mdp varianceProxy
      baseVisitFloor rounds <= 1 := by
  unfold selfConsistentScheduledCausalVanishingReturnDelta
  rw [Real.exp_le_one_iff]
  exact neg_nonpos.mpr (Real.sqrt_nonneg _)

omit [DecidableEq State] [DecidableEq Action]
    [MeasurableSingletonClass State] [MeasurableSingletonClass Action]
    [Nonempty State] [Nonempty Action] in
/-- The mass-adapted return failure share tends to zero. -/
theorem selfConsistentScheduledCausalVanishingReturnDelta_tendsto_zero
    (mdp : MDP State Action) (varianceProxy : NNReal)
    (baseVisitFloor : Real) :
    Tendsto
      (selfConsistentScheduledCausalVanishingReturnDelta mdp varianceProxy
        baseVisitFloor) atTop (nhds 0) := by
  let episodes := fun t =>
    AdaptiveStochasticEpisodeBatchSource.selfConsistentScheduledEpisodes
      mdp varianceProxy baseVisitFloor t
  have hmass :=
    HeterogeneousAdaptiveStochasticEpisodeBatchSource.successorEpisodeMass_tendsto_atTop
      episodes (fun t =>
        AdaptiveStochasticEpisodeBatchSource.selfConsistentScheduledEpisodes_pos
          mdp varianceProxy baseVisitFloor t)
  have hsqrt : Tendsto
      (fun rounds => Real.sqrt
        (HeterogeneousAdaptiveStochasticEpisodeBatchSource.successorEpisodeMass
          episodes rounds)) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp hmass
  have hneg : Tendsto
      (fun rounds => (-1 : Real) * Real.sqrt
        (HeterogeneousAdaptiveStochasticEpisodeBatchSource.successorEpisodeMass
          episodes rounds)) atTop atBot :=
    hsqrt.const_mul_atTop_of_neg (by norm_num)
  change Tendsto
    (fun rounds => Real.exp
      (-Real.sqrt
        (HeterogeneousAdaptiveStochasticEpisodeBatchSource.successorEpisodeMass
          episodes rounds))) atTop (nhds 0)
  rw [show (fun rounds => Real.exp
      (-Real.sqrt
        (HeterogeneousAdaptiveStochasticEpisodeBatchSource.successorEpisodeMass
          episodes rounds))) =
      fun rounds => Real.exp
        ((-1 : Real) * Real.sqrt
          (HeterogeneousAdaptiveStochasticEpisodeBatchSource.successorEpisodeMass
            episodes rounds)) by
    funext rounds
    congr 1
    ring]
  exact Real.tendsto_exp_atBot.comp hneg

/-- Explicit normalized return radius for the mass-adapted confidence share. -/
noncomputable def selfConsistentScheduledCausalVanishingReturnRateEnvelope
    (mdp : MDP State Action) (varianceProxy : NNReal)
    (baseVisitFloor : Real) (rounds : Nat) : Real :=
  Real.sqrt
    (2 * (mdp.globalReturnDeviationPerEpisodeVarianceProxy 1 varianceProxy : Real) *
      (Real.log 2 /
          HeterogeneousAdaptiveStochasticEpisodeBatchSource.successorEpisodeMass
            (fun t =>
              AdaptiveStochasticEpisodeBatchSource.selfConsistentScheduledEpisodes
                mdp varianceProxy baseVisitFloor t) rounds +
        1 / Real.sqrt
          (HeterogeneousAdaptiveStochasticEpisodeBatchSource.successorEpisodeMass
            (fun t =>
              AdaptiveStochasticEpisodeBatchSource.selfConsistentScheduledEpisodes
                mdp varianceProxy baseVisitFloor t) rounds)))

omit [DecidableEq State] [DecidableEq Action]
    [MeasurableSingletonClass State] [MeasurableSingletonClass Action]
    [Nonempty State] [Nonempty Action] in
/-- The mass-adapted normalized return radius has the explicit envelope. -/
theorem normalizedSuccessorGlobalReturnConfidenceRadius_vanishingDelta_eq
    (mdp : MDP State Action) (varianceProxy : NNReal)
    (baseVisitFloor : Real) (rounds : Nat) (hrounds : 0 < rounds) :
    let episodes := fun t =>
      AdaptiveStochasticEpisodeBatchSource.selfConsistentScheduledEpisodes
        mdp varianceProxy baseVisitFloor t
    HeterogeneousAdaptiveStochasticEpisodeBatchSource.normalizedSuccessorGlobalReturnConfidenceRadius
        mdp episodes rounds 1 varianceProxy
          (selfConsistentScheduledCausalVanishingReturnDelta mdp varianceProxy
            baseVisitFloor rounds) =
      selfConsistentScheduledCausalVanishingReturnRateEnvelope mdp
        varianceProxy baseVisitFloor rounds := by
  dsimp only
  let episodes := fun t =>
    AdaptiveStochasticEpisodeBatchSource.selfConsistentScheduledEpisodes
      mdp varianceProxy baseVisitFloor t
  let mass :=
    HeterogeneousAdaptiveStochasticEpisodeBatchSource.successorEpisodeMass
      episodes rounds
  have hepisodes : forall t, 0 < episodes t := fun t =>
    AdaptiveStochasticEpisodeBatchSource.selfConsistentScheduledEpisodes_pos
      mdp varianceProxy baseVisitFloor t
  have hmass : 0 < mass :=
    HeterogeneousAdaptiveStochasticEpisodeBatchSource.successorEpisodeMass_pos
      episodes rounds hrounds hepisodes
  rw [HeterogeneousAdaptiveStochasticEpisodeBatchSource.normalizedSuccessorGlobalReturnConfidenceRadius_eq
    mdp episodes rounds 1 varianceProxy
    (selfConsistentScheduledCausalVanishingReturnDelta mdp varianceProxy
      baseVisitFloor rounds) hmass
    (selfConsistentScheduledCausalVanishingReturnDelta_pos mdp varianceProxy
      baseVisitFloor rounds)
    (selfConsistentScheduledCausalVanishingReturnDelta_le_one mdp varianceProxy
      baseVisitFloor rounds)]
  unfold selfConsistentScheduledCausalVanishingReturnRateEnvelope
    selfConsistentScheduledCausalVanishingReturnDelta
  dsimp only
  simp only [episodes]
  change Real.sqrt
      ((2 * (mdp.globalReturnDeviationPerEpisodeVarianceProxy
            1 varianceProxy : Real) *
        Real.log (2 / Real.exp (-Real.sqrt mass))) / mass) =
    Real.sqrt
      (2 * (mdp.globalReturnDeviationPerEpisodeVarianceProxy
            1 varianceProxy : Real) *
        (Real.log 2 / mass + 1 / Real.sqrt mass))
  congr 1
  rw [Real.log_div (by norm_num) (Real.exp_ne_zero _), Real.log_exp]
  have hsqrtPos : 0 < Real.sqrt mass := Real.sqrt_pos.2 hmass
  have hsqrtSq : (Real.sqrt mass) ^ 2 = mass := Real.sq_sqrt hmass.le
  have hfraction :
      (Real.log 2 - -Real.sqrt mass) / mass =
        Real.log 2 / mass + 1 / Real.sqrt mass := by
    field_simp [ne_of_gt hmass, ne_of_gt hsqrtPos]
    nlinarith
  calc
    (2 * (mdp.globalReturnDeviationPerEpisodeVarianceProxy
            1 varianceProxy : Real) *
        (Real.log 2 - -Real.sqrt mass)) / mass =
      2 * (mdp.globalReturnDeviationPerEpisodeVarianceProxy
            1 varianceProxy : Real) *
        ((Real.log 2 - -Real.sqrt mass) / mass) := by ring
    _ = 2 * (mdp.globalReturnDeviationPerEpisodeVarianceProxy
            1 varianceProxy : Real) *
        (Real.log 2 / mass + 1 / Real.sqrt mass) := by rw [hfraction]

omit [DecidableEq State] [DecidableEq Action]
    [MeasurableSingletonClass State] [MeasurableSingletonClass Action]
    [Nonempty State] [Nonempty Action] in
/-- The mass-adapted normalized return radius tends to zero. -/
theorem selfConsistentScheduledCausalVanishingReturnRateEnvelope_tendsto_zero
    (mdp : MDP State Action) (varianceProxy : NNReal)
    (baseVisitFloor : Real) :
    Tendsto
      (selfConsistentScheduledCausalVanishingReturnRateEnvelope mdp
        varianceProxy baseVisitFloor) atTop (nhds 0) := by
  let episodes := fun t =>
    AdaptiveStochasticEpisodeBatchSource.selfConsistentScheduledEpisodes
      mdp varianceProxy baseVisitFloor t
  let mass := fun rounds =>
    HeterogeneousAdaptiveStochasticEpisodeBatchSource.successorEpisodeMass
      episodes rounds
  have hmass : Tendsto mass atTop atTop :=
    HeterogeneousAdaptiveStochasticEpisodeBatchSource.successorEpisodeMass_tendsto_atTop
      episodes (fun t =>
        AdaptiveStochasticEpisodeBatchSource.selfConsistentScheduledEpisodes_pos
          mdp varianceProxy baseVisitFloor t)
  have hsqrtMass : Tendsto (fun rounds => Real.sqrt (mass rounds))
      atTop atTop := Real.tendsto_sqrt_atTop.comp hmass
  have hlog : Tendsto (fun rounds => Real.log 2 / mass rounds)
      atTop (nhds 0) := tendsto_const_nhds.div_atTop hmass
  have hinvSqrt : Tendsto (fun rounds => 1 / Real.sqrt (mass rounds))
      atTop (nhds 0) := tendsto_const_nhds.div_atTop hsqrtMass
  have hinside : Tendsto
      (fun rounds =>
        2 * (mdp.globalReturnDeviationPerEpisodeVarianceProxy
              1 varianceProxy : Real) *
          (Real.log 2 / mass rounds + 1 / Real.sqrt (mass rounds)))
      atTop (nhds 0) := by
    simpa using tendsto_const_nhds.mul (hlog.add hinvSqrt)
  change Tendsto
    (fun rounds => Real.sqrt
      (2 * (mdp.globalReturnDeviationPerEpisodeVarianceProxy
            1 varianceProxy : Real) *
        (Real.log 2 / mass rounds + 1 / Real.sqrt (mass rounds))))
    atTop (nhds 0)
  simpa only [Function.comp_apply, Real.sqrt_zero] using
    (Real.continuous_sqrt.tendsto 0).comp hinside

/-- Tail model event combined with the mass-adapted two-sided return event. -/
noncomputable def selfConsistentScheduledCausalTailModelReturnBadEvent
    (mdp : MDP State Action) (initialState : Measure State)
    [IsProbabilityMeasure initialState]
    (rewardSource : mdp.MeanCompatibleRewardKernel)
    (initialTable : DeterministicMarkovPolicyTable mdp)
    (defaultState : State) (varianceProxy : NNReal)
    (baseVisitFloor : Real) (burnin rounds : Nat) :
    Set (HeterogeneousStochasticEpisodeBatchTrajectory mdp
      (fun t =>
        AdaptiveStochasticEpisodeBatchSource.selfConsistentScheduledEpisodes
          mdp varianceProxy baseVisitFloor t)) :=
  selfConsistentScheduledCausalTailModelBadEvent mdp initialState rewardSource
      initialTable defaultState varianceProxy baseVisitFloor burnin ∪
    selfConsistentScheduledCausalSuccessorReturnBadEvent mdp initialState
      rewardSource initialTable defaultState varianceProxy baseVisitFloor
        rounds
        (selfConsistentScheduledCausalVanishingReturnDelta mdp varianceProxy
          baseVisitFloor rounds)

/-- Exact tail-model plus mass-adapted return failure budget. -/
noncomputable def selfConsistentScheduledCausalTailModelReturnFailureBudget
    (mdp : MDP State Action) (varianceProxy : NNReal)
    (baseVisitFloor : Real) (burnin rounds : Nat) : ENNReal :=
  selfConsistentScheduledCausalTailModelFailureBudget mdp burnin +
    ENNReal.ofReal
      (selfConsistentScheduledCausalVanishingReturnDelta mdp varianceProxy
        baseVisitFloor rounds)

/-- Burn-in expected-regret envelope plus the mass-adapted return radius. -/
noncomputable def selfConsistentScheduledCausalBurninRealizedRegretRateEnvelope
    (mdp : MDP State Action) (varianceProxy : NNReal)
    (baseVisitFloor : Real) (burnin rounds : Nat) : Real :=
  selfConsistentScheduledCausalBurninExpectedRegretRateEnvelope mdp
      varianceProxy baseVisitFloor burnin rounds +
    selfConsistentScheduledCausalVanishingReturnRateEnvelope mdp
      varianceProxy baseVisitFloor rounds

omit [DecidableEq State] [DecidableEq Action]
    [MeasurableSingletonClass State] [MeasurableSingletonClass Action]
    [Nonempty State] [Nonempty Action] in
/-- For fixed burn-in, the complete deterministic realized envelope vanishes. -/
theorem selfConsistentScheduledCausalBurninRealizedRegretRateEnvelope_tendsto_zero
    (mdp : MDP State Action) (varianceProxy : NNReal)
    (baseVisitFloor : Real) (burnin : Nat) :
    Tendsto
      (selfConsistentScheduledCausalBurninRealizedRegretRateEnvelope mdp
        varianceProxy baseVisitFloor burnin) atTop (nhds 0) := by
  unfold selfConsistentScheduledCausalBurninRealizedRegretRateEnvelope
  simpa using
    (selfConsistentScheduledCausalBurninExpectedRegretRateEnvelope_tendsto_zero
      mdp varianceProxy baseVisitFloor burnin).add
    (selfConsistentScheduledCausalVanishingReturnRateEnvelope_tendsto_zero
      mdp varianceProxy baseVisitFloor)

/-
Finite-prefix terminal consumed by convergence in probability.  It differs
from the all-prefix terminal in two places: only coordinates after `burnin`
must be model-good, and the return share depends on actual successor mass.
-/
/-- Tail optimism and absolute realized regret on the natural causal source. -/
theorem selfConsistentScheduledCausalSource_trajectoryMeasure_tail_optimism_and_absoluteRealizedRegret
    (mdp : MDP State Action) (initialState : Measure State)
    [IsProbabilityMeasure initialState]
    [StandardBorelSpace State] [StandardBorelSpace Action]
    (rewardSource : mdp.MeanCompatibleRewardKernel)
    (varianceProxy : NNReal) (hvarianceProxy : 0 < varianceProxy)
    (law : rewardSource.UniformSubgaussianRewardLaw varianceProxy)
    (initialTable : DeterministicMarkovPolicyTable mdp)
    (defaultState : State)
    (support : ExploratoryPathSupport mdp initialState)
    (baseVisitFloor : Real)
    (hbaseFloor : ExploratoryPathUniformVisitFloor support 1 baseVisitFloor)
    (hrewardBound : forall state action, |mdp.reward state action| <= 1)
    (hhorizon : 0 < mdp.horizon) (hbaseVisitFloor : 0 < baseVisitFloor)
    (burnin rounds : Nat) (hburnin : burnin <= rounds) (hrounds : 0 < rounds) :
    let episodes := fun t =>
      AdaptiveStochasticEpisodeBatchSource.selfConsistentScheduledEpisodes
        mdp varianceProxy baseVisitFloor t
    let rewardBudget := fun t =>
      AdaptiveStochasticEpisodeBatchSource.selfConsistentScheduledRewardBudget
        mdp varianceProxy baseVisitFloor t
    let transitionBudget := fun t =>
      AdaptiveStochasticEpisodeBatchSource.selfConsistentScheduledTransitionBudget
        mdp varianceProxy baseVisitFloor t
    let source := selfConsistentScheduledCausalSource mdp initialState
      rewardSource initialTable defaultState varianceProxy baseVisitFloor
    let event := selfConsistentScheduledCausalTailModelReturnBadEvent mdp
      initialState rewardSource initialTable defaultState varianceProxy
        baseVisitFloor burnin rounds
    MeasurableSet event ∧
      source.trajectoryMeasure event <=
        selfConsistentScheduledCausalTailModelReturnFailureBudget mdp
          varianceProxy baseVisitFloor burnin rounds ∧
      forall trajectory, trajectory ∉ event ->
        (forall t, burnin <= t -> t < rounds -> forall state,
          mdp.optimalValueRemaining mdp.horizon le_rfl state <=
            (mdp.stochasticAllCoordinateEmpiricalFiniteBatchModel
              (episodes t)
              (mdp.sampledEpisodeBatchOfStochasticTrajectories
                (episodes t) (trajectory t))
              defaultState (rewardBudget t) (transitionBudget t)).plan.upperValueRemaining
                mdp.horizon le_rfl state) ∧
        |source.realizedSuccessorAverageRegret trajectory rounds| <=
          selfConsistentScheduledCausalBurninRealizedRegretRateEnvelope mdp
            varianceProxy baseVisitFloor burnin rounds := by
  dsimp only
  let episodes := fun t =>
    AdaptiveStochasticEpisodeBatchSource.selfConsistentScheduledEpisodes
      mdp varianceProxy baseVisitFloor t
  let rewardBudget := fun t =>
    AdaptiveStochasticEpisodeBatchSource.selfConsistentScheduledRewardBudget
      mdp varianceProxy baseVisitFloor t
  let transitionBudget := fun t =>
    AdaptiveStochasticEpisodeBatchSource.selfConsistentScheduledTransitionBudget
      mdp varianceProxy baseVisitFloor t
  let source := selfConsistentScheduledCausalSource mdp initialState
    rewardSource initialTable defaultState varianceProxy baseVisitFloor
  let modelEvent := selfConsistentScheduledCausalTailModelBadEvent mdp
    initialState rewardSource initialTable defaultState varianceProxy
      baseVisitFloor burnin
  let returnDelta := selfConsistentScheduledCausalVanishingReturnDelta mdp
    varianceProxy baseVisitFloor rounds
  let returnEvent := selfConsistentScheduledCausalSuccessorReturnBadEvent mdp
    initialState rewardSource initialTable defaultState varianceProxy
      baseVisitFloor rounds returnDelta
  let event := selfConsistentScheduledCausalTailModelReturnBadEvent mdp
    initialState rewardSource initialTable defaultState varianceProxy
      baseVisitFloor burnin rounds
  letI : source.GlobalReturnMeasurability := by
    dsimp [source, selfConsistentScheduledCausalSource]
    infer_instance
  have hepisodes : forall t, 0 < episodes t := fun t =>
    AdaptiveStochasticEpisodeBatchSource.selfConsistentScheduledEpisodes_pos
      mdp varianceProxy baseVisitFloor t
  have hmass : 0 <
      HeterogeneousAdaptiveStochasticEpisodeBatchSource.successorEpisodeMass
        episodes rounds :=
    HeterogeneousAdaptiveStochasticEpisodeBatchSource.successorEpisodeMass_pos
      episodes rounds hrounds hepisodes
  have htotal : 0 <
      ((HeterogeneousAdaptiveStochasticEpisodeBatchSource.cumulativeSuccessorGlobalReturnVarianceProxy
        mdp episodes rounds 1 varianceProxy : NNReal) : Real) :=
    HeterogeneousAdaptiveStochasticEpisodeBatchSource.cumulativeSuccessorGlobalReturnVarianceProxy_pos
      mdp episodes rounds 1 varianceProxy hrounds hepisodes hhorizon
        hvarianceProxy
  have hmodelMeasurable : MeasurableSet modelEvent := by
    simpa [modelEvent] using
      measurableSet_selfConsistentScheduledCausalTailModelBadEvent mdp
        initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor burnin
  have hmodelTail : source.trajectoryMeasure modelEvent <=
      selfConsistentScheduledCausalTailModelFailureBudget mdp burnin := by
    simpa [source, modelEvent] using
      selfConsistentScheduledCausalSource_trajectoryMeasure_tailModelBadEvent_le
        mdp initialState rewardSource varianceProxy hvarianceProxy law
          initialTable defaultState baseVisitFloor burnin
  have hreturnMeasurable : MeasurableSet returnEvent := by
    simpa [source, returnEvent,
      selfConsistentScheduledCausalSuccessorReturnBadEvent] using
      source.measurableSet_successorGlobalReturnDeviationBadEvent
        rounds 1 varianceProxy returnDelta
  have hrewardBoundNN : forall state action,
      |mdp.reward state action| <= ((1 : NNReal) : Real) := by
    simpa using hrewardBound
  have hreturnTail : source.trajectoryMeasure returnEvent <=
      ENNReal.ofReal returnDelta := by
    simpa [source, returnEvent,
      selfConsistentScheduledCausalSuccessorReturnBadEvent] using
      source.trajectoryMeasure_successorGlobalReturnDeviationBadEvent_le
        rounds 1 varianceProxy hrewardBoundNN law htotal returnDelta
        (selfConsistentScheduledCausalVanishingReturnDelta_pos mdp varianceProxy
          baseVisitFloor rounds)
        (selfConsistentScheduledCausalVanishingReturnDelta_le_one mdp
          varianceProxy baseVisitFloor rounds)
  have hevent : event = modelEvent ∪ returnEvent := by
    rfl
  refine ⟨?_, ?_, ?_⟩
  · simpa [event, modelEvent, returnEvent,
      selfConsistentScheduledCausalTailModelReturnBadEvent,
      selfConsistentScheduledCausalSuccessorReturnBadEvent] using
      hmodelMeasurable.union hreturnMeasurable
  · simpa [source, event, modelEvent, returnEvent, returnDelta,
      selfConsistentScheduledCausalTailModelReturnBadEvent,
      selfConsistentScheduledCausalTailModelReturnFailureBudget,
      selfConsistentScheduledCausalSuccessorReturnBadEvent] using
      (measure_union_le modelEvent returnEvent).trans
        (add_le_add hmodelTail hreturnTail)
  · intro trajectory htrajectory
    have hnotModel : trajectory ∉ modelEvent := by
      intro hmem
      apply htrajectory
      simpa [event, modelEvent, returnEvent,
        selfConsistentScheduledCausalTailModelReturnBadEvent,
        selfConsistentScheduledCausalSuccessorReturnBadEvent] using
        Set.mem_union_left returnEvent hmem
    have hnotReturn : trajectory ∉ returnEvent := by
      intro hmem
      apply htrajectory
      simpa [event, modelEvent, returnEvent,
        selfConsistentScheduledCausalTailModelReturnBadEvent,
        selfConsistentScheduledCausalSuccessorReturnBadEvent] using
        Set.mem_union_right modelEvent hmem
    refine ⟨?_, ?_⟩
    · intro t htBurnin _htRounds state
      have hnotRound :=
        not_mem_selfConsistentScheduledCausalModelRoundBadEvent_of_not_mem_tail
          mdp initialState rewardSource initialTable defaultState varianceProxy
            baseVisitFloor burnin t htBurnin trajectory
            (by simpa [modelEvent] using hnotModel)
      exact
        (selfConsistentScheduledCausalSource_coordinateConfidence_of_not_mem_modelRoundBadEvent
          mdp initialState rewardSource varianceProxy hvarianceProxy law
            initialTable defaultState support baseVisitFloor hbaseFloor
            hrewardBound hhorizon hbaseVisitFloor trajectory t hnotRound).1 state
    · have hexpected :=
        selfConsistentScheduledCausalSource_weightedExpectedSuccessorAverageRegret_le_burninEnvelope
          mdp initialState rewardSource varianceProxy hvarianceProxy law
            initialTable defaultState support baseVisitFloor hbaseFloor
            hrewardBound hhorizon hbaseVisitFloor burnin rounds hburnin hrounds
            trajectory (by simpa [modelEvent] using hnotModel)
      have hdeviation :
          |source.cumulativeSuccessorGlobalReturnDeviation rounds trajectory| <=
            Concentration.subGaussianSumConfidenceRadius
              (HeterogeneousAdaptiveStochasticEpisodeBatchSource.cumulativeSuccessorGlobalReturnVarianceProxy
                mdp episodes rounds 1 varianceProxy) returnDelta := by
        have hlt :
            |source.cumulativeSuccessorGlobalReturnDeviation rounds trajectory| <
              Concentration.subGaussianSumConfidenceRadius
                (HeterogeneousAdaptiveStochasticEpisodeBatchSource.cumulativeSuccessorGlobalReturnVarianceProxy
                  mdp episodes rounds 1 varianceProxy) returnDelta := by
          exact lt_of_not_ge (by simpa [returnEvent,
            selfConsistentScheduledCausalSuccessorReturnBadEvent,
            HeterogeneousAdaptiveStochasticEpisodeBatchSource.successorGlobalReturnDeviationBadEvent]
            using hnotReturn)
        exact hlt.le
      have habs :=
        source.abs_realizedSuccessorAverageRegret_le_of_expected_le_of_deviation_abs_le
          trajectory rounds hmass
          (selfConsistentScheduledCausalBurninExpectedRegretRateEnvelope mdp
            varianceProxy baseVisitFloor burnin rounds)
          (Concentration.subGaussianSumConfidenceRadius
            (HeterogeneousAdaptiveStochasticEpisodeBatchSource.cumulativeSuccessorGlobalReturnVarianceProxy
              mdp episodes rounds 1 varianceProxy) returnDelta)
          hexpected hdeviation
      have habsNormalized :
          |source.realizedSuccessorAverageRegret trajectory rounds| <=
            selfConsistentScheduledCausalBurninExpectedRegretRateEnvelope mdp
                varianceProxy baseVisitFloor burnin rounds +
              HeterogeneousAdaptiveStochasticEpisodeBatchSource.normalizedSuccessorGlobalReturnConfidenceRadius
                mdp episodes rounds 1 varianceProxy returnDelta := by
        simpa [HeterogeneousAdaptiveStochasticEpisodeBatchSource.normalizedSuccessorGlobalReturnConfidenceRadius]
          using habs
      rw [show
        HeterogeneousAdaptiveStochasticEpisodeBatchSource.normalizedSuccessorGlobalReturnConfidenceRadius
            mdp episodes rounds 1 varianceProxy returnDelta =
          selfConsistentScheduledCausalVanishingReturnRateEnvelope mdp
            varianceProxy baseVisitFloor rounds by
        simpa [returnDelta, episodes] using
          normalizedSuccessorGlobalReturnConfidenceRadius_vanishingDelta_eq
            mdp varianceProxy baseVisitFloor rounds hrounds] at habsNormalized
      simpa [selfConsistentScheduledCausalBurninRealizedRegretRateEnvelope]
        using habsNormalized

/-- Realized successor-average regret process on one natural causal trajectory. -/
noncomputable def selfConsistentScheduledNaturalCausalRealizedRegretProcess
    (mdp : MDP State Action) (initialState : Measure State)
    [IsProbabilityMeasure initialState]
    (rewardSource : mdp.MeanCompatibleRewardKernel)
    (initialTable : DeterministicMarkovPolicyTable mdp)
    (defaultState : State) (varianceProxy : NNReal)
    (baseVisitFloor : Real) (rounds : Nat) :
    HeterogeneousStochasticEpisodeBatchTrajectory mdp
        (fun t =>
          AdaptiveStochasticEpisodeBatchSource.selfConsistentScheduledEpisodes
            mdp varianceProxy baseVisitFloor t) -> Real :=
  let source := selfConsistentScheduledCausalSource mdp initialState
    rewardSource initialTable defaultState varianceProxy baseVisitFloor
  fun trajectory => source.realizedSuccessorAverageRegret trajectory rounds

/-- Every coordinate of the natural causal regret process is measurable. -/
theorem measurable_selfConsistentScheduledNaturalCausalRealizedRegretProcess
    (mdp : MDP State Action) (initialState : Measure State)
    [IsProbabilityMeasure initialState]
    (rewardSource : mdp.MeanCompatibleRewardKernel)
    (initialTable : DeterministicMarkovPolicyTable mdp)
    (defaultState : State) (varianceProxy : NNReal)
    (baseVisitFloor : Real) (rounds : Nat) :
    Measurable
      (selfConsistentScheduledNaturalCausalRealizedRegretProcess mdp
        initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor rounds) := by
  let source := selfConsistentScheduledCausalSource mdp initialState
    rewardSource initialTable defaultState varianceProxy baseVisitFloor
  simpa [selfConsistentScheduledNaturalCausalRealizedRegretProcess, source] using
    source.measurable_realizedSuccessorAverageRegret rounds

/-
Terminal route theorem.  The burn-in is chosen only inside the epsilon/eta
proof: its model tail receives half the requested probability tolerance, while
the mass-adapted return share eventually receives the other half.  For that
fixed burn-in, the deterministic absolute-regret envelope tends to zero.
-/
/-- Natural causal realized successor-average regret converges in probability. -/
theorem selfConsistentScheduledCausalSource_realizedRegret_tendstoInMeasure_zero
    (mdp : MDP State Action) (initialState : Measure State)
    [IsProbabilityMeasure initialState]
    [StandardBorelSpace State] [StandardBorelSpace Action]
    (rewardSource : mdp.MeanCompatibleRewardKernel)
    (varianceProxy : NNReal) (hvarianceProxy : 0 < varianceProxy)
    (law : rewardSource.UniformSubgaussianRewardLaw varianceProxy)
    (initialTable : DeterministicMarkovPolicyTable mdp)
    (defaultState : State)
    (support : ExploratoryPathSupport mdp initialState)
    (baseVisitFloor : Real)
    (hbaseFloor : ExploratoryPathUniformVisitFloor support 1 baseVisitFloor)
    (hrewardBound : forall state action, |mdp.reward state action| <= 1)
    (hhorizon : 0 < mdp.horizon) (hbaseVisitFloor : 0 < baseVisitFloor) :
    let source := selfConsistentScheduledCausalSource mdp initialState
      rewardSource initialTable defaultState varianceProxy baseVisitFloor
    (forall rounds,
      Measurable
        (selfConsistentScheduledNaturalCausalRealizedRegretProcess mdp
          initialState rewardSource initialTable defaultState varianceProxy
            baseVisitFloor rounds)) ∧
      TendstoInMeasure source.trajectoryMeasure
        (selfConsistentScheduledNaturalCausalRealizedRegretProcess mdp
          initialState rewardSource initialTable defaultState varianceProxy
            baseVisitFloor) atTop (fun _ => 0) := by
  dsimp only
  let source := selfConsistentScheduledCausalSource mdp initialState
    rewardSource initialTable defaultState varianceProxy baseVisitFloor
  refine ⟨fun rounds =>
    measurable_selfConsistentScheduledNaturalCausalRealizedRegretProcess mdp
      initialState rewardSource initialTable defaultState varianceProxy
        baseVisitFloor rounds, ?_⟩
  rw [tendstoInMeasure_iff_dist]
  intro epsilon hepsilon
  apply ENNReal.tendsto_nhds_zero.2
  intro eta heta
  have htailEventually :
      ∀ᶠ burnin in atTop,
        selfConsistentScheduledCausalTailModelFailureBudget mdp burnin <=
          eta / 2 :=
    (ENNReal.tendsto_nhds_zero.1
      (selfConsistentScheduledCausalTailModelFailureBudget_tendsto_zero mdp)
      (eta / 2) (ENNReal.half_pos heta.ne'))
  obtain ⟨burnin, htailBurnin⟩ := htailEventually.exists
  have hboundEventually :
      ∀ᶠ rounds in atTop,
        selfConsistentScheduledCausalBurninRealizedRegretRateEnvelope mdp
          varianceProxy baseVisitFloor burnin rounds < epsilon :=
    (tendsto_order.1
      (selfConsistentScheduledCausalBurninRealizedRegretRateEnvelope_tendsto_zero
        mdp varianceProxy baseVisitFloor burnin)).2 epsilon hepsilon
  have hreturnFailureTendsto : Tendsto
      (fun rounds => ENNReal.ofReal
        (selfConsistentScheduledCausalVanishingReturnDelta mdp varianceProxy
          baseVisitFloor rounds)) atTop (nhds 0) :=
    by
      simpa only [ENNReal.ofReal_zero] using
        ENNReal.tendsto_ofReal
          (selfConsistentScheduledCausalVanishingReturnDelta_tendsto_zero mdp
            varianceProxy baseVisitFloor)
  have hreturnFailureEventually :
      ∀ᶠ rounds in atTop,
        ENNReal.ofReal
            (selfConsistentScheduledCausalVanishingReturnDelta mdp varianceProxy
              baseVisitFloor rounds) <=
          eta / 2 :=
    (ENNReal.tendsto_nhds_zero.1 hreturnFailureTendsto
      (eta / 2) (ENNReal.half_pos heta.ne'))
  filter_upwards [eventually_ge_atTop (max burnin 1), hboundEventually,
    hreturnFailureEventually] with rounds hroundsLarge hbound hreturnFailure
  have hburnin : burnin <= rounds := le_trans (Nat.le_max_left _ _) hroundsLarge
  have hrounds : 0 < rounds := lt_of_lt_of_le (by omega : 0 < max burnin 1)
    hroundsLarge
  have hfinite :=
    selfConsistentScheduledCausalSource_trajectoryMeasure_tail_optimism_and_absoluteRealizedRegret
      mdp initialState rewardSource varianceProxy hvarianceProxy law
        initialTable defaultState support baseVisitFloor hbaseFloor hrewardBound
        hhorizon hbaseVisitFloor burnin rounds hburnin hrounds
  dsimp only at hfinite
  calc
    source.trajectoryMeasure
        {trajectory |
          epsilon <= dist
            (selfConsistentScheduledNaturalCausalRealizedRegretProcess mdp
              initialState rewardSource initialTable defaultState varianceProxy
                baseVisitFloor rounds trajectory) 0} <=
      source.trajectoryMeasure
        (selfConsistentScheduledCausalTailModelReturnBadEvent mdp initialState
          rewardSource initialTable defaultState varianceProxy baseVisitFloor
            burnin rounds) := by
      apply measure_mono
      intro trajectory hdistance
      by_contra hnotEvent
      have habs := (hfinite.2.2 trajectory hnotEvent).2
      have hdistanceAbs :
          epsilon <= |source.realizedSuccessorAverageRegret trajectory rounds| := by
        simpa [selfConsistentScheduledNaturalCausalRealizedRegretProcess,
          source, Real.dist_eq] using hdistance
      exact (not_le_of_gt hbound) (hdistanceAbs.trans habs)
    _ <= selfConsistentScheduledCausalTailModelReturnFailureBudget mdp
        varianceProxy baseVisitFloor burnin rounds := hfinite.2.1
    _ <= eta / 2 + eta / 2 :=
      add_le_add htailBurnin hreturnFailure
    _ = eta := ENNReal.add_halves eta

end AdaptiveStochasticSampledEmpiricalOptimisticSource

end BanditRLProof.FiniteHorizonRL
