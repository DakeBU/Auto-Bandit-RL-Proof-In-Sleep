import BanditRLProof.RL.FiniteHorizonAdaptiveStochasticRewardSampledEmpiricalOptimisticSelfConsistentExplicitRate
import BanditRLProof.RL.FiniteHorizonAdaptiveStochasticRewardCumulativeDecayingExplorationCommonSpaceConsistency

/-!
# Common-space consistency for actual-sampled self-consistent optimism

Target theorem route: place the complete actual-sampled scheduled experiments
on one exact-marginal dependent product space and prove that realized successor-
average regret converges to zero in Mathlib `TendstoInMeasure`.

Supporting obligations are:

1. strengthen the finite-window terminal from a one-sided realized bound to an
   absolute bound using the model-good expected-regret certificate and the
   return-good two-sided deviation certificate;
2. construct the scheduled window source/law and its `Measure.infinitePi`
   coupling;
3. transport the measurable bad event and regret bound through coordinate
   evaluation; and
4. squeeze the distance event by the explicit failure and regret envelopes.

Local APIs/imports are the compiled self-consistent explicit-rate terminal,
the self-consistent expected-regret occupancy identity, the stochastic realized
decomposition, `Measure.infinitePi_map_eval`,
`measurePreserving_eval_infinitePi`, and `tendstoInMeasure_iff_dist`.
Retrieval found no existing actual-sampled self-consistent common-space route;
the general evidence is project-local plus `MLIB-PROBABILITY-KERNEL`,
`MLIB-MEASURE-INTEGRAL`, `MLIB-METRIC-TOPOLOGY`, and `MLIB-ASYMPTOTICS`.

Regularity is unchanged from the finite terminal: finite nonempty measurable
State/Action with equality and measurable singletons, Standard Borel
State/Action, a probability initial law, positive horizon/base floor/reward
proxy, a uniform selected-reward sub-Gaussian law, bounded means, and a full-
exploration path floor.

Failure policy: preserve actual sampled rewards, successor indexing, initial
batch exclusion, all three confidence shares, global centering, and
`episodes * rounds` normalization. The product coupling below has exact window
marginals but is intentionally independent across complete windows. It is not
a nested causal stream and proves no pathwise, almost-sure, anytime, minimax,
state-reachability, or complete-UCB-VI claim.
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

namespace AdaptiveStochasticSampledEmpiricalOptimisticSource

/-
This theorem deliberately reuses the same finite bad event as the compiled
explicit-rate terminal. The extra work is to recover a two-sided realized
certificate rather than treating the one-sided terminal as an absolute bound.
-/

/-- Actual-sampled optimism and an absolute realized-regret explicit rate. -/
theorem exploratorySource_trajectoryMeasure_selfConsistentScheduledExplicitRate_allCoordinateConfidence_optimism_and_absoluteRealizedSuccessorAverageRegret
    (mdp : MDP State Action) (initialState : Measure State)
    [IsProbabilityMeasure initialState]
    [StandardBorelSpace State] [StandardBorelSpace Action]
    (baseVisitFloor : Real) (n : Nat)
    (rewardSource : mdp.MeanCompatibleRewardKernel)
    (varianceProxy : NNReal) (hvarianceProxy : 0 < varianceProxy)
    (law : rewardSource.UniformSubgaussianRewardLaw varianceProxy)
    (initialTable : DeterministicMarkovPolicyTable mdp) (defaultState : State)
    (support : ExploratoryPathSupport mdp initialState)
    (hbaseFloor : ExploratoryPathUniformVisitFloor support 1 baseVisitFloor)
    (hrewardBound : forall state action, |mdp.reward state action| <= 1)
    (hhorizon : 0 < mdp.horizon) (hbaseVisitFloor : 0 < baseVisitFloor) :
    let rounds := AdaptiveEpisodeBatchSource.decayingExplorationRounds mdp n
    let delta := AdaptiveEpisodeBatchSource.vanishingAverageConfidenceDelta n
    let explorationRate := AdaptiveEpisodeBatchSource.decayingExplorationRate n
    let episodes :=
      AdaptiveStochasticEpisodeBatchSource.selfConsistentScheduledEpisodes
        mdp varianceProxy baseVisitFloor n
    let rewardBudget :=
      AdaptiveStochasticEpisodeBatchSource.selfConsistentScheduledRewardBudget
        mdp varianceProxy baseVisitFloor n
    let transitionBudget :=
      AdaptiveStochasticEpisodeBatchSource.selfConsistentScheduledTransitionBudget
        mdp varianceProxy baseVisitFloor n
    let source := exploratorySource mdp initialState episodes rewardSource
      initialTable defaultState rewardBudget transitionBudget explorationRate
        (AdaptiveEpisodeBatchSource.decayingExplorationRate_le_one n)
    let modelBadEvent := source.adaptiveAllCoordinateEmpiricalModelBadEvent
      rounds varianceProxy delta delta
    let returnBadEvent := source.successorGlobalReturnDeviationBadEvent
      rounds 1 varianceProxy delta
    let combinedBadEvent := modelBadEvent ∪ returnBadEvent
    MeasurableSet combinedBadEvent /\
      source.trajectoryMeasure combinedBadEvent <=
        AdaptiveStochasticEpisodeBatchSource.selfConsistentScheduledRealizedFailureRateEnvelope n /\
      forall trajectory, trajectory ∉ combinedBadEvent ->
        (forall round : Fin rounds, forall state,
          mdp.optimalValueRemaining mdp.horizon le_rfl state <=
            (adaptiveStochasticSampledEmpiricalOptimisticPlanAt trajectory
              defaultState rewardBudget transitionBudget round).upperValueRemaining
                mdp.horizon le_rfl state) /\
          |source.realizedSuccessorAverageRegret trajectory rounds| <=
            AdaptiveStochasticEpisodeBatchSource.selfConsistentScheduledRealizedSuccessorAverageRegretRateEnvelope
              mdp varianceProxy n := by
  dsimp only
  let rounds := AdaptiveEpisodeBatchSource.decayingExplorationRounds mdp n
  let delta := AdaptiveEpisodeBatchSource.vanishingAverageConfidenceDelta n
  let explorationRate := AdaptiveEpisodeBatchSource.decayingExplorationRate n
  let visitFloor := AdaptiveEpisodeBatchSource.decayingExplorationVisitFloor
    mdp baseVisitFloor n
  let episodes :=
    AdaptiveStochasticEpisodeBatchSource.selfConsistentScheduledEpisodes
      mdp varianceProxy baseVisitFloor n
  let localDelta :=
    AdaptiveStochasticEpisodeBatchSource.selfConsistentScheduledLocalDelta mdp n
  let rewardBudget :=
    AdaptiveStochasticEpisodeBatchSource.selfConsistentScheduledRewardBudget
      mdp varianceProxy baseVisitFloor n
  let transitionBudget :=
    AdaptiveStochasticEpisodeBatchSource.selfConsistentScheduledTransitionBudget
      mdp varianceProxy baseVisitFloor n
  let source := exploratorySource mdp initialState episodes rewardSource
    initialTable defaultState rewardBudget transitionBudget explorationRate
      (AdaptiveEpisodeBatchSource.decayingExplorationRate_le_one n)
  let modelBadEvent := source.adaptiveAllCoordinateEmpiricalModelBadEvent
    rounds varianceProxy delta delta
  let returnBadEvent := source.successorGlobalReturnDeviationBadEvent
    rounds 1 varianceProxy delta
  let combinedBadEvent := modelBadEvent ∪ returnBadEvent
  have hparent :=
    exploratorySource_trajectoryMeasure_selfConsistentScheduledExplicitRate_allCoordinateConfidence_optimism_and_realizedSuccessorAverageRegret
      mdp initialState baseVisitFloor n rewardSource varianceProxy hvarianceProxy
      law initialTable defaultState support hbaseFloor hrewardBound hhorizon
      hbaseVisitFloor
  dsimp only at hparent
  have hrounds : 0 < rounds :=
    AdaptiveEpisodeBatchSource.decayingExplorationRounds_pos mdp n
  have hepisodes : 0 < episodes :=
    AdaptiveStochasticEpisodeBatchSource.selfConsistentScheduledEpisodes_pos
      mdp varianceProxy baseVisitFloor n
  have hdelta : 0 < delta :=
    AdaptiveEpisodeBatchSource.vanishingAverageConfidenceDelta_pos n
  have hdelta_le_one : delta <= 1 :=
    AdaptiveEpisodeBatchSource.vanishingAverageConfidenceDelta_le_one n
  have hfloor : ExploratoryPathUniformVisitFloor support explorationRate
      visitFloor :=
    AdaptiveEpisodeBatchSource.decayingExplorationUniformVisitFloor
      support hbaseFloor n
  have hcalibration :=
    AdaptiveStochasticEpisodeBatchSource.selfConsistentScheduled_countMargin_and_halfContraction
      mdp defaultState varianceProxy hhorizon hbaseVisitFloor n
  have hmargin : simultaneousCountConfidenceRadius mdp episodes localDelta <
      (episodes : Real) * visitFloor := by
    simpa [episodes, localDelta, visitFloor] using hcalibration.1
  have hq : uniformFloorStochasticTransitionContraction mdp episodes
      localDelta visitFloor < 1 := by
    simpa [episodes, localDelta, visitFloor] using
      AdaptiveStochasticEpisodeBatchSource.selfConsistentScheduledTransitionContraction_lt_one
        mdp defaultState varianceProxy hhorizon hbaseVisitFloor n
  have hmodelTotal : 0 < ((((episodes : NNReal) * varianceProxy : NNReal) : Real)) := by
    positivity
  have hmodel :=
    exploratorySource_trajectoryMeasure_finiteRound_allCoordinateConfidence_optimism_and_cumulativeSuccessorExploratoryBehaviorExpectedRegret_of_pathSupport_selfConsistentCalibration
      rewardSource initialTable explorationRate
      (AdaptiveEpisodeBatchSource.decayingExplorationRate_le_one n)
      rounds hrounds hepisodes varianceProxy law hmodelTotal
      delta hdelta hdelta_le_one delta hdelta hdelta_le_one
      defaultState 1 hrewardBound support visitFloor hfloor hmargin hq
  have hmodel' :
      MeasurableSet modelBadEvent /\
        source.trajectoryMeasure modelBadEvent <=
          ENNReal.ofReal delta + ENNReal.ofReal delta /\
        forall trajectory, trajectory ∉ modelBadEvent ->
          (forall round : Fin rounds, forall state,
            mdp.optimalValueRemaining mdp.horizon le_rfl state <=
              (adaptiveStochasticSampledEmpiricalOptimisticPlanAt trajectory
                defaultState rewardBudget transitionBudget round).upperValueRemaining
                  mdp.horizon le_rfl state) /\
            adaptiveStochasticSampledEmpiricalOptimisticSuccessorExploratoryBehaviorExpectedRegret
                (mdp := mdp) (initialState := initialState) (episodes := episodes)
                trajectory defaultState rewardBudget transitionBudget
                  explorationRate
                  (AdaptiveEpisodeBatchSource.decayingExplorationRate_le_one n)
                  rounds <=
              adaptiveStochasticSampledEmpiricalOptimisticOccupancyRadiusSum
                  (mdp := mdp) (initialState := initialState) (episodes := episodes)
                  trajectory defaultState rewardBudget transitionBudget rounds +
                (rounds : Real) * exploratoryBehaviorRegretCharge mdp
                  explorationRate 1 := by
    simpa [rounds, delta, explorationRate, visitFloor, episodes, localDelta,
      rewardBudget, transitionBudget, source, modelBadEvent,
      AdaptiveStochasticEpisodeBatchSource.selfConsistentScheduledRewardBudget,
      AdaptiveStochasticEpisodeBatchSource.selfConsistentScheduledTransitionBudget,
      AdaptiveStochasticEpisodeBatchSource.selfConsistentScheduledLocalDelta]
      using hmodel
  refine ⟨hparent.1, hparent.2.1, ?_⟩
  intro trajectory htrajectory
  have hnotModel : trajectory ∉ modelBadEvent := by
    exact fun hmem => htrajectory (Set.mem_union_left returnBadEvent hmem)
  have hnotReturn : trajectory ∉ returnBadEvent := by
    exact fun hmem => htrajectory (Set.mem_union_right modelBadEvent hmem)
  have hparentGood := hparent.2.2 trajectory htrajectory
  have hmodelGood := hmodel'.2.2 trajectory hnotModel
  have hexpected : source.successorExpectedAverageRegret trajectory rounds <=
      AdaptiveStochasticEpisodeBatchSource.selfConsistentScheduledPlanningAverageRegretBound
        mdp varianceProxy baseVisitFloor n := by
    have hroundsReal : 0 < (rounds : Real) := by exact_mod_cast hrounds
    have haverage : source.successorExpectedAverageRegret trajectory rounds <=
        (adaptiveStochasticSampledEmpiricalOptimisticOccupancyRadiusSum
              (mdp := mdp) (initialState := initialState) (episodes := episodes)
              trajectory defaultState rewardBudget transitionBudget rounds +
            (rounds : Real) * exploratoryBehaviorRegretCharge mdp
              explorationRate 1) /
          (rounds : Real) := by
      rw [show source.successorExpectedAverageRegret trajectory rounds =
          adaptiveStochasticSampledEmpiricalOptimisticSuccessorExploratoryBehaviorExpectedRegret
              (mdp := mdp) (initialState := initialState) (episodes := episodes)
              trajectory defaultState rewardBudget transitionBudget
                explorationRate
                (AdaptiveEpisodeBatchSource.decayingExplorationRate_le_one n)
                rounds /
            (rounds : Real) by
        simpa [source] using
          exploratorySource_successorExpectedAverageRegret_eq_sampledPlanExploratoryBehaviorExpectedRegret
            rewardSource initialTable defaultState rewardBudget transitionBudget
              explorationRate
              (AdaptiveEpisodeBatchSource.decayingExplorationRate_le_one n)
              trajectory rounds]
      exact div_le_div_of_nonneg_right hmodelGood.2 hroundsReal.le
    exact haverage.trans_eq (by
      simpa [AdaptiveStochasticEpisodeBatchSource.selfConsistentScheduledPlanningAverageRegretBound,
        rounds, explorationRate, episodes, localDelta, visitFloor, rewardBudget,
        transitionBudget] using
        (adaptiveStochasticSampledEmpiricalOptimistic_occupancyAndChargeAverage_eq_selfConsistentBudgetAverageBound
          (mdp := mdp) (initialState := initialState) (episodes := episodes)
          trajectory defaultState localDelta visitFloor 1 rewardBudget
            explorationRate rounds hrounds))
  have hexpectedRate := hexpected.trans
    (AdaptiveStochasticEpisodeBatchSource.selfConsistentScheduledPlanningAverageRegretBound_le_rateEnvelope
      mdp varianceProxy hhorizon hbaseVisitFloor n)
  have hdeviation :
      |source.cumulativeSuccessorGlobalReturnDeviation rounds trajectory| <=
        Concentration.subGaussianSumConfidenceRadius
          (AdaptiveStochasticEpisodeBatchSource.cumulativeSuccessorGlobalReturnVarianceProxy
            mdp rounds episodes 1 varianceProxy) delta := by
    have hdeviationLt :
        |source.cumulativeSuccessorGlobalReturnDeviation rounds trajectory| <
          Concentration.subGaussianSumConfidenceRadius
            (AdaptiveStochasticEpisodeBatchSource.cumulativeSuccessorGlobalReturnVarianceProxy
              mdp rounds episodes 1 varianceProxy) delta := by
      apply lt_of_not_ge
      intro hge
      apply hnotReturn
      simpa [returnBadEvent,
        AdaptiveStochasticEpisodeBatchSource.successorGlobalReturnDeviationBadEvent]
        using hge
    exact hdeviationLt.le
  have habs :=
    source.abs_realizedSuccessorAverageRegret_le_of_expected_le_of_deviation_abs_le
      trajectory rounds hrounds hepisodes
      (AdaptiveStochasticEpisodeBatchSource.selfConsistentScheduledPlanningAverageRegretRateEnvelope
        mdp n)
      (Concentration.subGaussianSumConfidenceRadius
        (AdaptiveStochasticEpisodeBatchSource.cumulativeSuccessorGlobalReturnVarianceProxy
          mdp rounds episodes 1 varianceProxy) delta)
      hexpectedRate hdeviation
  have habsNormalized :
      |source.realizedSuccessorAverageRegret trajectory rounds| <=
        AdaptiveStochasticEpisodeBatchSource.selfConsistentScheduledPlanningAverageRegretRateEnvelope
            mdp n +
          AdaptiveStochasticEpisodeBatchSource.normalizedSuccessorGlobalReturnConfidenceRadius
            mdp episodes rounds 1 varianceProxy delta := by
    simpa [AdaptiveStochasticEpisodeBatchSource.normalizedSuccessorGlobalReturnConfidenceRadius]
      using habs
  have hreturn :=
    AdaptiveStochasticEpisodeBatchSource.normalizedSuccessorGlobalReturnConfidenceRadius_le_decayingEnvelope
      mdp episodes 1 varianceProxy n hepisodes
  refine ⟨hparentGood.1, habsNormalized.trans ?_⟩
  unfold AdaptiveStochasticEpisodeBatchSource.selfConsistentScheduledRealizedSuccessorAverageRegretRateEnvelope
  exact add_le_add (le_refl _) hreturn

/-- One complete actual-sampled self-consistent experiment at each coordinate. -/
abbrev SelfConsistentScheduledStochasticWindowSpace
    (mdp : MDP State Action) (varianceProxy : NNReal)
    (baseVisitFloor : Real) :=
  (n : Nat) -> StochasticEpisodeBatchTrajectory mdp
    (AdaptiveStochasticEpisodeBatchSource.selfConsistentScheduledEpisodes
      mdp varianceProxy baseVisitFloor n)

/-- The actual-sampled self-consistent source at schedule coordinate `n`. -/
noncomputable def selfConsistentScheduledStochasticWindowSource
    (mdp : MDP State Action) (initialState : Measure State)
    [IsProbabilityMeasure initialState]
    (rewardSource : mdp.MeanCompatibleRewardKernel)
    (initialTable : DeterministicMarkovPolicyTable mdp)
    (defaultState : State) (varianceProxy : NNReal)
    (baseVisitFloor : Real) (n : Nat) :
    AdaptiveStochasticEpisodeBatchSource mdp initialState
      (AdaptiveStochasticEpisodeBatchSource.selfConsistentScheduledEpisodes
        mdp varianceProxy baseVisitFloor n) :=
  exploratorySource mdp initialState
    (AdaptiveStochasticEpisodeBatchSource.selfConsistentScheduledEpisodes
      mdp varianceProxy baseVisitFloor n)
    rewardSource initialTable defaultState
    (AdaptiveStochasticEpisodeBatchSource.selfConsistentScheduledRewardBudget
      mdp varianceProxy baseVisitFloor n)
    (AdaptiveStochasticEpisodeBatchSource.selfConsistentScheduledTransitionBudget
      mdp varianceProxy baseVisitFloor n)
    (AdaptiveEpisodeBatchSource.decayingExplorationRate n)
    (AdaptiveEpisodeBatchSource.decayingExplorationRate_le_one n)

/-- The actual-sampled self-consistent trajectory law at coordinate `n`. -/
noncomputable def selfConsistentScheduledStochasticWindowMeasure
    (mdp : MDP State Action) (initialState : Measure State)
    [IsProbabilityMeasure initialState]
    (rewardSource : mdp.MeanCompatibleRewardKernel)
    (initialTable : DeterministicMarkovPolicyTable mdp)
    (defaultState : State) (varianceProxy : NNReal)
    (baseVisitFloor : Real) (n : Nat) :
    Measure (StochasticEpisodeBatchTrajectory mdp
      (AdaptiveStochasticEpisodeBatchSource.selfConsistentScheduledEpisodes
        mdp varianceProxy baseVisitFloor n)) :=
  (selfConsistentScheduledStochasticWindowSource mdp initialState rewardSource
    initialTable defaultState varianceProxy baseVisitFloor n).trajectoryMeasure

instance instSelfConsistentScheduledStochasticWindowMeasureIsProbabilityMeasure
    (mdp : MDP State Action) (initialState : Measure State)
    [IsProbabilityMeasure initialState]
    (rewardSource : mdp.MeanCompatibleRewardKernel)
    (initialTable : DeterministicMarkovPolicyTable mdp)
    (defaultState : State) (varianceProxy : NNReal)
    (baseVisitFloor : Real) (n : Nat) :
    IsProbabilityMeasure
      (selfConsistentScheduledStochasticWindowMeasure mdp initialState
        rewardSource initialTable defaultState varianceProxy baseVisitFloor n) := by
  unfold selfConsistentScheduledStochasticWindowMeasure
  infer_instance

/-- Independent product coupling of the complete self-consistent window laws. -/
noncomputable def selfConsistentScheduledStochasticCommonMeasure
    (mdp : MDP State Action) (initialState : Measure State)
    [IsProbabilityMeasure initialState]
    (rewardSource : mdp.MeanCompatibleRewardKernel)
    (initialTable : DeterministicMarkovPolicyTable mdp)
    (defaultState : State) (varianceProxy : NNReal)
    (baseVisitFloor : Real) :
    Measure (SelfConsistentScheduledStochasticWindowSpace mdp varianceProxy
      baseVisitFloor) :=
  Measure.infinitePi fun n =>
    selfConsistentScheduledStochasticWindowMeasure mdp initialState
      rewardSource initialTable defaultState varianceProxy baseVisitFloor n

instance instSelfConsistentScheduledStochasticCommonMeasureIsProbabilityMeasure
    (mdp : MDP State Action) (initialState : Measure State)
    [IsProbabilityMeasure initialState]
    (rewardSource : mdp.MeanCompatibleRewardKernel)
    (initialTable : DeterministicMarkovPolicyTable mdp)
    (defaultState : State) (varianceProxy : NNReal)
    (baseVisitFloor : Real) :
    IsProbabilityMeasure
      (selfConsistentScheduledStochasticCommonMeasure mdp initialState
        rewardSource initialTable defaultState varianceProxy baseVisitFloor) := by
  unfold selfConsistentScheduledStochasticCommonMeasure
  infer_instance

/-- Each common-space coordinate has exactly its scheduled trajectory law. -/
theorem selfConsistentScheduledStochasticCommonMeasure_map_eval
    (mdp : MDP State Action) (initialState : Measure State)
    [IsProbabilityMeasure initialState]
    (rewardSource : mdp.MeanCompatibleRewardKernel)
    (initialTable : DeterministicMarkovPolicyTable mdp)
    (defaultState : State) (varianceProxy : NNReal)
    (baseVisitFloor : Real) (n : Nat) :
    (selfConsistentScheduledStochasticCommonMeasure mdp initialState
      rewardSource initialTable defaultState varianceProxy baseVisitFloor).map
        (fun omega => omega n) =
      selfConsistentScheduledStochasticWindowMeasure mdp initialState
        rewardSource initialTable defaultState varianceProxy baseVisitFloor n := by
  unfold selfConsistentScheduledStochasticCommonMeasure
  exact Measure.infinitePi_map_eval _ n

/-- Scheduled actual-sampled realized successor-average regret. -/
noncomputable def selfConsistentScheduledStochasticRealizedRegretProcess
    (mdp : MDP State Action) (initialState : Measure State)
    [IsProbabilityMeasure initialState]
    (rewardSource : mdp.MeanCompatibleRewardKernel)
    (initialTable : DeterministicMarkovPolicyTable mdp)
    (defaultState : State) (varianceProxy : NNReal)
    (baseVisitFloor : Real) (n : Nat)
    (omega : SelfConsistentScheduledStochasticWindowSpace mdp varianceProxy
      baseVisitFloor) : Real :=
  (selfConsistentScheduledStochasticWindowSource mdp initialState rewardSource
    initialTable defaultState varianceProxy baseVisitFloor n
    ).realizedSuccessorAverageRegret (omega n)
      (AdaptiveEpisodeBatchSource.decayingExplorationRounds mdp n)

/-- Every coordinate of the scheduled actual-sampled regret is measurable. -/
theorem measurable_selfConsistentScheduledStochasticRealizedRegretProcess
    (mdp : MDP State Action) (initialState : Measure State)
    [IsProbabilityMeasure initialState]
    (rewardSource : mdp.MeanCompatibleRewardKernel)
    (initialTable : DeterministicMarkovPolicyTable mdp)
    (defaultState : State) (varianceProxy : NNReal)
    (baseVisitFloor : Real) (n : Nat) :
    Measurable
      (selfConsistentScheduledStochasticRealizedRegretProcess mdp initialState
        rewardSource initialTable defaultState varianceProxy baseVisitFloor n) := by
  unfold selfConsistentScheduledStochasticRealizedRegretProcess
  exact
    ((selfConsistentScheduledStochasticWindowSource mdp initialState
      rewardSource initialTable defaultState varianceProxy baseVisitFloor n
      ).measurable_realizedSuccessorAverageRegret
        (AdaptiveEpisodeBatchSource.decayingExplorationRounds mdp n)).comp
      (measurable_pi_apply n)

/-- Pull the model/global-return union at coordinate `n` to the common space. -/
noncomputable def selfConsistentScheduledStochasticCommonBadEvent
    (mdp : MDP State Action) (initialState : Measure State)
    [IsProbabilityMeasure initialState]
    (rewardSource : mdp.MeanCompatibleRewardKernel)
    (initialTable : DeterministicMarkovPolicyTable mdp)
    (defaultState : State) (varianceProxy : NNReal)
    (baseVisitFloor : Real) (n : Nat) :
    Set (SelfConsistentScheduledStochasticWindowSpace mdp varianceProxy
      baseVisitFloor) :=
  let source := selfConsistentScheduledStochasticWindowSource mdp initialState
    rewardSource initialTable defaultState varianceProxy baseVisitFloor n
  let rounds := AdaptiveEpisodeBatchSource.decayingExplorationRounds mdp n
  let delta := AdaptiveEpisodeBatchSource.vanishingAverageConfidenceDelta n
  (fun omega => omega n) ⁻¹'
    (source.adaptiveAllCoordinateEmpiricalModelBadEvent
        rounds varianceProxy delta delta ∪
      source.successorGlobalReturnDeviationBadEvent
        rounds 1 varianceProxy delta)

/-- The pulled-back bad event inherits the explicit finite-window failure rate. -/
theorem selfConsistentScheduledStochasticCommonMeasure_badEvent_le
    (mdp : MDP State Action) (initialState : Measure State)
    [IsProbabilityMeasure initialState]
    [StandardBorelSpace State] [StandardBorelSpace Action]
    (baseVisitFloor : Real)
    (rewardSource : mdp.MeanCompatibleRewardKernel)
    (varianceProxy : NNReal) (hvarianceProxy : 0 < varianceProxy)
    (law : rewardSource.UniformSubgaussianRewardLaw varianceProxy)
    (initialTable : DeterministicMarkovPolicyTable mdp)
    (defaultState : State)
    (support : ExploratoryPathSupport mdp initialState)
    (hbaseFloor : ExploratoryPathUniformVisitFloor support 1 baseVisitFloor)
    (hrewardBound : forall state action, |mdp.reward state action| <= 1)
    (hhorizon : 0 < mdp.horizon) (hbaseVisitFloor : 0 < baseVisitFloor)
    (n : Nat) :
    selfConsistentScheduledStochasticCommonMeasure mdp initialState
        rewardSource initialTable defaultState varianceProxy baseVisitFloor
        (selfConsistentScheduledStochasticCommonBadEvent mdp initialState
          rewardSource initialTable defaultState varianceProxy baseVisitFloor n) <=
      AdaptiveStochasticEpisodeBatchSource.selfConsistentScheduledRealizedFailureRateEnvelope n := by
  have hfinite :=
    exploratorySource_trajectoryMeasure_selfConsistentScheduledExplicitRate_allCoordinateConfidence_optimism_and_absoluteRealizedSuccessorAverageRegret
      mdp initialState baseVisitFloor n rewardSource varianceProxy hvarianceProxy
      law initialTable defaultState support hbaseFloor hrewardBound hhorizon
      hbaseVisitFloor
  dsimp only at hfinite
  rcases hfinite with ⟨hmeasurable, htail, _houtside⟩
  have hmeasurable' : MeasurableSet
      ((selfConsistentScheduledStochasticWindowSource mdp initialState
          rewardSource initialTable defaultState varianceProxy baseVisitFloor n
          ).adaptiveAllCoordinateEmpiricalModelBadEvent
            (AdaptiveEpisodeBatchSource.decayingExplorationRounds mdp n)
            varianceProxy
            (AdaptiveEpisodeBatchSource.vanishingAverageConfidenceDelta n)
            (AdaptiveEpisodeBatchSource.vanishingAverageConfidenceDelta n) ∪
        (selfConsistentScheduledStochasticWindowSource mdp initialState
          rewardSource initialTable defaultState varianceProxy baseVisitFloor n
          ).successorGlobalReturnDeviationBadEvent
            (AdaptiveEpisodeBatchSource.decayingExplorationRounds mdp n)
            1 varianceProxy
            (AdaptiveEpisodeBatchSource.vanishingAverageConfidenceDelta n)) := by
    simpa [selfConsistentScheduledStochasticWindowSource] using hmeasurable
  unfold selfConsistentScheduledStochasticCommonBadEvent
  dsimp only
  unfold selfConsistentScheduledStochasticCommonMeasure
  rw [(measurePreserving_eval_infinitePi
    (fun k => selfConsistentScheduledStochasticWindowMeasure mdp initialState
      rewardSource initialTable defaultState varianceProxy baseVisitFloor k) n
    ).measure_preimage hmeasurable'.nullMeasurableSet]
  simpa [selfConsistentScheduledStochasticWindowMeasure,
    selfConsistentScheduledStochasticWindowSource] using htail

/-- Outside the pulled-back event, coordinate `n` has the absolute rate bound. -/
theorem abs_selfConsistentScheduledStochasticRealizedRegretProcess_le_of_not_mem_badEvent
    (mdp : MDP State Action) (initialState : Measure State)
    [IsProbabilityMeasure initialState]
    [StandardBorelSpace State] [StandardBorelSpace Action]
    (baseVisitFloor : Real)
    (rewardSource : mdp.MeanCompatibleRewardKernel)
    (varianceProxy : NNReal) (hvarianceProxy : 0 < varianceProxy)
    (law : rewardSource.UniformSubgaussianRewardLaw varianceProxy)
    (initialTable : DeterministicMarkovPolicyTable mdp)
    (defaultState : State)
    (support : ExploratoryPathSupport mdp initialState)
    (hbaseFloor : ExploratoryPathUniformVisitFloor support 1 baseVisitFloor)
    (hrewardBound : forall state action, |mdp.reward state action| <= 1)
    (hhorizon : 0 < mdp.horizon) (hbaseVisitFloor : 0 < baseVisitFloor)
    (n : Nat)
    (omega : SelfConsistentScheduledStochasticWindowSpace mdp varianceProxy
      baseVisitFloor)
    (homega : omega ∉
      selfConsistentScheduledStochasticCommonBadEvent mdp initialState
        rewardSource initialTable defaultState varianceProxy baseVisitFloor n) :
    |selfConsistentScheduledStochasticRealizedRegretProcess mdp initialState
        rewardSource initialTable defaultState varianceProxy baseVisitFloor n
        omega| <=
      AdaptiveStochasticEpisodeBatchSource.selfConsistentScheduledRealizedSuccessorAverageRegretRateEnvelope
        mdp varianceProxy n := by
  have hfinite :=
    exploratorySource_trajectoryMeasure_selfConsistentScheduledExplicitRate_allCoordinateConfidence_optimism_and_absoluteRealizedSuccessorAverageRegret
      mdp initialState baseVisitFloor n rewardSource varianceProxy hvarianceProxy
      law initialTable defaultState support hbaseFloor hrewardBound hhorizon
      hbaseVisitFloor
  dsimp only at hfinite
  rcases hfinite with ⟨_hmeasurable, _htail, houtside⟩
  exact (houtside (omega n) (by
    simpa [selfConsistentScheduledStochasticCommonBadEvent] using homega)).2

/--
Terminal theorem: exact scheduled marginals and convergence in probability of
actual-sampled realized successor-average regret to zero.
-/
theorem exploratorySource_selfConsistentScheduledStochasticCommonMeasure_marginals_and_realizedRegret_tendstoInMeasure_zero
    (mdp : MDP State Action) (initialState : Measure State)
    [IsProbabilityMeasure initialState]
    [StandardBorelSpace State] [StandardBorelSpace Action]
    (baseVisitFloor : Real)
    (rewardSource : mdp.MeanCompatibleRewardKernel)
    (varianceProxy : NNReal) (hvarianceProxy : 0 < varianceProxy)
    (law : rewardSource.UniformSubgaussianRewardLaw varianceProxy)
    (initialTable : DeterministicMarkovPolicyTable mdp)
    (defaultState : State)
    (support : ExploratoryPathSupport mdp initialState)
    (hbaseFloor : ExploratoryPathUniformVisitFloor support 1 baseVisitFloor)
    (hrewardBound : forall state action, |mdp.reward state action| <= 1)
    (hhorizon : 0 < mdp.horizon) (hbaseVisitFloor : 0 < baseVisitFloor) :
    (forall n,
      Measurable
        (selfConsistentScheduledStochasticRealizedRegretProcess mdp
          initialState rewardSource initialTable defaultState varianceProxy
            baseVisitFloor n)) /\
      (forall n,
        (selfConsistentScheduledStochasticCommonMeasure mdp initialState
          rewardSource initialTable defaultState varianceProxy baseVisitFloor
          ).map (fun omega => omega n) =
          selfConsistentScheduledStochasticWindowMeasure mdp initialState
            rewardSource initialTable defaultState varianceProxy baseVisitFloor n) /\
      TendstoInMeasure
        (selfConsistentScheduledStochasticCommonMeasure mdp initialState
          rewardSource initialTable defaultState varianceProxy baseVisitFloor)
        (selfConsistentScheduledStochasticRealizedRegretProcess mdp initialState
          rewardSource initialTable defaultState varianceProxy baseVisitFloor)
        atTop (fun _ => 0) := by
  refine ⟨fun n =>
    measurable_selfConsistentScheduledStochasticRealizedRegretProcess mdp
      initialState rewardSource initialTable defaultState varianceProxy
        baseVisitFloor n,
    fun n =>
      selfConsistentScheduledStochasticCommonMeasure_map_eval mdp initialState
        rewardSource initialTable defaultState varianceProxy baseVisitFloor n,
    ?_⟩
  rw [tendstoInMeasure_iff_dist]
  intro epsilon hepsilon
  have hbound :=
    AdaptiveStochasticEpisodeBatchSource.selfConsistentScheduledRealizedSuccessorAverageRegretRateEnvelope_tendsto_zero
      mdp varianceProxy
  have hboundEventually :
      ∀ᶠ n in atTop,
        AdaptiveStochasticEpisodeBatchSource.selfConsistentScheduledRealizedSuccessorAverageRegretRateEnvelope
          mdp varianceProxy n < epsilon :=
    (tendsto_order.1 hbound).2 epsilon hepsilon
  apply ENNReal.tendsto_nhds_zero.2
  intro eta heta
  have hfailureEventually :
      ∀ᶠ n in atTop,
        AdaptiveStochasticEpisodeBatchSource.selfConsistentScheduledRealizedFailureRateEnvelope n <=
          eta :=
    (ENNReal.tendsto_nhds_zero.1
      AdaptiveStochasticEpisodeBatchSource.selfConsistentScheduledRealizedFailureRateEnvelope_tendsto_zero
      eta heta)
  filter_upwards [hboundEventually, hfailureEventually] with n hboundN hfailureN
  calc
    selfConsistentScheduledStochasticCommonMeasure mdp initialState
        rewardSource initialTable defaultState varianceProxy baseVisitFloor
        {omega |
          epsilon <= dist
            (selfConsistentScheduledStochasticRealizedRegretProcess mdp
              initialState rewardSource initialTable defaultState varianceProxy
                baseVisitFloor n omega)
            0} <=
      selfConsistentScheduledStochasticCommonMeasure mdp initialState
        rewardSource initialTable defaultState varianceProxy baseVisitFloor
        (selfConsistentScheduledStochasticCommonBadEvent mdp initialState
          rewardSource initialTable defaultState varianceProxy baseVisitFloor n) := by
      apply measure_mono
      intro omega homega
      by_contra hnotBad
      have habs :=
        abs_selfConsistentScheduledStochasticRealizedRegretProcess_le_of_not_mem_badEvent
          mdp initialState baseVisitFloor rewardSource varianceProxy
          hvarianceProxy law initialTable defaultState support hbaseFloor
          hrewardBound hhorizon hbaseVisitFloor n omega hnotBad
      have hdist :
          epsilon <=
            |selfConsistentScheduledStochasticRealizedRegretProcess mdp
              initialState rewardSource initialTable defaultState varianceProxy
                baseVisitFloor n omega| := by
        simpa [Real.dist_eq] using homega
      exact (not_le_of_gt hboundN) (hdist.trans habs)
    _ <= AdaptiveStochasticEpisodeBatchSource.selfConsistentScheduledRealizedFailureRateEnvelope n :=
      selfConsistentScheduledStochasticCommonMeasure_badEvent_le mdp initialState
        baseVisitFloor rewardSource varianceProxy hvarianceProxy law initialTable
        defaultState support hbaseFloor hrewardBound hhorizon hbaseVisitFloor n
    _ <= eta := hfailureN

end AdaptiveStochasticSampledEmpiricalOptimisticSource

end BanditRLProof.FiniteHorizonRL
