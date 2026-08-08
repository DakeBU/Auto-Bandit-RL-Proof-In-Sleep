import BanditRLProof.RL.FiniteHorizonAdaptiveStochasticRewardSampledEmpiricalOptimisticSelfConsistentCausalCommonSpaceAlmostSureConsistency

/-!
# Natural-causal almost-sure behavior expected-regret consistency

This module proves that the actual exploratory successor policy's expected
regret tends to zero along almost every trajectory of the one heterogeneous
causal source.  The key project-local leaf extracts a pointwise behavior-
policy rate from the existing coordinate confidence proof.  First
Borel-Cantelli supplies eventual model-goodness, and the deterministic causal
planning rate then squeezes the nonnegative behavior regret to zero.

Regularity is unchanged from the almost-sure realized-regret parent: finite
nonempty Standard Borel State/Action, probability initial law, positive
horizon, reward proxy and base visit floor, bounded stored means, uniform
mean-compatible selected-reward sub-Gaussianity, and full-exploration path
support.

Failure policy: preserve the one dependent source, actual sampled coordinates,
`n`-prefix to `n+1` behavior selection, scheduled budgets, and the distinction
between the empirical model's recommended policy and the source's exploratory
successor policy.  The behavior expected-regret process is not claimed
measurable here, so this route proves an a.e. pathwise limit but no new
in-measure or `Lp` statement.  It also gives no every-trajectory, anytime,
reachability, minimax, or complete-UCB-VI result.
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

namespace AdaptiveStochasticSampledEmpiricalOptimisticSource

/-
This is the pointwise calculation previously embedded in the weighted
finite-prefix proof.  Naming it prevents future almost-sure consumers from
reconstructing the recommended-to-exploratory policy transport.
-/
/-- A model-good coordinate bounds the actual successor policy by the causal rate. -/
theorem selfConsistentScheduledCausalSource_successorPolicyAt_expectedRegret_le_rateAt_of_not_mem_modelRoundBadEvent
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
    let source := selfConsistentScheduledCausalSource mdp initialState
      rewardSource initialTable defaultState varianceProxy baseVisitFloor
    (source.successorPolicyAt trajectory t).expectedRegret initialState <=
      selfConsistentScheduledCausalPlanningRateAt mdp t := by
  dsimp only
  let episodes := fun s =>
    AdaptiveStochasticEpisodeBatchSource.selfConsistentScheduledEpisodes
      mdp varianceProxy baseVisitFloor s
  let rewardBudget := fun s =>
    AdaptiveStochasticEpisodeBatchSource.selfConsistentScheduledRewardBudget
      mdp varianceProxy baseVisitFloor s
  let transitionBudget := fun s =>
    AdaptiveStochasticEpisodeBatchSource.selfConsistentScheduledTransitionBudget
      mdp varianceProxy baseVisitFloor s
  let source := selfConsistentScheduledCausalSource mdp initialState
    rewardSource initialTable defaultState varianceProxy baseVisitFloor
  have hcert :=
    selfConsistentScheduledCausalSource_coordinateConfidence_of_not_mem_modelRoundBadEvent
      mdp initialState rewardSource varianceProxy hvarianceProxy law
        initialTable defaultState support baseVisitFloor hbaseFloor
          hrewardBound hhorizon hbaseVisitFloor trajectory t hnot
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
  exact hlocal.trans
    (selfConsistentScheduledCausalLocalPlanningBound_le_rateAt mdp
      varianceProxy hhorizon hbaseVisitFloor t)

/-- Expected regret of the actual exploratory successor policy at one coordinate. -/
noncomputable def selfConsistentScheduledNaturalCausalSuccessorPolicyExpectedRegretProcess
    (mdp : MDP State Action) (initialState : Measure State)
    [IsProbabilityMeasure initialState]
    (rewardSource : mdp.MeanCompatibleRewardKernel)
    (initialTable : DeterministicMarkovPolicyTable mdp)
    (defaultState : State) (varianceProxy : NNReal)
    (baseVisitFloor : Real) (t : Nat) :
    HeterogeneousStochasticEpisodeBatchTrajectory mdp
        (fun s =>
          AdaptiveStochasticEpisodeBatchSource.selfConsistentScheduledEpisodes
            mdp varianceProxy baseVisitFloor s) -> Real :=
  let source := selfConsistentScheduledCausalSource mdp initialState
    rewardSource initialTable defaultState varianceProxy baseVisitFloor
  fun trajectory =>
    (source.successorPolicyAt trajectory t).expectedRegret initialState

/-- Every actual successor-policy expected-regret coordinate is nonnegative. -/
theorem selfConsistentScheduledNaturalCausalSuccessorPolicyExpectedRegretProcess_nonneg
    (mdp : MDP State Action) (initialState : Measure State)
    [IsProbabilityMeasure initialState]
    (rewardSource : mdp.MeanCompatibleRewardKernel)
    (initialTable : DeterministicMarkovPolicyTable mdp)
    (defaultState : State) (varianceProxy : NNReal)
    (baseVisitFloor : Real) (t : Nat)
    (trajectory : HeterogeneousStochasticEpisodeBatchTrajectory mdp
      (fun s =>
        AdaptiveStochasticEpisodeBatchSource.selfConsistentScheduledEpisodes
          mdp varianceProxy baseVisitFloor s)) :
    0 <= selfConsistentScheduledNaturalCausalSuccessorPolicyExpectedRegretProcess
      mdp initialState rewardSource initialTable defaultState varianceProxy
        baseVisitFloor t trajectory := by
  unfold selfConsistentScheduledNaturalCausalSuccessorPolicyExpectedRegretProcess
  exact
    ((selfConsistentScheduledCausalSource mdp initialState rewardSource
      initialTable defaultState varianceProxy baseVisitFloor).successorPolicyAt
        trajectory t).expectedRegret_nonneg initialState

/-
Only the model-event sequence is needed for this limit.  The return-event
sequence used by realized-regret concentration is deliberately absent.
-/
/-- Actual successor-policy expected regret converges to zero almost surely. -/
theorem selfConsistentScheduledCausalSource_successorPolicyExpectedRegret_tendstoAlmostEverywhere_zero
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
    ∀ᵐ trajectory ∂source.trajectoryMeasure,
      Tendsto
        (fun t =>
          selfConsistentScheduledNaturalCausalSuccessorPolicyExpectedRegretProcess
            mdp initialState rewardSource initialTable defaultState
              varianceProxy baseVisitFloor t trajectory)
        atTop (nhds 0) := by
  dsimp only
  let source := selfConsistentScheduledCausalSource mdp initialState
    rewardSource initialTable defaultState varianceProxy baseVisitFloor
  have hmodel : ∀ᵐ trajectory ∂source.trajectoryMeasure,
      ∀ᶠ t in atTop,
        trajectory ∉ selfConsistentScheduledCausalModelRoundBadEvent mdp
          initialState rewardSource initialTable defaultState varianceProxy
            baseVisitFloor t :=
    ae_eventually_notMem
      (tsum_selfConsistentScheduledCausalModelRoundBadEvent_measure_ne_top
        mdp initialState rewardSource varianceProxy hvarianceProxy law
          initialTable defaultState baseVisitFloor)
  filter_upwards [hmodel] with trajectory htrajectory
  rw [Metric.tendsto_atTop]
  intro epsilon hepsilon
  have hrateSmall : ∀ᶠ t in atTop,
      selfConsistentScheduledCausalPlanningRateAt mdp t < epsilon :=
    (tendsto_order.1
      (selfConsistentScheduledCausalPlanningRateAt_tendsto_zero mdp)).2
        epsilon hepsilon
  exact eventually_atTop.1 (by
    filter_upwards [htrajectory, hrateSmall] with t hnot hrate
    have hupper :=
      selfConsistentScheduledCausalSource_successorPolicyAt_expectedRegret_le_rateAt_of_not_mem_modelRoundBadEvent
        mdp initialState rewardSource varianceProxy hvarianceProxy law
          initialTable defaultState support baseVisitFloor hbaseFloor
            hrewardBound hhorizon hbaseVisitFloor trajectory t hnot
    have hnonneg :=
      selfConsistentScheduledNaturalCausalSuccessorPolicyExpectedRegretProcess_nonneg
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor t trajectory
    simpa [Real.dist_eq, abs_of_nonneg hnonneg] using
      lt_of_le_of_lt hupper hrate)

/-
Terminal route theorem.  The empirical-model certificate, expected behavior
consistency, and realized consistency all hold on one intersection of
full-measure sets for the original dependent source.
-/
/-- Eventual optimism and expected/realized behavior consistency hold jointly a.e. -/
theorem selfConsistentScheduledCausalSource_eventually_modelOptimistic_and_behaviorExpected_and_realizedRegret_tendstoAlmostEverywhere_zero
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
    (forall rounds,
      Measurable
        (selfConsistentScheduledNaturalCausalRealizedRegretProcess mdp
          initialState rewardSource initialTable defaultState varianceProxy
            baseVisitFloor rounds)) ∧
      ∀ᵐ trajectory ∂source.trajectoryMeasure,
        (∀ᶠ t in atTop,
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
                mdp.horizon le_rfl initialState) ∧
        Tendsto
          (fun t =>
            selfConsistentScheduledNaturalCausalSuccessorPolicyExpectedRegretProcess
              mdp initialState rewardSource initialTable defaultState
                varianceProxy baseVisitFloor t trajectory)
          atTop (nhds 0) ∧
        Tendsto
          (fun rounds =>
            selfConsistentScheduledNaturalCausalRealizedRegretProcess mdp
              initialState rewardSource initialTable defaultState varianceProxy
                baseVisitFloor rounds trajectory)
          atTop (nhds 0) := by
  dsimp only
  have hjoint :=
    selfConsistentScheduledCausalSource_eventually_modelOptimistic_and_realizedRegret_tendstoAlmostEverywhere_zero
      mdp initialState rewardSource varianceProxy hvarianceProxy law
        initialTable defaultState support baseVisitFloor hbaseFloor hrewardBound
          hhorizon hbaseVisitFloor
  have hbehavior :=
    selfConsistentScheduledCausalSource_successorPolicyExpectedRegret_tendstoAlmostEverywhere_zero
      mdp initialState rewardSource varianceProxy hvarianceProxy law
        initialTable defaultState support baseVisitFloor hbaseFloor hrewardBound
          hhorizon hbaseVisitFloor
  refine ⟨hjoint.1, ?_⟩
  filter_upwards [hjoint.2, hbehavior] with trajectory htrajectory htrajectoryBehavior
  exact ⟨htrajectory.1, htrajectoryBehavior, htrajectory.2⟩

end AdaptiveStochasticSampledEmpiricalOptimisticSource

end BanditRLProof.FiniteHorizonRL
