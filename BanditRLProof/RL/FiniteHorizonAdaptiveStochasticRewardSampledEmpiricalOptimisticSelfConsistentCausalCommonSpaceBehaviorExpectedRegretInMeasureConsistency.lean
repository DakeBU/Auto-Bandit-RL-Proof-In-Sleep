import BanditRLProof.RL.FiniteHorizonAdaptiveStochasticRewardSampledEmpiricalOptimisticSelfConsistentCausalCommonSpaceAlmostSureBehaviorExpectedRegretConsistency

/-!
# Natural-causal behavior expected-regret convergence in measure

This module closes the regularity boundary left by the a.e. behavior route.
For a measurable finite policy-table selector, expected regret of the selected
exploratory policy is measurable by a finite indicator-sum representation.
The heterogeneous trajectory coordinate selector is already measurable, so
every actual successor-policy expected-regret coordinate is measurable.
Mathlib then transports the compiled a.e. limit to `TendstoInMeasure` on the
same genuine dependent causal trajectory measure.

Regularity is unchanged from the a.e. parent: finite nonempty Standard Borel
State/Action, probability initial law, positive horizon/base visit floor/reward
proxy, bounded stored means, uniform mean-compatible selected-reward sub-
Gaussianity, and full-exploration path support. The generic selector lemma
uses only finite measurable State/Action, measurable singletons, and a
probability initial law.

Failure policy: preserve the actual exploratory `source.successorPolicyAt`,
the sampled-model recommendation/behavior distinction, the one dependent
causal measure, `n`-prefix to `n+1` selection, and the existing a.e. route.
This module proves coordinate measurability and convergence in measure, but
does not derive `Lp`, expected-value, every-trajectory, anytime, reachability,
minimax, optimal-rate, or complete-UCB-VI control.
-/

open Filter MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal ProbabilityTheory Topology BigOperators

namespace BanditRLProof.FiniteHorizonRL

universe u v w

variable {State : Type u} {Action : Type v}
    [MeasurableSpace State] [MeasurableSpace Action]
    [Fintype State] [Fintype Action]
    [DecidableEq State] [DecidableEq Action]
    [MeasurableSingletonClass State] [MeasurableSingletonClass Action]
    [Nonempty State] [Nonempty Action]

namespace DeterministicMarkovPolicyTable

omit [Nonempty State] in
/-- Expected regret after a measurable finite table selection is measurable. -/
theorem measurable_exploratoryPolicy_expectedRegret_comp
    {Omega : Type w} [MeasurableSpace Omega]
    {mdp : MDP State Action} (initialState : Measure State)
    [IsProbabilityMeasure initialState]
    (selector : Omega -> DeterministicMarkovPolicyTable mdp)
    (hselector : Measurable selector)
    (explorationRate : NNReal) (hexplorationRate : explorationRate <= 1) :
    Measurable fun omega =>
      ((selector omega).exploratoryPolicy explorationRate
        hexplorationRate).expectedRegret initialState := by
  classical
  let statistic := fun table : DeterministicMarkovPolicyTable mdp =>
    (table.exploratoryPolicy explorationRate
      hexplorationRate).expectedRegret initialState
  have hrepresentation :
      (fun omega =>
        ((selector omega).exploratoryPolicy explorationRate
          hexplorationRate).expectedRegret initialState) =
        fun omega =>
          ∑ table : DeterministicMarkovPolicyTable mdp,
            if selector omega = table then statistic table else 0 := by
    funext omega
    simp [statistic]
  rw [hrepresentation]
  exact Finset.measurable_sum Finset.univ fun table _ =>
    Measurable.ite
      (hselector (measurableSet_singleton table))
      measurable_const measurable_const

end DeterministicMarkovPolicyTable

namespace AdaptiveStochasticSampledEmpiricalOptimisticSource

/-- Every actual causal successor-policy expected-regret coordinate is measurable. -/
theorem measurable_selfConsistentScheduledNaturalCausalSuccessorPolicyExpectedRegretProcess
    (mdp : MDP State Action) (initialState : Measure State)
    [IsProbabilityMeasure initialState]
    (rewardSource : mdp.MeanCompatibleRewardKernel)
    (initialTable : DeterministicMarkovPolicyTable mdp)
    (defaultState : State) (varianceProxy : NNReal)
    (baseVisitFloor : Real) (t : Nat) :
    Measurable
      (selfConsistentScheduledNaturalCausalSuccessorPolicyExpectedRegretProcess
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor t) := by
  let episodes := fun s =>
    AdaptiveStochasticEpisodeBatchSource.selfConsistentScheduledEpisodes
      mdp varianceProxy baseVisitFloor s
  let rewardBudget := fun s =>
    AdaptiveStochasticEpisodeBatchSource.selfConsistentScheduledRewardBudget
      mdp varianceProxy baseVisitFloor s
  let transitionBudget := fun s =>
    AdaptiveStochasticEpisodeBatchSource.selfConsistentScheduledTransitionBudget
      mdp varianceProxy baseVisitFloor s
  let selector := fun trajectory :
      HeterogeneousStochasticEpisodeBatchTrajectory mdp episodes =>
    (trajectory t).sampledEmpiricalOptimisticPolicyTable defaultState
      (rewardBudget t) (transitionBudget t)
  have hselector : Measurable selector :=
    (StochasticEpisodeBatch.measurable_sampledEmpiricalOptimisticPolicyTable
      defaultState (rewardBudget t) (transitionBudget t)).comp
        (measurable_pi_apply t)
  simpa [selfConsistentScheduledNaturalCausalSuccessorPolicyExpectedRegretProcess,
    selfConsistentScheduledCausalSource, heterogeneousExploratorySource,
    HeterogeneousAdaptiveStochasticEpisodeBatchSource.successorPolicyAt,
    heterogeneousSuccessorTable, heterogeneousLatestBatch,
    Preorder.frestrictLe_apply, episodes, rewardBudget, transitionBudget,
    selector] using
      DeterministicMarkovPolicyTable.measurable_exploratoryPolicy_expectedRegret_comp
        initialState selector hselector
          (AdaptiveEpisodeBatchSource.decayingExplorationRate (t + 1))
          (AdaptiveEpisodeBatchSource.decayingExplorationRate_le_one (t + 1))

/-- Actual successor-policy expected regret converges in measure to zero. -/
theorem selfConsistentScheduledCausalSource_successorPolicyExpectedRegret_tendstoInMeasure_zero
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
    (forall t,
      Measurable
        (selfConsistentScheduledNaturalCausalSuccessorPolicyExpectedRegretProcess
          mdp initialState rewardSource initialTable defaultState varianceProxy
            baseVisitFloor t)) ∧
      TendstoInMeasure source.trajectoryMeasure
        (selfConsistentScheduledNaturalCausalSuccessorPolicyExpectedRegretProcess
          mdp initialState rewardSource initialTable defaultState varianceProxy
            baseVisitFloor) atTop (fun _ => 0) := by
  dsimp only
  let source := selfConsistentScheduledCausalSource mdp initialState
    rewardSource initialTable defaultState varianceProxy baseVisitFloor
  have hmeasurable : forall t,
      Measurable
        (selfConsistentScheduledNaturalCausalSuccessorPolicyExpectedRegretProcess
          mdp initialState rewardSource initialTable defaultState varianceProxy
            baseVisitFloor t) := fun t =>
    measurable_selfConsistentScheduledNaturalCausalSuccessorPolicyExpectedRegretProcess
      mdp initialState rewardSource initialTable defaultState varianceProxy
        baseVisitFloor t
  refine ⟨hmeasurable, ?_⟩
  exact tendstoInMeasure_of_tendsto_ae
    (fun t => (hmeasurable t).aestronglyMeasurable)
    (selfConsistentScheduledCausalSource_successorPolicyExpectedRegret_tendstoAlmostEverywhere_zero
      mdp initialState rewardSource varianceProxy hvarianceProxy law
        initialTable defaultState support baseVisitFloor hbaseFloor hrewardBound
          hhorizon hbaseVisitFloor)

/-- Actual behavior expected and realized regret both converge in measure. -/
theorem selfConsistentScheduledCausalSource_behaviorExpected_and_realizedRegret_tendstoInMeasure_zero
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
    ((forall t,
        Measurable
          (selfConsistentScheduledNaturalCausalSuccessorPolicyExpectedRegretProcess
            mdp initialState rewardSource initialTable defaultState
              varianceProxy baseVisitFloor t)) ∧
      TendstoInMeasure source.trajectoryMeasure
        (selfConsistentScheduledNaturalCausalSuccessorPolicyExpectedRegretProcess
          mdp initialState rewardSource initialTable defaultState varianceProxy
            baseVisitFloor) atTop (fun _ => 0)) ∧
    ((forall rounds,
        Measurable
          (selfConsistentScheduledNaturalCausalRealizedRegretProcess mdp
            initialState rewardSource initialTable defaultState varianceProxy
              baseVisitFloor rounds)) ∧
      TendstoInMeasure source.trajectoryMeasure
        (selfConsistentScheduledNaturalCausalRealizedRegretProcess mdp
          initialState rewardSource initialTable defaultState varianceProxy
            baseVisitFloor) atTop (fun _ => 0)) := by
  dsimp only
  exact ⟨
    selfConsistentScheduledCausalSource_successorPolicyExpectedRegret_tendstoInMeasure_zero
      mdp initialState rewardSource varianceProxy hvarianceProxy law
        initialTable defaultState support baseVisitFloor hbaseFloor hrewardBound
          hhorizon hbaseVisitFloor,
    selfConsistentScheduledCausalSource_realizedRegret_tendstoInMeasure_zero
      mdp initialState rewardSource varianceProxy hvarianceProxy law
        initialTable defaultState support baseVisitFloor hbaseFloor hrewardBound
          hhorizon hbaseVisitFloor⟩

end AdaptiveStochasticSampledEmpiricalOptimisticSource

end BanditRLProof.FiniteHorizonRL
