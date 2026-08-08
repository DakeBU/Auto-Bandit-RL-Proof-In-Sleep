import BanditRLProof.RL.FiniteHorizonNaturalCausalInverseSqrtThresholdCappedUnboundedHittingAfterExpectedRegretTruncationReplacement
import BanditRLProof.RL.FiniteHorizonNaturalCausalBoundedStoppingTimeExplicitDeterministicMomentExpectedAverageRealizedBehaviorRegret

/-!
# Policy-value semantics at the genuine uncapped hittingAfter prefix

This module evaluates the pathwise average successor-policy value gap and the
normalized return deviation at the same genuine uncapped `hittingAfter` prefix
as the accepted stopped realized-regret process. A deterministic `2H` envelope
and almost-everywhere random-prefix composition give behavior expected-regret
`L1` consistency. The exact realized/behavior/return decomposition then gives
return-deviation `L1` consistency.

No expectation is commuted through the random index. This is not optional
stopping or a finite-index policy-value identity.
-/

open Filter MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal ProbabilityTheory Topology

namespace BanditRLProof.FiniteHorizonRL

universe u v

variable {State : Type u} {Action : Type v}
    [MeasurableSpace State] [MeasurableSpace Action]
    [Fintype State] [Fintype Action]
    [DecidableEq State] [DecidableEq Action]
    [MeasurableSingletonClass State] [MeasurableSingletonClass Action]
    [Nonempty State] [Nonempty Action]

namespace AdaptiveStochasticSampledEmpiricalOptimisticSource

/-- Average successor-policy expected regret evaluated at a stopping prefix. -/
noncomputable def
    selfConsistentScheduledNaturalCausalStoppingTimeAverageBehaviorExpectedRegretProcess
    (mdp : MDP State Action) (initialState : Measure State)
    [IsProbabilityMeasure initialState]
    (rewardSource : mdp.MeanCompatibleRewardKernel)
    (initialTable : DeterministicMarkovPolicyTable mdp)
    (defaultState : State) (varianceProxy : NNReal)
    (baseVisitFloor : Real)
    (stoppingPrefix : Nat ->
      HeterogeneousStochasticEpisodeBatchTrajectory mdp
        (fun t =>
          AdaptiveStochasticEpisodeBatchSource.selfConsistentScheduledEpisodes
            mdp varianceProxy baseVisitFloor t) -> WithTop Nat)
    (scheduleIndex : Nat) :
    HeterogeneousStochasticEpisodeBatchTrajectory mdp
        (fun t =>
          AdaptiveStochasticEpisodeBatchSource.selfConsistentScheduledEpisodes
            mdp varianceProxy baseVisitFloor t) -> Real :=
  stoppedValue
    (selfConsistentScheduledNaturalCausalAverageBehaviorExpectedRegretProcess
      mdp initialState rewardSource initialTable defaultState varianceProxy
        baseVisitFloor)
    (stoppingPrefix scheduleIndex)

@[simp]
theorem
    selfConsistentScheduledNaturalCausalStoppingTimeAverageBehaviorExpectedRegretProcess_apply
    (mdp : MDP State Action) (initialState : Measure State)
    [IsProbabilityMeasure initialState]
    (rewardSource : mdp.MeanCompatibleRewardKernel)
    (initialTable : DeterministicMarkovPolicyTable mdp)
    (defaultState : State) (varianceProxy : NNReal)
    (baseVisitFloor : Real)
    (stoppingPrefix : Nat ->
      HeterogeneousStochasticEpisodeBatchTrajectory mdp
        (fun t =>
          AdaptiveStochasticEpisodeBatchSource.selfConsistentScheduledEpisodes
            mdp varianceProxy baseVisitFloor t) -> WithTop Nat)
    (scheduleIndex : Nat)
    (trajectory : HeterogeneousStochasticEpisodeBatchTrajectory mdp
      (fun t =>
        AdaptiveStochasticEpisodeBatchSource.selfConsistentScheduledEpisodes
          mdp varianceProxy baseVisitFloor t)) :
    selfConsistentScheduledNaturalCausalStoppingTimeAverageBehaviorExpectedRegretProcess
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor stoppingPrefix scheduleIndex trajectory =
      selfConsistentScheduledNaturalCausalAverageBehaviorExpectedRegretProcess
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor (stoppingPrefix scheduleIndex trajectory).untopA
            trajectory :=
  rfl

/-- Average normalized return deviation evaluated at a stopping prefix. -/
noncomputable def
    selfConsistentScheduledNaturalCausalStoppingTimeAverageReturnDeviationProcess
    (mdp : MDP State Action) (initialState : Measure State)
    [IsProbabilityMeasure initialState]
    (rewardSource : mdp.MeanCompatibleRewardKernel)
    (initialTable : DeterministicMarkovPolicyTable mdp)
    (defaultState : State) (varianceProxy : NNReal)
    (baseVisitFloor : Real)
    (stoppingPrefix : Nat ->
      HeterogeneousStochasticEpisodeBatchTrajectory mdp
        (fun t =>
          AdaptiveStochasticEpisodeBatchSource.selfConsistentScheduledEpisodes
            mdp varianceProxy baseVisitFloor t) -> WithTop Nat)
    (scheduleIndex : Nat) :
    HeterogeneousStochasticEpisodeBatchTrajectory mdp
        (fun t =>
          AdaptiveStochasticEpisodeBatchSource.selfConsistentScheduledEpisodes
            mdp varianceProxy baseVisitFloor t) -> Real :=
  stoppedValue
    (selfConsistentScheduledNaturalCausalAverageReturnDeviationProcess
      mdp initialState rewardSource initialTable defaultState varianceProxy
        baseVisitFloor)
    (stoppingPrefix scheduleIndex)

@[simp]
theorem
    selfConsistentScheduledNaturalCausalStoppingTimeAverageReturnDeviationProcess_apply
    (mdp : MDP State Action) (initialState : Measure State)
    [IsProbabilityMeasure initialState]
    (rewardSource : mdp.MeanCompatibleRewardKernel)
    (initialTable : DeterministicMarkovPolicyTable mdp)
    (defaultState : State) (varianceProxy : NNReal)
    (baseVisitFloor : Real)
    (stoppingPrefix : Nat ->
      HeterogeneousStochasticEpisodeBatchTrajectory mdp
        (fun t =>
          AdaptiveStochasticEpisodeBatchSource.selfConsistentScheduledEpisodes
            mdp varianceProxy baseVisitFloor t) -> WithTop Nat)
    (scheduleIndex : Nat)
    (trajectory : HeterogeneousStochasticEpisodeBatchTrajectory mdp
      (fun t =>
        AdaptiveStochasticEpisodeBatchSource.selfConsistentScheduledEpisodes
          mdp varianceProxy baseVisitFloor t)) :
    selfConsistentScheduledNaturalCausalStoppingTimeAverageReturnDeviationProcess
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor stoppingPrefix scheduleIndex trajectory =
      selfConsistentScheduledNaturalCausalAverageReturnDeviationProcess
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor (stoppingPrefix scheduleIndex trajectory).untopA
            trajectory :=
  rfl

/-- Every deterministic-prefix average behavior expected-regret coordinate is
measurable. -/
theorem measurable_selfConsistentScheduledNaturalCausalAverageBehaviorExpectedRegretProcess
    (mdp : MDP State Action) (initialState : Measure State)
    [IsProbabilityMeasure initialState]
    (rewardSource : mdp.MeanCompatibleRewardKernel)
    (initialTable : DeterministicMarkovPolicyTable mdp)
    (defaultState : State) (varianceProxy : NNReal)
    (baseVisitFloor : Real) (rounds : Nat) :
    Measurable
      (selfConsistentScheduledNaturalCausalAverageBehaviorExpectedRegretProcess
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor rounds) := by
  unfold selfConsistentScheduledNaturalCausalAverageBehaviorExpectedRegretProcess
  exact
    (measurable_selfConsistentScheduledNaturalCausalCumulativeBehaviorExpectedRegretProcess
      mdp initialState rewardSource initialTable defaultState varianceProxy
        baseVisitFloor rounds).div measurable_const

/-- Every deterministic-prefix average behavior expected regret is
nonnegative, including the zero-prefix convention. -/
theorem selfConsistentScheduledNaturalCausalAverageBehaviorExpectedRegretProcess_nonneg
    (mdp : MDP State Action) (initialState : Measure State)
    [IsProbabilityMeasure initialState]
    (rewardSource : mdp.MeanCompatibleRewardKernel)
    (initialTable : DeterministicMarkovPolicyTable mdp)
    (defaultState : State) (varianceProxy : NNReal)
    (baseVisitFloor : Real) (rounds : Nat)
    (trajectory : HeterogeneousStochasticEpisodeBatchTrajectory mdp
      (fun t =>
        AdaptiveStochasticEpisodeBatchSource.selfConsistentScheduledEpisodes
          mdp varianceProxy baseVisitFloor t)) :
    0 <=
      selfConsistentScheduledNaturalCausalAverageBehaviorExpectedRegretProcess
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor rounds trajectory := by
  unfold selfConsistentScheduledNaturalCausalAverageBehaviorExpectedRegretProcess
  exact div_nonneg
    (selfConsistentScheduledNaturalCausalCumulativeBehaviorExpectedRegretProcess_nonneg
      mdp initialState rewardSource initialTable defaultState varianceProxy
        baseVisitFloor rounds trajectory)
    (by positivity)

/-- The deterministic-prefix average behavior expected regret has the global
policy-value envelope `2H`. -/
theorem selfConsistentScheduledNaturalCausalAverageBehaviorExpectedRegretProcess_le_two_mul_horizon
    (mdp : MDP State Action) (initialState : Measure State)
    [IsProbabilityMeasure initialState]
    (rewardSource : mdp.MeanCompatibleRewardKernel)
    (initialTable : DeterministicMarkovPolicyTable mdp)
    (defaultState : State) (varianceProxy : NNReal)
    (baseVisitFloor : Real)
    (hrewardBound : forall state action, |mdp.reward state action| <= 1)
    (rounds : Nat)
    (trajectory : HeterogeneousStochasticEpisodeBatchTrajectory mdp
      (fun t =>
        AdaptiveStochasticEpisodeBatchSource.selfConsistentScheduledEpisodes
          mdp varianceProxy baseVisitFloor t)) :
    selfConsistentScheduledNaturalCausalAverageBehaviorExpectedRegretProcess
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor rounds trajectory <=
      2 * (mdp.horizon : Real) := by
  cases rounds with
  | zero =>
      simp [selfConsistentScheduledNaturalCausalAverageBehaviorExpectedRegretProcess,
        selfConsistentScheduledNaturalCausalCumulativeBehaviorExpectedRegretProcess]
  | succ rounds =>
      unfold selfConsistentScheduledNaturalCausalAverageBehaviorExpectedRegretProcess
      have hrounds : (0 : Real) < ((rounds + 1 : Nat) : Real) := by positivity
      apply (div_le_iff₀ hrounds).2
      simpa only [Nat.cast_add, Nat.cast_one, mul_comm] using
        (selfConsistentScheduledNaturalCausalCumulativeBehaviorExpectedRegretProcess_le_rounds_mul_two_horizon
          mdp initialState rewardSource initialTable defaultState varianceProxy
            baseVisitFloor hrewardBound (rounds + 1) trajectory)

/-- A measurable stopping prefix gives a measurable stopped behavior
expected-regret coordinate. -/
theorem measurable_selfConsistentScheduledNaturalCausalStoppingTimeAverageBehaviorExpectedRegretProcess
    (mdp : MDP State Action) (initialState : Measure State)
    [IsProbabilityMeasure initialState]
    (rewardSource : mdp.MeanCompatibleRewardKernel)
    (initialTable : DeterministicMarkovPolicyTable mdp)
    (defaultState : State) (varianceProxy : NNReal)
    (baseVisitFloor : Real)
    (stoppingPrefix : Nat ->
      HeterogeneousStochasticEpisodeBatchTrajectory mdp
        (fun t =>
          AdaptiveStochasticEpisodeBatchSource.selfConsistentScheduledEpisodes
            mdp varianceProxy baseVisitFloor t) -> WithTop Nat)
    (scheduleIndex : Nat)
    (hstopping : IsStoppingTime
      (selfConsistentScheduledNaturalCausalTrajectoryFiltration mdp initialState
        rewardSource initialTable defaultState varianceProxy baseVisitFloor)
      (stoppingPrefix scheduleIndex)) :
    Measurable
      (selfConsistentScheduledNaturalCausalStoppingTimeAverageBehaviorExpectedRegretProcess
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor stoppingPrefix scheduleIndex) := by
  simpa [
    selfConsistentScheduledNaturalCausalStoppingTimeAverageBehaviorExpectedRegretProcess,
    stoppedValue] using
      (measurable_apply_randomNat
        (fun rounds =>
          selfConsistentScheduledNaturalCausalAverageBehaviorExpectedRegretProcess
            mdp initialState rewardSource initialTable defaultState varianceProxy
              baseVisitFloor rounds)
        (fun trajectory => (stoppingPrefix scheduleIndex trajectory).untopA)
        (fun rounds =>
          measurable_selfConsistentScheduledNaturalCausalAverageBehaviorExpectedRegretProcess
            mdp initialState rewardSource initialTable defaultState varianceProxy
              baseVisitFloor rounds)
        hstopping.measurable'.untopA)

/-- Stopping preserves nonnegativity of the pathwise behavior expected-regret
average. -/
theorem selfConsistentScheduledNaturalCausalStoppingTimeAverageBehaviorExpectedRegretProcess_nonneg
    (mdp : MDP State Action) (initialState : Measure State)
    [IsProbabilityMeasure initialState]
    (rewardSource : mdp.MeanCompatibleRewardKernel)
    (initialTable : DeterministicMarkovPolicyTable mdp)
    (defaultState : State) (varianceProxy : NNReal)
    (baseVisitFloor : Real)
    (stoppingPrefix : Nat ->
      HeterogeneousStochasticEpisodeBatchTrajectory mdp
        (fun t =>
          AdaptiveStochasticEpisodeBatchSource.selfConsistentScheduledEpisodes
            mdp varianceProxy baseVisitFloor t) -> WithTop Nat)
    (scheduleIndex : Nat)
    (trajectory : HeterogeneousStochasticEpisodeBatchTrajectory mdp
      (fun t =>
        AdaptiveStochasticEpisodeBatchSource.selfConsistentScheduledEpisodes
          mdp varianceProxy baseVisitFloor t)) :
    0 <=
      selfConsistentScheduledNaturalCausalStoppingTimeAverageBehaviorExpectedRegretProcess
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor stoppingPrefix scheduleIndex trajectory := by
  rw [selfConsistentScheduledNaturalCausalStoppingTimeAverageBehaviorExpectedRegretProcess_apply]
  exact
    selfConsistentScheduledNaturalCausalAverageBehaviorExpectedRegretProcess_nonneg
      mdp initialState rewardSource initialTable defaultState varianceProxy
        baseVisitFloor _ trajectory

/-- Stopping preserves the deterministic `2H` policy-value envelope. -/
theorem selfConsistentScheduledNaturalCausalStoppingTimeAverageBehaviorExpectedRegretProcess_le_two_mul_horizon
    (mdp : MDP State Action) (initialState : Measure State)
    [IsProbabilityMeasure initialState]
    (rewardSource : mdp.MeanCompatibleRewardKernel)
    (initialTable : DeterministicMarkovPolicyTable mdp)
    (defaultState : State) (varianceProxy : NNReal)
    (baseVisitFloor : Real)
    (hrewardBound : forall state action, |mdp.reward state action| <= 1)
    (stoppingPrefix : Nat ->
      HeterogeneousStochasticEpisodeBatchTrajectory mdp
        (fun t =>
          AdaptiveStochasticEpisodeBatchSource.selfConsistentScheduledEpisodes
            mdp varianceProxy baseVisitFloor t) -> WithTop Nat)
    (scheduleIndex : Nat)
    (trajectory : HeterogeneousStochasticEpisodeBatchTrajectory mdp
      (fun t =>
        AdaptiveStochasticEpisodeBatchSource.selfConsistentScheduledEpisodes
          mdp varianceProxy baseVisitFloor t)) :
    selfConsistentScheduledNaturalCausalStoppingTimeAverageBehaviorExpectedRegretProcess
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor stoppingPrefix scheduleIndex trajectory <=
      2 * (mdp.horizon : Real) := by
  rw [selfConsistentScheduledNaturalCausalStoppingTimeAverageBehaviorExpectedRegretProcess_apply]
  exact
    selfConsistentScheduledNaturalCausalAverageBehaviorExpectedRegretProcess_le_two_mul_horizon
      mdp initialState rewardSource initialTable defaultState varianceProxy
        baseVisitFloor hrewardBound _ trajectory

/-- The stopped realized process is exactly stopped behavior expected regret
minus stopped normalized return deviation at the same prefix. -/
theorem selfConsistentScheduledNaturalCausalStoppingTimeAverageRealizedBehaviorRegretProcess_eq_behaviorExpected_sub_returnDeviation
    (mdp : MDP State Action) (initialState : Measure State)
    [IsProbabilityMeasure initialState]
    (rewardSource : mdp.MeanCompatibleRewardKernel)
    (initialTable : DeterministicMarkovPolicyTable mdp)
    (defaultState : State) (varianceProxy : NNReal)
    (baseVisitFloor : Real)
    (stoppingPrefix : Nat ->
      HeterogeneousStochasticEpisodeBatchTrajectory mdp
        (fun t =>
          AdaptiveStochasticEpisodeBatchSource.selfConsistentScheduledEpisodes
            mdp varianceProxy baseVisitFloor t) -> WithTop Nat)
    (scheduleIndex : Nat)
    (trajectory : HeterogeneousStochasticEpisodeBatchTrajectory mdp
      (fun t =>
        AdaptiveStochasticEpisodeBatchSource.selfConsistentScheduledEpisodes
          mdp varianceProxy baseVisitFloor t)) :
    selfConsistentScheduledNaturalCausalStoppingTimeAverageRealizedBehaviorRegretProcess
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor stoppingPrefix scheduleIndex trajectory =
      selfConsistentScheduledNaturalCausalStoppingTimeAverageBehaviorExpectedRegretProcess
          mdp initialState rewardSource initialTable defaultState varianceProxy
            baseVisitFloor stoppingPrefix scheduleIndex trajectory -
        selfConsistentScheduledNaturalCausalStoppingTimeAverageReturnDeviationProcess
          mdp initialState rewardSource initialTable defaultState varianceProxy
            baseVisitFloor stoppingPrefix scheduleIndex trajectory := by
  rw [
    selfConsistentScheduledNaturalCausalStoppingTimeAverageRealizedBehaviorRegretProcess_apply,
    selfConsistentScheduledNaturalCausalStoppingTimeAverageBehaviorExpectedRegretProcess_apply,
    selfConsistentScheduledNaturalCausalStoppingTimeAverageReturnDeviationProcess_apply,
    selfConsistentScheduledNaturalCausalAverageRealizedBehaviorRegretProcess_eq_expected_sub_deviation]
  unfold selfConsistentScheduledNaturalCausalAverageBehaviorExpectedRegretProcess
    selfConsistentScheduledNaturalCausalAverageReturnDeviationProcess
  exact sub_div _ _ _

/-- The exact uncapped stopped behavior expected-regret process converges
almost everywhere. -/
theorem
    selfConsistentScheduledCausalSource_inverseSqrtThresholdUnboundedHittingAfter_stoppedBehaviorExpectedRegret_tendstoAlmostEverywhere_zero
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
    let stoppingPrefix :=
      selfConsistentScheduledNaturalCausalInverseSqrtThresholdUnboundedHittingAfterStoppingPrefix
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor
    let behaviorProcess :=
      selfConsistentScheduledNaturalCausalStoppingTimeAverageBehaviorExpectedRegretProcess
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor stoppingPrefix
    ∀ᵐ trajectory ∂source.trajectoryMeasure,
      Tendsto (fun scheduleIndex => behaviorProcess scheduleIndex trajectory)
        atTop (nhds 0) := by
  dsimp only
  have hprocess :=
    selfConsistentScheduledCausalSource_naturalAverageBehaviorExpectedRegret_tendstoAlmostEverywhere_zero
      mdp initialState rewardSource varianceProxy hvarianceProxy law initialTable
        defaultState support baseVisitFloor hbaseFloor hrewardBound hhorizon
          hbaseVisitFloor
  have hprefix :=
    ae_tendsto_untopA_selfConsistentScheduledNaturalCausalInverseSqrtThresholdUnboundedHittingAfterStoppingPrefix_atTop
      mdp initialState rewardSource varianceProxy hvarianceProxy law initialTable
        defaultState support baseVisitFloor hbaseFloor hrewardBound hhorizon
          hbaseVisitFloor
  simpa [
    selfConsistentScheduledNaturalCausalStoppingTimeAverageBehaviorExpectedRegretProcess,
    stoppedValue] using
      (ae_tendsto_apply_randomPrefix hprocess hprefix)

/-- Every exact uncapped stopped behavior expected-regret coordinate is
measurable. -/
theorem
    measurable_selfConsistentScheduledNaturalCausalInverseSqrtThresholdUnboundedHittingAfterStoppedBehaviorExpectedRegret
    (mdp : MDP State Action) (initialState : Measure State)
    [IsProbabilityMeasure initialState]
    (rewardSource : mdp.MeanCompatibleRewardKernel)
    (initialTable : DeterministicMarkovPolicyTable mdp)
    (defaultState : State) (varianceProxy : NNReal)
    (baseVisitFloor : Real) (scheduleIndex : Nat) :
    Measurable
      (selfConsistentScheduledNaturalCausalStoppingTimeAverageBehaviorExpectedRegretProcess
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor
          (selfConsistentScheduledNaturalCausalInverseSqrtThresholdUnboundedHittingAfterStoppingPrefix
            mdp initialState rewardSource initialTable defaultState varianceProxy
              baseVisitFloor)
          scheduleIndex) := by
  exact
    measurable_selfConsistentScheduledNaturalCausalStoppingTimeAverageBehaviorExpectedRegretProcess
      mdp initialState rewardSource initialTable defaultState varianceProxy
        baseVisitFloor _ scheduleIndex
        (selfConsistentScheduledNaturalCausalInverseSqrtThresholdUnboundedHittingAfterStoppingPrefix_isStoppingTime
          mdp initialState rewardSource initialTable defaultState varianceProxy
            baseVisitFloor scheduleIndex)

/-- Every exact uncapped stopped behavior expected-regret coordinate is
integrable by the global `2H` envelope. -/
theorem
    integrable_selfConsistentScheduledNaturalCausalInverseSqrtThresholdUnboundedHittingAfterStoppedBehaviorExpectedRegret
    (mdp : MDP State Action) (initialState : Measure State)
    [IsProbabilityMeasure initialState]
    (rewardSource : mdp.MeanCompatibleRewardKernel)
    (initialTable : DeterministicMarkovPolicyTable mdp)
    (defaultState : State) (varianceProxy : NNReal)
    (baseVisitFloor : Real)
    (hrewardBound : forall state action, |mdp.reward state action| <= 1)
    (scheduleIndex : Nat) :
    Integrable
      (selfConsistentScheduledNaturalCausalStoppingTimeAverageBehaviorExpectedRegretProcess
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor
          (selfConsistentScheduledNaturalCausalInverseSqrtThresholdUnboundedHittingAfterStoppingPrefix
            mdp initialState rewardSource initialTable defaultState varianceProxy
              baseVisitFloor)
          scheduleIndex)
      (selfConsistentScheduledCausalSource mdp initialState rewardSource
        initialTable defaultState varianceProxy baseVisitFloor).trajectoryMeasure := by
  let stoppingPrefix :=
    selfConsistentScheduledNaturalCausalInverseSqrtThresholdUnboundedHittingAfterStoppingPrefix
      mdp initialState rewardSource initialTable defaultState varianceProxy
        baseVisitFloor
  let behaviorProcess :=
    selfConsistentScheduledNaturalCausalStoppingTimeAverageBehaviorExpectedRegretProcess
      mdp initialState rewardSource initialTable defaultState varianceProxy
        baseVisitFloor stoppingPrefix
  refine Integrable.of_bound
    (measurable_selfConsistentScheduledNaturalCausalInverseSqrtThresholdUnboundedHittingAfterStoppedBehaviorExpectedRegret
      mdp initialState rewardSource initialTable defaultState varianceProxy
        baseVisitFloor scheduleIndex).aestronglyMeasurable
    (2 * (mdp.horizon : Real)) ?_
  exact Filter.Eventually.of_forall fun trajectory => by
    rw [Real.norm_eq_abs, abs_of_nonneg]
    · exact
        selfConsistentScheduledNaturalCausalStoppingTimeAverageBehaviorExpectedRegretProcess_le_two_mul_horizon
          mdp initialState rewardSource initialTable defaultState varianceProxy
            baseVisitFloor hrewardBound stoppingPrefix scheduleIndex trajectory
    · exact
        selfConsistentScheduledNaturalCausalStoppingTimeAverageBehaviorExpectedRegretProcess_nonneg
          mdp initialState rewardSource initialTable defaultState varianceProxy
            baseVisitFloor stoppingPrefix scheduleIndex trajectory

/-- Every exact uncapped stopped behavior expected-regret coordinate belongs
to `L1`. -/
theorem
    memLp_one_selfConsistentScheduledNaturalCausalInverseSqrtThresholdUnboundedHittingAfterStoppedBehaviorExpectedRegret
    (mdp : MDP State Action) (initialState : Measure State)
    [IsProbabilityMeasure initialState]
    (rewardSource : mdp.MeanCompatibleRewardKernel)
    (initialTable : DeterministicMarkovPolicyTable mdp)
    (defaultState : State) (varianceProxy : NNReal)
    (baseVisitFloor : Real)
    (hrewardBound : forall state action, |mdp.reward state action| <= 1)
    (scheduleIndex : Nat) :
    MemLp
      (selfConsistentScheduledNaturalCausalStoppingTimeAverageBehaviorExpectedRegretProcess
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor
          (selfConsistentScheduledNaturalCausalInverseSqrtThresholdUnboundedHittingAfterStoppingPrefix
            mdp initialState rewardSource initialTable defaultState varianceProxy
              baseVisitFloor)
          scheduleIndex)
      1
      (selfConsistentScheduledCausalSource mdp initialState rewardSource
        initialTable defaultState varianceProxy baseVisitFloor).trajectoryMeasure := by
  rw [memLp_one_iff_integrable]
  exact
    integrable_selfConsistentScheduledNaturalCausalInverseSqrtThresholdUnboundedHittingAfterStoppedBehaviorExpectedRegret
      mdp initialState rewardSource initialTable defaultState varianceProxy
        baseVisitFloor hrewardBound scheduleIndex

/-- Expected absolute stopped behavior expected regret tends to zero. -/
theorem
    integral_abs_selfConsistentScheduledNaturalCausalInverseSqrtThresholdUnboundedHittingAfterStoppedBehaviorExpectedRegret_tendsto_zero
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
    let stoppingPrefix :=
      selfConsistentScheduledNaturalCausalInverseSqrtThresholdUnboundedHittingAfterStoppingPrefix
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor
    let behaviorProcess :=
      selfConsistentScheduledNaturalCausalStoppingTimeAverageBehaviorExpectedRegretProcess
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor stoppingPrefix
    Tendsto
      (fun scheduleIndex => integral source.trajectoryMeasure
        (fun trajectory => |behaviorProcess scheduleIndex trajectory|))
      atTop (nhds 0) := by
  dsimp only
  let source := selfConsistentScheduledCausalSource mdp initialState
    rewardSource initialTable defaultState varianceProxy baseVisitFloor
  let stoppingPrefix :=
    selfConsistentScheduledNaturalCausalInverseSqrtThresholdUnboundedHittingAfterStoppingPrefix
      mdp initialState rewardSource initialTable defaultState varianceProxy
        baseVisitFloor
  let behaviorProcess :=
    selfConsistentScheduledNaturalCausalStoppingTimeAverageBehaviorExpectedRegretProcess
      mdp initialState rewardSource initialTable defaultState varianceProxy
        baseVisitFloor stoppingPrefix
  have hmeas : forall scheduleIndex,
      AEStronglyMeasurable (behaviorProcess scheduleIndex)
        source.trajectoryMeasure := fun scheduleIndex =>
    (measurable_selfConsistentScheduledNaturalCausalInverseSqrtThresholdUnboundedHittingAfterStoppedBehaviorExpectedRegret
      mdp initialState rewardSource initialTable defaultState varianceProxy
        baseVisitFloor scheduleIndex).aestronglyMeasurable
  have hbound : exists C : Real, ∀ᶠ scheduleIndex in atTop,
      ∀ᵐ trajectory ∂source.trajectoryMeasure,
        ‖behaviorProcess scheduleIndex trajectory‖ <= C := by
    refine ⟨2 * (mdp.horizon : Real),
      Filter.Eventually.of_forall fun scheduleIndex =>
        Filter.Eventually.of_forall fun trajectory => ?_⟩
    rw [Real.norm_eq_abs, abs_of_nonneg]
    · exact
        selfConsistentScheduledNaturalCausalStoppingTimeAverageBehaviorExpectedRegretProcess_le_two_mul_horizon
          mdp initialState rewardSource initialTable defaultState varianceProxy
            baseVisitFloor hrewardBound stoppingPrefix scheduleIndex trajectory
    · exact
        selfConsistentScheduledNaturalCausalStoppingTimeAverageBehaviorExpectedRegretProcess_nonneg
          mdp initialState rewardSource initialTable defaultState varianceProxy
            baseVisitFloor stoppingPrefix scheduleIndex trajectory
  have hlimit : ∀ᵐ trajectory ∂source.trajectoryMeasure,
      Tendsto (fun scheduleIndex => behaviorProcess scheduleIndex trajectory)
        atTop (nhds 0) := by
    simpa only [source, stoppingPrefix, behaviorProcess] using
      (selfConsistentScheduledCausalSource_inverseSqrtThresholdUnboundedHittingAfter_stoppedBehaviorExpectedRegret_tendstoAlmostEverywhere_zero
        mdp initialState rewardSource varianceProxy hvarianceProxy law initialTable
          defaultState support baseVisitFloor hbaseFloor hrewardBound hhorizon
            hbaseVisitFloor)
  have hintegral :
      Tendsto (fun scheduleIndex =>
        integral source.trajectoryMeasure (behaviorProcess scheduleIndex))
        atTop (nhds 0) := by
    simpa using
      (tendsto_integral_filter_of_norm_le_const
        (l := atTop) (μ := source.trajectoryMeasure)
        (F := behaviorProcess) (f := fun _ => (0 : Real))
        (Filter.Eventually.of_forall hmeas) hbound hlimit)
  have habs :
      (fun scheduleIndex => integral source.trajectoryMeasure
        (fun trajectory => |behaviorProcess scheduleIndex trajectory|)) =
      (fun scheduleIndex =>
        integral source.trajectoryMeasure (behaviorProcess scheduleIndex)) := by
    funext scheduleIndex
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun trajectory =>
      abs_of_nonneg
        (selfConsistentScheduledNaturalCausalStoppingTimeAverageBehaviorExpectedRegretProcess_nonneg
          mdp initialState rewardSource initialTable defaultState varianceProxy
            baseVisitFloor stoppingPrefix scheduleIndex trajectory)
  rw [habs]
  simpa only [source, stoppingPrefix, behaviorProcess] using hintegral

/-- Exponent-one norm of the exact stopped behavior expected-regret process is
the lifted expected absolute value. -/
theorem
    eLpNorm_one_selfConsistentScheduledNaturalCausalInverseSqrtThresholdUnboundedHittingAfterStoppedBehaviorExpectedRegret_eq
    (mdp : MDP State Action) (initialState : Measure State)
    [IsProbabilityMeasure initialState]
    (rewardSource : mdp.MeanCompatibleRewardKernel)
    (initialTable : DeterministicMarkovPolicyTable mdp)
    (defaultState : State) (varianceProxy : NNReal)
    (baseVisitFloor : Real)
    (hrewardBound : forall state action, |mdp.reward state action| <= 1)
    (scheduleIndex : Nat) :
    let source := selfConsistentScheduledCausalSource mdp initialState
      rewardSource initialTable defaultState varianceProxy baseVisitFloor
    let stoppingPrefix :=
      selfConsistentScheduledNaturalCausalInverseSqrtThresholdUnboundedHittingAfterStoppingPrefix
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor
    let behaviorProcess :=
      selfConsistentScheduledNaturalCausalStoppingTimeAverageBehaviorExpectedRegretProcess
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor stoppingPrefix
    eLpNorm (behaviorProcess scheduleIndex) 1 source.trajectoryMeasure =
      ENNReal.ofReal
        (integral source.trajectoryMeasure
          (fun trajectory => |behaviorProcess scheduleIndex trajectory|)) := by
  dsimp only
  rw [MemLp.eLpNorm_eq_integral_rpow_norm one_ne_zero ENNReal.one_ne_top
    (memLp_one_selfConsistentScheduledNaturalCausalInverseSqrtThresholdUnboundedHittingAfterStoppedBehaviorExpectedRegret
      mdp initialState rewardSource initialTable defaultState varianceProxy
        baseVisitFloor hrewardBound scheduleIndex)]
  simp [Real.norm_eq_abs]

/-- The exact stopped behavior expected-regret process converges to zero in
exponent-one norm. -/
theorem
    eLpNorm_one_selfConsistentScheduledNaturalCausalInverseSqrtThresholdUnboundedHittingAfterStoppedBehaviorExpectedRegret_tendsto_zero
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
    let stoppingPrefix :=
      selfConsistentScheduledNaturalCausalInverseSqrtThresholdUnboundedHittingAfterStoppingPrefix
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor
    let behaviorProcess :=
      selfConsistentScheduledNaturalCausalStoppingTimeAverageBehaviorExpectedRegretProcess
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor stoppingPrefix
    Tendsto
      (fun scheduleIndex =>
        eLpNorm (behaviorProcess scheduleIndex) 1 source.trajectoryMeasure)
      atTop (nhds 0) := by
  dsimp only
  have habs :=
    integral_abs_selfConsistentScheduledNaturalCausalInverseSqrtThresholdUnboundedHittingAfterStoppedBehaviorExpectedRegret_tendsto_zero
      mdp initialState rewardSource varianceProxy hvarianceProxy law initialTable
        defaultState support baseVisitFloor hbaseFloor hrewardBound hhorizon
          hbaseVisitFloor
  have hofReal := (ENNReal.continuous_ofReal.tendsto 0).comp habs
  simpa only [ENNReal.ofReal_zero,
    eLpNorm_one_selfConsistentScheduledNaturalCausalInverseSqrtThresholdUnboundedHittingAfterStoppedBehaviorExpectedRegret_eq
      mdp initialState rewardSource initialTable defaultState varianceProxy
        baseVisitFloor hrewardBound] using hofReal

/-- Signed expectation of the exact stopped behavior expected-regret process
tends to zero. -/
theorem
    selfConsistentScheduledNaturalCausalInverseSqrtThresholdUnboundedHittingAfterStoppedBehaviorExpectedRegretIntegral_tendsto_zero
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
    let stoppingPrefix :=
      selfConsistentScheduledNaturalCausalInverseSqrtThresholdUnboundedHittingAfterStoppingPrefix
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor
    let behaviorProcess :=
      selfConsistentScheduledNaturalCausalStoppingTimeAverageBehaviorExpectedRegretProcess
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor stoppingPrefix
    Tendsto
      (fun scheduleIndex =>
        integral source.trajectoryMeasure (behaviorProcess scheduleIndex))
      atTop (nhds 0) := by
  dsimp only
  exact integral_tendsto_zero_of_memLp_one_of_eLpNorm_tendsto_zero
    (fun scheduleIndex =>
      memLp_one_selfConsistentScheduledNaturalCausalInverseSqrtThresholdUnboundedHittingAfterStoppedBehaviorExpectedRegret
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor hrewardBound scheduleIndex)
    (eLpNorm_one_selfConsistentScheduledNaturalCausalInverseSqrtThresholdUnboundedHittingAfterStoppedBehaviorExpectedRegret_tendsto_zero
      mdp initialState rewardSource varianceProxy hvarianceProxy law initialTable
        defaultState support baseVisitFloor hbaseFloor hrewardBound hhorizon
          hbaseVisitFloor)

/-- The exact uncapped stopped return-deviation coordinates belong to `L1`. -/
theorem
    memLp_one_selfConsistentScheduledNaturalCausalInverseSqrtThresholdUnboundedHittingAfterStoppedReturnDeviation
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
    (hhorizon : 4 < mdp.horizon) (hbaseVisitFloor : 0 < baseVisitFloor)
    (scheduleIndex : Nat) :
    let source := selfConsistentScheduledCausalSource mdp initialState
      rewardSource initialTable defaultState varianceProxy baseVisitFloor
    let stoppingPrefix :=
      selfConsistentScheduledNaturalCausalInverseSqrtThresholdUnboundedHittingAfterStoppingPrefix
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor
    let returnProcess :=
      selfConsistentScheduledNaturalCausalStoppingTimeAverageReturnDeviationProcess
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor stoppingPrefix
    MemLp (returnProcess scheduleIndex) 1 source.trajectoryMeasure := by
  dsimp only
  let source := selfConsistentScheduledCausalSource mdp initialState
    rewardSource initialTable defaultState varianceProxy baseVisitFloor
  let stoppingPrefix :=
    selfConsistentScheduledNaturalCausalInverseSqrtThresholdUnboundedHittingAfterStoppingPrefix
      mdp initialState rewardSource initialTable defaultState varianceProxy
        baseVisitFloor
  let behaviorProcess :=
    selfConsistentScheduledNaturalCausalStoppingTimeAverageBehaviorExpectedRegretProcess
      mdp initialState rewardSource initialTable defaultState varianceProxy
        baseVisitFloor stoppingPrefix
  let realizedProcess :=
    selfConsistentScheduledNaturalCausalStoppingTimeAverageRealizedBehaviorRegretProcess
      mdp initialState rewardSource initialTable defaultState varianceProxy
        baseVisitFloor stoppingPrefix
  let returnProcess :=
    selfConsistentScheduledNaturalCausalStoppingTimeAverageReturnDeviationProcess
      mdp initialState rewardSource initialTable defaultState varianceProxy
        baseVisitFloor stoppingPrefix
  have hbehavior : MemLp (behaviorProcess scheduleIndex) 1
      source.trajectoryMeasure := by
    simpa only [source, stoppingPrefix, behaviorProcess] using
      (memLp_one_selfConsistentScheduledNaturalCausalInverseSqrtThresholdUnboundedHittingAfterStoppedBehaviorExpectedRegret
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor hrewardBound scheduleIndex)
  have hrealized : MemLp (realizedProcess scheduleIndex) 1
      source.trajectoryMeasure := by
    simpa only [source, stoppingPrefix, realizedProcess] using
      (memLp_one_selfConsistentScheduledNaturalCausalInverseSqrtThresholdUnboundedHittingAfterStoppedAverageRealizedBehaviorRegret
        mdp initialState rewardSource varianceProxy hvarianceProxy law initialTable
          defaultState support baseVisitFloor hbaseFloor hrewardBound hhorizon
            hbaseVisitFloor scheduleIndex)
  have heq : returnProcess scheduleIndex =ᵐ[source.trajectoryMeasure]
      behaviorProcess scheduleIndex - realizedProcess scheduleIndex :=
    Filter.Eventually.of_forall fun trajectory => by
      have hdecomp :=
        selfConsistentScheduledNaturalCausalStoppingTimeAverageRealizedBehaviorRegretProcess_eq_behaviorExpected_sub_returnDeviation
          mdp initialState rewardSource initialTable defaultState varianceProxy
            baseVisitFloor stoppingPrefix scheduleIndex trajectory
      change realizedProcess scheduleIndex trajectory =
        behaviorProcess scheduleIndex trajectory -
          returnProcess scheduleIndex trajectory at hdecomp
      change returnProcess scheduleIndex trajectory =
        behaviorProcess scheduleIndex trajectory -
          realizedProcess scheduleIndex trajectory
      linarith
  exact (memLp_congr_ae heq).mpr (hbehavior.sub hrealized)

/-- Exponent-one norm of the exact stopped return deviation tends to zero. -/
theorem
    eLpNorm_one_selfConsistentScheduledNaturalCausalInverseSqrtThresholdUnboundedHittingAfterStoppedReturnDeviation_tendsto_zero
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
    (hhorizon : 4 < mdp.horizon) (hbaseVisitFloor : 0 < baseVisitFloor) :
    let source := selfConsistentScheduledCausalSource mdp initialState
      rewardSource initialTable defaultState varianceProxy baseVisitFloor
    let stoppingPrefix :=
      selfConsistentScheduledNaturalCausalInverseSqrtThresholdUnboundedHittingAfterStoppingPrefix
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor
    let returnProcess :=
      selfConsistentScheduledNaturalCausalStoppingTimeAverageReturnDeviationProcess
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor stoppingPrefix
    Tendsto
      (fun scheduleIndex =>
        eLpNorm (returnProcess scheduleIndex) 1 source.trajectoryMeasure)
      atTop (nhds 0) := by
  dsimp only
  let source := selfConsistentScheduledCausalSource mdp initialState
    rewardSource initialTable defaultState varianceProxy baseVisitFloor
  let stoppingPrefix :=
    selfConsistentScheduledNaturalCausalInverseSqrtThresholdUnboundedHittingAfterStoppingPrefix
      mdp initialState rewardSource initialTable defaultState varianceProxy
        baseVisitFloor
  let behaviorProcess :=
    selfConsistentScheduledNaturalCausalStoppingTimeAverageBehaviorExpectedRegretProcess
      mdp initialState rewardSource initialTable defaultState varianceProxy
        baseVisitFloor stoppingPrefix
  let realizedProcess :=
    selfConsistentScheduledNaturalCausalStoppingTimeAverageRealizedBehaviorRegretProcess
      mdp initialState rewardSource initialTable defaultState varianceProxy
        baseVisitFloor stoppingPrefix
  let returnProcess :=
    selfConsistentScheduledNaturalCausalStoppingTimeAverageReturnDeviationProcess
      mdp initialState rewardSource initialTable defaultState varianceProxy
        baseVisitFloor stoppingPrefix
  have hbehaviorNorm : Tendsto
      (fun scheduleIndex =>
        eLpNorm (behaviorProcess scheduleIndex) 1 source.trajectoryMeasure)
      atTop (nhds 0) := by
    simpa only [source, stoppingPrefix, behaviorProcess] using
      (eLpNorm_one_selfConsistentScheduledNaturalCausalInverseSqrtThresholdUnboundedHittingAfterStoppedBehaviorExpectedRegret_tendsto_zero
        mdp initialState rewardSource varianceProxy hvarianceProxy law initialTable
          defaultState support baseVisitFloor hbaseFloor hrewardBound
            (lt_trans (by decide : 0 < 4) hhorizon) hbaseVisitFloor)
  have hrealizedNorm : Tendsto
      (fun scheduleIndex =>
        eLpNorm (realizedProcess scheduleIndex) 1 source.trajectoryMeasure)
      atTop (nhds 0) := by
    simpa only [source, stoppingPrefix, realizedProcess] using
      (eLpNorm_one_selfConsistentScheduledNaturalCausalInverseSqrtThresholdUnboundedHittingAfterStoppedAverageRealizedBehaviorRegret_tendsto_zero
        mdp initialState rewardSource varianceProxy hvarianceProxy law initialTable
          defaultState support baseVisitFloor hbaseFloor hrewardBound hhorizon
            hbaseVisitFloor)
  have hsum : Tendsto
      (fun scheduleIndex =>
        eLpNorm (behaviorProcess scheduleIndex) 1 source.trajectoryMeasure +
          eLpNorm (realizedProcess scheduleIndex) 1 source.trajectoryMeasure)
      atTop (nhds 0) := by
    simpa only [zero_add] using hbehaviorNorm.add hrealizedNorm
  have hbehaviorMem : forall scheduleIndex,
      MemLp (behaviorProcess scheduleIndex) 1 source.trajectoryMeasure :=
    fun scheduleIndex => by
      simpa only [source, stoppingPrefix, behaviorProcess] using
        (memLp_one_selfConsistentScheduledNaturalCausalInverseSqrtThresholdUnboundedHittingAfterStoppedBehaviorExpectedRegret
          mdp initialState rewardSource initialTable defaultState varianceProxy
            baseVisitFloor hrewardBound scheduleIndex)
  have hrealizedMem : forall scheduleIndex,
      MemLp (realizedProcess scheduleIndex) 1 source.trajectoryMeasure :=
    fun scheduleIndex => by
      simpa only [source, stoppingPrefix, realizedProcess] using
        (memLp_one_selfConsistentScheduledNaturalCausalInverseSqrtThresholdUnboundedHittingAfterStoppedAverageRealizedBehaviorRegret
          mdp initialState rewardSource varianceProxy hvarianceProxy law initialTable
            defaultState support baseVisitFloor hbaseFloor hrewardBound hhorizon
              hbaseVisitFloor scheduleIndex)
  have heq : forall scheduleIndex,
      returnProcess scheduleIndex =ᵐ[source.trajectoryMeasure]
        behaviorProcess scheduleIndex - realizedProcess scheduleIndex :=
    fun scheduleIndex => Filter.Eventually.of_forall fun trajectory => by
      have hdecomp :=
        selfConsistentScheduledNaturalCausalStoppingTimeAverageRealizedBehaviorRegretProcess_eq_behaviorExpected_sub_returnDeviation
          mdp initialState rewardSource initialTable defaultState varianceProxy
            baseVisitFloor stoppingPrefix scheduleIndex trajectory
      change realizedProcess scheduleIndex trajectory =
        behaviorProcess scheduleIndex trajectory -
          returnProcess scheduleIndex trajectory at hdecomp
      change returnProcess scheduleIndex trajectory =
        behaviorProcess scheduleIndex trajectory -
          realizedProcess scheduleIndex trajectory
      linarith
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le'
    tendsto_const_nhds hsum
    (Filter.Eventually.of_forall fun _ => bot_le)
    (Filter.Eventually.of_forall fun scheduleIndex => by
      rw [eLpNorm_congr_ae (heq scheduleIndex)]
      exact eLpNorm_sub_le
        (hbehaviorMem scheduleIndex).aestronglyMeasurable
        (hrealizedMem scheduleIndex).aestronglyMeasurable (by norm_num))

/-- Signed expectation of the stopped return deviation tends to zero. -/
theorem
    selfConsistentScheduledNaturalCausalInverseSqrtThresholdUnboundedHittingAfterStoppedReturnDeviationIntegral_tendsto_zero
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
    (hhorizon : 4 < mdp.horizon) (hbaseVisitFloor : 0 < baseVisitFloor) :
    let source := selfConsistentScheduledCausalSource mdp initialState
      rewardSource initialTable defaultState varianceProxy baseVisitFloor
    let stoppingPrefix :=
      selfConsistentScheduledNaturalCausalInverseSqrtThresholdUnboundedHittingAfterStoppingPrefix
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor
    let returnProcess :=
      selfConsistentScheduledNaturalCausalStoppingTimeAverageReturnDeviationProcess
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor stoppingPrefix
    Tendsto
      (fun scheduleIndex =>
        integral source.trajectoryMeasure (returnProcess scheduleIndex))
      atTop (nhds 0) := by
  dsimp only
  exact integral_tendsto_zero_of_memLp_one_of_eLpNorm_tendsto_zero
    (fun scheduleIndex =>
      memLp_one_selfConsistentScheduledNaturalCausalInverseSqrtThresholdUnboundedHittingAfterStoppedReturnDeviation
        mdp initialState rewardSource varianceProxy hvarianceProxy law initialTable
          defaultState support baseVisitFloor hbaseFloor hrewardBound hhorizon
            hbaseVisitFloor scheduleIndex)
    (eLpNorm_one_selfConsistentScheduledNaturalCausalInverseSqrtThresholdUnboundedHittingAfterStoppedReturnDeviation_tendsto_zero
      mdp initialState rewardSource varianceProxy hvarianceProxy law initialTable
        defaultState support baseVisitFloor hbaseFloor hrewardBound hhorizon
          hbaseVisitFloor)

/-- Terminal policy-value semantic and `L1` package at genuine uncapped
`hittingAfter`. -/
theorem
    selfConsistentScheduledCausalSource_inverseSqrtThresholdUnboundedHittingAfter_stoppedBehaviorExpectedRegret_and_returnDeviation_L1_consistency
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
    (hhorizon : 4 < mdp.horizon) (hbaseVisitFloor : 0 < baseVisitFloor) :
    let source := selfConsistentScheduledCausalSource mdp initialState
      rewardSource initialTable defaultState varianceProxy baseVisitFloor
    let stoppingPrefix :=
      selfConsistentScheduledNaturalCausalInverseSqrtThresholdUnboundedHittingAfterStoppingPrefix
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor
    let behaviorProcess :=
      selfConsistentScheduledNaturalCausalStoppingTimeAverageBehaviorExpectedRegretProcess
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor stoppingPrefix
    let realizedProcess :=
      selfConsistentScheduledNaturalCausalStoppingTimeAverageRealizedBehaviorRegretProcess
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor stoppingPrefix
    let returnProcess :=
      selfConsistentScheduledNaturalCausalStoppingTimeAverageReturnDeviationProcess
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor stoppingPrefix
    (forall scheduleIndex,
      Measurable (behaviorProcess scheduleIndex) /\
        MemLp (behaviorProcess scheduleIndex) 1 source.trajectoryMeasure /\
        MemLp (returnProcess scheduleIndex) 1 source.trajectoryMeasure) /\
      (forall scheduleIndex trajectory,
        0 <= behaviorProcess scheduleIndex trajectory /\
          behaviorProcess scheduleIndex trajectory <=
            2 * (mdp.horizon : Real) /\
          realizedProcess scheduleIndex trajectory =
            behaviorProcess scheduleIndex trajectory -
              returnProcess scheduleIndex trajectory) /\
      (∀ᵐ trajectory ∂source.trajectoryMeasure,
        Tendsto (fun scheduleIndex => behaviorProcess scheduleIndex trajectory)
          atTop (nhds 0)) /\
      Tendsto
        (fun scheduleIndex => integral source.trajectoryMeasure
          (fun trajectory => |behaviorProcess scheduleIndex trajectory|))
        atTop (nhds 0) /\
      Tendsto
        (fun scheduleIndex =>
          eLpNorm (behaviorProcess scheduleIndex) 1 source.trajectoryMeasure)
        atTop (nhds 0) /\
      Tendsto
        (fun scheduleIndex =>
          integral source.trajectoryMeasure (behaviorProcess scheduleIndex))
        atTop (nhds 0) /\
      Tendsto
        (fun scheduleIndex =>
          eLpNorm (returnProcess scheduleIndex) 1 source.trajectoryMeasure)
        atTop (nhds 0) /\
      Tendsto
        (fun scheduleIndex =>
          integral source.trajectoryMeasure (returnProcess scheduleIndex))
        atTop (nhds 0) /\
      (forall scheduleIndex,
        integral source.trajectoryMeasure (realizedProcess scheduleIndex) =
          integral source.trajectoryMeasure (behaviorProcess scheduleIndex) -
            integral source.trajectoryMeasure (returnProcess scheduleIndex)) /\
      Tendsto
        (fun scheduleIndex =>
          integral source.trajectoryMeasure (realizedProcess scheduleIndex))
        atTop (nhds 0) := by
  dsimp only
  let source := selfConsistentScheduledCausalSource mdp initialState
    rewardSource initialTable defaultState varianceProxy baseVisitFloor
  let stoppingPrefix :=
    selfConsistentScheduledNaturalCausalInverseSqrtThresholdUnboundedHittingAfterStoppingPrefix
      mdp initialState rewardSource initialTable defaultState varianceProxy
        baseVisitFloor
  let behaviorProcess :=
    selfConsistentScheduledNaturalCausalStoppingTimeAverageBehaviorExpectedRegretProcess
      mdp initialState rewardSource initialTable defaultState varianceProxy
        baseVisitFloor stoppingPrefix
  let realizedProcess :=
    selfConsistentScheduledNaturalCausalStoppingTimeAverageRealizedBehaviorRegretProcess
      mdp initialState rewardSource initialTable defaultState varianceProxy
        baseVisitFloor stoppingPrefix
  let returnProcess :=
    selfConsistentScheduledNaturalCausalStoppingTimeAverageReturnDeviationProcess
      mdp initialState rewardSource initialTable defaultState varianceProxy
        baseVisitFloor stoppingPrefix
  have hbehaviorMem : forall scheduleIndex,
      MemLp (behaviorProcess scheduleIndex) 1 source.trajectoryMeasure :=
    fun scheduleIndex => by
      simpa only [source, stoppingPrefix, behaviorProcess] using
        (memLp_one_selfConsistentScheduledNaturalCausalInverseSqrtThresholdUnboundedHittingAfterStoppedBehaviorExpectedRegret
          mdp initialState rewardSource initialTable defaultState varianceProxy
            baseVisitFloor hrewardBound scheduleIndex)
  have hreturnMem : forall scheduleIndex,
      MemLp (returnProcess scheduleIndex) 1 source.trajectoryMeasure :=
    fun scheduleIndex => by
      simpa only [source, stoppingPrefix, returnProcess] using
        (memLp_one_selfConsistentScheduledNaturalCausalInverseSqrtThresholdUnboundedHittingAfterStoppedReturnDeviation
          mdp initialState rewardSource varianceProxy hvarianceProxy law initialTable
            defaultState support baseVisitFloor hbaseFloor hrewardBound hhorizon
              hbaseVisitFloor scheduleIndex)
  have hrealizedMem : forall scheduleIndex,
      MemLp (realizedProcess scheduleIndex) 1 source.trajectoryMeasure :=
    fun scheduleIndex => by
      simpa only [source, stoppingPrefix, realizedProcess] using
        (memLp_one_selfConsistentScheduledNaturalCausalInverseSqrtThresholdUnboundedHittingAfterStoppedAverageRealizedBehaviorRegret
          mdp initialState rewardSource varianceProxy hvarianceProxy law initialTable
            defaultState support baseVisitFloor hbaseFloor hrewardBound hhorizon
              hbaseVisitFloor scheduleIndex)
  refine ⟨fun scheduleIndex => ⟨?_, hbehaviorMem scheduleIndex,
      hreturnMem scheduleIndex⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact
      measurable_selfConsistentScheduledNaturalCausalInverseSqrtThresholdUnboundedHittingAfterStoppedBehaviorExpectedRegret
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor scheduleIndex
  · intro scheduleIndex trajectory
    exact ⟨
      selfConsistentScheduledNaturalCausalStoppingTimeAverageBehaviorExpectedRegretProcess_nonneg
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor stoppingPrefix scheduleIndex trajectory,
      selfConsistentScheduledNaturalCausalStoppingTimeAverageBehaviorExpectedRegretProcess_le_two_mul_horizon
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor hrewardBound stoppingPrefix scheduleIndex trajectory,
      selfConsistentScheduledNaturalCausalStoppingTimeAverageRealizedBehaviorRegretProcess_eq_behaviorExpected_sub_returnDeviation
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor stoppingPrefix scheduleIndex trajectory⟩
  · simpa only [source, stoppingPrefix, behaviorProcess] using
      (selfConsistentScheduledCausalSource_inverseSqrtThresholdUnboundedHittingAfter_stoppedBehaviorExpectedRegret_tendstoAlmostEverywhere_zero
        mdp initialState rewardSource varianceProxy hvarianceProxy law initialTable
          defaultState support baseVisitFloor hbaseFloor hrewardBound
            (lt_trans (by decide : 0 < 4) hhorizon) hbaseVisitFloor)
  · simpa only [source, stoppingPrefix, behaviorProcess] using
      (integral_abs_selfConsistentScheduledNaturalCausalInverseSqrtThresholdUnboundedHittingAfterStoppedBehaviorExpectedRegret_tendsto_zero
        mdp initialState rewardSource varianceProxy hvarianceProxy law initialTable
          defaultState support baseVisitFloor hbaseFloor hrewardBound
            (lt_trans (by decide : 0 < 4) hhorizon) hbaseVisitFloor)
  · simpa only [source, stoppingPrefix, behaviorProcess] using
      (eLpNorm_one_selfConsistentScheduledNaturalCausalInverseSqrtThresholdUnboundedHittingAfterStoppedBehaviorExpectedRegret_tendsto_zero
        mdp initialState rewardSource varianceProxy hvarianceProxy law initialTable
          defaultState support baseVisitFloor hbaseFloor hrewardBound
            (lt_trans (by decide : 0 < 4) hhorizon) hbaseVisitFloor)
  · simpa only [source, stoppingPrefix, behaviorProcess] using
      (selfConsistentScheduledNaturalCausalInverseSqrtThresholdUnboundedHittingAfterStoppedBehaviorExpectedRegretIntegral_tendsto_zero
        mdp initialState rewardSource varianceProxy hvarianceProxy law initialTable
          defaultState support baseVisitFloor hbaseFloor hrewardBound
            (lt_trans (by decide : 0 < 4) hhorizon) hbaseVisitFloor)
  · simpa only [source, stoppingPrefix, returnProcess] using
      (eLpNorm_one_selfConsistentScheduledNaturalCausalInverseSqrtThresholdUnboundedHittingAfterStoppedReturnDeviation_tendsto_zero
        mdp initialState rewardSource varianceProxy hvarianceProxy law initialTable
          defaultState support baseVisitFloor hbaseFloor hrewardBound hhorizon
            hbaseVisitFloor)
  · simpa only [source, stoppingPrefix, returnProcess] using
      (selfConsistentScheduledNaturalCausalInverseSqrtThresholdUnboundedHittingAfterStoppedReturnDeviationIntegral_tendsto_zero
        mdp initialState rewardSource varianceProxy hvarianceProxy law initialTable
          defaultState support baseVisitFloor hbaseFloor hrewardBound hhorizon
            hbaseVisitFloor)
  · intro scheduleIndex
    have hdecomp : realizedProcess scheduleIndex =ᵐ[source.trajectoryMeasure]
        behaviorProcess scheduleIndex - returnProcess scheduleIndex :=
      Filter.Eventually.of_forall fun trajectory => by
        exact
          selfConsistentScheduledNaturalCausalStoppingTimeAverageRealizedBehaviorRegretProcess_eq_behaviorExpected_sub_returnDeviation
            mdp initialState rewardSource initialTable defaultState varianceProxy
              baseVisitFloor stoppingPrefix scheduleIndex trajectory
    rw [integral_congr_ae hdecomp]
    exact integral_sub
      (memLp_one_iff_integrable.mp (hbehaviorMem scheduleIndex))
      (memLp_one_iff_integrable.mp (hreturnMem scheduleIndex))
  · simpa only [source, stoppingPrefix, realizedProcess] using
      (selfConsistentScheduledNaturalCausalInverseSqrtThresholdUnboundedHittingAfterStoppedAverageRealizedBehaviorRegretIntegral_tendsto_zero
        mdp initialState rewardSource varianceProxy hvarianceProxy law initialTable
          defaultState support baseVisitFloor hbaseFloor hrewardBound hhorizon
            hbaseVisitFloor)

end AdaptiveStochasticSampledEmpiricalOptimisticSource

end BanditRLProof.FiniteHorizonRL
