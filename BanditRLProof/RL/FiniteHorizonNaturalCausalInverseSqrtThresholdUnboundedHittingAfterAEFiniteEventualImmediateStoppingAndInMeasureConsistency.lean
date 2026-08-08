import BanditRLProof.RL.FiniteHorizonNaturalCausalInverseSqrtThresholdCappedDoubleLinearRawWindowFirstPassageSummableDelayAndEventualImmediateStoppingL1Consistency
import BanditRLProof.RL.FiniteHorizonNaturalCausalStoppingTimeAverageRealizedBehaviorRegretAlmostSureConsistency
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure

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

/-!
This route replaces the finite `hittingBtwn` scan by Mathlib's genuine
uncapped `hittingAfter`. All-prefix almost-sure convergence proves that every
fixed schedule-indexed hitting time is finite almost surely. The compiled
summable-delay route separately proves that almost every trajectory eventually
hits immediately at the fourth-power base. These facts yield a diverging
stopped subsequence and hence stopped-process convergence almost everywhere
and in measure. No expected-delay, uniform-integrability, L1, or optional-
stopping claim is made.
-/

/-- Uncapped first passage below the inverse-square-root threshold after the
fourth-power scheduled base. -/
noncomputable def
    selfConsistentScheduledNaturalCausalInverseSqrtThresholdUnboundedHittingAfterStoppingPrefix
    (mdp : MDP State Action) (initialState : Measure State)
    [IsProbabilityMeasure initialState]
    (rewardSource : mdp.MeanCompatibleRewardKernel)
    (initialTable : DeterministicMarkovPolicyTable mdp)
    (defaultState : State) (varianceProxy : NNReal)
    (baseVisitFloor : Real) (scheduleIndex : Nat) :
    HeterogeneousStochasticEpisodeBatchTrajectory mdp
        (fun t =>
          AdaptiveStochasticEpisodeBatchSource.selfConsistentScheduledEpisodes
            mdp varianceProxy baseVisitFloor t) -> WithTop Nat :=
  MeasureTheory.hittingAfter
    (selfConsistentScheduledNaturalCausalAverageRealizedBehaviorRegretProcess
      mdp initialState rewardSource initialTable defaultState varianceProxy
        baseVisitFloor)
    (Set.Iic
      (selfConsistentScheduledNaturalCausalInverseSqrtFirstPassageThreshold
        scheduleIndex))
    (explicitHighProbabilityRounds scheduleIndex)

/-- Uncapped first passage cannot precede its scheduled base. -/
theorem
    selfConsistentScheduledNaturalCausalInverseSqrtThresholdUnboundedHittingAfterStoppingPrefix_lower
    (mdp : MDP State Action) (initialState : Measure State)
    [IsProbabilityMeasure initialState]
    (rewardSource : mdp.MeanCompatibleRewardKernel)
    (initialTable : DeterministicMarkovPolicyTable mdp)
    (defaultState : State) (varianceProxy : NNReal)
    (baseVisitFloor : Real) (scheduleIndex : Nat)
    (trajectory : HeterogeneousStochasticEpisodeBatchTrajectory mdp
      (fun t =>
        AdaptiveStochasticEpisodeBatchSource.selfConsistentScheduledEpisodes
          mdp varianceProxy baseVisitFloor t)) :
    (explicitHighProbabilityRounds scheduleIndex : WithTop Nat) <=
      selfConsistentScheduledNaturalCausalInverseSqrtThresholdUnboundedHittingAfterStoppingPrefix
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor scheduleIndex trajectory := by
  unfold
    selfConsistentScheduledNaturalCausalInverseSqrtThresholdUnboundedHittingAfterStoppingPrefix
  exact MeasureTheory.le_hittingAfter trajectory

/-- If the process already lies below threshold at the base, uncapped first
passage stops exactly at the base. -/
theorem
    selfConsistentScheduledNaturalCausalInverseSqrtThresholdUnboundedHittingAfterStoppingPrefix_eq_base_of_process_le
    (mdp : MDP State Action) (initialState : Measure State)
    [IsProbabilityMeasure initialState]
    (rewardSource : mdp.MeanCompatibleRewardKernel)
    (initialTable : DeterministicMarkovPolicyTable mdp)
    (defaultState : State) (varianceProxy : NNReal)
    (baseVisitFloor : Real) (scheduleIndex : Nat)
    (trajectory : HeterogeneousStochasticEpisodeBatchTrajectory mdp
      (fun t =>
        AdaptiveStochasticEpisodeBatchSource.selfConsistentScheduledEpisodes
          mdp varianceProxy baseVisitFloor t))
    (hprocess :
      selfConsistentScheduledNaturalCausalAverageRealizedBehaviorRegretProcess
          mdp initialState rewardSource initialTable defaultState varianceProxy
            baseVisitFloor (explicitHighProbabilityRounds scheduleIndex)
              trajectory <=
        selfConsistentScheduledNaturalCausalInverseSqrtFirstPassageThreshold
          scheduleIndex) :
    selfConsistentScheduledNaturalCausalInverseSqrtThresholdUnboundedHittingAfterStoppingPrefix
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor scheduleIndex trajectory =
      (explicitHighProbabilityRounds scheduleIndex : WithTop Nat) := by
  unfold
    selfConsistentScheduledNaturalCausalInverseSqrtThresholdUnboundedHittingAfterStoppingPrefix
  apply le_antisymm
  · exact MeasureTheory.hittingAfter_le_of_mem le_rfl hprocess
  · exact MeasureTheory.le_hittingAfter trajectory

/-- A finite uncapped first passage really lands in the inverse-square-root
lower interval. -/
theorem
    selfConsistentScheduledNaturalCausalAverageRealizedBehaviorRegretProcess_untopA_unboundedHittingAfter_le_threshold
    (mdp : MDP State Action) (initialState : Measure State)
    [IsProbabilityMeasure initialState]
    (rewardSource : mdp.MeanCompatibleRewardKernel)
    (initialTable : DeterministicMarkovPolicyTable mdp)
    (defaultState : State) (varianceProxy : NNReal)
    (baseVisitFloor : Real) (scheduleIndex : Nat)
    (trajectory : HeterogeneousStochasticEpisodeBatchTrajectory mdp
      (fun t =>
        AdaptiveStochasticEpisodeBatchSource.selfConsistentScheduledEpisodes
          mdp varianceProxy baseVisitFloor t))
    (hfinite :
      selfConsistentScheduledNaturalCausalInverseSqrtThresholdUnboundedHittingAfterStoppingPrefix
          mdp initialState rewardSource initialTable defaultState varianceProxy
            baseVisitFloor scheduleIndex trajectory ≠ ⊤) :
    selfConsistentScheduledNaturalCausalAverageRealizedBehaviorRegretProcess
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor
          (selfConsistentScheduledNaturalCausalInverseSqrtThresholdUnboundedHittingAfterStoppingPrefix
            mdp initialState rewardSource initialTable defaultState varianceProxy
              baseVisitFloor scheduleIndex trajectory).untopA trajectory <=
      selfConsistentScheduledNaturalCausalInverseSqrtFirstPassageThreshold
        scheduleIndex := by
  change
    selfConsistentScheduledNaturalCausalAverageRealizedBehaviorRegretProcess
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor
          (MeasureTheory.hittingAfter
            (selfConsistentScheduledNaturalCausalAverageRealizedBehaviorRegretProcess
              mdp initialState rewardSource initialTable defaultState varianceProxy
                baseVisitFloor)
            (Set.Iic
              (selfConsistentScheduledNaturalCausalInverseSqrtFirstPassageThreshold
                scheduleIndex))
            (explicitHighProbabilityRounds scheduleIndex) trajectory).untopA
              trajectory <=
      selfConsistentScheduledNaturalCausalInverseSqrtFirstPassageThreshold
        scheduleIndex
  simpa only [Set.mem_Iic] using
    (MeasureTheory.hittingAfter_mem_set_of_ne_top
      (u :=
        selfConsistentScheduledNaturalCausalAverageRealizedBehaviorRegretProcess
          mdp initialState rewardSource initialTable defaultState varianceProxy
            baseVisitFloor)
      (s := Set.Iic
        (selfConsistentScheduledNaturalCausalInverseSqrtFirstPassageThreshold
          scheduleIndex))
      (n := explicitHighProbabilityRounds scheduleIndex)
      (ω := trajectory)
      (by
        simpa only [
          selfConsistentScheduledNaturalCausalInverseSqrtThresholdUnboundedHittingAfterStoppingPrefix]
          using hfinite))

/-- Every schedule-indexed uncapped inverse-square-root first passage is a
stopping time for the exact natural causal filtration. -/
theorem
    selfConsistentScheduledNaturalCausalInverseSqrtThresholdUnboundedHittingAfterStoppingPrefix_isStoppingTime
    (mdp : MDP State Action) (initialState : Measure State)
    [IsProbabilityMeasure initialState]
    (rewardSource : mdp.MeanCompatibleRewardKernel)
    (initialTable : DeterministicMarkovPolicyTable mdp)
    (defaultState : State) (varianceProxy : NNReal)
    (baseVisitFloor : Real) (scheduleIndex : Nat) :
    IsStoppingTime
      (selfConsistentScheduledNaturalCausalTrajectoryFiltration mdp initialState
        rewardSource initialTable defaultState varianceProxy baseVisitFloor)
      (selfConsistentScheduledNaturalCausalInverseSqrtThresholdUnboundedHittingAfterStoppingPrefix
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor scheduleIndex) := by
  unfold
    selfConsistentScheduledNaturalCausalInverseSqrtThresholdUnboundedHittingAfterStoppingPrefix
  exact
    (selfConsistentScheduledNaturalCausalAverageRealizedBehaviorRegretProcess_stronglyAdapted
      mdp initialState rewardSource initialTable defaultState varianceProxy
        baseVisitFloor).adapted.isStoppingTime_hittingAfter measurableSet_Iic

/-- For every fixed schedule index, all-prefix almost-sure convergence forces
the uncapped inverse-square-root first passage to be finite almost surely. -/
theorem
    ae_ne_top_selfConsistentScheduledNaturalCausalInverseSqrtThresholdUnboundedHittingAfterStoppingPrefix
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
    (scheduleIndex : Nat) :
    let source := selfConsistentScheduledCausalSource mdp initialState
      rewardSource initialTable defaultState varianceProxy baseVisitFloor
    ∀ᵐ trajectory ∂source.trajectoryMeasure,
      selfConsistentScheduledNaturalCausalInverseSqrtThresholdUnboundedHittingAfterStoppingPrefix
          mdp initialState rewardSource initialTable defaultState varianceProxy
            baseVisitFloor scheduleIndex trajectory ≠ ⊤ := by
  dsimp only
  have hparent :=
    selfConsistentScheduledCausalSource_naturalAverageRealizedBehaviorRegret_tendstoAlmostEverywhere_zero
      mdp initialState rewardSource varianceProxy hvarianceProxy law initialTable
        defaultState support baseVisitFloor hbaseFloor hrewardBound hhorizon
          hbaseVisitFloor
  filter_upwards [hparent.2] with trajectory htrajectory
  intro htop
  have heventually :
      ∀ᶠ rounds in atTop,
        selfConsistentScheduledNaturalCausalAverageRealizedBehaviorRegretProcess
            mdp initialState rewardSource initialTable defaultState varianceProxy
              baseVisitFloor rounds trajectory <
          selfConsistentScheduledNaturalCausalInverseSqrtFirstPassageThreshold
            scheduleIndex :=
    (tendsto_order.1 htrajectory).2 _
      (selfConsistentScheduledNaturalCausalInverseSqrtFirstPassageThreshold_pos
        scheduleIndex)
  have hhitEventually :
      ∀ᶠ rounds in atTop,
        explicitHighProbabilityRounds scheduleIndex <= rounds /\
          selfConsistentScheduledNaturalCausalAverageRealizedBehaviorRegretProcess
              mdp initialState rewardSource initialTable defaultState varianceProxy
                baseVisitFloor rounds trajectory ∈
            Set.Iic
              (selfConsistentScheduledNaturalCausalInverseSqrtFirstPassageThreshold
                scheduleIndex) := by
    filter_upwards [eventually_ge_atTop
      (explicitHighProbabilityRounds scheduleIndex), heventually] with
      rounds hbase hprocess
    exact ⟨hbase, hprocess.le⟩
  obtain ⟨rounds, hbase, hmem⟩ := hhitEventually.exists
  have htop' :
      MeasureTheory.hittingAfter
          (selfConsistentScheduledNaturalCausalAverageRealizedBehaviorRegretProcess
            mdp initialState rewardSource initialTable defaultState varianceProxy
              baseVisitFloor)
          (Set.Iic
            (selfConsistentScheduledNaturalCausalInverseSqrtFirstPassageThreshold
              scheduleIndex))
          (explicitHighProbabilityRounds scheduleIndex) trajectory = ⊤ := by
    simpa only [
      selfConsistentScheduledNaturalCausalInverseSqrtThresholdUnboundedHittingAfterStoppingPrefix]
      using htop
  exact
    (MeasureTheory.hittingAfter_eq_top_iff.mp htop' rounds hbase) hmem

/-- Countability places all fixed-index a.e. finiteness statements on one
common almost-sure set. -/
theorem
    ae_all_ne_top_selfConsistentScheduledNaturalCausalInverseSqrtThresholdUnboundedHittingAfterStoppingPrefix
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
      forall scheduleIndex,
        selfConsistentScheduledNaturalCausalInverseSqrtThresholdUnboundedHittingAfterStoppingPrefix
            mdp initialState rewardSource initialTable defaultState varianceProxy
              baseVisitFloor scheduleIndex trajectory ≠ ⊤ := by
  dsimp only
  rw [ae_all_iff]
  exact fun scheduleIndex =>
    ae_ne_top_selfConsistentScheduledNaturalCausalInverseSqrtThresholdUnboundedHittingAfterStoppingPrefix
      mdp initialState rewardSource varianceProxy hvarianceProxy law initialTable
        defaultState support baseVisitFloor hbaseFloor hrewardBound hhorizon
          hbaseVisitFloor scheduleIndex

/-- Summable inverse-square-root delay forces the genuine uncapped first
passage to hit immediately at the base for all sufficiently large schedule
indices, almost surely. -/
theorem
    ae_eventually_selfConsistentScheduledNaturalCausalInverseSqrtThresholdUnboundedHittingAfterStoppingPrefix_eq_base
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
      ∀ᶠ scheduleIndex in atTop,
        selfConsistentScheduledNaturalCausalInverseSqrtThresholdUnboundedHittingAfterStoppingPrefix
            mdp initialState rewardSource initialTable defaultState varianceProxy
              baseVisitFloor scheduleIndex trajectory =
          (explicitHighProbabilityRounds scheduleIndex : WithTop Nat) := by
  dsimp only
  have hnotDelay :=
    ae_eventually_not_mem_selfConsistentScheduledNaturalCausalInverseSqrtThresholdCappedDoubleLinearRawWindowFirstPassageDelayedSet
      mdp initialState rewardSource varianceProxy hvarianceProxy law initialTable
        defaultState support baseVisitFloor hbaseFloor hrewardBound hhorizon
          hbaseVisitFloor
  filter_upwards [hnotDelay] with trajectory htrajectory
  filter_upwards [htrajectory] with scheduleIndex hnot
  apply
    selfConsistentScheduledNaturalCausalInverseSqrtThresholdUnboundedHittingAfterStoppingPrefix_eq_base_of_process_le
  exact le_of_not_gt <| by
    simpa only [
      selfConsistentScheduledNaturalCausalInverseSqrtThresholdCappedDoubleLinearRawWindowFirstPassageDelayedSet_eq,
      Set.mem_setOf_eq] using hnot

/-- Eventual exact-base equality makes the uncapped stopped prefixes diverge
after applying Mathlib's `WithTop.untopA`. -/
theorem
    ae_tendsto_untopA_selfConsistentScheduledNaturalCausalInverseSqrtThresholdUnboundedHittingAfterStoppingPrefix_atTop
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
        (fun scheduleIndex =>
          (selfConsistentScheduledNaturalCausalInverseSqrtThresholdUnboundedHittingAfterStoppingPrefix
            mdp initialState rewardSource initialTable defaultState varianceProxy
              baseVisitFloor scheduleIndex trajectory).untopA)
        atTop atTop := by
  dsimp only
  have heventually :=
    ae_eventually_selfConsistentScheduledNaturalCausalInverseSqrtThresholdUnboundedHittingAfterStoppingPrefix_eq_base
      mdp initialState rewardSource varianceProxy hvarianceProxy law initialTable
        defaultState support baseVisitFloor hbaseFloor hrewardBound hhorizon
          hbaseVisitFloor
  filter_upwards [heventually] with trajectory htrajectory
  apply explicitHighProbabilityRounds_tendsto_atTop.congr'
  filter_upwards [htrajectory] with scheduleIndex heq
  rw [heq]
  rfl

/-- The genuine uncapped inverse-square-root first-passage stopped process is
measurable and converges almost everywhere. -/
theorem
    selfConsistentScheduledCausalSource_inverseSqrtThresholdUnboundedHittingAfter_stoppedProcess_tendstoAlmostEverywhere_zero
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
    let process :=
      selfConsistentScheduledNaturalCausalAverageRealizedBehaviorRegretProcess
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor
    let stoppingPrefix :=
      selfConsistentScheduledNaturalCausalInverseSqrtThresholdUnboundedHittingAfterStoppingPrefix
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor
    let stoppedProcess :=
      selfConsistentScheduledNaturalCausalStoppingTimeAverageRealizedBehaviorRegretProcess
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor stoppingPrefix
    StronglyAdapted
        (selfConsistentScheduledNaturalCausalTrajectoryFiltration mdp initialState
          rewardSource initialTable defaultState varianceProxy baseVisitFloor)
        process /\
      (forall scheduleIndex, Measurable (stoppedProcess scheduleIndex)) /\
      ∀ᵐ trajectory ∂source.trajectoryMeasure,
        Tendsto (fun scheduleIndex => stoppedProcess scheduleIndex trajectory)
          atTop (nhds 0) := by
  dsimp only
  exact
    selfConsistentScheduledCausalSource_stoppingTimeNaturalAverageRealizedBehaviorRegret_tendstoAlmostEverywhere_zero
      mdp initialState rewardSource varianceProxy hvarianceProxy law initialTable
        defaultState support baseVisitFloor hbaseFloor hrewardBound hhorizon
          hbaseVisitFloor
          (selfConsistentScheduledNaturalCausalInverseSqrtThresholdUnboundedHittingAfterStoppingPrefix
            mdp initialState rewardSource initialTable defaultState varianceProxy
              baseVisitFloor)
          (selfConsistentScheduledNaturalCausalInverseSqrtThresholdUnboundedHittingAfterStoppingPrefix_isStoppingTime
            mdp initialState rewardSource initialTable defaultState varianceProxy
              baseVisitFloor)
          (ae_tendsto_untopA_selfConsistentScheduledNaturalCausalInverseSqrtThresholdUnboundedHittingAfterStoppingPrefix_atTop
            mdp initialState rewardSource varianceProxy hvarianceProxy law
              initialTable defaultState support baseVisitFloor hbaseFloor
                hrewardBound hhorizon hbaseVisitFloor)

/-- Almost-everywhere convergence of the measurable uncapped stopped process
implies convergence in measure under the generated probability law. -/
theorem
    selfConsistentScheduledCausalSource_inverseSqrtThresholdUnboundedHittingAfter_stoppedProcess_tendstoInMeasure_zero
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
    let stoppedProcess :=
      selfConsistentScheduledNaturalCausalStoppingTimeAverageRealizedBehaviorRegretProcess
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor stoppingPrefix
    TendstoInMeasure source.trajectoryMeasure stoppedProcess atTop (fun _ => 0) := by
  dsimp only
  have hparent :=
    selfConsistentScheduledCausalSource_inverseSqrtThresholdUnboundedHittingAfter_stoppedProcess_tendstoAlmostEverywhere_zero
      mdp initialState rewardSource varianceProxy hvarianceProxy law initialTable
        defaultState support baseVisitFloor hbaseFloor hrewardBound hhorizon
          hbaseVisitFloor
  exact tendstoInMeasure_of_tendsto_ae
    (fun scheduleIndex => (hparent.2.1 scheduleIndex).aestronglyMeasurable)
    hparent.2.2

/-- Complete uncapped inverse-square-root first-passage a.e.-finiteness and
stopped-process consistency package. -/
theorem
    selfConsistentScheduledCausalSource_inverseSqrtThresholdUnboundedHittingAfter_aeFinite_eventuallyImmediateStopping_and_inMeasure_consistency
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
    let threshold :=
      selfConsistentScheduledNaturalCausalInverseSqrtFirstPassageThreshold
    let stoppingPrefix :=
      selfConsistentScheduledNaturalCausalInverseSqrtThresholdUnboundedHittingAfterStoppingPrefix
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor
    let source := selfConsistentScheduledCausalSource mdp initialState
      rewardSource initialTable defaultState varianceProxy baseVisitFloor
    let process :=
      selfConsistentScheduledNaturalCausalAverageRealizedBehaviorRegretProcess
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor
    let stoppedProcess :=
      selfConsistentScheduledNaturalCausalStoppingTimeAverageRealizedBehaviorRegretProcess
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor stoppingPrefix
    (forall scheduleIndex, 0 < threshold scheduleIndex) /\
      Tendsto threshold atTop (nhds 0) /\
      (forall scheduleIndex,
        IsStoppingTime
          (selfConsistentScheduledNaturalCausalTrajectoryFiltration mdp
            initialState rewardSource initialTable defaultState varianceProxy
              baseVisitFloor)
          (stoppingPrefix scheduleIndex)) /\
      (forall scheduleIndex trajectory,
        (explicitHighProbabilityRounds scheduleIndex : WithTop Nat) <=
          stoppingPrefix scheduleIndex trajectory) /\
      (forall scheduleIndex trajectory,
        stoppingPrefix scheduleIndex trajectory ≠ ⊤ ->
          process (stoppingPrefix scheduleIndex trajectory).untopA trajectory <=
            threshold scheduleIndex) /\
      (forall scheduleIndex trajectory,
        process (explicitHighProbabilityRounds scheduleIndex) trajectory <=
            threshold scheduleIndex ->
          stoppingPrefix scheduleIndex trajectory =
            (explicitHighProbabilityRounds scheduleIndex : WithTop Nat)) /\
      (forall scheduleIndex,
        ∀ᵐ trajectory ∂source.trajectoryMeasure,
          stoppingPrefix scheduleIndex trajectory ≠ ⊤) /\
      (∀ᵐ trajectory ∂source.trajectoryMeasure,
        forall scheduleIndex, stoppingPrefix scheduleIndex trajectory ≠ ⊤) /\
      (∀ᵐ trajectory ∂source.trajectoryMeasure,
        ∀ᶠ scheduleIndex in atTop,
          stoppingPrefix scheduleIndex trajectory =
            (explicitHighProbabilityRounds scheduleIndex : WithTop Nat)) /\
      (∀ᵐ trajectory ∂source.trajectoryMeasure,
        Tendsto (fun scheduleIndex =>
          (stoppingPrefix scheduleIndex trajectory).untopA) atTop atTop) /\
      StronglyAdapted
        (selfConsistentScheduledNaturalCausalTrajectoryFiltration mdp initialState
          rewardSource initialTable defaultState varianceProxy baseVisitFloor)
        process /\
      (forall scheduleIndex, Measurable (stoppedProcess scheduleIndex)) /\
      TendstoInMeasure source.trajectoryMeasure stoppedProcess atTop
        (fun _ => 0) /\
      ∀ᵐ trajectory ∂source.trajectoryMeasure,
        Tendsto (fun scheduleIndex => stoppedProcess scheduleIndex trajectory)
          atTop (nhds 0) := by
  dsimp only
  have hstopped :=
    selfConsistentScheduledCausalSource_inverseSqrtThresholdUnboundedHittingAfter_stoppedProcess_tendstoAlmostEverywhere_zero
      mdp initialState rewardSource varianceProxy hvarianceProxy law initialTable
        defaultState support baseVisitFloor hbaseFloor hrewardBound hhorizon
          hbaseVisitFloor
  exact ⟨
    selfConsistentScheduledNaturalCausalInverseSqrtFirstPassageThreshold_pos,
    selfConsistentScheduledNaturalCausalInverseSqrtFirstPassageThreshold_tendsto_zero,
    selfConsistentScheduledNaturalCausalInverseSqrtThresholdUnboundedHittingAfterStoppingPrefix_isStoppingTime
      mdp initialState rewardSource initialTable defaultState varianceProxy
        baseVisitFloor,
    selfConsistentScheduledNaturalCausalInverseSqrtThresholdUnboundedHittingAfterStoppingPrefix_lower
      mdp initialState rewardSource initialTable defaultState varianceProxy
        baseVisitFloor,
    selfConsistentScheduledNaturalCausalAverageRealizedBehaviorRegretProcess_untopA_unboundedHittingAfter_le_threshold
      mdp initialState rewardSource initialTable defaultState varianceProxy
        baseVisitFloor,
    selfConsistentScheduledNaturalCausalInverseSqrtThresholdUnboundedHittingAfterStoppingPrefix_eq_base_of_process_le
      mdp initialState rewardSource initialTable defaultState varianceProxy
        baseVisitFloor,
    ae_ne_top_selfConsistentScheduledNaturalCausalInverseSqrtThresholdUnboundedHittingAfterStoppingPrefix
      mdp initialState rewardSource varianceProxy hvarianceProxy law initialTable
        defaultState support baseVisitFloor hbaseFloor hrewardBound hhorizon
          hbaseVisitFloor,
    ae_all_ne_top_selfConsistentScheduledNaturalCausalInverseSqrtThresholdUnboundedHittingAfterStoppingPrefix
      mdp initialState rewardSource varianceProxy hvarianceProxy law initialTable
        defaultState support baseVisitFloor hbaseFloor hrewardBound hhorizon
          hbaseVisitFloor,
    ae_eventually_selfConsistentScheduledNaturalCausalInverseSqrtThresholdUnboundedHittingAfterStoppingPrefix_eq_base
      mdp initialState rewardSource varianceProxy hvarianceProxy law initialTable
        defaultState support baseVisitFloor hbaseFloor hrewardBound hhorizon
          hbaseVisitFloor,
    ae_tendsto_untopA_selfConsistentScheduledNaturalCausalInverseSqrtThresholdUnboundedHittingAfterStoppingPrefix_atTop
      mdp initialState rewardSource varianceProxy hvarianceProxy law initialTable
        defaultState support baseVisitFloor hbaseFloor hrewardBound hhorizon
          hbaseVisitFloor,
    hstopped.1,
    hstopped.2.1,
    selfConsistentScheduledCausalSource_inverseSqrtThresholdUnboundedHittingAfter_stoppedProcess_tendstoInMeasure_zero
      mdp initialState rewardSource varianceProxy hvarianceProxy law initialTable
        defaultState support baseVisitFloor hbaseFloor hrewardBound hhorizon
          hbaseVisitFloor,
    hstopped.2.2⟩

end AdaptiveStochasticSampledEmpiricalOptimisticSource

end BanditRLProof.FiniteHorizonRL
