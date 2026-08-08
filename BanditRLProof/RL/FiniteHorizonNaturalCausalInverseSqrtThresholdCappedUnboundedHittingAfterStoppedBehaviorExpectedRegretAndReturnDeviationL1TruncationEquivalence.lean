import BanditRLProof.RL.FiniteHorizonNaturalCausalInverseSqrtThresholdCappedUnboundedHittingAfterL1TruncationEquivalence
import BanditRLProof.RL.FiniteHorizonNaturalCausalInverseSqrtThresholdUnboundedHittingAfterStoppedBehaviorExpectedRegretAndReturnDeviationL1Consistency

/-!
# Componentwise L1 truncation for stopped policy-value semantics

This module transports the genuine uncapped `hittingAfter` policy-value and
return-deviation semantics to the capped double-linear first-passage prefix.
It proves exponent-one norm replacement for both semantic components on the
exact generated trajectory law.

No expectation is commuted through a random index.  The result is not an
optional-stopping theorem and does not assert finite-index equality.
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

/-- The capped inverse-square-root first-passage prefix diverges after
`WithTop.untopA`, almost surely. -/
theorem
    ae_tendsto_untopA_selfConsistentScheduledNaturalCausalInverseSqrtThresholdCappedDoubleLinearRawWindowFirstPassageStoppingPrefix_atTop
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
          (selfConsistentScheduledNaturalCausalInverseSqrtThresholdCappedDoubleLinearRawWindowFirstPassageStoppingPrefix
            mdp initialState rewardSource initialTable defaultState varianceProxy
              baseVisitFloor scheduleIndex trajectory).untopA)
        atTop atTop := by
  dsimp only
  have heventually :=
    ae_eventually_selfConsistentScheduledNaturalCausalInverseSqrtThresholdCappedDoubleLinearRawWindowFirstPassageStoppingPrefix_eq_base
      mdp initialState rewardSource varianceProxy hvarianceProxy law initialTable
        defaultState support baseVisitFloor hbaseFloor hrewardBound hhorizon
          hbaseVisitFloor
  filter_upwards [heventually] with trajectory htrajectory
  apply explicitHighProbabilityRounds_tendsto_atTop.congr'
  filter_upwards [htrajectory] with scheduleIndex heq
  rw [heq]
  rfl

/-- Capped and uncapped stopped policy-value and return-deviation coordinates
are eventually exactly equal, almost surely. -/
theorem
    ae_eventually_selfConsistentScheduledNaturalCausalInverseSqrtThresholdCappedUnboundedHittingAfterStoppedBehaviorExpectedRegret_and_returnDeviation_eq
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
    let cappedStoppingPrefix :=
      selfConsistentScheduledNaturalCausalInverseSqrtThresholdCappedDoubleLinearRawWindowFirstPassageStoppingPrefix
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor
    let uncappedStoppingPrefix :=
      selfConsistentScheduledNaturalCausalInverseSqrtThresholdUnboundedHittingAfterStoppingPrefix
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor
    let cappedBehavior :=
      selfConsistentScheduledNaturalCausalStoppingTimeAverageBehaviorExpectedRegretProcess
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor cappedStoppingPrefix
    let uncappedBehavior :=
      selfConsistentScheduledNaturalCausalStoppingTimeAverageBehaviorExpectedRegretProcess
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor uncappedStoppingPrefix
    let cappedReturn :=
      selfConsistentScheduledNaturalCausalStoppingTimeAverageReturnDeviationProcess
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor cappedStoppingPrefix
    let uncappedReturn :=
      selfConsistentScheduledNaturalCausalStoppingTimeAverageReturnDeviationProcess
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor uncappedStoppingPrefix
    ∀ᵐ trajectory ∂source.trajectoryMeasure,
      ∀ᶠ scheduleIndex in atTop,
        cappedBehavior scheduleIndex trajectory =
            uncappedBehavior scheduleIndex trajectory ∧
          cappedReturn scheduleIndex trajectory =
            uncappedReturn scheduleIndex trajectory := by
  dsimp only
  have hcapped :=
    ae_eventually_selfConsistentScheduledNaturalCausalInverseSqrtThresholdCappedDoubleLinearRawWindowFirstPassageStoppingPrefix_eq_base
      mdp initialState rewardSource varianceProxy hvarianceProxy law initialTable
        defaultState support baseVisitFloor hbaseFloor hrewardBound hhorizon
          hbaseVisitFloor
  have huncapped :=
    ae_eventually_selfConsistentScheduledNaturalCausalInverseSqrtThresholdUnboundedHittingAfterStoppingPrefix_eq_base
      mdp initialState rewardSource varianceProxy hvarianceProxy law initialTable
        defaultState support baseVisitFloor hbaseFloor hrewardBound hhorizon
          hbaseVisitFloor
  filter_upwards [hcapped, huncapped] with trajectory hcap huncap
  filter_upwards [hcap, huncap] with scheduleIndex hcapEq huncapEq
  constructor <;>
    simp only [
      selfConsistentScheduledNaturalCausalStoppingTimeAverageBehaviorExpectedRegretProcess_apply,
      selfConsistentScheduledNaturalCausalStoppingTimeAverageReturnDeviationProcess_apply,
      hcapEq, huncapEq]

/-- The capped stopped behavior expected-regret process converges almost
everywhere. -/
theorem
    selfConsistentScheduledCausalSource_inverseSqrtThresholdCapped_stoppedBehaviorExpectedRegret_tendstoAlmostEverywhere_zero
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
      selfConsistentScheduledNaturalCausalInverseSqrtThresholdCappedDoubleLinearRawWindowFirstPassageStoppingPrefix
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
    ae_tendsto_untopA_selfConsistentScheduledNaturalCausalInverseSqrtThresholdCappedDoubleLinearRawWindowFirstPassageStoppingPrefix_atTop
      mdp initialState rewardSource varianceProxy hvarianceProxy law initialTable
        defaultState support baseVisitFloor hbaseFloor hrewardBound hhorizon
          hbaseVisitFloor
  simpa [
    selfConsistentScheduledNaturalCausalStoppingTimeAverageBehaviorExpectedRegretProcess,
    stoppedValue] using
      (ae_tendsto_apply_randomPrefix hprocess hprefix)

/-- Every capped stopped behavior expected-regret coordinate is measurable. -/
theorem
    measurable_selfConsistentScheduledNaturalCausalInverseSqrtThresholdCappedStoppedBehaviorExpectedRegret
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
          (selfConsistentScheduledNaturalCausalInverseSqrtThresholdCappedDoubleLinearRawWindowFirstPassageStoppingPrefix
            mdp initialState rewardSource initialTable defaultState varianceProxy
              baseVisitFloor)
          scheduleIndex) := by
  exact
    measurable_selfConsistentScheduledNaturalCausalStoppingTimeAverageBehaviorExpectedRegretProcess
      mdp initialState rewardSource initialTable defaultState varianceProxy
        baseVisitFloor _ scheduleIndex (by
          simpa [
            selfConsistentScheduledNaturalCausalInverseSqrtThresholdCappedDoubleLinearRawWindowFirstPassageStoppingPrefix] using
            (selfConsistentScheduledNaturalCausalCappedDoubleLinearRawWindowFirstPassageStoppingPrefix_isStoppingTime
              mdp initialState rewardSource initialTable defaultState
                varianceProxy baseVisitFloor
                  selfConsistentScheduledNaturalCausalInverseSqrtFirstPassageThreshold
                    scheduleIndex))

/-- Every capped stopped behavior expected-regret coordinate belongs to
`L1`. -/
theorem
    memLp_one_selfConsistentScheduledNaturalCausalInverseSqrtThresholdCappedStoppedBehaviorExpectedRegret
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
      selfConsistentScheduledNaturalCausalInverseSqrtThresholdCappedDoubleLinearRawWindowFirstPassageStoppingPrefix
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor
    let behaviorProcess :=
      selfConsistentScheduledNaturalCausalStoppingTimeAverageBehaviorExpectedRegretProcess
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor stoppingPrefix
    MemLp (behaviorProcess scheduleIndex) 1 source.trajectoryMeasure := by
  dsimp only
  rw [memLp_one_iff_integrable]
  refine Integrable.of_bound
    (measurable_selfConsistentScheduledNaturalCausalInverseSqrtThresholdCappedStoppedBehaviorExpectedRegret
      mdp initialState rewardSource initialTable defaultState varianceProxy
        baseVisitFloor scheduleIndex).aestronglyMeasurable
    (2 * (mdp.horizon : Real)) ?_
  exact Filter.Eventually.of_forall fun trajectory => by
    rw [Real.norm_eq_abs, abs_of_nonneg]
    · exact
        selfConsistentScheduledNaturalCausalStoppingTimeAverageBehaviorExpectedRegretProcess_le_two_mul_horizon
          mdp initialState rewardSource initialTable defaultState varianceProxy
            baseVisitFloor hrewardBound _ scheduleIndex trajectory
    · exact
        selfConsistentScheduledNaturalCausalStoppingTimeAverageBehaviorExpectedRegretProcess_nonneg
          mdp initialState rewardSource initialTable defaultState varianceProxy
            baseVisitFloor _ scheduleIndex trajectory

/-- The exponent-one norm of the capped stopped behavior expected regret
tends to zero. -/
theorem
    eLpNorm_one_selfConsistentScheduledNaturalCausalInverseSqrtThresholdCappedStoppedBehaviorExpectedRegret_tendsto_zero
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
      selfConsistentScheduledNaturalCausalInverseSqrtThresholdCappedDoubleLinearRawWindowFirstPassageStoppingPrefix
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
  let source := selfConsistentScheduledCausalSource mdp initialState
    rewardSource initialTable defaultState varianceProxy baseVisitFloor
  let stoppingPrefix :=
    selfConsistentScheduledNaturalCausalInverseSqrtThresholdCappedDoubleLinearRawWindowFirstPassageStoppingPrefix
      mdp initialState rewardSource initialTable defaultState varianceProxy
        baseVisitFloor
  let behaviorProcess :=
    selfConsistentScheduledNaturalCausalStoppingTimeAverageBehaviorExpectedRegretProcess
      mdp initialState rewardSource initialTable defaultState varianceProxy
        baseVisitFloor stoppingPrefix
  have hmeas : forall scheduleIndex,
      AEStronglyMeasurable (behaviorProcess scheduleIndex)
        source.trajectoryMeasure := fun scheduleIndex =>
    (measurable_selfConsistentScheduledNaturalCausalInverseSqrtThresholdCappedStoppedBehaviorExpectedRegret
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
      (selfConsistentScheduledCausalSource_inverseSqrtThresholdCapped_stoppedBehaviorExpectedRegret_tendstoAlmostEverywhere_zero
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
  have habsLimit : Tendsto
      (fun scheduleIndex => integral source.trajectoryMeasure
        (fun trajectory => |behaviorProcess scheduleIndex trajectory|))
      atTop (nhds 0) := by
    rw [habs]
    exact hintegral
  have hofReal := (ENNReal.continuous_ofReal.tendsto 0).comp habsLimit
  have hnormEq : forall scheduleIndex,
      eLpNorm (behaviorProcess scheduleIndex) 1 source.trajectoryMeasure =
        ENNReal.ofReal
          (integral source.trajectoryMeasure
            (fun trajectory => |behaviorProcess scheduleIndex trajectory|)) :=
    fun scheduleIndex => by
      rw [MemLp.eLpNorm_eq_integral_rpow_norm one_ne_zero ENNReal.one_ne_top]
      · simp [Real.norm_eq_abs]
      · simpa only [source, stoppingPrefix, behaviorProcess] using
          (memLp_one_selfConsistentScheduledNaturalCausalInverseSqrtThresholdCappedStoppedBehaviorExpectedRegret
            mdp initialState rewardSource initialTable defaultState varianceProxy
              baseVisitFloor hrewardBound scheduleIndex)
  change Tendsto
    (fun scheduleIndex =>
      eLpNorm (behaviorProcess scheduleIndex) 1 source.trajectoryMeasure)
    atTop (nhds 0)
  simpa only [Function.comp_apply, ENNReal.ofReal_zero, hnormEq] using hofReal

/-- Signed expectation of the capped stopped behavior expected regret tends
to zero. -/
theorem
    selfConsistentScheduledNaturalCausalInverseSqrtThresholdCappedStoppedBehaviorExpectedRegretIntegral_tendsto_zero
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
      selfConsistentScheduledNaturalCausalInverseSqrtThresholdCappedDoubleLinearRawWindowFirstPassageStoppingPrefix
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
      memLp_one_selfConsistentScheduledNaturalCausalInverseSqrtThresholdCappedStoppedBehaviorExpectedRegret
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor hrewardBound scheduleIndex)
    (eLpNorm_one_selfConsistentScheduledNaturalCausalInverseSqrtThresholdCappedStoppedBehaviorExpectedRegret_tendsto_zero
      mdp initialState rewardSource varianceProxy hvarianceProxy law initialTable
        defaultState support baseVisitFloor hbaseFloor hrewardBound hhorizon
          hbaseVisitFloor)

/-- Every capped stopped return-deviation coordinate belongs to `L1`. -/
theorem
    memLp_one_selfConsistentScheduledNaturalCausalInverseSqrtThresholdCappedStoppedReturnDeviation
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
      selfConsistentScheduledNaturalCausalInverseSqrtThresholdCappedDoubleLinearRawWindowFirstPassageStoppingPrefix
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
    selfConsistentScheduledNaturalCausalInverseSqrtThresholdCappedDoubleLinearRawWindowFirstPassageStoppingPrefix
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
      (memLp_one_selfConsistentScheduledNaturalCausalInverseSqrtThresholdCappedStoppedBehaviorExpectedRegret
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor hrewardBound scheduleIndex)
  have hrealized : MemLp (realizedProcess scheduleIndex) 1
      source.trajectoryMeasure := by
    simpa only [source, stoppingPrefix, realizedProcess] using
      (memLp_one_selfConsistentScheduledNaturalCausalInverseSqrtThresholdCappedStoppedAverageRealizedBehaviorRegret
        mdp initialState rewardSource varianceProxy hvarianceProxy law initialTable
          defaultState support baseVisitFloor hbaseFloor hrewardBound
            (lt_trans (by decide : 0 < 4) hhorizon) hbaseVisitFloor scheduleIndex)
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

/-- Exponent-one norm of the capped stopped return deviation tends to zero. -/
theorem
    eLpNorm_one_selfConsistentScheduledNaturalCausalInverseSqrtThresholdCappedStoppedReturnDeviation_tendsto_zero
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
      selfConsistentScheduledNaturalCausalInverseSqrtThresholdCappedDoubleLinearRawWindowFirstPassageStoppingPrefix
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
    selfConsistentScheduledNaturalCausalInverseSqrtThresholdCappedDoubleLinearRawWindowFirstPassageStoppingPrefix
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
      (eLpNorm_one_selfConsistentScheduledNaturalCausalInverseSqrtThresholdCappedStoppedBehaviorExpectedRegret_tendsto_zero
        mdp initialState rewardSource varianceProxy hvarianceProxy law initialTable
          defaultState support baseVisitFloor hbaseFloor hrewardBound
            (lt_trans (by decide : 0 < 4) hhorizon) hbaseVisitFloor)
  have hrealizedNorm : Tendsto
      (fun scheduleIndex =>
        eLpNorm (realizedProcess scheduleIndex) 1 source.trajectoryMeasure)
      atTop (nhds 0) := by
    simpa only [source, stoppingPrefix, realizedProcess] using
      (eLpNorm_one_selfConsistentScheduledNaturalCausalInverseSqrtThresholdCappedStoppedAverageRealizedBehaviorRegret_tendsto_zero
        mdp initialState rewardSource varianceProxy hvarianceProxy law initialTable
          defaultState support baseVisitFloor hbaseFloor hrewardBound
            (lt_trans (by decide : 0 < 4) hhorizon) hbaseVisitFloor)
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
        (memLp_one_selfConsistentScheduledNaturalCausalInverseSqrtThresholdCappedStoppedBehaviorExpectedRegret
          mdp initialState rewardSource initialTable defaultState varianceProxy
            baseVisitFloor hrewardBound scheduleIndex)
  have hrealizedMem : forall scheduleIndex,
      MemLp (realizedProcess scheduleIndex) 1 source.trajectoryMeasure :=
    fun scheduleIndex => by
      simpa only [source, stoppingPrefix, realizedProcess] using
        (memLp_one_selfConsistentScheduledNaturalCausalInverseSqrtThresholdCappedStoppedAverageRealizedBehaviorRegret
          mdp initialState rewardSource varianceProxy hvarianceProxy law initialTable
            defaultState support baseVisitFloor hbaseFloor hrewardBound
              (lt_trans (by decide : 0 < 4) hhorizon) hbaseVisitFloor scheduleIndex)
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
  change Tendsto
    (fun scheduleIndex =>
      eLpNorm (returnProcess scheduleIndex) 1 source.trajectoryMeasure)
    atTop (nhds 0)
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le'
    tendsto_const_nhds hsum
    (Filter.Eventually.of_forall fun _ => bot_le)
    (Filter.Eventually.of_forall fun scheduleIndex => by
      rw [eLpNorm_congr_ae (heq scheduleIndex)]
      exact eLpNorm_sub_le
        (hbehaviorMem scheduleIndex).aestronglyMeasurable
        (hrealizedMem scheduleIndex).aestronglyMeasurable (by norm_num))

/-- Signed expectation of the capped stopped return deviation tends to zero. -/
theorem
    selfConsistentScheduledNaturalCausalInverseSqrtThresholdCappedStoppedReturnDeviationIntegral_tendsto_zero
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
      selfConsistentScheduledNaturalCausalInverseSqrtThresholdCappedDoubleLinearRawWindowFirstPassageStoppingPrefix
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
      memLp_one_selfConsistentScheduledNaturalCausalInverseSqrtThresholdCappedStoppedReturnDeviation
        mdp initialState rewardSource varianceProxy hvarianceProxy law initialTable
          defaultState support baseVisitFloor hbaseFloor hrewardBound hhorizon
            hbaseVisitFloor scheduleIndex)
    (eLpNorm_one_selfConsistentScheduledNaturalCausalInverseSqrtThresholdCappedStoppedReturnDeviation_tendsto_zero
      mdp initialState rewardSource varianceProxy hvarianceProxy law initialTable
        defaultState support baseVisitFloor hbaseFloor hrewardBound hhorizon
          hbaseVisitFloor)

/-- The uncapped-minus-capped stopped behavior expected-regret coordinate
belongs to `L1`. -/
theorem
    memLp_one_selfConsistentScheduledNaturalCausalInverseSqrtThresholdCappedUnboundedHittingAfterStoppedBehaviorExpectedRegretDifference
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
    let cappedStoppingPrefix :=
      selfConsistentScheduledNaturalCausalInverseSqrtThresholdCappedDoubleLinearRawWindowFirstPassageStoppingPrefix
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor
    let uncappedStoppingPrefix :=
      selfConsistentScheduledNaturalCausalInverseSqrtThresholdUnboundedHittingAfterStoppingPrefix
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor
    let cappedBehavior :=
      selfConsistentScheduledNaturalCausalStoppingTimeAverageBehaviorExpectedRegretProcess
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor cappedStoppingPrefix
    let uncappedBehavior :=
      selfConsistentScheduledNaturalCausalStoppingTimeAverageBehaviorExpectedRegretProcess
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor uncappedStoppingPrefix
    MemLp (uncappedBehavior scheduleIndex - cappedBehavior scheduleIndex) 1
      source.trajectoryMeasure := by
  dsimp only
  exact
    (memLp_one_selfConsistentScheduledNaturalCausalInverseSqrtThresholdUnboundedHittingAfterStoppedBehaviorExpectedRegret
      mdp initialState rewardSource initialTable defaultState varianceProxy
        baseVisitFloor hrewardBound scheduleIndex).sub
      (memLp_one_selfConsistentScheduledNaturalCausalInverseSqrtThresholdCappedStoppedBehaviorExpectedRegret
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor hrewardBound scheduleIndex)

/-- Capped and uncapped stopped behavior expected regret are asymptotically
equivalent in exponent-one norm. -/
theorem
    eLpNorm_one_selfConsistentScheduledNaturalCausalInverseSqrtThresholdCappedUnboundedHittingAfterStoppedBehaviorExpectedRegretDifference_tendsto_zero
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
    let cappedStoppingPrefix :=
      selfConsistentScheduledNaturalCausalInverseSqrtThresholdCappedDoubleLinearRawWindowFirstPassageStoppingPrefix
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor
    let uncappedStoppingPrefix :=
      selfConsistentScheduledNaturalCausalInverseSqrtThresholdUnboundedHittingAfterStoppingPrefix
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor
    let cappedBehavior :=
      selfConsistentScheduledNaturalCausalStoppingTimeAverageBehaviorExpectedRegretProcess
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor cappedStoppingPrefix
    let uncappedBehavior :=
      selfConsistentScheduledNaturalCausalStoppingTimeAverageBehaviorExpectedRegretProcess
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor uncappedStoppingPrefix
    Tendsto
      (fun scheduleIndex => eLpNorm
        (uncappedBehavior scheduleIndex - cappedBehavior scheduleIndex) 1
          source.trajectoryMeasure)
      atTop (nhds 0) := by
  dsimp only
  let source := selfConsistentScheduledCausalSource mdp initialState
    rewardSource initialTable defaultState varianceProxy baseVisitFloor
  let cappedStoppingPrefix :=
    selfConsistentScheduledNaturalCausalInverseSqrtThresholdCappedDoubleLinearRawWindowFirstPassageStoppingPrefix
      mdp initialState rewardSource initialTable defaultState varianceProxy
        baseVisitFloor
  let uncappedStoppingPrefix :=
    selfConsistentScheduledNaturalCausalInverseSqrtThresholdUnboundedHittingAfterStoppingPrefix
      mdp initialState rewardSource initialTable defaultState varianceProxy
        baseVisitFloor
  let cappedBehavior :=
    selfConsistentScheduledNaturalCausalStoppingTimeAverageBehaviorExpectedRegretProcess
      mdp initialState rewardSource initialTable defaultState varianceProxy
        baseVisitFloor cappedStoppingPrefix
  let uncappedBehavior :=
    selfConsistentScheduledNaturalCausalStoppingTimeAverageBehaviorExpectedRegretProcess
      mdp initialState rewardSource initialTable defaultState varianceProxy
        baseVisitFloor uncappedStoppingPrefix
  have huncappedNorm : Tendsto
      (fun scheduleIndex =>
        eLpNorm (uncappedBehavior scheduleIndex) 1 source.trajectoryMeasure)
      atTop (nhds 0) := by
    simpa only [source, uncappedStoppingPrefix, uncappedBehavior] using
      (eLpNorm_one_selfConsistentScheduledNaturalCausalInverseSqrtThresholdUnboundedHittingAfterStoppedBehaviorExpectedRegret_tendsto_zero
        mdp initialState rewardSource varianceProxy hvarianceProxy law initialTable
          defaultState support baseVisitFloor hbaseFloor hrewardBound hhorizon
            hbaseVisitFloor)
  have hcappedNorm : Tendsto
      (fun scheduleIndex =>
        eLpNorm (cappedBehavior scheduleIndex) 1 source.trajectoryMeasure)
      atTop (nhds 0) := by
    simpa only [source, cappedStoppingPrefix, cappedBehavior] using
      (eLpNorm_one_selfConsistentScheduledNaturalCausalInverseSqrtThresholdCappedStoppedBehaviorExpectedRegret_tendsto_zero
        mdp initialState rewardSource varianceProxy hvarianceProxy law initialTable
          defaultState support baseVisitFloor hbaseFloor hrewardBound hhorizon
            hbaseVisitFloor)
  have hsum : Tendsto
      (fun scheduleIndex =>
        eLpNorm (uncappedBehavior scheduleIndex) 1 source.trajectoryMeasure +
          eLpNorm (cappedBehavior scheduleIndex) 1 source.trajectoryMeasure)
      atTop (nhds 0) := by
    simpa only [zero_add] using huncappedNorm.add hcappedNorm
  have huncappedMem : forall scheduleIndex,
      MemLp (uncappedBehavior scheduleIndex) 1 source.trajectoryMeasure :=
    fun scheduleIndex => by
      simpa only [source, uncappedStoppingPrefix, uncappedBehavior] using
        (memLp_one_selfConsistentScheduledNaturalCausalInverseSqrtThresholdUnboundedHittingAfterStoppedBehaviorExpectedRegret
          mdp initialState rewardSource initialTable defaultState varianceProxy
            baseVisitFloor hrewardBound scheduleIndex)
  have hcappedMem : forall scheduleIndex,
      MemLp (cappedBehavior scheduleIndex) 1 source.trajectoryMeasure :=
    fun scheduleIndex => by
      simpa only [source, cappedStoppingPrefix, cappedBehavior] using
        (memLp_one_selfConsistentScheduledNaturalCausalInverseSqrtThresholdCappedStoppedBehaviorExpectedRegret
          mdp initialState rewardSource initialTable defaultState varianceProxy
            baseVisitFloor hrewardBound scheduleIndex)
  change Tendsto
    (fun scheduleIndex => eLpNorm
      (uncappedBehavior scheduleIndex - cappedBehavior scheduleIndex) 1
        source.trajectoryMeasure)
    atTop (nhds 0)
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le'
    tendsto_const_nhds hsum
    (Filter.Eventually.of_forall fun _ => bot_le)
    (Filter.Eventually.of_forall fun scheduleIndex =>
      eLpNorm_sub_le
        (huncappedMem scheduleIndex).aestronglyMeasurable
        (hcappedMem scheduleIndex).aestronglyMeasurable (by norm_num))

/-- Signed integral of the stopped behavior truncation difference tends to
zero. -/
theorem
    selfConsistentScheduledNaturalCausalInverseSqrtThresholdCappedUnboundedHittingAfterStoppedBehaviorExpectedRegretDifferenceIntegral_tendsto_zero
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
    let cappedStoppingPrefix :=
      selfConsistentScheduledNaturalCausalInverseSqrtThresholdCappedDoubleLinearRawWindowFirstPassageStoppingPrefix
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor
    let uncappedStoppingPrefix :=
      selfConsistentScheduledNaturalCausalInverseSqrtThresholdUnboundedHittingAfterStoppingPrefix
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor
    let cappedBehavior :=
      selfConsistentScheduledNaturalCausalStoppingTimeAverageBehaviorExpectedRegretProcess
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor cappedStoppingPrefix
    let uncappedBehavior :=
      selfConsistentScheduledNaturalCausalStoppingTimeAverageBehaviorExpectedRegretProcess
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor uncappedStoppingPrefix
    Tendsto
      (fun scheduleIndex => integral source.trajectoryMeasure
        (uncappedBehavior scheduleIndex - cappedBehavior scheduleIndex))
      atTop (nhds 0) := by
  dsimp only
  exact integral_tendsto_zero_of_memLp_one_of_eLpNorm_tendsto_zero
    (fun scheduleIndex =>
      memLp_one_selfConsistentScheduledNaturalCausalInverseSqrtThresholdCappedUnboundedHittingAfterStoppedBehaviorExpectedRegretDifference
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor hrewardBound scheduleIndex)
    (eLpNorm_one_selfConsistentScheduledNaturalCausalInverseSqrtThresholdCappedUnboundedHittingAfterStoppedBehaviorExpectedRegretDifference_tendsto_zero
      mdp initialState rewardSource varianceProxy hvarianceProxy law initialTable
        defaultState support baseVisitFloor hbaseFloor hrewardBound hhorizon
          hbaseVisitFloor)

/-- The semantic return-difference is exactly the behavior-value difference
minus the realized-regret difference. -/
theorem
    selfConsistentScheduledNaturalCausalInverseSqrtThresholdCappedUnboundedHittingAfterStoppedReturnDeviationDifference_eq_behaviorExpectedRegretDifference_sub_realizedBehaviorRegretDifference
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
    let cappedStoppingPrefix :=
      selfConsistentScheduledNaturalCausalInverseSqrtThresholdCappedDoubleLinearRawWindowFirstPassageStoppingPrefix
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor
    let uncappedStoppingPrefix :=
      selfConsistentScheduledNaturalCausalInverseSqrtThresholdUnboundedHittingAfterStoppingPrefix
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor
    let cappedBehavior :=
      selfConsistentScheduledNaturalCausalStoppingTimeAverageBehaviorExpectedRegretProcess
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor cappedStoppingPrefix
    let uncappedBehavior :=
      selfConsistentScheduledNaturalCausalStoppingTimeAverageBehaviorExpectedRegretProcess
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor uncappedStoppingPrefix
    let cappedRealized :=
      selfConsistentScheduledNaturalCausalStoppingTimeAverageRealizedBehaviorRegretProcess
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor cappedStoppingPrefix
    let uncappedRealized :=
      selfConsistentScheduledNaturalCausalStoppingTimeAverageRealizedBehaviorRegretProcess
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor uncappedStoppingPrefix
    let cappedReturn :=
      selfConsistentScheduledNaturalCausalStoppingTimeAverageReturnDeviationProcess
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor cappedStoppingPrefix
    let uncappedReturn :=
      selfConsistentScheduledNaturalCausalStoppingTimeAverageReturnDeviationProcess
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor uncappedStoppingPrefix
    uncappedReturn scheduleIndex trajectory -
        cappedReturn scheduleIndex trajectory =
      (uncappedBehavior scheduleIndex trajectory -
          cappedBehavior scheduleIndex trajectory) -
        (uncappedRealized scheduleIndex trajectory -
          cappedRealized scheduleIndex trajectory) := by
  dsimp only
  have huncapped :=
    selfConsistentScheduledNaturalCausalStoppingTimeAverageRealizedBehaviorRegretProcess_eq_behaviorExpected_sub_returnDeviation
      mdp initialState rewardSource initialTable defaultState varianceProxy
        baseVisitFloor
          (selfConsistentScheduledNaturalCausalInverseSqrtThresholdUnboundedHittingAfterStoppingPrefix
            mdp initialState rewardSource initialTable defaultState varianceProxy
              baseVisitFloor)
          scheduleIndex trajectory
  have hcapped :=
    selfConsistentScheduledNaturalCausalStoppingTimeAverageRealizedBehaviorRegretProcess_eq_behaviorExpected_sub_returnDeviation
      mdp initialState rewardSource initialTable defaultState varianceProxy
        baseVisitFloor
          (selfConsistentScheduledNaturalCausalInverseSqrtThresholdCappedDoubleLinearRawWindowFirstPassageStoppingPrefix
            mdp initialState rewardSource initialTable defaultState varianceProxy
              baseVisitFloor)
          scheduleIndex trajectory
  linarith

/-- The uncapped-minus-capped stopped return-deviation coordinate belongs to
`L1`. -/
theorem
    memLp_one_selfConsistentScheduledNaturalCausalInverseSqrtThresholdCappedUnboundedHittingAfterStoppedReturnDeviationDifference
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
    let cappedStoppingPrefix :=
      selfConsistentScheduledNaturalCausalInverseSqrtThresholdCappedDoubleLinearRawWindowFirstPassageStoppingPrefix
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor
    let uncappedStoppingPrefix :=
      selfConsistentScheduledNaturalCausalInverseSqrtThresholdUnboundedHittingAfterStoppingPrefix
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor
    let cappedReturn :=
      selfConsistentScheduledNaturalCausalStoppingTimeAverageReturnDeviationProcess
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor cappedStoppingPrefix
    let uncappedReturn :=
      selfConsistentScheduledNaturalCausalStoppingTimeAverageReturnDeviationProcess
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor uncappedStoppingPrefix
    MemLp (uncappedReturn scheduleIndex - cappedReturn scheduleIndex) 1
      source.trajectoryMeasure := by
  dsimp only
  exact
    (memLp_one_selfConsistentScheduledNaturalCausalInverseSqrtThresholdUnboundedHittingAfterStoppedReturnDeviation
      mdp initialState rewardSource varianceProxy hvarianceProxy law initialTable
        defaultState support baseVisitFloor hbaseFloor hrewardBound hhorizon
          hbaseVisitFloor scheduleIndex).sub
      (memLp_one_selfConsistentScheduledNaturalCausalInverseSqrtThresholdCappedStoppedReturnDeviation
        mdp initialState rewardSource varianceProxy hvarianceProxy law initialTable
          defaultState support baseVisitFloor hbaseFloor hrewardBound hhorizon
            hbaseVisitFloor scheduleIndex)

/-- Capped and uncapped stopped return deviation are asymptotically equivalent
in exponent-one norm. -/
theorem
    eLpNorm_one_selfConsistentScheduledNaturalCausalInverseSqrtThresholdCappedUnboundedHittingAfterStoppedReturnDeviationDifference_tendsto_zero
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
    let cappedStoppingPrefix :=
      selfConsistentScheduledNaturalCausalInverseSqrtThresholdCappedDoubleLinearRawWindowFirstPassageStoppingPrefix
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor
    let uncappedStoppingPrefix :=
      selfConsistentScheduledNaturalCausalInverseSqrtThresholdUnboundedHittingAfterStoppingPrefix
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor
    let cappedReturn :=
      selfConsistentScheduledNaturalCausalStoppingTimeAverageReturnDeviationProcess
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor cappedStoppingPrefix
    let uncappedReturn :=
      selfConsistentScheduledNaturalCausalStoppingTimeAverageReturnDeviationProcess
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor uncappedStoppingPrefix
    Tendsto
      (fun scheduleIndex => eLpNorm
        (uncappedReturn scheduleIndex - cappedReturn scheduleIndex) 1
          source.trajectoryMeasure)
      atTop (nhds 0) := by
  dsimp only
  let source := selfConsistentScheduledCausalSource mdp initialState
    rewardSource initialTable defaultState varianceProxy baseVisitFloor
  let cappedStoppingPrefix :=
    selfConsistentScheduledNaturalCausalInverseSqrtThresholdCappedDoubleLinearRawWindowFirstPassageStoppingPrefix
      mdp initialState rewardSource initialTable defaultState varianceProxy
        baseVisitFloor
  let uncappedStoppingPrefix :=
    selfConsistentScheduledNaturalCausalInverseSqrtThresholdUnboundedHittingAfterStoppingPrefix
      mdp initialState rewardSource initialTable defaultState varianceProxy
        baseVisitFloor
  let cappedBehavior :=
    selfConsistentScheduledNaturalCausalStoppingTimeAverageBehaviorExpectedRegretProcess
      mdp initialState rewardSource initialTable defaultState varianceProxy
        baseVisitFloor cappedStoppingPrefix
  let uncappedBehavior :=
    selfConsistentScheduledNaturalCausalStoppingTimeAverageBehaviorExpectedRegretProcess
      mdp initialState rewardSource initialTable defaultState varianceProxy
        baseVisitFloor uncappedStoppingPrefix
  let cappedRealized :=
    selfConsistentScheduledNaturalCausalStoppingTimeAverageRealizedBehaviorRegretProcess
      mdp initialState rewardSource initialTable defaultState varianceProxy
        baseVisitFloor cappedStoppingPrefix
  let uncappedRealized :=
    selfConsistentScheduledNaturalCausalStoppingTimeAverageRealizedBehaviorRegretProcess
      mdp initialState rewardSource initialTable defaultState varianceProxy
        baseVisitFloor uncappedStoppingPrefix
  let cappedReturn :=
    selfConsistentScheduledNaturalCausalStoppingTimeAverageReturnDeviationProcess
      mdp initialState rewardSource initialTable defaultState varianceProxy
        baseVisitFloor cappedStoppingPrefix
  let uncappedReturn :=
    selfConsistentScheduledNaturalCausalStoppingTimeAverageReturnDeviationProcess
      mdp initialState rewardSource initialTable defaultState varianceProxy
        baseVisitFloor uncappedStoppingPrefix
  let behaviorDifference := fun scheduleIndex =>
    uncappedBehavior scheduleIndex - cappedBehavior scheduleIndex
  let realizedDifference := fun scheduleIndex =>
    uncappedRealized scheduleIndex - cappedRealized scheduleIndex
  have hbehaviorNorm : Tendsto
      (fun scheduleIndex =>
        eLpNorm (behaviorDifference scheduleIndex) 1 source.trajectoryMeasure)
      atTop (nhds 0) := by
    simpa only [source, cappedStoppingPrefix, uncappedStoppingPrefix,
      cappedBehavior, uncappedBehavior, behaviorDifference] using
      (eLpNorm_one_selfConsistentScheduledNaturalCausalInverseSqrtThresholdCappedUnboundedHittingAfterStoppedBehaviorExpectedRegretDifference_tendsto_zero
        mdp initialState rewardSource varianceProxy hvarianceProxy law initialTable
          defaultState support baseVisitFloor hbaseFloor hrewardBound
            (lt_trans (by decide : 0 < 4) hhorizon) hbaseVisitFloor)
  have hrealizedNorm : Tendsto
      (fun scheduleIndex =>
        eLpNorm (realizedDifference scheduleIndex) 1 source.trajectoryMeasure)
      atTop (nhds 0) := by
    simpa only [source, cappedStoppingPrefix, uncappedStoppingPrefix,
      cappedRealized, uncappedRealized, realizedDifference] using
      (eLpNorm_one_selfConsistentScheduledNaturalCausalInverseSqrtThresholdCappedUnboundedHittingAfterStoppedAverageRealizedBehaviorRegretDifference_tendsto_zero
        mdp initialState rewardSource varianceProxy hvarianceProxy law initialTable
          defaultState support baseVisitFloor hbaseFloor hrewardBound hhorizon
            hbaseVisitFloor)
  have hsum : Tendsto
      (fun scheduleIndex =>
        eLpNorm (behaviorDifference scheduleIndex) 1 source.trajectoryMeasure +
          eLpNorm (realizedDifference scheduleIndex) 1 source.trajectoryMeasure)
      atTop (nhds 0) := by
    simpa only [zero_add] using hbehaviorNorm.add hrealizedNorm
  have hbehaviorMem : forall scheduleIndex,
      MemLp (behaviorDifference scheduleIndex) 1 source.trajectoryMeasure :=
    fun scheduleIndex => by
      simpa only [source, cappedStoppingPrefix, uncappedStoppingPrefix,
        cappedBehavior, uncappedBehavior, behaviorDifference] using
        (memLp_one_selfConsistentScheduledNaturalCausalInverseSqrtThresholdCappedUnboundedHittingAfterStoppedBehaviorExpectedRegretDifference
          mdp initialState rewardSource initialTable defaultState varianceProxy
            baseVisitFloor hrewardBound scheduleIndex)
  have hrealizedMem : forall scheduleIndex,
      MemLp (realizedDifference scheduleIndex) 1 source.trajectoryMeasure :=
    fun scheduleIndex => by
      simpa only [source, cappedStoppingPrefix, uncappedStoppingPrefix,
        cappedRealized, uncappedRealized, realizedDifference] using
        (memLp_one_selfConsistentScheduledNaturalCausalInverseSqrtThresholdCappedUnboundedHittingAfterStoppedAverageRealizedBehaviorRegretDifference
          mdp initialState rewardSource varianceProxy hvarianceProxy law initialTable
            defaultState support baseVisitFloor hbaseFloor hrewardBound hhorizon
              hbaseVisitFloor scheduleIndex)
  have heq : forall scheduleIndex,
      uncappedReturn scheduleIndex - cappedReturn scheduleIndex
        =ᵐ[source.trajectoryMeasure]
          behaviorDifference scheduleIndex - realizedDifference scheduleIndex :=
    fun scheduleIndex => Filter.Eventually.of_forall fun trajectory => by
      simpa only [cappedStoppingPrefix, uncappedStoppingPrefix,
        cappedBehavior, uncappedBehavior, cappedRealized, uncappedRealized,
        cappedReturn, uncappedReturn, behaviorDifference, realizedDifference]
        using
          (selfConsistentScheduledNaturalCausalInverseSqrtThresholdCappedUnboundedHittingAfterStoppedReturnDeviationDifference_eq_behaviorExpectedRegretDifference_sub_realizedBehaviorRegretDifference
            mdp initialState rewardSource initialTable defaultState varianceProxy
              baseVisitFloor scheduleIndex trajectory)
  change Tendsto
    (fun scheduleIndex => eLpNorm
      (uncappedReturn scheduleIndex - cappedReturn scheduleIndex) 1
        source.trajectoryMeasure)
    atTop (nhds 0)
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le'
    tendsto_const_nhds hsum
    (Filter.Eventually.of_forall fun _ => bot_le)
    (Filter.Eventually.of_forall fun scheduleIndex => by
      rw [eLpNorm_congr_ae (heq scheduleIndex)]
      exact eLpNorm_sub_le
        (hbehaviorMem scheduleIndex).aestronglyMeasurable
        (hrealizedMem scheduleIndex).aestronglyMeasurable (by norm_num))

/-- Signed integral of the stopped return-deviation truncation difference
tends to zero. -/
theorem
    selfConsistentScheduledNaturalCausalInverseSqrtThresholdCappedUnboundedHittingAfterStoppedReturnDeviationDifferenceIntegral_tendsto_zero
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
    let cappedStoppingPrefix :=
      selfConsistentScheduledNaturalCausalInverseSqrtThresholdCappedDoubleLinearRawWindowFirstPassageStoppingPrefix
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor
    let uncappedStoppingPrefix :=
      selfConsistentScheduledNaturalCausalInverseSqrtThresholdUnboundedHittingAfterStoppingPrefix
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor
    let cappedReturn :=
      selfConsistentScheduledNaturalCausalStoppingTimeAverageReturnDeviationProcess
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor cappedStoppingPrefix
    let uncappedReturn :=
      selfConsistentScheduledNaturalCausalStoppingTimeAverageReturnDeviationProcess
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor uncappedStoppingPrefix
    Tendsto
      (fun scheduleIndex => integral source.trajectoryMeasure
        (uncappedReturn scheduleIndex - cappedReturn scheduleIndex))
      atTop (nhds 0) := by
  dsimp only
  exact integral_tendsto_zero_of_memLp_one_of_eLpNorm_tendsto_zero
    (fun scheduleIndex =>
      memLp_one_selfConsistentScheduledNaturalCausalInverseSqrtThresholdCappedUnboundedHittingAfterStoppedReturnDeviationDifference
        mdp initialState rewardSource varianceProxy hvarianceProxy law initialTable
          defaultState support baseVisitFloor hbaseFloor hrewardBound hhorizon
            hbaseVisitFloor scheduleIndex)
    (eLpNorm_one_selfConsistentScheduledNaturalCausalInverseSqrtThresholdCappedUnboundedHittingAfterStoppedReturnDeviationDifference_tendsto_zero
      mdp initialState rewardSource varianceProxy hvarianceProxy law initialTable
        defaultState support baseVisitFloor hbaseFloor hrewardBound hhorizon
          hbaseVisitFloor)

/-- Terminal componentwise semantic and `L1` truncation-equivalence package
for the capped and genuine uncapped first-passage prefixes. -/
theorem
    selfConsistentScheduledCausalSource_inverseSqrtThresholdCappedUnboundedHittingAfter_stoppedBehaviorExpectedRegret_and_returnDeviation_L1_truncation_equivalence
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
    let cappedStoppingPrefix :=
      selfConsistentScheduledNaturalCausalInverseSqrtThresholdCappedDoubleLinearRawWindowFirstPassageStoppingPrefix
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor
    let uncappedStoppingPrefix :=
      selfConsistentScheduledNaturalCausalInverseSqrtThresholdUnboundedHittingAfterStoppingPrefix
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor
    let cappedBehavior :=
      selfConsistentScheduledNaturalCausalStoppingTimeAverageBehaviorExpectedRegretProcess
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor cappedStoppingPrefix
    let uncappedBehavior :=
      selfConsistentScheduledNaturalCausalStoppingTimeAverageBehaviorExpectedRegretProcess
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor uncappedStoppingPrefix
    let cappedRealized :=
      selfConsistentScheduledNaturalCausalStoppingTimeAverageRealizedBehaviorRegretProcess
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor cappedStoppingPrefix
    let uncappedRealized :=
      selfConsistentScheduledNaturalCausalStoppingTimeAverageRealizedBehaviorRegretProcess
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor uncappedStoppingPrefix
    let cappedReturn :=
      selfConsistentScheduledNaturalCausalStoppingTimeAverageReturnDeviationProcess
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor cappedStoppingPrefix
    let uncappedReturn :=
      selfConsistentScheduledNaturalCausalStoppingTimeAverageReturnDeviationProcess
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor uncappedStoppingPrefix
    (forall scheduleIndex,
      Measurable (cappedBehavior scheduleIndex) /\
        MemLp (cappedBehavior scheduleIndex) 1 source.trajectoryMeasure /\
        MemLp (cappedReturn scheduleIndex) 1 source.trajectoryMeasure /\
        MemLp (uncappedBehavior scheduleIndex - cappedBehavior scheduleIndex) 1
          source.trajectoryMeasure /\
        MemLp (uncappedReturn scheduleIndex - cappedReturn scheduleIndex) 1
          source.trajectoryMeasure) /\
      (forall scheduleIndex trajectory,
        0 <= cappedBehavior scheduleIndex trajectory /\
          cappedBehavior scheduleIndex trajectory <=
            2 * (mdp.horizon : Real) /\
          cappedRealized scheduleIndex trajectory =
            cappedBehavior scheduleIndex trajectory -
              cappedReturn scheduleIndex trajectory /\
          uncappedRealized scheduleIndex trajectory =
            uncappedBehavior scheduleIndex trajectory -
              uncappedReturn scheduleIndex trajectory /\
          uncappedReturn scheduleIndex trajectory -
              cappedReturn scheduleIndex trajectory =
            (uncappedBehavior scheduleIndex trajectory -
                cappedBehavior scheduleIndex trajectory) -
              (uncappedRealized scheduleIndex trajectory -
                cappedRealized scheduleIndex trajectory)) /\
      (∀ᵐ trajectory ∂source.trajectoryMeasure,
        ∀ᶠ scheduleIndex in atTop,
          cappedBehavior scheduleIndex trajectory =
              uncappedBehavior scheduleIndex trajectory /\
            cappedReturn scheduleIndex trajectory =
              uncappedReturn scheduleIndex trajectory) /\
      Tendsto
        (fun scheduleIndex =>
          eLpNorm (cappedBehavior scheduleIndex) 1 source.trajectoryMeasure)
        atTop (nhds 0) /\
      Tendsto
        (fun scheduleIndex =>
          integral source.trajectoryMeasure (cappedBehavior scheduleIndex))
        atTop (nhds 0) /\
      Tendsto
        (fun scheduleIndex =>
          eLpNorm (cappedReturn scheduleIndex) 1 source.trajectoryMeasure)
        atTop (nhds 0) /\
      Tendsto
        (fun scheduleIndex =>
          integral source.trajectoryMeasure (cappedReturn scheduleIndex))
        atTop (nhds 0) /\
      Tendsto
        (fun scheduleIndex => eLpNorm
          (uncappedBehavior scheduleIndex - cappedBehavior scheduleIndex) 1
            source.trajectoryMeasure)
        atTop (nhds 0) /\
      Tendsto
        (fun scheduleIndex => integral source.trajectoryMeasure
          (uncappedBehavior scheduleIndex - cappedBehavior scheduleIndex))
        atTop (nhds 0) /\
      Tendsto
        (fun scheduleIndex => eLpNorm
          (uncappedReturn scheduleIndex - cappedReturn scheduleIndex) 1
            source.trajectoryMeasure)
        atTop (nhds 0) /\
      Tendsto
        (fun scheduleIndex => integral source.trajectoryMeasure
          (uncappedReturn scheduleIndex - cappedReturn scheduleIndex))
        atTop (nhds 0) := by
  dsimp only
  let source := selfConsistentScheduledCausalSource mdp initialState
    rewardSource initialTable defaultState varianceProxy baseVisitFloor
  let cappedStoppingPrefix :=
    selfConsistentScheduledNaturalCausalInverseSqrtThresholdCappedDoubleLinearRawWindowFirstPassageStoppingPrefix
      mdp initialState rewardSource initialTable defaultState varianceProxy
        baseVisitFloor
  let uncappedStoppingPrefix :=
    selfConsistentScheduledNaturalCausalInverseSqrtThresholdUnboundedHittingAfterStoppingPrefix
      mdp initialState rewardSource initialTable defaultState varianceProxy
        baseVisitFloor
  let cappedBehavior :=
    selfConsistentScheduledNaturalCausalStoppingTimeAverageBehaviorExpectedRegretProcess
      mdp initialState rewardSource initialTable defaultState varianceProxy
        baseVisitFloor cappedStoppingPrefix
  let uncappedBehavior :=
    selfConsistentScheduledNaturalCausalStoppingTimeAverageBehaviorExpectedRegretProcess
      mdp initialState rewardSource initialTable defaultState varianceProxy
        baseVisitFloor uncappedStoppingPrefix
  let cappedRealized :=
    selfConsistentScheduledNaturalCausalStoppingTimeAverageRealizedBehaviorRegretProcess
      mdp initialState rewardSource initialTable defaultState varianceProxy
        baseVisitFloor cappedStoppingPrefix
  let uncappedRealized :=
    selfConsistentScheduledNaturalCausalStoppingTimeAverageRealizedBehaviorRegretProcess
      mdp initialState rewardSource initialTable defaultState varianceProxy
        baseVisitFloor uncappedStoppingPrefix
  let cappedReturn :=
    selfConsistentScheduledNaturalCausalStoppingTimeAverageReturnDeviationProcess
      mdp initialState rewardSource initialTable defaultState varianceProxy
        baseVisitFloor cappedStoppingPrefix
  let uncappedReturn :=
    selfConsistentScheduledNaturalCausalStoppingTimeAverageReturnDeviationProcess
      mdp initialState rewardSource initialTable defaultState varianceProxy
        baseVisitFloor uncappedStoppingPrefix
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro scheduleIndex
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa only [cappedStoppingPrefix, cappedBehavior] using
        (measurable_selfConsistentScheduledNaturalCausalInverseSqrtThresholdCappedStoppedBehaviorExpectedRegret
          mdp initialState rewardSource initialTable defaultState varianceProxy
            baseVisitFloor scheduleIndex)
    · simpa only [source, cappedStoppingPrefix, cappedBehavior] using
        (memLp_one_selfConsistentScheduledNaturalCausalInverseSqrtThresholdCappedStoppedBehaviorExpectedRegret
          mdp initialState rewardSource initialTable defaultState varianceProxy
            baseVisitFloor hrewardBound scheduleIndex)
    · simpa only [source, cappedStoppingPrefix, cappedReturn] using
        (memLp_one_selfConsistentScheduledNaturalCausalInverseSqrtThresholdCappedStoppedReturnDeviation
          mdp initialState rewardSource varianceProxy hvarianceProxy law initialTable
            defaultState support baseVisitFloor hbaseFloor hrewardBound hhorizon
              hbaseVisitFloor scheduleIndex)
    · simpa only [source, cappedStoppingPrefix, uncappedStoppingPrefix,
        cappedBehavior, uncappedBehavior] using
        (memLp_one_selfConsistentScheduledNaturalCausalInverseSqrtThresholdCappedUnboundedHittingAfterStoppedBehaviorExpectedRegretDifference
          mdp initialState rewardSource initialTable defaultState varianceProxy
            baseVisitFloor hrewardBound scheduleIndex)
    · simpa only [source, cappedStoppingPrefix, uncappedStoppingPrefix,
        cappedReturn, uncappedReturn] using
        (memLp_one_selfConsistentScheduledNaturalCausalInverseSqrtThresholdCappedUnboundedHittingAfterStoppedReturnDeviationDifference
          mdp initialState rewardSource varianceProxy hvarianceProxy law initialTable
            defaultState support baseVisitFloor hbaseFloor hrewardBound hhorizon
              hbaseVisitFloor scheduleIndex)
  · intro scheduleIndex trajectory
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · exact
        selfConsistentScheduledNaturalCausalStoppingTimeAverageBehaviorExpectedRegretProcess_nonneg
          mdp initialState rewardSource initialTable defaultState varianceProxy
            baseVisitFloor cappedStoppingPrefix scheduleIndex trajectory
    · exact
        selfConsistentScheduledNaturalCausalStoppingTimeAverageBehaviorExpectedRegretProcess_le_two_mul_horizon
          mdp initialState rewardSource initialTable defaultState varianceProxy
            baseVisitFloor hrewardBound cappedStoppingPrefix scheduleIndex
              trajectory
    · exact
        selfConsistentScheduledNaturalCausalStoppingTimeAverageRealizedBehaviorRegretProcess_eq_behaviorExpected_sub_returnDeviation
          mdp initialState rewardSource initialTable defaultState varianceProxy
            baseVisitFloor cappedStoppingPrefix scheduleIndex trajectory
    · exact
        selfConsistentScheduledNaturalCausalStoppingTimeAverageRealizedBehaviorRegretProcess_eq_behaviorExpected_sub_returnDeviation
          mdp initialState rewardSource initialTable defaultState varianceProxy
            baseVisitFloor uncappedStoppingPrefix scheduleIndex trajectory
    · simpa only [cappedStoppingPrefix, uncappedStoppingPrefix,
        cappedBehavior, uncappedBehavior, cappedRealized, uncappedRealized,
        cappedReturn, uncappedReturn] using
        (selfConsistentScheduledNaturalCausalInverseSqrtThresholdCappedUnboundedHittingAfterStoppedReturnDeviationDifference_eq_behaviorExpectedRegretDifference_sub_realizedBehaviorRegretDifference
          mdp initialState rewardSource initialTable defaultState varianceProxy
            baseVisitFloor scheduleIndex trajectory)
  · simpa only [source, cappedStoppingPrefix, uncappedStoppingPrefix,
      cappedBehavior, uncappedBehavior, cappedReturn, uncappedReturn] using
      (ae_eventually_selfConsistentScheduledNaturalCausalInverseSqrtThresholdCappedUnboundedHittingAfterStoppedBehaviorExpectedRegret_and_returnDeviation_eq
        mdp initialState rewardSource varianceProxy hvarianceProxy law initialTable
          defaultState support baseVisitFloor hbaseFloor hrewardBound
            (lt_trans (by decide : 0 < 4) hhorizon) hbaseVisitFloor)
  · simpa only [source, cappedStoppingPrefix, cappedBehavior] using
      (eLpNorm_one_selfConsistentScheduledNaturalCausalInverseSqrtThresholdCappedStoppedBehaviorExpectedRegret_tendsto_zero
        mdp initialState rewardSource varianceProxy hvarianceProxy law initialTable
          defaultState support baseVisitFloor hbaseFloor hrewardBound
            (lt_trans (by decide : 0 < 4) hhorizon) hbaseVisitFloor)
  · simpa only [source, cappedStoppingPrefix, cappedBehavior] using
      (selfConsistentScheduledNaturalCausalInverseSqrtThresholdCappedStoppedBehaviorExpectedRegretIntegral_tendsto_zero
        mdp initialState rewardSource varianceProxy hvarianceProxy law initialTable
          defaultState support baseVisitFloor hbaseFloor hrewardBound
            (lt_trans (by decide : 0 < 4) hhorizon) hbaseVisitFloor)
  · simpa only [source, cappedStoppingPrefix, cappedReturn] using
      (eLpNorm_one_selfConsistentScheduledNaturalCausalInverseSqrtThresholdCappedStoppedReturnDeviation_tendsto_zero
        mdp initialState rewardSource varianceProxy hvarianceProxy law initialTable
          defaultState support baseVisitFloor hbaseFloor hrewardBound hhorizon
            hbaseVisitFloor)
  · simpa only [source, cappedStoppingPrefix, cappedReturn] using
      (selfConsistentScheduledNaturalCausalInverseSqrtThresholdCappedStoppedReturnDeviationIntegral_tendsto_zero
        mdp initialState rewardSource varianceProxy hvarianceProxy law initialTable
          defaultState support baseVisitFloor hbaseFloor hrewardBound hhorizon
            hbaseVisitFloor)
  · simpa only [source, cappedStoppingPrefix, uncappedStoppingPrefix,
      cappedBehavior, uncappedBehavior] using
      (eLpNorm_one_selfConsistentScheduledNaturalCausalInverseSqrtThresholdCappedUnboundedHittingAfterStoppedBehaviorExpectedRegretDifference_tendsto_zero
        mdp initialState rewardSource varianceProxy hvarianceProxy law initialTable
          defaultState support baseVisitFloor hbaseFloor hrewardBound
            (lt_trans (by decide : 0 < 4) hhorizon) hbaseVisitFloor)
  · simpa only [source, cappedStoppingPrefix, uncappedStoppingPrefix,
      cappedBehavior, uncappedBehavior] using
      (selfConsistentScheduledNaturalCausalInverseSqrtThresholdCappedUnboundedHittingAfterStoppedBehaviorExpectedRegretDifferenceIntegral_tendsto_zero
        mdp initialState rewardSource varianceProxy hvarianceProxy law initialTable
          defaultState support baseVisitFloor hbaseFloor hrewardBound
            (lt_trans (by decide : 0 < 4) hhorizon) hbaseVisitFloor)
  · simpa only [source, cappedStoppingPrefix, uncappedStoppingPrefix,
      cappedReturn, uncappedReturn] using
      (eLpNorm_one_selfConsistentScheduledNaturalCausalInverseSqrtThresholdCappedUnboundedHittingAfterStoppedReturnDeviationDifference_tendsto_zero
        mdp initialState rewardSource varianceProxy hvarianceProxy law initialTable
          defaultState support baseVisitFloor hbaseFloor hrewardBound hhorizon
            hbaseVisitFloor)
  · simpa only [source, cappedStoppingPrefix, uncappedStoppingPrefix,
      cappedReturn, uncappedReturn] using
      (selfConsistentScheduledNaturalCausalInverseSqrtThresholdCappedUnboundedHittingAfterStoppedReturnDeviationDifferenceIntegral_tendsto_zero
        mdp initialState rewardSource varianceProxy hvarianceProxy law initialTable
          defaultState support baseVisitFloor hbaseFloor hrewardBound hhorizon
            hbaseVisitFloor)

end AdaptiveStochasticSampledEmpiricalOptimisticSource

end BanditRLProof.FiniteHorizonRL
