import BanditRLProof.RL.FiniteHorizonNaturalCausalInverseSqrtThresholdUnboundedHittingAfterLpConsistency
import Mathlib.MeasureTheory.Function.UniformIntegrable
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Uniform integrability at the uncapped inverse-sqrt hitting time

This module upgrades the accepted exact `hittingAfter` L1/Lp convergence
package to Mathlib probability-theory uniform integrability and signed
expectation convergence. It does not use or prove an optional-stopping
identity.
-/

open Filter MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal ProbabilityTheory Topology

namespace BanditRLProof.FiniteHorizonRL

universe u v w

variable {State : Type u} {Action : Type v}
    [MeasurableSpace State] [MeasurableSpace Action]
    [Fintype State] [Fintype Action]
    [DecidableEq State] [DecidableEq Action]
    [MeasurableSingletonClass State] [MeasurableSingletonClass Action]
    [Nonempty State] [Nonempty Action]

namespace AdaptiveStochasticSampledEmpiricalOptimisticSource

/-- L1 convergence to zero gives probability-theory uniform integrability.

The `UnifIntegrable` component is Mathlib's Lp convergence theorem. The
additional uniform L1 bound is obtained from boundedness of the convergent
sequence in `Lp` and transported back through `MemLp.toLp`. -/
theorem uniformIntegrable_one_of_memLp_and_tendsto_eLpNorm_sub_zero
    {Omega : Type w} [MeasurableSpace Omega] {mu : Measure Omega}
    {f : Nat -> Omega -> Real}
    (hf : forall n, MemLp (f n) 1 mu)
    (hfg : Tendsto
      (fun n => eLpNorm (f n - (fun _ => 0)) 1 mu)
      atTop (nhds 0)) :
    UniformIntegrable f 1 mu := by
  constructor
  case left => exact fun n => (hf n).aestronglyMeasurable
  case right =>
    constructor
    case left =>
      exact unifIntegrable_of_tendsto_Lp le_rfl ENNReal.one_ne_top hf
        MemLp.zero' hfg
    case right =>
      let F : Nat -> Lp Real 1 mu := fun n => (hf n).toLp (f n)
      have hF : Tendsto F atTop (nhds 0) :=
        (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' f hf
          (fun _ => (0 : Real)) MemLp.zero').2 hfg
      have hnn : Tendsto (fun n => nnnorm (F n)) atTop (nhds 0) := by
        simpa only [Function.comp_apply, nnnorm_zero] using
          (continuous_nnnorm.tendsto 0).comp hF
      have hbdd :=
        Metric.isBounded_range_of_tendsto (fun n => nnnorm (F n)) hnn
      let C : NNReal := hbdd.bddAbove.choose
      have hC := hbdd.bddAbove.choose_spec
      refine Exists.intro C ?_
      intro n
      calc
        eLpNorm (f n) 1 mu = enorm ((hf n).toLp (f n)) :=
          (Lp.enorm_toLp (hf n)).symm
        _ = (nnnorm (F n) : ENNReal) := rfl
        _ <= (C : ENNReal) :=
          ENNReal.coe_le_coe.2 (hC (Set.mem_range_self n))

/-- The exact uncapped stopped average realized behavior-regret family is
uniformly integrable in Mathlib's probability-theory sense at exponent one. -/
theorem
    uniformIntegrable_selfConsistentScheduledNaturalCausalInverseSqrtThresholdUnboundedHittingAfterStoppedAverageRealizedBehaviorRegret
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
    let stoppedProcess :=
      selfConsistentScheduledNaturalCausalStoppingTimeAverageRealizedBehaviorRegretProcess
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor stoppingPrefix
    UniformIntegrable stoppedProcess 1 source.trajectoryMeasure := by
  dsimp only
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
  have hmem : forall scheduleIndex,
      MemLp (stoppedProcess scheduleIndex) 1 source.trajectoryMeasure :=
    fun scheduleIndex =>
      memLp_one_selfConsistentScheduledNaturalCausalInverseSqrtThresholdUnboundedHittingAfterStoppedAverageRealizedBehaviorRegret
        mdp initialState rewardSource varianceProxy hvarianceProxy law initialTable
          defaultState support baseVisitFloor hbaseFloor hrewardBound hhorizon
            hbaseVisitFloor scheduleIndex
  have hnorm :=
    eLpNorm_one_selfConsistentScheduledNaturalCausalInverseSqrtThresholdUnboundedHittingAfterStoppedAverageRealizedBehaviorRegret_sub_zero_tendsto_zero
      mdp initialState rewardSource varianceProxy hvarianceProxy law initialTable
        defaultState support baseVisitFloor hbaseFloor hrewardBound hhorizon
          hbaseVisitFloor
  exact uniformIntegrable_one_of_memLp_and_tendsto_eLpNorm_sub_zero hmem
    (by simpa [stoppedProcess, source] using hnorm)

/-- The signed expectation of the exact uncapped stopped process tends to
zero. This is continuity of the Bochner integral under L1 convergence, not an
optional-stopping identity. -/
theorem
    selfConsistentScheduledNaturalCausalInverseSqrtThresholdUnboundedHittingAfterStoppedAverageRealizedBehaviorRegretIntegral_tendsto_zero
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
    let stoppedProcess :=
      selfConsistentScheduledNaturalCausalStoppingTimeAverageRealizedBehaviorRegretProcess
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor stoppingPrefix
    Tendsto
      (fun scheduleIndex =>
        integral source.trajectoryMeasure (stoppedProcess scheduleIndex))
      atTop (nhds 0) := by
  dsimp only
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
  have hmem : forall scheduleIndex,
      MemLp (stoppedProcess scheduleIndex) 1 source.trajectoryMeasure :=
    fun scheduleIndex =>
      memLp_one_selfConsistentScheduledNaturalCausalInverseSqrtThresholdUnboundedHittingAfterStoppedAverageRealizedBehaviorRegret
        mdp initialState rewardSource varianceProxy hvarianceProxy law initialTable
          defaultState support baseVisitFloor hbaseFloor hrewardBound hhorizon
            hbaseVisitFloor scheduleIndex
  have hnorm :=
    eLpNorm_one_selfConsistentScheduledNaturalCausalInverseSqrtThresholdUnboundedHittingAfterStoppedAverageRealizedBehaviorRegret_sub_zero_tendsto_zero
      mdp initialState rewardSource varianceProxy hvarianceProxy law initialTable
        defaultState support baseVisitFloor hbaseFloor hrewardBound hhorizon
          hbaseVisitFloor
  have hintegral := tendsto_integral_of_L1'
    (fun _ : HeterogeneousStochasticEpisodeBatchTrajectory mdp
      (fun t =>
        AdaptiveStochasticEpisodeBatchSource.selfConsistentScheduledEpisodes
          mdp varianceProxy baseVisitFloor t) => (0 : Real))
    (integrable_zero _ Real source.trajectoryMeasure)
    (Eventually.of_forall fun scheduleIndex =>
      (hmem scheduleIndex).integrable le_rfl)
    (by simpa [stoppedProcess, source] using hnorm)
  simpa [stoppedProcess, source] using hintegral

/- Terminal uniform-integrability and signed-expectation package for the
exact uncapped inverse-square-root `hittingAfter` stopped process. -/
theorem
    selfConsistentScheduledCausalSource_inverseSqrtThresholdUnboundedHittingAfter_stoppedAverageRealizedBehaviorRegret_uniformIntegrable_and_integral_tendsto_zero
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
    let stoppedProcess :=
      selfConsistentScheduledNaturalCausalStoppingTimeAverageRealizedBehaviorRegretProcess
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor stoppingPrefix
    UniformIntegrable stoppedProcess 1 source.trajectoryMeasure /\
      Tendsto
        (fun scheduleIndex =>
          integral source.trajectoryMeasure (stoppedProcess scheduleIndex))
        atTop (nhds 0) := by
  dsimp only
  exact And.intro
    (uniformIntegrable_selfConsistentScheduledNaturalCausalInverseSqrtThresholdUnboundedHittingAfterStoppedAverageRealizedBehaviorRegret
      mdp initialState rewardSource varianceProxy hvarianceProxy law initialTable
        defaultState support baseVisitFloor hbaseFloor hrewardBound hhorizon
          hbaseVisitFloor)
    (selfConsistentScheduledNaturalCausalInverseSqrtThresholdUnboundedHittingAfterStoppedAverageRealizedBehaviorRegretIntegral_tendsto_zero
      mdp initialState rewardSource varianceProxy hvarianceProxy law initialTable
        defaultState support baseVisitFloor hbaseFloor hrewardBound hhorizon
          hbaseVisitFloor)

end AdaptiveStochasticSampledEmpiricalOptimisticSource

end BanditRLProof.FiniteHorizonRL
