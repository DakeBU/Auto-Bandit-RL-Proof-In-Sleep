import BanditRLProof.RL.FiniteHorizonNaturalCausalInverseSqrtThresholdUnboundedHittingAfterUniformIntegrabilityExpectedConsistency
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# Uniform absolute continuity at the uncapped inverse-sqrt hitting time

This module consumes the accepted probability-theory uniform-integrability
interface. Uniformly over the exact stopped-process schedule index, sufficiently
small measurable trajectory events have small absolute stopped-regret
integrals. This is an epsilon-delta consequence of uniform integrability, not
an optional-stopping or quantitative tail theorem.
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

/-- Probability-theory uniform integrability at exponent one gives uniform
absolute continuity of the expected norm over measurable events.

This is a thin real-valued wrapper around Mathlib's `UnifIntegrable`
epsilon-delta interface. -/
theorem integral_abs_restrict_le_of_uniformIntegrable_one
    {Omega : Type w} [MeasurableSpace Omega] {mu : Measure Omega}
    {f : Nat -> Omega -> Real}
    (hui : UniformIntegrable f 1 mu) :
    forall epsilon : Real, 0 < epsilon ->
      exists delta : Real, 0 < delta /\
        forall i event, MeasurableSet event ->
          mu event <= ENNReal.ofReal delta ->
            integral (mu.restrict event) (fun omega => |f i omega|) <=
              epsilon := by
  intro epsilon hepsilon
  obtain ⟨delta, hdelta, hsmall⟩ := hui.unifIntegrable hepsilon
  refine ⟨delta, hdelta, ?_⟩
  intro i event hevent hmeasure
  have hmem : MemLp (event.indicator (f i)) 1 mu :=
    (hui.memLp i).indicator hevent
  have hnorm := hsmall i event hevent hmeasure
  have heq :
      eLpNorm (event.indicator (f i)) 1 mu =
        ENNReal.ofReal
          (integral (mu.restrict event) (fun omega => |f i omega|)) := by
    rw [hmem.eLpNorm_eq_integral_rpow_norm one_ne_zero ENNReal.one_ne_top]
    simp only [ENNReal.toReal_one, Real.rpow_one, inv_one]
    simp_rw [norm_indicator_eq_indicator_norm]
    rw [integral_indicator hevent]
    simp only [Real.norm_eq_abs]
  rw [heq] at hnorm
  exact (ENNReal.ofReal_le_ofReal_iff hepsilon.le).1 hnorm

/-- Uniform absolute continuity of the exact uncapped stopped average
realized behavior-regret family. One delta works for every schedule index and
controls both the absolute signed set integral and the set integral of the
absolute stopped regret. -/
theorem
    selfConsistentScheduledCausalSource_inverseSqrtThresholdUnboundedHittingAfter_stoppedAverageRealizedBehaviorRegret_uniformAbsoluteContinuity
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
    forall epsilon : Real, 0 < epsilon ->
      exists delta : Real, 0 < delta /\
        forall scheduleIndex event, MeasurableSet event ->
          source.trajectoryMeasure event <= ENNReal.ofReal delta ->
            |integral (source.trajectoryMeasure.restrict event)
                (stoppedProcess scheduleIndex)| <= epsilon /\
            integral (source.trajectoryMeasure.restrict event)
                (fun trajectory => |stoppedProcess scheduleIndex trajectory|) <=
              epsilon := by
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
  have hui : UniformIntegrable stoppedProcess 1 source.trajectoryMeasure := by
    simpa only [source, stoppingPrefix, stoppedProcess] using
      uniformIntegrable_selfConsistentScheduledNaturalCausalInverseSqrtThresholdUnboundedHittingAfterStoppedAverageRealizedBehaviorRegret
        mdp initialState rewardSource varianceProxy hvarianceProxy law initialTable
          defaultState support baseVisitFloor hbaseFloor hrewardBound hhorizon
            hbaseVisitFloor
  intro epsilon hepsilon
  obtain ⟨delta, hdelta, habsolute⟩ :=
    integral_abs_restrict_le_of_uniformIntegrable_one hui epsilon hepsilon
  refine ⟨delta, hdelta, ?_⟩
  intro scheduleIndex event hevent hmeasure
  have habsolute' := habsolute scheduleIndex event hevent hmeasure
  exact ⟨abs_integral_le_integral_abs.trans habsolute', habsolute'⟩

end AdaptiveStochasticSampledEmpiricalOptimisticSource

end BanditRLProof.FiniteHorizonRL
