import BanditRLProof.RL.FiniteHorizonNaturalCausalInverseSqrtThresholdUnboundedHittingAfterPolynomialSecondMomentExpectedAbsoluteAsymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Cauchy--Schwarz degree-four expected-absolute asymptotics

This module replaces the Young-inequality absolute-first-moment envelope by a
Cauchy--Schwarz estimate on the stopping fibers. The actual stopping-round
second moment still uses the accepted degree-eight polynomial envelope, while
its square root yields a degree-four expected-absolute growth bound.

All model and source parameters are fixed as the threshold index varies. The
result is not optional stopping, uniform integrability, L1 convergence, or a
claim that the polynomial exponent is sharp.
-/

open Filter MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal ProbabilityTheory Topology

namespace BanditRLProof.FiniteHorizonRL

universe u v

variable {State : Type u} {Action : Type v}
    [MeasurableSpace State] [MeasurableSpace Action]
    [Fintype State] [Fintype Action]
    [DecidableEq State] [DecidableEq Action]
    [MeasurableSingletonClass State] [MeasurableSingletonClass Action]
    [Nonempty State] [Nonempty Action]

namespace AdaptiveStochasticSampledEmpiricalOptimisticSource

/-- Real degree-four comparison scale for the threshold schedule. -/
noncomputable def
    inverseSqrtThresholdUnboundedHittingAfterDegreeFourScale
    (scheduleIndex : Nat) : Real :=
  (explicitHighProbabilityScale scheduleIndex : Real) ^ 4

omit [DecidableEq State] [DecidableEq Action]
    [MeasurableSingletonClass State] [MeasurableSingletonClass Action]
    [Nonempty State] [Nonempty Action] in
theorem inverseSqrtThresholdUnboundedHittingAfterDegreeFourScale_nonneg
    (scheduleIndex : Nat) :
    0 <= inverseSqrtThresholdUnboundedHittingAfterDegreeFourScale
      scheduleIndex := by
  unfold inverseSqrtThresholdUnboundedHittingAfterDegreeFourScale
  positivity

omit [DecidableEq State] [DecidableEq Action]
    [MeasurableSingletonClass State] [MeasurableSingletonClass Action]
    [Nonempty State] [Nonempty Action] in
/-- The square root of the degree-eight scale is exactly the degree-four
scale, with no asymptotic slack. -/
theorem sqrt_inverseSqrtThresholdUnboundedHittingAfterDegreeEightScale
    (scheduleIndex : Nat) :
    Real.sqrt
        (inverseSqrtThresholdUnboundedHittingAfterDegreeEightScale
          scheduleIndex) =
      inverseSqrtThresholdUnboundedHittingAfterDegreeFourScale
        scheduleIndex := by
  unfold inverseSqrtThresholdUnboundedHittingAfterDegreeEightScale
    inverseSqrtThresholdUnboundedHittingAfterDegreeFourScale
  rw [show
    (explicitHighProbabilityScale scheduleIndex : Real) ^ 8 =
      ((explicitHighProbabilityScale scheduleIndex : Real) ^ 4) ^ 2 by ring]
  exact Real.sqrt_sq (by positivity)

omit [DecidableEq State] [DecidableEq Action]
    [MeasurableSingletonClass State] [MeasurableSingletonClass Action]
    [Nonempty State] [Nonempty Action] in
/-- Taking square roots of the accepted degree-eight polynomial moment budget
yields a degree-four asymptotic envelope. -/
theorem
    sqrt_inverseSqrtThresholdUnboundedHittingAfterPolynomialStoppingRoundSecondMomentBudget_isBigO_degreeFour
    (mdp : MDP State Action) (varianceProxy : NNReal) :
    (fun scheduleIndex : Nat =>
      Real.sqrt
        (inverseSqrtThresholdUnboundedHittingAfterPolynomialStoppingRoundSecondMomentBudget
          mdp varianceProxy scheduleIndex)) =O[atTop]
      inverseSqrtThresholdUnboundedHittingAfterDegreeFourScale := by
  have hbound :=
    (inverseSqrtThresholdUnboundedHittingAfterPolynomialStoppingRoundSecondMomentBudget_isBigO_degreeEight
      mdp varianceProxy).sqrt
      (Filter.Eventually.of_forall
        inverseSqrtThresholdUnboundedHittingAfterDegreeEightScale_nonneg)
  simpa only
    [sqrt_inverseSqrtThresholdUnboundedHittingAfterDegreeEightScale] using
      hbound

/-- Cauchy--Schwarz polynomial absolute-first-moment budget. Its only varying
factor is the square root of the accepted stopping-round second-moment budget. -/
noncomputable def
    selfConsistentScheduledNaturalCausalInverseSqrtThresholdUnboundedHittingAfterCauchySchwarzPolynomialAbsoluteFirstMomentBudget
    (mdp : MDP State Action) (varianceProxy : NNReal)
    (scheduleIndex : Nat) : Real :=
  (Real.sqrt
      (selfConsistentScheduledNaturalCausalAverageRealizedBehaviorRegretUniformSecondMomentEnvelope
        mdp varianceProxy) *
    Real.sqrt
      inverseSqrtThresholdUnboundedHittingAfterShiftedInverseSquareSeriesConstant) *
    Real.sqrt
      (inverseSqrtThresholdUnboundedHittingAfterPolynomialStoppingRoundSecondMomentBudget
        mdp varianceProxy scheduleIndex)

omit [DecidableEq State] [DecidableEq Action]
    [MeasurableSingletonClass State] [MeasurableSingletonClass Action]
    [Nonempty State] [Nonempty Action] in
theorem
    selfConsistentScheduledNaturalCausalInverseSqrtThresholdUnboundedHittingAfterCauchySchwarzPolynomialAbsoluteFirstMomentBudget_nonneg
    (mdp : MDP State Action) (varianceProxy : NNReal)
    (scheduleIndex : Nat) :
    0 <=
      selfConsistentScheduledNaturalCausalInverseSqrtThresholdUnboundedHittingAfterCauchySchwarzPolynomialAbsoluteFirstMomentBudget
        mdp varianceProxy scheduleIndex := by
  unfold
    selfConsistentScheduledNaturalCausalInverseSqrtThresholdUnboundedHittingAfterCauchySchwarzPolynomialAbsoluteFirstMomentBudget
  positivity

omit [DecidableEq State] [DecidableEq Action]
    [MeasurableSingletonClass State] [MeasurableSingletonClass Action]
    [Nonempty State] [Nonempty Action] in
theorem
    selfConsistentScheduledNaturalCausalInverseSqrtThresholdUnboundedHittingAfterCauchySchwarzPolynomialAbsoluteFirstMomentBudget_isBigO_degreeFour
    (mdp : MDP State Action) (varianceProxy : NNReal) :
    (fun scheduleIndex : Nat =>
      selfConsistentScheduledNaturalCausalInverseSqrtThresholdUnboundedHittingAfterCauchySchwarzPolynomialAbsoluteFirstMomentBudget
        mdp varianceProxy scheduleIndex) =O[atTop]
      inverseSqrtThresholdUnboundedHittingAfterDegreeFourScale := by
  have hbound :=
    sqrt_inverseSqrtThresholdUnboundedHittingAfterPolynomialStoppingRoundSecondMomentBudget_isBigO_degreeFour
      mdp varianceProxy
  have hconstant := hbound.const_mul_left
    (Real.sqrt
        (selfConsistentScheduledNaturalCausalAverageRealizedBehaviorRegretUniformSecondMomentEnvelope
          mdp varianceProxy) *
      Real.sqrt
        inverseSqrtThresholdUnboundedHittingAfterShiftedInverseSquareSeriesConstant)
  simpa only
    [selfConsistentScheduledNaturalCausalInverseSqrtThresholdUnboundedHittingAfterCauchySchwarzPolynomialAbsoluteFirstMomentBudget] using
      hconstant

/-- For each fixed threshold index, Cauchy--Schwarz controls the actual
stopped average realized behavior regret by the square root of the accepted
polynomial stopping-round second-moment budget. -/
theorem
    selfConsistentScheduledCausalSource_inverseSqrtThresholdUnboundedHittingAfter_stoppedAverageRealizedBehaviorRegret_integrable_and_integral_abs_le_cauchySchwarzPolynomialBudget
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
    let stoppedProcess :=
      selfConsistentScheduledNaturalCausalStoppingTimeAverageRealizedBehaviorRegretProcess
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor stoppingPrefix scheduleIndex
    Integrable stoppedProcess source.trajectoryMeasure /\
      integral source.trajectoryMeasure
          (fun trajectory => |stoppedProcess trajectory|) <=
        selfConsistentScheduledNaturalCausalInverseSqrtThresholdUnboundedHittingAfterCauchySchwarzPolynomialAbsoluteFirstMomentBudget
          mdp varianceProxy scheduleIndex := by
  dsimp only
  let source := selfConsistentScheduledCausalSource mdp initialState
    rewardSource initialTable defaultState varianceProxy baseVisitFloor
  let stoppingPrefix :=
    selfConsistentScheduledNaturalCausalInverseSqrtThresholdUnboundedHittingAfterStoppingPrefix
      mdp initialState rewardSource initialTable defaultState varianceProxy
        baseVisitFloor
  let process :=
    selfConsistentScheduledNaturalCausalAverageRealizedBehaviorRegretProcess
      mdp initialState rewardSource initialTable defaultState varianceProxy
        baseVisitFloor
  let stoppedProcess :=
    selfConsistentScheduledNaturalCausalStoppingTimeAverageRealizedBehaviorRegretProcess
      mdp initialState rewardSource initialTable defaultState varianceProxy
        baseVisitFloor stoppingPrefix scheduleIndex
  have hstopping : IsStoppingTime
      (selfConsistentScheduledNaturalCausalTrajectoryFiltration mdp initialState
        rewardSource initialTable defaultState varianceProxy baseVisitFloor)
      (stoppingPrefix scheduleIndex) := by
    simpa only [stoppingPrefix] using
      selfConsistentScheduledNaturalCausalInverseSqrtThresholdUnboundedHittingAfterStoppingPrefix_isStoppingTime
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor scheduleIndex
  have hstop : BanditRLProof.OFUL.SquareIntegrableFiniteStoppingTime
      source.trajectoryMeasure (stoppingPrefix scheduleIndex) := by
    simpa only [source, stoppingPrefix] using
      selfConsistentScheduledCausalSource_inverseSqrtThresholdUnboundedHittingAfter_squareIntegrableFiniteStoppingTime
        mdp initialState rewardSource varianceProxy hvarianceProxy law initialTable
          defaultState support baseVisitFloor hbaseFloor hrewardBound hhorizon
            hbaseVisitFloor scheduleIndex
  have hparent :=
    selfConsistentScheduledCausalSource_inverseSqrtThresholdUnboundedHittingAfter_stoppedAverageRealizedBehaviorRegret_integrable_and_integral_abs_le_polynomialStoppingRoundSecondMomentBudget
      mdp initialState rewardSource varianceProxy hvarianceProxy law initialTable
        defaultState support baseVisitFloor hbaseFloor hrewardBound hhorizon
          hbaseVisitFloor scheduleIndex
  have hstoppedIntegrable :
      Integrable stoppedProcess source.trajectoryMeasure := by
    simpa only [stoppedProcess, source, stoppingPrefix] using hparent.1
  have habsolute :=
    BanditRLProof.integral_abs_stoppedValue_le_uniformSecondMoment_mul_sqrt_integral_rounds_sq_mul_sqrt_tsum_inverse_natSuccSquare_of_memLp_two_rounds
      source.trajectoryMeasure (stoppingPrefix scheduleIndex)
        hstopping.measurable' hstop.finite_ae hstop.memLp_rounds process
          (selfConsistentScheduledNaturalCausalAverageRealizedBehaviorRegretUniformSecondMomentEnvelope
            mdp varianceProxy)
          (fun rounds => by
            simpa only [process, source] using
              memLp_two_selfConsistentScheduledNaturalCausalAverageRealizedBehaviorRegretProcess
                mdp initialState rewardSource varianceProxy law initialTable
                  defaultState baseVisitFloor hrewardBound rounds)
          (fun rounds => by
            simpa only [process, source] using
              integral_sq_selfConsistentScheduledNaturalCausalAverageRealizedBehaviorRegretProcess_le_uniformSecondMomentEnvelope
                mdp initialState rewardSource varianceProxy law initialTable
                  defaultState baseVisitFloor hrewardBound rounds)
  have hmoment :=
    selfConsistentScheduledCausalSource_inverseSqrtThresholdUnboundedHittingAfter_integral_stoppingRound_sq_le_polynomialBudget
      mdp initialState rewardSource varianceProxy hvarianceProxy law initialTable
        defaultState support baseVisitFloor hbaseFloor hrewardBound hhorizon
          hbaseVisitFloor scheduleIndex
  have hsqrtMoment := Real.sqrt_le_sqrt hmoment
  refine ⟨hstoppedIntegrable, ?_⟩
  have hbound := habsolute.trans (mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_right hsqrtMoment (Real.sqrt_nonneg _))
    (Real.sqrt_nonneg _))
  simp only [process,
    selfConsistentScheduledNaturalCausalStoppingTimeAverageRealizedBehaviorRegretProcess,
    selfConsistentScheduledNaturalCausalInverseSqrtThresholdUnboundedHittingAfterCauchySchwarzPolynomialAbsoluteFirstMomentBudget,
    inverseSqrtThresholdUnboundedHittingAfterShiftedInverseSquareSeriesConstant,
    source, stoppingPrefix] at hbound ⊢
  convert hbound using 1
  ring

theorem
    selfConsistentScheduledCausalSource_inverseSqrtThresholdUnboundedHittingAfter_stoppedAverageRealizedBehaviorRegretExpectedAbsolute_le_cauchySchwarzPolynomialBudget
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
    selfConsistentScheduledNaturalCausalInverseSqrtThresholdUnboundedHittingAfterStoppedAverageRealizedBehaviorRegretExpectedAbsolute
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor scheduleIndex <=
      selfConsistentScheduledNaturalCausalInverseSqrtThresholdUnboundedHittingAfterCauchySchwarzPolynomialAbsoluteFirstMomentBudget
        mdp varianceProxy scheduleIndex := by
  simpa only
    [selfConsistentScheduledNaturalCausalInverseSqrtThresholdUnboundedHittingAfterStoppedAverageRealizedBehaviorRegretExpectedAbsolute] using
    (selfConsistentScheduledCausalSource_inverseSqrtThresholdUnboundedHittingAfter_stoppedAverageRealizedBehaviorRegret_integrable_and_integral_abs_le_cauchySchwarzPolynomialBudget
      mdp initialState rewardSource varianceProxy hvarianceProxy law initialTable
        defaultState support baseVisitFloor hbaseFloor hrewardBound hhorizon
          hbaseVisitFloor scheduleIndex).2

/-- With all model/source parameters fixed, the actual expected absolute
stopped regret grows at most at the Cauchy--Schwarz degree-four rate. -/
theorem
    selfConsistentScheduledCausalSource_inverseSqrtThresholdUnboundedHittingAfter_stoppedAverageRealizedBehaviorRegretExpectedAbsolute_isBigO_degreeFour
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
    (selfConsistentScheduledNaturalCausalInverseSqrtThresholdUnboundedHittingAfterStoppedAverageRealizedBehaviorRegretExpectedAbsolute
      mdp initialState rewardSource initialTable defaultState varianceProxy
        baseVisitFloor) =O[atTop]
      inverseSqrtThresholdUnboundedHittingAfterDegreeFourScale := by
  have hbound :=
    selfConsistentScheduledNaturalCausalInverseSqrtThresholdUnboundedHittingAfterCauchySchwarzPolynomialAbsoluteFirstMomentBudget_isBigO_degreeFour
      mdp varianceProxy
  rw [Asymptotics.isBigO_iff] at hbound ⊢
  obtain ⟨c, hc⟩ := hbound
  refine ⟨c, ?_⟩
  filter_upwards [hc] with scheduleIndex hbudget
  have hpoint :=
    selfConsistentScheduledCausalSource_inverseSqrtThresholdUnboundedHittingAfter_stoppedAverageRealizedBehaviorRegretExpectedAbsolute_le_cauchySchwarzPolynomialBudget
      mdp initialState rewardSource varianceProxy hvarianceProxy law initialTable
        defaultState support baseVisitFloor hbaseFloor hrewardBound hhorizon
          hbaseVisitFloor scheduleIndex
  rw [Real.norm_eq_abs,
    abs_of_nonneg
      (selfConsistentScheduledNaturalCausalInverseSqrtThresholdUnboundedHittingAfterStoppedAverageRealizedBehaviorRegretExpectedAbsolute_nonneg
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor scheduleIndex)]
  exact hpoint.trans ((le_abs_self _).trans hbudget)

end AdaptiveStochasticSampledEmpiricalOptimisticSource

end BanditRLProof.FiniteHorizonRL
