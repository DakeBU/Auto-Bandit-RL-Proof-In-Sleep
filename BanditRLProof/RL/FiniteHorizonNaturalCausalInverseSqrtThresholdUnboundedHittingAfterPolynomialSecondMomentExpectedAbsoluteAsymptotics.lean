import BanditRLProof.RL.FiniteHorizonNaturalCausalInverseSqrtThresholdUnboundedHittingAfterPolynomialSecondMomentExpectedAbsoluteBound
import Mathlib.Analysis.Asymptotics.Lemmas

/-!
# Degree-eight asymptotics for the uncapped inverse-sqrt hitting time

This module transports the explicit polynomial moment envelope to the actual
stopping-round second moment and stopped-regret expected absolute value. All
model and source parameters are fixed while the threshold index varies.

The resulting `IsBigO` statements are growth bounds. They do not establish
uniform integrability, L1 convergence, or an optional-stopping identity.
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

/-- Real degree-eight comparison scale for the threshold schedule. -/
noncomputable def
    inverseSqrtThresholdUnboundedHittingAfterDegreeEightScale
    (scheduleIndex : Nat) : Real :=
  (explicitHighProbabilityScale scheduleIndex : Real) ^ 8

omit [DecidableEq State] [DecidableEq Action]
    [MeasurableSingletonClass State] [MeasurableSingletonClass Action]
    [Nonempty State] [Nonempty Action] in
theorem inverseSqrtThresholdUnboundedHittingAfterDegreeEightScale_nonneg
    (scheduleIndex : Nat) :
    0 <= inverseSqrtThresholdUnboundedHittingAfterDegreeEightScale
      scheduleIndex := by
  unfold inverseSqrtThresholdUnboundedHittingAfterDegreeEightScale
  positivity

omit [DecidableEq State] [DecidableEq Action]
    [MeasurableSingletonClass State] [MeasurableSingletonClass Action]
    [Nonempty State] [Nonempty Action] in
theorem inverseSqrtThresholdUnboundedHittingAfterDegreeEightScale_one_le
    (scheduleIndex : Nat) :
    1 <= inverseSqrtThresholdUnboundedHittingAfterDegreeEightScale
      scheduleIndex := by
  have hscale :
      (1 : Real) <= (explicitHighProbabilityScale scheduleIndex : Real) := by
    exact_mod_cast explicitHighProbabilityScale_pos scheduleIndex
  exact one_le_pow₀ hscale

/-- Fixed natural coefficient for the degree-eight checkpoint envelope. -/
noncomputable def
    inverseSqrtThresholdUnboundedHittingAfterPolynomialCheckpointAsymptoticCoefficient
    (mdp : MDP State Action) (varianceProxy : NNReal) : Nat :=
  (inverseSqrtThresholdUnboundedHittingAfterPolynomialScaleCoefficient
      mdp varianceProxy ^ 4 + 1) ^ 2

omit [DecidableEq State] [DecidableEq Action]
    [MeasurableSingletonClass State] [MeasurableSingletonClass Action]
    [Nonempty State] [Nonempty Action] in
/-- The explicit checkpoint polynomial is bounded by one fixed coefficient
times the degree-eight scale. -/
theorem
    inverseSqrtThresholdUnboundedHittingAfterPolynomialCheckpointSquare_le_asymptoticCoefficient_mul_scale_pow_eight
    (mdp : MDP State Action) (varianceProxy : NNReal)
    (scheduleIndex : Nat) :
    inverseSqrtThresholdUnboundedHittingAfterPolynomialCheckpointSquare
        mdp varianceProxy scheduleIndex <=
      inverseSqrtThresholdUnboundedHittingAfterPolynomialCheckpointAsymptoticCoefficient
          mdp varianceProxy *
        explicitHighProbabilityScale scheduleIndex ^ 8 := by
  let c :=
    inverseSqrtThresholdUnboundedHittingAfterPolynomialScaleCoefficient
      mdp varianceProxy
  let s := explicitHighProbabilityScale scheduleIndex
  have hspos : 0 < s := by
    simpa [s] using explicitHighProbabilityScale_pos scheduleIndex
  have hs4 : 1 <= s ^ 4 := Nat.one_le_pow 4 s hspos
  have hinner : (c * s) ^ 4 + 1 <= (c ^ 4 + 1) * s ^ 4 := by
    rw [mul_pow]
    nlinarith
  calc
    inverseSqrtThresholdUnboundedHittingAfterPolynomialCheckpointSquare
        mdp varianceProxy scheduleIndex = ((c * s) ^ 4 + 1) ^ 2 := by
      simp only
        [inverseSqrtThresholdUnboundedHittingAfterPolynomialCheckpointSquare,
          c, s]
    _ <= ((c ^ 4 + 1) * s ^ 4) ^ 2 :=
      Nat.pow_le_pow_left hinner 2
    _ =
        inverseSqrtThresholdUnboundedHittingAfterPolynomialCheckpointAsymptoticCoefficient
            mdp varianceProxy * s ^ 8 := by
      unfold
        inverseSqrtThresholdUnboundedHittingAfterPolynomialCheckpointAsymptoticCoefficient
      dsimp only [c]
      ring

/-- Fixed real coefficient for the polynomial stopping-round second-moment
budget. -/
noncomputable def
    inverseSqrtThresholdUnboundedHittingAfterPolynomialStoppingRoundSecondMomentAsymptoticCoefficient
    (mdp : MDP State Action) (varianceProxy : NNReal) : Real :=
  (inverseSqrtThresholdUnboundedHittingAfterPolynomialCheckpointAsymptoticCoefficient
      mdp varianceProxy : Real) +
    inverseSqrtThresholdUnboundedHittingAfterWeightedFailureSecondMomentConstant
      mdp

omit [DecidableEq State] [DecidableEq Action]
    [MeasurableSingletonClass State] [MeasurableSingletonClass Action]
    [Nonempty State] [Nonempty Action] in
theorem
    inverseSqrtThresholdUnboundedHittingAfterPolynomialStoppingRoundSecondMomentAsymptoticCoefficient_nonneg
    (mdp : MDP State Action) (varianceProxy : NNReal) :
    0 <=
      inverseSqrtThresholdUnboundedHittingAfterPolynomialStoppingRoundSecondMomentAsymptoticCoefficient
        mdp varianceProxy := by
  unfold
    inverseSqrtThresholdUnboundedHittingAfterPolynomialStoppingRoundSecondMomentAsymptoticCoefficient
    inverseSqrtThresholdUnboundedHittingAfterWeightedFailureSecondMomentConstant
  positivity

omit [DecidableEq State] [DecidableEq Action]
    [MeasurableSingletonClass State] [MeasurableSingletonClass Action]
    [Nonempty State] [Nonempty Action] in
/-- Pointwise degree-eight bound for the real deterministic moment budget. -/
theorem
    inverseSqrtThresholdUnboundedHittingAfterPolynomialStoppingRoundSecondMomentBudget_le_asymptoticCoefficient_mul_degreeEightScale
    (mdp : MDP State Action) (varianceProxy : NNReal)
    (scheduleIndex : Nat) :
    inverseSqrtThresholdUnboundedHittingAfterPolynomialStoppingRoundSecondMomentBudget
        mdp varianceProxy scheduleIndex <=
      inverseSqrtThresholdUnboundedHittingAfterPolynomialStoppingRoundSecondMomentAsymptoticCoefficient
          mdp varianceProxy *
        inverseSqrtThresholdUnboundedHittingAfterDegreeEightScale
          scheduleIndex := by
  have hcheckpointNat :=
    inverseSqrtThresholdUnboundedHittingAfterPolynomialCheckpointSquare_le_asymptoticCoefficient_mul_scale_pow_eight
      mdp varianceProxy scheduleIndex
  have hcheckpoint :
      (inverseSqrtThresholdUnboundedHittingAfterPolynomialCheckpointSquare
          mdp varianceProxy scheduleIndex : Real) <=
        (inverseSqrtThresholdUnboundedHittingAfterPolynomialCheckpointAsymptoticCoefficient
            mdp varianceProxy : Real) *
          inverseSqrtThresholdUnboundedHittingAfterDegreeEightScale
            scheduleIndex := by
    unfold inverseSqrtThresholdUnboundedHittingAfterDegreeEightScale
    exact_mod_cast hcheckpointNat
  have hfailure :
      0 <=
        inverseSqrtThresholdUnboundedHittingAfterWeightedFailureSecondMomentConstant
          mdp := by
    unfold
      inverseSqrtThresholdUnboundedHittingAfterWeightedFailureSecondMomentConstant
    exact ENNReal.toReal_nonneg
  have hscale :=
    inverseSqrtThresholdUnboundedHittingAfterDegreeEightScale_one_le
      scheduleIndex
  have hfailureScale :
      inverseSqrtThresholdUnboundedHittingAfterWeightedFailureSecondMomentConstant
          mdp <=
        inverseSqrtThresholdUnboundedHittingAfterWeightedFailureSecondMomentConstant
            mdp *
          inverseSqrtThresholdUnboundedHittingAfterDegreeEightScale
            scheduleIndex := by
    calc
      inverseSqrtThresholdUnboundedHittingAfterWeightedFailureSecondMomentConstant
          mdp =
          inverseSqrtThresholdUnboundedHittingAfterWeightedFailureSecondMomentConstant
              mdp * 1 := by ring
      _ <=
          inverseSqrtThresholdUnboundedHittingAfterWeightedFailureSecondMomentConstant
              mdp *
            inverseSqrtThresholdUnboundedHittingAfterDegreeEightScale
              scheduleIndex :=
        mul_le_mul_of_nonneg_left hscale hfailure
  unfold
    inverseSqrtThresholdUnboundedHittingAfterPolynomialStoppingRoundSecondMomentBudget
    inverseSqrtThresholdUnboundedHittingAfterPolynomialStoppingRoundSecondMomentAsymptoticCoefficient
  calc
    (inverseSqrtThresholdUnboundedHittingAfterPolynomialCheckpointSquare
          mdp varianceProxy scheduleIndex : Real) +
        inverseSqrtThresholdUnboundedHittingAfterWeightedFailureSecondMomentConstant
          mdp <=
        (inverseSqrtThresholdUnboundedHittingAfterPolynomialCheckpointAsymptoticCoefficient
            mdp varianceProxy : Real) *
            inverseSqrtThresholdUnboundedHittingAfterDegreeEightScale
              scheduleIndex +
          inverseSqrtThresholdUnboundedHittingAfterWeightedFailureSecondMomentConstant
            mdp := by
              exact add_le_add hcheckpoint le_rfl
    _ <=
        (inverseSqrtThresholdUnboundedHittingAfterPolynomialCheckpointAsymptoticCoefficient
            mdp varianceProxy : Real) *
            inverseSqrtThresholdUnboundedHittingAfterDegreeEightScale
              scheduleIndex +
          inverseSqrtThresholdUnboundedHittingAfterWeightedFailureSecondMomentConstant
              mdp *
            inverseSqrtThresholdUnboundedHittingAfterDegreeEightScale
              scheduleIndex := add_le_add le_rfl hfailureScale
    _ =
        ((inverseSqrtThresholdUnboundedHittingAfterPolynomialCheckpointAsymptoticCoefficient
              mdp varianceProxy : Real) +
            inverseSqrtThresholdUnboundedHittingAfterWeightedFailureSecondMomentConstant
              mdp) *
          inverseSqrtThresholdUnboundedHittingAfterDegreeEightScale
            scheduleIndex := by ring

omit [DecidableEq State] [DecidableEq Action]
    [MeasurableSingletonClass State] [MeasurableSingletonClass Action]
    [Nonempty State] [Nonempty Action] in
theorem
    inverseSqrtThresholdUnboundedHittingAfterPolynomialStoppingRoundSecondMomentBudget_nonneg
    (mdp : MDP State Action) (varianceProxy : NNReal)
    (scheduleIndex : Nat) :
    0 <=
      inverseSqrtThresholdUnboundedHittingAfterPolynomialStoppingRoundSecondMomentBudget
        mdp varianceProxy scheduleIndex := by
  unfold
    inverseSqrtThresholdUnboundedHittingAfterPolynomialStoppingRoundSecondMomentBudget
    inverseSqrtThresholdUnboundedHittingAfterWeightedFailureSecondMomentConstant
  positivity

omit [DecidableEq State] [DecidableEq Action]
    [MeasurableSingletonClass State] [MeasurableSingletonClass Action]
    [Nonempty State] [Nonempty Action] in
theorem
    inverseSqrtThresholdUnboundedHittingAfterPolynomialStoppingRoundSecondMomentBudget_isBigO_degreeEight
    (mdp : MDP State Action) (varianceProxy : NNReal) :
    (fun scheduleIndex : Nat =>
      inverseSqrtThresholdUnboundedHittingAfterPolynomialStoppingRoundSecondMomentBudget
        mdp varianceProxy scheduleIndex) =O[atTop]
      inverseSqrtThresholdUnboundedHittingAfterDegreeEightScale := by
  rw [Asymptotics.isBigO_iff]
  refine
    ⟨inverseSqrtThresholdUnboundedHittingAfterPolynomialStoppingRoundSecondMomentAsymptoticCoefficient
        mdp varianceProxy, Filter.Eventually.of_forall ?_⟩
  intro scheduleIndex
  rw [Real.norm_eq_abs,
    abs_of_nonneg
      (inverseSqrtThresholdUnboundedHittingAfterPolynomialStoppingRoundSecondMomentBudget_nonneg
        mdp varianceProxy scheduleIndex),
    Real.norm_eq_abs,
    abs_of_nonneg
      (inverseSqrtThresholdUnboundedHittingAfterDegreeEightScale_nonneg
        scheduleIndex)]
  exact
    inverseSqrtThresholdUnboundedHittingAfterPolynomialStoppingRoundSecondMomentBudget_le_asymptoticCoefficient_mul_degreeEightScale
      mdp varianceProxy scheduleIndex

/-- Actual successor stopping-round second moment as a function of the
threshold schedule index. -/
noncomputable def
    selfConsistentScheduledNaturalCausalInverseSqrtThresholdUnboundedHittingAfterStoppingRoundSecondMoment
    (mdp : MDP State Action) (initialState : Measure State)
    [IsProbabilityMeasure initialState]
    (rewardSource : mdp.MeanCompatibleRewardKernel)
    (initialTable : DeterministicMarkovPolicyTable mdp)
    (defaultState : State) (varianceProxy : NNReal)
    (baseVisitFloor : Real) (scheduleIndex : Nat) : Real :=
  let source := selfConsistentScheduledCausalSource mdp initialState
    rewardSource initialTable defaultState varianceProxy baseVisitFloor
  let tau :=
    selfConsistentScheduledNaturalCausalInverseSqrtThresholdUnboundedHittingAfterStoppingPrefix
      mdp initialState rewardSource initialTable defaultState varianceProxy
        baseVisitFloor scheduleIndex
  integral source.trajectoryMeasure
    (fun trajectory => ((((tau trajectory).untopA + 1 : Nat) : Real)) ^ 2)

theorem
    selfConsistentScheduledNaturalCausalInverseSqrtThresholdUnboundedHittingAfterStoppingRoundSecondMoment_nonneg
    (mdp : MDP State Action) (initialState : Measure State)
    [IsProbabilityMeasure initialState]
    (rewardSource : mdp.MeanCompatibleRewardKernel)
    (initialTable : DeterministicMarkovPolicyTable mdp)
    (defaultState : State) (varianceProxy : NNReal)
    (baseVisitFloor : Real) (scheduleIndex : Nat) :
    0 <=
      selfConsistentScheduledNaturalCausalInverseSqrtThresholdUnboundedHittingAfterStoppingRoundSecondMoment
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor scheduleIndex := by
  unfold
    selfConsistentScheduledNaturalCausalInverseSqrtThresholdUnboundedHittingAfterStoppingRoundSecondMoment
  apply integral_nonneg
  intro trajectory
  exact sq_nonneg _

theorem
    selfConsistentScheduledCausalSource_inverseSqrtThresholdUnboundedHittingAfter_stoppingRoundSecondMoment_le_polynomialBudget
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
    selfConsistentScheduledNaturalCausalInverseSqrtThresholdUnboundedHittingAfterStoppingRoundSecondMoment
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor scheduleIndex <=
      inverseSqrtThresholdUnboundedHittingAfterPolynomialStoppingRoundSecondMomentBudget
        mdp varianceProxy scheduleIndex := by
  simpa only
    [selfConsistentScheduledNaturalCausalInverseSqrtThresholdUnboundedHittingAfterStoppingRoundSecondMoment] using
    selfConsistentScheduledCausalSource_inverseSqrtThresholdUnboundedHittingAfter_integral_stoppingRound_sq_le_polynomialBudget
      mdp initialState rewardSource varianceProxy hvarianceProxy law initialTable
        defaultState support baseVisitFloor hbaseFloor hrewardBound hhorizon
          hbaseVisitFloor scheduleIndex

theorem
    selfConsistentScheduledCausalSource_inverseSqrtThresholdUnboundedHittingAfter_integral_stoppingRound_sq_isBigO_degreeEight
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
    (selfConsistentScheduledNaturalCausalInverseSqrtThresholdUnboundedHittingAfterStoppingRoundSecondMoment
      mdp initialState rewardSource initialTable defaultState varianceProxy
        baseVisitFloor) =O[atTop]
      inverseSqrtThresholdUnboundedHittingAfterDegreeEightScale := by
  have hbound :=
    inverseSqrtThresholdUnboundedHittingAfterPolynomialStoppingRoundSecondMomentBudget_isBigO_degreeEight
      mdp varianceProxy
  rw [Asymptotics.isBigO_iff] at hbound ⊢
  obtain ⟨c, hc⟩ := hbound
  refine ⟨c, ?_⟩
  filter_upwards [hc] with scheduleIndex hbudget
  have hpoint :=
    selfConsistentScheduledCausalSource_inverseSqrtThresholdUnboundedHittingAfter_stoppingRoundSecondMoment_le_polynomialBudget
      mdp initialState rewardSource varianceProxy hvarianceProxy law initialTable
        defaultState support baseVisitFloor hbaseFloor hrewardBound hhorizon
          hbaseVisitFloor scheduleIndex
  rw [Real.norm_eq_abs,
    abs_of_nonneg
      (selfConsistentScheduledNaturalCausalInverseSqrtThresholdUnboundedHittingAfterStoppingRoundSecondMoment_nonneg
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor scheduleIndex)]
  exact hpoint.trans ((le_abs_self _).trans hbudget)

/-- Universal shifted inverse-square series appearing in the stopped-value
absolute-first-moment bridge. -/
noncomputable def
    inverseSqrtThresholdUnboundedHittingAfterShiftedInverseSquareSeriesConstant :
    Real :=
  ∑' rounds : Nat, 1 / (((rounds + 1 : Nat) : Real) ^ 2)

omit [DecidableEq State] [DecidableEq Action]
    [MeasurableSingletonClass State] [MeasurableSingletonClass Action]
    [Nonempty State] [Nonempty Action] in
theorem
    inverseSqrtThresholdUnboundedHittingAfterShiftedInverseSquareSeriesConstant_nonneg :
    0 <=
      inverseSqrtThresholdUnboundedHittingAfterShiftedInverseSquareSeriesConstant := by
  unfold inverseSqrtThresholdUnboundedHittingAfterShiftedInverseSquareSeriesConstant
  exact tsum_nonneg (fun _ => by positivity)

/-- Fixed coefficient for the polynomial absolute-first-moment budget. -/
noncomputable def
    selfConsistentScheduledNaturalCausalInverseSqrtThresholdUnboundedHittingAfterPolynomialAbsoluteFirstMomentAsymptoticCoefficient
    (mdp : MDP State Action) (varianceProxy : NNReal) : Real :=
  Real.sqrt
      (selfConsistentScheduledNaturalCausalAverageRealizedBehaviorRegretUniformSecondMomentEnvelope
        mdp varianceProxy) *
    ((1 / 2 : Real) *
      (inverseSqrtThresholdUnboundedHittingAfterPolynomialStoppingRoundSecondMomentAsymptoticCoefficient
          mdp varianceProxy +
        inverseSqrtThresholdUnboundedHittingAfterShiftedInverseSquareSeriesConstant))

omit [DecidableEq State] [DecidableEq Action]
    [MeasurableSingletonClass State] [MeasurableSingletonClass Action]
    [Nonempty State] [Nonempty Action] in
theorem
    selfConsistentScheduledNaturalCausalInverseSqrtThresholdUnboundedHittingAfterPolynomialAbsoluteFirstMomentAsymptoticCoefficient_nonneg
    (mdp : MDP State Action) (varianceProxy : NNReal) :
    0 <=
      selfConsistentScheduledNaturalCausalInverseSqrtThresholdUnboundedHittingAfterPolynomialAbsoluteFirstMomentAsymptoticCoefficient
        mdp varianceProxy := by
  have hmoment :=
    inverseSqrtThresholdUnboundedHittingAfterPolynomialStoppingRoundSecondMomentAsymptoticCoefficient_nonneg
      mdp varianceProxy
  have hseries :=
    inverseSqrtThresholdUnboundedHittingAfterShiftedInverseSquareSeriesConstant_nonneg
  unfold
    selfConsistentScheduledNaturalCausalInverseSqrtThresholdUnboundedHittingAfterPolynomialAbsoluteFirstMomentAsymptoticCoefficient
  positivity

omit [DecidableEq State] [DecidableEq Action]
    [MeasurableSingletonClass State] [MeasurableSingletonClass Action]
    [Nonempty State] [Nonempty Action] in
theorem
    selfConsistentScheduledNaturalCausalInverseSqrtThresholdUnboundedHittingAfterPolynomialStoppingRoundSecondMomentAbsoluteFirstMomentBudget_le_asymptoticCoefficient_mul_degreeEightScale
    (mdp : MDP State Action) (varianceProxy : NNReal)
    (scheduleIndex : Nat) :
    selfConsistentScheduledNaturalCausalInverseSqrtThresholdUnboundedHittingAfterPolynomialStoppingRoundSecondMomentAbsoluteFirstMomentBudget
        mdp varianceProxy scheduleIndex <=
      selfConsistentScheduledNaturalCausalInverseSqrtThresholdUnboundedHittingAfterPolynomialAbsoluteFirstMomentAsymptoticCoefficient
          mdp varianceProxy *
        inverseSqrtThresholdUnboundedHittingAfterDegreeEightScale
          scheduleIndex := by
  have hmoment :=
    inverseSqrtThresholdUnboundedHittingAfterPolynomialStoppingRoundSecondMomentBudget_le_asymptoticCoefficient_mul_degreeEightScale
      mdp varianceProxy scheduleIndex
  have hseries :=
    inverseSqrtThresholdUnboundedHittingAfterShiftedInverseSquareSeriesConstant_nonneg
  have hscale :=
    inverseSqrtThresholdUnboundedHittingAfterDegreeEightScale_one_le
      scheduleIndex
  have hseriesScale :
      inverseSqrtThresholdUnboundedHittingAfterShiftedInverseSquareSeriesConstant <=
        inverseSqrtThresholdUnboundedHittingAfterShiftedInverseSquareSeriesConstant *
          inverseSqrtThresholdUnboundedHittingAfterDegreeEightScale
            scheduleIndex := by
    calc
      inverseSqrtThresholdUnboundedHittingAfterShiftedInverseSquareSeriesConstant =
          inverseSqrtThresholdUnboundedHittingAfterShiftedInverseSquareSeriesConstant * 1 := by
        ring
      _ <=
          inverseSqrtThresholdUnboundedHittingAfterShiftedInverseSquareSeriesConstant *
            inverseSqrtThresholdUnboundedHittingAfterDegreeEightScale
              scheduleIndex := mul_le_mul_of_nonneg_left hscale hseries
  have hinner :
      inverseSqrtThresholdUnboundedHittingAfterPolynomialStoppingRoundSecondMomentBudget
            mdp varianceProxy scheduleIndex +
          inverseSqrtThresholdUnboundedHittingAfterShiftedInverseSquareSeriesConstant <=
        (inverseSqrtThresholdUnboundedHittingAfterPolynomialStoppingRoundSecondMomentAsymptoticCoefficient
              mdp varianceProxy +
            inverseSqrtThresholdUnboundedHittingAfterShiftedInverseSquareSeriesConstant) *
          inverseSqrtThresholdUnboundedHittingAfterDegreeEightScale
            scheduleIndex := by
    calc
      inverseSqrtThresholdUnboundedHittingAfterPolynomialStoppingRoundSecondMomentBudget
              mdp varianceProxy scheduleIndex +
            inverseSqrtThresholdUnboundedHittingAfterShiftedInverseSquareSeriesConstant <=
          inverseSqrtThresholdUnboundedHittingAfterPolynomialStoppingRoundSecondMomentAsymptoticCoefficient
                mdp varianceProxy *
              inverseSqrtThresholdUnboundedHittingAfterDegreeEightScale
                scheduleIndex +
            inverseSqrtThresholdUnboundedHittingAfterShiftedInverseSquareSeriesConstant := by
        exact add_le_add hmoment le_rfl
      _ <=
          inverseSqrtThresholdUnboundedHittingAfterPolynomialStoppingRoundSecondMomentAsymptoticCoefficient
                mdp varianceProxy *
              inverseSqrtThresholdUnboundedHittingAfterDegreeEightScale
                scheduleIndex +
            inverseSqrtThresholdUnboundedHittingAfterShiftedInverseSquareSeriesConstant *
              inverseSqrtThresholdUnboundedHittingAfterDegreeEightScale
                scheduleIndex := add_le_add le_rfl hseriesScale
      _ =
          (inverseSqrtThresholdUnboundedHittingAfterPolynomialStoppingRoundSecondMomentAsymptoticCoefficient
                mdp varianceProxy +
              inverseSqrtThresholdUnboundedHittingAfterShiftedInverseSquareSeriesConstant) *
            inverseSqrtThresholdUnboundedHittingAfterDegreeEightScale
              scheduleIndex := by ring
  unfold
    selfConsistentScheduledNaturalCausalInverseSqrtThresholdUnboundedHittingAfterPolynomialStoppingRoundSecondMomentAbsoluteFirstMomentBudget
    selfConsistentScheduledNaturalCausalInverseSqrtThresholdUnboundedHittingAfterPolynomialAbsoluteFirstMomentAsymptoticCoefficient
    inverseSqrtThresholdUnboundedHittingAfterShiftedInverseSquareSeriesConstant at *
  calc
    Real.sqrt
          (selfConsistentScheduledNaturalCausalAverageRealizedBehaviorRegretUniformSecondMomentEnvelope
            mdp varianceProxy) *
        ((1 / 2 : Real) *
          (inverseSqrtThresholdUnboundedHittingAfterPolynomialStoppingRoundSecondMomentBudget
              mdp varianceProxy scheduleIndex +
            ∑' rounds : Nat, 1 / (((rounds + 1 : Nat) : Real) ^ 2))) <=
      Real.sqrt
          (selfConsistentScheduledNaturalCausalAverageRealizedBehaviorRegretUniformSecondMomentEnvelope
            mdp varianceProxy) *
        ((1 / 2 : Real) *
          ((inverseSqrtThresholdUnboundedHittingAfterPolynomialStoppingRoundSecondMomentAsymptoticCoefficient
                mdp varianceProxy +
              ∑' rounds : Nat,
                1 / (((rounds + 1 : Nat) : Real) ^ 2)) *
            inverseSqrtThresholdUnboundedHittingAfterDegreeEightScale
              scheduleIndex)) := by
        apply mul_le_mul_of_nonneg_left
        · exact mul_le_mul_of_nonneg_left hinner (by norm_num)
        · exact Real.sqrt_nonneg _
    _ =
        (Real.sqrt
            (selfConsistentScheduledNaturalCausalAverageRealizedBehaviorRegretUniformSecondMomentEnvelope
              mdp varianceProxy) *
          ((1 / 2 : Real) *
            (inverseSqrtThresholdUnboundedHittingAfterPolynomialStoppingRoundSecondMomentAsymptoticCoefficient
                mdp varianceProxy +
              ∑' rounds : Nat,
                1 / (((rounds + 1 : Nat) : Real) ^ 2)))) *
          inverseSqrtThresholdUnboundedHittingAfterDegreeEightScale
            scheduleIndex := by ring

omit [DecidableEq State] [DecidableEq Action]
    [MeasurableSingletonClass State] [MeasurableSingletonClass Action]
    [Nonempty State] [Nonempty Action] in
theorem
    selfConsistentScheduledNaturalCausalInverseSqrtThresholdUnboundedHittingAfterPolynomialStoppingRoundSecondMomentAbsoluteFirstMomentBudget_nonneg
    (mdp : MDP State Action) (varianceProxy : NNReal)
    (scheduleIndex : Nat) :
    0 <=
      selfConsistentScheduledNaturalCausalInverseSqrtThresholdUnboundedHittingAfterPolynomialStoppingRoundSecondMomentAbsoluteFirstMomentBudget
        mdp varianceProxy scheduleIndex := by
  have hmoment :=
    inverseSqrtThresholdUnboundedHittingAfterPolynomialStoppingRoundSecondMomentBudget_nonneg
      mdp varianceProxy scheduleIndex
  have hseries :=
    inverseSqrtThresholdUnboundedHittingAfterShiftedInverseSquareSeriesConstant_nonneg
  have hseries' :
      0 <= ∑' rounds : Nat,
        1 / (((rounds + 1 : Nat) : Real) ^ 2) := by
    simpa only
      [inverseSqrtThresholdUnboundedHittingAfterShiftedInverseSquareSeriesConstant] using
      hseries
  unfold
    selfConsistentScheduledNaturalCausalInverseSqrtThresholdUnboundedHittingAfterPolynomialStoppingRoundSecondMomentAbsoluteFirstMomentBudget
  exact
    mul_nonneg (Real.sqrt_nonneg _)
      (mul_nonneg (by norm_num) (add_nonneg hmoment hseries'))

omit [DecidableEq State] [DecidableEq Action]
    [MeasurableSingletonClass State] [MeasurableSingletonClass Action]
    [Nonempty State] [Nonempty Action] in
theorem
    selfConsistentScheduledNaturalCausalInverseSqrtThresholdUnboundedHittingAfterPolynomialStoppingRoundSecondMomentAbsoluteFirstMomentBudget_isBigO_degreeEight
    (mdp : MDP State Action) (varianceProxy : NNReal) :
    (fun scheduleIndex : Nat =>
      selfConsistentScheduledNaturalCausalInverseSqrtThresholdUnboundedHittingAfterPolynomialStoppingRoundSecondMomentAbsoluteFirstMomentBudget
        mdp varianceProxy scheduleIndex) =O[atTop]
      inverseSqrtThresholdUnboundedHittingAfterDegreeEightScale := by
  rw [Asymptotics.isBigO_iff]
  refine
    ⟨selfConsistentScheduledNaturalCausalInverseSqrtThresholdUnboundedHittingAfterPolynomialAbsoluteFirstMomentAsymptoticCoefficient
        mdp varianceProxy, Filter.Eventually.of_forall ?_⟩
  intro scheduleIndex
  rw [Real.norm_eq_abs,
    abs_of_nonneg
      (selfConsistentScheduledNaturalCausalInverseSqrtThresholdUnboundedHittingAfterPolynomialStoppingRoundSecondMomentAbsoluteFirstMomentBudget_nonneg
        mdp varianceProxy scheduleIndex),
    Real.norm_eq_abs,
    abs_of_nonneg
      (inverseSqrtThresholdUnboundedHittingAfterDegreeEightScale_nonneg
        scheduleIndex)]
  exact
    selfConsistentScheduledNaturalCausalInverseSqrtThresholdUnboundedHittingAfterPolynomialStoppingRoundSecondMomentAbsoluteFirstMomentBudget_le_asymptoticCoefficient_mul_degreeEightScale
      mdp varianceProxy scheduleIndex

/-- Expected absolute stopped average realized behavior regret as a function
of the threshold schedule index. -/
noncomputable def
    selfConsistentScheduledNaturalCausalInverseSqrtThresholdUnboundedHittingAfterStoppedAverageRealizedBehaviorRegretExpectedAbsolute
    (mdp : MDP State Action) (initialState : Measure State)
    [IsProbabilityMeasure initialState]
    (rewardSource : mdp.MeanCompatibleRewardKernel)
    (initialTable : DeterministicMarkovPolicyTable mdp)
    (defaultState : State) (varianceProxy : NNReal)
    (baseVisitFloor : Real) (scheduleIndex : Nat) : Real :=
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
  integral source.trajectoryMeasure
    (fun trajectory => |stoppedProcess trajectory|)

theorem
    selfConsistentScheduledNaturalCausalInverseSqrtThresholdUnboundedHittingAfterStoppedAverageRealizedBehaviorRegretExpectedAbsolute_nonneg
    (mdp : MDP State Action) (initialState : Measure State)
    [IsProbabilityMeasure initialState]
    (rewardSource : mdp.MeanCompatibleRewardKernel)
    (initialTable : DeterministicMarkovPolicyTable mdp)
    (defaultState : State) (varianceProxy : NNReal)
    (baseVisitFloor : Real) (scheduleIndex : Nat) :
    0 <=
      selfConsistentScheduledNaturalCausalInverseSqrtThresholdUnboundedHittingAfterStoppedAverageRealizedBehaviorRegretExpectedAbsolute
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor scheduleIndex := by
  unfold
    selfConsistentScheduledNaturalCausalInverseSqrtThresholdUnboundedHittingAfterStoppedAverageRealizedBehaviorRegretExpectedAbsolute
  apply integral_nonneg
  intro trajectory
  exact abs_nonneg _

theorem
    selfConsistentScheduledCausalSource_inverseSqrtThresholdUnboundedHittingAfter_stoppedAverageRealizedBehaviorRegretExpectedAbsolute_le_polynomialBudget
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
      selfConsistentScheduledNaturalCausalInverseSqrtThresholdUnboundedHittingAfterPolynomialStoppingRoundSecondMomentAbsoluteFirstMomentBudget
        mdp varianceProxy scheduleIndex := by
  simpa only
    [selfConsistentScheduledNaturalCausalInverseSqrtThresholdUnboundedHittingAfterStoppedAverageRealizedBehaviorRegretExpectedAbsolute] using
    (selfConsistentScheduledCausalSource_inverseSqrtThresholdUnboundedHittingAfter_stoppedAverageRealizedBehaviorRegret_integrable_and_integral_abs_le_polynomialStoppingRoundSecondMomentBudget
      mdp initialState rewardSource varianceProxy hvarianceProxy law initialTable
        defaultState support baseVisitFloor hbaseFloor hrewardBound hhorizon
          hbaseVisitFloor scheduleIndex).2

/-- With all model/source parameters fixed, the actual expected absolute
stopped regret grows at most at the compiled degree-eight rate. -/
theorem
    selfConsistentScheduledCausalSource_inverseSqrtThresholdUnboundedHittingAfter_stoppedAverageRealizedBehaviorRegretExpectedAbsolute_isBigO_degreeEight
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
      inverseSqrtThresholdUnboundedHittingAfterDegreeEightScale := by
  have hbound :=
    selfConsistentScheduledNaturalCausalInverseSqrtThresholdUnboundedHittingAfterPolynomialStoppingRoundSecondMomentAbsoluteFirstMomentBudget_isBigO_degreeEight
      mdp varianceProxy
  rw [Asymptotics.isBigO_iff] at hbound ⊢
  obtain ⟨c, hc⟩ := hbound
  refine ⟨c, ?_⟩
  filter_upwards [hc] with scheduleIndex hbudget
  have hpoint :=
    selfConsistentScheduledCausalSource_inverseSqrtThresholdUnboundedHittingAfter_stoppedAverageRealizedBehaviorRegretExpectedAbsolute_le_polynomialBudget
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
