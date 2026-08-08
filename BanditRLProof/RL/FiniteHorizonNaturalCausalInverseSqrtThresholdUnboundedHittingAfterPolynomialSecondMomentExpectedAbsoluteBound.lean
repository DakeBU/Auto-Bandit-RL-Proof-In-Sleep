import BanditRLProof.RL.FiniteHorizonNaturalCausalInverseSqrtThresholdUnboundedHittingAfterExplicitTailStartExpectedAbsoluteBound

/-!
# Polynomial moment envelope for the uncapped inverse-sqrt hitting time

This module bounds the explicit ceiling tail start by a model-dependent
natural coefficient times the schedule scale. The resulting fourth-power
checkpoint square is an explicit degree-eight polynomial in the fixed
threshold index.

The result remains fixed-index. It does not establish uniform integrability,
L1 convergence, or an optional-stopping identity.
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

/-- Natural model coefficient used by the polynomial tail-start envelope. -/
noncomputable def
    inverseSqrtThresholdUnboundedHittingAfterPolynomialScaleCoefficient
    (mdp : MDP State Action) (varianceProxy : NNReal) : Nat :=
  Nat.ceil
      (explicitPolynomialPrefixAverageRealizedBehaviorRegretRateLinearCoefficient
        mdp varianceProxy) +
    2

omit [DecidableEq State] [DecidableEq Action]
    [MeasurableSingletonClass State] [MeasurableSingletonClass Action]
    [Nonempty State] [Nonempty Action] in
/-- The explicit ceiling start grows at most linearly in the schedule scale. -/
theorem
    inverseSqrtThresholdUnboundedHittingAfterExplicitTailStart_succ_le_polynomialScale
    (mdp : MDP State Action) (varianceProxy : NNReal)
    (scheduleIndex : Nat) :
    inverseSqrtThresholdUnboundedHittingAfterExplicitTailStart
          mdp varianceProxy scheduleIndex + 1 <=
      inverseSqrtThresholdUnboundedHittingAfterPolynomialScaleCoefficient
          mdp varianceProxy *
        explicitHighProbabilityScale scheduleIndex := by
  let C : Real :=
    explicitPolynomialPrefixAverageRealizedBehaviorRegretRateLinearCoefficient
      mdp varianceProxy
  let c : Nat := Nat.ceil C
  let s : Nat := explicitHighProbabilityScale scheduleIndex
  have hspos : 0 < s := by
    simpa [s] using explicitHighProbabilityScale_pos scheduleIndex
  have hsOneReal : (1 : Real) <= (s : Real) := by
    exact_mod_cast hspos
  have hsqrtLe : Real.sqrt (s : Real) <= (s : Real) := by
    rw [Real.sqrt_le_iff]
    exact ⟨by positivity, by nlinarith⟩
  have hCceil : C <= (c : Real) := by
    dsimp [c]
    exact Nat.le_ceil C
  have hproduct :
      C * Real.sqrt (s : Real) <= ((c * s : Nat) : Real) := by
    calc
      C * Real.sqrt (s : Real) <=
          (c : Real) * Real.sqrt (s : Real) :=
        mul_le_mul_of_nonneg_right hCceil (Real.sqrt_nonneg _)
      _ <= (c : Real) * (s : Real) :=
        mul_le_mul_of_nonneg_left hsqrtLe (Nat.cast_nonneg c)
      _ = ((c * s : Nat) : Real) := by norm_num
  have hceil : Nat.ceil (C * Real.sqrt (s : Real)) <= c * s := by
    exact Nat.ceil_le.2 hproduct
  have hindex : scheduleIndex <= s := by
    simp [s, explicitHighProbabilityScale]
  have hsMul : s <= (c + 1) * s :=
    Nat.le_mul_of_pos_left s (Nat.succ_pos c)
  have hstart :
      max scheduleIndex (Nat.ceil (C * Real.sqrt (s : Real))) <=
        (c + 1) * s := by
    apply max_le
    · exact hindex.trans hsMul
    · exact hceil.trans (Nat.mul_le_mul_right s (Nat.le_succ c))
  have hfinal :
      max scheduleIndex (Nat.ceil (C * Real.sqrt (s : Real))) + 1 <=
        (c + 2) * s := by
    calc
      max scheduleIndex (Nat.ceil (C * Real.sqrt (s : Real))) + 1 <=
          (c + 1) * s + 1 := Nat.add_le_add_right hstart 1
      _ <= (c + 1) * s + s :=
        Nat.add_le_add_left (Nat.one_le_iff_ne_zero.2 hspos.ne') _
      _ = (c + 2) * s := by ring
  simpa
      [inverseSqrtThresholdUnboundedHittingAfterExplicitTailStart,
        inverseSqrtThresholdUnboundedHittingAfterPolynomialScaleCoefficient,
        C, c, s] using hfinal

/-- Explicit degree-eight natural checkpoint-square envelope. -/
noncomputable def
    inverseSqrtThresholdUnboundedHittingAfterPolynomialCheckpointSquare
    (mdp : MDP State Action) (varianceProxy : NNReal)
    (scheduleIndex : Nat) : Nat :=
  ((inverseSqrtThresholdUnboundedHittingAfterPolynomialScaleCoefficient
          mdp varianceProxy *
        explicitHighProbabilityScale scheduleIndex) ^ 4 + 1) ^ 2

omit [DecidableEq State] [DecidableEq Action]
    [MeasurableSingletonClass State] [MeasurableSingletonClass Action]
    [Nonempty State] [Nonempty Action] in
/-- The exact explicit-start checkpoint square is bounded by the polynomial
envelope. -/
theorem
    inverseSqrtThresholdUnboundedHittingAfterExplicitCheckpointSquare_le_polynomial
    (mdp : MDP State Action) (varianceProxy : NNReal)
    (scheduleIndex : Nat) :
    (explicitHighProbabilityRounds
          (inverseSqrtThresholdUnboundedHittingAfterExplicitTailStart
            mdp varianceProxy scheduleIndex) + 1) ^ 2 <=
      inverseSqrtThresholdUnboundedHittingAfterPolynomialCheckpointSquare
        mdp varianceProxy scheduleIndex := by
  unfold
    inverseSqrtThresholdUnboundedHittingAfterPolynomialCheckpointSquare
    explicitHighProbabilityRounds
  apply Nat.pow_le_pow_left
  apply Nat.add_le_add_right
  apply Nat.pow_le_pow_left
  simpa [explicitHighProbabilityScale] using
    (inverseSqrtThresholdUnboundedHittingAfterExplicitTailStart_succ_le_polynomialScale
      mdp varianceProxy scheduleIndex)

/-- The weighted model/return failure contribution to the stopping-round
second moment. It depends only on the MDP. -/
noncomputable def
    inverseSqrtThresholdUnboundedHittingAfterWeightedFailureSecondMomentENNRealConstant
    (mdp : MDP State Action) : ENNReal :=
  ∑' n : Nat,
    (explicitHighProbabilityQuarticSquareBlockWeight n : ENNReal) *
      explicitPolynomialPrefixTailModelReturnFailureBudget mdp n

omit [DecidableEq State] [DecidableEq Action]
    [MeasurableSingletonClass State] [MeasurableSingletonClass Action]
    [Nonempty State] [Nonempty Action] in
/-- The weighted failure constant is finite under the horizon-five contract. -/
theorem
    inverseSqrtThresholdUnboundedHittingAfterWeightedFailureSecondMomentENNRealConstant_ne_top
    (mdp : MDP State Action) (hhorizon : 4 < mdp.horizon) :
    inverseSqrtThresholdUnboundedHittingAfterWeightedFailureSecondMomentENNRealConstant
        mdp ≠ ∞ := by
  simpa only
      [inverseSqrtThresholdUnboundedHittingAfterWeightedFailureSecondMomentENNRealConstant] using
    (tsum_quarticSquareBlockWeight_mul_explicitPolynomialPrefixTailModelReturnFailureBudget_ne_top
      mdp hhorizon)

/-- Real-valued form of the weighted model/return failure constant. -/
noncomputable def
    inverseSqrtThresholdUnboundedHittingAfterWeightedFailureSecondMomentConstant
    (mdp : MDP State Action) : Real :=
  (inverseSqrtThresholdUnboundedHittingAfterWeightedFailureSecondMomentENNRealConstant
    mdp).toReal

/-- ENNReal polynomial stopping-round second-moment budget. -/
noncomputable def
    inverseSqrtThresholdUnboundedHittingAfterPolynomialStoppingRoundSecondMomentENNRealBudget
    (mdp : MDP State Action) (varianceProxy : NNReal)
    (scheduleIndex : Nat) : ENNReal :=
  (inverseSqrtThresholdUnboundedHittingAfterPolynomialCheckpointSquare
      mdp varianceProxy scheduleIndex : ENNReal) +
    inverseSqrtThresholdUnboundedHittingAfterWeightedFailureSecondMomentENNRealConstant
      mdp

omit [DecidableEq State] [DecidableEq Action]
    [MeasurableSingletonClass State] [MeasurableSingletonClass Action]
    [Nonempty State] [Nonempty Action] in
/-- The polynomial ENNReal budget is finite under the same horizon contract. -/
theorem
    inverseSqrtThresholdUnboundedHittingAfterPolynomialStoppingRoundSecondMomentENNRealBudget_ne_top
    (mdp : MDP State Action) (varianceProxy : NNReal)
    (scheduleIndex : Nat) (hhorizon : 4 < mdp.horizon) :
    inverseSqrtThresholdUnboundedHittingAfterPolynomialStoppingRoundSecondMomentENNRealBudget
        mdp varianceProxy scheduleIndex ≠ ∞ := by
  unfold
    inverseSqrtThresholdUnboundedHittingAfterPolynomialStoppingRoundSecondMomentENNRealBudget
  rw [ENNReal.add_ne_top]
  exact ⟨by simp,
    inverseSqrtThresholdUnboundedHittingAfterWeightedFailureSecondMomentENNRealConstant_ne_top
      mdp hhorizon⟩

/-- Real polynomial stopping-round second-moment budget, displayed as a
degree-eight checkpoint term plus the named MDP failure constant. -/
noncomputable def
    inverseSqrtThresholdUnboundedHittingAfterPolynomialStoppingRoundSecondMomentBudget
    (mdp : MDP State Action) (varianceProxy : NNReal)
    (scheduleIndex : Nat) : Real :=
  (inverseSqrtThresholdUnboundedHittingAfterPolynomialCheckpointSquare
      mdp varianceProxy scheduleIndex : Real) +
    inverseSqrtThresholdUnboundedHittingAfterWeightedFailureSecondMomentConstant
      mdp

omit [DecidableEq State] [DecidableEq Action]
    [MeasurableSingletonClass State] [MeasurableSingletonClass Action]
    [Nonempty State] [Nonempty Action] in
/-- Taking `toReal` of the polynomial ENNReal budget gives its displayed real
polynomial-plus-constant form. -/
theorem
    inverseSqrtThresholdUnboundedHittingAfterPolynomialStoppingRoundSecondMomentENNRealBudget_toReal
    (mdp : MDP State Action) (varianceProxy : NNReal)
    (scheduleIndex : Nat) (hhorizon : 4 < mdp.horizon) :
    (inverseSqrtThresholdUnboundedHittingAfterPolynomialStoppingRoundSecondMomentENNRealBudget
        mdp varianceProxy scheduleIndex).toReal =
      inverseSqrtThresholdUnboundedHittingAfterPolynomialStoppingRoundSecondMomentBudget
        mdp varianceProxy scheduleIndex := by
  unfold
    inverseSqrtThresholdUnboundedHittingAfterPolynomialStoppingRoundSecondMomentENNRealBudget
    inverseSqrtThresholdUnboundedHittingAfterPolynomialStoppingRoundSecondMomentBudget
    inverseSqrtThresholdUnboundedHittingAfterWeightedFailureSecondMomentConstant
  rw [ENNReal.toReal_add (by simp)
    (inverseSqrtThresholdUnboundedHittingAfterWeightedFailureSecondMomentENNRealConstant_ne_top
      mdp hhorizon)]
  simp only [ENNReal.toReal_natCast]

omit [DecidableEq State] [DecidableEq Action]
    [MeasurableSingletonClass State] [MeasurableSingletonClass Action]
    [Nonempty State] [Nonempty Action] in
/-- The ceiling-start ENNReal budget is bounded by the polynomial budget. -/
theorem
    inverseSqrtThresholdUnboundedHittingAfterExplicitStoppingRoundSecondMomentENNRealBudget_le_polynomial
    (mdp : MDP State Action) (varianceProxy : NNReal)
    (scheduleIndex : Nat) :
    inverseSqrtThresholdUnboundedHittingAfterExplicitStoppingRoundSecondMomentENNRealBudget
        mdp varianceProxy scheduleIndex <=
      inverseSqrtThresholdUnboundedHittingAfterPolynomialStoppingRoundSecondMomentENNRealBudget
        mdp varianceProxy scheduleIndex := by
  unfold
    inverseSqrtThresholdUnboundedHittingAfterExplicitStoppingRoundSecondMomentENNRealBudget
    inverseSqrtThresholdUnboundedHittingAfterPolynomialStoppingRoundSecondMomentENNRealBudget
    inverseSqrtThresholdUnboundedHittingAfterWeightedFailureSecondMomentENNRealConstant
  apply add_le_add
  · exact_mod_cast
      inverseSqrtThresholdUnboundedHittingAfterExplicitCheckpointSquare_le_polynomial
        mdp varianceProxy scheduleIndex
  · exact le_rfl

omit [DecidableEq State] [DecidableEq Action]
    [MeasurableSingletonClass State] [MeasurableSingletonClass Action]
    [Nonempty State] [Nonempty Action] in
/-- The real ceiling-start second-moment budget is bounded by its displayed
polynomial-plus-constant envelope. -/
theorem
    inverseSqrtThresholdUnboundedHittingAfterExplicitStoppingRoundSecondMomentBudget_le_polynomial
    (mdp : MDP State Action) (varianceProxy : NNReal)
    (scheduleIndex : Nat) (hhorizon : 4 < mdp.horizon) :
    inverseSqrtThresholdUnboundedHittingAfterExplicitStoppingRoundSecondMomentBudget
        mdp varianceProxy scheduleIndex <=
      inverseSqrtThresholdUnboundedHittingAfterPolynomialStoppingRoundSecondMomentBudget
        mdp varianceProxy scheduleIndex := by
  unfold
    inverseSqrtThresholdUnboundedHittingAfterExplicitStoppingRoundSecondMomentBudget
  calc
    (inverseSqrtThresholdUnboundedHittingAfterExplicitStoppingRoundSecondMomentENNRealBudget
        mdp varianceProxy scheduleIndex).toReal <=
        (inverseSqrtThresholdUnboundedHittingAfterPolynomialStoppingRoundSecondMomentENNRealBudget
          mdp varianceProxy scheduleIndex).toReal :=
      ENNReal.toReal_mono
        (inverseSqrtThresholdUnboundedHittingAfterPolynomialStoppingRoundSecondMomentENNRealBudget_ne_top
          mdp varianceProxy scheduleIndex hhorizon)
        (inverseSqrtThresholdUnboundedHittingAfterExplicitStoppingRoundSecondMomentENNRealBudget_le_polynomial
          mdp varianceProxy scheduleIndex)
    _ =
        inverseSqrtThresholdUnboundedHittingAfterPolynomialStoppingRoundSecondMomentBudget
          mdp varianceProxy scheduleIndex :=
      inverseSqrtThresholdUnboundedHittingAfterPolynomialStoppingRoundSecondMomentENNRealBudget_toReal
        mdp varianceProxy scheduleIndex hhorizon

/-- The actual successor stopping-round second moment is bounded by the
polynomial-plus-model-constant budget. -/
theorem
    selfConsistentScheduledCausalSource_inverseSqrtThresholdUnboundedHittingAfter_integral_stoppingRound_sq_le_polynomialBudget
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
    let tau :=
      selfConsistentScheduledNaturalCausalInverseSqrtThresholdUnboundedHittingAfterStoppingPrefix
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor scheduleIndex
    integral source.trajectoryMeasure
        (fun trajectory =>
          ((((tau trajectory).untopA + 1 : Nat) : Real)) ^ 2) <=
      inverseSqrtThresholdUnboundedHittingAfterPolynomialStoppingRoundSecondMomentBudget
        mdp varianceProxy scheduleIndex := by
  dsimp only
  exact
    (selfConsistentScheduledCausalSource_inverseSqrtThresholdUnboundedHittingAfter_integral_stoppingRound_sq_le_explicitTailStartBudget
      mdp initialState rewardSource varianceProxy hvarianceProxy law initialTable
        defaultState support baseVisitFloor hbaseFloor hrewardBound hhorizon
          hbaseVisitFloor scheduleIndex).trans
      (inverseSqrtThresholdUnboundedHittingAfterExplicitStoppingRoundSecondMomentBudget_le_polynomial
        mdp varianceProxy scheduleIndex hhorizon)

/-- Polynomial-envelope absolute-first-moment budget. -/
noncomputable def
    selfConsistentScheduledNaturalCausalInverseSqrtThresholdUnboundedHittingAfterPolynomialStoppingRoundSecondMomentAbsoluteFirstMomentBudget
    (mdp : MDP State Action) (varianceProxy : NNReal)
    (scheduleIndex : Nat) : Real :=
  Real.sqrt
      (selfConsistentScheduledNaturalCausalAverageRealizedBehaviorRegretUniformSecondMomentEnvelope
        mdp varianceProxy) *
    ((1 / 2 : Real) *
      (inverseSqrtThresholdUnboundedHittingAfterPolynomialStoppingRoundSecondMomentBudget
          mdp varianceProxy scheduleIndex +
        ∑' rounds : Nat,
          1 / (((rounds + 1 : Nat) : Real) ^ 2)))

/-- For each fixed threshold index, the stopped average realized behavior
regret has a polynomial-plus-model-constant absolute first-moment bound. -/
theorem
    selfConsistentScheduledCausalSource_inverseSqrtThresholdUnboundedHittingAfter_stoppedAverageRealizedBehaviorRegret_integrable_and_integral_abs_le_polynomialStoppingRoundSecondMomentBudget
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
        selfConsistentScheduledNaturalCausalInverseSqrtThresholdUnboundedHittingAfterPolynomialStoppingRoundSecondMomentAbsoluteFirstMomentBudget
          mdp varianceProxy scheduleIndex := by
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
        baseVisitFloor stoppingPrefix scheduleIndex
  have hparent :=
    selfConsistentScheduledCausalSource_inverseSqrtThresholdUnboundedHittingAfter_stoppedAverageRealizedBehaviorRegret_integrable_and_integral_abs_le_explicitTailStartDeterministicStoppingRoundSecondMomentBudget
      mdp initialState rewardSource varianceProxy hvarianceProxy law initialTable
        defaultState support baseVisitFloor hbaseFloor hrewardBound hhorizon
          hbaseVisitFloor scheduleIndex
  have hmoment :=
    inverseSqrtThresholdUnboundedHittingAfterExplicitStoppingRoundSecondMomentBudget_le_polynomial
      mdp varianceProxy scheduleIndex hhorizon
  have hbudget :
      selfConsistentScheduledNaturalCausalInverseSqrtThresholdUnboundedHittingAfterExplicitTailStartDeterministicStoppingRoundSecondMomentAbsoluteFirstMomentBudget
          mdp varianceProxy scheduleIndex <=
        selfConsistentScheduledNaturalCausalInverseSqrtThresholdUnboundedHittingAfterPolynomialStoppingRoundSecondMomentAbsoluteFirstMomentBudget
          mdp varianceProxy scheduleIndex := by
    unfold
      selfConsistentScheduledNaturalCausalInverseSqrtThresholdUnboundedHittingAfterExplicitTailStartDeterministicStoppingRoundSecondMomentAbsoluteFirstMomentBudget
      selfConsistentScheduledNaturalCausalInverseSqrtThresholdUnboundedHittingAfterPolynomialStoppingRoundSecondMomentAbsoluteFirstMomentBudget
    apply mul_le_mul_of_nonneg_left
    · apply mul_le_mul_of_nonneg_left
      · exact add_le_add hmoment le_rfl
      · norm_num
    · exact Real.sqrt_nonneg _
  refine ⟨?_, ?_⟩
  · simpa only [stoppedProcess, source, stoppingPrefix] using hparent.1
  · simpa only [stoppedProcess, source, stoppingPrefix] using
      hparent.2.trans hbudget

end AdaptiveStochasticSampledEmpiricalOptimisticSource

end BanditRLProof.FiniteHorizonRL
