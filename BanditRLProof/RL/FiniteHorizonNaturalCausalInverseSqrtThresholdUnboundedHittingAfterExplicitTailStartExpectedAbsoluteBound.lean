import BanditRLProof.RL.FiniteHorizonNaturalCausalInverseSqrtThresholdUnboundedHittingAfterIntegrableExpectedUpperBound

/-!
# Explicit tail start for the uncapped inverse-sqrt hitting time

This module replaces the convergence-selected tail start in the fixed-index
second-moment route by a concrete ceiling expression. It then transports that
explicit witness into the deterministic stopped-regret absolute-moment budget.

The result remains fixed-index. It does not establish a uniform moment rate,
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

/-- Coefficient of a reciprocal-linear envelope for the exact scheduled
realized-regret rate. -/
noncomputable def
    explicitPolynomialPrefixAverageRealizedBehaviorRegretRateLinearCoefficient
    (mdp : MDP State Action) (varianceProxy : NNReal) : Real :=
  2 * (mdp.horizon : Real) +
    4 * selfConsistentScheduledNaturalCausalLogarithmicRateCoefficient mdp +
    2 *
      (((mdp.globalReturnDeviationPerEpisodeVarianceProxy
          1 varianceProxy : NNReal) : Real) + 1)

omit [DecidableEq State] [DecidableEq Action]
    [MeasurableSingletonClass State] [MeasurableSingletonClass Action]
    [Nonempty State] [Nonempty Action] in
/-- The reciprocal-linear rate coefficient is nonnegative. -/
theorem
    explicitPolynomialPrefixAverageRealizedBehaviorRegretRateLinearCoefficient_nonneg
    (mdp : MDP State Action) (varianceProxy : NNReal) :
    0 <=
      explicitPolynomialPrefixAverageRealizedBehaviorRegretRateLinearCoefficient
        mdp varianceProxy := by
  unfold
    explicitPolynomialPrefixAverageRealizedBehaviorRegretRateLinearCoefficient
  exact add_nonneg
    (add_nonneg
      (mul_nonneg (by norm_num) (Nat.cast_nonneg _))
      (mul_nonneg (by norm_num)
        (selfConsistentScheduledNaturalCausalLogarithmicRateCoefficient_nonneg
          mdp)))
    (mul_nonneg (by norm_num) (by positivity))

omit [DecidableEq State] [DecidableEq Action]
    [MeasurableSingletonClass State] [MeasurableSingletonClass Action]
    [Nonempty State] [Nonempty Action] in
/-- The exact scheduled realized-regret rate is controlled by a reciprocal
linear envelope in the fourth-power schedule scale. -/
theorem explicitPolynomialPrefixAverageRealizedBehaviorRegretRate_le_linearEnvelope
    (mdp : MDP State Action) (varianceProxy : NNReal)
    (baseVisitFloor : Real) (n : Nat) :
    explicitPolynomialPrefixAverageRealizedBehaviorRegretRate
        mdp varianceProxy baseVisitFloor n <=
      explicitPolynomialPrefixAverageRealizedBehaviorRegretRateLinearCoefficient
          mdp varianceProxy /
        (explicitHighProbabilityScale n : Real) := by
  let s : Real := explicitHighProbabilityScale n
  let H : Real := mdp.horizon
  let C : Real :=
    selfConsistentScheduledNaturalCausalLogarithmicRateCoefficient mdp
  let V : Real :=
    ((mdp.globalReturnDeviationPerEpisodeVarianceProxy
      1 varianceProxy : NNReal) : Real)
  have hs : 0 < s := by
    dsimp [s]
    exact_mod_cast explicitHighProbabilityScale_pos n
  have hsOne : 1 <= s := by
    dsimp [s]
    exact_mod_cast explicitHighProbabilityScale_pos n
  have hH : 0 <= H := by
    dsimp [H]
    positivity
  have hC : 0 <= C := by
    exact selfConsistentScheduledNaturalCausalLogarithmicRateCoefficient_nonneg
      mdp
  have hA : 0 <= 2 * H + 4 * C := by positivity
  have hsSq : 1 <= s ^ 2 := by
    have hplus : 0 <= s + 1 := by linarith
    nlinarith [mul_nonneg (sub_nonneg.mpr hsOne) hplus]
  have hsCube : s <= s ^ 3 := by
    calc
      s = s * 1 := by ring
      _ <= s * s ^ 2 := mul_le_mul_of_nonneg_left hsSq hs.le
      _ = s ^ 3 := by ring
  have hInv : 1 / s ^ 3 <= 1 / s := by
    apply (div_le_div_iff₀ (pow_pos hs 3) hs).2
    simpa using hsCube
  have hCubic : (2 * H + 4 * C) / s ^ 3 <=
      (2 * H + 4 * C) / s := by
    calc
      (2 * H + 4 * C) / s ^ 3 =
          (2 * H + 4 * C) * (1 / s ^ 3) := by ring
      _ <= (2 * H + 4 * C) * (1 / s) :=
        mul_le_mul_of_nonneg_left hInv hA
      _ = (2 * H + 4 * C) / s := by ring
  have hlog :=
    selfConsistentScheduledNaturalCausalLogarithmicAverageIntegratedBehaviorExpectedRegretRate_explicitRounds_le_summableEnvelope
      mdp n
  have hreturn :=
    explicitPolynomialPrefixAverageReturnRadius_le
      mdp varianceProxy baseVisitFloor n
  have hlog' :
      selfConsistentScheduledNaturalCausalLogarithmicAverageIntegratedBehaviorExpectedRegretRate
          mdp (explicitHighProbabilityRounds n) <=
        4 * C / s ^ 3 := by
    simpa [explicitPolynomialPrefixAverageBehaviorRegretL1SummableEnvelope,
      C, s] using hlog
  have hreturn' :
      explicitPolynomialPrefixAverageReturnRadius
          mdp varianceProxy baseVisitFloor n <=
        2 * (V + 1) / s := by
    simpa [V, s] using hreturn
  have hdecomp :
      explicitPolynomialPrefixAverageRealizedBehaviorRegretRate
          mdp varianceProxy baseVisitFloor n =
        2 * H / s ^ 3 +
          selfConsistentScheduledNaturalCausalLogarithmicAverageIntegratedBehaviorExpectedRegretRate
            mdp (explicitHighProbabilityRounds n) +
          explicitPolynomialPrefixAverageReturnRadius
            mdp varianceProxy baseVisitFloor n := by
    unfold explicitPolynomialPrefixAverageRealizedBehaviorRegretRate
      selfConsistentScheduledNaturalCausalBurninRealizedAverageLogarithmicRate
      selfConsistentScheduledNaturalCausalBurninRealizedCumulativeLogarithmicRate
      selfConsistentScheduledNaturalCausalBurninCumulativeBehaviorExpectedRegretLogarithmicRate
      selfConsistentScheduledNaturalCausalLogarithmicAverageIntegratedBehaviorExpectedRegretRate
      explicitPolynomialPrefixAverageReturnRadius
    simp [explicitHighProbabilityBurnin, explicitHighProbabilityRounds,
      s, H]
    field_simp [ne_of_gt hs]
  rw [hdecomp]
  calc
    2 * H / s ^ 3 +
          selfConsistentScheduledNaturalCausalLogarithmicAverageIntegratedBehaviorExpectedRegretRate
            mdp (explicitHighProbabilityRounds n) +
          explicitPolynomialPrefixAverageReturnRadius
            mdp varianceProxy baseVisitFloor n <=
        2 * H / s ^ 3 + 4 * C / s ^ 3 + 2 * (V + 1) / s := by
      exact add_le_add (add_le_add le_rfl hlog') hreturn'
    _ <= (2 * H + 4 * C) / s + 2 * (V + 1) / s := by
      calc
        2 * H / s ^ 3 + 4 * C / s ^ 3 + 2 * (V + 1) / s =
            (2 * H + 4 * C) / s ^ 3 + 2 * (V + 1) / s := by ring
        _ <= (2 * H + 4 * C) / s + 2 * (V + 1) / s :=
          by simpa [add_comm] using
            (add_le_add_right hCubic (2 * (V + 1) / s))
    _ =
        explicitPolynomialPrefixAverageRealizedBehaviorRegretRateLinearCoefficient
            mdp varianceProxy /
          (explicitHighProbabilityScale n : Real) := by
      unfold
        explicitPolynomialPrefixAverageRealizedBehaviorRegretRateLinearCoefficient
      dsimp [H, C, V, s]
      ring

/-- Explicit checkpoint index that clears the fixed inverse-square-root
threshold for every later scheduled regret-rate checkpoint. -/
noncomputable def inverseSqrtThresholdUnboundedHittingAfterExplicitTailStart
    (mdp : MDP State Action) (varianceProxy : NNReal)
    (scheduleIndex : Nat) : Nat :=
  max scheduleIndex
    (Nat.ceil
      (explicitPolynomialPrefixAverageRealizedBehaviorRegretRateLinearCoefficient
          mdp varianceProxy *
        Real.sqrt (explicitHighProbabilityScale scheduleIndex : Real)))

omit [DecidableEq State] [DecidableEq Action]
    [MeasurableSingletonClass State] [MeasurableSingletonClass Action]
    [Nonempty State] [Nonempty Action] in
/-- The explicit ceiling witness is beyond the threshold index and validates
the exact scheduled rate comparison at every later checkpoint. -/
theorem inverseSqrtThresholdUnboundedHittingAfterExplicitTailStart_spec
    (mdp : MDP State Action) (varianceProxy : NNReal)
    (baseVisitFloor : Real) (scheduleIndex : Nat) :
    scheduleIndex <=
        inverseSqrtThresholdUnboundedHittingAfterExplicitTailStart
          mdp varianceProxy scheduleIndex /\
      forall n,
        inverseSqrtThresholdUnboundedHittingAfterExplicitTailStart
              mdp varianceProxy scheduleIndex <= n ->
          explicitPolynomialPrefixAverageRealizedBehaviorRegretRate
              mdp varianceProxy baseVisitFloor n <=
            selfConsistentScheduledNaturalCausalInverseSqrtFirstPassageThreshold
              scheduleIndex := by
  let coefficient :=
    explicitPolynomialPrefixAverageRealizedBehaviorRegretRateLinearCoefficient
      mdp varianceProxy
  let thresholdScale : Real :=
    explicitHighProbabilityScale scheduleIndex
  let ceiling := Nat.ceil (coefficient * Real.sqrt thresholdScale)
  have hthresholdScale : 0 < thresholdScale := by
    dsimp [thresholdScale]
    exact_mod_cast explicitHighProbabilityScale_pos scheduleIndex
  have hsqrt : 0 < Real.sqrt thresholdScale :=
    Real.sqrt_pos.2 hthresholdScale
  have hceil : coefficient * Real.sqrt thresholdScale <=
      (ceiling : Real) := by
    exact Nat.le_ceil _
  constructor
  · exact le_max_left _ _
  · intro n hn
    have hceilingLe : ceiling <= n := by
      exact (le_max_right scheduleIndex ceiling).trans hn
    have hcoefficientSqrtLe :
        coefficient * Real.sqrt thresholdScale <=
          (explicitHighProbabilityScale n : Real) := by
      calc
        coefficient * Real.sqrt thresholdScale <= (ceiling : Real) := hceil
        _ <= (n : Real) := by exact_mod_cast hceilingLe
        _ <= (explicitHighProbabilityScale n : Real) := by
          simp [explicitHighProbabilityScale]
    have hscale : 0 < (explicitHighProbabilityScale n : Real) := by
      exact_mod_cast explicitHighProbabilityScale_pos n
    have henvelope : coefficient /
          (explicitHighProbabilityScale n : Real) <=
        1 / Real.sqrt thresholdScale := by
      apply (div_le_div_iff₀ hscale hsqrt).2
      simpa using hcoefficientSqrtLe
    exact
      (explicitPolynomialPrefixAverageRealizedBehaviorRegretRate_le_linearEnvelope
        mdp varianceProxy baseVisitFloor n).trans
        (by
          simpa [coefficient, thresholdScale,
            selfConsistentScheduledNaturalCausalInverseSqrtFirstPassageThreshold]
            using henvelope)

/-- The accepted least eventual witness is no larger than the explicit
ceiling-based tail start. -/
theorem inverseSqrtThresholdUnboundedHittingAfterTailStart_le_explicitTailStart
    (mdp : MDP State Action) (varianceProxy : NNReal)
    (baseVisitFloor : Real) (scheduleIndex : Nat) :
    inverseSqrtThresholdUnboundedHittingAfterTailStart
        mdp varianceProxy baseVisitFloor scheduleIndex <=
      inverseSqrtThresholdUnboundedHittingAfterExplicitTailStart
        mdp varianceProxy scheduleIndex := by
  classical
  unfold inverseSqrtThresholdUnboundedHittingAfterTailStart
  exact Nat.find_min'
    (exists_inverseSqrtThresholdUnboundedHittingAfterTailStart
      mdp varianceProxy baseVisitFloor scheduleIndex)
    (inverseSqrtThresholdUnboundedHittingAfterExplicitTailStart_spec
      mdp varianceProxy baseVisitFloor scheduleIndex)

/-- ENNReal second-moment budget obtained by replacing the canonical tail
start with its explicit ceiling-based upper bound. -/
noncomputable def
    inverseSqrtThresholdUnboundedHittingAfterExplicitStoppingRoundSecondMomentENNRealBudget
    (mdp : MDP State Action) (varianceProxy : NNReal)
    (scheduleIndex : Nat) : ENNReal :=
  let start := inverseSqrtThresholdUnboundedHittingAfterExplicitTailStart
    mdp varianceProxy scheduleIndex
  (((explicitHighProbabilityRounds start + 1) ^ 2 : Nat) : ENNReal) +
    ∑' n : Nat,
      (explicitHighProbabilityQuarticSquareBlockWeight n : ENNReal) *
        explicitPolynomialPrefixTailModelReturnFailureBudget mdp n

omit [DecidableEq State] [DecidableEq Action]
    [MeasurableSingletonClass State] [MeasurableSingletonClass Action]
    [Nonempty State] [Nonempty Action] in
/-- The explicit-start ENNReal budget is finite under the same horizon-five
contract as the accepted canonical budget. -/
theorem
    inverseSqrtThresholdUnboundedHittingAfterExplicitStoppingRoundSecondMomentENNRealBudget_ne_top
    (mdp : MDP State Action) (varianceProxy : NNReal)
    (scheduleIndex : Nat) (hhorizon : 4 < mdp.horizon) :
    inverseSqrtThresholdUnboundedHittingAfterExplicitStoppingRoundSecondMomentENNRealBudget
        mdp varianceProxy scheduleIndex ≠ ∞ := by
  unfold
    inverseSqrtThresholdUnboundedHittingAfterExplicitStoppingRoundSecondMomentENNRealBudget
  rw [ENNReal.add_ne_top]
  exact ⟨by simp,
    tsum_quarticSquareBlockWeight_mul_explicitPolynomialPrefixTailModelReturnFailureBudget_ne_top
      mdp hhorizon⟩

/-- Real-valued form of the explicit-start stopping-round second-moment
budget. -/
noncomputable def
    inverseSqrtThresholdUnboundedHittingAfterExplicitStoppingRoundSecondMomentBudget
    (mdp : MDP State Action) (varianceProxy : NNReal)
    (scheduleIndex : Nat) : Real :=
  (inverseSqrtThresholdUnboundedHittingAfterExplicitStoppingRoundSecondMomentENNRealBudget
    mdp varianceProxy scheduleIndex).toReal

omit [DecidableEq State] [DecidableEq Action]
    [MeasurableSingletonClass State] [MeasurableSingletonClass Action]
    [Nonempty State] [Nonempty Action] in
/-- The checkpoint-square plus fixed weighted failure series is monotone in
its deterministic checkpoint start. -/
theorem explicitStoppingRoundSecondMomentENNRealBudgetAt_mono
    (mdp : MDP State Action) {left right : Nat} (h : left <= right) :
    (((explicitHighProbabilityRounds left + 1) ^ 2 : Nat) : ENNReal) +
        ∑' n : Nat,
          (explicitHighProbabilityQuarticSquareBlockWeight n : ENNReal) *
            explicitPolynomialPrefixTailModelReturnFailureBudget mdp n <=
      (((explicitHighProbabilityRounds right + 1) ^ 2 : Nat) : ENNReal) +
        ∑' n : Nat,
          (explicitHighProbabilityQuarticSquareBlockWeight n : ENNReal) *
            explicitPolynomialPrefixTailModelReturnFailureBudget mdp n := by
  apply add_le_add
  · exact_mod_cast Nat.pow_le_pow_left
      (Nat.succ_le_succ (explicitHighProbabilityRounds_mono h)) 2
  · exact le_rfl

/-- Replacing the least eventual witness by the explicit tail start can only
increase the deterministic ENNReal second-moment budget. -/
theorem
    inverseSqrtThresholdUnboundedHittingAfterStoppingRoundSecondMomentENNRealBudget_le_explicit
    (mdp : MDP State Action) (varianceProxy : NNReal)
    (baseVisitFloor : Real) (scheduleIndex : Nat) :
    inverseSqrtThresholdUnboundedHittingAfterStoppingRoundSecondMomentENNRealBudget
        mdp varianceProxy baseVisitFloor scheduleIndex <=
      inverseSqrtThresholdUnboundedHittingAfterExplicitStoppingRoundSecondMomentENNRealBudget
        mdp varianceProxy scheduleIndex := by
  simpa only
      [inverseSqrtThresholdUnboundedHittingAfterStoppingRoundSecondMomentENNRealBudget,
        inverseSqrtThresholdUnboundedHittingAfterExplicitStoppingRoundSecondMomentENNRealBudget] using
    (explicitStoppingRoundSecondMomentENNRealBudgetAt_mono mdp
      (inverseSqrtThresholdUnboundedHittingAfterTailStart_le_explicitTailStart
        mdp varianceProxy baseVisitFloor scheduleIndex))

/-- Real-valued canonical second-moment budget is bounded by the explicit
tail-start budget. -/
theorem
    inverseSqrtThresholdUnboundedHittingAfterStoppingRoundSecondMomentBudget_le_explicit
    (mdp : MDP State Action) (varianceProxy : NNReal)
    (baseVisitFloor : Real) (scheduleIndex : Nat)
    (hhorizon : 4 < mdp.horizon) :
    inverseSqrtThresholdUnboundedHittingAfterStoppingRoundSecondMomentBudget
        mdp varianceProxy baseVisitFloor scheduleIndex <=
      inverseSqrtThresholdUnboundedHittingAfterExplicitStoppingRoundSecondMomentBudget
        mdp varianceProxy scheduleIndex := by
  unfold
    inverseSqrtThresholdUnboundedHittingAfterStoppingRoundSecondMomentBudget
    inverseSqrtThresholdUnboundedHittingAfterExplicitStoppingRoundSecondMomentBudget
  exact ENNReal.toReal_mono
    (inverseSqrtThresholdUnboundedHittingAfterExplicitStoppingRoundSecondMomentENNRealBudget_ne_top
      mdp varianceProxy scheduleIndex hhorizon)
    (inverseSqrtThresholdUnboundedHittingAfterStoppingRoundSecondMomentENNRealBudget_le_explicit
      mdp varianceProxy baseVisitFloor scheduleIndex)

/-- The actual successor stopping-round second moment is bounded by the
explicit ceiling-based deterministic budget. -/
theorem
    selfConsistentScheduledCausalSource_inverseSqrtThresholdUnboundedHittingAfter_integral_stoppingRound_sq_le_explicitTailStartBudget
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
      inverseSqrtThresholdUnboundedHittingAfterExplicitStoppingRoundSecondMomentBudget
        mdp varianceProxy scheduleIndex := by
  dsimp only
  exact
    (selfConsistentScheduledCausalSource_inverseSqrtThresholdUnboundedHittingAfter_integral_stoppingRound_sq_le_budget
      mdp initialState rewardSource varianceProxy hvarianceProxy law initialTable
        defaultState support baseVisitFloor hbaseFloor hrewardBound hhorizon
          hbaseVisitFloor scheduleIndex).trans
      (inverseSqrtThresholdUnboundedHittingAfterStoppingRoundSecondMomentBudget_le_explicit
        mdp varianceProxy baseVisitFloor scheduleIndex hhorizon)

/-- Explicit-tail-start absolute-first-moment budget. Its public parameters
contain no canonical `Nat.find` witness and no unevaluated random integral. -/
noncomputable def
    selfConsistentScheduledNaturalCausalInverseSqrtThresholdUnboundedHittingAfterExplicitTailStartDeterministicStoppingRoundSecondMomentAbsoluteFirstMomentBudget
    (mdp : MDP State Action) (varianceProxy : NNReal)
    (scheduleIndex : Nat) : Real :=
  Real.sqrt
      (selfConsistentScheduledNaturalCausalAverageRealizedBehaviorRegretUniformSecondMomentEnvelope
        mdp varianceProxy) *
    ((1 / 2 : Real) *
      (inverseSqrtThresholdUnboundedHittingAfterExplicitStoppingRoundSecondMomentBudget
          mdp varianceProxy scheduleIndex +
        ∑' rounds : Nat,
          1 / (((rounds + 1 : Nat) : Real) ^ 2)))

/-- For each fixed threshold index, the exact stopped average realized
behavior regret is integrable and its absolute first moment is controlled by
the explicit ceiling-based deterministic second-moment budget. -/
theorem
    selfConsistentScheduledCausalSource_inverseSqrtThresholdUnboundedHittingAfter_stoppedAverageRealizedBehaviorRegret_integrable_and_integral_abs_le_explicitTailStartDeterministicStoppingRoundSecondMomentBudget
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
        selfConsistentScheduledNaturalCausalInverseSqrtThresholdUnboundedHittingAfterExplicitTailStartDeterministicStoppingRoundSecondMomentAbsoluteFirstMomentBudget
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
    selfConsistentScheduledCausalSource_inverseSqrtThresholdUnboundedHittingAfter_stoppedAverageRealizedBehaviorRegret_integrable_and_integral_abs_le_deterministicStoppingRoundSecondMomentBudget
      mdp initialState rewardSource varianceProxy hvarianceProxy law initialTable
        defaultState support baseVisitFloor hbaseFloor hrewardBound hhorizon
          hbaseVisitFloor scheduleIndex
  have hmoment :=
    inverseSqrtThresholdUnboundedHittingAfterStoppingRoundSecondMomentBudget_le_explicit
      mdp varianceProxy baseVisitFloor scheduleIndex hhorizon
  have hbudget :
      selfConsistentScheduledNaturalCausalInverseSqrtThresholdUnboundedHittingAfterDeterministicStoppingRoundSecondMomentAbsoluteFirstMomentBudget
          mdp varianceProxy baseVisitFloor scheduleIndex <=
        selfConsistentScheduledNaturalCausalInverseSqrtThresholdUnboundedHittingAfterExplicitTailStartDeterministicStoppingRoundSecondMomentAbsoluteFirstMomentBudget
          mdp varianceProxy scheduleIndex := by
    unfold
      selfConsistentScheduledNaturalCausalInverseSqrtThresholdUnboundedHittingAfterDeterministicStoppingRoundSecondMomentAbsoluteFirstMomentBudget
      selfConsistentScheduledNaturalCausalInverseSqrtThresholdUnboundedHittingAfterExplicitTailStartDeterministicStoppingRoundSecondMomentAbsoluteFirstMomentBudget
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
