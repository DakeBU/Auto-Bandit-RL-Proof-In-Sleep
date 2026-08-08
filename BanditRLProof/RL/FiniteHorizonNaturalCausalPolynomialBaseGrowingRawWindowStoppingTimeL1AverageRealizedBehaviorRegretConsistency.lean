import BanditRLProof.ExpectationBochnerSums
import BanditRLProof.RL.FiniteHorizonNaturalCausalAverageRealizedBehaviorRegretAlmostSureExplicitSchedule
import BanditRLProof.RL.FiniteHorizonNaturalCausalBoundedWindowStoppingTimeL1AverageRealizedBehaviorRegretConsistency

/-!
# Polynomial-base growing raw-window stopping-time L1 consistency

This module strengthens the fourth-power grid stopping theorem to a contiguous
window of raw natural prefixes. At schedule index `n`, the stopping prefix may
select any integer in `[(n + 1)^4, (n + 1)^4 + n]`. The all-prefix L1 envelope
is bounded by one inverse square root, so every candidate costs at most
`D / (n + 1)^2`; summing the `n + 1` raw candidates gives `D / (n + 1)`.

The base points remain the explicit fourth-power schedule. This does not cover
arbitrary raw base indices, wider windows, optional stopping, or independence.
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

omit [DecidableEq State] [DecidableEq Action]
    [MeasurableSingletonClass State] [MeasurableSingletonClass Action]
    [Nonempty State] [Nonempty Action] in
/-- A positive real number satisfies `1 + log x <= 2 * sqrt x`. -/
theorem one_add_log_le_two_mul_sqrt {x : Real} (hx : 0 < x) :
    1 + Real.log x <= 2 * Real.sqrt x := by
  have hsqrtPos : 0 < Real.sqrt x := Real.sqrt_pos.2 hx
  have hlog := Real.log_le_sub_one_of_pos hsqrtPos
  rw [Real.log_sqrt hx.le] at hlog
  linarith

omit [DecidableEq State] [DecidableEq Action]
    [MeasurableSingletonClass State] [MeasurableSingletonClass Action]
    [Nonempty State] [Nonempty Action] in
/-- The compiled logarithmic average rate admits an inverse-square-root bound. -/
theorem
    selfConsistentScheduledNaturalCausalLogarithmicAverageIntegratedBehaviorExpectedRegretRate_le_inverseSqrt
    (mdp : MDP State Action) (rounds : Nat) (hrounds : 0 < rounds) :
    selfConsistentScheduledNaturalCausalLogarithmicAverageIntegratedBehaviorExpectedRegretRate
        mdp rounds <=
      2 * selfConsistentScheduledNaturalCausalLogarithmicRateCoefficient mdp /
        Real.sqrt (rounds : Real) := by
  let C := selfConsistentScheduledNaturalCausalLogarithmicRateCoefficient mdp
  let x : Real := rounds
  have hC : 0 <= C :=
    selfConsistentScheduledNaturalCausalLogarithmicRateCoefficient_nonneg mdp
  have hx : 0 < x := by
    dsimp [x]
    exact_mod_cast hrounds
  have hlog : 1 + Real.log x <= 2 * Real.sqrt x :=
    one_add_log_le_two_mul_sqrt hx
  have hnum : C * (1 + Real.log x) <= C * (2 * Real.sqrt x) :=
    mul_le_mul_of_nonneg_left hlog hC
  unfold selfConsistentScheduledNaturalCausalLogarithmicAverageIntegratedBehaviorExpectedRegretRate
    selfConsistentScheduledNaturalCausalLogarithmicCumulativeIntegratedBehaviorExpectedRegretRate
  change C * (1 + Real.log x) / x <= 2 * C / Real.sqrt x
  calc
    C * (1 + Real.log x) / x <= C * (2 * Real.sqrt x) / x :=
      div_le_div_of_nonneg_right hnum hx.le
    _ = 2 * C / Real.sqrt x := by
      have hsqrtPos : 0 < Real.sqrt x := Real.sqrt_pos.2 hx
      field_simp [ne_of_gt hx, ne_of_gt hsqrtPos]
      rw [Real.sq_sqrt hx.le]

/-- Coefficient of the common inverse-square-root all-prefix L1 envelope. -/
noncomputable def selfConsistentScheduledNaturalCausalRawWindowL1Coefficient
    (mdp : MDP State Action) (varianceProxy : NNReal) : Real :=
  2 * selfConsistentScheduledNaturalCausalLogarithmicRateCoefficient mdp +
    2 * Real.sqrt
      (mdp.globalReturnDeviationPerEpisodeVarianceProxy 1 varianceProxy : Real) *
      Real.exp (1 / 2 : Real)

/-- Common inverse-square-root envelope used on every raw candidate prefix. -/
noncomputable def
    selfConsistentScheduledNaturalCausalRawWindowInverseSqrtL1Envelope
    (mdp : MDP State Action) (varianceProxy : NNReal) (rounds : Nat) : Real :=
  selfConsistentScheduledNaturalCausalRawWindowL1Coefficient mdp varianceProxy /
    Real.sqrt (rounds : Real)

omit [DecidableEq State] [DecidableEq Action]
    [MeasurableSingletonClass State] [MeasurableSingletonClass Action]
    [Nonempty State] [Nonempty Action] in
/-- The common raw-window L1 coefficient is nonnegative. -/
theorem selfConsistentScheduledNaturalCausalRawWindowL1Coefficient_nonneg
    (mdp : MDP State Action) (varianceProxy : NNReal) :
    0 <= selfConsistentScheduledNaturalCausalRawWindowL1Coefficient
      mdp varianceProxy := by
  unfold selfConsistentScheduledNaturalCausalRawWindowL1Coefficient
  exact add_nonneg
    (mul_nonneg (by norm_num)
      (selfConsistentScheduledNaturalCausalLogarithmicRateCoefficient_nonneg mdp))
    (by positivity)

omit [DecidableEq State] [DecidableEq Action]
    [MeasurableSingletonClass State] [MeasurableSingletonClass Action]
    [Nonempty State] [Nonempty Action] in
/-- The exact all-prefix L1 envelope is bounded by the common inverse square root. -/
theorem
    selfConsistentScheduledNaturalCausalAverageRealizedBehaviorRegretL1Envelope_le_rawWindowInverseSqrtL1Envelope
    (mdp : MDP State Action) (varianceProxy : NNReal)
    (baseVisitFloor : Real) (rounds : Nat) (hrounds : 0 < rounds) :
    selfConsistentScheduledNaturalCausalAverageRealizedBehaviorRegretL1Envelope
        mdp varianceProxy baseVisitFloor rounds <=
      selfConsistentScheduledNaturalCausalRawWindowInverseSqrtL1Envelope
        mdp varianceProxy rounds := by
  unfold selfConsistentScheduledNaturalCausalAverageRealizedBehaviorRegretL1Envelope
    selfConsistentScheduledNaturalCausalRawWindowInverseSqrtL1Envelope
    selfConsistentScheduledNaturalCausalRawWindowL1Coefficient
  calc
    selfConsistentScheduledNaturalCausalLogarithmicAverageIntegratedBehaviorExpectedRegretRate
          mdp rounds +
        selfConsistentScheduledNaturalCausalAverageReturnFirstMomentBound mdp
          varianceProxy baseVisitFloor rounds <=
      2 * selfConsistentScheduledNaturalCausalLogarithmicRateCoefficient mdp /
          Real.sqrt (rounds : Real) +
        (2 * Real.sqrt
            (mdp.globalReturnDeviationPerEpisodeVarianceProxy 1 varianceProxy : Real) *
            Real.exp (1 / 2 : Real)) /
          Real.sqrt (rounds : Real) :=
      add_le_add
        (selfConsistentScheduledNaturalCausalLogarithmicAverageIntegratedBehaviorExpectedRegretRate_le_inverseSqrt
          mdp rounds hrounds)
        (selfConsistentScheduledNaturalCausalAverageReturnFirstMomentBound_le_inverseSqrtEnvelope
          mdp varianceProxy baseVisitFloor rounds hrounds)
    _ =
      (2 * selfConsistentScheduledNaturalCausalLogarithmicRateCoefficient mdp +
          2 * Real.sqrt
            (mdp.globalReturnDeviationPerEpisodeVarianceProxy 1 varianceProxy : Real) *
            Real.exp (1 / 2 : Real)) /
        Real.sqrt (rounds : Real) := by ring

omit [DecidableEq State] [DecidableEq Action]
    [MeasurableSingletonClass State] [MeasurableSingletonClass Action]
    [Nonempty State] [Nonempty Action] in
/-- A raw prefix after the fourth-power base has square root at least `(n+1)^2`. -/
theorem explicitHighProbabilityScale_sq_le_sqrt_rounds_add
    (scheduleIndex offset : Nat) :
    (explicitHighProbabilityScale scheduleIndex : Real) ^ 2 <=
      Real.sqrt
        (explicitHighProbabilityRounds scheduleIndex + offset : Nat) := by
  let s : Real := explicitHighProbabilityScale scheduleIndex
  have hrounds : (explicitHighProbabilityRounds scheduleIndex : Real) = s ^ 4 := by
    simp [explicitHighProbabilityRounds, s]
  have hcast : (explicitHighProbabilityRounds scheduleIndex : Real) <=
      (explicitHighProbabilityRounds scheduleIndex + offset : Nat) := by
    exact_mod_cast
      Nat.le_add_right (explicitHighProbabilityRounds scheduleIndex) offset
  have hsqrt := Real.sqrt_le_sqrt hcast
  rw [hrounds, show s ^ 4 = (s ^ 2) ^ 2 by ring,
    Real.sqrt_sq (sq_nonneg s)] at hsqrt
  exact hsqrt

omit [DecidableEq State] [DecidableEq Action]
    [MeasurableSingletonClass State] [MeasurableSingletonClass Action]
    [Nonempty State] [Nonempty Action] in
/-- Every candidate in the raw window costs at most one inverse-square term. -/
theorem
    selfConsistentScheduledNaturalCausalRawWindowInverseSqrtL1Envelope_add_le_inverseSquare
    (mdp : MDP State Action) (varianceProxy : NNReal)
    (scheduleIndex offset : Nat) :
    selfConsistentScheduledNaturalCausalRawWindowInverseSqrtL1Envelope
        mdp varianceProxy
          (explicitHighProbabilityRounds scheduleIndex + offset) <=
      selfConsistentScheduledNaturalCausalRawWindowL1Coefficient mdp varianceProxy /
        (explicitHighProbabilityScale scheduleIndex : Real) ^ 2 := by
  unfold selfConsistentScheduledNaturalCausalRawWindowInverseSqrtL1Envelope
  exact div_le_div_of_nonneg_left
    (selfConsistentScheduledNaturalCausalRawWindowL1Coefficient_nonneg
      mdp varianceProxy)
    (pow_pos (by
      exact_mod_cast explicitHighProbabilityScale_pos scheduleIndex) 2)
    (explicitHighProbabilityScale_sq_le_sqrt_rounds_add scheduleIndex offset)

/-- L1 budget over all raw prefixes from `(n+1)^4` through `(n+1)^4+n`. -/
noncomputable def
    selfConsistentScheduledNaturalCausalPolynomialBaseGrowingRawWindowStoppingL1Budget
    (mdp : MDP State Action) (varianceProxy : NNReal)
    (baseVisitFloor : Real) (scheduleIndex : Nat) : Real :=
  (Finset.range (scheduleIndex + 1)).sum fun offset =>
    selfConsistentScheduledNaturalCausalAverageRealizedBehaviorRegretL1Envelope
      mdp varianceProxy baseVisitFloor
        (explicitHighProbabilityRounds scheduleIndex + offset)

omit [DecidableEq State] [DecidableEq Action]
    [MeasurableSingletonClass State] [MeasurableSingletonClass Action]
    [Nonempty State] [Nonempty Action] in
/-- The finite raw-window L1 budget is nonnegative. -/
theorem
    selfConsistentScheduledNaturalCausalPolynomialBaseGrowingRawWindowStoppingL1Budget_nonneg
    (mdp : MDP State Action) (varianceProxy : NNReal)
    (baseVisitFloor : Real) (scheduleIndex : Nat) :
    0 <=
      selfConsistentScheduledNaturalCausalPolynomialBaseGrowingRawWindowStoppingL1Budget
        mdp varianceProxy baseVisitFloor scheduleIndex := by
  exact Finset.sum_nonneg fun offset _ =>
    selfConsistentScheduledNaturalCausalAverageRealizedBehaviorRegretL1Envelope_nonneg
      mdp varianceProxy baseVisitFloor
        (explicitHighProbabilityRounds scheduleIndex + offset)

omit [DecidableEq State] [DecidableEq Action]
    [MeasurableSingletonClass State] [MeasurableSingletonClass Action]
    [Nonempty State] [Nonempty Action] in
/-- The `n+1` raw candidates have total budget at most `D/(n+1)`. -/
theorem
    selfConsistentScheduledNaturalCausalPolynomialBaseGrowingRawWindowStoppingL1Budget_le_rate
    (mdp : MDP State Action) (varianceProxy : NNReal)
    (baseVisitFloor : Real) (scheduleIndex : Nat) :
    selfConsistentScheduledNaturalCausalPolynomialBaseGrowingRawWindowStoppingL1Budget
        mdp varianceProxy baseVisitFloor scheduleIndex <=
      selfConsistentScheduledNaturalCausalRawWindowL1Coefficient mdp varianceProxy /
        (explicitHighProbabilityScale scheduleIndex : Real) := by
  calc
    selfConsistentScheduledNaturalCausalPolynomialBaseGrowingRawWindowStoppingL1Budget
        mdp varianceProxy baseVisitFloor scheduleIndex <=
      (Finset.range (scheduleIndex + 1)).sum (fun _ =>
        selfConsistentScheduledNaturalCausalRawWindowL1Coefficient mdp
            varianceProxy /
          (explicitHighProbabilityScale scheduleIndex : Real) ^ 2) := by
      unfold selfConsistentScheduledNaturalCausalPolynomialBaseGrowingRawWindowStoppingL1Budget
      apply Finset.sum_le_sum
      intro offset _hoffset
      have hrounds :
          0 < explicitHighProbabilityRounds scheduleIndex + offset :=
        Nat.add_pos_left (explicitHighProbabilityRounds_pos scheduleIndex) offset
      exact
        (selfConsistentScheduledNaturalCausalAverageRealizedBehaviorRegretL1Envelope_le_rawWindowInverseSqrtL1Envelope
          mdp varianceProxy baseVisitFloor
            (explicitHighProbabilityRounds scheduleIndex + offset) hrounds).trans
          (selfConsistentScheduledNaturalCausalRawWindowInverseSqrtL1Envelope_add_le_inverseSquare
            mdp varianceProxy scheduleIndex offset)
    _ = selfConsistentScheduledNaturalCausalRawWindowL1Coefficient mdp
          varianceProxy /
        (explicitHighProbabilityScale scheduleIndex : Real) := by
      have hs : (((scheduleIndex + 1 : Nat) : Real)) ≠ 0 := by positivity
      simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      simp only [explicitHighProbabilityScale]
      field_simp [hs]

omit [DecidableEq State] [DecidableEq Action]
    [MeasurableSingletonClass State] [MeasurableSingletonClass Action]
    [Nonempty State] [Nonempty Action] in
/-- The explicit `D/(n+1)` raw-window budget rate tends to zero. -/
theorem selfConsistentScheduledNaturalCausalRawWindowL1Rate_tendsto_zero
    (mdp : MDP State Action) (varianceProxy : NNReal) :
    Tendsto
      (fun scheduleIndex =>
        selfConsistentScheduledNaturalCausalRawWindowL1Coefficient mdp
            varianceProxy /
          (explicitHighProbabilityScale scheduleIndex : Real))
      atTop (nhds 0) := by
  exact tendsto_const_nhds.div_atTop
    explicitHighProbabilityScale_real_tendsto_atTop

omit [DecidableEq State] [DecidableEq Action]
    [MeasurableSingletonClass State] [MeasurableSingletonClass Action]
    [Nonempty State] [Nonempty Action] in
/-- The finite growing raw-window L1 budget tends to zero. -/
theorem
    selfConsistentScheduledNaturalCausalPolynomialBaseGrowingRawWindowStoppingL1Budget_tendsto_zero
    (mdp : MDP State Action) (varianceProxy : NNReal)
    (baseVisitFloor : Real) :
    Tendsto
      (selfConsistentScheduledNaturalCausalPolynomialBaseGrowingRawWindowStoppingL1Budget
        mdp varianceProxy baseVisitFloor) atTop (nhds 0) := by
  apply squeeze_zero'
  · exact Filter.Eventually.of_forall fun scheduleIndex =>
      selfConsistentScheduledNaturalCausalPolynomialBaseGrowingRawWindowStoppingL1Budget_nonneg
        mdp varianceProxy baseVisitFloor scheduleIndex
  · exact Filter.Eventually.of_forall fun scheduleIndex =>
      selfConsistentScheduledNaturalCausalPolynomialBaseGrowingRawWindowStoppingL1Budget_le_rate
        mdp varianceProxy baseVisitFloor scheduleIndex
  · exact selfConsistentScheduledNaturalCausalRawWindowL1Rate_tendsto_zero
      mdp varianceProxy

/-- The WithTop bounds select one raw natural prefix in the growing window. -/
theorem exists_polynomialBaseGrowingRawWindow_offset_untopA_eq
    {Omega : Type*} (stoppingPrefix : Nat -> Omega -> WithTop Nat)
    (hstoppingLower : forall scheduleIndex trajectory,
      (explicitHighProbabilityRounds scheduleIndex : WithTop Nat) <=
        stoppingPrefix scheduleIndex trajectory)
    (hstoppingUpper : forall scheduleIndex trajectory,
      stoppingPrefix scheduleIndex trajectory <=
        (explicitHighProbabilityRounds scheduleIndex + scheduleIndex :
          WithTop Nat))
    (scheduleIndex : Nat) (trajectory : Omega) :
    exists offset, offset ∈ Finset.range (scheduleIndex + 1) /\
      (stoppingPrefix scheduleIndex trajectory).untopA =
        explicitHighProbabilityRounds scheduleIndex + offset := by
  exact exists_window_offset_untopA_eq_of_withTop_bounds
    (stoppingPrefix scheduleIndex)
      (explicitHighProbabilityRounds scheduleIndex) scheduleIndex
        (hstoppingLower scheduleIndex) (hstoppingUpper scheduleIndex) trajectory

/-- Expected absolute value of the polynomial-base raw-window stopped process. -/
noncomputable def
    selfConsistentScheduledNaturalCausalExpectedAbsolutePolynomialBaseGrowingRawWindowStoppingAverageRealizedBehaviorRegret
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
    (scheduleIndex : Nat) : Real :=
  integral
    (selfConsistentScheduledCausalSource mdp initialState rewardSource
      initialTable defaultState varianceProxy baseVisitFloor).trajectoryMeasure
    (fun trajectory =>
      |selfConsistentScheduledNaturalCausalStoppingTimeAverageRealizedBehaviorRegretProcess
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor stoppingPrefix scheduleIndex trajectory|)

/-- Every polynomial-base raw-window stopped coordinate belongs to `L1`. -/
theorem
    memLp_one_selfConsistentScheduledNaturalCausalPolynomialBaseGrowingRawWindowStoppingAverageRealizedBehaviorRegret
    (mdp : MDP State Action) (initialState : Measure State)
    [IsProbabilityMeasure initialState]
    [StandardBorelSpace State] [StandardBorelSpace Action]
    (rewardSource : mdp.MeanCompatibleRewardKernel)
    (varianceProxy : NNReal)
    (law : rewardSource.UniformSubgaussianRewardLaw varianceProxy)
    (initialTable : DeterministicMarkovPolicyTable mdp)
    (defaultState : State) (baseVisitFloor : Real)
    (hrewardBound : forall state action, |mdp.reward state action| <= 1)
    (stoppingPrefix : Nat ->
      HeterogeneousStochasticEpisodeBatchTrajectory mdp
        (fun t =>
          AdaptiveStochasticEpisodeBatchSource.selfConsistentScheduledEpisodes
            mdp varianceProxy baseVisitFloor t) -> WithTop Nat)
    (hstopping : forall scheduleIndex, IsStoppingTime
      (selfConsistentScheduledNaturalCausalTrajectoryFiltration mdp initialState
        rewardSource initialTable defaultState varianceProxy baseVisitFloor)
      (stoppingPrefix scheduleIndex))
    (hstoppingUpper : forall scheduleIndex trajectory,
      stoppingPrefix scheduleIndex trajectory <=
        (explicitHighProbabilityRounds scheduleIndex + scheduleIndex :
          WithTop Nat))
    (scheduleIndex : Nat) :
    MemLp
      (selfConsistentScheduledNaturalCausalStoppingTimeAverageRealizedBehaviorRegretProcess
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor stoppingPrefix scheduleIndex)
      1
      (selfConsistentScheduledCausalSource mdp initialState rewardSource
        initialTable defaultState varianceProxy baseVisitFloor).trajectoryMeasure := by
  exact memLp_stoppedValue (hstopping scheduleIndex)
    (fun rounds =>
      memLp_one_selfConsistentScheduledNaturalCausalAverageRealizedBehaviorRegretProcess
        mdp initialState rewardSource varianceProxy law initialTable defaultState
          baseVisitFloor hrewardBound rounds)
    (hstoppingUpper scheduleIndex)

/-- Expected absolute polynomial-base raw-window stopped regret is nonnegative. -/
theorem
    selfConsistentScheduledNaturalCausalExpectedAbsolutePolynomialBaseGrowingRawWindowStoppingAverageRealizedBehaviorRegret_nonneg
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
    0 <=
      selfConsistentScheduledNaturalCausalExpectedAbsolutePolynomialBaseGrowingRawWindowStoppingAverageRealizedBehaviorRegret
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor stoppingPrefix scheduleIndex := by
  unfold selfConsistentScheduledNaturalCausalExpectedAbsolutePolynomialBaseGrowingRawWindowStoppingAverageRealizedBehaviorRegret
  exact integral_nonneg fun _ => abs_nonneg _

/-- The selected raw coordinate is bounded by the finite candidate L1 budget. -/
theorem
    selfConsistentScheduledNaturalCausalExpectedAbsolutePolynomialBaseGrowingRawWindowStoppingAverageRealizedBehaviorRegret_le_budget
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
    (stoppingPrefix : Nat ->
      HeterogeneousStochasticEpisodeBatchTrajectory mdp
        (fun t =>
          AdaptiveStochasticEpisodeBatchSource.selfConsistentScheduledEpisodes
            mdp varianceProxy baseVisitFloor t) -> WithTop Nat)
    (hstopping : forall scheduleIndex, IsStoppingTime
      (selfConsistentScheduledNaturalCausalTrajectoryFiltration mdp initialState
        rewardSource initialTable defaultState varianceProxy baseVisitFloor)
      (stoppingPrefix scheduleIndex))
    (hstoppingLower : forall scheduleIndex trajectory,
      (explicitHighProbabilityRounds scheduleIndex : WithTop Nat) <=
        stoppingPrefix scheduleIndex trajectory)
    (hstoppingUpper : forall scheduleIndex trajectory,
      stoppingPrefix scheduleIndex trajectory <=
        (explicitHighProbabilityRounds scheduleIndex + scheduleIndex :
          WithTop Nat))
    (scheduleIndex : Nat) :
    selfConsistentScheduledNaturalCausalExpectedAbsolutePolynomialBaseGrowingRawWindowStoppingAverageRealizedBehaviorRegret
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor stoppingPrefix scheduleIndex <=
      selfConsistentScheduledNaturalCausalPolynomialBaseGrowingRawWindowStoppingL1Budget
        mdp varianceProxy baseVisitFloor scheduleIndex := by
  let source := selfConsistentScheduledCausalSource mdp initialState
    rewardSource initialTable defaultState varianceProxy baseVisitFloor
  let mu := source.trajectoryMeasure
  let process :=
    selfConsistentScheduledNaturalCausalAverageRealizedBehaviorRegretProcess mdp
      initialState rewardSource initialTable defaultState varianceProxy
        baseVisitFloor
  let stoppedProcess :=
    selfConsistentScheduledNaturalCausalStoppingTimeAverageRealizedBehaviorRegretProcess
      mdp initialState rewardSource initialTable defaultState varianceProxy
        baseVisitFloor stoppingPrefix
  have hcoordinateIntegrable : forall rounds,
      Integrable (fun trajectory => |process rounds trajectory|) mu := by
    intro rounds
    exact
      (integrable_selfConsistentScheduledNaturalCausalAverageRealizedBehaviorRegretProcess
        mdp initialState rewardSource varianceProxy law initialTable defaultState
          baseVisitFloor hrewardBound rounds).abs
  have hsumIntegrable : Integrable
      (fun trajectory =>
        (Finset.range (scheduleIndex + 1)).sum fun offset =>
          |process (explicitHighProbabilityRounds scheduleIndex + offset)
            trajectory|) mu := by
    exact IntegrabilitySums.integrable_finset_sum mu
      (Finset.range (scheduleIndex + 1))
      (fun offset trajectory =>
        |process (explicitHighProbabilityRounds scheduleIndex + offset) trajectory|)
      (fun offset _ =>
        hcoordinateIntegrable
          (explicitHighProbabilityRounds scheduleIndex + offset))
  have hstoppedIntegrable : Integrable
      (fun trajectory => |stoppedProcess scheduleIndex trajectory|) mu := by
    have hmem :=
      memLp_one_selfConsistentScheduledNaturalCausalPolynomialBaseGrowingRawWindowStoppingAverageRealizedBehaviorRegret
        mdp initialState rewardSource varianceProxy law initialTable defaultState
          baseVisitFloor hrewardBound stoppingPrefix hstopping hstoppingUpper
            scheduleIndex
    rw [memLp_one_iff_integrable] at hmem
    exact hmem.abs
  have hpoint : forall trajectory,
      |stoppedProcess scheduleIndex trajectory| <=
        (Finset.range (scheduleIndex + 1)).sum fun offset =>
          |process (explicitHighProbabilityRounds scheduleIndex + offset)
            trajectory| := by
    intro trajectory
    obtain ⟨offset, hoffset, hoffsetEq⟩ :=
      exists_polynomialBaseGrowingRawWindow_offset_untopA_eq stoppingPrefix
        hstoppingLower hstoppingUpper scheduleIndex trajectory
    change |process (stoppingPrefix scheduleIndex trajectory).untopA trajectory| <= _
    rw [hoffsetEq]
    exact Finset.single_le_sum
      (fun candidate _ => abs_nonneg
        (process (explicitHighProbabilityRounds scheduleIndex + candidate)
          trajectory)) hoffset
  calc
    selfConsistentScheduledNaturalCausalExpectedAbsolutePolynomialBaseGrowingRawWindowStoppingAverageRealizedBehaviorRegret
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor stoppingPrefix scheduleIndex =
        integral mu (fun trajectory => |stoppedProcess scheduleIndex trajectory|) := by
      rfl
    _ <= integral mu (fun trajectory =>
        (Finset.range (scheduleIndex + 1)).sum fun offset =>
          |process (explicitHighProbabilityRounds scheduleIndex + offset)
            trajectory|) :=
      integral_mono hstoppedIntegrable hsumIntegrable hpoint
    _ = (Finset.range (scheduleIndex + 1)).sum fun offset =>
        integral mu (fun trajectory =>
          |process (explicitHighProbabilityRounds scheduleIndex + offset)
            trajectory|) := by
      exact ExpectationBochnerSums.integral_finset_sum mu
        (Finset.range (scheduleIndex + 1))
        (fun offset trajectory =>
          |process (explicitHighProbabilityRounds scheduleIndex + offset)
            trajectory|)
        (fun offset _ =>
          hcoordinateIntegrable
            (explicitHighProbabilityRounds scheduleIndex + offset))
    _ <= (Finset.range (scheduleIndex + 1)).sum fun offset =>
        selfConsistentScheduledNaturalCausalAverageRealizedBehaviorRegretL1Envelope
          mdp varianceProxy baseVisitFloor
            (explicitHighProbabilityRounds scheduleIndex + offset) := by
      apply Finset.sum_le_sum
      intro offset _
      simpa [process, mu, source,
        selfConsistentScheduledNaturalCausalExpectedAbsoluteAverageRealizedBehaviorRegret]
        using
          selfConsistentScheduledNaturalCausalExpectedAbsoluteAverageRealizedBehaviorRegret_le_L1Envelope
            mdp initialState rewardSource varianceProxy hvarianceProxy law
              initialTable defaultState support baseVisitFloor hbaseFloor
                hrewardBound hhorizon hbaseVisitFloor
                  (explicitHighProbabilityRounds scheduleIndex + offset)
    _ =
      selfConsistentScheduledNaturalCausalPolynomialBaseGrowingRawWindowStoppingL1Budget
        mdp varianceProxy baseVisitFloor scheduleIndex := rfl

/-- Expected absolute raw-window stopped regret tends to zero. -/
theorem
    selfConsistentScheduledNaturalCausalExpectedAbsolutePolynomialBaseGrowingRawWindowStoppingAverageRealizedBehaviorRegret_tendsto_zero
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
    (stoppingPrefix : Nat ->
      HeterogeneousStochasticEpisodeBatchTrajectory mdp
        (fun t =>
          AdaptiveStochasticEpisodeBatchSource.selfConsistentScheduledEpisodes
            mdp varianceProxy baseVisitFloor t) -> WithTop Nat)
    (hstopping : forall scheduleIndex, IsStoppingTime
      (selfConsistentScheduledNaturalCausalTrajectoryFiltration mdp initialState
        rewardSource initialTable defaultState varianceProxy baseVisitFloor)
      (stoppingPrefix scheduleIndex))
    (hstoppingLower : forall scheduleIndex trajectory,
      (explicitHighProbabilityRounds scheduleIndex : WithTop Nat) <=
        stoppingPrefix scheduleIndex trajectory)
    (hstoppingUpper : forall scheduleIndex trajectory,
      stoppingPrefix scheduleIndex trajectory <=
        (explicitHighProbabilityRounds scheduleIndex + scheduleIndex :
          WithTop Nat)) :
    Tendsto
      (selfConsistentScheduledNaturalCausalExpectedAbsolutePolynomialBaseGrowingRawWindowStoppingAverageRealizedBehaviorRegret
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor stoppingPrefix) atTop (nhds 0) := by
  apply squeeze_zero'
  · exact Filter.Eventually.of_forall fun scheduleIndex =>
      selfConsistentScheduledNaturalCausalExpectedAbsolutePolynomialBaseGrowingRawWindowStoppingAverageRealizedBehaviorRegret_nonneg
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor stoppingPrefix scheduleIndex
  · exact Filter.Eventually.of_forall fun scheduleIndex =>
      selfConsistentScheduledNaturalCausalExpectedAbsolutePolynomialBaseGrowingRawWindowStoppingAverageRealizedBehaviorRegret_le_budget
        mdp initialState rewardSource varianceProxy hvarianceProxy law initialTable
          defaultState support baseVisitFloor hbaseFloor hrewardBound hhorizon
            hbaseVisitFloor stoppingPrefix hstopping hstoppingLower
              hstoppingUpper scheduleIndex
  · exact
      selfConsistentScheduledNaturalCausalPolynomialBaseGrowingRawWindowStoppingL1Budget_tendsto_zero
        mdp varianceProxy baseVisitFloor

/-- At exponent one, the raw-window stopped norm is its expected absolute value. -/
theorem
    eLpNorm_one_selfConsistentScheduledNaturalCausalPolynomialBaseGrowingRawWindowStoppingAverageRealizedBehaviorRegret_eq
    (mdp : MDP State Action) (initialState : Measure State)
    [IsProbabilityMeasure initialState]
    [StandardBorelSpace State] [StandardBorelSpace Action]
    (rewardSource : mdp.MeanCompatibleRewardKernel)
    (varianceProxy : NNReal)
    (law : rewardSource.UniformSubgaussianRewardLaw varianceProxy)
    (initialTable : DeterministicMarkovPolicyTable mdp)
    (defaultState : State) (baseVisitFloor : Real)
    (hrewardBound : forall state action, |mdp.reward state action| <= 1)
    (stoppingPrefix : Nat ->
      HeterogeneousStochasticEpisodeBatchTrajectory mdp
        (fun t =>
          AdaptiveStochasticEpisodeBatchSource.selfConsistentScheduledEpisodes
            mdp varianceProxy baseVisitFloor t) -> WithTop Nat)
    (hstopping : forall scheduleIndex, IsStoppingTime
      (selfConsistentScheduledNaturalCausalTrajectoryFiltration mdp initialState
        rewardSource initialTable defaultState varianceProxy baseVisitFloor)
      (stoppingPrefix scheduleIndex))
    (hstoppingUpper : forall scheduleIndex trajectory,
      stoppingPrefix scheduleIndex trajectory <=
        (explicitHighProbabilityRounds scheduleIndex + scheduleIndex :
          WithTop Nat))
    (scheduleIndex : Nat) :
    eLpNorm
        (selfConsistentScheduledNaturalCausalStoppingTimeAverageRealizedBehaviorRegretProcess
          mdp initialState rewardSource initialTable defaultState varianceProxy
            baseVisitFloor stoppingPrefix scheduleIndex)
        1
        (selfConsistentScheduledCausalSource mdp initialState rewardSource
          initialTable defaultState varianceProxy baseVisitFloor).trajectoryMeasure =
      ENNReal.ofReal
        (selfConsistentScheduledNaturalCausalExpectedAbsolutePolynomialBaseGrowingRawWindowStoppingAverageRealizedBehaviorRegret
          mdp initialState rewardSource initialTable defaultState varianceProxy
            baseVisitFloor stoppingPrefix scheduleIndex) := by
  rw [MemLp.eLpNorm_eq_integral_rpow_norm one_ne_zero ENNReal.one_ne_top
    (memLp_one_selfConsistentScheduledNaturalCausalPolynomialBaseGrowingRawWindowStoppingAverageRealizedBehaviorRegret
      mdp initialState rewardSource varianceProxy law initialTable defaultState
        baseVisitFloor hrewardBound stoppingPrefix hstopping hstoppingUpper
          scheduleIndex)]
  simp [
    selfConsistentScheduledNaturalCausalExpectedAbsolutePolynomialBaseGrowingRawWindowStoppingAverageRealizedBehaviorRegret,
    Real.norm_eq_abs]

/-- The raw-window stopped process converges to zero in the exponent-one norm. -/
theorem
    eLpNorm_one_selfConsistentScheduledNaturalCausalPolynomialBaseGrowingRawWindowStoppingAverageRealizedBehaviorRegret_sub_zero_tendsto_zero
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
    (stoppingPrefix : Nat ->
      HeterogeneousStochasticEpisodeBatchTrajectory mdp
        (fun t =>
          AdaptiveStochasticEpisodeBatchSource.selfConsistentScheduledEpisodes
            mdp varianceProxy baseVisitFloor t) -> WithTop Nat)
    (hstopping : forall scheduleIndex, IsStoppingTime
      (selfConsistentScheduledNaturalCausalTrajectoryFiltration mdp initialState
        rewardSource initialTable defaultState varianceProxy baseVisitFloor)
      (stoppingPrefix scheduleIndex))
    (hstoppingLower : forall scheduleIndex trajectory,
      (explicitHighProbabilityRounds scheduleIndex : WithTop Nat) <=
        stoppingPrefix scheduleIndex trajectory)
    (hstoppingUpper : forall scheduleIndex trajectory,
      stoppingPrefix scheduleIndex trajectory <=
        (explicitHighProbabilityRounds scheduleIndex + scheduleIndex :
          WithTop Nat)) :
    Tendsto
      (fun scheduleIndex => eLpNorm
        (selfConsistentScheduledNaturalCausalStoppingTimeAverageRealizedBehaviorRegretProcess
            mdp initialState rewardSource initialTable defaultState varianceProxy
              baseVisitFloor stoppingPrefix scheduleIndex -
          (fun _ => 0))
        1
        (selfConsistentScheduledCausalSource mdp initialState rewardSource
          initialTable defaultState varianceProxy baseVisitFloor).trajectoryMeasure)
      atTop (nhds 0) := by
  have hexpected :=
    selfConsistentScheduledNaturalCausalExpectedAbsolutePolynomialBaseGrowingRawWindowStoppingAverageRealizedBehaviorRegret_tendsto_zero
      mdp initialState rewardSource varianceProxy hvarianceProxy law initialTable
        defaultState support baseVisitFloor hbaseFloor hrewardBound hhorizon
          hbaseVisitFloor stoppingPrefix hstopping hstoppingLower hstoppingUpper
  have hofReal := (ENNReal.continuous_ofReal.tendsto 0).comp hexpected
  have hnorm : Tendsto
      (fun scheduleIndex => eLpNorm
        (selfConsistentScheduledNaturalCausalStoppingTimeAverageRealizedBehaviorRegretProcess
          mdp initialState rewardSource initialTable defaultState varianceProxy
            baseVisitFloor stoppingPrefix scheduleIndex)
        1
        (selfConsistentScheduledCausalSource mdp initialState rewardSource
          initialTable defaultState varianceProxy baseVisitFloor).trajectoryMeasure)
      atTop (nhds 0) := by
    have hnormEq :
        (fun scheduleIndex => eLpNorm
          (selfConsistentScheduledNaturalCausalStoppingTimeAverageRealizedBehaviorRegretProcess
            mdp initialState rewardSource initialTable defaultState varianceProxy
              baseVisitFloor stoppingPrefix scheduleIndex)
          1
          (selfConsistentScheduledCausalSource mdp initialState rewardSource
            initialTable defaultState varianceProxy baseVisitFloor).trajectoryMeasure) =
        (fun scheduleIndex => ENNReal.ofReal
          (selfConsistentScheduledNaturalCausalExpectedAbsolutePolynomialBaseGrowingRawWindowStoppingAverageRealizedBehaviorRegret
            mdp initialState rewardSource initialTable defaultState varianceProxy
              baseVisitFloor stoppingPrefix scheduleIndex)) := by
      funext scheduleIndex
      exact
        eLpNorm_one_selfConsistentScheduledNaturalCausalPolynomialBaseGrowingRawWindowStoppingAverageRealizedBehaviorRegret_eq
          mdp initialState rewardSource varianceProxy law initialTable defaultState
            baseVisitFloor hrewardBound stoppingPrefix hstopping hstoppingUpper
              scheduleIndex
    rw [hnormEq]
    simpa only [Function.comp_apply, ENNReal.ofReal_zero] using hofReal
  convert hnorm using 1
  funext scheduleIndex
  apply eLpNorm_congr_ae
  exact Filter.Eventually.of_forall fun trajectory => by simp

/-
Terminal L1 theorem for the contiguous raw window from `(n+1)^4` through
`(n+1)^4+n` on the exact natural causal source.
-/
theorem
    selfConsistentScheduledCausalSource_explicitPolynomialBaseGrowingRawWindowStoppingTimeNaturalAverageRealizedBehaviorRegret_L1_consistency
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
    (stoppingPrefix : Nat ->
      HeterogeneousStochasticEpisodeBatchTrajectory mdp
        (fun t =>
          AdaptiveStochasticEpisodeBatchSource.selfConsistentScheduledEpisodes
            mdp varianceProxy baseVisitFloor t) -> WithTop Nat)
    (hstopping : forall scheduleIndex, IsStoppingTime
      (selfConsistentScheduledNaturalCausalTrajectoryFiltration mdp initialState
        rewardSource initialTable defaultState varianceProxy baseVisitFloor)
      (stoppingPrefix scheduleIndex))
    (hstoppingLower : forall scheduleIndex trajectory,
      (explicitHighProbabilityRounds scheduleIndex : WithTop Nat) <=
        stoppingPrefix scheduleIndex trajectory)
    (hstoppingUpper : forall scheduleIndex trajectory,
      stoppingPrefix scheduleIndex trajectory <=
        (explicitHighProbabilityRounds scheduleIndex + scheduleIndex :
          WithTop Nat)) :
    let source := selfConsistentScheduledCausalSource mdp initialState
      rewardSource initialTable defaultState varianceProxy baseVisitFloor
    let process :=
      selfConsistentScheduledNaturalCausalAverageRealizedBehaviorRegretProcess mdp
        initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor
    let stoppedProcess :=
      selfConsistentScheduledNaturalCausalStoppingTimeAverageRealizedBehaviorRegretProcess
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor stoppingPrefix
    let expectedAbsolute :=
      selfConsistentScheduledNaturalCausalExpectedAbsolutePolynomialBaseGrowingRawWindowStoppingAverageRealizedBehaviorRegret
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor stoppingPrefix
    let budget :=
      selfConsistentScheduledNaturalCausalPolynomialBaseGrowingRawWindowStoppingL1Budget
        mdp varianceProxy baseVisitFloor
    let rate := fun scheduleIndex =>
      selfConsistentScheduledNaturalCausalRawWindowL1Coefficient mdp varianceProxy /
        (explicitHighProbabilityScale scheduleIndex : Real)
    Tendsto (fun scheduleIndex : Nat => scheduleIndex) atTop atTop /\
      StronglyAdapted
        (selfConsistentScheduledNaturalCausalTrajectoryFiltration mdp initialState
          rewardSource initialTable defaultState varianceProxy baseVisitFloor)
        process /\
      (forall scheduleIndex, Measurable (stoppedProcess scheduleIndex)) /\
      (forall scheduleIndex,
        MemLp (stoppedProcess scheduleIndex) 1 source.trajectoryMeasure) /\
      (forall scheduleIndex, expectedAbsolute scheduleIndex <= budget scheduleIndex) /\
      (forall scheduleIndex, budget scheduleIndex <= rate scheduleIndex) /\
      Tendsto budget atTop (nhds 0) /\
      Tendsto expectedAbsolute atTop (nhds 0) /\
      Tendsto
        (fun scheduleIndex => eLpNorm
          (stoppedProcess scheduleIndex - (fun _ => 0)) 1
            source.trajectoryMeasure) atTop (nhds 0) /\
      TendstoInMeasure source.trajectoryMeasure stoppedProcess atTop (fun _ => 0) /\
      ∀ᵐ trajectory ∂source.trajectoryMeasure,
        Tendsto (fun scheduleIndex => stoppedProcess scheduleIndex trajectory)
          atTop (nhds 0) := by
  dsimp only
  let source := selfConsistentScheduledCausalSource mdp initialState
    rewardSource initialTable defaultState varianceProxy baseVisitFloor
  let process :=
    selfConsistentScheduledNaturalCausalAverageRealizedBehaviorRegretProcess mdp
      initialState rewardSource initialTable defaultState varianceProxy
        baseVisitFloor
  let stoppedProcess :=
    selfConsistentScheduledNaturalCausalStoppingTimeAverageRealizedBehaviorRegretProcess
      mdp initialState rewardSource initialTable defaultState varianceProxy
        baseVisitFloor stoppingPrefix
  let expectedAbsolute :=
    selfConsistentScheduledNaturalCausalExpectedAbsolutePolynomialBaseGrowingRawWindowStoppingAverageRealizedBehaviorRegret
      mdp initialState rewardSource initialTable defaultState varianceProxy
        baseVisitFloor stoppingPrefix
  let budget :=
    selfConsistentScheduledNaturalCausalPolynomialBaseGrowingRawWindowStoppingL1Budget
      mdp varianceProxy baseVisitFloor
  let rate := fun scheduleIndex =>
    selfConsistentScheduledNaturalCausalRawWindowL1Coefficient mdp varianceProxy /
      (explicitHighProbabilityScale scheduleIndex : Real)
  have hmem := fun scheduleIndex =>
    memLp_one_selfConsistentScheduledNaturalCausalPolynomialBaseGrowingRawWindowStoppingAverageRealizedBehaviorRegret
      mdp initialState rewardSource varianceProxy law initialTable defaultState
        baseVisitFloor hrewardBound stoppingPrefix hstopping hstoppingUpper
          scheduleIndex
  have heLp :=
    eLpNorm_one_selfConsistentScheduledNaturalCausalPolynomialBaseGrowingRawWindowStoppingAverageRealizedBehaviorRegret_sub_zero_tendsto_zero
      mdp initialState rewardSource varianceProxy hvarianceProxy law initialTable
        defaultState support baseVisitFloor hbaseFloor hrewardBound hhorizon
          hbaseVisitFloor stoppingPrefix hstopping hstoppingLower hstoppingUpper
  have hlowerNat : forall scheduleIndex trajectory,
      scheduleIndex <= (stoppingPrefix scheduleIndex trajectory).untopA := by
    intro scheduleIndex trajectory
    obtain ⟨offset, _hoffset, hoffsetEq⟩ :=
      exists_polynomialBaseGrowingRawWindow_offset_untopA_eq stoppingPrefix
        hstoppingLower hstoppingUpper scheduleIndex trajectory
    rw [hoffsetEq]
    unfold explicitHighProbabilityRounds explicitHighProbabilityScale
    calc
      scheduleIndex <= scheduleIndex + 1 := Nat.le_succ _
      _ <= (scheduleIndex + 1) ^ 4 := Nat.le_pow (by norm_num)
      _ <= (scheduleIndex + 1) ^ 4 + offset := Nat.le_add_right _ _
  have haeParent :=
    selfConsistentScheduledCausalSource_stoppingTimeNaturalAverageRealizedBehaviorRegret_tendstoAlmostEverywhere_zero_of_nat_le
      mdp initialState rewardSource varianceProxy hvarianceProxy law initialTable
        defaultState support baseVisitFloor hbaseFloor hrewardBound hhorizon
          hbaseVisitFloor stoppingPrefix hstopping hlowerNat
  refine ⟨
    tendsto_id,
    selfConsistentScheduledNaturalCausalAverageRealizedBehaviorRegretProcess_stronglyAdapted
      mdp initialState rewardSource initialTable defaultState varianceProxy
        baseVisitFloor,
    fun scheduleIndex =>
      measurable_selfConsistentScheduledNaturalCausalStoppingTimeAverageRealizedBehaviorRegretProcess
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor stoppingPrefix scheduleIndex (hstopping scheduleIndex),
    hmem,
    fun scheduleIndex =>
      selfConsistentScheduledNaturalCausalExpectedAbsolutePolynomialBaseGrowingRawWindowStoppingAverageRealizedBehaviorRegret_le_budget
        mdp initialState rewardSource varianceProxy hvarianceProxy law initialTable
          defaultState support baseVisitFloor hbaseFloor hrewardBound hhorizon
            hbaseVisitFloor stoppingPrefix hstopping hstoppingLower
              hstoppingUpper scheduleIndex,
    fun scheduleIndex =>
      selfConsistentScheduledNaturalCausalPolynomialBaseGrowingRawWindowStoppingL1Budget_le_rate
        mdp varianceProxy baseVisitFloor scheduleIndex,
    selfConsistentScheduledNaturalCausalPolynomialBaseGrowingRawWindowStoppingL1Budget_tendsto_zero
      mdp varianceProxy baseVisitFloor,
    selfConsistentScheduledNaturalCausalExpectedAbsolutePolynomialBaseGrowingRawWindowStoppingAverageRealizedBehaviorRegret_tendsto_zero
      mdp initialState rewardSource varianceProxy hvarianceProxy law initialTable
        defaultState support baseVisitFloor hbaseFloor hrewardBound hhorizon
          hbaseVisitFloor stoppingPrefix hstopping hstoppingLower hstoppingUpper,
    heLp,
    ?_,
    haeParent.2.2⟩
  exact tendstoInMeasure_of_tendsto_eLpNorm one_ne_zero
    (fun scheduleIndex => (hmem scheduleIndex).aestronglyMeasurable)
    (by fun_prop) (by simpa [stoppedProcess, source] using heLp)

end AdaptiveStochasticSampledEmpiricalOptimisticSource

end BanditRLProof.FiniteHorizonRL
