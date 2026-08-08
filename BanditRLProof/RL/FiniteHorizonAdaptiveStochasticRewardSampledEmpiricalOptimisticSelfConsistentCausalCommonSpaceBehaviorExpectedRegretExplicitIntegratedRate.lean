import BanditRLProof.RL.FiniteHorizonAdaptiveStochasticRewardSampledEmpiricalOptimisticSelfConsistentCausalCommonSpaceBehaviorExpectedRegretL1Consistency

/-!
# Natural-causal behavior expected-regret explicit integrated rate

This module turns the actual exploratory `source.successorPolicyAt` pointwise
planning certificate into a finite-coordinate expectation bound on the same
genuine heterogeneous dependent causal trajectory measure. A generic event
split integrates a local bound off one measurable bad event and a global bound
on it. For the natural causal source, the local term is the compiled planning
rate, the global term is `2 * horizon`, and the event has the compiled two-share
coordinate model-confidence budget.

The resulting envelope is explicit: the model-event fallback is
`4 * horizon * selfConsistentScheduledLocalDelta mdp t`, and a closed-form
theorem expands both this confidence term and the existing planning rate. The
envelope tends to zero, yielding a quantitative squeeze proof of expected-
absolute behavior-regret convergence without using the realized-return MGF.

Regularity: the generic integral lemma needs a probability measure, a
measurable bad event, integrability, and pointwise local/global bounds. The
causal consumer retains finite nonempty Standard Borel State/Action,
probability initial law, positive horizon/base floor/reward proxy, bounded
means, uniform mean-compatible selected-reward sub-Gaussianity, and path
support. Failure policy preserves the actual exploratory policy, one dependent
source, actual samples, `n`-prefix to `n+1` selection, scheduled budgets,
initial exclusion, and behavior/recommendation separation. This is a
per-coordinate integrated rate, not cumulative/average regret, anytime,
reachability, minimax/optimal rate, or complete UCB-VI.
-/

open Filter MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal ProbabilityTheory Topology BigOperators

namespace BanditRLProof.FiniteHorizonRL

/-- Integrate a local bound off one bad event and a global bound on it. -/
theorem integral_le_add_const_mul_measureReal_of_le_on_compl
    {Omega : Type*} [MeasurableSpace Omega]
    (mu : Measure Omega) [IsProbabilityMeasure mu]
    (f : Omega -> Real) (bad : Set Omega) (hbad : MeasurableSet bad)
    (hf : Integrable f mu) (rate envelope : Real)
    (hrate : 0 <= rate)
    (hglobal : forall omega, f omega <= envelope)
    (hgood : forall omega, omega ∉ bad -> f omega <= rate) :
    integral mu f <= rate + envelope * (mu bad).toReal := by
  let penalty : Omega -> Real := bad.indicator (fun _ => envelope)
  have hpenalty : Integrable penalty mu :=
    (integrable_const envelope).indicator hbad
  have hmajorant : Integrable (fun omega => rate + penalty omega) mu :=
    (integrable_const rate).add hpenalty
  calc
    integral mu f <= integral mu (fun omega => rate + penalty omega) := by
      apply integral_mono hf hmajorant
      intro omega
      by_cases hmem : omega ∈ bad
      · simp [penalty, hmem]
        exact hglobal omega |>.trans (le_add_of_nonneg_left hrate)
      · simp [penalty, hmem]
        exact hgood omega hmem
    _ = rate + envelope * (mu bad).toReal := by
      rw [integral_add (integrable_const rate) hpenalty]
      simp [penalty, hbad, Measure.real_def, mul_comm]

end BanditRLProof.FiniteHorizonRL

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
    [Nonempty Action] in
/-- The named causal planning envelope is pointwise nonnegative. -/
theorem selfConsistentScheduledCausalPlanningRateAt_nonneg
    (mdp : MDP State Action) (t : Nat) :
    0 <= selfConsistentScheduledCausalPlanningRateAt mdp t := by
  unfold selfConsistentScheduledCausalPlanningRateAt
  rw [AdaptiveStochasticEpisodeBatchSource.selfConsistentScheduledTransitionBudgetRateEnvelope_eq]
  unfold exploratoryBehaviorRegretCharge
  positivity

omit [DecidableEq State] [DecidableEq Action]
    [MeasurableSingletonClass State] [MeasurableSingletonClass Action]
    [Nonempty State] [Nonempty Action] in
/-- The two coordinate model-confidence shares have real mass `2 * delta_t`. -/
theorem selfConsistentScheduledCausalCoordinateModelFailureBudget_toReal_eq
    (mdp : MDP State Action) (t : Nat) :
    (selfConsistentScheduledCausalCoordinateModelFailureBudget mdp t).toReal =
      2 * AdaptiveStochasticEpisodeBatchSource.selfConsistentScheduledLocalDelta
        mdp t := by
  have hdelta : 0 <=
      AdaptiveStochasticEpisodeBatchSource.selfConsistentScheduledLocalDelta
        mdp t := by
    rw [selfConsistentScheduledLocalDelta_eq_inv_pow]
    positivity
  unfold selfConsistentScheduledCausalCoordinateModelFailureBudget
  rw [ENNReal.toReal_add (by simp) (by simp)]
  simp only [ENNReal.toReal_ofReal hdelta]
  ring

/-- Planning rate plus the one-event `2H` expectation fallback. -/
noncomputable def selfConsistentScheduledNaturalCausalIntegratedBehaviorExpectedRegretRateAt
    (mdp : MDP State Action) (t : Nat) : Real :=
  selfConsistentScheduledCausalPlanningRateAt mdp t +
    4 * (mdp.horizon : Real) *
      AdaptiveStochasticEpisodeBatchSource.selfConsistentScheduledLocalDelta
        mdp t

omit [DecidableEq State] [DecidableEq Action]
    [MeasurableSingletonClass State] [MeasurableSingletonClass Action]
    [Nonempty State] [Nonempty Action] in
/-- Closed form of the finite-coordinate integrated behavior envelope. -/
theorem selfConsistentScheduledNaturalCausalIntegratedBehaviorExpectedRegretRateAt_eq
    (mdp : MDP State Action) (t : Nat) :
    selfConsistentScheduledNaturalCausalIntegratedBehaviorExpectedRegretRateAt
        mdp t =
      (mdp.horizon : Real) *
          (2 *
            (1 / (AdaptiveEpisodeBatchSource.decayingExplorationScale t : Real) ^ 2 +
              (12 * (Fintype.card State : Real) * (mdp.horizon : Real)) /
                (AdaptiveEpisodeBatchSource.decayingExplorationScale t : Real) ^ 2)) +
        exploratoryBehaviorRegretCharge mdp
          (AdaptiveEpisodeBatchSource.decayingExplorationRate (t + 1)) 1 +
        (4 * (mdp.horizon : Real)) /
          (((t + 2 : Nat) : Real) ^ (mdp.horizon + 5)) := by
  unfold selfConsistentScheduledNaturalCausalIntegratedBehaviorExpectedRegretRateAt
    selfConsistentScheduledCausalPlanningRateAt
  rw [AdaptiveStochasticEpisodeBatchSource.selfConsistentScheduledTransitionBudgetRateEnvelope_eq,
    selfConsistentScheduledLocalDelta_eq_inv_pow]
  ring

omit [DecidableEq State] [DecidableEq Action]
    [MeasurableSingletonClass State] [MeasurableSingletonClass Action]
    [Nonempty Action] in
/-- The explicit integrated behavior envelope is nonnegative. -/
theorem selfConsistentScheduledNaturalCausalIntegratedBehaviorExpectedRegretRateAt_nonneg
    (mdp : MDP State Action) (t : Nat) :
    0 <= selfConsistentScheduledNaturalCausalIntegratedBehaviorExpectedRegretRateAt
      mdp t := by
  unfold selfConsistentScheduledNaturalCausalIntegratedBehaviorExpectedRegretRateAt
  apply add_nonneg (selfConsistentScheduledCausalPlanningRateAt_nonneg mdp t)
  rw [selfConsistentScheduledLocalDelta_eq_inv_pow]
  positivity

/-- Expected absolute behavior regret obeys the explicit finite-coordinate rate. -/
theorem selfConsistentScheduledNaturalCausalExpectedAbsoluteBehaviorRegret_le_rateAt
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
    (t : Nat) :
    selfConsistentScheduledNaturalCausalExpectedAbsoluteBehaviorRegret mdp
        initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor t <=
      selfConsistentScheduledNaturalCausalIntegratedBehaviorExpectedRegretRateAt
        mdp t := by
  let source := selfConsistentScheduledCausalSource mdp initialState
    rewardSource initialTable defaultState varianceProxy baseVisitFloor
  let process :=
    selfConsistentScheduledNaturalCausalSuccessorPolicyExpectedRegretProcess
      mdp initialState rewardSource initialTable defaultState varianceProxy
        baseVisitFloor t
  let bad := selfConsistentScheduledCausalModelRoundBadEvent mdp initialState
    rewardSource initialTable defaultState varianceProxy baseVisitFloor t
  have hsplit : integral source.trajectoryMeasure process <=
      selfConsistentScheduledCausalPlanningRateAt mdp t +
        (2 * (mdp.horizon : Real)) *
          (source.trajectoryMeasure bad).toReal := by
    apply integral_le_add_const_mul_measureReal_of_le_on_compl
      source.trajectoryMeasure process bad
      (measurableSet_selfConsistentScheduledCausalModelRoundBadEvent mdp
        initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor t)
      (integrable_selfConsistentScheduledNaturalCausalSuccessorPolicyExpectedRegretProcess
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor hrewardBound t)
      (selfConsistentScheduledCausalPlanningRateAt mdp t)
      (2 * (mdp.horizon : Real))
      (selfConsistentScheduledCausalPlanningRateAt_nonneg mdp t)
      (fun trajectory =>
        selfConsistentScheduledNaturalCausalSuccessorPolicyExpectedRegretProcess_le_two_mul_horizon
          mdp initialState rewardSource initialTable defaultState varianceProxy
            baseVisitFloor hrewardBound t trajectory)
      (fun trajectory hnot =>
        selfConsistentScheduledCausalSource_successorPolicyAt_expectedRegret_le_rateAt_of_not_mem_modelRoundBadEvent
          mdp initialState rewardSource varianceProxy hvarianceProxy law
            initialTable defaultState support baseVisitFloor hbaseFloor
              hrewardBound hhorizon hbaseVisitFloor trajectory t hnot)
  have hmeasure :=
    selfConsistentScheduledCausalSource_trajectoryMeasure_modelRoundBadEvent_le
      mdp initialState rewardSource varianceProxy hvarianceProxy law
        initialTable defaultState baseVisitFloor t
  have hbudget_ne_top :
      selfConsistentScheduledCausalCoordinateModelFailureBudget mdp t ≠
        (⊤ : ENNReal) := by
    unfold selfConsistentScheduledCausalCoordinateModelFailureBudget
    simp
  have hmeasureReal :
      (source.trajectoryMeasure bad).toReal <=
        (selfConsistentScheduledCausalCoordinateModelFailureBudget mdp t).toReal := by
    apply (ENNReal.toReal_le_toReal
      (measure_ne_top source.trajectoryMeasure bad) hbudget_ne_top).2
    simpa [source, bad] using hmeasure
  have hscaled := mul_le_mul_of_nonneg_left hmeasureReal
    (by positivity : 0 <= 2 * (mdp.horizon : Real))
  have hbound : integral source.trajectoryMeasure process <=
      selfConsistentScheduledCausalPlanningRateAt mdp t +
        (2 * (mdp.horizon : Real)) *
          (selfConsistentScheduledCausalCoordinateModelFailureBudget mdp t).toReal :=
    hsplit.trans (add_le_add (le_refl _) hscaled)
  have habs : selfConsistentScheduledNaturalCausalExpectedAbsoluteBehaviorRegret
      mdp initialState rewardSource initialTable defaultState varianceProxy
        baseVisitFloor t = integral source.trajectoryMeasure process := by
    unfold selfConsistentScheduledNaturalCausalExpectedAbsoluteBehaviorRegret
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun trajectory =>
      abs_of_nonneg
        (selfConsistentScheduledNaturalCausalSuccessorPolicyExpectedRegretProcess_nonneg
          mdp initialState rewardSource initialTable defaultState varianceProxy
            baseVisitFloor t trajectory)
  rw [habs]
  unfold selfConsistentScheduledNaturalCausalIntegratedBehaviorExpectedRegretRateAt
  rw [selfConsistentScheduledCausalCoordinateModelFailureBudget_toReal_eq] at hbound
  nlinarith

omit [DecidableEq State] [DecidableEq Action]
    [MeasurableSingletonClass State] [MeasurableSingletonClass Action]
    [Nonempty State] [Nonempty Action] in
/-- The explicit integrated behavior envelope vanishes. -/
theorem selfConsistentScheduledNaturalCausalIntegratedBehaviorExpectedRegretRateAt_tendsto_zero
    (mdp : MDP State Action) :
    Tendsto
      (selfConsistentScheduledNaturalCausalIntegratedBehaviorExpectedRegretRateAt
        mdp) atTop (nhds 0) := by
  have hdelta : Tendsto
      (AdaptiveStochasticEpisodeBatchSource.selfConsistentScheduledLocalDelta mdp)
      atTop (nhds 0) :=
    (summable_selfConsistentScheduledLocalDelta mdp).tendsto_atTop_zero
  simpa [selfConsistentScheduledNaturalCausalIntegratedBehaviorExpectedRegretRateAt,
    mul_assoc] using
    (selfConsistentScheduledCausalPlanningRateAt_tendsto_zero mdp).add
      (tendsto_const_nhds.mul hdelta)

/-- Quantitative squeeze proof of expected-absolute convergence. -/
theorem selfConsistentScheduledNaturalCausalExpectedAbsoluteBehaviorRegret_tendsto_zero_of_explicit_rate
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
    Tendsto
      (selfConsistentScheduledNaturalCausalExpectedAbsoluteBehaviorRegret mdp
        initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor)
      atTop (nhds 0) := by
  apply squeeze_zero'
  · exact Filter.Eventually.of_forall fun t => integral_nonneg fun _ => abs_nonneg _
  · exact Filter.Eventually.of_forall fun t =>
      selfConsistentScheduledNaturalCausalExpectedAbsoluteBehaviorRegret_le_rateAt
        mdp initialState rewardSource varianceProxy hvarianceProxy law
          initialTable defaultState support baseVisitFloor hbaseFloor
            hrewardBound hhorizon hbaseVisitFloor t
  · exact
      selfConsistentScheduledNaturalCausalIntegratedBehaviorExpectedRegretRateAt_tendsto_zero
        mdp

/-- The finite-coordinate rate, its limit, and the induced expectation limit. -/
theorem selfConsistentScheduledCausalSource_behaviorExpectedRegret_explicitIntegratedRate
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
    (forall t,
      selfConsistentScheduledNaturalCausalExpectedAbsoluteBehaviorRegret mdp
          initialState rewardSource initialTable defaultState varianceProxy
            baseVisitFloor t <=
        selfConsistentScheduledNaturalCausalIntegratedBehaviorExpectedRegretRateAt
          mdp t) /\
      Tendsto
        (selfConsistentScheduledNaturalCausalIntegratedBehaviorExpectedRegretRateAt
          mdp) atTop (nhds 0) /\
      Tendsto
        (selfConsistentScheduledNaturalCausalExpectedAbsoluteBehaviorRegret mdp
          initialState rewardSource initialTable defaultState varianceProxy
            baseVisitFloor) atTop (nhds 0) := by
  exact ⟨fun t =>
      selfConsistentScheduledNaturalCausalExpectedAbsoluteBehaviorRegret_le_rateAt
        mdp initialState rewardSource varianceProxy hvarianceProxy law
          initialTable defaultState support baseVisitFloor hbaseFloor
            hrewardBound hhorizon hbaseVisitFloor t,
    selfConsistentScheduledNaturalCausalIntegratedBehaviorExpectedRegretRateAt_tendsto_zero
      mdp,
    selfConsistentScheduledNaturalCausalExpectedAbsoluteBehaviorRegret_tendsto_zero_of_explicit_rate
      mdp initialState rewardSource varianceProxy hvarianceProxy law initialTable
        defaultState support baseVisitFloor hbaseFloor hrewardBound hhorizon
          hbaseVisitFloor⟩

end AdaptiveStochasticSampledEmpiricalOptimisticSource
end BanditRLProof.FiniteHorizonRL
