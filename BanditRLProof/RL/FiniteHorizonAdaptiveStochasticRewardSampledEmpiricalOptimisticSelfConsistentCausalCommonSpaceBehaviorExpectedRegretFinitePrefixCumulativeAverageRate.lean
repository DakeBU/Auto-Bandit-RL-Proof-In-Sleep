import BanditRLProof.RL.FiniteHorizonAdaptiveStochasticRewardSampledEmpiricalOptimisticSelfConsistentCausalCommonSpaceBehaviorExpectedRegretExplicitIntegratedRate
import BanditRLProof.ExpectationBochnerSums

/-!
# Natural-causal finite-prefix cumulative and average behavior regret

This module sums the actual `source.successorPolicyAt` expected-regret process
over `Finset.range rounds` on the one genuine heterogeneous dependent causal
trajectory measure. `ExpectationBochnerSums.integral_finset_sum` identifies the
integral of that pathwise finite sum with the sum of coordinate expectations;
coordinate nonnegativity then identifies those terms with the compiled expected
absolute regrets. Summing the explicit integrated coordinate bounds gives a
finite-prefix cumulative rate, and division by `rounds` gives its Cesaro rate.
The existing `tendsto_natWeightedAverage_zero` theorem at unit natural weights
proves that this deterministic average rate tends to zero, so a nonnegative
squeeze yields average behavior expected-regret consistency.

Regularity for the finite-sum identity is only the probability initial law and
the deterministic reward bound needed by coordinate integrability. The rate
consumer retains finite nonempty Standard Borel State/Action, a probability
initial law, positive horizon/base floor/reward proxy, bounded means, uniform
mean-compatible selected-reward sub-Gaussianity, and exploratory path support.

Failure policy: preserve the actual exploratory behavior rather than the
recommended policy, the same dependent source and sampled batches, natural
coordinate `t` selecting successor batch `t + 1`, scheduled budgets, initial
batch exclusion, and the two model-confidence shares already integrated by the
parent. This route proves a finite-prefix cumulative bound and a vanishing
Cesaro average. It does not provide a closed sublinear cumulative rate,
realized-return control, every-trajectory or anytime guarantees, reachability,
minimax/optimal rates, or complete UCB-VI.
-/

open Filter MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal ProbabilityTheory Topology BigOperators

namespace BanditRLProof.FiniteHorizonRL

universe u v

variable {State : Type u} {Action : Type v}
    [MeasurableSpace State] [MeasurableSpace Action]
    [Fintype State] [Fintype Action]
    [DecidableEq State] [DecidableEq Action]
    [MeasurableSingletonClass State] [MeasurableSingletonClass Action]
    [Nonempty State] [Nonempty Action]

namespace AdaptiveStochasticSampledEmpiricalOptimisticSource

/-- Natural-prefix cumulative expected regret of the actual successor behavior. -/
noncomputable def selfConsistentScheduledNaturalCausalCumulativeBehaviorExpectedRegretProcess
    (mdp : MDP State Action) (initialState : Measure State)
    [IsProbabilityMeasure initialState]
    (rewardSource : mdp.MeanCompatibleRewardKernel)
    (initialTable : DeterministicMarkovPolicyTable mdp)
    (defaultState : State) (varianceProxy : NNReal)
    (baseVisitFloor : Real) (rounds : Nat) :=
  fun trajectory =>
    (Finset.range rounds).sum fun t =>
      selfConsistentScheduledNaturalCausalSuccessorPolicyExpectedRegretProcess
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor t trajectory

/-- Expectation of the natural-prefix cumulative behavior regret. -/
noncomputable def selfConsistentScheduledNaturalCausalExpectedCumulativeBehaviorRegret
    (mdp : MDP State Action) (initialState : Measure State)
    [IsProbabilityMeasure initialState]
    (rewardSource : mdp.MeanCompatibleRewardKernel)
    (initialTable : DeterministicMarkovPolicyTable mdp)
    (defaultState : State) (varianceProxy : NNReal)
    (baseVisitFloor : Real) (rounds : Nat) : Real :=
  integral
    (selfConsistentScheduledCausalSource mdp initialState rewardSource
      initialTable defaultState varianceProxy baseVisitFloor).trajectoryMeasure
    (selfConsistentScheduledNaturalCausalCumulativeBehaviorExpectedRegretProcess
      mdp initialState rewardSource initialTable defaultState varianceProxy
        baseVisitFloor rounds)

/-- Finite-prefix sum of the explicit integrated coordinate rates. -/
noncomputable def selfConsistentScheduledNaturalCausalCumulativeIntegratedBehaviorExpectedRegretRate
    (mdp : MDP State Action) (rounds : Nat) : Real :=
  (Finset.range rounds).sum fun t =>
    selfConsistentScheduledNaturalCausalIntegratedBehaviorExpectedRegretRateAt
      mdp t

/-- Natural-prefix average behavior expected regret. -/
noncomputable def selfConsistentScheduledNaturalCausalAverageBehaviorExpectedRegret
    (mdp : MDP State Action) (initialState : Measure State)
    [IsProbabilityMeasure initialState]
    (rewardSource : mdp.MeanCompatibleRewardKernel)
    (initialTable : DeterministicMarkovPolicyTable mdp)
    (defaultState : State) (varianceProxy : NNReal)
    (baseVisitFloor : Real) (rounds : Nat) : Real :=
  selfConsistentScheduledNaturalCausalExpectedCumulativeBehaviorRegret mdp
      initialState rewardSource initialTable defaultState varianceProxy
        baseVisitFloor rounds /
    (rounds : Real)

/-- Cesaro average of the explicit integrated coordinate rates. -/
noncomputable def selfConsistentScheduledNaturalCausalAverageIntegratedBehaviorExpectedRegretRate
    (mdp : MDP State Action) (rounds : Nat) : Real :=
  selfConsistentScheduledNaturalCausalCumulativeIntegratedBehaviorExpectedRegretRate
      mdp rounds /
    (rounds : Real)

theorem selfConsistentScheduledNaturalCausalCumulativeBehaviorExpectedRegretProcess_nonneg
    (mdp : MDP State Action) (initialState : Measure State)
    [IsProbabilityMeasure initialState]
    (rewardSource : mdp.MeanCompatibleRewardKernel)
    (initialTable : DeterministicMarkovPolicyTable mdp)
    (defaultState : State) (varianceProxy : NNReal)
    (baseVisitFloor : Real) (rounds : Nat) (trajectory) :
    0 <=
      selfConsistentScheduledNaturalCausalCumulativeBehaviorExpectedRegretProcess
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor rounds trajectory := by
  unfold selfConsistentScheduledNaturalCausalCumulativeBehaviorExpectedRegretProcess
  exact Finset.sum_nonneg fun t _ =>
    selfConsistentScheduledNaturalCausalSuccessorPolicyExpectedRegretProcess_nonneg
      mdp initialState rewardSource initialTable defaultState varianceProxy
        baseVisitFloor t trajectory

theorem integrable_selfConsistentScheduledNaturalCausalCumulativeBehaviorExpectedRegretProcess
    (mdp : MDP State Action) (initialState : Measure State)
    [IsProbabilityMeasure initialState]
    (rewardSource : mdp.MeanCompatibleRewardKernel)
    (initialTable : DeterministicMarkovPolicyTable mdp)
    (defaultState : State) (varianceProxy : NNReal)
    (baseVisitFloor : Real)
    (hrewardBound : forall state action, |mdp.reward state action| <= 1)
    (rounds : Nat) :
    Integrable
      (selfConsistentScheduledNaturalCausalCumulativeBehaviorExpectedRegretProcess
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor rounds)
      (selfConsistentScheduledCausalSource mdp initialState rewardSource
        initialTable defaultState varianceProxy baseVisitFloor).trajectoryMeasure := by
  unfold selfConsistentScheduledNaturalCausalCumulativeBehaviorExpectedRegretProcess
  exact IntegrabilitySums.integrable_finset_sum _ _ _ fun t _ =>
    integrable_selfConsistentScheduledNaturalCausalSuccessorPolicyExpectedRegretProcess
      mdp initialState rewardSource initialTable defaultState varianceProxy
        baseVisitFloor hrewardBound t

theorem selfConsistentScheduledNaturalCausalExpectedCumulativeBehaviorRegret_eq_sum_expectedAbsolute
    (mdp : MDP State Action) (initialState : Measure State)
    [IsProbabilityMeasure initialState]
    (rewardSource : mdp.MeanCompatibleRewardKernel)
    (initialTable : DeterministicMarkovPolicyTable mdp)
    (defaultState : State) (varianceProxy : NNReal)
    (baseVisitFloor : Real)
    (hrewardBound : forall state action, |mdp.reward state action| <= 1)
    (rounds : Nat) :
    selfConsistentScheduledNaturalCausalExpectedCumulativeBehaviorRegret mdp
        initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor rounds =
      (Finset.range rounds).sum fun t =>
        selfConsistentScheduledNaturalCausalExpectedAbsoluteBehaviorRegret mdp
          initialState rewardSource initialTable defaultState varianceProxy
            baseVisitFloor t := by
  unfold selfConsistentScheduledNaturalCausalExpectedCumulativeBehaviorRegret
    selfConsistentScheduledNaturalCausalCumulativeBehaviorExpectedRegretProcess
  rw [ExpectationBochnerSums.integral_finset_sum]
  · apply Finset.sum_congr rfl
    intro t _
    unfold selfConsistentScheduledNaturalCausalExpectedAbsoluteBehaviorRegret
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun trajectory =>
      (abs_of_nonneg
        (selfConsistentScheduledNaturalCausalSuccessorPolicyExpectedRegretProcess_nonneg
          mdp initialState rewardSource initialTable defaultState varianceProxy
            baseVisitFloor t trajectory)).symm
  · intro t _
    exact
      integrable_selfConsistentScheduledNaturalCausalSuccessorPolicyExpectedRegretProcess
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor hrewardBound t

theorem selfConsistentScheduledNaturalCausalExpectedCumulativeBehaviorRegret_nonneg
    (mdp : MDP State Action) (initialState : Measure State)
    [IsProbabilityMeasure initialState]
    (rewardSource : mdp.MeanCompatibleRewardKernel)
    (initialTable : DeterministicMarkovPolicyTable mdp)
    (defaultState : State) (varianceProxy : NNReal)
    (baseVisitFloor : Real) (rounds : Nat) :
    0 <= selfConsistentScheduledNaturalCausalExpectedCumulativeBehaviorRegret
      mdp initialState rewardSource initialTable defaultState varianceProxy
        baseVisitFloor rounds := by
  unfold selfConsistentScheduledNaturalCausalExpectedCumulativeBehaviorRegret
  exact integral_nonneg fun trajectory =>
    selfConsistentScheduledNaturalCausalCumulativeBehaviorExpectedRegretProcess_nonneg
      mdp initialState rewardSource initialTable defaultState varianceProxy
        baseVisitFloor rounds trajectory

omit [DecidableEq State] [DecidableEq Action]
    [MeasurableSingletonClass State] [MeasurableSingletonClass Action]
    [Nonempty Action] in
theorem selfConsistentScheduledNaturalCausalCumulativeIntegratedBehaviorExpectedRegretRate_nonneg
    (mdp : MDP State Action) (rounds : Nat) :
    0 <= selfConsistentScheduledNaturalCausalCumulativeIntegratedBehaviorExpectedRegretRate
      mdp rounds := by
  unfold selfConsistentScheduledNaturalCausalCumulativeIntegratedBehaviorExpectedRegretRate
  exact Finset.sum_nonneg fun t _ =>
    selfConsistentScheduledNaturalCausalIntegratedBehaviorExpectedRegretRateAt_nonneg
      mdp t

theorem selfConsistentScheduledNaturalCausalExpectedCumulativeBehaviorRegret_le_rate
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
    (rounds : Nat) :
    selfConsistentScheduledNaturalCausalExpectedCumulativeBehaviorRegret mdp
        initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor rounds <=
      selfConsistentScheduledNaturalCausalCumulativeIntegratedBehaviorExpectedRegretRate
        mdp rounds := by
  rw [selfConsistentScheduledNaturalCausalExpectedCumulativeBehaviorRegret_eq_sum_expectedAbsolute
    mdp initialState rewardSource initialTable defaultState varianceProxy
      baseVisitFloor hrewardBound rounds]
  unfold selfConsistentScheduledNaturalCausalCumulativeIntegratedBehaviorExpectedRegretRate
  exact Finset.sum_le_sum fun t _ =>
    selfConsistentScheduledNaturalCausalExpectedAbsoluteBehaviorRegret_le_rateAt
      mdp initialState rewardSource varianceProxy hvarianceProxy law initialTable
        defaultState support baseVisitFloor hbaseFloor hrewardBound hhorizon
          hbaseVisitFloor t

theorem selfConsistentScheduledNaturalCausalAverageBehaviorExpectedRegret_le_rate
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
    (rounds : Nat) :
    selfConsistentScheduledNaturalCausalAverageBehaviorExpectedRegret mdp
        initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor rounds <=
      selfConsistentScheduledNaturalCausalAverageIntegratedBehaviorExpectedRegretRate
        mdp rounds := by
  unfold selfConsistentScheduledNaturalCausalAverageBehaviorExpectedRegret
    selfConsistentScheduledNaturalCausalAverageIntegratedBehaviorExpectedRegretRate
  exact div_le_div_of_nonneg_right
    (selfConsistentScheduledNaturalCausalExpectedCumulativeBehaviorRegret_le_rate
      mdp initialState rewardSource varianceProxy hvarianceProxy law initialTable
        defaultState support baseVisitFloor hbaseFloor hrewardBound hhorizon
          hbaseVisitFloor rounds)
    (Nat.cast_nonneg rounds)

omit [DecidableEq State] [DecidableEq Action]
    [MeasurableSingletonClass State] [MeasurableSingletonClass Action]
    [Nonempty State] [Nonempty Action] in
theorem selfConsistentScheduledNaturalCausalAverageIntegratedBehaviorExpectedRegretRate_eq_natWeightedAverage
    (mdp : MDP State Action) (rounds : Nat) :
    selfConsistentScheduledNaturalCausalAverageIntegratedBehaviorExpectedRegretRate
        mdp rounds =
      natWeightedAverage (fun _ => 1)
        (selfConsistentScheduledNaturalCausalIntegratedBehaviorExpectedRegretRateAt
          mdp) rounds := by
  simp [selfConsistentScheduledNaturalCausalAverageIntegratedBehaviorExpectedRegretRate,
    selfConsistentScheduledNaturalCausalCumulativeIntegratedBehaviorExpectedRegretRate,
    natWeightedAverage]

omit [DecidableEq State] [DecidableEq Action]
    [MeasurableSingletonClass State] [MeasurableSingletonClass Action]
    [Nonempty State] [Nonempty Action] in
theorem selfConsistentScheduledNaturalCausalAverageIntegratedBehaviorExpectedRegretRate_tendsto_zero
    (mdp : MDP State Action) :
    Tendsto
      (selfConsistentScheduledNaturalCausalAverageIntegratedBehaviorExpectedRegretRate
        mdp) atTop (nhds 0) := by
  rw [show selfConsistentScheduledNaturalCausalAverageIntegratedBehaviorExpectedRegretRate
      mdp =
      natWeightedAverage (fun _ => 1)
        (selfConsistentScheduledNaturalCausalIntegratedBehaviorExpectedRegretRateAt
          mdp) by
    funext rounds
    exact
      selfConsistentScheduledNaturalCausalAverageIntegratedBehaviorExpectedRegretRate_eq_natWeightedAverage
        mdp rounds]
  exact tendsto_natWeightedAverage_zero (fun _ => 1) (by simp) _
    (selfConsistentScheduledNaturalCausalIntegratedBehaviorExpectedRegretRateAt_tendsto_zero
      mdp)

theorem selfConsistentScheduledNaturalCausalAverageBehaviorExpectedRegret_nonneg
    (mdp : MDP State Action) (initialState : Measure State)
    [IsProbabilityMeasure initialState]
    (rewardSource : mdp.MeanCompatibleRewardKernel)
    (initialTable : DeterministicMarkovPolicyTable mdp)
    (defaultState : State) (varianceProxy : NNReal)
    (baseVisitFloor : Real) (rounds : Nat) :
    0 <= selfConsistentScheduledNaturalCausalAverageBehaviorExpectedRegret mdp
      initialState rewardSource initialTable defaultState varianceProxy
        baseVisitFloor rounds := by
  unfold selfConsistentScheduledNaturalCausalAverageBehaviorExpectedRegret
  exact div_nonneg
    (selfConsistentScheduledNaturalCausalExpectedCumulativeBehaviorRegret_nonneg
      mdp initialState rewardSource initialTable defaultState varianceProxy
        baseVisitFloor rounds)
    (Nat.cast_nonneg rounds)

theorem selfConsistentScheduledNaturalCausalAverageBehaviorExpectedRegret_tendsto_zero
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
      (selfConsistentScheduledNaturalCausalAverageBehaviorExpectedRegret mdp
        initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor) atTop (nhds 0) := by
  apply squeeze_zero'
  · exact Filter.Eventually.of_forall fun rounds =>
      selfConsistentScheduledNaturalCausalAverageBehaviorExpectedRegret_nonneg
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor rounds
  · exact Filter.Eventually.of_forall fun rounds =>
      selfConsistentScheduledNaturalCausalAverageBehaviorExpectedRegret_le_rate
        mdp initialState rewardSource varianceProxy hvarianceProxy law initialTable
          defaultState support baseVisitFloor hbaseFloor hrewardBound hhorizon
            hbaseVisitFloor rounds
  · exact
      selfConsistentScheduledNaturalCausalAverageIntegratedBehaviorExpectedRegretRate_tendsto_zero
        mdp

/-- Same-source finite-prefix cumulative and Cesaro-average behavior-regret route. -/
theorem selfConsistentScheduledCausalSource_cumulative_and_averageBehaviorExpectedRegret_explicitRate
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
    (forall rounds, Integrable
      (selfConsistentScheduledNaturalCausalCumulativeBehaviorExpectedRegretProcess
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor rounds) source.trajectoryMeasure) /\
    (forall rounds,
      selfConsistentScheduledNaturalCausalExpectedCumulativeBehaviorRegret mdp
          initialState rewardSource initialTable defaultState varianceProxy
            baseVisitFloor rounds =
        (Finset.range rounds).sum fun t =>
          selfConsistentScheduledNaturalCausalExpectedAbsoluteBehaviorRegret mdp
            initialState rewardSource initialTable defaultState varianceProxy
              baseVisitFloor t) /\
    (forall rounds,
      selfConsistentScheduledNaturalCausalExpectedCumulativeBehaviorRegret mdp
          initialState rewardSource initialTable defaultState varianceProxy
            baseVisitFloor rounds <=
        selfConsistentScheduledNaturalCausalCumulativeIntegratedBehaviorExpectedRegretRate
          mdp rounds) /\
    (forall rounds,
      selfConsistentScheduledNaturalCausalAverageBehaviorExpectedRegret mdp
          initialState rewardSource initialTable defaultState varianceProxy
            baseVisitFloor rounds <=
        selfConsistentScheduledNaturalCausalAverageIntegratedBehaviorExpectedRegretRate
          mdp rounds) /\
    Tendsto
      (selfConsistentScheduledNaturalCausalAverageIntegratedBehaviorExpectedRegretRate
        mdp) atTop (nhds 0) /\
    Tendsto
      (selfConsistentScheduledNaturalCausalAverageBehaviorExpectedRegret mdp
        initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor) atTop (nhds 0) := by
  dsimp only
  exact
    ⟨fun rounds =>
        integrable_selfConsistentScheduledNaturalCausalCumulativeBehaviorExpectedRegretProcess
          mdp initialState rewardSource initialTable defaultState varianceProxy
            baseVisitFloor hrewardBound rounds,
      fun rounds =>
        selfConsistentScheduledNaturalCausalExpectedCumulativeBehaviorRegret_eq_sum_expectedAbsolute
          mdp initialState rewardSource initialTable defaultState varianceProxy
            baseVisitFloor hrewardBound rounds,
      fun rounds =>
        selfConsistentScheduledNaturalCausalExpectedCumulativeBehaviorRegret_le_rate
          mdp initialState rewardSource varianceProxy hvarianceProxy law initialTable
            defaultState support baseVisitFloor hbaseFloor hrewardBound hhorizon
              hbaseVisitFloor rounds,
      fun rounds =>
        selfConsistentScheduledNaturalCausalAverageBehaviorExpectedRegret_le_rate
          mdp initialState rewardSource varianceProxy hvarianceProxy law initialTable
            defaultState support baseVisitFloor hbaseFloor hrewardBound hhorizon
              hbaseVisitFloor rounds,
      selfConsistentScheduledNaturalCausalAverageIntegratedBehaviorExpectedRegretRate_tendsto_zero
        mdp,
      selfConsistentScheduledNaturalCausalAverageBehaviorExpectedRegret_tendsto_zero
        mdp initialState rewardSource varianceProxy hvarianceProxy law initialTable
          defaultState support baseVisitFloor hbaseFloor hrewardBound hhorizon
            hbaseVisitFloor⟩

end AdaptiveStochasticSampledEmpiricalOptimisticSource
end BanditRLProof.FiniteHorizonRL
