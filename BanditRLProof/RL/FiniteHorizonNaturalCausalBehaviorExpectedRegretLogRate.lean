import BanditRLProof.RL.FiniteHorizonAdaptiveStochasticRewardSampledEmpiricalOptimisticSelfConsistentCausalCommonSpaceBehaviorExpectedRegretFinitePrefixCumulativeAverageRate
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Explicit logarithmic natural-causal cumulative behavior regret

This module closes the symbolic finite-prefix envelope for the actual
`source.successorPolicyAt` behavior on the one genuine heterogeneous dependent
causal trajectory measure. The expanded coordinate rate has an inverse-square
term, the scheduled exploration harmonic term, and a confidence term with
exponent `mdp.horizon + 5`.

The inverse-square budget telescopes after comparison with
`1 / ((t + 1) * (t + 2))`, and the high-power budget is bounded by that square
budget. Mathlib's `harmonic_le_one_add_log` controls the remaining shifted
harmonic sum. The resulting expected cumulative regret is bounded by an
explicit coefficient times `1 + log rounds`; dividing by `rounds` gives an
explicit average envelope tending to zero through
`Real.isLittleO_log_id_atTop`.

Regularity: the scalar sum and asymptotic lemmas are unconditional. The
same-source regret consumers retain finite nonempty Standard Borel
State/Action, a probability initial law, positive horizon/base floor/reward
proxy, bounded deterministic means, uniform mean-compatible selected-reward
sub-Gaussianity, and exploratory path support.

Failure policy: preserve the actual exploratory behavior rather than the
recommended policy, the same dependent source and sampled batches, natural
coordinate `t` selecting successor batch `t + 1`, scheduled budgets, initial
batch exclusion, and both integrated model-confidence shares. This is an
explicit expected cumulative and average rate, not realized-return control,
an anytime/pathwise theorem, state reachability, a minimax-optimal rate, or
complete UCB-VI.
-/

open scoped BigOperators

namespace BanditRLProof

theorem sum_range_one_div_natCast_add_two_sq_le_one (rounds : Nat) :
    (Finset.range rounds).sum (fun t =>
      1 / (((t + 2 : Nat) : Real) ^ 2)) <= 1 := by
  calc
    (Finset.range rounds).sum (fun t =>
        1 / (((t + 2 : Nat) : Real) ^ 2)) <=
        (Finset.range rounds).sum (fun t =>
          1 / (((t + 1 : Nat) : Real) * ((t + 2 : Nat) : Real))) := by
      apply Finset.sum_le_sum
      intro t ht
      apply one_div_le_one_div_of_le (by positivity)
      push_cast
      nlinarith [show (0 : Real) <= t by positivity]
    _ = (Finset.range rounds).sum (fun t =>
          1 / (((t + 1 : Nat) : Real)) -
            1 / (((t + 2 : Nat) : Real))) := by
      apply Finset.sum_congr rfl
      intro t ht
      field_simp
      push_cast
      ring
    _ = 1 - 1 / (((rounds + 1 : Nat) : Real)) := by
      simpa [Nat.cast_add, Nat.cast_one, add_assoc] using
        (Finset.sum_range_sub'
          (fun t : Nat => 1 / (((t + 1 : Nat) : Real))) rounds)
    _ <= 1 := sub_le_self _ (by positivity)

theorem sum_range_one_div_natCast_add_two_pow_le_one
    (rounds exponent : Nat) (hexponent : 2 <= exponent) :
    (Finset.range rounds).sum (fun t =>
      1 / (((t + 2 : Nat) : Real) ^ exponent)) <= 1 := by
  calc
    (Finset.range rounds).sum (fun t =>
        1 / (((t + 2 : Nat) : Real) ^ exponent)) <=
        (Finset.range rounds).sum (fun t =>
          1 / (((t + 2 : Nat) : Real) ^ 2)) := by
      apply Finset.sum_le_sum
      intro t ht
      exact one_div_pow_le_one_div_pow_of_le
        (by exact_mod_cast (show 1 <= t + 2 by omega)) hexponent
    _ <= 1 := sum_range_one_div_natCast_add_two_sq_le_one rounds

theorem sum_range_one_div_natCast_add_three_le_one_add_log
    (rounds : Nat) :
    (Finset.range rounds).sum (fun t =>
      1 / (((t + 3 : Nat) : Real))) <=
        1 + Real.log (rounds : Real) := by
  calc
    (Finset.range rounds).sum (fun t =>
        1 / (((t + 3 : Nat) : Real))) <=
        (Finset.range rounds).sum (fun t =>
          1 / (((t + 1 : Nat) : Real))) := by
      apply Finset.sum_le_sum
      intro t ht
      apply one_div_le_one_div_of_le (by positivity)
      norm_num
    _ = (harmonic rounds : Real) := by
      unfold harmonic
      rw [Rat.cast_sum]
      apply Finset.sum_congr rfl
      intro t ht
      simp only [Rat.cast_inv, Rat.cast_natCast]
      norm_num
    _ <= 1 + Real.log (rounds : Real) := harmonic_le_one_add_log rounds

theorem one_le_one_add_log_natCast (rounds : Nat) :
    (1 : Real) <= 1 + Real.log (rounds : Real) := by
  by_cases hrounds : rounds = 0
  · simp [hrounds]
  · have hone : (1 : Real) <= (rounds : Real) := by
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr hrounds
    linarith [Real.log_nonneg hone]

theorem tendsto_one_add_log_natCast_div_natCast_zero :
    Filter.Tendsto
      (fun rounds : Nat =>
        (1 + Real.log (rounds : Real)) / (rounds : Real))
      Filter.atTop (nhds 0) := by
  have hlog : Filter.Tendsto
      (fun rounds : Nat => Real.log (rounds : Real) / (rounds : Real))
      Filter.atTop (nhds 0) := by
    exact
      (Real.isLittleO_log_id_atTop.comp_tendsto
        tendsto_natCast_atTop_atTop).tendsto_div_nhds_zero
  have hone : Filter.Tendsto
      (fun rounds : Nat => (1 : Real) / (rounds : Real))
      Filter.atTop (nhds 0) :=
    tendsto_const_div_atTop_nhds_zero_nat 1
  simpa [add_div] using hone.add hlog

end BanditRLProof

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

noncomputable def selfConsistentScheduledNaturalCausalInverseSquareRateCoefficient
    (mdp : MDP State Action) : Real :=
  2 * (mdp.horizon : Real) *
    (1 + 12 * (Fintype.card State : Real) * (mdp.horizon : Real))

noncomputable def selfConsistentScheduledNaturalCausalExplorationHarmonicRateCoefficient
    (mdp : MDP State Action) : Real :=
  (mdp.horizon : Real) * (((mdp.horizon + 1 : Nat) : Real))

noncomputable def selfConsistentScheduledNaturalCausalHighPowerRateCoefficient
    (mdp : MDP State Action) : Real :=
  4 * (mdp.horizon : Real)

noncomputable def selfConsistentScheduledNaturalCausalLogarithmicRateCoefficient
    (mdp : MDP State Action) : Real :=
  selfConsistentScheduledNaturalCausalInverseSquareRateCoefficient mdp +
    selfConsistentScheduledNaturalCausalExplorationHarmonicRateCoefficient mdp +
    selfConsistentScheduledNaturalCausalHighPowerRateCoefficient mdp

noncomputable def selfConsistentScheduledNaturalCausalRefinedCumulativeIntegratedBehaviorExpectedRegretRate
    (mdp : MDP State Action) (rounds : Nat) : Real :=
  selfConsistentScheduledNaturalCausalInverseSquareRateCoefficient mdp +
    selfConsistentScheduledNaturalCausalHighPowerRateCoefficient mdp +
    selfConsistentScheduledNaturalCausalExplorationHarmonicRateCoefficient mdp *
      (1 + Real.log (rounds : Real))

noncomputable def selfConsistentScheduledNaturalCausalLogarithmicCumulativeIntegratedBehaviorExpectedRegretRate
    (mdp : MDP State Action) (rounds : Nat) : Real :=
  selfConsistentScheduledNaturalCausalLogarithmicRateCoefficient mdp *
    (1 + Real.log (rounds : Real))

noncomputable def selfConsistentScheduledNaturalCausalLogarithmicAverageIntegratedBehaviorExpectedRegretRate
    (mdp : MDP State Action) (rounds : Nat) : Real :=
  selfConsistentScheduledNaturalCausalLogarithmicCumulativeIntegratedBehaviorExpectedRegretRate
      mdp rounds /
    (rounds : Real)

omit [DecidableEq State] [DecidableEq Action]
    [MeasurableSingletonClass State] [MeasurableSingletonClass Action]
    [Nonempty State] [Nonempty Action] in
theorem selfConsistentScheduledNaturalCausalIntegratedBehaviorExpectedRegretRateAt_eq_threeTerm
    (mdp : MDP State Action) (t : Nat) :
    selfConsistentScheduledNaturalCausalIntegratedBehaviorExpectedRegretRateAt
        mdp t =
      selfConsistentScheduledNaturalCausalInverseSquareRateCoefficient mdp *
          (1 / (((t + 2 : Nat) : Real) ^ 2)) +
        selfConsistentScheduledNaturalCausalExplorationHarmonicRateCoefficient mdp *
          (1 / (((t + 3 : Nat) : Real))) +
        selfConsistentScheduledNaturalCausalHighPowerRateCoefficient mdp *
          (1 / (((t + 2 : Nat) : Real) ^ (mdp.horizon + 5))) := by
  rw [selfConsistentScheduledNaturalCausalIntegratedBehaviorExpectedRegretRateAt_eq]
  unfold selfConsistentScheduledNaturalCausalInverseSquareRateCoefficient
    selfConsistentScheduledNaturalCausalExplorationHarmonicRateCoefficient
    selfConsistentScheduledNaturalCausalHighPowerRateCoefficient
    exploratoryBehaviorRegretCharge
    AdaptiveEpisodeBatchSource.decayingExplorationRate
    AdaptiveEpisodeBatchSource.decayingExplorationScale
  push_cast
  ring

omit [DecidableEq State] [DecidableEq Action]
    [MeasurableSingletonClass State] [MeasurableSingletonClass Action]
    [Nonempty State] [Nonempty Action] in
theorem selfConsistentScheduledNaturalCausalInverseSquareRateCoefficient_nonneg
    (mdp : MDP State Action) :
    0 <= selfConsistentScheduledNaturalCausalInverseSquareRateCoefficient mdp := by
  unfold selfConsistentScheduledNaturalCausalInverseSquareRateCoefficient
  positivity

omit [DecidableEq State] [DecidableEq Action]
    [MeasurableSingletonClass State] [MeasurableSingletonClass Action]
    [Nonempty State] [Nonempty Action] in
theorem selfConsistentScheduledNaturalCausalExplorationHarmonicRateCoefficient_nonneg
    (mdp : MDP State Action) :
    0 <= selfConsistentScheduledNaturalCausalExplorationHarmonicRateCoefficient mdp := by
  unfold selfConsistentScheduledNaturalCausalExplorationHarmonicRateCoefficient
  positivity

omit [DecidableEq State] [DecidableEq Action]
    [MeasurableSingletonClass State] [MeasurableSingletonClass Action]
    [Nonempty State] [Nonempty Action] in
theorem selfConsistentScheduledNaturalCausalHighPowerRateCoefficient_nonneg
    (mdp : MDP State Action) :
    0 <= selfConsistentScheduledNaturalCausalHighPowerRateCoefficient mdp := by
  unfold selfConsistentScheduledNaturalCausalHighPowerRateCoefficient
  positivity

omit [DecidableEq State] [DecidableEq Action]
    [MeasurableSingletonClass State] [MeasurableSingletonClass Action]
    [Nonempty State] [Nonempty Action] in
theorem selfConsistentScheduledNaturalCausalLogarithmicRateCoefficient_nonneg
    (mdp : MDP State Action) :
    0 <= selfConsistentScheduledNaturalCausalLogarithmicRateCoefficient mdp := by
  unfold selfConsistentScheduledNaturalCausalLogarithmicRateCoefficient
  exact add_nonneg
    (add_nonneg
      (selfConsistentScheduledNaturalCausalInverseSquareRateCoefficient_nonneg mdp)
      (selfConsistentScheduledNaturalCausalExplorationHarmonicRateCoefficient_nonneg mdp))
    (selfConsistentScheduledNaturalCausalHighPowerRateCoefficient_nonneg mdp)

omit [DecidableEq State] [DecidableEq Action]
    [MeasurableSingletonClass State] [MeasurableSingletonClass Action]
    [Nonempty State] [Nonempty Action] in
theorem selfConsistentScheduledNaturalCausalCumulativeIntegratedBehaviorExpectedRegretRate_le_refined
    (mdp : MDP State Action) (rounds : Nat) :
    selfConsistentScheduledNaturalCausalCumulativeIntegratedBehaviorExpectedRegretRate
        mdp rounds <=
      selfConsistentScheduledNaturalCausalRefinedCumulativeIntegratedBehaviorExpectedRegretRate
        mdp rounds := by
  let a := selfConsistentScheduledNaturalCausalInverseSquareRateCoefficient mdp
  let b := selfConsistentScheduledNaturalCausalExplorationHarmonicRateCoefficient mdp
  let c := selfConsistentScheduledNaturalCausalHighPowerRateCoefficient mdp
  have ha : 0 <= a :=
    selfConsistentScheduledNaturalCausalInverseSquareRateCoefficient_nonneg mdp
  have hb : 0 <= b :=
    selfConsistentScheduledNaturalCausalExplorationHarmonicRateCoefficient_nonneg mdp
  have hc : 0 <= c :=
    selfConsistentScheduledNaturalCausalHighPowerRateCoefficient_nonneg mdp
  have hsquare := BanditRLProof.sum_range_one_div_natCast_add_two_sq_le_one rounds
  have hharmonic :=
    BanditRLProof.sum_range_one_div_natCast_add_three_le_one_add_log rounds
  have hpower := BanditRLProof.sum_range_one_div_natCast_add_two_pow_le_one
    rounds (mdp.horizon + 5) (by omega)
  have haBound := mul_le_mul_of_nonneg_left hsquare ha
  have hbBound := mul_le_mul_of_nonneg_left hharmonic hb
  have hcBound := mul_le_mul_of_nonneg_left hpower hc
  have hsum :
      selfConsistentScheduledNaturalCausalCumulativeIntegratedBehaviorExpectedRegretRate
          mdp rounds =
        a * (Finset.range rounds).sum (fun t =>
            1 / (((t + 2 : Nat) : Real) ^ 2)) +
          b * (Finset.range rounds).sum (fun t =>
            1 / (((t + 3 : Nat) : Real))) +
          c * (Finset.range rounds).sum (fun t =>
            1 / (((t + 2 : Nat) : Real) ^ (mdp.horizon + 5))) := by
    unfold selfConsistentScheduledNaturalCausalCumulativeIntegratedBehaviorExpectedRegretRate
    simp_rw [selfConsistentScheduledNaturalCausalIntegratedBehaviorExpectedRegretRateAt_eq_threeTerm]
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
    simp only [Finset.mul_sum]
    rfl
  rw [hsum]
  unfold selfConsistentScheduledNaturalCausalRefinedCumulativeIntegratedBehaviorExpectedRegretRate
  change a * _ + b * _ + c * _ <= a + c + b * _
  linarith

omit [DecidableEq State] [DecidableEq Action]
    [MeasurableSingletonClass State] [MeasurableSingletonClass Action]
    [Nonempty State] [Nonempty Action] in
theorem selfConsistentScheduledNaturalCausalRefinedCumulativeIntegratedBehaviorExpectedRegretRate_le_logarithmic
    (mdp : MDP State Action) (rounds : Nat) :
    selfConsistentScheduledNaturalCausalRefinedCumulativeIntegratedBehaviorExpectedRegretRate
        mdp rounds <=
      selfConsistentScheduledNaturalCausalLogarithmicCumulativeIntegratedBehaviorExpectedRegretRate
        mdp rounds := by
  let a := selfConsistentScheduledNaturalCausalInverseSquareRateCoefficient mdp
  let b := selfConsistentScheduledNaturalCausalExplorationHarmonicRateCoefficient mdp
  let c := selfConsistentScheduledNaturalCausalHighPowerRateCoefficient mdp
  let g := 1 + Real.log (rounds : Real)
  have ha : 0 <= a :=
    selfConsistentScheduledNaturalCausalInverseSquareRateCoefficient_nonneg mdp
  have hc : 0 <= c :=
    selfConsistentScheduledNaturalCausalHighPowerRateCoefficient_nonneg mdp
  have hg : 1 <= g := BanditRLProof.one_le_one_add_log_natCast rounds
  have haGrow : a <= a * g := by
    simpa using mul_le_mul_of_nonneg_left hg ha
  have hcGrow : c <= c * g := by
    simpa using mul_le_mul_of_nonneg_left hg hc
  unfold selfConsistentScheduledNaturalCausalRefinedCumulativeIntegratedBehaviorExpectedRegretRate
    selfConsistentScheduledNaturalCausalLogarithmicCumulativeIntegratedBehaviorExpectedRegretRate
    selfConsistentScheduledNaturalCausalLogarithmicRateCoefficient
  change a + c + b * g <= (a + b + c) * g
  nlinarith

omit [DecidableEq State] [DecidableEq Action]
    [MeasurableSingletonClass State] [MeasurableSingletonClass Action]
    [Nonempty State] [Nonempty Action] in
theorem selfConsistentScheduledNaturalCausalCumulativeIntegratedBehaviorExpectedRegretRate_le_logarithmic
    (mdp : MDP State Action) (rounds : Nat) :
    selfConsistentScheduledNaturalCausalCumulativeIntegratedBehaviorExpectedRegretRate
        mdp rounds <=
      selfConsistentScheduledNaturalCausalLogarithmicCumulativeIntegratedBehaviorExpectedRegretRate
        mdp rounds :=
  (selfConsistentScheduledNaturalCausalCumulativeIntegratedBehaviorExpectedRegretRate_le_refined
    mdp rounds).trans
      (selfConsistentScheduledNaturalCausalRefinedCumulativeIntegratedBehaviorExpectedRegretRate_le_logarithmic
        mdp rounds)

omit [DecidableEq State] [DecidableEq Action]
    [MeasurableSingletonClass State] [MeasurableSingletonClass Action]
    [Nonempty State] [Nonempty Action] in
theorem selfConsistentScheduledNaturalCausalLogarithmicCumulativeIntegratedBehaviorExpectedRegretRate_nonneg
    (mdp : MDP State Action) (rounds : Nat) :
    0 <= selfConsistentScheduledNaturalCausalLogarithmicCumulativeIntegratedBehaviorExpectedRegretRate
      mdp rounds := by
  unfold selfConsistentScheduledNaturalCausalLogarithmicCumulativeIntegratedBehaviorExpectedRegretRate
  exact mul_nonneg
    (selfConsistentScheduledNaturalCausalLogarithmicRateCoefficient_nonneg mdp)
    ((show (0 : Real) <= 1 by norm_num).trans
      (BanditRLProof.one_le_one_add_log_natCast rounds))

omit [DecidableEq State] [DecidableEq Action]
    [MeasurableSingletonClass State] [MeasurableSingletonClass Action]
    [Nonempty State] [Nonempty Action] in
theorem selfConsistentScheduledNaturalCausalLogarithmicAverageIntegratedBehaviorExpectedRegretRate_nonneg
    (mdp : MDP State Action) (rounds : Nat) :
    0 <= selfConsistentScheduledNaturalCausalLogarithmicAverageIntegratedBehaviorExpectedRegretRate
      mdp rounds := by
  unfold selfConsistentScheduledNaturalCausalLogarithmicAverageIntegratedBehaviorExpectedRegretRate
  exact div_nonneg
    (selfConsistentScheduledNaturalCausalLogarithmicCumulativeIntegratedBehaviorExpectedRegretRate_nonneg
      mdp rounds)
    (Nat.cast_nonneg rounds)

omit [DecidableEq State] [DecidableEq Action]
    [MeasurableSingletonClass State] [MeasurableSingletonClass Action]
    [Nonempty State] [Nonempty Action] in
theorem selfConsistentScheduledNaturalCausalLogarithmicAverageIntegratedBehaviorExpectedRegretRate_tendsto_zero
    (mdp : MDP State Action) :
    Tendsto
      (selfConsistentScheduledNaturalCausalLogarithmicAverageIntegratedBehaviorExpectedRegretRate
        mdp) atTop (nhds 0) := by
  change Tendsto
    (fun rounds : Nat =>
      selfConsistentScheduledNaturalCausalLogarithmicRateCoefficient mdp *
        (1 + Real.log (rounds : Real)) / (rounds : Real))
    atTop (nhds 0)
  simpa only [mul_div_assoc, mul_zero] using
      BanditRLProof.tendsto_one_add_log_natCast_div_natCast_zero.const_mul
        (selfConsistentScheduledNaturalCausalLogarithmicRateCoefficient mdp)

omit [DecidableEq State] [DecidableEq Action]
    [MeasurableSingletonClass State] [MeasurableSingletonClass Action]
    [Nonempty State] [Nonempty Action] in
theorem selfConsistentScheduledNaturalCausalLogarithmicCumulativeIntegratedBehaviorExpectedRegretRate_isBigO
    (mdp : MDP State Action) :
    (selfConsistentScheduledNaturalCausalLogarithmicCumulativeIntegratedBehaviorExpectedRegretRate
      mdp) =O[atTop]
        (fun rounds : Nat => 1 + Real.log (rounds : Real)) := by
  simpa [selfConsistentScheduledNaturalCausalLogarithmicCumulativeIntegratedBehaviorExpectedRegretRate] using
    (Asymptotics.isBigO_refl
      (fun rounds : Nat => 1 + Real.log (rounds : Real)) atTop).const_mul_left
      (selfConsistentScheduledNaturalCausalLogarithmicRateCoefficient mdp)

theorem selfConsistentScheduledNaturalCausalExpectedCumulativeBehaviorRegret_le_logarithmic
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
      selfConsistentScheduledNaturalCausalLogarithmicCumulativeIntegratedBehaviorExpectedRegretRate
        mdp rounds :=
  (selfConsistentScheduledNaturalCausalExpectedCumulativeBehaviorRegret_le_rate
    mdp initialState rewardSource varianceProxy hvarianceProxy law initialTable
      defaultState support baseVisitFloor hbaseFloor hrewardBound hhorizon
        hbaseVisitFloor rounds).trans
    (selfConsistentScheduledNaturalCausalCumulativeIntegratedBehaviorExpectedRegretRate_le_logarithmic
      mdp rounds)

theorem selfConsistentScheduledNaturalCausalExpectedCumulativeBehaviorRegret_isBigO_one_add_log
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
    (selfConsistentScheduledNaturalCausalExpectedCumulativeBehaviorRegret mdp
      initialState rewardSource initialTable defaultState varianceProxy
        baseVisitFloor) =O[atTop]
      (fun rounds : Nat => 1 + Real.log (rounds : Real)) := by
  have henvelope :=
    selfConsistentScheduledNaturalCausalLogarithmicCumulativeIntegratedBehaviorExpectedRegretRate_isBigO
      mdp
  rw [Asymptotics.isBigO_iff] at henvelope ⊢
  obtain ⟨c, hc⟩ := henvelope
  refine ⟨c, ?_⟩
  filter_upwards [hc] with rounds hrounds
  have hactual :
      0 <= selfConsistentScheduledNaturalCausalExpectedCumulativeBehaviorRegret mdp
        initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor rounds :=
    selfConsistentScheduledNaturalCausalExpectedCumulativeBehaviorRegret_nonneg
      mdp initialState rewardSource initialTable defaultState varianceProxy
        baseVisitFloor rounds
  have henvelopeNonneg :
      0 <= selfConsistentScheduledNaturalCausalLogarithmicCumulativeIntegratedBehaviorExpectedRegretRate
        mdp rounds :=
    selfConsistentScheduledNaturalCausalLogarithmicCumulativeIntegratedBehaviorExpectedRegretRate_nonneg
      mdp rounds
  calc
    ‖selfConsistentScheduledNaturalCausalExpectedCumulativeBehaviorRegret mdp
        initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor rounds‖ =
      selfConsistentScheduledNaturalCausalExpectedCumulativeBehaviorRegret mdp
        initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor rounds := Real.norm_of_nonneg hactual
    _ <= selfConsistentScheduledNaturalCausalLogarithmicCumulativeIntegratedBehaviorExpectedRegretRate
        mdp rounds :=
      selfConsistentScheduledNaturalCausalExpectedCumulativeBehaviorRegret_le_logarithmic
        mdp initialState rewardSource varianceProxy hvarianceProxy law initialTable
          defaultState support baseVisitFloor hbaseFloor hrewardBound hhorizon
            hbaseVisitFloor rounds
    _ = ‖selfConsistentScheduledNaturalCausalLogarithmicCumulativeIntegratedBehaviorExpectedRegretRate
        mdp rounds‖ := (Real.norm_of_nonneg henvelopeNonneg).symm
    _ <= c * ‖1 + Real.log (rounds : Real)‖ := hrounds

theorem selfConsistentScheduledNaturalCausalAverageBehaviorExpectedRegret_le_logarithmic
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
      selfConsistentScheduledNaturalCausalLogarithmicAverageIntegratedBehaviorExpectedRegretRate
        mdp rounds := by
  unfold selfConsistentScheduledNaturalCausalAverageBehaviorExpectedRegret
    selfConsistentScheduledNaturalCausalLogarithmicAverageIntegratedBehaviorExpectedRegretRate
  exact div_le_div_of_nonneg_right
    (selfConsistentScheduledNaturalCausalExpectedCumulativeBehaviorRegret_le_logarithmic
      mdp initialState rewardSource varianceProxy hvarianceProxy law initialTable
        defaultState support baseVisitFloor hbaseFloor hrewardBound hhorizon
          hbaseVisitFloor rounds)
    (Nat.cast_nonneg rounds)

theorem selfConsistentScheduledNaturalCausalAverageBehaviorExpectedRegret_isBigO_log_div_natCast
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
    (selfConsistentScheduledNaturalCausalAverageBehaviorExpectedRegret mdp
      initialState rewardSource initialTable defaultState varianceProxy
        baseVisitFloor) =O[atTop]
      (fun rounds : Nat => (1 + Real.log (rounds : Real)) / (rounds : Real)) := by
  have henvelope :
      (selfConsistentScheduledNaturalCausalLogarithmicAverageIntegratedBehaviorExpectedRegretRate
        mdp) =O[atTop]
        (fun rounds : Nat => (1 + Real.log (rounds : Real)) / (rounds : Real)) := by
    change
      (fun rounds : Nat =>
        selfConsistentScheduledNaturalCausalLogarithmicRateCoefficient mdp *
          (1 + Real.log (rounds : Real)) / (rounds : Real)) =O[atTop]
        (fun rounds : Nat => (1 + Real.log (rounds : Real)) / (rounds : Real))
    simpa only [mul_div_assoc] using
      (Asymptotics.isBigO_refl
        (fun rounds : Nat => (1 + Real.log (rounds : Real)) / (rounds : Real))
        atTop).const_mul_left
          (selfConsistentScheduledNaturalCausalLogarithmicRateCoefficient mdp)
  rw [Asymptotics.isBigO_iff] at henvelope ⊢
  obtain ⟨c, hc⟩ := henvelope
  refine ⟨c, ?_⟩
  filter_upwards [hc] with rounds hrounds
  have hactual :
      0 <= selfConsistentScheduledNaturalCausalAverageBehaviorExpectedRegret mdp
        initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor rounds :=
    selfConsistentScheduledNaturalCausalAverageBehaviorExpectedRegret_nonneg
      mdp initialState rewardSource initialTable defaultState varianceProxy
        baseVisitFloor rounds
  have henvelopeNonneg :
      0 <= selfConsistentScheduledNaturalCausalLogarithmicAverageIntegratedBehaviorExpectedRegretRate
        mdp rounds :=
    selfConsistentScheduledNaturalCausalLogarithmicAverageIntegratedBehaviorExpectedRegretRate_nonneg
      mdp rounds
  calc
    ‖selfConsistentScheduledNaturalCausalAverageBehaviorExpectedRegret mdp
        initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor rounds‖ =
      selfConsistentScheduledNaturalCausalAverageBehaviorExpectedRegret mdp
        initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor rounds := Real.norm_of_nonneg hactual
    _ <= selfConsistentScheduledNaturalCausalLogarithmicAverageIntegratedBehaviorExpectedRegretRate
        mdp rounds :=
      selfConsistentScheduledNaturalCausalAverageBehaviorExpectedRegret_le_logarithmic
        mdp initialState rewardSource varianceProxy hvarianceProxy law initialTable
          defaultState support baseVisitFloor hbaseFloor hrewardBound hhorizon
            hbaseVisitFloor rounds
    _ = ‖selfConsistentScheduledNaturalCausalLogarithmicAverageIntegratedBehaviorExpectedRegretRate
        mdp rounds‖ := (Real.norm_of_nonneg henvelopeNonneg).symm
    _ <= c * ‖(1 + Real.log (rounds : Real)) / (rounds : Real)‖ := hrounds

theorem selfConsistentScheduledNaturalCausalAverageBehaviorExpectedRegret_tendsto_zero_of_logarithmicRate
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
      selfConsistentScheduledNaturalCausalAverageBehaviorExpectedRegret_le_logarithmic
        mdp initialState rewardSource varianceProxy hvarianceProxy law initialTable
          defaultState support baseVisitFloor hbaseFloor hrewardBound hhorizon
            hbaseVisitFloor rounds
  · exact
      selfConsistentScheduledNaturalCausalLogarithmicAverageIntegratedBehaviorExpectedRegretRate_tendsto_zero
        mdp

/-- Same-source explicit logarithmic cumulative and `log(n) / n` average route. -/
theorem selfConsistentScheduledCausalSource_cumulative_and_averageBehaviorExpectedRegret_explicitLogarithmicRate
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
    (forall rounds,
      selfConsistentScheduledNaturalCausalCumulativeIntegratedBehaviorExpectedRegretRate
          mdp rounds <=
        selfConsistentScheduledNaturalCausalRefinedCumulativeIntegratedBehaviorExpectedRegretRate
          mdp rounds /\
      selfConsistentScheduledNaturalCausalRefinedCumulativeIntegratedBehaviorExpectedRegretRate
          mdp rounds <=
        selfConsistentScheduledNaturalCausalLogarithmicCumulativeIntegratedBehaviorExpectedRegretRate
          mdp rounds) /\
    (forall rounds,
      selfConsistentScheduledNaturalCausalExpectedCumulativeBehaviorRegret mdp
          initialState rewardSource initialTable defaultState varianceProxy
            baseVisitFloor rounds <=
        selfConsistentScheduledNaturalCausalLogarithmicCumulativeIntegratedBehaviorExpectedRegretRate
          mdp rounds) /\
    (forall rounds,
      selfConsistentScheduledNaturalCausalAverageBehaviorExpectedRegret mdp
          initialState rewardSource initialTable defaultState varianceProxy
            baseVisitFloor rounds <=
        selfConsistentScheduledNaturalCausalLogarithmicAverageIntegratedBehaviorExpectedRegretRate
          mdp rounds) /\
    (selfConsistentScheduledNaturalCausalLogarithmicCumulativeIntegratedBehaviorExpectedRegretRate
      mdp) =O[atTop] (fun rounds : Nat => 1 + Real.log (rounds : Real)) /\
    (selfConsistentScheduledNaturalCausalExpectedCumulativeBehaviorRegret mdp
      initialState rewardSource initialTable defaultState varianceProxy
        baseVisitFloor) =O[atTop]
      (fun rounds : Nat => 1 + Real.log (rounds : Real)) /\
    (selfConsistentScheduledNaturalCausalAverageBehaviorExpectedRegret mdp
      initialState rewardSource initialTable defaultState varianceProxy
        baseVisitFloor) =O[atTop]
      (fun rounds : Nat => (1 + Real.log (rounds : Real)) / (rounds : Real)) /\
    Tendsto
      (selfConsistentScheduledNaturalCausalLogarithmicAverageIntegratedBehaviorExpectedRegretRate
        mdp) atTop (nhds 0) /\
    Tendsto
      (selfConsistentScheduledNaturalCausalAverageBehaviorExpectedRegret mdp
        initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor) atTop (nhds 0) := by
  exact
    ⟨fun rounds =>
        ⟨selfConsistentScheduledNaturalCausalCumulativeIntegratedBehaviorExpectedRegretRate_le_refined
            mdp rounds,
          selfConsistentScheduledNaturalCausalRefinedCumulativeIntegratedBehaviorExpectedRegretRate_le_logarithmic
            mdp rounds⟩,
      fun rounds =>
        selfConsistentScheduledNaturalCausalExpectedCumulativeBehaviorRegret_le_logarithmic
          mdp initialState rewardSource varianceProxy hvarianceProxy law initialTable
            defaultState support baseVisitFloor hbaseFloor hrewardBound hhorizon
              hbaseVisitFloor rounds,
      fun rounds =>
        selfConsistentScheduledNaturalCausalAverageBehaviorExpectedRegret_le_logarithmic
          mdp initialState rewardSource varianceProxy hvarianceProxy law initialTable
            defaultState support baseVisitFloor hbaseFloor hrewardBound hhorizon
              hbaseVisitFloor rounds,
      selfConsistentScheduledNaturalCausalLogarithmicCumulativeIntegratedBehaviorExpectedRegretRate_isBigO
        mdp,
      selfConsistentScheduledNaturalCausalExpectedCumulativeBehaviorRegret_isBigO_one_add_log
        mdp initialState rewardSource varianceProxy hvarianceProxy law initialTable
          defaultState support baseVisitFloor hbaseFloor hrewardBound hhorizon
            hbaseVisitFloor,
      selfConsistentScheduledNaturalCausalAverageBehaviorExpectedRegret_isBigO_log_div_natCast
        mdp initialState rewardSource varianceProxy hvarianceProxy law initialTable
          defaultState support baseVisitFloor hbaseFloor hrewardBound hhorizon
            hbaseVisitFloor,
      selfConsistentScheduledNaturalCausalLogarithmicAverageIntegratedBehaviorExpectedRegretRate_tendsto_zero
        mdp,
      selfConsistentScheduledNaturalCausalAverageBehaviorExpectedRegret_tendsto_zero_of_logarithmicRate
        mdp initialState rewardSource varianceProxy hvarianceProxy law initialTable
          defaultState support baseVisitFloor hbaseFloor hrewardBound hhorizon
            hbaseVisitFloor⟩

end AdaptiveStochasticSampledEmpiricalOptimisticSource

end BanditRLProof.FiniteHorizonRL
