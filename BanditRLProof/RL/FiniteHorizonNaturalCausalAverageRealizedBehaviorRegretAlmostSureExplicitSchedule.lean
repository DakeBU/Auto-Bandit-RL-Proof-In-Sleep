import BanditRLProof.RL.FiniteHorizonNaturalCausalAverageRealizedBehaviorRegretL1Consistency
import Mathlib.Analysis.PSeries
import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli

/-!
# Explicit-schedule almost-sure consistency for natural average realized behavior regret

This module keeps the exact process which divides every successor batch by its
own positive episode count and then weights rounds equally. Along the
deterministic fourth-power prefixes `(n + 1)^4`, its compiled all-prefix L1
envelope is dominated by a sum of shifted exponent-three and exponent-two
p-series. Markov's inequality and the first Borel-Cantelli lemma then give
almost-everywhere convergence on this subsequence.

This is not the older total-episode-mass-weighted process and is not an
all-prefix, anytime, or stopping-time almost-sure result.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped BigOperators ENNReal NNReal

namespace BanditRLProof.FiniteHorizonRL

universe u v

variable {State : Type u} {Action : Type v}
    [MeasurableSpace State] [MeasurableSpace Action]
    [Fintype State] [Fintype Action]
    [DecidableEq State] [DecidableEq Action]
    [MeasurableSingletonClass State] [MeasurableSingletonClass Action]
    [Nonempty State] [Nonempty Action]

namespace AdaptiveStochasticSampledEmpiricalOptimisticSource

/-- Shifted exponent-three envelope for the scheduled behavior-regret L1 term. -/
noncomputable def explicitPolynomialPrefixAverageBehaviorRegretL1SummableEnvelope
    (mdp : MDP State Action) (n : Nat) : Real :=
  4 * selfConsistentScheduledNaturalCausalLogarithmicRateCoefficient mdp /
    (explicitHighProbabilityScale n : Real) ^ 3

/-- Shifted exponent-two envelope for the scheduled normalized-return L1 term. -/
noncomputable def explicitPolynomialPrefixAverageReturnL1SummableEnvelope
    (mdp : MDP State Action) (varianceProxy : NNReal) (n : Nat) : Real :=
  (2 * Real.sqrt
      (mdp.globalReturnDeviationPerEpisodeVarianceProxy 1 varianceProxy : Real) *
      Real.exp (1 / 2 : Real)) /
    (explicitHighProbabilityScale n : Real) ^ 2

/-- Summable deterministic L1 envelope on the fourth-power prefix schedule. -/
noncomputable def explicitPolynomialPrefixAverageRealizedBehaviorRegretL1SummableEnvelope
    (mdp : MDP State Action) (varianceProxy : NNReal) (n : Nat) : Real :=
  explicitPolynomialPrefixAverageBehaviorRegretL1SummableEnvelope mdp n +
    explicitPolynomialPrefixAverageReturnL1SummableEnvelope mdp varianceProxy n

omit [DecidableEq State] [DecidableEq Action]
    [MeasurableSingletonClass State] [MeasurableSingletonClass Action]
    [Nonempty State] [Nonempty Action] in
/-- The scheduled logarithmic average is dominated by a shifted exponent-three term. -/
theorem selfConsistentScheduledNaturalCausalLogarithmicAverageIntegratedBehaviorExpectedRegretRate_explicitRounds_le_summableEnvelope
    (mdp : MDP State Action) (n : Nat) :
    selfConsistentScheduledNaturalCausalLogarithmicAverageIntegratedBehaviorExpectedRegretRate
        mdp (explicitHighProbabilityRounds n) <=
      explicitPolynomialPrefixAverageBehaviorRegretL1SummableEnvelope mdp n := by
  let s : Real := explicitHighProbabilityScale n
  let C : Real :=
    selfConsistentScheduledNaturalCausalLogarithmicRateCoefficient mdp
  have hs : 0 < s := by
    dsimp [s]
    exact_mod_cast explicitHighProbabilityScale_pos n
  have hC : 0 <= C :=
    selfConsistentScheduledNaturalCausalLogarithmicRateCoefficient_nonneg mdp
  have hrounds : (explicitHighProbabilityRounds n : Real) = s ^ 4 := by
    simp [explicitHighProbabilityRounds, s]
  have hlog : Real.log s <= s - 1 :=
    Real.log_le_sub_one_of_pos hs
  have hlogBound : 1 + Real.log (s ^ 4) <= 4 * s := by
    rw [Real.log_pow]
    norm_num
    linarith
  have hsPow : 0 < s ^ 4 := pow_pos hs 4
  unfold selfConsistentScheduledNaturalCausalLogarithmicAverageIntegratedBehaviorExpectedRegretRate
    selfConsistentScheduledNaturalCausalLogarithmicCumulativeIntegratedBehaviorExpectedRegretRate
    explicitPolynomialPrefixAverageBehaviorRegretL1SummableEnvelope
  change C * (1 + Real.log (explicitHighProbabilityRounds n : Real)) /
      (explicitHighProbabilityRounds n : Real) <= 4 * C / s ^ 3
  rw [hrounds]
  calc
    C * (1 + Real.log (s ^ 4)) / s ^ 4 <=
        C * (4 * s) / s ^ 4 :=
      div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left hlogBound hC) hsPow.le
    _ = 4 * C / s ^ 3 := by
      field_simp [ne_of_gt hs]

omit [DecidableEq State] [DecidableEq Action]
    [MeasurableSingletonClass State] [MeasurableSingletonClass Action]
    [Nonempty State] [Nonempty Action] in
/-- The scheduled return first moment is dominated by a shifted exponent-two term. -/
theorem selfConsistentScheduledNaturalCausalAverageReturnFirstMomentBound_explicitRounds_le_summableEnvelope
    (mdp : MDP State Action) (varianceProxy : NNReal)
    (baseVisitFloor : Real) (n : Nat) :
    selfConsistentScheduledNaturalCausalAverageReturnFirstMomentBound mdp
        varianceProxy baseVisitFloor (explicitHighProbabilityRounds n) <=
      explicitPolynomialPrefixAverageReturnL1SummableEnvelope mdp
        varianceProxy n := by
  let s : Real := explicitHighProbabilityScale n
  have hs : 0 < s := by
    dsimp [s]
    exact_mod_cast explicitHighProbabilityScale_pos n
  have hrounds : (explicitHighProbabilityRounds n : Real) = s ^ 4 := by
    simp [explicitHighProbabilityRounds, s]
  calc
    selfConsistentScheduledNaturalCausalAverageReturnFirstMomentBound mdp
        varianceProxy baseVisitFloor (explicitHighProbabilityRounds n) <=
      selfConsistentScheduledNaturalCausalAverageReturnInverseSqrtEnvelope mdp
        varianceProxy (explicitHighProbabilityRounds n) :=
      selfConsistentScheduledNaturalCausalAverageReturnFirstMomentBound_le_inverseSqrtEnvelope
        mdp varianceProxy baseVisitFloor (explicitHighProbabilityRounds n)
          (explicitHighProbabilityRounds_pos n)
    _ = explicitPolynomialPrefixAverageReturnL1SummableEnvelope mdp
        varianceProxy n := by
      unfold selfConsistentScheduledNaturalCausalAverageReturnInverseSqrtEnvelope
        explicitPolynomialPrefixAverageReturnL1SummableEnvelope
      rw [hrounds, show s ^ 4 = (s ^ 2) ^ 2 by ring,
        Real.sqrt_sq (sq_nonneg s)]

omit [DecidableEq State] [DecidableEq Action]
    [MeasurableSingletonClass State] [MeasurableSingletonClass Action]
    [Nonempty State] [Nonempty Action] in
/-- The explicit scheduled L1 envelope is nonnegative. -/
theorem explicitPolynomialPrefixAverageRealizedBehaviorRegretL1SummableEnvelope_nonneg
    (mdp : MDP State Action) (varianceProxy : NNReal) (n : Nat) :
    0 <= explicitPolynomialPrefixAverageRealizedBehaviorRegretL1SummableEnvelope
      mdp varianceProxy n := by
  unfold explicitPolynomialPrefixAverageRealizedBehaviorRegretL1SummableEnvelope
    explicitPolynomialPrefixAverageBehaviorRegretL1SummableEnvelope
    explicitPolynomialPrefixAverageReturnL1SummableEnvelope
  exact add_nonneg
    (div_nonneg
      (mul_nonneg (by norm_num)
        (selfConsistentScheduledNaturalCausalLogarithmicRateCoefficient_nonneg
          mdp))
      (pow_nonneg (Nat.cast_nonneg _) 3))
    (div_nonneg (by positivity) (pow_nonneg (Nat.cast_nonneg _) 2))

omit [DecidableEq State] [DecidableEq Action]
    [MeasurableSingletonClass State] [MeasurableSingletonClass Action]
    [Nonempty State] [Nonempty Action] in
/-- The all-prefix L1 envelope is pointwise controlled on fourth-power prefixes. -/
theorem selfConsistentScheduledNaturalCausalAverageRealizedBehaviorRegretL1Envelope_explicitRounds_le_summableEnvelope
    (mdp : MDP State Action) (varianceProxy : NNReal)
    (baseVisitFloor : Real) (n : Nat) :
    selfConsistentScheduledNaturalCausalAverageRealizedBehaviorRegretL1Envelope
        mdp varianceProxy baseVisitFloor (explicitHighProbabilityRounds n) <=
      explicitPolynomialPrefixAverageRealizedBehaviorRegretL1SummableEnvelope
        mdp varianceProxy n := by
  unfold selfConsistentScheduledNaturalCausalAverageRealizedBehaviorRegretL1Envelope
    explicitPolynomialPrefixAverageRealizedBehaviorRegretL1SummableEnvelope
  exact add_le_add
    (selfConsistentScheduledNaturalCausalLogarithmicAverageIntegratedBehaviorExpectedRegretRate_explicitRounds_le_summableEnvelope
      mdp n)
    (selfConsistentScheduledNaturalCausalAverageReturnFirstMomentBound_explicitRounds_le_summableEnvelope
      mdp varianceProxy baseVisitFloor n)

omit [DecidableEq State] [DecidableEq Action]
    [MeasurableSingletonClass State] [MeasurableSingletonClass Action]
    [Nonempty State] [Nonempty Action] in
/-- The shifted exponent-three behavior envelope is summable. -/
theorem summable_explicitPolynomialPrefixAverageBehaviorRegretL1SummableEnvelope
    (mdp : MDP State Action) :
    Summable (explicitPolynomialPrefixAverageBehaviorRegretL1SummableEnvelope mdp) := by
  have hp : Summable (fun n : Nat =>
      1 / (((n + 1 : Nat) : Real) ^ 3)) := by
    simpa only [Nat.cast_add, Nat.cast_one] using
      ((summable_nat_add_iff (f := fun n : Nat =>
        1 / ((n : Real) ^ 3)) 1).2
          (Real.summable_one_div_nat_pow.mpr (by norm_num)))
  unfold explicitPolynomialPrefixAverageBehaviorRegretL1SummableEnvelope
  refine (hp.mul_left
    (4 * selfConsistentScheduledNaturalCausalLogarithmicRateCoefficient mdp)).congr ?_
  intro n
  simp [explicitHighProbabilityScale, div_eq_mul_inv]

omit [DecidableEq State] [DecidableEq Action]
    [MeasurableSingletonClass State] [MeasurableSingletonClass Action]
    [Nonempty State] [Nonempty Action] in
/-- The shifted exponent-two return envelope is summable. -/
theorem summable_explicitPolynomialPrefixAverageReturnL1SummableEnvelope
    (mdp : MDP State Action) (varianceProxy : NNReal) :
    Summable
      (explicitPolynomialPrefixAverageReturnL1SummableEnvelope mdp
        varianceProxy) := by
  have hp : Summable (fun n : Nat =>
      1 / (((n + 1 : Nat) : Real) ^ 2)) := by
    simpa only [Nat.cast_add, Nat.cast_one] using
      ((summable_nat_add_iff (f := fun n : Nat =>
        1 / ((n : Real) ^ 2)) 1).2
          (Real.summable_one_div_nat_pow.mpr (by norm_num)))
  unfold explicitPolynomialPrefixAverageReturnL1SummableEnvelope
  refine (hp.mul_left
    (2 * Real.sqrt
      (mdp.globalReturnDeviationPerEpisodeVarianceProxy 1 varianceProxy : Real) *
      Real.exp (1 / 2 : Real))).congr ?_
  intro n
  simp [explicitHighProbabilityScale, div_eq_mul_inv]

omit [DecidableEq State] [DecidableEq Action]
    [MeasurableSingletonClass State] [MeasurableSingletonClass Action]
    [Nonempty State] [Nonempty Action] in
/-- The deterministic fourth-power scheduled L1 envelope is summable. -/
theorem summable_explicitPolynomialPrefixAverageRealizedBehaviorRegretL1SummableEnvelope
    (mdp : MDP State Action) (varianceProxy : NNReal) :
    Summable
      (explicitPolynomialPrefixAverageRealizedBehaviorRegretL1SummableEnvelope
        mdp varianceProxy) := by
  simpa [explicitPolynomialPrefixAverageRealizedBehaviorRegretL1SummableEnvelope]
    using
      (summable_explicitPolynomialPrefixAverageBehaviorRegretL1SummableEnvelope
          mdp).add
        (summable_explicitPolynomialPrefixAverageReturnL1SummableEnvelope
          mdp varianceProxy)

/-- Expected absolute exact average realized regret on the fourth-power schedule. -/
noncomputable def
    explicitPolynomialPrefixExpectedAbsoluteAverageRealizedBehaviorRegret
    (mdp : MDP State Action) (initialState : Measure State)
    [IsProbabilityMeasure initialState]
    (rewardSource : mdp.MeanCompatibleRewardKernel)
    (initialTable : DeterministicMarkovPolicyTable mdp)
    (defaultState : State) (varianceProxy : NNReal)
    (baseVisitFloor : Real) (n : Nat) : Real :=
  selfConsistentScheduledNaturalCausalExpectedAbsoluteAverageRealizedBehaviorRegret
    mdp initialState rewardSource initialTable defaultState varianceProxy
      baseVisitFloor (explicitHighProbabilityRounds n)

/-- The scheduled expected absolute process is nonnegative. -/
theorem explicitPolynomialPrefixExpectedAbsoluteAverageRealizedBehaviorRegret_nonneg
    (mdp : MDP State Action) (initialState : Measure State)
    [IsProbabilityMeasure initialState]
    (rewardSource : mdp.MeanCompatibleRewardKernel)
    (initialTable : DeterministicMarkovPolicyTable mdp)
    (defaultState : State) (varianceProxy : NNReal)
    (baseVisitFloor : Real) (n : Nat) :
    0 <= explicitPolynomialPrefixExpectedAbsoluteAverageRealizedBehaviorRegret
      mdp initialState rewardSource initialTable defaultState varianceProxy
        baseVisitFloor n := by
  exact
    selfConsistentScheduledNaturalCausalExpectedAbsoluteAverageRealizedBehaviorRegret_nonneg
      mdp initialState rewardSource initialTable defaultState varianceProxy
        baseVisitFloor (explicitHighProbabilityRounds n)

/-- The scheduled expected absolute process is bounded by the summable envelope. -/
theorem explicitPolynomialPrefixExpectedAbsoluteAverageRealizedBehaviorRegret_le_summableEnvelope
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
    (n : Nat) :
    explicitPolynomialPrefixExpectedAbsoluteAverageRealizedBehaviorRegret
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor n <=
      explicitPolynomialPrefixAverageRealizedBehaviorRegretL1SummableEnvelope
        mdp varianceProxy n := by
  exact
    (selfConsistentScheduledNaturalCausalExpectedAbsoluteAverageRealizedBehaviorRegret_le_L1Envelope
      mdp initialState rewardSource varianceProxy hvarianceProxy law initialTable
        defaultState support baseVisitFloor hbaseFloor hrewardBound hhorizon
          hbaseVisitFloor (explicitHighProbabilityRounds n)).trans
      (selfConsistentScheduledNaturalCausalAverageRealizedBehaviorRegretL1Envelope_explicitRounds_le_summableEnvelope
        mdp varianceProxy baseVisitFloor n)

/-- Scheduled expected absolute exact average realized regret is summable. -/
theorem summable_explicitPolynomialPrefixExpectedAbsoluteAverageRealizedBehaviorRegret
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
    Summable
      (explicitPolynomialPrefixExpectedAbsoluteAverageRealizedBehaviorRegret
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor) := by
  exact Summable.of_nonneg_of_le
    (fun n =>
      explicitPolynomialPrefixExpectedAbsoluteAverageRealizedBehaviorRegret_nonneg
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor n)
    (fun n =>
      explicitPolynomialPrefixExpectedAbsoluteAverageRealizedBehaviorRegret_le_summableEnvelope
        mdp initialState rewardSource varianceProxy hvarianceProxy law initialTable
          defaultState support baseVisitFloor hbaseFloor hrewardBound hhorizon
            hbaseVisitFloor n)
    (summable_explicitPolynomialPrefixAverageRealizedBehaviorRegretL1SummableEnvelope
      mdp varianceProxy)

/-- Reciprocal thresholds used to turn fixed-threshold Borel-Cantelli into convergence. -/
noncomputable def explicitPolynomialPrefixReciprocalThreshold (k : Nat) : Real :=
  1 / ((k + 1 : Nat) : Real)

theorem explicitPolynomialPrefixReciprocalThreshold_pos (k : Nat) :
    0 < explicitPolynomialPrefixReciprocalThreshold k := by
  unfold explicitPolynomialPrefixReciprocalThreshold
  positivity

/-- Markov's inequality for one scheduled distance-from-zero violation. -/
theorem explicitPolynomialPrefixAverageRealizedBehaviorRegretDistanceViolationProbability_le_expectedAbsolute_div
    (mdp : MDP State Action) (initialState : Measure State)
    [IsProbabilityMeasure initialState]
    [StandardBorelSpace State] [StandardBorelSpace Action]
    (rewardSource : mdp.MeanCompatibleRewardKernel)
    (varianceProxy : NNReal)
    (law : rewardSource.UniformSubgaussianRewardLaw varianceProxy)
    (initialTable : DeterministicMarkovPolicyTable mdp)
    (defaultState : State) (baseVisitFloor epsilon : Real)
    (hrewardBound : forall state action, |mdp.reward state action| <= 1)
    (hepsilon : 0 < epsilon) (n : Nat) :
    explicitPolynomialPrefixAverageRealizedBehaviorRegretDistanceViolationProbability
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor epsilon n <=
      ENNReal.ofReal
        (explicitPolynomialPrefixExpectedAbsoluteAverageRealizedBehaviorRegret
          mdp initialState rewardSource initialTable defaultState varianceProxy
            baseVisitFloor n / epsilon) := by
  let source := selfConsistentScheduledCausalSource mdp initialState
    rewardSource initialTable defaultState varianceProxy baseVisitFloor
  let mu := source.trajectoryMeasure
  let process := explicitPolynomialPrefixAverageRealizedBehaviorRegretProcess
    mdp initialState rewardSource initialTable defaultState varianceProxy
      baseVisitFloor n
  have hmeas : Measurable process := by
    simpa [process] using
      measurable_explicitPolynomialPrefixAverageRealizedBehaviorRegretProcess
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor n
  have hintegrable : Integrable process mu := by
    simpa [process, mu, source,
      explicitPolynomialPrefixAverageRealizedBehaviorRegretProcess] using
      (integrable_selfConsistentScheduledNaturalCausalAverageRealizedBehaviorRegretProcess
        mdp initialState rewardSource varianceProxy law initialTable defaultState
          baseVisitFloor hrewardBound (explicitHighProbabilityRounds n))
  have hevent :
      explicitPolynomialPrefixAverageRealizedBehaviorRegretDistanceViolationSet
          mdp initialState rewardSource initialTable defaultState varianceProxy
            baseVisitFloor epsilon n =
        {trajectory | ENNReal.ofReal epsilon <=
          ENNReal.ofReal |process trajectory|} := by
    ext trajectory
    simp [explicitPolynomialPrefixAverageRealizedBehaviorRegretDistanceViolationSet,
      process]
  have hmarkov :
      mu {trajectory | ENNReal.ofReal epsilon <=
          ENNReal.ofReal |process trajectory|} <=
        lintegral mu (fun trajectory => ENNReal.ofReal |process trajectory|) /
          ENNReal.ofReal epsilon :=
    meas_ge_le_lintegral_div (μ := mu)
      (hmeas.abs.ennreal_ofReal.aemeasurable)
      (ENNReal.ofReal_ne_zero_iff.mpr hepsilon) ENNReal.ofReal_ne_top
  unfold explicitPolynomialPrefixAverageRealizedBehaviorRegretDistanceViolationProbability
  dsimp only
  change mu
      (explicitPolynomialPrefixAverageRealizedBehaviorRegretDistanceViolationSet
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor epsilon n) <= _
  rw [hevent]
  calc
    mu {trajectory | ENNReal.ofReal epsilon <=
        ENNReal.ofReal |process trajectory|} <=
      lintegral mu (fun trajectory => ENNReal.ofReal |process trajectory|) /
        ENNReal.ofReal epsilon := hmarkov
    _ = ENNReal.ofReal
        (integral mu (fun trajectory => |process trajectory|) / epsilon) := by
      rw [← ofReal_integral_eq_lintegral_ofReal hintegrable.abs
        (Filter.Eventually.of_forall fun _ => abs_nonneg _),
        ENNReal.ofReal_div_of_pos hepsilon]
    _ = ENNReal.ofReal
        (explicitPolynomialPrefixExpectedAbsoluteAverageRealizedBehaviorRegret
          mdp initialState rewardSource initialTable defaultState varianceProxy
            baseVisitFloor n / epsilon) := by
      rfl

/-- Fixed positive scheduled violation probabilities have finite total mass. -/
theorem tsum_explicitPolynomialPrefixAverageRealizedBehaviorRegretDistanceViolationProbability_ne_top
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
    (epsilon : Real) (hepsilon : 0 < epsilon) :
    (∑' n,
      explicitPolynomialPrefixAverageRealizedBehaviorRegretDistanceViolationProbability
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor epsilon n) ≠ ∞ := by
  have hexpected :=
    summable_explicitPolynomialPrefixExpectedAbsoluteAverageRealizedBehaviorRegret
      mdp initialState rewardSource varianceProxy hvarianceProxy law initialTable
        defaultState support baseVisitFloor hbaseFloor hrewardBound hhorizon
          hbaseVisitFloor
  have hdiv : Summable (fun n =>
      explicitPolynomialPrefixExpectedAbsoluteAverageRealizedBehaviorRegret
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor n / epsilon) :=
    hexpected.div_const epsilon
  exact ne_top_of_le_ne_top hdiv.tsum_ofReal_ne_top
    (ENNReal.tsum_le_tsum fun n =>
      explicitPolynomialPrefixAverageRealizedBehaviorRegretDistanceViolationProbability_le_expectedAbsolute_div
        mdp initialState rewardSource varianceProxy law initialTable defaultState
          baseVisitFloor epsilon hrewardBound hepsilon n)

/-- Almost every trajectory eventually avoids every reciprocal scheduled violation. -/
theorem ae_eventually_not_mem_explicitPolynomialPrefixAverageRealizedBehaviorRegretReciprocalDistanceViolationSet
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
    ∀ᵐ trajectory ∂source.trajectoryMeasure, forall k,
      ∀ᶠ n in atTop,
        trajectory ∉
          explicitPolynomialPrefixAverageRealizedBehaviorRegretDistanceViolationSet
            mdp initialState rewardSource initialTable defaultState varianceProxy
              baseVisitFloor (explicitPolynomialPrefixReciprocalThreshold k) n := by
  dsimp only
  apply ae_all_iff.2
  intro k
  apply ae_eventually_notMem
  simpa [explicitPolynomialPrefixAverageRealizedBehaviorRegretDistanceViolationProbability]
    using
      (tsum_explicitPolynomialPrefixAverageRealizedBehaviorRegretDistanceViolationProbability_ne_top
        mdp initialState rewardSource varianceProxy hvarianceProxy law initialTable
          defaultState support baseVisitFloor hbaseFloor hrewardBound hhorizon
            hbaseVisitFloor (explicitPolynomialPrefixReciprocalThreshold k)
              (explicitPolynomialPrefixReciprocalThreshold_pos k))

/-- The exact equal-round average process converges a.e. on fourth-power prefixes. -/
theorem explicitPolynomialPrefixAverageRealizedBehaviorRegret_tendstoAlmostEverywhere_zero
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
    ∀ᵐ trajectory ∂source.trajectoryMeasure,
      Tendsto
        (fun n =>
          explicitPolynomialPrefixAverageRealizedBehaviorRegretProcess mdp
            initialState rewardSource initialTable defaultState varianceProxy
              baseVisitFloor n trajectory)
        atTop (nhds 0) := by
  dsimp only
  have hreciprocal :=
    ae_eventually_not_mem_explicitPolynomialPrefixAverageRealizedBehaviorRegretReciprocalDistanceViolationSet
      mdp initialState rewardSource varianceProxy hvarianceProxy law initialTable
        defaultState support baseVisitFloor hbaseFloor hrewardBound hhorizon
          hbaseVisitFloor
  filter_upwards [hreciprocal] with trajectory htrajectory
  rw [Metric.tendsto_atTop]
  intro epsilon hepsilon
  obtain ⟨k, hk⟩ := exists_nat_one_div_lt hepsilon
  have heventually := htrajectory k
  exact eventually_atTop.1 (by
    filter_upwards [heventually] with n hn
    have hdist :
        dist
            (explicitPolynomialPrefixAverageRealizedBehaviorRegretProcess mdp
              initialState rewardSource initialTable defaultState varianceProxy
                baseVisitFloor n trajectory)
            0 < explicitPolynomialPrefixReciprocalThreshold k := by
      simpa [explicitPolynomialPrefixAverageRealizedBehaviorRegretDistanceViolationSet]
        using hn
    exact hdist.trans (by
      simpa [explicitPolynomialPrefixReciprocalThreshold] using hk))

/-
Terminal route certificate. The trajectory space and process semantics are
unchanged from the all-prefix L1 theorem; only the deterministic fourth-power
subsequence supplies enough summability for first Borel-Cantelli.
-/
/-- Scheduled L1 summability and almost-sure consistency on the common source. -/
theorem selfConsistentScheduledCausalSource_explicitPolynomialPrefixAverageRealizedBehaviorRegret_tendstoAlmostEverywhere_zero
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
    (forall n,
      Measurable
        (explicitPolynomialPrefixAverageRealizedBehaviorRegretProcess mdp
          initialState rewardSource initialTable defaultState varianceProxy
            baseVisitFloor n)) ∧
      Summable
        (explicitPolynomialPrefixAverageRealizedBehaviorRegretL1SummableEnvelope
          mdp varianceProxy) ∧
      Summable
        (explicitPolynomialPrefixExpectedAbsoluteAverageRealizedBehaviorRegret
          mdp initialState rewardSource initialTable defaultState varianceProxy
            baseVisitFloor) ∧
      (forall epsilon, 0 < epsilon ->
        (∑' n,
          explicitPolynomialPrefixAverageRealizedBehaviorRegretDistanceViolationProbability
            mdp initialState rewardSource initialTable defaultState varianceProxy
              baseVisitFloor epsilon n) ≠ ∞) ∧
      ∀ᵐ trajectory ∂source.trajectoryMeasure,
        Tendsto
          (fun n =>
            explicitPolynomialPrefixAverageRealizedBehaviorRegretProcess mdp
              initialState rewardSource initialTable defaultState varianceProxy
                baseVisitFloor n trajectory)
          atTop (nhds 0) := by
  dsimp only
  exact ⟨
    fun n =>
      measurable_explicitPolynomialPrefixAverageRealizedBehaviorRegretProcess
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor n,
    summable_explicitPolynomialPrefixAverageRealizedBehaviorRegretL1SummableEnvelope
      mdp varianceProxy,
    summable_explicitPolynomialPrefixExpectedAbsoluteAverageRealizedBehaviorRegret
      mdp initialState rewardSource varianceProxy hvarianceProxy law initialTable
        defaultState support baseVisitFloor hbaseFloor hrewardBound hhorizon
          hbaseVisitFloor,
    fun epsilon hepsilon =>
      tsum_explicitPolynomialPrefixAverageRealizedBehaviorRegretDistanceViolationProbability_ne_top
        mdp initialState rewardSource varianceProxy hvarianceProxy law initialTable
          defaultState support baseVisitFloor hbaseFloor hrewardBound hhorizon
            hbaseVisitFloor epsilon hepsilon,
    explicitPolynomialPrefixAverageRealizedBehaviorRegret_tendstoAlmostEverywhere_zero
      mdp initialState rewardSource varianceProxy hvarianceProxy law initialTable
        defaultState support baseVisitFloor hbaseFloor hrewardBound hhorizon
          hbaseVisitFloor⟩

end AdaptiveStochasticSampledEmpiricalOptimisticSource

end BanditRLProof.FiniteHorizonRL
