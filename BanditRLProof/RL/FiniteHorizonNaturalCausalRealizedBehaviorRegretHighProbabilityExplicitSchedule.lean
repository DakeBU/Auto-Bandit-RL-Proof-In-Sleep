import BanditRLProof.RL.FiniteHorizonNaturalCausalRealizedBehaviorRegretHighProbabilityBurninLogRate

/-!
# Explicit polynomial-prefix high-probability natural causal regret schedule

This module chooses the concrete schedule
`scale n = n + 1`, `burnin n = scale n`, `rounds n = scale n ^ 4`, and
`returnDelta n = exp (-scale n)` for the compiled natural-causal burn-in
terminal.  The fourth-power prefix simultaneously absorbs the linear burn-in
charge and the fixed-prefix normalized-return confidence radius.

The result concerns this deterministic cofinal subsequence of prefixes.  It is
not an all-prefix or anytime statement, and the model-tail and return events
are still combined only by a union bound.
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

namespace HeterogeneousAdaptiveStochasticEpisodeBatchSource

omit [DecidableEq State] [DecidableEq Action]
    [MeasurableSingletonClass State] [MeasurableSingletonClass Action]
    [Nonempty State] [Nonempty Action] in
/--
Each positive-count normalized successor coordinate contributes at most one
copy of the one-episode global return proxy.
-/
theorem naturalCumulativeSuccessorAverageReturnVarianceProxy_le_rounds_mul
    (mdp : MDP State Action) (episodes : Nat -> Nat) (rounds : Nat)
    (rewardBound rewardVarianceProxy : NNReal)
    (hepisodes : forall n, 0 < episodes n) :
    naturalCumulativeSuccessorAverageReturnVarianceProxy mdp episodes
        rounds rewardBound rewardVarianceProxy <=
      (rounds : NNReal) *
        mdp.globalReturnDeviationPerEpisodeVarianceProxy
          rewardBound rewardVarianceProxy := by
  rw [naturalCumulativeSuccessorAverageReturnVarianceProxy]
  rw [Finset.sum_range_succ']
  simp only [naturalSuccessorAverageReturnVarianceProxyAt, add_zero]
  calc
    (Finset.range rounds).sum (fun n =>
        ((episodes (n + 1) : NNReal)⁻¹) ^ 2 *
          mdp.iidGlobalSampledCumulativeReturnDeviationVarianceProxy
            (episodes (n + 1)) rewardBound rewardVarianceProxy) <=
        (Finset.range rounds).sum (fun _ =>
          mdp.globalReturnDeviationPerEpisodeVarianceProxy
            rewardBound rewardVarianceProxy) := by
      apply Finset.sum_le_sum
      intro n _hn
      rw [MDP.iidGlobalSampledCumulativeReturnDeviationVarianceProxy_eq]
      have he : (episodes (n + 1) : NNReal) ≠ 0 := by
        exact_mod_cast (Nat.ne_of_gt (hepisodes (n + 1)))
      have he_one : (1 : NNReal) <= (episodes (n + 1) : NNReal) := by
        exact_mod_cast (hepisodes (n + 1))
      have hinv : (episodes (n + 1) : NNReal)⁻¹ <= 1 :=
        inv_le_one_of_one_le₀ he_one
      calc
        ((episodes (n + 1) : NNReal)⁻¹) ^ 2 *
              ((episodes (n + 1) : NNReal) *
                mdp.globalReturnDeviationPerEpisodeVarianceProxy
                  rewardBound rewardVarianceProxy) =
            (episodes (n + 1) : NNReal)⁻¹ *
              mdp.globalReturnDeviationPerEpisodeVarianceProxy
                rewardBound rewardVarianceProxy := by
                  field_simp [he]
        _ <= 1 * mdp.globalReturnDeviationPerEpisodeVarianceProxy
              rewardBound rewardVarianceProxy :=
          mul_le_mul_of_nonneg_right hinv (zero_le _)
        _ = mdp.globalReturnDeviationPerEpisodeVarianceProxy
              rewardBound rewardVarianceProxy := one_mul _
    _ = (rounds : NNReal) *
        mdp.globalReturnDeviationPerEpisodeVarianceProxy
          rewardBound rewardVarianceProxy := by simp

end HeterogeneousAdaptiveStochasticEpisodeBatchSource

namespace AdaptiveStochasticSampledEmpiricalOptimisticSource

/-- Positive scale used by the explicit prefix schedule. -/
def explicitHighProbabilityScale (n : Nat) : Nat := n + 1

/-- The model-tail burn-in is linear in the schedule scale. -/
def explicitHighProbabilityBurnin (n : Nat) : Nat :=
  explicitHighProbabilityScale n

/-- Natural successor prefixes are sampled along a fourth-power subsequence. -/
def explicitHighProbabilityRounds (n : Nat) : Nat :=
  explicitHighProbabilityScale n ^ 4

/-- Exponentially vanishing fixed-prefix return failure share. -/
noncomputable def explicitHighProbabilityReturnDelta (n : Nat) : Real :=
  Real.exp (-(explicitHighProbabilityScale n : Real))

theorem explicitHighProbabilityScale_pos (n : Nat) :
    0 < explicitHighProbabilityScale n := by
  simp [explicitHighProbabilityScale]

theorem explicitHighProbabilityBurnin_le_rounds (n : Nat) :
    explicitHighProbabilityBurnin n <= explicitHighProbabilityRounds n := by
  unfold explicitHighProbabilityBurnin explicitHighProbabilityRounds
  exact Nat.le_pow (by norm_num)

theorem explicitHighProbabilityRounds_pos (n : Nat) :
    0 < explicitHighProbabilityRounds n := by
  unfold explicitHighProbabilityRounds
  exact pow_pos (explicitHighProbabilityScale_pos n) 4

theorem explicitHighProbabilityReturnDelta_pos (n : Nat) :
    0 < explicitHighProbabilityReturnDelta n := by
  exact Real.exp_pos _

theorem explicitHighProbabilityReturnDelta_le_one (n : Nat) :
    explicitHighProbabilityReturnDelta n <= 1 := by
  rw [explicitHighProbabilityReturnDelta, Real.exp_le_one_iff]
  exact neg_nonpos.mpr (Nat.cast_nonneg _)

theorem explicitHighProbabilityScale_tendsto_atTop :
    Tendsto explicitHighProbabilityScale atTop atTop := by
  simpa [explicitHighProbabilityScale] using
    (Filter.tendsto_add_atTop_nat 1)

theorem explicitHighProbabilityScale_real_tendsto_atTop :
    Tendsto (fun n => (explicitHighProbabilityScale n : Real))
      atTop atTop :=
  tendsto_natCast_atTop_atTop.comp explicitHighProbabilityScale_tendsto_atTop

theorem explicitHighProbabilityRounds_tendsto_atTop :
    Tendsto explicitHighProbabilityRounds atTop atTop := by
  exact (tendsto_pow_atTop (by norm_num : (4 : Nat) ≠ 0)).comp
    explicitHighProbabilityScale_tendsto_atTop

theorem explicitHighProbabilityReturnDelta_tendsto_zero :
    Tendsto explicitHighProbabilityReturnDelta atTop (nhds 0) := by
  have hneg : Tendsto
      (fun n => -(explicitHighProbabilityScale n : Real)) atTop atBot :=
    tendsto_neg_atBot_iff.mpr explicitHighProbabilityScale_real_tendsto_atTop
  exact Real.tendsto_exp_atBot.comp hneg

omit [DecidableEq State] [DecidableEq Action]
    [MeasurableSingletonClass State] [MeasurableSingletonClass Action]
    [Nonempty State] [Nonempty Action] in
/-- Self-consistent specialization of the generic own-count proxy bound. -/
theorem selfConsistentScheduledNaturalCausalCumulativeReturnVarianceProxy_le_rounds_mul
    (mdp : MDP State Action) (varianceProxy : NNReal)
    (baseVisitFloor : Real) (rounds : Nat) :
    selfConsistentScheduledNaturalCausalCumulativeReturnVarianceProxy
        mdp varianceProxy baseVisitFloor rounds <=
      (rounds : NNReal) *
        mdp.globalReturnDeviationPerEpisodeVarianceProxy 1 varianceProxy := by
  simpa [selfConsistentScheduledNaturalCausalCumulativeReturnVarianceProxy] using
    (HeterogeneousAdaptiveStochasticEpisodeBatchSource.naturalCumulativeSuccessorAverageReturnVarianceProxy_le_rounds_mul
      mdp
      (fun t =>
        AdaptiveStochasticEpisodeBatchSource.selfConsistentScheduledEpisodes
          mdp varianceProxy baseVisitFloor t)
      rounds 1 varianceProxy
      (fun t =>
        AdaptiveStochasticEpisodeBatchSource.selfConsistentScheduledEpisodes_pos
          mdp varianceProxy baseVisitFloor t))

/-- Return-confidence contribution after division by the scheduled prefix. -/
noncomputable def explicitPolynomialPrefixAverageReturnRadius
    (mdp : MDP State Action) (varianceProxy : NNReal)
    (baseVisitFloor : Real) (n : Nat) : Real :=
  Concentration.subGaussianSumConfidenceRadius
      (selfConsistentScheduledNaturalCausalCumulativeReturnVarianceProxy
        mdp varianceProxy baseVisitFloor (explicitHighProbabilityRounds n))
      (explicitHighProbabilityReturnDelta n) /
    (explicitHighProbabilityRounds n : Real)

omit [DecidableEq State] [DecidableEq Action]
    [MeasurableSingletonClass State] [MeasurableSingletonClass Action]
    [Nonempty State] [Nonempty Action] in
/-- A coarse `O(1 / scale)` envelope for the scheduled average radius. -/
theorem explicitPolynomialPrefixAverageReturnRadius_le
    (mdp : MDP State Action) (varianceProxy : NNReal)
    (baseVisitFloor : Real) (n : Nat) :
    explicitPolynomialPrefixAverageReturnRadius
        mdp varianceProxy baseVisitFloor n <=
      2 * (((mdp.globalReturnDeviationPerEpisodeVarianceProxy
          1 varianceProxy : NNReal) : Real) + 1) /
        (explicitHighProbabilityScale n : Real) := by
  let s : Real := explicitHighProbabilityScale n
  let C : Real :=
    ((mdp.globalReturnDeviationPerEpisodeVarianceProxy
      1 varianceProxy : NNReal) : Real)
  let radius : Real :=
    Concentration.subGaussianSumConfidenceRadius
      (selfConsistentScheduledNaturalCausalCumulativeReturnVarianceProxy
        mdp varianceProxy baseVisitFloor (explicitHighProbabilityRounds n))
      (explicitHighProbabilityReturnDelta n)
  have hs_nat : 0 < explicitHighProbabilityScale n :=
    explicitHighProbabilityScale_pos n
  have hs : 0 < s := by
    dsimp [s]
    exact_mod_cast hs_nat
  have hs_one : 1 <= s := by
    dsimp [s]
    exact_mod_cast hs_nat
  have hC : 0 <= C := NNReal.coe_nonneg _
  have hproxyNN :=
    selfConsistentScheduledNaturalCausalCumulativeReturnVarianceProxy_le_rounds_mul
      mdp varianceProxy baseVisitFloor (explicitHighProbabilityRounds n)
  have hproxyReal :
      ((selfConsistentScheduledNaturalCausalCumulativeReturnVarianceProxy
        mdp varianceProxy baseVisitFloor
          (explicitHighProbabilityRounds n) : NNReal) : Real) <=
      (((explicitHighProbabilityRounds n : NNReal) *
        mdp.globalReturnDeviationPerEpisodeVarianceProxy
          1 varianceProxy : NNReal) : Real) :=
    NNReal.coe_le_coe.mpr hproxyNN
  have hproxy :
      ((selfConsistentScheduledNaturalCausalCumulativeReturnVarianceProxy
          mdp varianceProxy baseVisitFloor
            (explicitHighProbabilityRounds n) : NNReal) : Real) <=
        s ^ 4 * C := by
    simpa [explicitHighProbabilityRounds, s, C] using hproxyReal
  have hlog :
      Real.log (2 / explicitHighProbabilityReturnDelta n) =
        Real.log 2 + s := by
    rw [Real.log_div (by norm_num)
      (ne_of_gt (explicitHighProbabilityReturnDelta_pos n))]
    rw [explicitHighProbabilityReturnDelta, Real.log_exp]
    simp [s]
  have hlog_nonneg :
      0 <= Real.log (2 / explicitHighProbabilityReturnDelta n) := by
    have hone : (1 : Real) <= 2 / explicitHighProbabilityReturnDelta n := by
      rw [le_div_iff₀ (explicitHighProbabilityReturnDelta_pos n)]
      linarith [explicitHighProbabilityReturnDelta_le_one n]
    exact Real.log_nonneg hone
  have hlog_le :
      Real.log (2 / explicitHighProbabilityReturnDelta n) <= 2 * s := by
    rw [hlog]
    have hlogTwo :=
      Real.log_le_sub_one_of_pos (by norm_num : (0 : Real) < 2)
    norm_num at hlogTwo
    linarith
  have hradius_nonneg : 0 <= radius :=
    Concentration.subGaussianSumConfidenceRadius_nonneg _ _
  have hinside : radius ^ 2 <= 4 * C * s ^ 5 := by
    rw [show radius ^ 2 =
      2 * (((selfConsistentScheduledNaturalCausalCumulativeReturnVarianceProxy
          mdp varianceProxy baseVisitFloor
            (explicitHighProbabilityRounds n) : NNReal) : Real)) *
        Real.log (2 / explicitHighProbabilityReturnDelta n) by
      exact Concentration.subGaussianSumConfidenceRadius_sq _ _
        (explicitHighProbabilityReturnDelta_pos n)
        (explicitHighProbabilityReturnDelta_le_one n)]
    calc
      2 * (((selfConsistentScheduledNaturalCausalCumulativeReturnVarianceProxy
          mdp varianceProxy baseVisitFloor
            (explicitHighProbabilityRounds n) : NNReal) : Real)) *
            Real.log (2 / explicitHighProbabilityReturnDelta n) <=
          2 * (s ^ 4 * C) * (2 * s) := by
            gcongr
      _ = 4 * C * s ^ 5 := by ring
  have hCquad : C <= (C + 1) ^ 2 := by
    nlinarith [sq_nonneg C]
  have hs56 : s ^ 5 <= s ^ 6 := by
    calc
      s ^ 5 = s ^ 5 * 1 := by ring
      _ <= s ^ 5 * s :=
        mul_le_mul_of_nonneg_left hs_one (pow_nonneg hs.le 5)
      _ = s ^ 6 := by ring
  have hproduct : C * s ^ 5 <= (C + 1) ^ 2 * s ^ 6 := by
    calc
      C * s ^ 5 <= (C + 1) ^ 2 * s ^ 5 :=
        mul_le_mul_of_nonneg_right hCquad (pow_nonneg hs.le 5)
      _ <= (C + 1) ^ 2 * s ^ 6 :=
        mul_le_mul_of_nonneg_left hs56 (sq_nonneg (C + 1))
  have hsquare :
      radius ^ 2 <= (2 * (C + 1) * s ^ 3) ^ 2 := by
    calc
      radius ^ 2 <= 4 * C * s ^ 5 := hinside
      _ <= 4 * ((C + 1) ^ 2 * s ^ 6) := by
        simpa [mul_assoc] using
          (mul_le_mul_of_nonneg_left hproduct
            (by norm_num : (0 : Real) <= 4))
      _ = (2 * (C + 1) * s ^ 3) ^ 2 := by ring
  have hradius : radius <= 2 * (C + 1) * s ^ 3 :=
    (sq_le_sq₀ hradius_nonneg (by positivity)).mp hsquare
  have hrounds :
      (explicitHighProbabilityRounds n : Real) = s ^ 4 := by
    simp [explicitHighProbabilityRounds, s]
  have hrounds_pos : 0 < (explicitHighProbabilityRounds n : Real) := by
    exact_mod_cast explicitHighProbabilityRounds_pos n
  change radius / (explicitHighProbabilityRounds n : Real) <=
      2 * (C + 1) / s
  calc
    radius / (explicitHighProbabilityRounds n : Real) <=
        (2 * (C + 1) * s ^ 3) /
          (explicitHighProbabilityRounds n : Real) :=
      div_le_div_of_nonneg_right hradius hrounds_pos.le
    _ = 2 * (C + 1) / s := by
      rw [hrounds]
      field_simp [ne_of_gt hs]

/-- The explicit fixed-prefix return confidence contribution vanishes. -/
theorem explicitPolynomialPrefixAverageReturnRadius_tendsto_zero
    (mdp : MDP State Action) (varianceProxy : NNReal)
    (baseVisitFloor : Real) :
    Tendsto
      (explicitPolynomialPrefixAverageReturnRadius
        mdp varianceProxy baseVisitFloor) atTop (nhds 0) := by
  apply squeeze_zero
  · intro n
    exact div_nonneg
      (Concentration.subGaussianSumConfidenceRadius_nonneg _ _)
      (Nat.cast_nonneg _)
  · intro n
    exact explicitPolynomialPrefixAverageReturnRadius_le
      mdp varianceProxy baseVisitFloor n
  · exact tendsto_const_nhds.div_atTop
      explicitHighProbabilityScale_real_tendsto_atTop

/-- Exact tail-model plus return-share budget along the explicit schedule. -/
noncomputable def explicitPolynomialPrefixTailModelReturnFailureBudget
    (mdp : MDP State Action) (n : Nat) : ENNReal :=
  selfConsistentScheduledNaturalCausalBurninTailModelReturnFailureBudget
    mdp (explicitHighProbabilityBurnin n)
      (explicitHighProbabilityReturnDelta n)

/-- Scheduled positive-prefix average realized behavior-regret envelope. -/
noncomputable def explicitPolynomialPrefixAverageRealizedBehaviorRegretRate
    (mdp : MDP State Action) (varianceProxy : NNReal)
    (baseVisitFloor : Real) (n : Nat) : Real :=
  selfConsistentScheduledNaturalCausalBurninRealizedAverageLogarithmicRate
    mdp varianceProxy baseVisitFloor
      (explicitHighProbabilityBurnin n)
      (explicitHighProbabilityRounds n)
      (explicitHighProbabilityReturnDelta n)

omit [DecidableEq State] [DecidableEq Action]
    [MeasurableSingletonClass State] [MeasurableSingletonClass Action]
    [Nonempty State] [Nonempty Action] in
/-- The exact union-bound failure budget vanishes along the schedule. -/
theorem explicitPolynomialPrefixTailModelReturnFailureBudget_tendsto_zero
    (mdp : MDP State Action) :
    Tendsto (explicitPolynomialPrefixTailModelReturnFailureBudget mdp)
      atTop (nhds 0) := by
  have htail :
      Tendsto
        (fun n =>
          selfConsistentScheduledCausalTailModelFailureBudget mdp
            (explicitHighProbabilityBurnin n)) atTop (nhds 0) := by
    exact
      (selfConsistentScheduledCausalTailModelFailureBudget_tendsto_zero mdp).comp
        (by simpa [explicitHighProbabilityBurnin] using
          explicitHighProbabilityScale_tendsto_atTop)
  have hreturn :
      Tendsto
        (fun n => ENNReal.ofReal (explicitHighProbabilityReturnDelta n))
          atTop (nhds 0) := by
    simpa using
      (ENNReal.continuous_ofReal.tendsto 0).comp
        explicitHighProbabilityReturnDelta_tendsto_zero
  simpa [explicitPolynomialPrefixTailModelReturnFailureBudget,
    selfConsistentScheduledNaturalCausalBurninTailModelReturnFailureBudget]
    using htail.add hreturn

/-- The full scheduled average realized-regret envelope vanishes. -/
theorem explicitPolynomialPrefixAverageRealizedBehaviorRegretRate_tendsto_zero
    (mdp : MDP State Action) (varianceProxy : NNReal)
    (baseVisitFloor : Real) :
    Tendsto
      (explicitPolynomialPrefixAverageRealizedBehaviorRegretRate
        mdp varianceProxy baseVisitFloor) atTop (nhds 0) := by
  have hscaleCube :
      Tendsto (fun n => (explicitHighProbabilityScale n : Real) ^ 3)
        atTop atTop :=
    (tendsto_pow_atTop (by norm_num : (3 : Nat) ≠ 0)).comp
      explicitHighProbabilityScale_real_tendsto_atTop
  have hearly :
      Tendsto
        (fun n => (2 * (mdp.horizon : Real)) /
          (explicitHighProbabilityScale n : Real) ^ 3)
        atTop (nhds 0) :=
    tendsto_const_nhds.div_atTop hscaleCube
  have hearly' :
      Tendsto
        (fun n =>
          (2 * (mdp.horizon : Real) *
              (explicitHighProbabilityBurnin n : Real)) /
            (explicitHighProbabilityRounds n : Real))
        atTop (nhds 0) := by
    convert hearly using 1
    funext n
    simp [explicitHighProbabilityBurnin, explicitHighProbabilityRounds,
      div_eq_mul_inv]
    field_simp [ne_of_gt (show (0 : Real) <
      explicitHighProbabilityScale n by
        exact_mod_cast explicitHighProbabilityScale_pos n)]
  have hlog :
      Tendsto
        (fun n =>
          selfConsistentScheduledNaturalCausalLogarithmicAverageIntegratedBehaviorExpectedRegretRate
            mdp (explicitHighProbabilityRounds n))
        atTop (nhds 0) :=
    (selfConsistentScheduledNaturalCausalLogarithmicAverageIntegratedBehaviorExpectedRegretRate_tendsto_zero
      mdp).comp explicitHighProbabilityRounds_tendsto_atTop
  have hreturn :=
    explicitPolynomialPrefixAverageReturnRadius_tendsto_zero
      mdp varianceProxy baseVisitFloor
  have hsum :
      Tendsto
        (fun n =>
          (2 * (mdp.horizon : Real) *
              (explicitHighProbabilityBurnin n : Real)) /
              (explicitHighProbabilityRounds n : Real) +
            (selfConsistentScheduledNaturalCausalLogarithmicAverageIntegratedBehaviorExpectedRegretRate
                mdp (explicitHighProbabilityRounds n) +
              explicitPolynomialPrefixAverageReturnRadius
                mdp varianceProxy baseVisitFloor n))
        atTop (nhds 0) := by
    simpa using hearly'.add (hlog.add hreturn)
  convert hsum using 1
  funext n
  unfold explicitPolynomialPrefixAverageRealizedBehaviorRegretRate
    selfConsistentScheduledNaturalCausalBurninRealizedAverageLogarithmicRate
    selfConsistentScheduledNaturalCausalBurninRealizedCumulativeLogarithmicRate
    selfConsistentScheduledNaturalCausalBurninCumulativeBehaviorExpectedRegretLogarithmicRate
    selfConsistentScheduledNaturalCausalLogarithmicAverageIntegratedBehaviorExpectedRegretRate
    explicitPolynomialPrefixAverageReturnRadius
  ring

/-- Scheduled model-tail/normalized-return union event. -/
noncomputable def explicitPolynomialPrefixTailModelReturnBadEvent
    (mdp : MDP State Action) (initialState : Measure State)
    [IsProbabilityMeasure initialState]
    (rewardSource : mdp.MeanCompatibleRewardKernel)
    (initialTable : DeterministicMarkovPolicyTable mdp)
    (defaultState : State) (varianceProxy : NNReal)
    (baseVisitFloor : Real) (n : Nat) :
    Set (HeterogeneousStochasticEpisodeBatchTrajectory mdp
      (fun t =>
        AdaptiveStochasticEpisodeBatchSource.selfConsistentScheduledEpisodes
          mdp varianceProxy baseVisitFloor t)) :=
  selfConsistentScheduledNaturalCausalBurninTailModelReturnBadEvent mdp
    initialState rewardSource initialTable defaultState varianceProxy
      baseVisitFloor (explicitHighProbabilityBurnin n)
        (explicitHighProbabilityRounds n)
          (explicitHighProbabilityReturnDelta n)

/-- Scheduled one-sided average realized behavior-regret violation set. -/
noncomputable def explicitPolynomialPrefixAverageRealizedBehaviorRegretViolationSet
    (mdp : MDP State Action) (initialState : Measure State)
    [IsProbabilityMeasure initialState]
    (rewardSource : mdp.MeanCompatibleRewardKernel)
    (initialTable : DeterministicMarkovPolicyTable mdp)
    (defaultState : State) (varianceProxy : NNReal)
    (baseVisitFloor : Real) (n : Nat) :
    Set (HeterogeneousStochasticEpisodeBatchTrajectory mdp
      (fun t =>
        AdaptiveStochasticEpisodeBatchSource.selfConsistentScheduledEpisodes
          mdp varianceProxy baseVisitFloor t)) :=
  selfConsistentScheduledNaturalCausalBurninAverageRealizedBehaviorRegretLogarithmicViolationSet
    mdp initialState rewardSource initialTable defaultState varianceProxy
      baseVisitFloor (explicitHighProbabilityBurnin n)
        (explicitHighProbabilityRounds n)
          (explicitHighProbabilityReturnDelta n)

/-
Terminal scheduled-prefix high-probability average realized behavior-regret
consistency certificate.  It packages every fixed-prefix event and pathwise
certificate together with the two vanishing deterministic envelopes.
-/
theorem
    selfConsistentScheduledCausalSource_explicitPolynomialPrefixHighProbabilityAverageRealizedBehaviorRegretConsistency
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
    let event := fun n =>
      explicitPolynomialPrefixTailModelReturnBadEvent mdp initialState
        rewardSource initialTable defaultState varianceProxy baseVisitFloor n
    let averageViolation := fun n =>
      explicitPolynomialPrefixAverageRealizedBehaviorRegretViolationSet mdp
        initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor n
    Tendsto (explicitPolynomialPrefixTailModelReturnFailureBudget mdp)
        atTop (nhds 0) ∧
      Tendsto
        (explicitPolynomialPrefixAverageRealizedBehaviorRegretRate
          mdp varianceProxy baseVisitFloor) atTop (nhds 0) ∧
      (∀ᶠ n in atTop,
        explicitPolynomialPrefixTailModelReturnFailureBudget mdp n < 1) ∧
      forall n,
        MeasurableSet (event n) ∧
        MeasurableSet (averageViolation n) ∧
        source.trajectoryMeasure (event n) <=
          explicitPolynomialPrefixTailModelReturnFailureBudget mdp n ∧
        averageViolation n ⊆ event n ∧
        source.trajectoryMeasure (averageViolation n) <=
          explicitPolynomialPrefixTailModelReturnFailureBudget mdp n ∧
        (explicitPolynomialPrefixTailModelReturnFailureBudget mdp n < 1 ->
          source.trajectoryMeasure (event n) < 1 ∧
          source.trajectoryMeasure (averageViolation n) < 1) ∧
        forall trajectory, trajectory ∉ event n ->
          selfConsistentScheduledNaturalCausalAverageRealizedBehaviorRegretProcess
              mdp initialState rewardSource initialTable defaultState
                varianceProxy baseVisitFloor
                  (explicitHighProbabilityRounds n) trajectory <=
            explicitPolynomialPrefixAverageRealizedBehaviorRegretRate
              mdp varianceProxy baseVisitFloor n := by
  dsimp only
  let source := selfConsistentScheduledCausalSource mdp initialState
    rewardSource initialTable defaultState varianceProxy baseVisitFloor
  let event := fun n =>
    explicitPolynomialPrefixTailModelReturnBadEvent mdp initialState
      rewardSource initialTable defaultState varianceProxy baseVisitFloor n
  let averageViolation := fun n =>
    explicitPolynomialPrefixAverageRealizedBehaviorRegretViolationSet mdp
      initialState rewardSource initialTable defaultState varianceProxy
        baseVisitFloor n
  have hbudget :=
    explicitPolynomialPrefixTailModelReturnFailureBudget_tendsto_zero mdp
  have hrate :=
    explicitPolynomialPrefixAverageRealizedBehaviorRegretRate_tendsto_zero
      mdp varianceProxy baseVisitFloor
  have hnontrivial :
      ∀ᶠ n in atTop,
        explicitPolynomialPrefixTailModelReturnFailureBudget mdp n < 1 :=
    hbudget.eventually_lt_const (by norm_num)
  refine ⟨hbudget, hrate, hnontrivial, ?_⟩
  intro n
  have hcert :=
    selfConsistentScheduledCausalSource_burninTailHighProbabilityLogarithmicCumulativeAverageRealizedBehaviorRegret
      mdp initialState rewardSource varianceProxy hvarianceProxy law
        initialTable defaultState support baseVisitFloor hbaseFloor
          hrewardBound hhorizon hbaseVisitFloor
            (explicitHighProbabilityBurnin n)
            (explicitHighProbabilityRounds n)
            (explicitHighProbabilityBurnin_le_rounds n)
            (explicitHighProbabilityRounds_pos n)
            (explicitHighProbabilityReturnDelta n)
            (explicitHighProbabilityReturnDelta_pos n)
            (explicitHighProbabilityReturnDelta_le_one n)
  dsimp only at hcert
  rcases hcert with
    ⟨heventMeasurable, _hcumulativeMeasurable, haverageMeasurable,
      heventMeasure, _hcumulativeSubset, haverageSubset,
      _hcumulativeMeasure, haverageMeasure, hstrict, hpath⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [event, explicitPolynomialPrefixTailModelReturnBadEvent] using
      heventMeasurable
  · simpa [averageViolation,
      explicitPolynomialPrefixAverageRealizedBehaviorRegretViolationSet] using
      haverageMeasurable
  · simpa [source, event, explicitPolynomialPrefixTailModelReturnBadEvent,
      explicitPolynomialPrefixTailModelReturnFailureBudget] using heventMeasure
  · simpa [averageViolation, event,
      explicitPolynomialPrefixAverageRealizedBehaviorRegretViolationSet,
      explicitPolynomialPrefixTailModelReturnBadEvent] using haverageSubset
  · simpa [source, averageViolation,
      explicitPolynomialPrefixAverageRealizedBehaviorRegretViolationSet,
      explicitPolynomialPrefixTailModelReturnFailureBudget] using haverageMeasure
  · intro hbudgetLt
    have hstrict' := hstrict (by
      simpa [explicitPolynomialPrefixTailModelReturnFailureBudget] using
        hbudgetLt)
    exact ⟨by
      simpa [source, event,
        explicitPolynomialPrefixTailModelReturnBadEvent] using hstrict'.1,
      by
        simpa [source, averageViolation,
          explicitPolynomialPrefixAverageRealizedBehaviorRegretViolationSet]
          using hstrict'.2.2⟩
  · intro trajectory htrajectory
    have hpath' := hpath trajectory (by
      simpa [event, explicitPolynomialPrefixTailModelReturnBadEvent] using
        htrajectory)
    simpa [explicitPolynomialPrefixAverageRealizedBehaviorRegretRate] using
      hpath'.2

end AdaptiveStochasticSampledEmpiricalOptimisticSource

end BanditRLProof.FiniteHorizonRL
