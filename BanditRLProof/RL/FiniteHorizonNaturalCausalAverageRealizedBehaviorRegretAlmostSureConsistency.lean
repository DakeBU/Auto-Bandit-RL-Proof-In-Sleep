import BanditRLProof.RL.FiniteHorizonNaturalCausalAverageRealizedBehaviorRegretAlmostSureExplicitSchedule
import BanditRLProof.RL.FiniteHorizonAdaptiveStochasticRewardSampledEmpiricalOptimisticSelfConsistentCausalCommonSpaceAlmostSureBehaviorExpectedRegretConsistency
import Mathlib.Analysis.Asymptotics.SpecificAsymptotics

/-!
# All-prefix almost-sure natural causal average realized behavior regret

This module strengthens the fourth-power-prefix almost-sure theorem to every
deterministic natural prefix for the same per-batch-normalized,
equal-round-weighted process on the one heterogeneous causal trajectory
measure.

The behavior term is the Cesaro average of the compiled almost-everywhere
successor-policy expected-regret limit. The return term uses the existing
fixed-prefix conditional-sub-Gaussian tail at rounds `n + 1` with summable
share `1 / (n + 2)^2`; first Borel-Cantelli needs no event independence.

This is not an anytime confidence sequence, stopping-time theorem, raw
single-episode process, behavior/recommended-policy equality, minimax rate,
reachability theorem, or complete UCB-VI.
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

/-- Pathwise equal-round average of successor-policy expected regret. -/
noncomputable def selfConsistentScheduledNaturalCausalAverageBehaviorExpectedRegretProcess
    (mdp : MDP State Action) (initialState : Measure State)
    [IsProbabilityMeasure initialState]
    (rewardSource : mdp.MeanCompatibleRewardKernel)
    (initialTable : DeterministicMarkovPolicyTable mdp)
    (defaultState : State) (varianceProxy : NNReal)
    (baseVisitFloor : Real) (rounds : Nat) :
    HeterogeneousStochasticEpisodeBatchTrajectory mdp
        (fun t =>
          AdaptiveStochasticEpisodeBatchSource.selfConsistentScheduledEpisodes
            mdp varianceProxy baseVisitFloor t) -> Real :=
  fun trajectory =>
    selfConsistentScheduledNaturalCausalCumulativeBehaviorExpectedRegretProcess
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor rounds trajectory /
      (rounds : Real)

/-- Cumulative normalized successor-return deviation divided by round count. -/
noncomputable def selfConsistentScheduledNaturalCausalAverageReturnDeviationProcess
    (mdp : MDP State Action) (initialState : Measure State)
    [IsProbabilityMeasure initialState]
    (rewardSource : mdp.MeanCompatibleRewardKernel)
    (initialTable : DeterministicMarkovPolicyTable mdp)
    (defaultState : State) (varianceProxy : NNReal)
    (baseVisitFloor : Real) (rounds : Nat) :
    HeterogeneousStochasticEpisodeBatchTrajectory mdp
        (fun t =>
          AdaptiveStochasticEpisodeBatchSource.selfConsistentScheduledEpisodes
            mdp varianceProxy baseVisitFloor t) -> Real :=
  fun trajectory =>
    selfConsistentScheduledNaturalCausalCumulativeReturnDeviationProcess
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor rounds trajectory /
      (rounds : Real)

/-- Summable confidence share for the return event at prefix `n + 1`. -/
noncomputable def naturalAllPrefixReturnDelta (n : Nat) : Real :=
  1 / (((n + 2 : Nat) : Real) ^ 2)

theorem naturalAllPrefixReturnDelta_pos (n : Nat) :
    0 < naturalAllPrefixReturnDelta n := by
  unfold naturalAllPrefixReturnDelta
  positivity

theorem naturalAllPrefixReturnDelta_le_one (n : Nat) :
    naturalAllPrefixReturnDelta n <= 1 := by
  unfold naturalAllPrefixReturnDelta
  have h : (1 : Real) <= ((n + 2 : Nat) : Real) := by
    exact_mod_cast (show 1 <= n + 2 by omega)
  have hsq : (1 : Real) <= (((n + 2 : Nat) : Real) ^ 2) := by
    nlinarith
  exact (div_le_one (by positivity)).2 hsq

theorem summable_naturalAllPrefixReturnDelta :
    Summable naturalAllPrefixReturnDelta := by
  change Summable (fun n : Nat => 1 / (((n + 2 : Nat) : Real) ^ 2))
  have hp : Summable (fun n : Nat =>
      1 / ((n : Real) ^ 2)) :=
    Real.summable_one_div_nat_pow.mpr (by norm_num)
  have hshift := (summable_nat_add_iff
    (f := fun n : Nat => 1 / ((n : Real) ^ 2)) 2).2 hp
  simpa only using hshift

/-- Fixed-prefix return radius after division by the positive prefix length. -/
noncomputable def naturalAllPrefixAverageReturnConfidenceRadius
    (mdp : MDP State Action) (varianceProxy : NNReal)
    (baseVisitFloor : Real) (n : Nat) : Real :=
  Concentration.subGaussianSumConfidenceRadius
      (selfConsistentScheduledNaturalCausalCumulativeReturnVarianceProxy
        mdp varianceProxy baseVisitFloor (n + 1))
      (naturalAllPrefixReturnDelta n) /
    ((n + 1 : Nat) : Real)

/-- Deterministic square-root envelope for the normalized all-prefix radius. -/
noncomputable def naturalAllPrefixAverageReturnConfidenceEnvelope
    (mdp : MDP State Action) (varianceProxy : NNReal) (n : Nat) : Real :=
  Real.sqrt
    (6 *
      (((mdp.globalReturnDeviationPerEpisodeVarianceProxy
        1 varianceProxy : NNReal) : Real) + 1) *
      ((1 + Real.log ((n + 2 : Nat) : Real)) / ((n + 1 : Nat) : Real)))

/-- The inverse-square confidence share contributes at most three shifted logs. -/
theorem log_two_div_naturalAllPrefixReturnDelta_le (n : Nat) :
    Real.log (2 / naturalAllPrefixReturnDelta n) <=
      3 * (1 + Real.log ((n + 2 : Nat) : Real)) := by
  let s : Real := ((n + 2 : Nat) : Real)
  have hs : 0 < s := by
    dsimp [s]
    positivity
  have hs_one : 1 <= s := by
    dsimp [s]
    exact_mod_cast (show 1 <= n + 2 by omega)
  have hlog_s : 0 <= Real.log s := Real.log_nonneg hs_one
  have hlog_two : Real.log 2 <= 1 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : Real) < 2)
    norm_num at h
    exact h
  have hquotient : 2 / naturalAllPrefixReturnDelta n = 2 * s ^ 2 := by
    unfold naturalAllPrefixReturnDelta
    dsimp [s]
    field_simp
  change Real.log (2 / naturalAllPrefixReturnDelta n) <=
    3 * (1 + Real.log s)
  rw [hquotient, Real.log_mul (by norm_num) (pow_ne_zero 2 hs.ne'),
    Real.log_pow]
  norm_num
  linarith

omit [DecidableEq State] [DecidableEq Action]
    [MeasurableSingletonClass State] [MeasurableSingletonClass Action]
    [Nonempty State] [Nonempty Action] in
theorem naturalAllPrefixAverageReturnConfidenceEnvelope_nonneg
    (mdp : MDP State Action) (varianceProxy : NNReal) (n : Nat) :
    0 <= naturalAllPrefixAverageReturnConfidenceEnvelope mdp varianceProxy n :=
  Real.sqrt_nonneg _

omit [DecidableEq State] [DecidableEq Action]
    [MeasurableSingletonClass State] [MeasurableSingletonClass Action]
    [Nonempty State] [Nonempty Action] in
/-- The normalized fixed-prefix return radius is below its deterministic envelope. -/
theorem naturalAllPrefixAverageReturnConfidenceRadius_le_envelope
    (mdp : MDP State Action) (varianceProxy : NNReal)
    (baseVisitFloor : Real) (n : Nat) :
    naturalAllPrefixAverageReturnConfidenceRadius mdp varianceProxy
        baseVisitFloor n <=
      naturalAllPrefixAverageReturnConfidenceEnvelope mdp varianceProxy n := by
  let r : Real := ((n + 1 : Nat) : Real)
  let s : Real := ((n + 2 : Nat) : Real)
  let C : Real :=
    ((mdp.globalReturnDeviationPerEpisodeVarianceProxy
      1 varianceProxy : NNReal) : Real)
  let L : Real := 1 + Real.log s
  let rawRadius : Real :=
    Concentration.subGaussianSumConfidenceRadius
      (selfConsistentScheduledNaturalCausalCumulativeReturnVarianceProxy
        mdp varianceProxy baseVisitFloor (n + 1))
      (naturalAllPrefixReturnDelta n)
  have hr : 0 < r := by
    dsimp [r]
    positivity
  have hs_one : 1 <= s := by
    dsimp [s]
    exact_mod_cast (show 1 <= n + 2 by omega)
  have hC : 0 <= C := NNReal.coe_nonneg _
  have hL : 0 <= L := by
    dsimp [L]
    have := Real.log_nonneg hs_one
    linarith
  have hproxyNN :=
    selfConsistentScheduledNaturalCausalCumulativeReturnVarianceProxy_le_rounds_mul
      mdp varianceProxy baseVisitFloor (n + 1)
  have hproxyReal := NNReal.coe_le_coe.mpr hproxyNN
  have hproxy :
      ((selfConsistentScheduledNaturalCausalCumulativeReturnVarianceProxy
        mdp varianceProxy baseVisitFloor (n + 1) : NNReal) : Real) <=
        r * C := by
    simpa [r, C] using hproxyReal
  have hlog_nonneg :
      0 <= Real.log (2 / naturalAllPrefixReturnDelta n) := by
    apply Real.log_nonneg
    rw [le_div_iff₀ (naturalAllPrefixReturnDelta_pos n)]
    linarith [naturalAllPrefixReturnDelta_le_one n]
  have hlog_le :
      Real.log (2 / naturalAllPrefixReturnDelta n) <= 3 * L := by
    simpa [L, s] using log_two_div_naturalAllPrefixReturnDelta_le n
  have hraw_nonneg : 0 <= rawRadius :=
    Concentration.subGaussianSumConfidenceRadius_nonneg _ _
  have hraw_sq : rawRadius ^ 2 <= 6 * r * C * L := by
    rw [show rawRadius ^ 2 =
        2 *
          ((selfConsistentScheduledNaturalCausalCumulativeReturnVarianceProxy
            mdp varianceProxy baseVisitFloor (n + 1) : NNReal) : Real) *
          Real.log (2 / naturalAllPrefixReturnDelta n) by
      exact Concentration.subGaussianSumConfidenceRadius_sq _ _
        (naturalAllPrefixReturnDelta_pos n)
        (naturalAllPrefixReturnDelta_le_one n)]
    calc
      2 *
            ((selfConsistentScheduledNaturalCausalCumulativeReturnVarianceProxy
              mdp varianceProxy baseVisitFloor (n + 1) : NNReal) : Real) *
            Real.log (2 / naturalAllPrefixReturnDelta n) <=
          2 * (r * C) * (3 * L) := by
            gcongr
      _ = 6 * r * C * L := by ring
  have hnormalized_nonneg : 0 <= rawRadius / r :=
    div_nonneg hraw_nonneg hr.le
  have hnormalized_sq :
      (rawRadius / r) ^ 2 <= 6 * (C + 1) * (L / r) := by
    rw [div_pow]
    apply (div_le_iff₀ (sq_pos_of_pos hr)).2
    calc
      rawRadius ^ 2 <= 6 * r * C * L := hraw_sq
      _ <= 6 * r * (C + 1) * L := by
        gcongr
        linarith
      _ = 6 * (C + 1) * (L / r) * r ^ 2 := by
        field_simp [hr.ne']
  have henvelope_sq :
      (naturalAllPrefixAverageReturnConfidenceEnvelope mdp varianceProxy n) ^ 2 =
        6 * (C + 1) * (L / r) := by
    change (Real.sqrt (6 * (C + 1) * (L / r))) ^ 2 =
      6 * (C + 1) * (L / r)
    rw [Real.sq_sqrt]
    positivity
  change rawRadius / r <=
    naturalAllPrefixAverageReturnConfidenceEnvelope mdp varianceProxy n
  apply (sq_le_sq₀ hnormalized_nonneg
    (naturalAllPrefixAverageReturnConfidenceEnvelope_nonneg
      mdp varianceProxy n)).mp
  rw [henvelope_sq]
  exact hnormalized_sq

omit [DecidableEq State] [DecidableEq Action]
    [MeasurableSingletonClass State] [MeasurableSingletonClass Action]
    [Nonempty State] [Nonempty Action] in
/-- The deterministic all-prefix return-radius envelope vanishes. -/
theorem naturalAllPrefixAverageReturnConfidenceEnvelope_tendsto_zero
    (mdp : MDP State Action) (varianceProxy : NNReal) :
    Tendsto
      (naturalAllPrefixAverageReturnConfidenceEnvelope mdp varianceProxy)
      atTop (nhds 0) := by
  have hlogShift : Tendsto
      (fun n : Nat =>
        (1 + Real.log ((n + 2 : Nat) : Real)) / ((n + 2 : Nat) : Real))
      atTop (nhds 0) := by
    simpa only using
      (tendsto_add_atTop_iff_nat 2).2
        BanditRLProof.tendsto_one_add_log_natCast_div_natCast_zero
  have hdenom : Tendsto (fun n : Nat => ((n + 1 : Nat) : Real))
      atTop atTop :=
    tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1)
  have hinv : Tendsto (fun n : Nat => 1 / ((n + 1 : Nat) : Real))
      atTop (nhds 0) := tendsto_const_nhds.div_atTop hdenom
  have hratio : Tendsto
      (fun n : Nat => ((n + 2 : Nat) : Real) / ((n + 1 : Nat) : Real))
      atTop (nhds 1) := by
    have hone : Tendsto (fun _ : Nat => (1 : Real)) atTop (nhds 1) :=
      tendsto_const_nhds
    have hadd := hone.add hinv
    convert hadd using 1
    · funext n
      field_simp
      norm_num [Nat.cast_add]
      ring
    · norm_num
  have hshiftedRatio : Tendsto
      (fun n : Nat =>
        (1 + Real.log ((n + 2 : Nat) : Real)) / ((n + 1 : Nat) : Real))
      atTop (nhds 0) := by
    have hmul := hlogShift.mul hratio
    convert hmul using 1
    · funext n
      have hn1 : (0 : Real) < ((n + 1 : Nat) : Real) := by positivity
      have hn2 : (0 : Real) < ((n + 2 : Nat) : Real) := by positivity
      field_simp [hn1.ne', hn2.ne']
    · norm_num
  have hinside : Tendsto
      (fun n : Nat =>
        6 *
          (((mdp.globalReturnDeviationPerEpisodeVarianceProxy
            1 varianceProxy : NNReal) : Real) + 1) *
          ((1 + Real.log ((n + 2 : Nat) : Real)) /
            ((n + 1 : Nat) : Real)))
      atTop (nhds 0) := by
    simpa using tendsto_const_nhds.mul hshiftedRatio
  change Tendsto
    (fun n : Nat => Real.sqrt
      (6 *
        (((mdp.globalReturnDeviationPerEpisodeVarianceProxy
          1 varianceProxy : NNReal) : Real) + 1) *
        ((1 + Real.log ((n + 2 : Nat) : Real)) /
          ((n + 1 : Nat) : Real)))) atTop (nhds 0)
  simpa only [Function.comp_apply, Real.sqrt_zero] using
    (Real.continuous_sqrt.tendsto 0).comp hinside

omit [DecidableEq State] [DecidableEq Action]
    [MeasurableSingletonClass State] [MeasurableSingletonClass Action]
    [Nonempty State] [Nonempty Action] in
/-- The normalized all-prefix return confidence radius vanishes. -/
theorem naturalAllPrefixAverageReturnConfidenceRadius_tendsto_zero
    (mdp : MDP State Action) (varianceProxy : NNReal)
    (baseVisitFloor : Real) :
    Tendsto
      (naturalAllPrefixAverageReturnConfidenceRadius mdp varianceProxy
        baseVisitFloor) atTop (nhds 0) := by
  apply squeeze_zero
  · intro n
    unfold naturalAllPrefixAverageReturnConfidenceRadius
    exact div_nonneg
      (Concentration.subGaussianSumConfidenceRadius_nonneg _ _)
      (by positivity)
  · intro n
    exact naturalAllPrefixAverageReturnConfidenceRadius_le_envelope
      mdp varianceProxy baseVisitFloor n
  · exact naturalAllPrefixAverageReturnConfidenceEnvelope_tendsto_zero
      mdp varianceProxy

/-- Return bad event at positive prefix `n + 1` and inverse-square share. -/
noncomputable def naturalAllPrefixReturnBadEvent
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
  selfConsistentScheduledNaturalCausalCumulativeReturnBadEvent mdp initialState
    rewardSource initialTable defaultState varianceProxy baseVisitFloor
      (n + 1) (naturalAllPrefixReturnDelta n)

/-- The all-prefix shifted return event is measurable. -/
theorem measurableSet_naturalAllPrefixReturnBadEvent
    (mdp : MDP State Action) (initialState : Measure State)
    [IsProbabilityMeasure initialState]
    (rewardSource : mdp.MeanCompatibleRewardKernel)
    (initialTable : DeterministicMarkovPolicyTable mdp)
    (defaultState : State) (varianceProxy : NNReal)
    (baseVisitFloor : Real) (n : Nat) :
    MeasurableSet
      (naturalAllPrefixReturnBadEvent mdp initialState rewardSource
        initialTable defaultState varianceProxy baseVisitFloor n) := by
  simpa [naturalAllPrefixReturnBadEvent] using
    (measurableSet_selfConsistentScheduledNaturalCausalCumulativeReturnBadEvent
      mdp initialState rewardSource initialTable defaultState varianceProxy
        baseVisitFloor (n + 1) (naturalAllPrefixReturnDelta n))

/-- Each shifted return event has probability at most its inverse-square share. -/
theorem selfConsistentScheduledCausalSource_trajectoryMeasure_naturalAllPrefixReturnBadEvent_le
    (mdp : MDP State Action) (initialState : Measure State)
    [IsProbabilityMeasure initialState]
    [StandardBorelSpace State] [StandardBorelSpace Action]
    (rewardSource : mdp.MeanCompatibleRewardKernel)
    (varianceProxy : NNReal)
    (law : rewardSource.UniformSubgaussianRewardLaw varianceProxy)
    (initialTable : DeterministicMarkovPolicyTable mdp)
    (defaultState : State) (baseVisitFloor : Real)
    (hrewardBound : forall state action, |mdp.reward state action| <= 1)
    (hhorizon : 0 < mdp.horizon) (n : Nat) :
    let source := selfConsistentScheduledCausalSource mdp initialState
      rewardSource initialTable defaultState varianceProxy baseVisitFloor
    source.trajectoryMeasure
        (naturalAllPrefixReturnBadEvent mdp initialState rewardSource
          initialTable defaultState varianceProxy baseVisitFloor n) <=
      ENNReal.ofReal (naturalAllPrefixReturnDelta n) := by
  dsimp only
  simpa [naturalAllPrefixReturnBadEvent] using
    (selfConsistentScheduledCausalSource_trajectoryMeasure_naturalCumulativeReturnBadEvent_le
      mdp initialState rewardSource varianceProxy law initialTable defaultState
        baseVisitFloor hrewardBound hhorizon (n + 1) (by omega)
          (naturalAllPrefixReturnDelta n) (naturalAllPrefixReturnDelta_pos n)
            (naturalAllPrefixReturnDelta_le_one n))

/-- The shifted return-event probabilities have finite total mass. -/
theorem tsum_naturalAllPrefixReturnBadEvent_measure_ne_top
    (mdp : MDP State Action) (initialState : Measure State)
    [IsProbabilityMeasure initialState]
    [StandardBorelSpace State] [StandardBorelSpace Action]
    (rewardSource : mdp.MeanCompatibleRewardKernel)
    (varianceProxy : NNReal)
    (law : rewardSource.UniformSubgaussianRewardLaw varianceProxy)
    (initialTable : DeterministicMarkovPolicyTable mdp)
    (defaultState : State) (baseVisitFloor : Real)
    (hrewardBound : forall state action, |mdp.reward state action| <= 1)
    (hhorizon : 0 < mdp.horizon) :
    let source := selfConsistentScheduledCausalSource mdp initialState
      rewardSource initialTable defaultState varianceProxy baseVisitFloor
    (∑' n, source.trajectoryMeasure
      (naturalAllPrefixReturnBadEvent mdp initialState rewardSource
        initialTable defaultState varianceProxy baseVisitFloor n)) ≠ ∞ := by
  dsimp only
  exact ne_top_of_le_ne_top
    summable_naturalAllPrefixReturnDelta.tsum_ofReal_ne_top
    (ENNReal.tsum_le_tsum fun n =>
      selfConsistentScheduledCausalSource_trajectoryMeasure_naturalAllPrefixReturnBadEvent_le
        mdp initialState rewardSource varianceProxy law initialTable defaultState
          baseVisitFloor hrewardBound hhorizon n)

/-- Almost every trajectory eventually avoids all shifted return bad events. -/
theorem ae_eventually_not_mem_naturalAllPrefixReturnBadEvent
    (mdp : MDP State Action) (initialState : Measure State)
    [IsProbabilityMeasure initialState]
    [StandardBorelSpace State] [StandardBorelSpace Action]
    (rewardSource : mdp.MeanCompatibleRewardKernel)
    (varianceProxy : NNReal)
    (law : rewardSource.UniformSubgaussianRewardLaw varianceProxy)
    (initialTable : DeterministicMarkovPolicyTable mdp)
    (defaultState : State) (baseVisitFloor : Real)
    (hrewardBound : forall state action, |mdp.reward state action| <= 1)
    (hhorizon : 0 < mdp.horizon) :
    let source := selfConsistentScheduledCausalSource mdp initialState
      rewardSource initialTable defaultState varianceProxy baseVisitFloor
    ∀ᵐ trajectory ∂source.trajectoryMeasure,
      ∀ᶠ n in atTop,
        trajectory ∉ naturalAllPrefixReturnBadEvent mdp initialState
          rewardSource initialTable defaultState varianceProxy baseVisitFloor n := by
  dsimp only
  apply ae_eventually_notMem
  exact
    tsum_naturalAllPrefixReturnBadEvent_measure_ne_top mdp initialState
      rewardSource varianceProxy law initialTable defaultState baseVisitFloor
        hrewardBound hhorizon

/-- The pathwise behavior expected-regret Cesaro average tends to zero a.e. -/
theorem selfConsistentScheduledCausalSource_naturalAverageBehaviorExpectedRegret_tendstoAlmostEverywhere_zero
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
        (fun rounds =>
          selfConsistentScheduledNaturalCausalAverageBehaviorExpectedRegretProcess
            mdp initialState rewardSource initialTable defaultState
              varianceProxy baseVisitFloor rounds trajectory)
        atTop (nhds 0) := by
  dsimp only
  have hcoordinate :=
    selfConsistentScheduledCausalSource_successorPolicyExpectedRegret_tendstoAlmostEverywhere_zero
      mdp initialState rewardSource varianceProxy hvarianceProxy law initialTable
        defaultState support baseVisitFloor hbaseFloor hrewardBound hhorizon
          hbaseVisitFloor
  filter_upwards [hcoordinate] with trajectory htrajectory
  have hcesaro := htrajectory.cesaro
  simpa [selfConsistentScheduledNaturalCausalAverageBehaviorExpectedRegretProcess,
    selfConsistentScheduledNaturalCausalCumulativeBehaviorExpectedRegretProcess,
    div_eq_mul_inv, mul_comm] using hcesaro

/-- The equal-round normalized return deviation vanishes on almost every trajectory. -/
theorem selfConsistentScheduledCausalSource_naturalAverageReturnDeviation_tendstoAlmostEverywhere_zero
    (mdp : MDP State Action) (initialState : Measure State)
    [IsProbabilityMeasure initialState]
    [StandardBorelSpace State] [StandardBorelSpace Action]
    (rewardSource : mdp.MeanCompatibleRewardKernel)
    (varianceProxy : NNReal)
    (law : rewardSource.UniformSubgaussianRewardLaw varianceProxy)
    (initialTable : DeterministicMarkovPolicyTable mdp)
    (defaultState : State) (baseVisitFloor : Real)
    (hrewardBound : forall state action, |mdp.reward state action| <= 1)
    (hhorizon : 0 < mdp.horizon) :
    let source := selfConsistentScheduledCausalSource mdp initialState
      rewardSource initialTable defaultState varianceProxy baseVisitFloor
    ∀ᵐ trajectory ∂source.trajectoryMeasure,
      Tendsto
        (fun rounds =>
          selfConsistentScheduledNaturalCausalAverageReturnDeviationProcess
            mdp initialState rewardSource initialTable defaultState
              varianceProxy baseVisitFloor rounds trajectory)
        atTop (nhds 0) := by
  dsimp only
  have hgood :=
    ae_eventually_not_mem_naturalAllPrefixReturnBadEvent
      mdp initialState rewardSource varianceProxy law initialTable defaultState
        baseVisitFloor hrewardBound hhorizon
  filter_upwards [hgood] with trajectory htrajectory
  have hshifted : Tendsto
      (fun n =>
        selfConsistentScheduledNaturalCausalAverageReturnDeviationProcess
          mdp initialState rewardSource initialTable defaultState varianceProxy
            baseVisitFloor (n + 1) trajectory)
      atTop (nhds 0) := by
    rw [Metric.tendsto_atTop]
    intro epsilon hepsilon
    have hradiusSmall : ∀ᶠ n in atTop,
        naturalAllPrefixAverageReturnConfidenceRadius mdp varianceProxy
          baseVisitFloor n < epsilon :=
      (tendsto_order.1
        (naturalAllPrefixAverageReturnConfidenceRadius_tendsto_zero
          mdp varianceProxy baseVisitFloor)).2 epsilon hepsilon
    exact eventually_atTop.1 (by
      filter_upwards [htrajectory, hradiusSmall] with n hnotEvent hradius
      have hraw :
          |selfConsistentScheduledNaturalCausalCumulativeReturnDeviationProcess
            mdp initialState rewardSource initialTable defaultState varianceProxy
              baseVisitFloor (n + 1) trajectory| <
            Concentration.subGaussianSumConfidenceRadius
              (selfConsistentScheduledNaturalCausalCumulativeReturnVarianceProxy
                mdp varianceProxy baseVisitFloor (n + 1))
              (naturalAllPrefixReturnDelta n) := by
        exact lt_of_not_ge (by
          simpa [naturalAllPrefixReturnBadEvent,
            selfConsistentScheduledNaturalCausalCumulativeReturnBadEvent]
            using hnotEvent)
      have hrounds : (0 : Real) < ((n + 1 : Nat) : Real) := by positivity
      have hnormalized :
          |selfConsistentScheduledNaturalCausalAverageReturnDeviationProcess
            mdp initialState rewardSource initialTable defaultState varianceProxy
              baseVisitFloor (n + 1) trajectory| <
            naturalAllPrefixAverageReturnConfidenceRadius mdp varianceProxy
              baseVisitFloor n := by
        unfold selfConsistentScheduledNaturalCausalAverageReturnDeviationProcess
          naturalAllPrefixAverageReturnConfidenceRadius
        rw [abs_div, abs_of_pos hrounds]
        exact div_lt_div_of_pos_right hraw hrounds
      simpa [Real.dist_eq] using lt_trans hnormalized hradius)
  exact (tendsto_add_atTop_iff_nat 1).1 hshifted

/-
Terminal route theorem. The Cesaro and return-deviation limits are intersected
on the same dependent causal trajectory measure. First Borel-Cantelli was used
without independence; the conclusion ranges over every deterministic prefix.
-/
/-- All-prefix natural average realized behavior regret converges almost surely. -/
theorem selfConsistentScheduledCausalSource_naturalAverageRealizedBehaviorRegret_tendstoAlmostEverywhere_zero
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
    (forall rounds,
      Measurable
        (selfConsistentScheduledNaturalCausalAverageRealizedBehaviorRegretProcess
          mdp initialState rewardSource initialTable defaultState varianceProxy
            baseVisitFloor rounds)) ∧
      ∀ᵐ trajectory ∂source.trajectoryMeasure,
        Tendsto
          (fun rounds =>
            selfConsistentScheduledNaturalCausalAverageRealizedBehaviorRegretProcess
              mdp initialState rewardSource initialTable defaultState
                varianceProxy baseVisitFloor rounds trajectory)
          atTop (nhds 0) := by
  dsimp only
  refine ⟨fun rounds =>
    measurable_selfConsistentScheduledNaturalCausalAverageRealizedBehaviorRegretProcess
      mdp initialState rewardSource initialTable defaultState varianceProxy
        baseVisitFloor rounds, ?_⟩
  have hbehavior :=
    selfConsistentScheduledCausalSource_naturalAverageBehaviorExpectedRegret_tendstoAlmostEverywhere_zero
      mdp initialState rewardSource varianceProxy hvarianceProxy law initialTable
        defaultState support baseVisitFloor hbaseFloor hrewardBound hhorizon
          hbaseVisitFloor
  have hreturn :=
    selfConsistentScheduledCausalSource_naturalAverageReturnDeviation_tendstoAlmostEverywhere_zero
      mdp initialState rewardSource varianceProxy law initialTable defaultState
        baseVisitFloor hrewardBound hhorizon
  filter_upwards [hbehavior, hreturn] with trajectory htrajectoryBehavior htrajectoryReturn
  have hprocess :
      (fun rounds =>
        selfConsistentScheduledNaturalCausalAverageRealizedBehaviorRegretProcess
          mdp initialState rewardSource initialTable defaultState varianceProxy
            baseVisitFloor rounds trajectory) =
        (fun rounds =>
          selfConsistentScheduledNaturalCausalAverageBehaviorExpectedRegretProcess
              mdp initialState rewardSource initialTable defaultState
                varianceProxy baseVisitFloor rounds trajectory -
            selfConsistentScheduledNaturalCausalAverageReturnDeviationProcess
              mdp initialState rewardSource initialTable defaultState
                varianceProxy baseVisitFloor rounds trajectory) := by
    funext rounds
    rw [selfConsistentScheduledNaturalCausalAverageRealizedBehaviorRegretProcess_eq_expected_sub_deviation]
    unfold selfConsistentScheduledNaturalCausalAverageBehaviorExpectedRegretProcess
      selfConsistentScheduledNaturalCausalAverageReturnDeviationProcess
    exact sub_div _ _ _
  rw [hprocess]
  simpa using htrajectoryBehavior.sub htrajectoryReturn

end AdaptiveStochasticSampledEmpiricalOptimisticSource

end BanditRLProof.FiniteHorizonRL
