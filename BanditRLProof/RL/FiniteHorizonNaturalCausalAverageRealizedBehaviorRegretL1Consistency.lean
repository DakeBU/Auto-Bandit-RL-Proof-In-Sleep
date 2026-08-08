import BanditRLProof.RL.FiniteHorizonNaturalCausalRealizedBehaviorRegretInMeasureExplicitSchedule

/-!
# All-prefix L1 consistency for natural causal average realized behavior regret

This module controls the exact natural process which first normalizes every
successor batch by its own positive episode count and then weights rounds
equally. It is not the total-episode-mass-weighted process from the earlier L1
route. The argument exposes the cumulative normalized-return MGF, obtains a
first-moment inverse-square-root bound, and combines it with the compiled
logarithmic behavior expected-regret rate.
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
    [MeasurableSingletonClass State] [MeasurableSingletonClass Action] in
/-- The natural normalized successor-return sum has one global sub-Gaussian MGF. -/
theorem trajectoryMeasure_naturalCumulativeSuccessorAverageReturnDeviation_hasSubgaussianMGF
    {mdp : MDP State Action} {initialState : Measure State}
    [IsProbabilityMeasure initialState] {episodes : Nat -> Nat}
    [StandardBorelSpace State] [StandardBorelSpace Action]
    [forall n, StandardBorelSpace
      (HeterogeneousStochasticEpisodeBatchPrefix mdp episodes n)]
    [forall n, Nonempty
      (HeterogeneousStochasticEpisodeBatchPrefix mdp episodes n)]
    [forall n, StandardBorelSpace
      (StochasticEpisodeBatch mdp (episodes n))]
    [forall n, Nonempty (StochasticEpisodeBatch mdp (episodes n))]
    [StandardBorelSpace
      (HeterogeneousStochasticEpisodeBatchTrajectory mdp episodes)]
    (source : HeterogeneousAdaptiveStochasticEpisodeBatchSource
      mdp initialState episodes) [source.GlobalReturnMeasurability]
    (rounds : Nat) (rewardBound rewardVarianceProxy : NNReal)
    (hrewardBound : forall state action,
      |mdp.reward state action| <= (rewardBound : Real))
    (law : source.rewardSource.UniformSubgaussianRewardLaw
      rewardVarianceProxy) :
    HasSubgaussianMGF
      (source.naturalCumulativeSuccessorAverageReturnDeviation rounds)
      (naturalCumulativeSuccessorAverageReturnVarianceProxy mdp episodes rounds
        rewardBound rewardVarianceProxy)
      source.trajectoryMeasure := by
  let F := Filtration.piLE
    (X := fun n : Nat => StochasticEpisodeBatch mdp (episodes n))
  let cY : Nat -> NNReal := fun t =>
    naturalSuccessorAverageReturnVarianceProxyAt mdp episodes t
      rewardBound rewardVarianceProxy
  have hadapted : StronglyAdapted F
      source.naturalSuccessorAverageReturnDeviationIncrement := by
    simpa [F] using
      source.naturalSuccessorAverageReturnDeviationIncrement_stronglyAdapted_piLE
  have hzero : HasSubgaussianMGF
      (source.naturalSuccessorAverageReturnDeviationIncrement 0) (cY 0)
      source.trajectoryMeasure := by
    change HasSubgaussianMGF (fun _ => 0) 0 source.trajectoryMeasure
    exact HasSubgaussianMGF.fun_zero
  have hsucc : forall i, i < (rounds + 1) - 1 ->
      HasCondSubgaussianMGF
        (F i) (F.le i)
        (source.naturalSuccessorAverageReturnDeviationIncrement (i + 1))
        (cY (i + 1)) source.trajectoryMeasure := by
    intro i _hi
    simpa [F, cY] using
      source.naturalSuccessorAverageReturnDeviationIncrement_succ_hasCondSubgaussianMGF
        i rewardBound rewardVarianceProxy hrewardBound law
  simpa [naturalCumulativeSuccessorAverageReturnVarianceProxy,
    naturalCumulativeSuccessorAverageReturnDeviation, cY] using
    (HasSubgaussianMGF.sum_of_hasCondSubgaussianMGF
      hadapted hzero (rounds + 1) hsucc)

end HeterogeneousAdaptiveStochasticEpisodeBatchSource

namespace AdaptiveStochasticSampledEmpiricalOptimisticSource

/-- The self-consistent natural cumulative normalized-return deviation has a global MGF. -/
theorem selfConsistentScheduledNaturalCausalCumulativeReturnDeviationProcess_hasSubgaussianMGF
    (mdp : MDP State Action) (initialState : Measure State)
    [IsProbabilityMeasure initialState]
    [StandardBorelSpace State] [StandardBorelSpace Action]
    (rewardSource : mdp.MeanCompatibleRewardKernel)
    (varianceProxy : NNReal)
    (law : rewardSource.UniformSubgaussianRewardLaw varianceProxy)
    (initialTable : DeterministicMarkovPolicyTable mdp)
    (defaultState : State) (baseVisitFloor : Real)
    (hrewardBound : forall state action, |mdp.reward state action| <= 1)
    (rounds : Nat) :
    HasSubgaussianMGF
      (selfConsistentScheduledNaturalCausalCumulativeReturnDeviationProcess mdp
        initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor rounds)
      (selfConsistentScheduledNaturalCausalCumulativeReturnVarianceProxy mdp
        varianceProxy baseVisitFloor rounds)
      (selfConsistentScheduledCausalSource mdp initialState rewardSource
        initialTable defaultState varianceProxy baseVisitFloor).trajectoryMeasure := by
  let source := selfConsistentScheduledCausalSource mdp initialState
    rewardSource initialTable defaultState varianceProxy baseVisitFloor
  letI : source.GlobalReturnMeasurability := by
    dsimp [source, selfConsistentScheduledCausalSource]
    infer_instance
  have hrewardBoundNN : forall state action,
      |mdp.reward state action| <= ((1 : NNReal) : Real) := by
    simpa using hrewardBound
  simpa [source, selfConsistentScheduledCausalSource,
    selfConsistentScheduledNaturalCausalCumulativeReturnDeviationProcess,
    selfConsistentScheduledNaturalCausalCumulativeReturnVarianceProxy] using
    (source.trajectoryMeasure_naturalCumulativeSuccessorAverageReturnDeviation_hasSubgaussianMGF
      rounds 1 varianceProxy hrewardBoundNN (by
        simpa [source, selfConsistentScheduledCausalSource] using law))

/-- First-moment envelope for the round-normalized cumulative return deviation. -/
noncomputable def selfConsistentScheduledNaturalCausalAverageReturnFirstMomentBound
    (mdp : MDP State Action) (varianceProxy : NNReal)
    (baseVisitFloor : Real) (rounds : Nat) : Real :=
  (2 * Real.sqrt
      (selfConsistentScheduledNaturalCausalCumulativeReturnVarianceProxy mdp
        varianceProxy baseVisitFloor rounds : Real) *
      Real.exp (1 / 2 : Real)) /
    (rounds : Real)

/-- Coarser inverse-square-root envelope obtained from the linear proxy bound. -/
noncomputable def selfConsistentScheduledNaturalCausalAverageReturnInverseSqrtEnvelope
    (mdp : MDP State Action) (varianceProxy : NNReal) (rounds : Nat) : Real :=
  (2 * Real.sqrt
      (mdp.globalReturnDeviationPerEpisodeVarianceProxy 1 varianceProxy : Real) *
      Real.exp (1 / 2 : Real)) /
    Real.sqrt (rounds : Real)

omit [DecidableEq State] [DecidableEq Action]
    [MeasurableSingletonClass State] [MeasurableSingletonClass Action]
    [Nonempty State] [Nonempty Action] in
/-- The normalized-return first-moment envelope is nonnegative. -/
theorem selfConsistentScheduledNaturalCausalAverageReturnFirstMomentBound_nonneg
    (mdp : MDP State Action) (varianceProxy : NNReal)
    (baseVisitFloor : Real) (rounds : Nat) :
    0 <= selfConsistentScheduledNaturalCausalAverageReturnFirstMomentBound
      mdp varianceProxy baseVisitFloor rounds := by
  unfold selfConsistentScheduledNaturalCausalAverageReturnFirstMomentBound
  positivity

/-- The MGF controls the absolute first moment of the cumulative return deviation. -/
theorem integral_abs_selfConsistentScheduledNaturalCausalCumulativeReturnDeviationProcess_le
    (mdp : MDP State Action) (initialState : Measure State)
    [IsProbabilityMeasure initialState]
    [StandardBorelSpace State] [StandardBorelSpace Action]
    (rewardSource : mdp.MeanCompatibleRewardKernel)
    (varianceProxy : NNReal)
    (law : rewardSource.UniformSubgaussianRewardLaw varianceProxy)
    (initialTable : DeterministicMarkovPolicyTable mdp)
    (defaultState : State) (baseVisitFloor : Real)
    (hrewardBound : forall state action, |mdp.reward state action| <= 1)
    (rounds : Nat) :
    integral
        (selfConsistentScheduledCausalSource mdp initialState rewardSource
          initialTable defaultState varianceProxy baseVisitFloor).trajectoryMeasure
        (fun trajectory =>
          |selfConsistentScheduledNaturalCausalCumulativeReturnDeviationProcess mdp
            initialState rewardSource initialTable defaultState varianceProxy
              baseVisitFloor rounds trajectory|) <=
      2 * Real.sqrt
          (selfConsistentScheduledNaturalCausalCumulativeReturnVarianceProxy mdp
            varianceProxy baseVisitFloor rounds : Real) *
        Real.exp (1 / 2 : Real) := by
  exact
    Concentration.integral_abs_le_two_mul_sqrt_mul_exp_half_of_hasSubgaussianMGF
      _ _ _
      (selfConsistentScheduledNaturalCausalCumulativeReturnDeviationProcess_hasSubgaussianMGF
        mdp initialState rewardSource varianceProxy law initialTable defaultState
          baseVisitFloor hrewardBound rounds)

omit [DecidableEq State] [DecidableEq Action]
    [MeasurableSingletonClass State] [MeasurableSingletonClass Action]
    [Nonempty State] [Nonempty Action] in
/-- The normalized first-moment envelope is bounded by an inverse square root. -/
theorem selfConsistentScheduledNaturalCausalAverageReturnFirstMomentBound_le_inverseSqrtEnvelope
    (mdp : MDP State Action) (varianceProxy : NNReal)
    (baseVisitFloor : Real) (rounds : Nat) (hrounds : 0 < rounds) :
    selfConsistentScheduledNaturalCausalAverageReturnFirstMomentBound
        mdp varianceProxy baseVisitFloor rounds <=
      selfConsistentScheduledNaturalCausalAverageReturnInverseSqrtEnvelope
        mdp varianceProxy rounds := by
  let V : Real :=
    (selfConsistentScheduledNaturalCausalCumulativeReturnVarianceProxy mdp
      varianceProxy baseVisitFloor rounds : Real)
  let C : Real :=
    (mdp.globalReturnDeviationPerEpisodeVarianceProxy 1 varianceProxy : Real)
  let r : Real := (rounds : Real)
  have hr : 0 < r := by
    dsimp [r]
    exact_mod_cast hrounds
  have hproxyNN :=
    selfConsistentScheduledNaturalCausalCumulativeReturnVarianceProxy_le_rounds_mul
      mdp varianceProxy baseVisitFloor rounds
  have hproxy : V <= r * C := by
    exact_mod_cast hproxyNN
  have hsqrt : Real.sqrt V <= Real.sqrt (r * C) :=
    Real.sqrt_le_sqrt hproxy
  rw [Real.sqrt_mul hr.le C] at hsqrt
  have hnum :
      2 * Real.sqrt V * Real.exp (1 / 2 : Real) <=
        2 * (Real.sqrt r * Real.sqrt C) * Real.exp (1 / 2 : Real) := by
    gcongr
  have heq :
      (2 * (Real.sqrt r * Real.sqrt C) * Real.exp (1 / 2 : Real)) / r =
        (2 * Real.sqrt C * Real.exp (1 / 2 : Real)) / Real.sqrt r := by
    have hsqrtPos : 0 < Real.sqrt r := Real.sqrt_pos.2 hr
    field_simp [ne_of_gt hr, ne_of_gt hsqrtPos]
    rw [Real.sq_sqrt hr.le]
    ring
  unfold selfConsistentScheduledNaturalCausalAverageReturnFirstMomentBound
    selfConsistentScheduledNaturalCausalAverageReturnInverseSqrtEnvelope
  change (2 * Real.sqrt V * Real.exp (1 / 2 : Real)) / r <=
    (2 * Real.sqrt C * Real.exp (1 / 2 : Real)) / Real.sqrt r
  rw [← heq]
  exact div_le_div_of_nonneg_right hnum hr.le

omit [DecidableEq State] [DecidableEq Action]
    [MeasurableSingletonClass State] [MeasurableSingletonClass Action]
    [Nonempty State] [Nonempty Action] in
/-- The deterministic inverse-square-root return envelope tends to zero. -/
theorem selfConsistentScheduledNaturalCausalAverageReturnInverseSqrtEnvelope_tendsto_zero
    (mdp : MDP State Action) (varianceProxy : NNReal) :
    Tendsto
      (selfConsistentScheduledNaturalCausalAverageReturnInverseSqrtEnvelope
        mdp varianceProxy) atTop (nhds 0) := by
  have hrounds : Tendsto (fun rounds : Nat => (rounds : Real)) atTop atTop :=
    tendsto_natCast_atTop_atTop
  have hsqrt : Tendsto (fun rounds : Nat => Real.sqrt (rounds : Real))
      atTop atTop := Real.tendsto_sqrt_atTop.comp hrounds
  simpa [selfConsistentScheduledNaturalCausalAverageReturnInverseSqrtEnvelope] using
    (tendsto_const_nhds.div_atTop hsqrt)

omit [DecidableEq State] [DecidableEq Action]
    [MeasurableSingletonClass State] [MeasurableSingletonClass Action]
    [Nonempty State] [Nonempty Action] in
/-- The exact normalized-return first-moment envelope tends to zero on all prefixes. -/
theorem selfConsistentScheduledNaturalCausalAverageReturnFirstMomentBound_tendsto_zero
    (mdp : MDP State Action) (varianceProxy : NNReal)
    (baseVisitFloor : Real) :
    Tendsto
      (selfConsistentScheduledNaturalCausalAverageReturnFirstMomentBound mdp
        varianceProxy baseVisitFloor) atTop (nhds 0) := by
  apply squeeze_zero'
  · exact Filter.Eventually.of_forall fun rounds =>
      selfConsistentScheduledNaturalCausalAverageReturnFirstMomentBound_nonneg
        mdp varianceProxy baseVisitFloor rounds
  · filter_upwards [eventually_ge_atTop 1] with rounds hrounds
    exact
      selfConsistentScheduledNaturalCausalAverageReturnFirstMomentBound_le_inverseSqrtEnvelope
        mdp varianceProxy baseVisitFloor rounds (by omega)
  · exact
      selfConsistentScheduledNaturalCausalAverageReturnInverseSqrtEnvelope_tendsto_zero
        mdp varianceProxy

/-- The cumulative normalized-return deviation is integrable on every prefix. -/
theorem integrable_selfConsistentScheduledNaturalCausalCumulativeReturnDeviationProcess
    (mdp : MDP State Action) (initialState : Measure State)
    [IsProbabilityMeasure initialState]
    [StandardBorelSpace State] [StandardBorelSpace Action]
    (rewardSource : mdp.MeanCompatibleRewardKernel)
    (varianceProxy : NNReal)
    (law : rewardSource.UniformSubgaussianRewardLaw varianceProxy)
    (initialTable : DeterministicMarkovPolicyTable mdp)
    (defaultState : State) (baseVisitFloor : Real)
    (hrewardBound : forall state action, |mdp.reward state action| <= 1)
    (rounds : Nat) :
    Integrable
      (selfConsistentScheduledNaturalCausalCumulativeReturnDeviationProcess mdp
        initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor rounds)
      (selfConsistentScheduledCausalSource mdp initialState rewardSource
        initialTable defaultState varianceProxy baseVisitFloor).trajectoryMeasure :=
  (selfConsistentScheduledNaturalCausalCumulativeReturnDeviationProcess_hasSubgaussianMGF
    mdp initialState rewardSource varianceProxy law initialTable defaultState
      baseVisitFloor hrewardBound rounds).integrable

/-- The equal-round-weighted natural average realized behavior regret is integrable. -/
theorem integrable_selfConsistentScheduledNaturalCausalAverageRealizedBehaviorRegretProcess
    (mdp : MDP State Action) (initialState : Measure State)
    [IsProbabilityMeasure initialState]
    [StandardBorelSpace State] [StandardBorelSpace Action]
    (rewardSource : mdp.MeanCompatibleRewardKernel)
    (varianceProxy : NNReal)
    (law : rewardSource.UniformSubgaussianRewardLaw varianceProxy)
    (initialTable : DeterministicMarkovPolicyTable mdp)
    (defaultState : State) (baseVisitFloor : Real)
    (hrewardBound : forall state action, |mdp.reward state action| <= 1)
    (rounds : Nat) :
    Integrable
      (selfConsistentScheduledNaturalCausalAverageRealizedBehaviorRegretProcess mdp
        initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor rounds)
      (selfConsistentScheduledCausalSource mdp initialState rewardSource
        initialTable defaultState varianceProxy baseVisitFloor).trajectoryMeasure := by
  let mu := (selfConsistentScheduledCausalSource mdp initialState rewardSource
    initialTable defaultState varianceProxy baseVisitFloor).trajectoryMeasure
  let expected :=
    selfConsistentScheduledNaturalCausalCumulativeBehaviorExpectedRegretProcess mdp
      initialState rewardSource initialTable defaultState varianceProxy
        baseVisitFloor rounds
  let deviation :=
    selfConsistentScheduledNaturalCausalCumulativeReturnDeviationProcess mdp
      initialState rewardSource initialTable defaultState varianceProxy
        baseVisitFloor rounds
  have hexpected : Integrable expected mu := by
    simpa [expected, mu] using
      integrable_selfConsistentScheduledNaturalCausalCumulativeBehaviorExpectedRegretProcess
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor hrewardBound rounds
  have hdeviation : Integrable deviation mu := by
    simpa [deviation, mu] using
      integrable_selfConsistentScheduledNaturalCausalCumulativeReturnDeviationProcess
        mdp initialState rewardSource varianceProxy law initialTable defaultState
          baseVisitFloor hrewardBound rounds
  have hquotient : Integrable
      (fun trajectory => (expected trajectory - deviation trajectory) /
        (rounds : Real)) mu :=
    (hexpected.sub hdeviation).div_const (rounds : Real)
  exact hquotient.congr (Filter.Eventually.of_forall fun trajectory => by
    exact
      (selfConsistentScheduledNaturalCausalAverageRealizedBehaviorRegretProcess_eq_expected_sub_deviation
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor rounds trajectory).symm)

/-- Expected absolute equal-round-weighted natural average realized behavior regret. -/
noncomputable def selfConsistentScheduledNaturalCausalExpectedAbsoluteAverageRealizedBehaviorRegret
    (mdp : MDP State Action) (initialState : Measure State)
    [IsProbabilityMeasure initialState]
    (rewardSource : mdp.MeanCompatibleRewardKernel)
    (initialTable : DeterministicMarkovPolicyTable mdp)
    (defaultState : State) (varianceProxy : NNReal)
    (baseVisitFloor : Real) (rounds : Nat) : Real :=
  integral
    (selfConsistentScheduledCausalSource mdp initialState rewardSource
      initialTable defaultState varianceProxy baseVisitFloor).trajectoryMeasure
    (fun trajectory =>
      |selfConsistentScheduledNaturalCausalAverageRealizedBehaviorRegretProcess mdp
        initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor rounds trajectory|)

/-- Deterministic all-prefix L1 envelope for the exact average process. -/
noncomputable def selfConsistentScheduledNaturalCausalAverageRealizedBehaviorRegretL1Envelope
    (mdp : MDP State Action) (varianceProxy : NNReal)
    (baseVisitFloor : Real) (rounds : Nat) : Real :=
  selfConsistentScheduledNaturalCausalLogarithmicAverageIntegratedBehaviorExpectedRegretRate
      mdp rounds +
    selfConsistentScheduledNaturalCausalAverageReturnFirstMomentBound mdp
      varianceProxy baseVisitFloor rounds

omit [DecidableEq State] [DecidableEq Action]
    [MeasurableSingletonClass State] [MeasurableSingletonClass Action]
    [Nonempty State] [Nonempty Action] in
/-- The deterministic L1 envelope is nonnegative. -/
theorem selfConsistentScheduledNaturalCausalAverageRealizedBehaviorRegretL1Envelope_nonneg
    (mdp : MDP State Action) (varianceProxy : NNReal)
    (baseVisitFloor : Real) (rounds : Nat) :
    0 <= selfConsistentScheduledNaturalCausalAverageRealizedBehaviorRegretL1Envelope
      mdp varianceProxy baseVisitFloor rounds := by
  exact add_nonneg
    (selfConsistentScheduledNaturalCausalLogarithmicAverageIntegratedBehaviorExpectedRegretRate_nonneg
      mdp rounds)
    (selfConsistentScheduledNaturalCausalAverageReturnFirstMomentBound_nonneg
      mdp varianceProxy baseVisitFloor rounds)

omit [DecidableEq State] [DecidableEq Action]
    [MeasurableSingletonClass State] [MeasurableSingletonClass Action]
    [Nonempty State] [Nonempty Action] in
/-- The deterministic all-prefix L1 envelope tends to zero. -/
theorem selfConsistentScheduledNaturalCausalAverageRealizedBehaviorRegretL1Envelope_tendsto_zero
    (mdp : MDP State Action) (varianceProxy : NNReal)
    (baseVisitFloor : Real) :
    Tendsto
      (selfConsistentScheduledNaturalCausalAverageRealizedBehaviorRegretL1Envelope
        mdp varianceProxy baseVisitFloor) atTop (nhds 0) := by
  simpa [selfConsistentScheduledNaturalCausalAverageRealizedBehaviorRegretL1Envelope]
    using
      (selfConsistentScheduledNaturalCausalLogarithmicAverageIntegratedBehaviorExpectedRegretRate_tendsto_zero
          mdp).add
        (selfConsistentScheduledNaturalCausalAverageReturnFirstMomentBound_tendsto_zero
          mdp varianceProxy baseVisitFloor)

/-- Expected absolute average realized regret is nonnegative. -/
theorem selfConsistentScheduledNaturalCausalExpectedAbsoluteAverageRealizedBehaviorRegret_nonneg
    (mdp : MDP State Action) (initialState : Measure State)
    [IsProbabilityMeasure initialState]
    (rewardSource : mdp.MeanCompatibleRewardKernel)
    (initialTable : DeterministicMarkovPolicyTable mdp)
    (defaultState : State) (varianceProxy : NNReal)
    (baseVisitFloor : Real) (rounds : Nat) :
    0 <= selfConsistentScheduledNaturalCausalExpectedAbsoluteAverageRealizedBehaviorRegret
      mdp initialState rewardSource initialTable defaultState varianceProxy
        baseVisitFloor rounds := by
  unfold selfConsistentScheduledNaturalCausalExpectedAbsoluteAverageRealizedBehaviorRegret
  exact integral_nonneg fun _ => abs_nonneg _

/-- The expected absolute exact average process is bounded by the all-prefix L1 envelope. -/
theorem selfConsistentScheduledNaturalCausalExpectedAbsoluteAverageRealizedBehaviorRegret_le_L1Envelope
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
    selfConsistentScheduledNaturalCausalExpectedAbsoluteAverageRealizedBehaviorRegret
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor rounds <=
      selfConsistentScheduledNaturalCausalAverageRealizedBehaviorRegretL1Envelope
        mdp varianceProxy baseVisitFloor rounds := by
  let mu := (selfConsistentScheduledCausalSource mdp initialState rewardSource
    initialTable defaultState varianceProxy baseVisitFloor).trajectoryMeasure
  let process :=
    selfConsistentScheduledNaturalCausalAverageRealizedBehaviorRegretProcess mdp
      initialState rewardSource initialTable defaultState varianceProxy
        baseVisitFloor rounds
  let expected :=
    selfConsistentScheduledNaturalCausalCumulativeBehaviorExpectedRegretProcess mdp
      initialState rewardSource initialTable defaultState varianceProxy
        baseVisitFloor rounds
  let deviation :=
    selfConsistentScheduledNaturalCausalCumulativeReturnDeviationProcess mdp
      initialState rewardSource initialTable defaultState varianceProxy
        baseVisitFloor rounds
  have hprocess : Integrable process mu := by
    simpa [process, mu] using
      integrable_selfConsistentScheduledNaturalCausalAverageRealizedBehaviorRegretProcess
        mdp initialState rewardSource varianceProxy law initialTable defaultState
          baseVisitFloor hrewardBound rounds
  have hexpected : Integrable expected mu := by
    simpa [expected, mu] using
      integrable_selfConsistentScheduledNaturalCausalCumulativeBehaviorExpectedRegretProcess
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor hrewardBound rounds
  have hdeviation : Integrable deviation mu := by
    simpa [deviation, mu] using
      integrable_selfConsistentScheduledNaturalCausalCumulativeReturnDeviationProcess
        mdp initialState rewardSource varianceProxy law initialTable defaultState
          baseVisitFloor hrewardBound rounds
  have hpoint : forall trajectory,
      |process trajectory| <=
        expected trajectory / (rounds : Real) +
          |deviation trajectory| / (rounds : Real) := by
    intro trajectory
    rw [show process trajectory =
        (expected trajectory - deviation trajectory) / (rounds : Real) by
      exact
        selfConsistentScheduledNaturalCausalAverageRealizedBehaviorRegretProcess_eq_expected_sub_deviation
          mdp initialState rewardSource initialTable defaultState varianceProxy
            baseVisitFloor rounds trajectory]
    have hroundsAbs : |(rounds : Real)| = (rounds : Real) :=
      abs_of_nonneg (Nat.cast_nonneg rounds)
    rw [abs_div, hroundsAbs]
    have hsub : |expected trajectory - deviation trajectory| <=
        expected trajectory + |deviation trajectory| := by
      calc
        |expected trajectory - deviation trajectory| <=
            |expected trajectory| + |deviation trajectory| := abs_sub _ _
        _ = expected trajectory + |deviation trajectory| := by
          rw [abs_of_nonneg
            (selfConsistentScheduledNaturalCausalCumulativeBehaviorExpectedRegretProcess_nonneg
              mdp initialState rewardSource initialTable defaultState varianceProxy
                baseVisitFloor rounds trajectory)]
    calc
      |expected trajectory - deviation trajectory| / (rounds : Real) <=
          (expected trajectory + |deviation trajectory|) / (rounds : Real) :=
        div_le_div_of_nonneg_right hsub (Nat.cast_nonneg rounds)
      _ = expected trajectory / (rounds : Real) +
          |deviation trajectory| / (rounds : Real) := add_div _ _ _
  have hdom : Integrable
      (fun trajectory => expected trajectory / (rounds : Real) +
        |deviation trajectory| / (rounds : Real)) mu :=
    (hexpected.div_const (rounds : Real)).add
      (hdeviation.abs.div_const (rounds : Real))
  have hreturn :=
    integral_abs_selfConsistentScheduledNaturalCausalCumulativeReturnDeviationProcess_le
      mdp initialState rewardSource varianceProxy law initialTable defaultState
        baseVisitFloor hrewardBound rounds
  have hexpectedBound :=
    selfConsistentScheduledNaturalCausalExpectedCumulativeBehaviorRegret_le_logarithmic
      mdp initialState rewardSource varianceProxy hvarianceProxy law initialTable
        defaultState support baseVisitFloor hbaseFloor hrewardBound hhorizon
          hbaseVisitFloor rounds
  change integral mu (fun trajectory => |process trajectory|) <=
    selfConsistentScheduledNaturalCausalLogarithmicAverageIntegratedBehaviorExpectedRegretRate
        mdp rounds +
      selfConsistentScheduledNaturalCausalAverageReturnFirstMomentBound mdp
        varianceProxy baseVisitFloor rounds
  calc
    integral mu (fun trajectory => |process trajectory|) <=
        integral mu (fun trajectory => expected trajectory / (rounds : Real) +
          |deviation trajectory| / (rounds : Real)) :=
      integral_mono hprocess.abs hdom hpoint
    _ = selfConsistentScheduledNaturalCausalExpectedCumulativeBehaviorRegret mdp
            initialState rewardSource initialTable defaultState varianceProxy
              baseVisitFloor rounds / (rounds : Real) +
          integral mu (fun trajectory => |deviation trajectory|) /
            (rounds : Real) := by
      rw [integral_add (hexpected.div_const (rounds : Real))
        (hdeviation.abs.div_const (rounds : Real)), integral_div, integral_div]
      rfl
    _ <= selfConsistentScheduledNaturalCausalLogarithmicCumulativeIntegratedBehaviorExpectedRegretRate
            mdp rounds / (rounds : Real) +
          (2 * Real.sqrt
              (selfConsistentScheduledNaturalCausalCumulativeReturnVarianceProxy mdp
                varianceProxy baseVisitFloor rounds : Real) *
            Real.exp (1 / 2 : Real)) / (rounds : Real) :=
      add_le_add
        (div_le_div_of_nonneg_right hexpectedBound (Nat.cast_nonneg rounds))
        (div_le_div_of_nonneg_right hreturn (Nat.cast_nonneg rounds))
    _ = selfConsistentScheduledNaturalCausalLogarithmicAverageIntegratedBehaviorExpectedRegretRate
            mdp rounds +
          selfConsistentScheduledNaturalCausalAverageReturnFirstMomentBound mdp
            varianceProxy baseVisitFloor rounds := rfl

/-- Expected absolute exact average realized behavior regret tends to zero on all prefixes. -/
theorem selfConsistentScheduledNaturalCausalExpectedAbsoluteAverageRealizedBehaviorRegret_tendsto_zero
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
      (selfConsistentScheduledNaturalCausalExpectedAbsoluteAverageRealizedBehaviorRegret
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor) atTop (nhds 0) := by
  apply squeeze_zero'
  · exact Filter.Eventually.of_forall fun rounds =>
      selfConsistentScheduledNaturalCausalExpectedAbsoluteAverageRealizedBehaviorRegret_nonneg
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor rounds
  · exact Filter.Eventually.of_forall fun rounds =>
      selfConsistentScheduledNaturalCausalExpectedAbsoluteAverageRealizedBehaviorRegret_le_L1Envelope
        mdp initialState rewardSource varianceProxy hvarianceProxy law initialTable
          defaultState support baseVisitFloor hbaseFloor hrewardBound hhorizon
            hbaseVisitFloor rounds
  · exact
      selfConsistentScheduledNaturalCausalAverageRealizedBehaviorRegretL1Envelope_tendsto_zero
        mdp varianceProxy baseVisitFloor

/-- Every exact equal-round average realized-regret coordinate belongs to `L1`. -/
theorem memLp_one_selfConsistentScheduledNaturalCausalAverageRealizedBehaviorRegretProcess
    (mdp : MDP State Action) (initialState : Measure State)
    [IsProbabilityMeasure initialState]
    [StandardBorelSpace State] [StandardBorelSpace Action]
    (rewardSource : mdp.MeanCompatibleRewardKernel)
    (varianceProxy : NNReal)
    (law : rewardSource.UniformSubgaussianRewardLaw varianceProxy)
    (initialTable : DeterministicMarkovPolicyTable mdp)
    (defaultState : State) (baseVisitFloor : Real)
    (hrewardBound : forall state action, |mdp.reward state action| <= 1)
    (rounds : Nat) :
    MemLp
      (selfConsistentScheduledNaturalCausalAverageRealizedBehaviorRegretProcess mdp
        initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor rounds)
      1
      (selfConsistentScheduledCausalSource mdp initialState rewardSource
        initialTable defaultState varianceProxy baseVisitFloor).trajectoryMeasure := by
  rw [memLp_one_iff_integrable]
  exact
    integrable_selfConsistentScheduledNaturalCausalAverageRealizedBehaviorRegretProcess
      mdp initialState rewardSource varianceProxy law initialTable defaultState
        baseVisitFloor hrewardBound rounds

/-- At exponent one, `eLpNorm` is the lifted expected absolute exact average regret. -/
theorem eLpNorm_one_selfConsistentScheduledNaturalCausalAverageRealizedBehaviorRegretProcess_eq
    (mdp : MDP State Action) (initialState : Measure State)
    [IsProbabilityMeasure initialState]
    [StandardBorelSpace State] [StandardBorelSpace Action]
    (rewardSource : mdp.MeanCompatibleRewardKernel)
    (varianceProxy : NNReal)
    (law : rewardSource.UniformSubgaussianRewardLaw varianceProxy)
    (initialTable : DeterministicMarkovPolicyTable mdp)
    (defaultState : State) (baseVisitFloor : Real)
    (hrewardBound : forall state action, |mdp.reward state action| <= 1)
    (rounds : Nat) :
    eLpNorm
        (selfConsistentScheduledNaturalCausalAverageRealizedBehaviorRegretProcess mdp
          initialState rewardSource initialTable defaultState varianceProxy
            baseVisitFloor rounds)
        1
        (selfConsistentScheduledCausalSource mdp initialState rewardSource
          initialTable defaultState varianceProxy baseVisitFloor).trajectoryMeasure =
      ENNReal.ofReal
        (selfConsistentScheduledNaturalCausalExpectedAbsoluteAverageRealizedBehaviorRegret
          mdp initialState rewardSource initialTable defaultState varianceProxy
            baseVisitFloor rounds) := by
  rw [MemLp.eLpNorm_eq_integral_rpow_norm one_ne_zero ENNReal.one_ne_top
    (memLp_one_selfConsistentScheduledNaturalCausalAverageRealizedBehaviorRegretProcess
      mdp initialState rewardSource varianceProxy law initialTable defaultState
        baseVisitFloor hrewardBound rounds)]
  simp [selfConsistentScheduledNaturalCausalExpectedAbsoluteAverageRealizedBehaviorRegret,
    Real.norm_eq_abs]

/-- The exponent-one extended norm of the exact average process tends to zero. -/
theorem eLpNorm_one_selfConsistentScheduledNaturalCausalAverageRealizedBehaviorRegretProcess_tendsto_zero
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
      (fun rounds => eLpNorm
        (selfConsistentScheduledNaturalCausalAverageRealizedBehaviorRegretProcess mdp
          initialState rewardSource initialTable defaultState varianceProxy
            baseVisitFloor rounds)
        1
        (selfConsistentScheduledCausalSource mdp initialState rewardSource
          initialTable defaultState varianceProxy baseVisitFloor).trajectoryMeasure)
      atTop (nhds 0) := by
  have hexpected :=
    selfConsistentScheduledNaturalCausalExpectedAbsoluteAverageRealizedBehaviorRegret_tendsto_zero
      mdp initialState rewardSource varianceProxy hvarianceProxy law initialTable
        defaultState support baseVisitFloor hbaseFloor hrewardBound hhorizon
          hbaseVisitFloor
  have hofReal := (ENNReal.continuous_ofReal.tendsto 0).comp hexpected
  simpa only [ENNReal.ofReal_zero,
    eLpNorm_one_selfConsistentScheduledNaturalCausalAverageRealizedBehaviorRegretProcess_eq
      mdp initialState rewardSource varianceProxy law initialTable defaultState
        baseVisitFloor hrewardBound] using hofReal

/-- The exponent-one norm of the difference from zero tends to zero. -/
theorem eLpNorm_one_selfConsistentScheduledNaturalCausalAverageRealizedBehaviorRegretProcess_sub_zero_tendsto_zero
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
      (fun rounds => eLpNorm
        (selfConsistentScheduledNaturalCausalAverageRealizedBehaviorRegretProcess mdp
            initialState rewardSource initialTable defaultState varianceProxy
              baseVisitFloor rounds -
          (fun _ => 0))
        1
        (selfConsistentScheduledCausalSource mdp initialState rewardSource
          initialTable defaultState varianceProxy baseVisitFloor).trajectoryMeasure)
      atTop (nhds 0) := by
  have h :=
    eLpNorm_one_selfConsistentScheduledNaturalCausalAverageRealizedBehaviorRegretProcess_tendsto_zero
      mdp initialState rewardSource varianceProxy hvarianceProxy law initialTable
        defaultState support baseVisitFloor hbaseFloor hrewardBound hhorizon
          hbaseVisitFloor
  convert h using 1
  funext rounds
  apply eLpNorm_congr_ae
  exact Filter.Eventually.of_forall fun trajectory => by simp

/-- The exact equal-round average realized behavior regret as an `Lp Real 1` value. -/
noncomputable def selfConsistentScheduledNaturalCausalAverageRealizedBehaviorRegretLp
    (mdp : MDP State Action) (initialState : Measure State)
    [IsProbabilityMeasure initialState]
    [StandardBorelSpace State] [StandardBorelSpace Action]
    (rewardSource : mdp.MeanCompatibleRewardKernel)
    (varianceProxy : NNReal)
    (law : rewardSource.UniformSubgaussianRewardLaw varianceProxy)
    (initialTable : DeterministicMarkovPolicyTable mdp)
    (defaultState : State) (baseVisitFloor : Real)
    (hrewardBound : forall state action, |mdp.reward state action| <= 1)
    (rounds : Nat) :
    Lp Real 1
      (selfConsistentScheduledCausalSource mdp initialState rewardSource
        initialTable defaultState varianceProxy baseVisitFloor).trajectoryMeasure :=
  (memLp_one_selfConsistentScheduledNaturalCausalAverageRealizedBehaviorRegretProcess
    mdp initialState rewardSource varianceProxy law initialTable defaultState
      baseVisitFloor hrewardBound rounds).toLp
    (selfConsistentScheduledNaturalCausalAverageRealizedBehaviorRegretProcess mdp
      initialState rewardSource initialTable defaultState varianceProxy
        baseVisitFloor rounds)

/-- The named `Lp` coordinate represents the exact average process a.e. -/
theorem selfConsistentScheduledNaturalCausalAverageRealizedBehaviorRegretLp_coeFn_ae_eq
    (mdp : MDP State Action) (initialState : Measure State)
    [IsProbabilityMeasure initialState]
    [StandardBorelSpace State] [StandardBorelSpace Action]
    (rewardSource : mdp.MeanCompatibleRewardKernel)
    (varianceProxy : NNReal)
    (law : rewardSource.UniformSubgaussianRewardLaw varianceProxy)
    (initialTable : DeterministicMarkovPolicyTable mdp)
    (defaultState : State) (baseVisitFloor : Real)
    (hrewardBound : forall state action, |mdp.reward state action| <= 1)
    (rounds : Nat) :
    (selfConsistentScheduledNaturalCausalAverageRealizedBehaviorRegretLp mdp
        initialState rewardSource varianceProxy law initialTable defaultState
          baseVisitFloor hrewardBound rounds :
      HeterogeneousStochasticEpisodeBatchTrajectory mdp
        (fun t =>
          AdaptiveStochasticEpisodeBatchSource.selfConsistentScheduledEpisodes
            mdp varianceProxy baseVisitFloor t) -> Real) =ᵐ[
      (selfConsistentScheduledCausalSource mdp initialState rewardSource
        initialTable defaultState varianceProxy baseVisitFloor).trajectoryMeasure]
      selfConsistentScheduledNaturalCausalAverageRealizedBehaviorRegretProcess mdp
        initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor rounds := by
  exact
    (memLp_one_selfConsistentScheduledNaturalCausalAverageRealizedBehaviorRegretProcess
      mdp initialState rewardSource varianceProxy law initialTable defaultState
        baseVisitFloor hrewardBound rounds).coeFn_toLp

/-- The named exact average `Lp Real 1` process converges to zero. -/
theorem selfConsistentScheduledNaturalCausalAverageRealizedBehaviorRegretLp_tendsto_zero
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
      (selfConsistentScheduledNaturalCausalAverageRealizedBehaviorRegretLp mdp
        initialState rewardSource varianceProxy law initialTable defaultState
          baseVisitFloor hrewardBound)
      atTop (nhds 0) := by
  let source := selfConsistentScheduledCausalSource mdp initialState
    rewardSource initialTable defaultState varianceProxy baseVisitFloor
  let process := fun rounds =>
    selfConsistentScheduledNaturalCausalAverageRealizedBehaviorRegretProcess mdp
      initialState rewardSource initialTable defaultState varianceProxy
        baseVisitFloor rounds
  have hmem : forall rounds, MemLp (process rounds) 1 source.trajectoryMeasure :=
    fun rounds =>
      memLp_one_selfConsistentScheduledNaturalCausalAverageRealizedBehaviorRegretProcess
        mdp initialState rewardSource varianceProxy law initialTable defaultState
          baseVisitFloor hrewardBound rounds
  have hzero : MemLp
      (fun _ : HeterogeneousStochasticEpisodeBatchTrajectory mdp
        (fun t =>
          AdaptiveStochasticEpisodeBatchSource.selfConsistentScheduledEpisodes
            mdp varianceProxy baseVisitFloor t) => (0 : Real))
      1 source.trajectoryMeasure := MemLp.zero'
  have hnorm :=
    eLpNorm_one_selfConsistentScheduledNaturalCausalAverageRealizedBehaviorRegretProcess_sub_zero_tendsto_zero
      mdp initialState rewardSource varianceProxy hvarianceProxy law initialTable
        defaultState support baseVisitFloor hbaseFloor hrewardBound hhorizon
          hbaseVisitFloor
  have hLp :=
    (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' process hmem (fun _ => (0 : Real))
      hzero).2 (by simpa [process, source] using hnorm)
  simpa [selfConsistentScheduledNaturalCausalAverageRealizedBehaviorRegretLp,
    process, source] using hLp

/-
Terminal all-prefix L1 theorem for the exact per-batch-normalized,
equal-round-weighted natural realized behavior-regret process.
-/
theorem selfConsistentScheduledCausalSource_naturalAverageRealizedBehaviorRegret_allPrefix_L1_tendsto_zero
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
    let process :=
      selfConsistentScheduledNaturalCausalAverageRealizedBehaviorRegretProcess mdp
        initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor
    (forall rounds, Integrable (process rounds) source.trajectoryMeasure) /\
    (forall rounds, MemLp (process rounds) 1 source.trajectoryMeasure) /\
    (forall rounds,
      selfConsistentScheduledNaturalCausalExpectedAbsoluteAverageRealizedBehaviorRegret
          mdp initialState rewardSource initialTable defaultState varianceProxy
            baseVisitFloor rounds <=
        selfConsistentScheduledNaturalCausalAverageRealizedBehaviorRegretL1Envelope
          mdp varianceProxy baseVisitFloor rounds) /\
    Tendsto
      (selfConsistentScheduledNaturalCausalExpectedAbsoluteAverageRealizedBehaviorRegret
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor) atTop (nhds 0) /\
    (forall rounds, eLpNorm (process rounds) 1 source.trajectoryMeasure =
      ENNReal.ofReal
        (selfConsistentScheduledNaturalCausalExpectedAbsoluteAverageRealizedBehaviorRegret
          mdp initialState rewardSource initialTable defaultState varianceProxy
            baseVisitFloor rounds)) /\
    Tendsto
      (fun rounds => eLpNorm (process rounds - (fun _ => 0)) 1
        source.trajectoryMeasure) atTop (nhds 0) /\
    Tendsto
      (selfConsistentScheduledNaturalCausalAverageRealizedBehaviorRegretLp mdp
        initialState rewardSource varianceProxy law initialTable defaultState
          baseVisitFloor hrewardBound) atTop (nhds 0) /\
    TendstoInMeasure source.trajectoryMeasure process atTop (fun _ => 0) := by
  dsimp only
  let source := selfConsistentScheduledCausalSource mdp initialState
    rewardSource initialTable defaultState varianceProxy baseVisitFloor
  let process :=
    selfConsistentScheduledNaturalCausalAverageRealizedBehaviorRegretProcess mdp
      initialState rewardSource initialTable defaultState varianceProxy
        baseVisitFloor
  have hmem := fun rounds =>
    memLp_one_selfConsistentScheduledNaturalCausalAverageRealizedBehaviorRegretProcess
      mdp initialState rewardSource varianceProxy law initialTable defaultState
        baseVisitFloor hrewardBound rounds
  have hnorm :=
    eLpNorm_one_selfConsistentScheduledNaturalCausalAverageRealizedBehaviorRegretProcess_sub_zero_tendsto_zero
      mdp initialState rewardSource varianceProxy hvarianceProxy law initialTable
        defaultState support baseVisitFloor hbaseFloor hrewardBound hhorizon
          hbaseVisitFloor
  refine ⟨fun rounds =>
      integrable_selfConsistentScheduledNaturalCausalAverageRealizedBehaviorRegretProcess
        mdp initialState rewardSource varianceProxy law initialTable defaultState
          baseVisitFloor hrewardBound rounds,
    hmem,
    fun rounds =>
      selfConsistentScheduledNaturalCausalExpectedAbsoluteAverageRealizedBehaviorRegret_le_L1Envelope
        mdp initialState rewardSource varianceProxy hvarianceProxy law initialTable
          defaultState support baseVisitFloor hbaseFloor hrewardBound hhorizon
            hbaseVisitFloor rounds,
    selfConsistentScheduledNaturalCausalExpectedAbsoluteAverageRealizedBehaviorRegret_tendsto_zero
      mdp initialState rewardSource varianceProxy hvarianceProxy law initialTable
        defaultState support baseVisitFloor hbaseFloor hrewardBound hhorizon
          hbaseVisitFloor,
    fun rounds =>
      eLpNorm_one_selfConsistentScheduledNaturalCausalAverageRealizedBehaviorRegretProcess_eq
        mdp initialState rewardSource varianceProxy law initialTable defaultState
          baseVisitFloor hrewardBound rounds,
    hnorm,
    selfConsistentScheduledNaturalCausalAverageRealizedBehaviorRegretLp_tendsto_zero
      mdp initialState rewardSource varianceProxy hvarianceProxy law initialTable
        defaultState support baseVisitFloor hbaseFloor hrewardBound hhorizon
          hbaseVisitFloor,
    ?_⟩
  exact tendstoInMeasure_of_tendsto_eLpNorm one_ne_zero
    (fun rounds => (hmem rounds).aestronglyMeasurable)
    (by fun_prop) (by simpa [process, source] using hnorm)

end AdaptiveStochasticSampledEmpiricalOptimisticSource

end BanditRLProof.FiniteHorizonRL
