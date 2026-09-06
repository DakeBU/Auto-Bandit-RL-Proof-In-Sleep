import BanditRLProof.RL.FiniteHorizonNaturalCausalReciprocalThresholdCappedDoubleLinearRawWindowFirstPassageVanishingDelayProbabilityAndL1Consistency
import Mathlib.Analysis.PSeries

open Filter MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal ProbabilityTheory Topology

namespace BanditRLProof.FiniteHorizonRL

universe u v

variable {State : Type u} {Action : Type v}
    [MeasurableSpace State] [MeasurableSpace Action]
    [Fintype State] [Fintype Action]
    [DecidableEq State] [DecidableEq Action]
    [MeasurableSingletonClass State] [MeasurableSingletonClass Action]
    [Nonempty State] [Nonempty Action]

namespace AdaptiveStochasticSampledEmpiricalOptimisticSource

/-!
This theorem route slows the moving first-passage threshold from `1/(n+1)`
to `1/sqrt(n+1)`. Dividing the compiled inverse-cubic plus inverse-square L1
envelope by that threshold gives shifted p-series with exponents `5/2` and
`3/2`. Their summability permits first Borel-Cantelli and an almost-sure
eventual exact base-stop conclusion. No independence or optional-stopping
argument is used.
-/

/-- Inverse-square-root threshold `1/sqrt(n+1)` for first passage. -/
noncomputable def
    selfConsistentScheduledNaturalCausalInverseSqrtFirstPassageThreshold
    (scheduleIndex : Nat) : Real :=
  1 / Real.sqrt (explicitHighProbabilityScale scheduleIndex : Real)

/-- Every inverse-square-root first-passage threshold is positive. -/
theorem
    selfConsistentScheduledNaturalCausalInverseSqrtFirstPassageThreshold_pos
    (scheduleIndex : Nat) :
    0 <
      selfConsistentScheduledNaturalCausalInverseSqrtFirstPassageThreshold
        scheduleIndex := by
  unfold selfConsistentScheduledNaturalCausalInverseSqrtFirstPassageThreshold
  exact one_div_pos.mpr (Real.sqrt_pos.2
    (by exact_mod_cast explicitHighProbabilityScale_pos scheduleIndex))

/-- The inverse-square-root first-passage threshold tends to zero. -/
theorem
    selfConsistentScheduledNaturalCausalInverseSqrtFirstPassageThreshold_tendsto_zero :
    Tendsto
      selfConsistentScheduledNaturalCausalInverseSqrtFirstPassageThreshold
      atTop (nhds 0) := by
  unfold selfConsistentScheduledNaturalCausalInverseSqrtFirstPassageThreshold
  exact tendsto_const_nhds.div_atTop
    (Real.tendsto_sqrt_atTop.comp
      explicitHighProbabilityScale_real_tendsto_atTop)

/-- Capped first passage at the inverse-square-root threshold. -/
noncomputable def
    selfConsistentScheduledNaturalCausalInverseSqrtThresholdCappedDoubleLinearRawWindowFirstPassageStoppingPrefix
    (mdp : MDP State Action) (initialState : Measure State)
    [IsProbabilityMeasure initialState]
    (rewardSource : mdp.MeanCompatibleRewardKernel)
    (initialTable : DeterministicMarkovPolicyTable mdp)
    (defaultState : State) (varianceProxy : NNReal)
    (baseVisitFloor : Real) (scheduleIndex : Nat) :
    HeterogeneousStochasticEpisodeBatchTrajectory mdp
        (fun t =>
          AdaptiveStochasticEpisodeBatchSource.selfConsistentScheduledEpisodes
            mdp varianceProxy baseVisitFloor t) -> WithTop Nat :=
  selfConsistentScheduledNaturalCausalCappedDoubleLinearRawWindowFirstPassageStoppingPrefix
    mdp initialState rewardSource initialTable defaultState varianceProxy
      baseVisitFloor
        selfConsistentScheduledNaturalCausalInverseSqrtFirstPassageThreshold
          scheduleIndex

/-- Event that inverse-square-root first passage advances beyond its base. -/
noncomputable def
    selfConsistentScheduledNaturalCausalInverseSqrtThresholdCappedDoubleLinearRawWindowFirstPassageDelayedSet
    (mdp : MDP State Action) (initialState : Measure State)
    [IsProbabilityMeasure initialState]
    (rewardSource : mdp.MeanCompatibleRewardKernel)
    (initialTable : DeterministicMarkovPolicyTable mdp)
    (defaultState : State) (varianceProxy : NNReal)
    (baseVisitFloor : Real) (scheduleIndex : Nat) :
    Set (HeterogeneousStochasticEpisodeBatchTrajectory mdp
      (fun t =>
        AdaptiveStochasticEpisodeBatchSource.selfConsistentScheduledEpisodes
          mdp varianceProxy baseVisitFloor t)) :=
  {trajectory |
    (explicitHighProbabilityRounds scheduleIndex : WithTop Nat) <
      selfConsistentScheduledNaturalCausalInverseSqrtThresholdCappedDoubleLinearRawWindowFirstPassageStoppingPrefix
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor scheduleIndex trajectory}

/-- Probability that inverse-square-root first passage advances past its base. -/
noncomputable def
    selfConsistentScheduledNaturalCausalInverseSqrtThresholdCappedDoubleLinearRawWindowFirstPassageDelayedProbability
    (mdp : MDP State Action) (initialState : Measure State)
    [IsProbabilityMeasure initialState]
    (rewardSource : mdp.MeanCompatibleRewardKernel)
    (initialTable : DeterministicMarkovPolicyTable mdp)
    (defaultState : State) (varianceProxy : NNReal)
    (baseVisitFloor : Real) (scheduleIndex : Nat) : ENNReal :=
  let source := selfConsistentScheduledCausalSource mdp initialState
    rewardSource initialTable defaultState varianceProxy baseVisitFloor
  source.trajectoryMeasure
    (selfConsistentScheduledNaturalCausalInverseSqrtThresholdCappedDoubleLinearRawWindowFirstPassageDelayedSet
      mdp initialState rewardSource initialTable defaultState varianceProxy
        baseVisitFloor scheduleIndex)

/-- Markov rate obtained by dividing the scheduled L1 envelope by the
inverse-square-root threshold. -/
noncomputable def
    selfConsistentScheduledNaturalCausalInverseSqrtThresholdCappedDoubleLinearRawWindowFirstPassageDelayRate
    (mdp : MDP State Action) (varianceProxy : NNReal)
    (scheduleIndex : Nat) : Real :=
  explicitPolynomialPrefixAverageRealizedBehaviorRegretL1SummableEnvelope
      mdp varianceProxy scheduleIndex /
    selfConsistentScheduledNaturalCausalInverseSqrtFirstPassageThreshold
      scheduleIndex

/-- Delay is exactly strict one-sided threshold violation at the base. -/
theorem
    selfConsistentScheduledNaturalCausalInverseSqrtThresholdCappedDoubleLinearRawWindowFirstPassageDelayedSet_eq
    (mdp : MDP State Action) (initialState : Measure State)
    [IsProbabilityMeasure initialState]
    (rewardSource : mdp.MeanCompatibleRewardKernel)
    (initialTable : DeterministicMarkovPolicyTable mdp)
    (defaultState : State) (varianceProxy : NNReal)
    (baseVisitFloor : Real) (scheduleIndex : Nat) :
    selfConsistentScheduledNaturalCausalInverseSqrtThresholdCappedDoubleLinearRawWindowFirstPassageDelayedSet
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor scheduleIndex =
      {trajectory |
        selfConsistentScheduledNaturalCausalInverseSqrtFirstPassageThreshold
            scheduleIndex <
          explicitPolynomialPrefixAverageRealizedBehaviorRegretProcess mdp
            initialState rewardSource initialTable defaultState varianceProxy
              baseVisitFloor scheduleIndex trajectory} := by
  ext trajectory
  constructor
  · intro hdelay
    change (explicitHighProbabilityRounds scheduleIndex : WithTop Nat) <
      (selfConsistentScheduledNaturalCausalCappedDoubleLinearRawWindowFirstPassagePrefixNat
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor
            selfConsistentScheduledNaturalCausalInverseSqrtFirstPassageThreshold
              scheduleIndex trajectory : WithTop Nat) at hdelay
    have hdelayNat :
        explicitHighProbabilityRounds scheduleIndex <
          selfConsistentScheduledNaturalCausalCappedDoubleLinearRawWindowFirstPassagePrefixNat
            mdp initialState rewardSource initialTable defaultState varianceProxy
              baseVisitFloor
                selfConsistentScheduledNaturalCausalInverseSqrtFirstPassageThreshold
                  scheduleIndex trajectory := by
      exact_mod_cast hdelay
    simpa [explicitPolynomialPrefixAverageRealizedBehaviorRegretProcess] using
      (selfConsistentScheduledNaturalCausalCappedDoubleLinearRawWindowFirstPassagePrefixNat_before_gt
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor
            selfConsistentScheduledNaturalCausalInverseSqrtFirstPassageThreshold
              scheduleIndex (explicitHighProbabilityRounds scheduleIndex)
                trajectory le_rfl hdelayNat)
  · intro hbaseViolation
    change (explicitHighProbabilityRounds scheduleIndex : WithTop Nat) <
      selfConsistentScheduledNaturalCausalInverseSqrtThresholdCappedDoubleLinearRawWindowFirstPassageStoppingPrefix
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor scheduleIndex trajectory
    have hlower :=
      selfConsistentScheduledNaturalCausalCappedDoubleLinearRawWindowFirstPassageStoppingPrefix_lower
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor
            selfConsistentScheduledNaturalCausalInverseSqrtFirstPassageThreshold
              scheduleIndex trajectory
    apply lt_of_le_of_ne hlower
    intro heq
    have heqNat :
        selfConsistentScheduledNaturalCausalCappedDoubleLinearRawWindowFirstPassagePrefixNat
            mdp initialState rewardSource initialTable defaultState varianceProxy
              baseVisitFloor
                selfConsistentScheduledNaturalCausalInverseSqrtFirstPassageThreshold
                  scheduleIndex trajectory =
          explicitHighProbabilityRounds scheduleIndex := by
      change
        (explicitHighProbabilityRounds scheduleIndex : WithTop Nat) =
          (selfConsistentScheduledNaturalCausalCappedDoubleLinearRawWindowFirstPassagePrefixNat
            mdp initialState rewardSource initialTable defaultState varianceProxy
              baseVisitFloor
                selfConsistentScheduledNaturalCausalInverseSqrtFirstPassageThreshold
                  scheduleIndex trajectory : WithTop Nat) at heq
      exact_mod_cast heq.symm
    have hstrict :
        selfConsistentScheduledNaturalCausalCappedDoubleLinearRawWindowFirstPassagePrefixNat
            mdp initialState rewardSource initialTable defaultState varianceProxy
              baseVisitFloor
                selfConsistentScheduledNaturalCausalInverseSqrtFirstPassageThreshold
                  scheduleIndex trajectory <
          explicitHighProbabilityRounds scheduleIndex +
            (2 * scheduleIndex + 1) := by
      rw [heqNat]
      omega
    have hhit :=
      selfConsistentScheduledNaturalCausalCappedDoubleLinearRawWindowFirstPassagePrefixNat_le_threshold_of_lt_right
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor
            selfConsistentScheduledNaturalCausalInverseSqrtFirstPassageThreshold
              scheduleIndex trajectory hstrict
    rw [heqNat] at hhit
    exact (not_lt_of_ge hhit)
      (by
        simpa [explicitPolynomialPrefixAverageRealizedBehaviorRegretProcess]
          using hbaseViolation)

/-- The inverse-square-root delay event is measurable. -/
theorem
    measurableSet_selfConsistentScheduledNaturalCausalInverseSqrtThresholdCappedDoubleLinearRawWindowFirstPassageDelayedSet
    (mdp : MDP State Action) (initialState : Measure State)
    [IsProbabilityMeasure initialState]
    (rewardSource : mdp.MeanCompatibleRewardKernel)
    (initialTable : DeterministicMarkovPolicyTable mdp)
    (defaultState : State) (varianceProxy : NNReal)
    (baseVisitFloor : Real) (scheduleIndex : Nat) :
    MeasurableSet
      (selfConsistentScheduledNaturalCausalInverseSqrtThresholdCappedDoubleLinearRawWindowFirstPassageDelayedSet
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor scheduleIndex) := by
  rw [
    selfConsistentScheduledNaturalCausalInverseSqrtThresholdCappedDoubleLinearRawWindowFirstPassageDelayedSet_eq]
  exact measurableSet_lt measurable_const
    (measurable_explicitPolynomialPrefixAverageRealizedBehaviorRegretProcess
      mdp initialState rewardSource initialTable defaultState varianceProxy
        baseVisitFloor scheduleIndex)

/-- Delayed inverse-square-root first passage is contained in the scheduled
distance violation. -/
theorem
    selfConsistentScheduledNaturalCausalInverseSqrtThresholdCappedDoubleLinearRawWindowFirstPassageDelayedSet_subset_distanceViolationSet
    (mdp : MDP State Action) (initialState : Measure State)
    [IsProbabilityMeasure initialState]
    (rewardSource : mdp.MeanCompatibleRewardKernel)
    (initialTable : DeterministicMarkovPolicyTable mdp)
    (defaultState : State) (varianceProxy : NNReal)
    (baseVisitFloor : Real) (scheduleIndex : Nat) :
    selfConsistentScheduledNaturalCausalInverseSqrtThresholdCappedDoubleLinearRawWindowFirstPassageDelayedSet
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor scheduleIndex ⊆
      explicitPolynomialPrefixAverageRealizedBehaviorRegretDistanceViolationSet
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor
            (selfConsistentScheduledNaturalCausalInverseSqrtFirstPassageThreshold
              scheduleIndex) scheduleIndex := by
  rw [
    selfConsistentScheduledNaturalCausalInverseSqrtThresholdCappedDoubleLinearRawWindowFirstPassageDelayedSet_eq]
  intro trajectory hdelay
  change
    selfConsistentScheduledNaturalCausalInverseSqrtFirstPassageThreshold
        scheduleIndex <=
      dist
        (explicitPolynomialPrefixAverageRealizedBehaviorRegretProcess mdp
          initialState rewardSource initialTable defaultState varianceProxy
            baseVisitFloor scheduleIndex trajectory) 0
  have habs :
      selfConsistentScheduledNaturalCausalInverseSqrtFirstPassageThreshold
          scheduleIndex <=
        |explicitPolynomialPrefixAverageRealizedBehaviorRegretProcess mdp
          initialState rewardSource initialTable defaultState varianceProxy
            baseVisitFloor scheduleIndex trajectory| :=
    (le_of_lt hdelay).trans (le_abs_self _)
  simpa [Real.dist_eq] using habs

private lemma sqrt_div_pow_three_eq_inverse_rpow_five_halves
    (s : Real) (hs : 0 < s) :
    Real.sqrt s / s ^ 3 = 1 / s ^ (5 / 2 : Real) := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast]
  rw [← Real.rpow_sub hs]
  norm_num
  rw [Real.rpow_neg hs.le]

private lemma sqrt_div_pow_two_eq_inverse_rpow_three_halves
    (s : Real) (hs : 0 < s) :
    Real.sqrt s / s ^ 2 = 1 / s ^ (3 / 2 : Real) := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast]
  rw [← Real.rpow_sub hs]
  norm_num
  rw [Real.rpow_neg hs.le]

omit [DecidableEq State] [DecidableEq Action]
    [MeasurableSingletonClass State] [MeasurableSingletonClass Action]
    [Nonempty State] [Nonempty Action] in
/-- The inverse-square-root delay rate is an inverse-`5/2` behavior term plus
an inverse-`3/2` return term. -/
theorem
    selfConsistentScheduledNaturalCausalInverseSqrtThresholdCappedDoubleLinearRawWindowFirstPassageDelayRate_eq
    (mdp : MDP State Action) (varianceProxy : NNReal)
    (scheduleIndex : Nat) :
    selfConsistentScheduledNaturalCausalInverseSqrtThresholdCappedDoubleLinearRawWindowFirstPassageDelayRate
        mdp varianceProxy scheduleIndex =
      4 * selfConsistentScheduledNaturalCausalLogarithmicRateCoefficient mdp /
          (explicitHighProbabilityScale scheduleIndex : Real) ^
            (5 / 2 : Real) +
        (2 * Real.sqrt
            (mdp.globalReturnDeviationPerEpisodeVarianceProxy 1 varianceProxy :
              Real) *
            Real.exp (1 / 2 : Real)) /
          (explicitHighProbabilityScale scheduleIndex : Real) ^
            (3 / 2 : Real) := by
  let s : Real := explicitHighProbabilityScale scheduleIndex
  let a : Real :=
    4 * selfConsistentScheduledNaturalCausalLogarithmicRateCoefficient mdp
  let b : Real :=
    2 * Real.sqrt
      (mdp.globalReturnDeviationPerEpisodeVarianceProxy 1 varianceProxy : Real) *
        Real.exp (1 / 2 : Real)
  have hs : 0 < s := by
    dsimp [s]
    exact_mod_cast explicitHighProbabilityScale_pos scheduleIndex
  have hs0 : s ≠ 0 := ne_of_gt hs
  have hsqrt0 : Real.sqrt s ≠ 0 := (Real.sqrt_pos.2 hs).ne'
  unfold
    selfConsistentScheduledNaturalCausalInverseSqrtThresholdCappedDoubleLinearRawWindowFirstPassageDelayRate
    selfConsistentScheduledNaturalCausalInverseSqrtFirstPassageThreshold
    explicitPolynomialPrefixAverageRealizedBehaviorRegretL1SummableEnvelope
    explicitPolynomialPrefixAverageBehaviorRegretL1SummableEnvelope
    explicitPolynomialPrefixAverageReturnL1SummableEnvelope
  change (a / s ^ 3 + b / s ^ 2) / (1 / Real.sqrt s) =
    a / s ^ (5 / 2 : Real) + b / s ^ (3 / 2 : Real)
  calc
    (a / s ^ 3 + b / s ^ 2) / (1 / Real.sqrt s) =
        (a / s ^ 3 + b / s ^ 2) * Real.sqrt s := by
      field_simp [hsqrt0]
    _ = a * (Real.sqrt s / s ^ 3) +
          b * (Real.sqrt s / s ^ 2) := by
      field_simp [hs0, hsqrt0]
    _ = a / s ^ (5 / 2 : Real) + b / s ^ (3 / 2 : Real) := by
      rw [sqrt_div_pow_three_eq_inverse_rpow_five_halves s hs,
        sqrt_div_pow_two_eq_inverse_rpow_three_halves s hs]
      ring

/-- The expected absolute base process divided by the inverse-square-root
threshold is bounded by the explicit delay rate. -/
theorem
    explicitPolynomialPrefixExpectedAbsoluteAverageRealizedBehaviorRegret_div_inverseSqrtFirstPassageThreshold_le_delayRate
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
    (scheduleIndex : Nat) :
    explicitPolynomialPrefixExpectedAbsoluteAverageRealizedBehaviorRegret
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor scheduleIndex /
        selfConsistentScheduledNaturalCausalInverseSqrtFirstPassageThreshold
          scheduleIndex <=
      selfConsistentScheduledNaturalCausalInverseSqrtThresholdCappedDoubleLinearRawWindowFirstPassageDelayRate
        mdp varianceProxy scheduleIndex := by
  unfold
    selfConsistentScheduledNaturalCausalInverseSqrtThresholdCappedDoubleLinearRawWindowFirstPassageDelayRate
  exact div_le_div_of_nonneg_right
    (explicitPolynomialPrefixExpectedAbsoluteAverageRealizedBehaviorRegret_le_summableEnvelope
      mdp initialState rewardSource varianceProxy hvarianceProxy law initialTable
        defaultState support baseVisitFloor hbaseFloor hrewardBound hhorizon
          hbaseVisitFloor scheduleIndex)
    (selfConsistentScheduledNaturalCausalInverseSqrtFirstPassageThreshold_pos
      scheduleIndex).le

omit [DecidableEq State] [DecidableEq Action]
    [MeasurableSingletonClass State] [MeasurableSingletonClass Action]
    [Nonempty State] [Nonempty Action] in
/-- The inverse-square-root delay rate is summable. -/
theorem
    summable_selfConsistentScheduledNaturalCausalInverseSqrtThresholdCappedDoubleLinearRawWindowFirstPassageDelayRate
    (mdp : MDP State Action) (varianceProxy : NNReal) :
    Summable
      (selfConsistentScheduledNaturalCausalInverseSqrtThresholdCappedDoubleLinearRawWindowFirstPassageDelayRate
        mdp varianceProxy) := by
  rw [show
    selfConsistentScheduledNaturalCausalInverseSqrtThresholdCappedDoubleLinearRawWindowFirstPassageDelayRate
        mdp varianceProxy =
      fun scheduleIndex =>
        4 * selfConsistentScheduledNaturalCausalLogarithmicRateCoefficient mdp /
            (explicitHighProbabilityScale scheduleIndex : Real) ^
              (5 / 2 : Real) +
          (2 * Real.sqrt
              (mdp.globalReturnDeviationPerEpisodeVarianceProxy 1 varianceProxy :
                Real) *
              Real.exp (1 / 2 : Real)) /
            (explicitHighProbabilityScale scheduleIndex : Real) ^
              (3 / 2 : Real) by
      funext scheduleIndex
      exact
        selfConsistentScheduledNaturalCausalInverseSqrtThresholdCappedDoubleLinearRawWindowFirstPassageDelayRate_eq
          mdp varianceProxy scheduleIndex]
  have hfive :
      Summable (fun scheduleIndex : Nat =>
        1 / (explicitHighProbabilityScale scheduleIndex : Real) ^
          (5 / 2 : Real)) := by
    have h :=
      (Real.summable_one_div_nat_add_rpow 1 (5 / 2 : Real)).2
        (by norm_num)
    refine h.congr ?_
    intro n
    rw [abs_of_pos (by positivity : 0 < (n : Real) + 1)]
    simp [explicitHighProbabilityScale]
  have hthree :
      Summable (fun scheduleIndex : Nat =>
        1 / (explicitHighProbabilityScale scheduleIndex : Real) ^
          (3 / 2 : Real)) := by
    have h :=
      (Real.summable_one_div_nat_add_rpow 1 (3 / 2 : Real)).2
        (by norm_num)
    refine h.congr ?_
    intro n
    rw [abs_of_pos (by positivity : 0 < (n : Real) + 1)]
    simp [explicitHighProbabilityScale]
  simpa [div_eq_mul_inv] using
    (hfive.mul_left
        (4 * selfConsistentScheduledNaturalCausalLogarithmicRateCoefficient
          mdp)).add
      (hthree.mul_left
        (2 * Real.sqrt
            (mdp.globalReturnDeviationPerEpisodeVarianceProxy 1 varianceProxy :
              Real) *
          Real.exp (1 / 2 : Real)))

omit [DecidableEq State] [DecidableEq Action]
    [MeasurableSingletonClass State] [MeasurableSingletonClass Action]
    [Nonempty State] [Nonempty Action] in
/-- Summability implies that the inverse-square-root delay rate tends to zero. -/
theorem
    selfConsistentScheduledNaturalCausalInverseSqrtThresholdCappedDoubleLinearRawWindowFirstPassageDelayRate_tendsto_zero
    (mdp : MDP State Action) (varianceProxy : NNReal) :
    Tendsto
      (selfConsistentScheduledNaturalCausalInverseSqrtThresholdCappedDoubleLinearRawWindowFirstPassageDelayRate
        mdp varianceProxy) atTop (nhds 0) :=
  (summable_selfConsistentScheduledNaturalCausalInverseSqrtThresholdCappedDoubleLinearRawWindowFirstPassageDelayRate
    mdp varianceProxy).tendsto_atTop_zero

/-- Markov control of inverse-square-root first-passage delay. -/
theorem
    selfConsistentScheduledNaturalCausalInverseSqrtThresholdCappedDoubleLinearRawWindowFirstPassageDelayedProbability_le_rate
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
    (scheduleIndex : Nat) :
    selfConsistentScheduledNaturalCausalInverseSqrtThresholdCappedDoubleLinearRawWindowFirstPassageDelayedProbability
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor scheduleIndex <=
      ENNReal.ofReal
        (selfConsistentScheduledNaturalCausalInverseSqrtThresholdCappedDoubleLinearRawWindowFirstPassageDelayRate
          mdp varianceProxy scheduleIndex) := by
  let source := selfConsistentScheduledCausalSource mdp initialState
    rewardSource initialTable defaultState varianceProxy baseVisitFloor
  calc
    selfConsistentScheduledNaturalCausalInverseSqrtThresholdCappedDoubleLinearRawWindowFirstPassageDelayedProbability
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor scheduleIndex =
      source.trajectoryMeasure
        (selfConsistentScheduledNaturalCausalInverseSqrtThresholdCappedDoubleLinearRawWindowFirstPassageDelayedSet
          mdp initialState rewardSource initialTable defaultState varianceProxy
            baseVisitFloor scheduleIndex) := by rfl
    _ <= source.trajectoryMeasure
        (explicitPolynomialPrefixAverageRealizedBehaviorRegretDistanceViolationSet
          mdp initialState rewardSource initialTable defaultState varianceProxy
            baseVisitFloor
              (selfConsistentScheduledNaturalCausalInverseSqrtFirstPassageThreshold
                scheduleIndex) scheduleIndex) :=
      measure_mono
        (selfConsistentScheduledNaturalCausalInverseSqrtThresholdCappedDoubleLinearRawWindowFirstPassageDelayedSet_subset_distanceViolationSet
          mdp initialState rewardSource initialTable defaultState varianceProxy
            baseVisitFloor scheduleIndex)
    _ =
      explicitPolynomialPrefixAverageRealizedBehaviorRegretDistanceViolationProbability
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor
            (selfConsistentScheduledNaturalCausalInverseSqrtFirstPassageThreshold
              scheduleIndex) scheduleIndex := by rfl
    _ <= ENNReal.ofReal
        (explicitPolynomialPrefixExpectedAbsoluteAverageRealizedBehaviorRegret
          mdp initialState rewardSource initialTable defaultState varianceProxy
            baseVisitFloor scheduleIndex /
          selfConsistentScheduledNaturalCausalInverseSqrtFirstPassageThreshold
            scheduleIndex) :=
      explicitPolynomialPrefixAverageRealizedBehaviorRegretDistanceViolationProbability_le_expectedAbsolute_div
        mdp initialState rewardSource varianceProxy law initialTable defaultState
          baseVisitFloor
            (selfConsistentScheduledNaturalCausalInverseSqrtFirstPassageThreshold
              scheduleIndex)
            hrewardBound
              (selfConsistentScheduledNaturalCausalInverseSqrtFirstPassageThreshold_pos
                scheduleIndex) scheduleIndex
    _ <= ENNReal.ofReal
        (selfConsistentScheduledNaturalCausalInverseSqrtThresholdCappedDoubleLinearRawWindowFirstPassageDelayRate
          mdp varianceProxy scheduleIndex) :=
      ENNReal.ofReal_le_ofReal
        (explicitPolynomialPrefixExpectedAbsoluteAverageRealizedBehaviorRegret_div_inverseSqrtFirstPassageThreshold_le_delayRate
          mdp initialState rewardSource varianceProxy hvarianceProxy law initialTable
            defaultState support baseVisitFloor hbaseFloor hrewardBound hhorizon
              hbaseVisitFloor scheduleIndex)

/-- Inverse-square-root delay probabilities have finite total ENNReal mass. -/
theorem
    tsum_selfConsistentScheduledNaturalCausalInverseSqrtThresholdCappedDoubleLinearRawWindowFirstPassageDelayedProbability_ne_top
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
    (∑' scheduleIndex,
      selfConsistentScheduledNaturalCausalInverseSqrtThresholdCappedDoubleLinearRawWindowFirstPassageDelayedProbability
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor scheduleIndex) ≠ ∞ := by
  have hrate :=
    summable_selfConsistentScheduledNaturalCausalInverseSqrtThresholdCappedDoubleLinearRawWindowFirstPassageDelayRate
      mdp varianceProxy
  exact ne_top_of_le_ne_top hrate.tsum_ofReal_ne_top
    (ENNReal.tsum_le_tsum fun scheduleIndex =>
      selfConsistentScheduledNaturalCausalInverseSqrtThresholdCappedDoubleLinearRawWindowFirstPassageDelayedProbability_le_rate
        mdp initialState rewardSource varianceProxy hvarianceProxy law initialTable
          defaultState support baseVisitFloor hbaseFloor hrewardBound hhorizon
            hbaseVisitFloor scheduleIndex)

/-- Almost every trajectory eventually avoids every inverse-square-root delay
event. -/
theorem
    ae_eventually_not_mem_selfConsistentScheduledNaturalCausalInverseSqrtThresholdCappedDoubleLinearRawWindowFirstPassageDelayedSet
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
      ∀ᶠ scheduleIndex in atTop,
        trajectory ∉
          selfConsistentScheduledNaturalCausalInverseSqrtThresholdCappedDoubleLinearRawWindowFirstPassageDelayedSet
            mdp initialState rewardSource initialTable defaultState varianceProxy
              baseVisitFloor scheduleIndex := by
  dsimp only
  apply ae_eventually_notMem
  simpa [
    selfConsistentScheduledNaturalCausalInverseSqrtThresholdCappedDoubleLinearRawWindowFirstPassageDelayedProbability]
    using
      (tsum_selfConsistentScheduledNaturalCausalInverseSqrtThresholdCappedDoubleLinearRawWindowFirstPassageDelayedProbability_ne_top
        mdp initialState rewardSource varianceProxy hvarianceProxy law initialTable
          defaultState support baseVisitFloor hbaseFloor hrewardBound hhorizon
            hbaseVisitFloor)

/-- Almost surely, the inverse-square-root first-passage rule eventually stops
exactly at the fourth-power base. -/
theorem
    ae_eventually_selfConsistentScheduledNaturalCausalInverseSqrtThresholdCappedDoubleLinearRawWindowFirstPassageStoppingPrefix_eq_base
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
      ∀ᶠ scheduleIndex in atTop,
        selfConsistentScheduledNaturalCausalInverseSqrtThresholdCappedDoubleLinearRawWindowFirstPassageStoppingPrefix
            mdp initialState rewardSource initialTable defaultState varianceProxy
              baseVisitFloor scheduleIndex trajectory =
          (explicitHighProbabilityRounds scheduleIndex : WithTop Nat) := by
  dsimp only
  have hnotDelay :=
    ae_eventually_not_mem_selfConsistentScheduledNaturalCausalInverseSqrtThresholdCappedDoubleLinearRawWindowFirstPassageDelayedSet
      mdp initialState rewardSource varianceProxy hvarianceProxy law initialTable
        defaultState support baseVisitFloor hbaseFloor hrewardBound hhorizon
          hbaseVisitFloor
  filter_upwards [hnotDelay] with trajectory htrajectory
  filter_upwards [htrajectory] with scheduleIndex hnot
  have hupper :
      selfConsistentScheduledNaturalCausalInverseSqrtThresholdCappedDoubleLinearRawWindowFirstPassageStoppingPrefix
          mdp initialState rewardSource initialTable defaultState varianceProxy
            baseVisitFloor scheduleIndex trajectory <=
        (explicitHighProbabilityRounds scheduleIndex : WithTop Nat) := by
    exact not_lt.mp (by
      simpa [
        selfConsistentScheduledNaturalCausalInverseSqrtThresholdCappedDoubleLinearRawWindowFirstPassageDelayedSet]
        using hnot)
  exact le_antisymm hupper
    (selfConsistentScheduledNaturalCausalCappedDoubleLinearRawWindowFirstPassageStoppingPrefix_lower
      mdp initialState rewardSource initialTable defaultState varianceProxy
        baseVisitFloor
          selfConsistentScheduledNaturalCausalInverseSqrtFirstPassageThreshold
            scheduleIndex trajectory)

/-- The summably bounded inverse-square-root delay probability tends to zero. -/
theorem
    selfConsistentScheduledNaturalCausalInverseSqrtThresholdCappedDoubleLinearRawWindowFirstPassageDelayedProbability_tendsto_zero
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
      (selfConsistentScheduledNaturalCausalInverseSqrtThresholdCappedDoubleLinearRawWindowFirstPassageDelayedProbability
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor) atTop (nhds 0) := by
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le'
    tendsto_const_nhds
    (by
      simpa only [ENNReal.ofReal_zero] using
        ENNReal.tendsto_ofReal
          (selfConsistentScheduledNaturalCausalInverseSqrtThresholdCappedDoubleLinearRawWindowFirstPassageDelayRate_tendsto_zero
            mdp varianceProxy))
    (Filter.Eventually.of_forall fun _ => bot_le)
    (Filter.Eventually.of_forall fun scheduleIndex =>
      selfConsistentScheduledNaturalCausalInverseSqrtThresholdCappedDoubleLinearRawWindowFirstPassageDelayedProbability_le_rate
        mdp initialState rewardSource varianceProxy hvarianceProxy law initialTable
          defaultState support baseVisitFloor hbaseFloor hrewardBound hhorizon
            hbaseVisitFloor scheduleIndex)

/- The calibrated summable-delay conclusion and complete stopped L1 terminal. -/
theorem
    selfConsistentScheduledCausalSource_inverseSqrtThresholdCappedDoubleLinearRawWindowFirstPassage_summableDelay_eventuallyImmediateStopping_and_L1_consistency
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
    let threshold :=
      selfConsistentScheduledNaturalCausalInverseSqrtFirstPassageThreshold
    let stoppingPrefix :=
      selfConsistentScheduledNaturalCausalInverseSqrtThresholdCappedDoubleLinearRawWindowFirstPassageStoppingPrefix
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor
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
      selfConsistentScheduledNaturalCausalExpectedAbsoluteRateControlledRawWindowStoppingAverageRealizedBehaviorRegret
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor stoppingPrefix
    let budget :=
      selfConsistentScheduledNaturalCausalRateControlledRawWindowStoppingL1Budget
        mdp varianceProxy baseVisitFloor explicitHighProbabilityRounds
          (fun scheduleIndex => 2 * scheduleIndex + 1)
    let rate :=
      selfConsistentScheduledNaturalCausalRateControlledRawWindowStoppingL1Rate
        mdp varianceProxy explicitHighProbabilityRounds
          (fun scheduleIndex => 2 * scheduleIndex + 1)
    let delayedSet :=
      selfConsistentScheduledNaturalCausalInverseSqrtThresholdCappedDoubleLinearRawWindowFirstPassageDelayedSet
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor
    let delayedProbability :=
      selfConsistentScheduledNaturalCausalInverseSqrtThresholdCappedDoubleLinearRawWindowFirstPassageDelayedProbability
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor
    let delayRate :=
      selfConsistentScheduledNaturalCausalInverseSqrtThresholdCappedDoubleLinearRawWindowFirstPassageDelayRate
        mdp varianceProxy
    (forall scheduleIndex, 0 < threshold scheduleIndex) /\
      Tendsto threshold atTop (nhds 0) /\
      (forall scheduleIndex, MeasurableSet (delayedSet scheduleIndex)) /\
      (forall scheduleIndex,
        delayedSet scheduleIndex ⊆
          explicitPolynomialPrefixAverageRealizedBehaviorRegretDistanceViolationSet
            mdp initialState rewardSource initialTable defaultState varianceProxy
              baseVisitFloor (threshold scheduleIndex) scheduleIndex) /\
      (forall scheduleIndex,
        delayedProbability scheduleIndex <= ENNReal.ofReal (delayRate scheduleIndex)) /\
      Summable delayRate /\
      Tendsto delayRate atTop (nhds 0) /\
      (∑' scheduleIndex, delayedProbability scheduleIndex) ≠ ∞ /\
      Tendsto delayedProbability atTop (nhds 0) /\
      (∀ᵐ trajectory ∂source.trajectoryMeasure,
        ∀ᶠ scheduleIndex in atTop,
          trajectory ∉ delayedSet scheduleIndex) /\
      (∀ᵐ trajectory ∂source.trajectoryMeasure,
        ∀ᶠ scheduleIndex in atTop,
          stoppingPrefix scheduleIndex trajectory =
            (explicitHighProbabilityRounds scheduleIndex : WithTop Nat)) /\
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
  refine ⟨
    selfConsistentScheduledNaturalCausalInverseSqrtFirstPassageThreshold_pos,
    selfConsistentScheduledNaturalCausalInverseSqrtFirstPassageThreshold_tendsto_zero,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact fun scheduleIndex =>
      measurableSet_selfConsistentScheduledNaturalCausalInverseSqrtThresholdCappedDoubleLinearRawWindowFirstPassageDelayedSet
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor scheduleIndex
  · exact fun scheduleIndex =>
      selfConsistentScheduledNaturalCausalInverseSqrtThresholdCappedDoubleLinearRawWindowFirstPassageDelayedSet_subset_distanceViolationSet
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor scheduleIndex
  · exact fun scheduleIndex =>
      selfConsistentScheduledNaturalCausalInverseSqrtThresholdCappedDoubleLinearRawWindowFirstPassageDelayedProbability_le_rate
        mdp initialState rewardSource varianceProxy hvarianceProxy law initialTable
          defaultState support baseVisitFloor hbaseFloor hrewardBound hhorizon
            hbaseVisitFloor scheduleIndex
  · exact
      summable_selfConsistentScheduledNaturalCausalInverseSqrtThresholdCappedDoubleLinearRawWindowFirstPassageDelayRate
        mdp varianceProxy
  · exact
      selfConsistentScheduledNaturalCausalInverseSqrtThresholdCappedDoubleLinearRawWindowFirstPassageDelayRate_tendsto_zero
        mdp varianceProxy
  · exact
      tsum_selfConsistentScheduledNaturalCausalInverseSqrtThresholdCappedDoubleLinearRawWindowFirstPassageDelayedProbability_ne_top
        mdp initialState rewardSource varianceProxy hvarianceProxy law initialTable
          defaultState support baseVisitFloor hbaseFloor hrewardBound hhorizon
            hbaseVisitFloor
  · exact
      selfConsistentScheduledNaturalCausalInverseSqrtThresholdCappedDoubleLinearRawWindowFirstPassageDelayedProbability_tendsto_zero
        mdp initialState rewardSource varianceProxy hvarianceProxy law initialTable
          defaultState support baseVisitFloor hbaseFloor hrewardBound hhorizon
            hbaseVisitFloor
  · exact
      ae_eventually_not_mem_selfConsistentScheduledNaturalCausalInverseSqrtThresholdCappedDoubleLinearRawWindowFirstPassageDelayedSet
        mdp initialState rewardSource varianceProxy hvarianceProxy law initialTable
          defaultState support baseVisitFloor hbaseFloor hrewardBound hhorizon
            hbaseVisitFloor
  · exact
      ae_eventually_selfConsistentScheduledNaturalCausalInverseSqrtThresholdCappedDoubleLinearRawWindowFirstPassageStoppingPrefix_eq_base
        mdp initialState rewardSource varianceProxy hvarianceProxy law initialTable
          defaultState support baseVisitFloor hbaseFloor hrewardBound hhorizon
            hbaseVisitFloor
  · simpa only [
      selfConsistentScheduledNaturalCausalInverseSqrtThresholdCappedDoubleLinearRawWindowFirstPassageStoppingPrefix]
      using
        (selfConsistentScheduledCausalSource_cappedDoubleLinearRawWindowFirstPassageStoppingTimeNaturalAverageRealizedBehaviorRegret_L1_consistency
          mdp initialState rewardSource varianceProxy hvarianceProxy law
            initialTable defaultState support baseVisitFloor hbaseFloor
              hrewardBound hhorizon hbaseVisitFloor
                selfConsistentScheduledNaturalCausalInverseSqrtFirstPassageThreshold)

end AdaptiveStochasticSampledEmpiricalOptimisticSource

end BanditRLProof.FiniteHorizonRL
