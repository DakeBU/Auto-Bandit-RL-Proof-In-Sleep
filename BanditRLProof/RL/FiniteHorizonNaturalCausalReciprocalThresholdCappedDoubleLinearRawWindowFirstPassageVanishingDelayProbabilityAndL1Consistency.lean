import BanditRLProof.RL.FiniteHorizonNaturalCausalCappedDoubleLinearRawWindowFirstPassageStoppingTimeL1AverageRealizedBehaviorRegretConsistency
import BanditRLProof.RL.FiniteHorizonNaturalCausalAverageRealizedBehaviorRegretAlmostSureExplicitSchedule

/-!
# Reciprocal-threshold capped first-passage delay probability and L1 consistency

At schedule index `n`, use threshold `1/(n+1)` in the compiled capped
first-passage scan from `(n+1)^4` through `(n+1)^4+(2*n+1)`.

The event that the scan does not stop at its base is exactly the one-sided
base-prefix threshold violation. It is therefore contained in the compiled
absolute-distance event. The explicit scheduled L1 envelope and Markov's
inequality bound its probability by an inverse-square plus inverse-linear
rate, which tends to zero. The compiled capped first-passage theorem supplies
the full stopped L1, in-measure, and almost-everywhere terminal.

This is a moving-threshold first-moment result. It proves neither summability
of delay probabilities nor an uncapped hitting-time theorem.
-/

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

/-- Reciprocal threshold `1/(n+1)` for the scheduled first-passage scan. -/
noncomputable def
    selfConsistentScheduledNaturalCausalReciprocalFirstPassageThreshold
    (scheduleIndex : Nat) : Real :=
  1 / (explicitHighProbabilityScale scheduleIndex : Real)

/-- Every reciprocal first-passage threshold is strictly positive. -/
theorem
    selfConsistentScheduledNaturalCausalReciprocalFirstPassageThreshold_pos
    (scheduleIndex : Nat) :
    0 <
      selfConsistentScheduledNaturalCausalReciprocalFirstPassageThreshold
        scheduleIndex := by
  unfold selfConsistentScheduledNaturalCausalReciprocalFirstPassageThreshold
  exact one_div_pos.mpr
    (by
      exact_mod_cast explicitHighProbabilityScale_pos scheduleIndex)

/-- The reciprocal first-passage threshold tends to zero. -/
theorem
    selfConsistentScheduledNaturalCausalReciprocalFirstPassageThreshold_tendsto_zero :
    Tendsto
      selfConsistentScheduledNaturalCausalReciprocalFirstPassageThreshold
      atTop (nhds 0) := by
  unfold selfConsistentScheduledNaturalCausalReciprocalFirstPassageThreshold
  exact tendsto_const_nhds.div_atTop
    explicitHighProbabilityScale_real_tendsto_atTop

/-- The capped first-passage stopping rule at the reciprocal threshold. -/
noncomputable def
    selfConsistentScheduledNaturalCausalReciprocalThresholdCappedDoubleLinearRawWindowFirstPassageStoppingPrefix
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
        selfConsistentScheduledNaturalCausalReciprocalFirstPassageThreshold
          scheduleIndex

/-- Event that reciprocal-threshold first passage does not stop at its base. -/
noncomputable def
    selfConsistentScheduledNaturalCausalReciprocalThresholdCappedDoubleLinearRawWindowFirstPassageDelayedSet
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
      selfConsistentScheduledNaturalCausalReciprocalThresholdCappedDoubleLinearRawWindowFirstPassageStoppingPrefix
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor scheduleIndex trajectory}

/-- Probability of failing to stop at the first prefix in the scan window. -/
noncomputable def
    selfConsistentScheduledNaturalCausalReciprocalThresholdCappedDoubleLinearRawWindowFirstPassageDelayedProbability
    (mdp : MDP State Action) (initialState : Measure State)
    [IsProbabilityMeasure initialState]
    (rewardSource : mdp.MeanCompatibleRewardKernel)
    (initialTable : DeterministicMarkovPolicyTable mdp)
    (defaultState : State) (varianceProxy : NNReal)
    (baseVisitFloor : Real) (scheduleIndex : Nat) : ENNReal :=
  let source := selfConsistentScheduledCausalSource mdp initialState
    rewardSource initialTable defaultState varianceProxy baseVisitFloor
  source.trajectoryMeasure
    (selfConsistentScheduledNaturalCausalReciprocalThresholdCappedDoubleLinearRawWindowFirstPassageDelayedSet
      mdp initialState rewardSource initialTable defaultState varianceProxy
        baseVisitFloor scheduleIndex)

/-- Deterministic Markov rate for reciprocal-threshold first-passage delay. -/
noncomputable def
    selfConsistentScheduledNaturalCausalReciprocalThresholdCappedDoubleLinearRawWindowFirstPassageDelayRate
    (mdp : MDP State Action) (varianceProxy : NNReal)
    (scheduleIndex : Nat) : Real :=
  explicitPolynomialPrefixAverageRealizedBehaviorRegretL1SummableEnvelope
      mdp varianceProxy scheduleIndex /
    selfConsistentScheduledNaturalCausalReciprocalFirstPassageThreshold
      scheduleIndex

/-- Delay is exactly strict one-sided threshold violation at the base prefix. -/
theorem
    selfConsistentScheduledNaturalCausalReciprocalThresholdCappedDoubleLinearRawWindowFirstPassageDelayedSet_eq
    (mdp : MDP State Action) (initialState : Measure State)
    [IsProbabilityMeasure initialState]
    (rewardSource : mdp.MeanCompatibleRewardKernel)
    (initialTable : DeterministicMarkovPolicyTable mdp)
    (defaultState : State) (varianceProxy : NNReal)
    (baseVisitFloor : Real) (scheduleIndex : Nat) :
    selfConsistentScheduledNaturalCausalReciprocalThresholdCappedDoubleLinearRawWindowFirstPassageDelayedSet
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor scheduleIndex =
      {trajectory |
        selfConsistentScheduledNaturalCausalReciprocalFirstPassageThreshold
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
            selfConsistentScheduledNaturalCausalReciprocalFirstPassageThreshold
              scheduleIndex trajectory : WithTop Nat) at hdelay
    have hdelayNat :
        explicitHighProbabilityRounds scheduleIndex <
          selfConsistentScheduledNaturalCausalCappedDoubleLinearRawWindowFirstPassagePrefixNat
            mdp initialState rewardSource initialTable defaultState varianceProxy
              baseVisitFloor
                selfConsistentScheduledNaturalCausalReciprocalFirstPassageThreshold
                  scheduleIndex trajectory := by
      exact_mod_cast hdelay
    simpa [explicitPolynomialPrefixAverageRealizedBehaviorRegretProcess] using
      (selfConsistentScheduledNaturalCausalCappedDoubleLinearRawWindowFirstPassagePrefixNat_before_gt
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor
            selfConsistentScheduledNaturalCausalReciprocalFirstPassageThreshold
              scheduleIndex (explicitHighProbabilityRounds scheduleIndex)
                trajectory le_rfl hdelayNat)
  · intro hbaseViolation
    change (explicitHighProbabilityRounds scheduleIndex : WithTop Nat) <
      selfConsistentScheduledNaturalCausalReciprocalThresholdCappedDoubleLinearRawWindowFirstPassageStoppingPrefix
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor scheduleIndex trajectory
    have hlower :=
      selfConsistentScheduledNaturalCausalCappedDoubleLinearRawWindowFirstPassageStoppingPrefix_lower
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor
            selfConsistentScheduledNaturalCausalReciprocalFirstPassageThreshold
              scheduleIndex trajectory
    apply lt_of_le_of_ne hlower
    intro heq
    have heqNat :
        selfConsistentScheduledNaturalCausalCappedDoubleLinearRawWindowFirstPassagePrefixNat
            mdp initialState rewardSource initialTable defaultState varianceProxy
              baseVisitFloor
                selfConsistentScheduledNaturalCausalReciprocalFirstPassageThreshold
                  scheduleIndex trajectory =
          explicitHighProbabilityRounds scheduleIndex := by
      change
        (explicitHighProbabilityRounds scheduleIndex : WithTop Nat) =
          (selfConsistentScheduledNaturalCausalCappedDoubleLinearRawWindowFirstPassagePrefixNat
            mdp initialState rewardSource initialTable defaultState varianceProxy
              baseVisitFloor
                selfConsistentScheduledNaturalCausalReciprocalFirstPassageThreshold
                  scheduleIndex trajectory : WithTop Nat) at heq
      exact_mod_cast heq.symm
    have hstrict :
        selfConsistentScheduledNaturalCausalCappedDoubleLinearRawWindowFirstPassagePrefixNat
            mdp initialState rewardSource initialTable defaultState varianceProxy
              baseVisitFloor
                selfConsistentScheduledNaturalCausalReciprocalFirstPassageThreshold
                  scheduleIndex trajectory <
          explicitHighProbabilityRounds scheduleIndex +
            (2 * scheduleIndex + 1) := by
      rw [heqNat]
      omega
    have hhit :=
      selfConsistentScheduledNaturalCausalCappedDoubleLinearRawWindowFirstPassagePrefixNat_le_threshold_of_lt_right
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor
            selfConsistentScheduledNaturalCausalReciprocalFirstPassageThreshold
              scheduleIndex trajectory hstrict
    rw [heqNat] at hhit
    exact (not_lt_of_ge hhit)
      (by
        simpa [explicitPolynomialPrefixAverageRealizedBehaviorRegretProcess]
          using hbaseViolation)

/-- The reciprocal-threshold delay event is measurable. -/
theorem
    measurableSet_selfConsistentScheduledNaturalCausalReciprocalThresholdCappedDoubleLinearRawWindowFirstPassageDelayedSet
    (mdp : MDP State Action) (initialState : Measure State)
    [IsProbabilityMeasure initialState]
    (rewardSource : mdp.MeanCompatibleRewardKernel)
    (initialTable : DeterministicMarkovPolicyTable mdp)
    (defaultState : State) (varianceProxy : NNReal)
    (baseVisitFloor : Real) (scheduleIndex : Nat) :
    MeasurableSet
      (selfConsistentScheduledNaturalCausalReciprocalThresholdCappedDoubleLinearRawWindowFirstPassageDelayedSet
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor scheduleIndex) := by
  rw [
    selfConsistentScheduledNaturalCausalReciprocalThresholdCappedDoubleLinearRawWindowFirstPassageDelayedSet_eq]
  exact measurableSet_lt measurable_const
    (measurable_explicitPolynomialPrefixAverageRealizedBehaviorRegretProcess
      mdp initialState rewardSource initialTable defaultState varianceProxy
        baseVisitFloor scheduleIndex)

/-- Delayed first passage is contained in the scheduled distance violation. -/
theorem
    selfConsistentScheduledNaturalCausalReciprocalThresholdCappedDoubleLinearRawWindowFirstPassageDelayedSet_subset_distanceViolationSet
    (mdp : MDP State Action) (initialState : Measure State)
    [IsProbabilityMeasure initialState]
    (rewardSource : mdp.MeanCompatibleRewardKernel)
    (initialTable : DeterministicMarkovPolicyTable mdp)
    (defaultState : State) (varianceProxy : NNReal)
    (baseVisitFloor : Real) (scheduleIndex : Nat) :
    selfConsistentScheduledNaturalCausalReciprocalThresholdCappedDoubleLinearRawWindowFirstPassageDelayedSet
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor scheduleIndex ⊆
      explicitPolynomialPrefixAverageRealizedBehaviorRegretDistanceViolationSet
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor
            (selfConsistentScheduledNaturalCausalReciprocalFirstPassageThreshold
              scheduleIndex) scheduleIndex := by
  rw [
    selfConsistentScheduledNaturalCausalReciprocalThresholdCappedDoubleLinearRawWindowFirstPassageDelayedSet_eq]
  intro trajectory hdelay
  change
    selfConsistentScheduledNaturalCausalReciprocalFirstPassageThreshold
        scheduleIndex <=
      dist
        (explicitPolynomialPrefixAverageRealizedBehaviorRegretProcess mdp
          initialState rewardSource initialTable defaultState varianceProxy
            baseVisitFloor scheduleIndex trajectory) 0
  have habs :
      selfConsistentScheduledNaturalCausalReciprocalFirstPassageThreshold
          scheduleIndex <=
        |explicitPolynomialPrefixAverageRealizedBehaviorRegretProcess mdp
          initialState rewardSource initialTable defaultState varianceProxy
            baseVisitFloor scheduleIndex trajectory| :=
    (le_of_lt hdelay).trans (le_abs_self _)
  simpa [Real.dist_eq] using habs

omit [DecidableEq State] [DecidableEq Action]
    [MeasurableSingletonClass State] [MeasurableSingletonClass Action]
    [Nonempty State] [Nonempty Action] in
/-- Dividing the scheduled L1 envelope by the reciprocal threshold exposes
an inverse-square plus inverse-linear delay rate. -/
theorem
    selfConsistentScheduledNaturalCausalReciprocalThresholdCappedDoubleLinearRawWindowFirstPassageDelayRate_eq
    (mdp : MDP State Action) (varianceProxy : NNReal)
    (scheduleIndex : Nat) :
    selfConsistentScheduledNaturalCausalReciprocalThresholdCappedDoubleLinearRawWindowFirstPassageDelayRate
        mdp varianceProxy scheduleIndex =
      4 * selfConsistentScheduledNaturalCausalLogarithmicRateCoefficient mdp /
          (explicitHighProbabilityScale scheduleIndex : Real) ^ 2 +
        (2 * Real.sqrt
            (mdp.globalReturnDeviationPerEpisodeVarianceProxy 1 varianceProxy :
              Real) *
            Real.exp (1 / 2 : Real)) /
          (explicitHighProbabilityScale scheduleIndex : Real) := by
  unfold
    selfConsistentScheduledNaturalCausalReciprocalThresholdCappedDoubleLinearRawWindowFirstPassageDelayRate
    selfConsistentScheduledNaturalCausalReciprocalFirstPassageThreshold
    explicitPolynomialPrefixAverageRealizedBehaviorRegretL1SummableEnvelope
    explicitPolynomialPrefixAverageBehaviorRegretL1SummableEnvelope
    explicitPolynomialPrefixAverageReturnL1SummableEnvelope
  have hs : (explicitHighProbabilityScale scheduleIndex : Real) ≠ 0 := by
    exact_mod_cast (ne_of_gt (explicitHighProbabilityScale_pos scheduleIndex))
  field_simp [hs]

/-- The scheduled expected absolute base process divided by the reciprocal
threshold is bounded by the explicit delay rate. -/
theorem
    explicitPolynomialPrefixExpectedAbsoluteAverageRealizedBehaviorRegret_div_reciprocalFirstPassageThreshold_le_delayRate
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
        selfConsistentScheduledNaturalCausalReciprocalFirstPassageThreshold
          scheduleIndex <=
      selfConsistentScheduledNaturalCausalReciprocalThresholdCappedDoubleLinearRawWindowFirstPassageDelayRate
        mdp varianceProxy scheduleIndex := by
  unfold
    selfConsistentScheduledNaturalCausalReciprocalThresholdCappedDoubleLinearRawWindowFirstPassageDelayRate
  exact div_le_div_of_nonneg_right
    (explicitPolynomialPrefixExpectedAbsoluteAverageRealizedBehaviorRegret_le_summableEnvelope
      mdp initialState rewardSource varianceProxy hvarianceProxy law initialTable
        defaultState support baseVisitFloor hbaseFloor hrewardBound hhorizon
          hbaseVisitFloor scheduleIndex)
    (selfConsistentScheduledNaturalCausalReciprocalFirstPassageThreshold_pos
      scheduleIndex).le

omit [DecidableEq State] [DecidableEq Action]
    [MeasurableSingletonClass State] [MeasurableSingletonClass Action]
    [Nonempty State] [Nonempty Action] in
/-- The reciprocal-threshold delay rate tends to zero. -/
theorem
    selfConsistentScheduledNaturalCausalReciprocalThresholdCappedDoubleLinearRawWindowFirstPassageDelayRate_tendsto_zero
    (mdp : MDP State Action) (varianceProxy : NNReal) :
    Tendsto
      (selfConsistentScheduledNaturalCausalReciprocalThresholdCappedDoubleLinearRawWindowFirstPassageDelayRate
        mdp varianceProxy) atTop (nhds 0) := by
  rw [show
    selfConsistentScheduledNaturalCausalReciprocalThresholdCappedDoubleLinearRawWindowFirstPassageDelayRate
        mdp varianceProxy =
      fun scheduleIndex =>
        4 * selfConsistentScheduledNaturalCausalLogarithmicRateCoefficient mdp /
            (explicitHighProbabilityScale scheduleIndex : Real) ^ 2 +
          (2 * Real.sqrt
              (mdp.globalReturnDeviationPerEpisodeVarianceProxy 1 varianceProxy :
                Real) *
              Real.exp (1 / 2 : Real)) /
            (explicitHighProbabilityScale scheduleIndex : Real) by
      funext scheduleIndex
      exact
        selfConsistentScheduledNaturalCausalReciprocalThresholdCappedDoubleLinearRawWindowFirstPassageDelayRate_eq
          mdp varianceProxy scheduleIndex]
  have hscaleSq :
      Tendsto
        (fun scheduleIndex =>
          (explicitHighProbabilityScale scheduleIndex : Real) ^ 2)
        atTop atTop := by
    simpa only [Function.comp_apply] using
      ((tendsto_pow_atTop (α := Real) (by norm_num : (2 : Nat) ≠ 0)).comp
        explicitHighProbabilityScale_real_tendsto_atTop)
  have hbehavior :
      Tendsto
        (fun scheduleIndex =>
          4 * selfConsistentScheduledNaturalCausalLogarithmicRateCoefficient mdp /
            (explicitHighProbabilityScale scheduleIndex : Real) ^ 2)
        atTop (nhds 0) :=
    tendsto_const_nhds.div_atTop hscaleSq
  have hreturn :
      Tendsto
        (fun scheduleIndex =>
          (2 * Real.sqrt
              (mdp.globalReturnDeviationPerEpisodeVarianceProxy 1 varianceProxy :
                Real) *
              Real.exp (1 / 2 : Real)) /
            (explicitHighProbabilityScale scheduleIndex : Real))
        atTop (nhds 0) :=
    tendsto_const_nhds.div_atTop
      explicitHighProbabilityScale_real_tendsto_atTop
  simpa only [zero_add] using hbehavior.add hreturn

/-- Markov control of the reciprocal-threshold first-passage delay event. -/
theorem
    selfConsistentScheduledNaturalCausalReciprocalThresholdCappedDoubleLinearRawWindowFirstPassageDelayedProbability_le_rate
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
    selfConsistentScheduledNaturalCausalReciprocalThresholdCappedDoubleLinearRawWindowFirstPassageDelayedProbability
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor scheduleIndex <=
      ENNReal.ofReal
        (selfConsistentScheduledNaturalCausalReciprocalThresholdCappedDoubleLinearRawWindowFirstPassageDelayRate
          mdp varianceProxy scheduleIndex) := by
  let source := selfConsistentScheduledCausalSource mdp initialState
    rewardSource initialTable defaultState varianceProxy baseVisitFloor
  calc
    selfConsistentScheduledNaturalCausalReciprocalThresholdCappedDoubleLinearRawWindowFirstPassageDelayedProbability
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor scheduleIndex =
      source.trajectoryMeasure
        (selfConsistentScheduledNaturalCausalReciprocalThresholdCappedDoubleLinearRawWindowFirstPassageDelayedSet
          mdp initialState rewardSource initialTable defaultState varianceProxy
            baseVisitFloor scheduleIndex) := by rfl
    _ <= source.trajectoryMeasure
        (explicitPolynomialPrefixAverageRealizedBehaviorRegretDistanceViolationSet
          mdp initialState rewardSource initialTable defaultState varianceProxy
            baseVisitFloor
              (selfConsistentScheduledNaturalCausalReciprocalFirstPassageThreshold
                scheduleIndex) scheduleIndex) :=
      measure_mono
        (selfConsistentScheduledNaturalCausalReciprocalThresholdCappedDoubleLinearRawWindowFirstPassageDelayedSet_subset_distanceViolationSet
          mdp initialState rewardSource initialTable defaultState varianceProxy
            baseVisitFloor scheduleIndex)
    _ =
      explicitPolynomialPrefixAverageRealizedBehaviorRegretDistanceViolationProbability
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor
            (selfConsistentScheduledNaturalCausalReciprocalFirstPassageThreshold
              scheduleIndex) scheduleIndex := by rfl
    _ <= ENNReal.ofReal
        (explicitPolynomialPrefixExpectedAbsoluteAverageRealizedBehaviorRegret
          mdp initialState rewardSource initialTable defaultState varianceProxy
            baseVisitFloor scheduleIndex /
          selfConsistentScheduledNaturalCausalReciprocalFirstPassageThreshold
            scheduleIndex) :=
      explicitPolynomialPrefixAverageRealizedBehaviorRegretDistanceViolationProbability_le_expectedAbsolute_div
        mdp initialState rewardSource varianceProxy law initialTable defaultState
          baseVisitFloor
            (selfConsistentScheduledNaturalCausalReciprocalFirstPassageThreshold
              scheduleIndex)
            hrewardBound
              (selfConsistentScheduledNaturalCausalReciprocalFirstPassageThreshold_pos
                scheduleIndex) scheduleIndex
    _ <= ENNReal.ofReal
        (selfConsistentScheduledNaturalCausalReciprocalThresholdCappedDoubleLinearRawWindowFirstPassageDelayRate
          mdp varianceProxy scheduleIndex) :=
      ENNReal.ofReal_le_ofReal
        (explicitPolynomialPrefixExpectedAbsoluteAverageRealizedBehaviorRegret_div_reciprocalFirstPassageThreshold_le_delayRate
          mdp initialState rewardSource varianceProxy hvarianceProxy law initialTable
            defaultState support baseVisitFloor hbaseFloor hrewardBound hhorizon
              hbaseVisitFloor scheduleIndex)

/-- The probability of delaying beyond the first prefix tends to zero. -/
theorem
    selfConsistentScheduledNaturalCausalReciprocalThresholdCappedDoubleLinearRawWindowFirstPassageDelayedProbability_tendsto_zero
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
      (selfConsistentScheduledNaturalCausalReciprocalThresholdCappedDoubleLinearRawWindowFirstPassageDelayedProbability
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor) atTop (nhds 0) := by
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le'
    tendsto_const_nhds
    (by
      simpa only [ENNReal.ofReal_zero] using
        ENNReal.tendsto_ofReal
          (selfConsistentScheduledNaturalCausalReciprocalThresholdCappedDoubleLinearRawWindowFirstPassageDelayRate_tendsto_zero
            mdp varianceProxy))
    (Filter.Eventually.of_forall fun _ => bot_le)
    (Filter.Eventually.of_forall fun scheduleIndex =>
      selfConsistentScheduledNaturalCausalReciprocalThresholdCappedDoubleLinearRawWindowFirstPassageDelayedProbability_le_rate
        mdp initialState rewardSource varianceProxy hvarianceProxy law initialTable
          defaultState support baseVisitFloor hbaseFloor hrewardBound hhorizon
            hbaseVisitFloor scheduleIndex)

/- The calibrated first-passage probability and complete stopped L1 terminal. -/
theorem
    selfConsistentScheduledCausalSource_reciprocalThresholdCappedDoubleLinearRawWindowFirstPassage_vanishingDelayProbability_and_L1_consistency
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
      selfConsistentScheduledNaturalCausalReciprocalFirstPassageThreshold
    let stoppingPrefix :=
      selfConsistentScheduledNaturalCausalReciprocalThresholdCappedDoubleLinearRawWindowFirstPassageStoppingPrefix
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
      selfConsistentScheduledNaturalCausalReciprocalThresholdCappedDoubleLinearRawWindowFirstPassageDelayedSet
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor
    let delayedProbability :=
      selfConsistentScheduledNaturalCausalReciprocalThresholdCappedDoubleLinearRawWindowFirstPassageDelayedProbability
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor
    let delayRate :=
      selfConsistentScheduledNaturalCausalReciprocalThresholdCappedDoubleLinearRawWindowFirstPassageDelayRate
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
      Tendsto delayRate atTop (nhds 0) /\
      Tendsto delayedProbability atTop (nhds 0) /\
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
    selfConsistentScheduledNaturalCausalReciprocalFirstPassageThreshold_pos,
    selfConsistentScheduledNaturalCausalReciprocalFirstPassageThreshold_tendsto_zero,
    ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact fun scheduleIndex =>
      measurableSet_selfConsistentScheduledNaturalCausalReciprocalThresholdCappedDoubleLinearRawWindowFirstPassageDelayedSet
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor scheduleIndex
  · exact fun scheduleIndex =>
      selfConsistentScheduledNaturalCausalReciprocalThresholdCappedDoubleLinearRawWindowFirstPassageDelayedSet_subset_distanceViolationSet
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor scheduleIndex
  · exact fun scheduleIndex =>
      selfConsistentScheduledNaturalCausalReciprocalThresholdCappedDoubleLinearRawWindowFirstPassageDelayedProbability_le_rate
        mdp initialState rewardSource varianceProxy hvarianceProxy law initialTable
          defaultState support baseVisitFloor hbaseFloor hrewardBound hhorizon
            hbaseVisitFloor scheduleIndex
  · exact
      selfConsistentScheduledNaturalCausalReciprocalThresholdCappedDoubleLinearRawWindowFirstPassageDelayRate_tendsto_zero
        mdp varianceProxy
  · exact
      selfConsistentScheduledNaturalCausalReciprocalThresholdCappedDoubleLinearRawWindowFirstPassageDelayedProbability_tendsto_zero
        mdp initialState rewardSource varianceProxy hvarianceProxy law initialTable
          defaultState support baseVisitFloor hbaseFloor hrewardBound hhorizon
            hbaseVisitFloor
  · simpa only [
      selfConsistentScheduledNaturalCausalReciprocalThresholdCappedDoubleLinearRawWindowFirstPassageStoppingPrefix]
      using
        (selfConsistentScheduledCausalSource_cappedDoubleLinearRawWindowFirstPassageStoppingTimeNaturalAverageRealizedBehaviorRegret_L1_consistency
          mdp initialState rewardSource varianceProxy hvarianceProxy law
            initialTable defaultState support baseVisitFloor hbaseFloor
              hrewardBound hhorizon hbaseVisitFloor
                selfConsistentScheduledNaturalCausalReciprocalFirstPassageThreshold)

end AdaptiveStochasticSampledEmpiricalOptimisticSource

end BanditRLProof.FiniteHorizonRL
