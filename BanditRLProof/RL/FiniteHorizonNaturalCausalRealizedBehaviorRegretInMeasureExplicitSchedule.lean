import BanditRLProof.RL.FiniteHorizonNaturalCausalRealizedBehaviorRegretUpperTailInProbability

/-!
# Explicit polynomial-prefix absolute consistency in measure

This module upgrades the one-sided scheduled certificate to Mathlib
`TendstoInMeasure` for the same equal-round-weighted natural realized
behavior-regret process. Outside the compiled model-tail/return event, the
parent route supplies the upper bound. The exact expected-minus-deviation
identity, expected-regret nonnegativity, and the return-event complement
supply the missing lower bound.

The process differs from the existing mass-weighted
`realizedSuccessorAverageRegret` process. The result is only for the explicit
fourth-power prefix subsequence; it is not all-prefix, anytime, almost-sure,
or L1 convergence.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace BanditRLProof.FiniteHorizonRL

universe u v

variable {State : Type u} {Action : Type v}
    [MeasurableSpace State] [MeasurableSpace Action]
    [Fintype State] [Fintype Action]
    [DecidableEq State] [DecidableEq Action]
    [MeasurableSingletonClass State] [MeasurableSingletonClass Action]
    [Nonempty State] [Nonempty Action]

namespace AdaptiveStochasticSampledEmpiricalOptimisticSource

/-- The equal-round-weighted natural realized-regret process on the explicit schedule. -/
noncomputable def explicitPolynomialPrefixAverageRealizedBehaviorRegretProcess
    (mdp : MDP State Action) (initialState : Measure State)
    [IsProbabilityMeasure initialState]
    (rewardSource : mdp.MeanCompatibleRewardKernel)
    (initialTable : DeterministicMarkovPolicyTable mdp)
    (defaultState : State) (varianceProxy : NNReal)
    (baseVisitFloor : Real) (n : Nat) :
    HeterogeneousStochasticEpisodeBatchTrajectory mdp
        (fun t =>
          AdaptiveStochasticEpisodeBatchSource.selfConsistentScheduledEpisodes
            mdp varianceProxy baseVisitFloor t) -> Real :=
  selfConsistentScheduledNaturalCausalAverageRealizedBehaviorRegretProcess
    mdp initialState rewardSource initialTable defaultState varianceProxy
      baseVisitFloor (explicitHighProbabilityRounds n)

/-- Fixed-threshold distance-from-zero violation for the scheduled process. -/
noncomputable def
    explicitPolynomialPrefixAverageRealizedBehaviorRegretDistanceViolationSet
    (mdp : MDP State Action) (initialState : Measure State)
    [IsProbabilityMeasure initialState]
    (rewardSource : mdp.MeanCompatibleRewardKernel)
    (initialTable : DeterministicMarkovPolicyTable mdp)
    (defaultState : State) (varianceProxy : NNReal)
    (baseVisitFloor epsilon : Real) (n : Nat) :
    Set (HeterogeneousStochasticEpisodeBatchTrajectory mdp
      (fun t =>
        AdaptiveStochasticEpisodeBatchSource.selfConsistentScheduledEpisodes
          mdp varianceProxy baseVisitFloor t)) :=
  {trajectory |
    epsilon <= dist
      (explicitPolynomialPrefixAverageRealizedBehaviorRegretProcess mdp
        initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor n trajectory) 0}

/-- Trajectory probability of the scheduled distance violation. -/
noncomputable def
    explicitPolynomialPrefixAverageRealizedBehaviorRegretDistanceViolationProbability
    (mdp : MDP State Action) (initialState : Measure State)
    [IsProbabilityMeasure initialState]
    (rewardSource : mdp.MeanCompatibleRewardKernel)
    (initialTable : DeterministicMarkovPolicyTable mdp)
    (defaultState : State) (varianceProxy : NNReal)
    (baseVisitFloor epsilon : Real) (n : Nat) : ENNReal :=
  let source := selfConsistentScheduledCausalSource mdp initialState
    rewardSource initialTable defaultState varianceProxy baseVisitFloor
  source.trajectoryMeasure
    (explicitPolynomialPrefixAverageRealizedBehaviorRegretDistanceViolationSet
      mdp initialState rewardSource initialTable defaultState varianceProxy
        baseVisitFloor epsilon n)

/-- Every scheduled coordinate of the equal-round-weighted process is measurable. -/
theorem measurable_explicitPolynomialPrefixAverageRealizedBehaviorRegretProcess
    (mdp : MDP State Action) (initialState : Measure State)
    [IsProbabilityMeasure initialState]
    (rewardSource : mdp.MeanCompatibleRewardKernel)
    (initialTable : DeterministicMarkovPolicyTable mdp)
    (defaultState : State) (varianceProxy : NNReal)
    (baseVisitFloor : Real) (n : Nat) :
    Measurable
      (explicitPolynomialPrefixAverageRealizedBehaviorRegretProcess mdp
        initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor n) := by
  simpa [explicitPolynomialPrefixAverageRealizedBehaviorRegretProcess] using
    (measurable_selfConsistentScheduledNaturalCausalAverageRealizedBehaviorRegretProcess
      mdp initialState rewardSource initialTable defaultState varianceProxy
        baseVisitFloor (explicitHighProbabilityRounds n))

/-- Every fixed-threshold scheduled distance violation is measurable. -/
theorem
    measurableSet_explicitPolynomialPrefixAverageRealizedBehaviorRegretDistanceViolationSet
    (mdp : MDP State Action) (initialState : Measure State)
    [IsProbabilityMeasure initialState]
    (rewardSource : mdp.MeanCompatibleRewardKernel)
    (initialTable : DeterministicMarkovPolicyTable mdp)
    (defaultState : State) (varianceProxy : NNReal)
    (baseVisitFloor epsilon : Real) (n : Nat) :
    MeasurableSet
      (explicitPolynomialPrefixAverageRealizedBehaviorRegretDistanceViolationSet
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor epsilon n) := by
  unfold
    explicitPolynomialPrefixAverageRealizedBehaviorRegretDistanceViolationSet
  exact measurableSet_le measurable_const
    (Measurable.dist
      (measurable_explicitPolynomialPrefixAverageRealizedBehaviorRegretProcess
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor n)
      measurable_const)

/-
Outside the scheduled union event, the return deviation is strictly smaller
than its confidence radius. Nonnegative behavior expected regret therefore
gives the missing lower side after division by the positive scheduled prefix.
-/
theorem
    explicitPolynomialPrefixAverageRealizedBehaviorRegretProcess_neg_averageReturnRadius_lt_of_not_mem_event
    (mdp : MDP State Action) (initialState : Measure State)
    [IsProbabilityMeasure initialState]
    (rewardSource : mdp.MeanCompatibleRewardKernel)
    (initialTable : DeterministicMarkovPolicyTable mdp)
    (defaultState : State) (varianceProxy : NNReal)
    (baseVisitFloor : Real) (n : Nat)
    (trajectory : HeterogeneousStochasticEpisodeBatchTrajectory mdp
      (fun t =>
        AdaptiveStochasticEpisodeBatchSource.selfConsistentScheduledEpisodes
          mdp varianceProxy baseVisitFloor t))
    (htrajectory : trajectory ∉
      explicitPolynomialPrefixTailModelReturnBadEvent mdp initialState
        rewardSource initialTable defaultState varianceProxy baseVisitFloor n) :
    -explicitPolynomialPrefixAverageReturnRadius
        mdp varianceProxy baseVisitFloor n <
      explicitPolynomialPrefixAverageRealizedBehaviorRegretProcess mdp
        initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor n trajectory := by
  have hnotReturn : trajectory ∉
      selfConsistentScheduledNaturalCausalCumulativeReturnBadEvent mdp
        initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor (explicitHighProbabilityRounds n)
            (explicitHighProbabilityReturnDelta n) := by
    intro hreturn
    apply htrajectory
    unfold explicitPolynomialPrefixTailModelReturnBadEvent
      selfConsistentScheduledNaturalCausalBurninTailModelReturnBadEvent
    exact Or.inr hreturn
  have hdeviation :
      |selfConsistentScheduledNaturalCausalCumulativeReturnDeviationProcess
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor (explicitHighProbabilityRounds n) trajectory| <
        Concentration.subGaussianSumConfidenceRadius
          (selfConsistentScheduledNaturalCausalCumulativeReturnVarianceProxy
            mdp varianceProxy baseVisitFloor
              (explicitHighProbabilityRounds n))
          (explicitHighProbabilityReturnDelta n) := by
    simpa [selfConsistentScheduledNaturalCausalCumulativeReturnBadEvent]
      using hnotReturn
  have hexpected : 0 <=
      selfConsistentScheduledNaturalCausalCumulativeBehaviorExpectedRegretProcess
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor (explicitHighProbabilityRounds n) trajectory :=
    selfConsistentScheduledNaturalCausalCumulativeBehaviorExpectedRegretProcess_nonneg
      mdp initialState rewardSource initialTable defaultState varianceProxy
        baseVisitFloor (explicitHighProbabilityRounds n) trajectory
  have hnumerator :
      -Concentration.subGaussianSumConfidenceRadius
          (selfConsistentScheduledNaturalCausalCumulativeReturnVarianceProxy
            mdp varianceProxy baseVisitFloor
              (explicitHighProbabilityRounds n))
          (explicitHighProbabilityReturnDelta n) <
        selfConsistentScheduledNaturalCausalCumulativeBehaviorExpectedRegretProcess
            mdp initialState rewardSource initialTable defaultState varianceProxy
              baseVisitFloor (explicitHighProbabilityRounds n) trajectory -
          selfConsistentScheduledNaturalCausalCumulativeReturnDeviationProcess
            mdp initialState rewardSource initialTable defaultState varianceProxy
              baseVisitFloor (explicitHighProbabilityRounds n) trajectory := by
    have hdev_le :
        selfConsistentScheduledNaturalCausalCumulativeReturnDeviationProcess
            mdp initialState rewardSource initialTable defaultState varianceProxy
              baseVisitFloor (explicitHighProbabilityRounds n) trajectory <=
          |selfConsistentScheduledNaturalCausalCumulativeReturnDeviationProcess
            mdp initialState rewardSource initialTable defaultState varianceProxy
              baseVisitFloor (explicitHighProbabilityRounds n) trajectory| :=
      le_abs_self _
    linarith
  have hrounds : 0 < (explicitHighProbabilityRounds n : Real) := by
    exact_mod_cast explicitHighProbabilityRounds_pos n
  have hdiv := (div_lt_div_iff_of_pos_right hrounds).2 hnumerator
  rw [explicitPolynomialPrefixAverageRealizedBehaviorRegretProcess,
    selfConsistentScheduledNaturalCausalAverageRealizedBehaviorRegretProcess_eq_expected_sub_deviation]
  simpa [explicitPolynomialPrefixAverageReturnRadius, neg_div] using hdiv

/-- Direct projection of the scheduled parent-event probability bound. -/
theorem
    selfConsistentScheduledCausalSource_trajectoryMeasure_explicitPolynomialPrefixTailModelReturnBadEvent_le
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
    let source := selfConsistentScheduledCausalSource mdp initialState
      rewardSource initialTable defaultState varianceProxy baseVisitFloor
    source.trajectoryMeasure
        (explicitPolynomialPrefixTailModelReturnBadEvent mdp initialState
          rewardSource initialTable defaultState varianceProxy baseVisitFloor n) <=
      explicitPolynomialPrefixTailModelReturnFailureBudget mdp n := by
  dsimp only
  have hcert :=
    selfConsistentScheduledCausalSource_explicitPolynomialPrefixHighProbabilityAverageRealizedBehaviorRegretConsistency
      mdp initialState rewardSource varianceProxy hvarianceProxy law
        initialTable defaultState support baseVisitFloor hbaseFloor
          hrewardBound hhorizon hbaseVisitFloor
  dsimp only at hcert
  exact (hcert.2.2.2 n).2.2.1

/-- Eventually every fixed positive distance violation lies in the parent event. -/
theorem
    eventually_explicitPolynomialPrefixAverageRealizedBehaviorRegretDistanceViolationSet_subset_event
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
    ∀ᶠ n in atTop,
      explicitPolynomialPrefixAverageRealizedBehaviorRegretDistanceViolationSet
          mdp initialState rewardSource initialTable defaultState varianceProxy
            baseVisitFloor epsilon n ⊆
        explicitPolynomialPrefixTailModelReturnBadEvent mdp initialState
          rewardSource initialTable defaultState varianceProxy baseVisitFloor n := by
  have hcert :=
    selfConsistentScheduledCausalSource_explicitPolynomialPrefixHighProbabilityAverageRealizedBehaviorRegretConsistency
      mdp initialState rewardSource varianceProxy hvarianceProxy law
        initialTable defaultState support baseVisitFloor hbaseFloor
          hrewardBound hhorizon hbaseVisitFloor
  dsimp only at hcert
  have hrate := hcert.2.1.eventually_lt_const hepsilon
  have hradius :=
    (explicitPolynomialPrefixAverageReturnRadius_tendsto_zero
      mdp varianceProxy baseVisitFloor).eventually_lt_const hepsilon
  filter_upwards [hrate, hradius] with n hrateN hradiusN
  intro trajectory hdistance
  by_contra hnotEvent
  have hlower :=
    explicitPolynomialPrefixAverageRealizedBehaviorRegretProcess_neg_averageReturnRadius_lt_of_not_mem_event
      mdp initialState rewardSource initialTable defaultState varianceProxy
        baseVisitFloor n trajectory hnotEvent
  have hfixed := hcert.2.2.2 n
  rcases hfixed with
    ⟨_heventMeasurable, _hviolationMeasurable, _heventMeasure,
      _hviolationSubset, _hviolationMeasure, _hstrict, hupperPath⟩
  have hupper := hupperPath trajectory hnotEvent
  have hvalueUpper :
      explicitPolynomialPrefixAverageRealizedBehaviorRegretProcess mdp
          initialState rewardSource initialTable defaultState varianceProxy
            baseVisitFloor n trajectory < epsilon :=
    hupper.trans_lt hrateN
  have hvalueLower : -epsilon <
      explicitPolynomialPrefixAverageRealizedBehaviorRegretProcess mdp
        initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor n trajectory :=
    (neg_lt_neg hradiusN).trans hlower
  have habs :
      |explicitPolynomialPrefixAverageRealizedBehaviorRegretProcess mdp
        initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor n trajectory| < epsilon :=
    (abs_lt).2 ⟨hvalueLower, hvalueUpper⟩
  have hdistLt : dist
      (explicitPolynomialPrefixAverageRealizedBehaviorRegretProcess mdp
        initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor n trajectory) 0 < epsilon := by
    simpa [Real.dist_eq] using habs
  exact (not_lt_of_ge hdistance) hdistLt

/-- Eventually every fixed distance probability is bounded by the exact budget. -/
theorem
    eventually_explicitPolynomialPrefixAverageRealizedBehaviorRegretDistanceViolationProbability_le_failureBudget
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
    ∀ᶠ n in atTop,
      explicitPolynomialPrefixAverageRealizedBehaviorRegretDistanceViolationProbability
          mdp initialState rewardSource initialTable defaultState varianceProxy
            baseVisitFloor epsilon n <=
        explicitPolynomialPrefixTailModelReturnFailureBudget mdp n := by
  have hsubset :=
    eventually_explicitPolynomialPrefixAverageRealizedBehaviorRegretDistanceViolationSet_subset_event
      mdp initialState rewardSource varianceProxy hvarianceProxy law
        initialTable defaultState support baseVisitFloor hbaseFloor
          hrewardBound hhorizon hbaseVisitFloor epsilon hepsilon
  filter_upwards [hsubset] with n hn
  unfold
    explicitPolynomialPrefixAverageRealizedBehaviorRegretDistanceViolationProbability
  exact (measure_mono hn).trans
    (selfConsistentScheduledCausalSource_trajectoryMeasure_explicitPolynomialPrefixTailModelReturnBadEvent_le
      mdp initialState rewardSource varianceProxy hvarianceProxy law
        initialTable defaultState support baseVisitFloor hbaseFloor
          hrewardBound hhorizon hbaseVisitFloor n)

/-- The scheduled distance-violation probability vanishes at every positive threshold. -/
theorem
    explicitPolynomialPrefixAverageRealizedBehaviorRegretDistanceViolationProbability_tendsto_zero
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
    Tendsto
      (explicitPolynomialPrefixAverageRealizedBehaviorRegretDistanceViolationProbability
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor epsilon) atTop (nhds 0) := by
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le'
    tendsto_const_nhds
    (explicitPolynomialPrefixTailModelReturnFailureBudget_tendsto_zero mdp)
    (Eventually.of_forall fun _ => bot_le)
    (eventually_explicitPolynomialPrefixAverageRealizedBehaviorRegretDistanceViolationProbability_le_failureBudget
      mdp initialState rewardSource varianceProxy hvarianceProxy law
        initialTable defaultState support baseVisitFloor hbaseFloor
          hrewardBound hhorizon hbaseVisitFloor epsilon hepsilon)

/-
Terminal route: the equal-round-weighted natural realized behavior regret on
the explicit fourth-power prefixes converges absolutely in measure to zero.
-/
theorem
    selfConsistentScheduledCausalSource_explicitPolynomialPrefixAverageRealizedBehaviorRegret_tendstoInMeasure_zero
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
      explicitPolynomialPrefixAverageRealizedBehaviorRegretProcess mdp
        initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor
    (forall n, Measurable (process n)) /\
    (forall epsilon, 0 < epsilon ->
      (forall n, MeasurableSet
        (explicitPolynomialPrefixAverageRealizedBehaviorRegretDistanceViolationSet
          mdp initialState rewardSource initialTable defaultState varianceProxy
            baseVisitFloor epsilon n)) /\
      (∀ᶠ n in atTop,
        explicitPolynomialPrefixAverageRealizedBehaviorRegretDistanceViolationSet
            mdp initialState rewardSource initialTable defaultState varianceProxy
              baseVisitFloor epsilon n ⊆
          explicitPolynomialPrefixTailModelReturnBadEvent mdp initialState
              rewardSource initialTable defaultState varianceProxy
                baseVisitFloor n /\
        explicitPolynomialPrefixAverageRealizedBehaviorRegretDistanceViolationProbability
            mdp initialState rewardSource initialTable defaultState varianceProxy
              baseVisitFloor epsilon n <=
          explicitPolynomialPrefixTailModelReturnFailureBudget mdp n) /\
      Tendsto
        (explicitPolynomialPrefixAverageRealizedBehaviorRegretDistanceViolationProbability
          mdp initialState rewardSource initialTable defaultState varianceProxy
            baseVisitFloor epsilon) atTop (nhds 0)) /\
    TendstoInMeasure source.trajectoryMeasure process atTop (fun _ => 0) := by
  dsimp only
  refine ⟨?_, ?_, ?_⟩
  · intro n
    exact
      measurable_explicitPolynomialPrefixAverageRealizedBehaviorRegretProcess
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor n
  · intro epsilon hepsilon
    refine ⟨?_, ?_, ?_⟩
    · intro n
      exact
        measurableSet_explicitPolynomialPrefixAverageRealizedBehaviorRegretDistanceViolationSet
          mdp initialState rewardSource initialTable defaultState varianceProxy
            baseVisitFloor epsilon n
    · have hsubset :=
        eventually_explicitPolynomialPrefixAverageRealizedBehaviorRegretDistanceViolationSet_subset_event
          mdp initialState rewardSource varianceProxy hvarianceProxy law
            initialTable defaultState support baseVisitFloor hbaseFloor
              hrewardBound hhorizon hbaseVisitFloor epsilon hepsilon
      have hmeasure :=
        eventually_explicitPolynomialPrefixAverageRealizedBehaviorRegretDistanceViolationProbability_le_failureBudget
          mdp initialState rewardSource varianceProxy hvarianceProxy law
            initialTable defaultState support baseVisitFloor hbaseFloor
              hrewardBound hhorizon hbaseVisitFloor epsilon hepsilon
      filter_upwards [hsubset, hmeasure] with n hn hmeasureN
      exact ⟨hn, hmeasureN⟩
    · exact
        explicitPolynomialPrefixAverageRealizedBehaviorRegretDistanceViolationProbability_tendsto_zero
          mdp initialState rewardSource varianceProxy hvarianceProxy law
            initialTable defaultState support baseVisitFloor hbaseFloor
              hrewardBound hhorizon hbaseVisitFloor epsilon hepsilon
  · rw [tendstoInMeasure_iff_dist]
    intro epsilon hepsilon
    change Tendsto
      (explicitPolynomialPrefixAverageRealizedBehaviorRegretDistanceViolationProbability
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor epsilon) atTop (nhds 0)
    exact
      explicitPolynomialPrefixAverageRealizedBehaviorRegretDistanceViolationProbability_tendsto_zero
        mdp initialState rewardSource varianceProxy hvarianceProxy law
          initialTable defaultState support baseVisitFloor hbaseFloor
            hrewardBound hhorizon hbaseVisitFloor epsilon hepsilon

end AdaptiveStochasticSampledEmpiricalOptimisticSource

end BanditRLProof.FiniteHorizonRL
