import BanditRLProof.RL.FiniteHorizonNaturalCausalRealizedBehaviorRegretHighProbabilityExplicitSchedule

/-!
# Scheduled one-sided upper-tail consistency in probability

This module consumes the explicit fourth-power prefix high-probability
terminal. For every fixed positive threshold, the deterministic regret
envelope is eventually below that threshold, so the threshold violation is
contained in the compiled envelope violation and inherits its vanishing exact
failure budget.

The result is one-sided and only follows the deterministic fourth-power prefix
subsequence. It is not absolute TendstoInMeasure, all-prefix, or anytime
control.
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

/-- Fixed-threshold upper-tail event for the scheduled average realized regret. -/
noncomputable def
    explicitPolynomialPrefixAverageRealizedBehaviorRegretUpperTailSet
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
    epsilon <
      selfConsistentScheduledNaturalCausalAverageRealizedBehaviorRegretProcess
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor (explicitHighProbabilityRounds n) trajectory}

/-- Trajectory probability of the fixed-threshold scheduled upper tail. -/
noncomputable def
    explicitPolynomialPrefixAverageRealizedBehaviorRegretUpperTailProbability
    (mdp : MDP State Action) (initialState : Measure State)
    [IsProbabilityMeasure initialState]
    (rewardSource : mdp.MeanCompatibleRewardKernel)
    (initialTable : DeterministicMarkovPolicyTable mdp)
    (defaultState : State) (varianceProxy : NNReal)
    (baseVisitFloor epsilon : Real) (n : Nat) : ENNReal :=
  let source := selfConsistentScheduledCausalSource mdp initialState
    rewardSource initialTable defaultState varianceProxy baseVisitFloor
  source.trajectoryMeasure
    (explicitPolynomialPrefixAverageRealizedBehaviorRegretUpperTailSet mdp
      initialState rewardSource initialTable defaultState varianceProxy
        baseVisitFloor epsilon n)

/-- Every fixed-threshold scheduled upper-tail event is measurable. -/
theorem
    measurableSet_explicitPolynomialPrefixAverageRealizedBehaviorRegretUpperTailSet
    (mdp : MDP State Action) (initialState : Measure State)
    [IsProbabilityMeasure initialState]
    (rewardSource : mdp.MeanCompatibleRewardKernel)
    (initialTable : DeterministicMarkovPolicyTable mdp)
    (defaultState : State) (varianceProxy : NNReal)
    (baseVisitFloor epsilon : Real) (n : Nat) :
    MeasurableSet
      (explicitPolynomialPrefixAverageRealizedBehaviorRegretUpperTailSet mdp
        initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor epsilon n) := by
  unfold
    explicitPolynomialPrefixAverageRealizedBehaviorRegretUpperTailSet
  exact measurableSet_lt measurable_const
    (measurable_selfConsistentScheduledNaturalCausalAverageRealizedBehaviorRegretProcess
      mdp initialState rewardSource initialTable defaultState varianceProxy
        baseVisitFloor (explicitHighProbabilityRounds n))

/--
Once the deterministic envelope is below a positive fixed threshold, the
fixed-threshold upper tail is contained in the compiled envelope violation.
-/
theorem
    eventually_explicitPolynomialPrefixAverageRealizedBehaviorRegretUpperTailSet_subset_violationSet
    (mdp : MDP State Action) (initialState : Measure State)
    [IsProbabilityMeasure initialState]
    (rewardSource : mdp.MeanCompatibleRewardKernel)
    (initialTable : DeterministicMarkovPolicyTable mdp)
    (defaultState : State) (varianceProxy : NNReal)
    (baseVisitFloor epsilon : Real) (hepsilon : 0 < epsilon) :
    ∀ᶠ n in atTop,
      explicitPolynomialPrefixAverageRealizedBehaviorRegretUpperTailSet mdp
          initialState rewardSource initialTable defaultState varianceProxy
            baseVisitFloor epsilon n ⊆
        explicitPolynomialPrefixAverageRealizedBehaviorRegretViolationSet mdp
          initialState rewardSource initialTable defaultState varianceProxy
            baseVisitFloor n := by
  have hrate :=
    explicitPolynomialPrefixAverageRealizedBehaviorRegretRate_tendsto_zero
      mdp varianceProxy baseVisitFloor
  filter_upwards [hrate.eventually_lt_const hepsilon] with n hn
  intro trajectory htrajectory
  change epsilon <
    selfConsistentScheduledNaturalCausalAverageRealizedBehaviorRegretProcess
      mdp initialState rewardSource initialTable defaultState varianceProxy
        baseVisitFloor (explicitHighProbabilityRounds n) trajectory at htrajectory
  change explicitPolynomialPrefixAverageRealizedBehaviorRegretRate
      mdp varianceProxy baseVisitFloor n <
    selfConsistentScheduledNaturalCausalAverageRealizedBehaviorRegretProcess
      mdp initialState rewardSource initialTable defaultState varianceProxy
        baseVisitFloor (explicitHighProbabilityRounds n) trajectory
  exact hn.trans htrajectory

/-- Direct projection of the compiled scheduled violation probability bound. -/
theorem
    selfConsistentScheduledCausalSource_trajectoryMeasure_explicitPolynomialPrefixAverageRealizedBehaviorRegretViolationSet_le
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
        (explicitPolynomialPrefixAverageRealizedBehaviorRegretViolationSet mdp
          initialState rewardSource initialTable defaultState varianceProxy
            baseVisitFloor n) <=
      explicitPolynomialPrefixTailModelReturnFailureBudget mdp n := by
  dsimp only
  have hcert :=
    selfConsistentScheduledCausalSource_explicitPolynomialPrefixHighProbabilityAverageRealizedBehaviorRegretConsistency
      mdp initialState rewardSource varianceProxy hvarianceProxy law
        initialTable defaultState support baseVisitFloor hbaseFloor
          hrewardBound hhorizon hbaseVisitFloor
  dsimp only at hcert
  exact (hcert.2.2.2 n).2.2.2.2.1

/-- Eventually every fixed positive upper tail is bounded by the exact budget. -/
theorem
    eventually_explicitPolynomialPrefixAverageRealizedBehaviorRegretUpperTailProbability_le_failureBudget
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
      explicitPolynomialPrefixAverageRealizedBehaviorRegretUpperTailProbability
          mdp initialState rewardSource initialTable defaultState varianceProxy
            baseVisitFloor epsilon n <=
        explicitPolynomialPrefixTailModelReturnFailureBudget mdp n := by
  have hsubset :=
    eventually_explicitPolynomialPrefixAverageRealizedBehaviorRegretUpperTailSet_subset_violationSet
      mdp initialState rewardSource initialTable defaultState varianceProxy
        baseVisitFloor epsilon hepsilon
  filter_upwards [hsubset] with n hn
  unfold
    explicitPolynomialPrefixAverageRealizedBehaviorRegretUpperTailProbability
  exact (measure_mono hn).trans
    (selfConsistentScheduledCausalSource_trajectoryMeasure_explicitPolynomialPrefixAverageRealizedBehaviorRegretViolationSet_le
      mdp initialState rewardSource varianceProxy hvarianceProxy law
        initialTable defaultState support baseVisitFloor hbaseFloor
          hrewardBound hhorizon hbaseVisitFloor n)

/-- The fixed-positive-threshold scheduled upper-tail probability vanishes. -/
theorem
    explicitPolynomialPrefixAverageRealizedBehaviorRegretUpperTailProbability_tendsto_zero
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
      (explicitPolynomialPrefixAverageRealizedBehaviorRegretUpperTailProbability
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor epsilon) atTop (nhds 0) := by
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le'
    tendsto_const_nhds
    (explicitPolynomialPrefixTailModelReturnFailureBudget_tendsto_zero mdp)
    (Eventually.of_forall fun _ => bot_le)
    (eventually_explicitPolynomialPrefixAverageRealizedBehaviorRegretUpperTailProbability_le_failureBudget
      mdp initialState rewardSource varianceProxy hvarianceProxy law
        initialTable defaultState support baseVisitFloor hbaseFloor
          hrewardBound hhorizon hbaseVisitFloor epsilon hepsilon)

/--
All fixed positive one-sided upper-tail probabilities vanish on the same
explicit fourth-power prefix subsequence.
-/
theorem
    selfConsistentScheduledCausalSource_explicitPolynomialPrefixAverageRealizedBehaviorRegretUpperTailInProbability
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
    forall epsilon, 0 < epsilon ->
      (forall n,
        MeasurableSet
          (explicitPolynomialPrefixAverageRealizedBehaviorRegretUpperTailSet
            mdp initialState rewardSource initialTable defaultState
              varianceProxy baseVisitFloor epsilon n)) /\
      (∀ᶠ n in atTop,
        explicitPolynomialPrefixAverageRealizedBehaviorRegretUpperTailSet mdp
            initialState rewardSource initialTable defaultState varianceProxy
              baseVisitFloor epsilon n ⊆
          explicitPolynomialPrefixAverageRealizedBehaviorRegretViolationSet mdp
            initialState rewardSource initialTable defaultState varianceProxy
              baseVisitFloor n /\
        explicitPolynomialPrefixAverageRealizedBehaviorRegretUpperTailProbability
            mdp initialState rewardSource initialTable defaultState varianceProxy
              baseVisitFloor epsilon n <=
          explicitPolynomialPrefixTailModelReturnFailureBudget mdp n) /\
      Tendsto
        (explicitPolynomialPrefixAverageRealizedBehaviorRegretUpperTailProbability
          mdp initialState rewardSource initialTable defaultState varianceProxy
            baseVisitFloor epsilon) atTop (nhds 0) := by
  intro epsilon hepsilon
  refine ⟨?_, ?_, ?_⟩
  · intro n
    exact
      measurableSet_explicitPolynomialPrefixAverageRealizedBehaviorRegretUpperTailSet
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor epsilon n
  · have hsubset :=
      eventually_explicitPolynomialPrefixAverageRealizedBehaviorRegretUpperTailSet_subset_violationSet
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor epsilon hepsilon
    have hmeasure :=
      eventually_explicitPolynomialPrefixAverageRealizedBehaviorRegretUpperTailProbability_le_failureBudget
        mdp initialState rewardSource varianceProxy hvarianceProxy law
          initialTable defaultState support baseVisitFloor hbaseFloor
            hrewardBound hhorizon hbaseVisitFloor epsilon hepsilon
    filter_upwards [hsubset, hmeasure] with n hn hmeasureN
    exact ⟨hn, hmeasureN⟩
  · exact
      explicitPolynomialPrefixAverageRealizedBehaviorRegretUpperTailProbability_tendsto_zero
        mdp initialState rewardSource varianceProxy hvarianceProxy law
          initialTable defaultState support baseVisitFloor hbaseFloor
            hrewardBound hhorizon hbaseVisitFloor epsilon hepsilon

end AdaptiveStochasticSampledEmpiricalOptimisticSource

end BanditRLProof.FiniteHorizonRL
