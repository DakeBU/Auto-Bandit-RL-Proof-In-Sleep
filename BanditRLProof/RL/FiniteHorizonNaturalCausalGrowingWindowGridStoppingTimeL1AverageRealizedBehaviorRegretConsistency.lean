import BanditRLProof.ExpectationBochnerSums
import BanditRLProof.RL.FiniteHorizonNaturalCausalAverageRealizedBehaviorRegretAlmostSureExplicitSchedule
import BanditRLProof.RL.FiniteHorizonNaturalCausalBoundedWindowStoppingTimeL1AverageRealizedBehaviorRegretConsistency

/-!
# Growing-window grid stopping-time L1 natural causal consistency

This module transports the compiled natural-causal L1 process through stopping
families whose values lie in a growing finite window of the fourth-power prefix
grid.  Every finite candidate sum is dominated by the infinite tail of the
compiled summable grid envelope, so the window width may grow arbitrarily.

The result is restricted to the explicit fourth-power grid.  It does not prove
L1 convergence for an arbitrary growing interval of raw natural prefixes, and
it uses neither an optional-stopping identity nor independence.
-/

open Filter MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal ProbabilityTheory Topology

namespace BanditRLProof.FiniteHorizonRL

universe u v

variable {State : Type u} {Action : Type v}
    [MeasurableSpace State] [MeasurableSpace Action]
    [Fintype State] [Fintype Action]
    [DecidableEq State] [DecidableEq Action]
    [MeasurableSingletonClass State] [MeasurableSingletonClass Action]
    [Nonempty State] [Nonempty Action]

namespace AdaptiveStochasticSampledEmpiricalOptimisticSource

/-- The explicit fourth-power prefix grid is monotone in its index. -/
theorem explicitHighProbabilityRounds_mono {left right : Nat}
    (hle : left <= right) :
    explicitHighProbabilityRounds left <= explicitHighProbabilityRounds right := by
  unfold explicitHighProbabilityRounds explicitHighProbabilityScale
  exact Nat.pow_le_pow_left (by omega) 4

/-- Every explicit fourth-power prefix at index `n + offset` dominates `n`. -/
theorem scheduleIndex_le_explicitHighProbabilityRounds_add
    (scheduleIndex offset : Nat) :
    scheduleIndex <= explicitHighProbabilityRounds (scheduleIndex + offset) := by
  calc
    scheduleIndex <= scheduleIndex + offset + 1 := by omega
    _ <= (scheduleIndex + offset + 1) ^ 4 := Nat.le_pow (by norm_num)

/-- A grid-valued stopping prefix selects one finite window offset after `untopA`. -/
theorem exists_growingWindowGrid_offset_untopA_eq
    {Omega : Type*} (stoppingPrefix : Nat -> Omega -> WithTop Nat)
    (windowAt : Nat -> Nat)
    (hgrid : forall scheduleIndex trajectory,
      exists offset, offset ∈ Finset.range (windowAt scheduleIndex + 1) /\
        stoppingPrefix scheduleIndex trajectory =
          (explicitHighProbabilityRounds (scheduleIndex + offset) : WithTop Nat))
    (scheduleIndex : Nat) (trajectory : Omega) :
    exists offset, offset ∈ Finset.range (windowAt scheduleIndex + 1) /\
      (stoppingPrefix scheduleIndex trajectory).untopA =
        explicitHighProbabilityRounds (scheduleIndex + offset) := by
  obtain ⟨offset, hoffset, hvalue⟩ := hgrid scheduleIndex trajectory
  refine ⟨offset, hoffset, ?_⟩
  rw [hvalue]
  let rounds := explicitHighProbabilityRounds (scheduleIndex + offset)
  have hne : (rounds : WithTop Nat) ≠ ⊤ := WithTop.coe_ne_top
  have hcoe : ((((rounds : WithTop Nat).untopA : Nat) : WithTop Nat)) =
      (rounds : WithTop Nat) := by
    rw [WithTop.untopA_eq_untop hne]
    exact WithTop.coe_untop _ hne
  exact_mod_cast hcoe

/-- Every grid-valued stopping prefix has a pointwise finite upper bound. -/
theorem growingWindowGrid_stoppingPrefix_le
    {Omega : Type*} (stoppingPrefix : Nat -> Omega -> WithTop Nat)
    (windowAt : Nat -> Nat)
    (hgrid : forall scheduleIndex trajectory,
      exists offset, offset ∈ Finset.range (windowAt scheduleIndex + 1) /\
        stoppingPrefix scheduleIndex trajectory =
          (explicitHighProbabilityRounds (scheduleIndex + offset) : WithTop Nat))
    (scheduleIndex : Nat) (trajectory : Omega) :
    stoppingPrefix scheduleIndex trajectory <=
      (explicitHighProbabilityRounds (scheduleIndex + windowAt scheduleIndex) :
        WithTop Nat) := by
  obtain ⟨offset, hoffset, hvalue⟩ := hgrid scheduleIndex trajectory
  rw [hvalue]
  exact_mod_cast explicitHighProbabilityRounds_mono
    (Nat.add_le_add_left (Nat.le_of_lt_succ (Finset.mem_range.mp hoffset)) scheduleIndex)

/-- Finite L1 budget for a window of fourth-power grid candidates. -/
noncomputable def
    selfConsistentScheduledNaturalCausalGrowingWindowGridStoppingL1Budget
    (mdp : MDP State Action) (varianceProxy : NNReal)
    (windowAt : Nat -> Nat) (scheduleIndex : Nat) : Real :=
  (Finset.range (windowAt scheduleIndex + 1)).sum fun offset =>
    explicitPolynomialPrefixAverageRealizedBehaviorRegretL1SummableEnvelope
      mdp varianceProxy (scheduleIndex + offset)

/-- Infinite shifted tail controlling every finite grid window. -/
noncomputable def
    selfConsistentScheduledNaturalCausalGrowingWindowGridStoppingL1Tail
    (mdp : MDP State Action) (varianceProxy : NNReal)
    (scheduleIndex : Nat) : Real :=
  ∑' offset,
    explicitPolynomialPrefixAverageRealizedBehaviorRegretL1SummableEnvelope
      mdp varianceProxy (offset + scheduleIndex)

omit [DecidableEq State] [DecidableEq Action]
    [MeasurableSingletonClass State] [MeasurableSingletonClass Action]
    [Nonempty State] [Nonempty Action] in
/-- Every finite growing-window grid budget is nonnegative. -/
theorem selfConsistentScheduledNaturalCausalGrowingWindowGridStoppingL1Budget_nonneg
    (mdp : MDP State Action) (varianceProxy : NNReal)
    (windowAt : Nat -> Nat) (scheduleIndex : Nat) :
    0 <= selfConsistentScheduledNaturalCausalGrowingWindowGridStoppingL1Budget
      mdp varianceProxy windowAt scheduleIndex := by
  exact Finset.sum_nonneg fun offset _ =>
    explicitPolynomialPrefixAverageRealizedBehaviorRegretL1SummableEnvelope_nonneg
      mdp varianceProxy (scheduleIndex + offset)

omit [DecidableEq State] [DecidableEq Action]
    [MeasurableSingletonClass State] [MeasurableSingletonClass Action]
    [Nonempty State] [Nonempty Action] in
/-- Every finite grid-window budget is bounded by the full shifted tail. -/
theorem selfConsistentScheduledNaturalCausalGrowingWindowGridStoppingL1Budget_le_tail
    (mdp : MDP State Action) (varianceProxy : NNReal)
    (windowAt : Nat -> Nat) (scheduleIndex : Nat) :
    selfConsistentScheduledNaturalCausalGrowingWindowGridStoppingL1Budget
        mdp varianceProxy windowAt scheduleIndex <=
      selfConsistentScheduledNaturalCausalGrowingWindowGridStoppingL1Tail
        mdp varianceProxy scheduleIndex := by
  let envelope :=
    explicitPolynomialPrefixAverageRealizedBehaviorRegretL1SummableEnvelope
      mdp varianceProxy
  have hsummable : Summable envelope :=
    summable_explicitPolynomialPrefixAverageRealizedBehaviorRegretL1SummableEnvelope
      mdp varianceProxy
  have hshift : Summable (fun offset => envelope (offset + scheduleIndex)) :=
    (summable_nat_add_iff scheduleIndex).2 hsummable
  simpa [selfConsistentScheduledNaturalCausalGrowingWindowGridStoppingL1Budget,
    selfConsistentScheduledNaturalCausalGrowingWindowGridStoppingL1Tail,
    envelope, Nat.add_comm] using
    hshift.sum_le_tsum (Finset.range (windowAt scheduleIndex + 1))
      (fun offset _ =>
        explicitPolynomialPrefixAverageRealizedBehaviorRegretL1SummableEnvelope_nonneg
          mdp varianceProxy (offset + scheduleIndex))

omit [DecidableEq State] [DecidableEq Action]
    [MeasurableSingletonClass State] [MeasurableSingletonClass Action]
    [Nonempty State] [Nonempty Action] in
/-- The infinite shifted grid-envelope tail tends to zero. -/
theorem selfConsistentScheduledNaturalCausalGrowingWindowGridStoppingL1Tail_tendsto_zero
    (mdp : MDP State Action) (varianceProxy : NNReal) :
    Tendsto
      (selfConsistentScheduledNaturalCausalGrowingWindowGridStoppingL1Tail
        mdp varianceProxy) atTop (nhds 0) := by
  simpa [selfConsistentScheduledNaturalCausalGrowingWindowGridStoppingL1Tail] using
    tendsto_sum_nat_add
      (explicitPolynomialPrefixAverageRealizedBehaviorRegretL1SummableEnvelope
        mdp varianceProxy)

omit [DecidableEq State] [DecidableEq Action]
    [MeasurableSingletonClass State] [MeasurableSingletonClass Action]
    [Nonempty State] [Nonempty Action] in
/-- Any finite grid-window budget vanishes, even when its width grows. -/
theorem selfConsistentScheduledNaturalCausalGrowingWindowGridStoppingL1Budget_tendsto_zero
    (mdp : MDP State Action) (varianceProxy : NNReal)
    (windowAt : Nat -> Nat) :
    Tendsto
      (selfConsistentScheduledNaturalCausalGrowingWindowGridStoppingL1Budget
        mdp varianceProxy windowAt) atTop (nhds 0) := by
  apply squeeze_zero'
  · exact Filter.Eventually.of_forall fun scheduleIndex =>
      selfConsistentScheduledNaturalCausalGrowingWindowGridStoppingL1Budget_nonneg
        mdp varianceProxy windowAt scheduleIndex
  · exact Filter.Eventually.of_forall fun scheduleIndex =>
      selfConsistentScheduledNaturalCausalGrowingWindowGridStoppingL1Budget_le_tail
        mdp varianceProxy windowAt scheduleIndex
  · exact
      selfConsistentScheduledNaturalCausalGrowingWindowGridStoppingL1Tail_tendsto_zero
        mdp varianceProxy

/-- Expected absolute value of the growing-window grid-stopped process. -/
noncomputable def
    selfConsistentScheduledNaturalCausalExpectedAbsoluteGrowingWindowGridStoppingAverageRealizedBehaviorRegret
    (mdp : MDP State Action) (initialState : Measure State)
    [IsProbabilityMeasure initialState]
    (rewardSource : mdp.MeanCompatibleRewardKernel)
    (initialTable : DeterministicMarkovPolicyTable mdp)
    (defaultState : State) (varianceProxy : NNReal)
    (baseVisitFloor : Real)
    (stoppingPrefix : Nat ->
      HeterogeneousStochasticEpisodeBatchTrajectory mdp
        (fun t =>
          AdaptiveStochasticEpisodeBatchSource.selfConsistentScheduledEpisodes
            mdp varianceProxy baseVisitFloor t) -> WithTop Nat)
    (scheduleIndex : Nat) : Real :=
  integral
    (selfConsistentScheduledCausalSource mdp initialState rewardSource
      initialTable defaultState varianceProxy baseVisitFloor).trajectoryMeasure
    (fun trajectory =>
      |selfConsistentScheduledNaturalCausalStoppingTimeAverageRealizedBehaviorRegretProcess
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor stoppingPrefix scheduleIndex trajectory|)

/-- Every grid-window stopped coordinate belongs to `L1`. -/
theorem memLp_one_selfConsistentScheduledNaturalCausalGrowingWindowGridStoppingAverageRealizedBehaviorRegret
    (mdp : MDP State Action) (initialState : Measure State)
    [IsProbabilityMeasure initialState]
    [StandardBorelSpace State] [StandardBorelSpace Action]
    (rewardSource : mdp.MeanCompatibleRewardKernel)
    (varianceProxy : NNReal)
    (law : rewardSource.UniformSubgaussianRewardLaw varianceProxy)
    (initialTable : DeterministicMarkovPolicyTable mdp)
    (defaultState : State) (baseVisitFloor : Real)
    (hrewardBound : forall state action, |mdp.reward state action| <= 1)
    (stoppingPrefix : Nat ->
      HeterogeneousStochasticEpisodeBatchTrajectory mdp
        (fun t =>
          AdaptiveStochasticEpisodeBatchSource.selfConsistentScheduledEpisodes
            mdp varianceProxy baseVisitFloor t) -> WithTop Nat)
    (hstopping : forall scheduleIndex, IsStoppingTime
      (selfConsistentScheduledNaturalCausalTrajectoryFiltration mdp initialState
        rewardSource initialTable defaultState varianceProxy baseVisitFloor)
      (stoppingPrefix scheduleIndex))
    (windowAt : Nat -> Nat)
    (hgrid : forall scheduleIndex trajectory,
      exists offset, offset ∈ Finset.range (windowAt scheduleIndex + 1) /\
        stoppingPrefix scheduleIndex trajectory =
          (explicitHighProbabilityRounds (scheduleIndex + offset) : WithTop Nat))
    (scheduleIndex : Nat) :
    MemLp
      (selfConsistentScheduledNaturalCausalStoppingTimeAverageRealizedBehaviorRegretProcess
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor stoppingPrefix scheduleIndex)
      1
      (selfConsistentScheduledCausalSource mdp initialState rewardSource
        initialTable defaultState varianceProxy baseVisitFloor).trajectoryMeasure := by
  exact memLp_stoppedValue (hstopping scheduleIndex)
    (fun rounds =>
      memLp_one_selfConsistentScheduledNaturalCausalAverageRealizedBehaviorRegretProcess
        mdp initialState rewardSource varianceProxy law initialTable defaultState
          baseVisitFloor hrewardBound rounds)
    (fun trajectory =>
      growingWindowGrid_stoppingPrefix_le stoppingPrefix windowAt hgrid
        scheduleIndex trajectory)

/-- Expected absolute growing-window grid-stopped regret is nonnegative. -/
theorem
    selfConsistentScheduledNaturalCausalExpectedAbsoluteGrowingWindowGridStoppingAverageRealizedBehaviorRegret_nonneg
    (mdp : MDP State Action) (initialState : Measure State)
    [IsProbabilityMeasure initialState]
    (rewardSource : mdp.MeanCompatibleRewardKernel)
    (initialTable : DeterministicMarkovPolicyTable mdp)
    (defaultState : State) (varianceProxy : NNReal)
    (baseVisitFloor : Real)
    (stoppingPrefix : Nat ->
      HeterogeneousStochasticEpisodeBatchTrajectory mdp
        (fun t =>
          AdaptiveStochasticEpisodeBatchSource.selfConsistentScheduledEpisodes
            mdp varianceProxy baseVisitFloor t) -> WithTop Nat)
    (scheduleIndex : Nat) :
    0 <=
      selfConsistentScheduledNaturalCausalExpectedAbsoluteGrowingWindowGridStoppingAverageRealizedBehaviorRegret
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor stoppingPrefix scheduleIndex := by
  unfold selfConsistentScheduledNaturalCausalExpectedAbsoluteGrowingWindowGridStoppingAverageRealizedBehaviorRegret
  exact integral_nonneg fun _ => abs_nonneg _

/-- The selected grid coordinate is bounded by the finite candidate budget. -/
theorem
    selfConsistentScheduledNaturalCausalExpectedAbsoluteGrowingWindowGridStoppingAverageRealizedBehaviorRegret_le_budget
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
    (stoppingPrefix : Nat ->
      HeterogeneousStochasticEpisodeBatchTrajectory mdp
        (fun t =>
          AdaptiveStochasticEpisodeBatchSource.selfConsistentScheduledEpisodes
            mdp varianceProxy baseVisitFloor t) -> WithTop Nat)
    (hstopping : forall scheduleIndex, IsStoppingTime
      (selfConsistentScheduledNaturalCausalTrajectoryFiltration mdp initialState
        rewardSource initialTable defaultState varianceProxy baseVisitFloor)
      (stoppingPrefix scheduleIndex))
    (windowAt : Nat -> Nat)
    (hgrid : forall scheduleIndex trajectory,
      exists offset, offset ∈ Finset.range (windowAt scheduleIndex + 1) /\
        stoppingPrefix scheduleIndex trajectory =
          (explicitHighProbabilityRounds (scheduleIndex + offset) : WithTop Nat))
    (scheduleIndex : Nat) :
    selfConsistentScheduledNaturalCausalExpectedAbsoluteGrowingWindowGridStoppingAverageRealizedBehaviorRegret
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor stoppingPrefix scheduleIndex <=
      selfConsistentScheduledNaturalCausalGrowingWindowGridStoppingL1Budget
        mdp varianceProxy windowAt scheduleIndex := by
  let source := selfConsistentScheduledCausalSource mdp initialState
    rewardSource initialTable defaultState varianceProxy baseVisitFloor
  let mu := source.trajectoryMeasure
  let process :=
    selfConsistentScheduledNaturalCausalAverageRealizedBehaviorRegretProcess mdp
      initialState rewardSource initialTable defaultState varianceProxy
        baseVisitFloor
  let stoppedProcess :=
    selfConsistentScheduledNaturalCausalStoppingTimeAverageRealizedBehaviorRegretProcess
      mdp initialState rewardSource initialTable defaultState varianceProxy
        baseVisitFloor stoppingPrefix
  have hcoordinateIntegrable : forall rounds,
      Integrable (fun trajectory => |process rounds trajectory|) mu := by
    intro rounds
    exact
      (integrable_selfConsistentScheduledNaturalCausalAverageRealizedBehaviorRegretProcess
        mdp initialState rewardSource varianceProxy law initialTable defaultState
          baseVisitFloor hrewardBound rounds).abs
  have hsumIntegrable : Integrable
      (fun trajectory =>
        (Finset.range (windowAt scheduleIndex + 1)).sum fun offset =>
          |process (explicitHighProbabilityRounds (scheduleIndex + offset))
            trajectory|) mu := by
    exact IntegrabilitySums.integrable_finset_sum mu
      (Finset.range (windowAt scheduleIndex + 1))
      (fun offset trajectory =>
        |process (explicitHighProbabilityRounds (scheduleIndex + offset)) trajectory|)
      (fun offset _ =>
        hcoordinateIntegrable
          (explicitHighProbabilityRounds (scheduleIndex + offset)))
  have hstoppedIntegrable : Integrable
      (fun trajectory => |stoppedProcess scheduleIndex trajectory|) mu := by
    have hmem :=
      memLp_one_selfConsistentScheduledNaturalCausalGrowingWindowGridStoppingAverageRealizedBehaviorRegret
        mdp initialState rewardSource varianceProxy law initialTable defaultState
          baseVisitFloor hrewardBound stoppingPrefix hstopping windowAt hgrid
            scheduleIndex
    rw [memLp_one_iff_integrable] at hmem
    exact hmem.abs
  have hpoint : forall trajectory,
      |stoppedProcess scheduleIndex trajectory| <=
        (Finset.range (windowAt scheduleIndex + 1)).sum fun offset =>
          |process (explicitHighProbabilityRounds (scheduleIndex + offset))
            trajectory| := by
    intro trajectory
    obtain ⟨offset, hoffset, hoffsetEq⟩ :=
      exists_growingWindowGrid_offset_untopA_eq stoppingPrefix windowAt hgrid
        scheduleIndex trajectory
    change |process (stoppingPrefix scheduleIndex trajectory).untopA trajectory| <= _
    rw [hoffsetEq]
    exact Finset.single_le_sum
      (fun candidate _ => abs_nonneg
        (process (explicitHighProbabilityRounds (scheduleIndex + candidate))
          trajectory)) hoffset
  calc
    selfConsistentScheduledNaturalCausalExpectedAbsoluteGrowingWindowGridStoppingAverageRealizedBehaviorRegret
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor stoppingPrefix scheduleIndex =
        integral mu (fun trajectory => |stoppedProcess scheduleIndex trajectory|) := by
      rfl
    _ <= integral mu (fun trajectory =>
        (Finset.range (windowAt scheduleIndex + 1)).sum fun offset =>
          |process (explicitHighProbabilityRounds (scheduleIndex + offset))
            trajectory|) :=
      integral_mono hstoppedIntegrable hsumIntegrable hpoint
    _ = (Finset.range (windowAt scheduleIndex + 1)).sum fun offset =>
        integral mu (fun trajectory =>
          |process (explicitHighProbabilityRounds (scheduleIndex + offset))
            trajectory|) := by
      exact ExpectationBochnerSums.integral_finset_sum mu
        (Finset.range (windowAt scheduleIndex + 1))
        (fun offset trajectory =>
          |process (explicitHighProbabilityRounds (scheduleIndex + offset)) trajectory|)
        (fun offset _ =>
          hcoordinateIntegrable
            (explicitHighProbabilityRounds (scheduleIndex + offset)))
    _ <= (Finset.range (windowAt scheduleIndex + 1)).sum fun offset =>
        explicitPolynomialPrefixAverageRealizedBehaviorRegretL1SummableEnvelope
          mdp varianceProxy (scheduleIndex + offset) := by
      apply Finset.sum_le_sum
      intro offset _
      calc
        integral mu (fun trajectory =>
            |process (explicitHighProbabilityRounds (scheduleIndex + offset))
              trajectory|) <=
          selfConsistentScheduledNaturalCausalAverageRealizedBehaviorRegretL1Envelope
            mdp varianceProxy baseVisitFloor
              (explicitHighProbabilityRounds (scheduleIndex + offset)) := by
            simpa [process, mu, source,
              selfConsistentScheduledNaturalCausalExpectedAbsoluteAverageRealizedBehaviorRegret]
              using
                selfConsistentScheduledNaturalCausalExpectedAbsoluteAverageRealizedBehaviorRegret_le_L1Envelope
                  mdp initialState rewardSource varianceProxy hvarianceProxy law
                    initialTable defaultState support baseVisitFloor hbaseFloor
                      hrewardBound hhorizon hbaseVisitFloor
                        (explicitHighProbabilityRounds (scheduleIndex + offset))
        _ <=
          explicitPolynomialPrefixAverageRealizedBehaviorRegretL1SummableEnvelope
            mdp varianceProxy (scheduleIndex + offset) :=
          selfConsistentScheduledNaturalCausalAverageRealizedBehaviorRegretL1Envelope_explicitRounds_le_summableEnvelope
            mdp varianceProxy baseVisitFloor (scheduleIndex + offset)
    _ = selfConsistentScheduledNaturalCausalGrowingWindowGridStoppingL1Budget
        mdp varianceProxy windowAt scheduleIndex := rfl

/-- Expected absolute growing-window grid-stopped regret tends to zero. -/
theorem
    selfConsistentScheduledNaturalCausalExpectedAbsoluteGrowingWindowGridStoppingAverageRealizedBehaviorRegret_tendsto_zero
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
    (stoppingPrefix : Nat ->
      HeterogeneousStochasticEpisodeBatchTrajectory mdp
        (fun t =>
          AdaptiveStochasticEpisodeBatchSource.selfConsistentScheduledEpisodes
            mdp varianceProxy baseVisitFloor t) -> WithTop Nat)
    (hstopping : forall scheduleIndex, IsStoppingTime
      (selfConsistentScheduledNaturalCausalTrajectoryFiltration mdp initialState
        rewardSource initialTable defaultState varianceProxy baseVisitFloor)
      (stoppingPrefix scheduleIndex))
    (windowAt : Nat -> Nat)
    (hgrid : forall scheduleIndex trajectory,
      exists offset, offset ∈ Finset.range (windowAt scheduleIndex + 1) /\
        stoppingPrefix scheduleIndex trajectory =
          (explicitHighProbabilityRounds (scheduleIndex + offset) : WithTop Nat)) :
    Tendsto
      (selfConsistentScheduledNaturalCausalExpectedAbsoluteGrowingWindowGridStoppingAverageRealizedBehaviorRegret
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor stoppingPrefix) atTop (nhds 0) := by
  apply squeeze_zero'
  · exact Filter.Eventually.of_forall fun scheduleIndex =>
      selfConsistentScheduledNaturalCausalExpectedAbsoluteGrowingWindowGridStoppingAverageRealizedBehaviorRegret_nonneg
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor stoppingPrefix scheduleIndex
  · exact Filter.Eventually.of_forall fun scheduleIndex =>
      selfConsistentScheduledNaturalCausalExpectedAbsoluteGrowingWindowGridStoppingAverageRealizedBehaviorRegret_le_budget
        mdp initialState rewardSource varianceProxy hvarianceProxy law initialTable
          defaultState support baseVisitFloor hbaseFloor hrewardBound hhorizon
            hbaseVisitFloor stoppingPrefix hstopping windowAt hgrid scheduleIndex
  · exact
      selfConsistentScheduledNaturalCausalGrowingWindowGridStoppingL1Budget_tendsto_zero
        mdp varianceProxy windowAt

/-- At exponent one, the stopped norm is its lifted expected absolute value. -/
theorem
    eLpNorm_one_selfConsistentScheduledNaturalCausalGrowingWindowGridStoppingAverageRealizedBehaviorRegret_eq
    (mdp : MDP State Action) (initialState : Measure State)
    [IsProbabilityMeasure initialState]
    [StandardBorelSpace State] [StandardBorelSpace Action]
    (rewardSource : mdp.MeanCompatibleRewardKernel)
    (varianceProxy : NNReal)
    (law : rewardSource.UniformSubgaussianRewardLaw varianceProxy)
    (initialTable : DeterministicMarkovPolicyTable mdp)
    (defaultState : State) (baseVisitFloor : Real)
    (hrewardBound : forall state action, |mdp.reward state action| <= 1)
    (stoppingPrefix : Nat ->
      HeterogeneousStochasticEpisodeBatchTrajectory mdp
        (fun t =>
          AdaptiveStochasticEpisodeBatchSource.selfConsistentScheduledEpisodes
            mdp varianceProxy baseVisitFloor t) -> WithTop Nat)
    (hstopping : forall scheduleIndex, IsStoppingTime
      (selfConsistentScheduledNaturalCausalTrajectoryFiltration mdp initialState
        rewardSource initialTable defaultState varianceProxy baseVisitFloor)
      (stoppingPrefix scheduleIndex))
    (windowAt : Nat -> Nat)
    (hgrid : forall scheduleIndex trajectory,
      exists offset, offset ∈ Finset.range (windowAt scheduleIndex + 1) /\
        stoppingPrefix scheduleIndex trajectory =
          (explicitHighProbabilityRounds (scheduleIndex + offset) : WithTop Nat))
    (scheduleIndex : Nat) :
    eLpNorm
        (selfConsistentScheduledNaturalCausalStoppingTimeAverageRealizedBehaviorRegretProcess
          mdp initialState rewardSource initialTable defaultState varianceProxy
            baseVisitFloor stoppingPrefix scheduleIndex)
        1
        (selfConsistentScheduledCausalSource mdp initialState rewardSource
          initialTable defaultState varianceProxy baseVisitFloor).trajectoryMeasure =
      ENNReal.ofReal
        (selfConsistentScheduledNaturalCausalExpectedAbsoluteGrowingWindowGridStoppingAverageRealizedBehaviorRegret
          mdp initialState rewardSource initialTable defaultState varianceProxy
            baseVisitFloor stoppingPrefix scheduleIndex) := by
  rw [MemLp.eLpNorm_eq_integral_rpow_norm one_ne_zero ENNReal.one_ne_top
    (memLp_one_selfConsistentScheduledNaturalCausalGrowingWindowGridStoppingAverageRealizedBehaviorRegret
      mdp initialState rewardSource varianceProxy law initialTable defaultState
        baseVisitFloor hrewardBound stoppingPrefix hstopping windowAt hgrid
          scheduleIndex)]
  simp [
    selfConsistentScheduledNaturalCausalExpectedAbsoluteGrowingWindowGridStoppingAverageRealizedBehaviorRegret,
    Real.norm_eq_abs]

/-- The grid-stopped process converges to zero in the exponent-one norm. -/
theorem
    eLpNorm_one_selfConsistentScheduledNaturalCausalGrowingWindowGridStoppingAverageRealizedBehaviorRegret_sub_zero_tendsto_zero
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
    (stoppingPrefix : Nat ->
      HeterogeneousStochasticEpisodeBatchTrajectory mdp
        (fun t =>
          AdaptiveStochasticEpisodeBatchSource.selfConsistentScheduledEpisodes
            mdp varianceProxy baseVisitFloor t) -> WithTop Nat)
    (hstopping : forall scheduleIndex, IsStoppingTime
      (selfConsistentScheduledNaturalCausalTrajectoryFiltration mdp initialState
        rewardSource initialTable defaultState varianceProxy baseVisitFloor)
      (stoppingPrefix scheduleIndex))
    (windowAt : Nat -> Nat)
    (hgrid : forall scheduleIndex trajectory,
      exists offset, offset ∈ Finset.range (windowAt scheduleIndex + 1) /\
        stoppingPrefix scheduleIndex trajectory =
          (explicitHighProbabilityRounds (scheduleIndex + offset) : WithTop Nat)) :
    Tendsto
      (fun scheduleIndex => eLpNorm
        (selfConsistentScheduledNaturalCausalStoppingTimeAverageRealizedBehaviorRegretProcess
            mdp initialState rewardSource initialTable defaultState varianceProxy
              baseVisitFloor stoppingPrefix scheduleIndex -
          (fun _ => 0))
        1
        (selfConsistentScheduledCausalSource mdp initialState rewardSource
          initialTable defaultState varianceProxy baseVisitFloor).trajectoryMeasure)
      atTop (nhds 0) := by
  have hexpected :=
    selfConsistentScheduledNaturalCausalExpectedAbsoluteGrowingWindowGridStoppingAverageRealizedBehaviorRegret_tendsto_zero
      mdp initialState rewardSource varianceProxy hvarianceProxy law initialTable
        defaultState support baseVisitFloor hbaseFloor hrewardBound hhorizon
          hbaseVisitFloor stoppingPrefix hstopping windowAt hgrid
  have hofReal := (ENNReal.continuous_ofReal.tendsto 0).comp hexpected
  have hnorm : Tendsto
      (fun scheduleIndex => eLpNorm
        (selfConsistentScheduledNaturalCausalStoppingTimeAverageRealizedBehaviorRegretProcess
          mdp initialState rewardSource initialTable defaultState varianceProxy
            baseVisitFloor stoppingPrefix scheduleIndex)
        1
        (selfConsistentScheduledCausalSource mdp initialState rewardSource
          initialTable defaultState varianceProxy baseVisitFloor).trajectoryMeasure)
      atTop (nhds 0) := by
    have hnormEq :
        (fun scheduleIndex => eLpNorm
          (selfConsistentScheduledNaturalCausalStoppingTimeAverageRealizedBehaviorRegretProcess
            mdp initialState rewardSource initialTable defaultState varianceProxy
              baseVisitFloor stoppingPrefix scheduleIndex)
          1
          (selfConsistentScheduledCausalSource mdp initialState rewardSource
            initialTable defaultState varianceProxy baseVisitFloor).trajectoryMeasure) =
        (fun scheduleIndex => ENNReal.ofReal
          (selfConsistentScheduledNaturalCausalExpectedAbsoluteGrowingWindowGridStoppingAverageRealizedBehaviorRegret
            mdp initialState rewardSource initialTable defaultState varianceProxy
              baseVisitFloor stoppingPrefix scheduleIndex)) := by
      funext scheduleIndex
      exact
        eLpNorm_one_selfConsistentScheduledNaturalCausalGrowingWindowGridStoppingAverageRealizedBehaviorRegret_eq
          mdp initialState rewardSource varianceProxy law initialTable defaultState
            baseVisitFloor hrewardBound stoppingPrefix hstopping windowAt hgrid
              scheduleIndex
    rw [hnormEq]
    simpa only [Function.comp_apply, ENNReal.ofReal_zero] using hofReal
  convert hnorm using 1
  funext scheduleIndex
  apply eLpNorm_congr_ae
  exact Filter.Eventually.of_forall fun trajectory => by simp

/-
Terminal L1 theorem for an arbitrarily growing finite candidate window on the
explicit fourth-power natural-prefix grid.
-/
theorem
    selfConsistentScheduledCausalSource_growingWindowGridStoppingTimeNaturalAverageRealizedBehaviorRegret_L1_consistency
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
    (stoppingPrefix : Nat ->
      HeterogeneousStochasticEpisodeBatchTrajectory mdp
        (fun t =>
          AdaptiveStochasticEpisodeBatchSource.selfConsistentScheduledEpisodes
            mdp varianceProxy baseVisitFloor t) -> WithTop Nat)
    (hstopping : forall scheduleIndex, IsStoppingTime
      (selfConsistentScheduledNaturalCausalTrajectoryFiltration mdp initialState
        rewardSource initialTable defaultState varianceProxy baseVisitFloor)
      (stoppingPrefix scheduleIndex))
    (windowAt : Nat -> Nat)
    (hwindowAt : Tendsto windowAt atTop atTop)
    (hgrid : forall scheduleIndex trajectory,
      exists offset, offset ∈ Finset.range (windowAt scheduleIndex + 1) /\
        stoppingPrefix scheduleIndex trajectory =
          (explicitHighProbabilityRounds (scheduleIndex + offset) : WithTop Nat)) :
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
      selfConsistentScheduledNaturalCausalExpectedAbsoluteGrowingWindowGridStoppingAverageRealizedBehaviorRegret
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor stoppingPrefix
    let budget :=
      selfConsistentScheduledNaturalCausalGrowingWindowGridStoppingL1Budget mdp
        varianceProxy windowAt
    Tendsto windowAt atTop atTop /\
      StronglyAdapted
        (selfConsistentScheduledNaturalCausalTrajectoryFiltration mdp initialState
          rewardSource initialTable defaultState varianceProxy baseVisitFloor)
        process /\
      (forall scheduleIndex, Measurable (stoppedProcess scheduleIndex)) /\
      (forall scheduleIndex,
        MemLp (stoppedProcess scheduleIndex) 1 source.trajectoryMeasure) /\
      (forall scheduleIndex, expectedAbsolute scheduleIndex <= budget scheduleIndex) /\
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
    selfConsistentScheduledNaturalCausalExpectedAbsoluteGrowingWindowGridStoppingAverageRealizedBehaviorRegret
      mdp initialState rewardSource initialTable defaultState varianceProxy
        baseVisitFloor stoppingPrefix
  let budget :=
    selfConsistentScheduledNaturalCausalGrowingWindowGridStoppingL1Budget mdp
      varianceProxy windowAt
  have hmem := fun scheduleIndex =>
    memLp_one_selfConsistentScheduledNaturalCausalGrowingWindowGridStoppingAverageRealizedBehaviorRegret
      mdp initialState rewardSource varianceProxy law initialTable defaultState
        baseVisitFloor hrewardBound stoppingPrefix hstopping windowAt hgrid
          scheduleIndex
  have heLp :=
    eLpNorm_one_selfConsistentScheduledNaturalCausalGrowingWindowGridStoppingAverageRealizedBehaviorRegret_sub_zero_tendsto_zero
      mdp initialState rewardSource varianceProxy hvarianceProxy law initialTable
        defaultState support baseVisitFloor hbaseFloor hrewardBound hhorizon
          hbaseVisitFloor stoppingPrefix hstopping windowAt hgrid
  have hlowerNat : forall scheduleIndex trajectory,
      scheduleIndex <= (stoppingPrefix scheduleIndex trajectory).untopA := by
    intro scheduleIndex trajectory
    obtain ⟨offset, _hoffset, hoffsetEq⟩ :=
      exists_growingWindowGrid_offset_untopA_eq stoppingPrefix windowAt hgrid
        scheduleIndex trajectory
    rw [hoffsetEq]
    exact scheduleIndex_le_explicitHighProbabilityRounds_add scheduleIndex offset
  have haeParent :=
    selfConsistentScheduledCausalSource_stoppingTimeNaturalAverageRealizedBehaviorRegret_tendstoAlmostEverywhere_zero_of_nat_le
      mdp initialState rewardSource varianceProxy hvarianceProxy law initialTable
        defaultState support baseVisitFloor hbaseFloor hrewardBound hhorizon
          hbaseVisitFloor stoppingPrefix hstopping hlowerNat
  refine ⟨
    hwindowAt,
    selfConsistentScheduledNaturalCausalAverageRealizedBehaviorRegretProcess_stronglyAdapted
      mdp initialState rewardSource initialTable defaultState varianceProxy
        baseVisitFloor,
    fun scheduleIndex =>
      measurable_selfConsistentScheduledNaturalCausalStoppingTimeAverageRealizedBehaviorRegretProcess
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor stoppingPrefix scheduleIndex (hstopping scheduleIndex),
    hmem,
    fun scheduleIndex =>
      selfConsistentScheduledNaturalCausalExpectedAbsoluteGrowingWindowGridStoppingAverageRealizedBehaviorRegret_le_budget
        mdp initialState rewardSource varianceProxy hvarianceProxy law initialTable
          defaultState support baseVisitFloor hbaseFloor hrewardBound hhorizon
            hbaseVisitFloor stoppingPrefix hstopping windowAt hgrid scheduleIndex,
    selfConsistentScheduledNaturalCausalGrowingWindowGridStoppingL1Budget_tendsto_zero
      mdp varianceProxy windowAt,
    selfConsistentScheduledNaturalCausalExpectedAbsoluteGrowingWindowGridStoppingAverageRealizedBehaviorRegret_tendsto_zero
      mdp initialState rewardSource varianceProxy hvarianceProxy law initialTable
        defaultState support baseVisitFloor hbaseFloor hrewardBound hhorizon
          hbaseVisitFloor stoppingPrefix hstopping windowAt hgrid,
    heLp,
    ?_,
    haeParent.2.2⟩
  exact tendstoInMeasure_of_tendsto_eLpNorm one_ne_zero
    (fun scheduleIndex => (hmem scheduleIndex).aestronglyMeasurable)
    (by fun_prop) (by simpa [stoppedProcess, source] using heLp)

end AdaptiveStochasticSampledEmpiricalOptimisticSource

end BanditRLProof.FiniteHorizonRL
