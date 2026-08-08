import BanditRLProof.ExpectationBochnerSums
import BanditRLProof.RL.FiniteHorizonNaturalCausalAverageRealizedBehaviorRegretL1Consistency
import BanditRLProof.RL.FiniteHorizonNaturalCausalStoppingTimeAverageRealizedBehaviorRegretAlmostSureConsistency

/-!
# Fixed-window stopping-time L1 natural causal consistency

This module transports the compiled all-prefix L1 consistency theorem through
stopping times constrained to a fixed deterministic window around each natural
prefix.  The selector is charged to a finite sum of shifted coordinate L1
envelopes.  No optional-stopping identity or independence assumption is used.
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

/-- A finite `WithTop Nat` window selects one explicit natural offset. -/
theorem exists_window_offset_untopA_eq_of_withTop_bounds
    {Omega : Type*} (tau : Omega -> WithTop Nat) (start window : Nat)
    (htau_lower : forall omega, (start : WithTop Nat) <= tau omega)
    (htau_upper : forall omega,
      tau omega <= ((start + window : Nat) : WithTop Nat))
    (omega : Omega) :
    exists offset, offset ∈ Finset.range (window + 1) /\
      (tau omega).untopA = start + offset := by
  have hne : tau omega ≠ (⊤ : WithTop Nat) :=
    ne_top_of_le_ne_top WithTop.coe_ne_top (htau_upper omega)
  have hcoe : (((tau omega).untopA : Nat) : WithTop Nat) = tau omega := by
    rw [WithTop.untopA_eq_untop hne]
    exact WithTop.coe_untop _ hne
  have hlower : start <= (tau omega).untopA := by
    have hlowerTop := htau_lower omega
    rw [← hcoe] at hlowerTop
    exact WithTop.coe_le_coe.mp hlowerTop
  have hupper : (tau omega).untopA <= start + window := by
    have hupperTop := htau_upper omega
    rw [← hcoe] at hupperTop
    exact WithTop.coe_le_coe.mp hupperTop
  obtain ⟨offset, hoffset⟩ := Nat.exists_eq_add_of_le hlower
  refine ⟨offset, Finset.mem_range.mpr ?_, hoffset⟩
  rw [Nat.lt_add_one_iff]
  rw [hoffset] at hupper
  exact Nat.add_le_add_iff_left.mp hupper

/-- Sum of the coordinate L1 envelopes over one fixed-width shifted window. -/
noncomputable def selfConsistentScheduledNaturalCausalBoundedWindowStoppingL1Budget
    (mdp : MDP State Action) (varianceProxy : NNReal)
    (baseVisitFloor : Real) (window scheduleIndex : Nat) : Real :=
  (Finset.range (window + 1)).sum fun offset =>
    selfConsistentScheduledNaturalCausalAverageRealizedBehaviorRegretL1Envelope
      mdp varianceProxy baseVisitFloor (scheduleIndex + 1 + offset)

omit [DecidableEq State] [DecidableEq Action]
    [MeasurableSingletonClass State] [MeasurableSingletonClass Action]
    [Nonempty State] [Nonempty Action] in
/-- The fixed-window L1 budget is nonnegative. -/
theorem selfConsistentScheduledNaturalCausalBoundedWindowStoppingL1Budget_nonneg
    (mdp : MDP State Action) (varianceProxy : NNReal)
    (baseVisitFloor : Real) (window scheduleIndex : Nat) :
    0 <= selfConsistentScheduledNaturalCausalBoundedWindowStoppingL1Budget
      mdp varianceProxy baseVisitFloor window scheduleIndex := by
  exact Finset.sum_nonneg fun offset _ =>
    selfConsistentScheduledNaturalCausalAverageRealizedBehaviorRegretL1Envelope_nonneg
      mdp varianceProxy baseVisitFloor (scheduleIndex + 1 + offset)

omit [DecidableEq State] [DecidableEq Action]
    [MeasurableSingletonClass State] [MeasurableSingletonClass Action]
    [Nonempty State] [Nonempty Action] in
/-- Every fixed-width shifted finite sum of coordinate L1 envelopes vanishes. -/
theorem selfConsistentScheduledNaturalCausalBoundedWindowStoppingL1Budget_tendsto_zero
    (mdp : MDP State Action) (varianceProxy : NNReal)
    (baseVisitFloor : Real) (window : Nat) :
    Tendsto
      (selfConsistentScheduledNaturalCausalBoundedWindowStoppingL1Budget
        mdp varianceProxy baseVisitFloor window) atTop (nhds 0) := by
  unfold selfConsistentScheduledNaturalCausalBoundedWindowStoppingL1Budget
  have hsum : Tendsto
      (fun scheduleIndex => (Finset.range (window + 1)).sum fun offset =>
        selfConsistentScheduledNaturalCausalAverageRealizedBehaviorRegretL1Envelope
          mdp varianceProxy baseVisitFloor (scheduleIndex + 1 + offset))
      atTop (nhds ((Finset.range (window + 1)).sum fun _ => (0 : Real))) := by
    apply tendsto_finset_sum (Finset.range (window + 1))
    intro offset _
    have hcoordinate :=
      selfConsistentScheduledNaturalCausalAverageRealizedBehaviorRegretL1Envelope_tendsto_zero
        mdp varianceProxy baseVisitFloor
    simpa only [Nat.add_assoc] using
      hcoordinate.comp (Filter.tendsto_add_atTop_nat (1 + offset))
  simpa using hsum

/-- Expected absolute value of the fixed-window stopped average process. -/
noncomputable def
    selfConsistentScheduledNaturalCausalExpectedAbsoluteBoundedWindowStoppingAverageRealizedBehaviorRegret
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

/-- Every pointwise bounded stopped average process belongs to `L1`. -/
theorem memLp_one_selfConsistentScheduledNaturalCausalBoundedWindowStoppingAverageRealizedBehaviorRegret
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
    (window scheduleIndex : Nat)
    (hstoppingUpper : forall scheduleIndex trajectory,
      stoppingPrefix scheduleIndex trajectory <=
        ((scheduleIndex + 1 + window : Nat) : WithTop Nat)) :
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
    (hstoppingUpper scheduleIndex)

/-- Expected absolute stopped regret is nonnegative. -/
theorem
    selfConsistentScheduledNaturalCausalExpectedAbsoluteBoundedWindowStoppingAverageRealizedBehaviorRegret_nonneg
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
      selfConsistentScheduledNaturalCausalExpectedAbsoluteBoundedWindowStoppingAverageRealizedBehaviorRegret
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor stoppingPrefix scheduleIndex := by
  unfold selfConsistentScheduledNaturalCausalExpectedAbsoluteBoundedWindowStoppingAverageRealizedBehaviorRegret
  exact integral_nonneg fun _ => abs_nonneg _

/-- The selected stopped coordinate is bounded by the shifted finite L1 budget. -/
theorem
    selfConsistentScheduledNaturalCausalExpectedAbsoluteBoundedWindowStoppingAverageRealizedBehaviorRegret_le_budget
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
    (window scheduleIndex : Nat)
    (hstoppingLower : forall scheduleIndex trajectory,
      ((scheduleIndex + 1 : Nat) : WithTop Nat) <=
        stoppingPrefix scheduleIndex trajectory)
    (hstoppingUpper : forall scheduleIndex trajectory,
      stoppingPrefix scheduleIndex trajectory <=
        ((scheduleIndex + 1 + window : Nat) : WithTop Nat)) :
    selfConsistentScheduledNaturalCausalExpectedAbsoluteBoundedWindowStoppingAverageRealizedBehaviorRegret
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor stoppingPrefix scheduleIndex <=
      selfConsistentScheduledNaturalCausalBoundedWindowStoppingL1Budget
        mdp varianceProxy baseVisitFloor window scheduleIndex := by
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
    exact (integrable_selfConsistentScheduledNaturalCausalAverageRealizedBehaviorRegretProcess
      mdp initialState rewardSource varianceProxy law initialTable defaultState
        baseVisitFloor hrewardBound rounds).abs
  have hsumIntegrable : Integrable
      (fun trajectory =>
        (Finset.range (window + 1)).sum fun offset =>
          |process (scheduleIndex + 1 + offset) trajectory|) mu := by
    exact IntegrabilitySums.integrable_finset_sum mu (Finset.range (window + 1))
      (fun offset trajectory =>
        |process (scheduleIndex + 1 + offset) trajectory|)
      (fun offset _ => hcoordinateIntegrable (scheduleIndex + 1 + offset))
  have hstoppedIntegrable : Integrable
      (fun trajectory => |stoppedProcess scheduleIndex trajectory|) mu := by
    have hmem :=
      memLp_one_selfConsistentScheduledNaturalCausalBoundedWindowStoppingAverageRealizedBehaviorRegret
        mdp initialState rewardSource varianceProxy law initialTable defaultState
          baseVisitFloor hrewardBound stoppingPrefix hstopping window scheduleIndex
            hstoppingUpper
    rw [memLp_one_iff_integrable] at hmem
    exact hmem.abs
  have hpoint : forall trajectory,
      |stoppedProcess scheduleIndex trajectory| <=
        (Finset.range (window + 1)).sum fun offset =>
          |process (scheduleIndex + 1 + offset) trajectory| := by
    intro trajectory
    obtain ⟨offset, hoffsetMem, hoffsetEq⟩ :=
      exists_window_offset_untopA_eq_of_withTop_bounds
        (stoppingPrefix scheduleIndex) (scheduleIndex + 1) window
          (hstoppingLower scheduleIndex) (hstoppingUpper scheduleIndex) trajectory
    change |process (stoppingPrefix scheduleIndex trajectory).untopA trajectory| <= _
    rw [hoffsetEq]
    exact Finset.single_le_sum
      (fun candidate _ => abs_nonneg
        (process (scheduleIndex + 1 + candidate) trajectory)) hoffsetMem
  calc
    selfConsistentScheduledNaturalCausalExpectedAbsoluteBoundedWindowStoppingAverageRealizedBehaviorRegret
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor stoppingPrefix scheduleIndex =
        integral mu (fun trajectory => |stoppedProcess scheduleIndex trajectory|) := by
      rfl
    _ <= integral mu (fun trajectory =>
        (Finset.range (window + 1)).sum fun offset =>
          |process (scheduleIndex + 1 + offset) trajectory|) :=
      integral_mono hstoppedIntegrable hsumIntegrable hpoint
    _ = (Finset.range (window + 1)).sum fun offset =>
        integral mu (fun trajectory =>
          |process (scheduleIndex + 1 + offset) trajectory|) := by
      exact ExpectationBochnerSums.integral_finset_sum mu
        (Finset.range (window + 1))
        (fun offset trajectory =>
          |process (scheduleIndex + 1 + offset) trajectory|)
        (fun offset _ => hcoordinateIntegrable (scheduleIndex + 1 + offset))
    _ <= (Finset.range (window + 1)).sum fun offset =>
        selfConsistentScheduledNaturalCausalAverageRealizedBehaviorRegretL1Envelope
          mdp varianceProxy baseVisitFloor (scheduleIndex + 1 + offset) := by
      apply Finset.sum_le_sum
      intro offset _
      simpa [process, mu, source,
        selfConsistentScheduledNaturalCausalExpectedAbsoluteAverageRealizedBehaviorRegret]
        using
          selfConsistentScheduledNaturalCausalExpectedAbsoluteAverageRealizedBehaviorRegret_le_L1Envelope
            mdp initialState rewardSource varianceProxy hvarianceProxy law initialTable
              defaultState support baseVisitFloor hbaseFloor hrewardBound hhorizon
                hbaseVisitFloor (scheduleIndex + 1 + offset)
    _ = selfConsistentScheduledNaturalCausalBoundedWindowStoppingL1Budget
        mdp varianceProxy baseVisitFloor window scheduleIndex := rfl

/-- Expected absolute stopped average regret tends to zero. -/
theorem
    selfConsistentScheduledNaturalCausalExpectedAbsoluteBoundedWindowStoppingAverageRealizedBehaviorRegret_tendsto_zero
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
    (window : Nat)
    (hstoppingLower : forall scheduleIndex trajectory,
      ((scheduleIndex + 1 : Nat) : WithTop Nat) <=
        stoppingPrefix scheduleIndex trajectory)
    (hstoppingUpper : forall scheduleIndex trajectory,
      stoppingPrefix scheduleIndex trajectory <=
        ((scheduleIndex + 1 + window : Nat) : WithTop Nat)) :
    Tendsto
      (selfConsistentScheduledNaturalCausalExpectedAbsoluteBoundedWindowStoppingAverageRealizedBehaviorRegret
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor stoppingPrefix) atTop (nhds 0) := by
  apply squeeze_zero'
  · exact Filter.Eventually.of_forall fun scheduleIndex =>
      selfConsistentScheduledNaturalCausalExpectedAbsoluteBoundedWindowStoppingAverageRealizedBehaviorRegret_nonneg
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor stoppingPrefix scheduleIndex
  · exact Filter.Eventually.of_forall fun scheduleIndex =>
      selfConsistentScheduledNaturalCausalExpectedAbsoluteBoundedWindowStoppingAverageRealizedBehaviorRegret_le_budget
        mdp initialState rewardSource varianceProxy hvarianceProxy law initialTable
          defaultState support baseVisitFloor hbaseFloor hrewardBound hhorizon
            hbaseVisitFloor stoppingPrefix hstopping window scheduleIndex
              hstoppingLower hstoppingUpper
  · exact
      selfConsistentScheduledNaturalCausalBoundedWindowStoppingL1Budget_tendsto_zero
        mdp varianceProxy baseVisitFloor window

/-- At exponent one, the stopped norm is its lifted expected absolute value. -/
theorem
    eLpNorm_one_selfConsistentScheduledNaturalCausalBoundedWindowStoppingAverageRealizedBehaviorRegret_eq
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
    (window scheduleIndex : Nat)
    (hstoppingUpper : forall scheduleIndex trajectory,
      stoppingPrefix scheduleIndex trajectory <=
        ((scheduleIndex + 1 + window : Nat) : WithTop Nat)) :
    eLpNorm
        (selfConsistentScheduledNaturalCausalStoppingTimeAverageRealizedBehaviorRegretProcess
          mdp initialState rewardSource initialTable defaultState varianceProxy
            baseVisitFloor stoppingPrefix scheduleIndex)
        1
        (selfConsistentScheduledCausalSource mdp initialState rewardSource
          initialTable defaultState varianceProxy baseVisitFloor).trajectoryMeasure =
      ENNReal.ofReal
        (selfConsistentScheduledNaturalCausalExpectedAbsoluteBoundedWindowStoppingAverageRealizedBehaviorRegret
          mdp initialState rewardSource initialTable defaultState varianceProxy
            baseVisitFloor stoppingPrefix scheduleIndex) := by
  rw [MemLp.eLpNorm_eq_integral_rpow_norm one_ne_zero ENNReal.one_ne_top
    (memLp_one_selfConsistentScheduledNaturalCausalBoundedWindowStoppingAverageRealizedBehaviorRegret
      mdp initialState rewardSource varianceProxy law initialTable defaultState
        baseVisitFloor hrewardBound stoppingPrefix hstopping window scheduleIndex
          hstoppingUpper)]
  simp [
    selfConsistentScheduledNaturalCausalExpectedAbsoluteBoundedWindowStoppingAverageRealizedBehaviorRegret,
    Real.norm_eq_abs]

/-- The stopped process converges to zero in the exponent-one extended norm. -/
theorem
    eLpNorm_one_selfConsistentScheduledNaturalCausalBoundedWindowStoppingAverageRealizedBehaviorRegret_sub_zero_tendsto_zero
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
    (window : Nat)
    (hstoppingLower : forall scheduleIndex trajectory,
      ((scheduleIndex + 1 : Nat) : WithTop Nat) <=
        stoppingPrefix scheduleIndex trajectory)
    (hstoppingUpper : forall scheduleIndex trajectory,
      stoppingPrefix scheduleIndex trajectory <=
        ((scheduleIndex + 1 + window : Nat) : WithTop Nat)) :
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
    selfConsistentScheduledNaturalCausalExpectedAbsoluteBoundedWindowStoppingAverageRealizedBehaviorRegret_tendsto_zero
      mdp initialState rewardSource varianceProxy hvarianceProxy law initialTable
        defaultState support baseVisitFloor hbaseFloor hrewardBound hhorizon
          hbaseVisitFloor stoppingPrefix hstopping window hstoppingLower
            hstoppingUpper
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
          (selfConsistentScheduledNaturalCausalExpectedAbsoluteBoundedWindowStoppingAverageRealizedBehaviorRegret
            mdp initialState rewardSource initialTable defaultState varianceProxy
              baseVisitFloor stoppingPrefix scheduleIndex)) := by
      funext scheduleIndex
      exact
        eLpNorm_one_selfConsistentScheduledNaturalCausalBoundedWindowStoppingAverageRealizedBehaviorRegret_eq
          mdp initialState rewardSource varianceProxy law initialTable defaultState
            baseVisitFloor hrewardBound stoppingPrefix hstopping window scheduleIndex
              hstoppingUpper
    rw [hnormEq]
    simpa only [Function.comp_apply, ENNReal.ofReal_zero] using hofReal
  convert hnorm using 1
  funext scheduleIndex
  apply eLpNorm_congr_ae
  exact Filter.Eventually.of_forall fun trajectory => by simp

/-
Terminal fixed-window stopping-time L1 theorem for the exact
per-batch-normalized, equal-round-weighted natural realized behavior-regret
process.
-/
theorem
    selfConsistentScheduledCausalSource_boundedWindowStoppingTimeNaturalAverageRealizedBehaviorRegret_L1_consistency
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
    (window : Nat)
    (hstoppingLower : forall scheduleIndex trajectory,
      ((scheduleIndex + 1 : Nat) : WithTop Nat) <=
        stoppingPrefix scheduleIndex trajectory)
    (hstoppingUpper : forall scheduleIndex trajectory,
      stoppingPrefix scheduleIndex trajectory <=
        ((scheduleIndex + 1 + window : Nat) : WithTop Nat)) :
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
      selfConsistentScheduledNaturalCausalExpectedAbsoluteBoundedWindowStoppingAverageRealizedBehaviorRegret
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor stoppingPrefix
    let budget :=
      selfConsistentScheduledNaturalCausalBoundedWindowStoppingL1Budget mdp
        varianceProxy baseVisitFloor window
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
    selfConsistentScheduledNaturalCausalExpectedAbsoluteBoundedWindowStoppingAverageRealizedBehaviorRegret
      mdp initialState rewardSource initialTable defaultState varianceProxy
        baseVisitFloor stoppingPrefix
  let budget :=
    selfConsistentScheduledNaturalCausalBoundedWindowStoppingL1Budget mdp
      varianceProxy baseVisitFloor window
  have hmem := fun scheduleIndex =>
    memLp_one_selfConsistentScheduledNaturalCausalBoundedWindowStoppingAverageRealizedBehaviorRegret
      mdp initialState rewardSource varianceProxy law initialTable defaultState
        baseVisitFloor hrewardBound stoppingPrefix hstopping window scheduleIndex
          hstoppingUpper
  have heLp :=
    eLpNorm_one_selfConsistentScheduledNaturalCausalBoundedWindowStoppingAverageRealizedBehaviorRegret_sub_zero_tendsto_zero
      mdp initialState rewardSource varianceProxy hvarianceProxy law initialTable
        defaultState support baseVisitFloor hbaseFloor hrewardBound hhorizon
          hbaseVisitFloor stoppingPrefix hstopping window hstoppingLower
            hstoppingUpper
  have hlowerNat : forall scheduleIndex trajectory,
      scheduleIndex <= (stoppingPrefix scheduleIndex trajectory).untopA := by
    intro scheduleIndex trajectory
    obtain ⟨offset, _hoffsetMem, hoffsetEq⟩ :=
      exists_window_offset_untopA_eq_of_withTop_bounds
        (stoppingPrefix scheduleIndex) (scheduleIndex + 1) window
          (hstoppingLower scheduleIndex) (hstoppingUpper scheduleIndex) trajectory
    rw [hoffsetEq]
    omega
  have haeParent :=
    selfConsistentScheduledCausalSource_stoppingTimeNaturalAverageRealizedBehaviorRegret_tendstoAlmostEverywhere_zero_of_nat_le
      mdp initialState rewardSource varianceProxy hvarianceProxy law initialTable
        defaultState support baseVisitFloor hbaseFloor hrewardBound hhorizon
          hbaseVisitFloor stoppingPrefix hstopping hlowerNat
  refine ⟨
    selfConsistentScheduledNaturalCausalAverageRealizedBehaviorRegretProcess_stronglyAdapted
      mdp initialState rewardSource initialTable defaultState varianceProxy
        baseVisitFloor,
    fun scheduleIndex =>
      measurable_selfConsistentScheduledNaturalCausalStoppingTimeAverageRealizedBehaviorRegretProcess
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor stoppingPrefix scheduleIndex (hstopping scheduleIndex),
    hmem,
    fun scheduleIndex =>
      selfConsistentScheduledNaturalCausalExpectedAbsoluteBoundedWindowStoppingAverageRealizedBehaviorRegret_le_budget
        mdp initialState rewardSource varianceProxy hvarianceProxy law initialTable
          defaultState support baseVisitFloor hbaseFloor hrewardBound hhorizon
            hbaseVisitFloor stoppingPrefix hstopping window scheduleIndex
              hstoppingLower hstoppingUpper,
    selfConsistentScheduledNaturalCausalBoundedWindowStoppingL1Budget_tendsto_zero
      mdp varianceProxy baseVisitFloor window,
    selfConsistentScheduledNaturalCausalExpectedAbsoluteBoundedWindowStoppingAverageRealizedBehaviorRegret_tendsto_zero
      mdp initialState rewardSource varianceProxy hvarianceProxy law initialTable
        defaultState support baseVisitFloor hbaseFloor hrewardBound hhorizon
          hbaseVisitFloor stoppingPrefix hstopping window hstoppingLower
            hstoppingUpper,
    heLp,
    ?_,
    haeParent.2.2⟩
  exact tendstoInMeasure_of_tendsto_eLpNorm one_ne_zero
    (fun scheduleIndex => (hmem scheduleIndex).aestronglyMeasurable)
    (by fun_prop) (by simpa [stoppedProcess, source] using heLp)

end AdaptiveStochasticSampledEmpiricalOptimisticSource

end BanditRLProof.FiniteHorizonRL
