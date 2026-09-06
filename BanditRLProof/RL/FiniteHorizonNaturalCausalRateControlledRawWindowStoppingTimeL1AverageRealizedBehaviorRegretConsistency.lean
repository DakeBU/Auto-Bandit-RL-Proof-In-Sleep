import BanditRLProof.RL.FiniteHorizonNaturalCausalPolynomialBaseGrowingRawWindowStoppingTimeL1AverageRealizedBehaviorRegretConsistency

/-!
# Rate-controlled raw-window stopping-time L1 consistency

This module replaces the fixed fourth-power base and width `n` by deterministic
functions `baseRounds` and `windowWidth`. The exact regularity contract is

`(windowWidth n + 1) / sqrt (baseRounds n) -> 0`.

Every stopping prefix may select any raw natural coordinate in
`[baseRounds n, baseRounds n + windowWidth n]`. The proof charges the selector
to the finite sum of all candidate-coordinate L1 envelopes. The extra contract
`n <= baseRounds n` is used only by the almost-sure parent theorem; no optional
stopping identity or independence assumption is introduced.
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

/-- Sum of all coordinate L1 envelopes in a parameterized raw window. -/
noncomputable def
    selfConsistentScheduledNaturalCausalRateControlledRawWindowStoppingL1Budget
    (mdp : MDP State Action) (varianceProxy : NNReal)
    (baseVisitFloor : Real) (baseRounds windowWidth : Nat -> Nat)
    (scheduleIndex : Nat) : Real :=
  (Finset.range (windowWidth scheduleIndex + 1)).sum fun offset =>
    selfConsistentScheduledNaturalCausalAverageRealizedBehaviorRegretL1Envelope
      mdp varianceProxy baseVisitFloor
        (baseRounds scheduleIndex + offset)

/-- Candidate-count times inverse-square-root rate for a raw window. -/
noncomputable def
    selfConsistentScheduledNaturalCausalRateControlledRawWindowStoppingL1Rate
    (mdp : MDP State Action) (varianceProxy : NNReal)
    (baseRounds windowWidth : Nat -> Nat) (scheduleIndex : Nat) : Real :=
  selfConsistentScheduledNaturalCausalRawWindowL1Coefficient mdp varianceProxy *
    (((windowWidth scheduleIndex + 1 : Nat) : Real) /
      Real.sqrt (baseRounds scheduleIndex : Real))

omit [DecidableEq State] [DecidableEq Action]
    [MeasurableSingletonClass State] [MeasurableSingletonClass Action]
    [Nonempty State] [Nonempty Action] in
/-- Adding a natural offset cannot decrease the square root of a base prefix. -/
theorem sqrt_baseRounds_le_sqrt_add (baseRounds offset : Nat) :
    Real.sqrt (baseRounds : Real) <=
      Real.sqrt (baseRounds + offset : Nat) := by
  exact Real.sqrt_le_sqrt (by exact_mod_cast Nat.le_add_right baseRounds offset)

omit [DecidableEq State] [DecidableEq Action]
    [MeasurableSingletonClass State] [MeasurableSingletonClass Action]
    [Nonempty State] [Nonempty Action] in
/-- Every candidate envelope is controlled by the inverse square root of its base. -/
theorem
    selfConsistentScheduledNaturalCausalRawWindowInverseSqrtL1Envelope_add_le_base
    (mdp : MDP State Action) (varianceProxy : NNReal)
    (baseRounds offset : Nat) (hbaseRounds : 0 < baseRounds) :
    selfConsistentScheduledNaturalCausalRawWindowInverseSqrtL1Envelope
        mdp varianceProxy (baseRounds + offset) <=
      selfConsistentScheduledNaturalCausalRawWindowL1Coefficient
          mdp varianceProxy /
        Real.sqrt (baseRounds : Real) := by
  unfold selfConsistentScheduledNaturalCausalRawWindowInverseSqrtL1Envelope
  exact div_le_div_of_nonneg_left
    (selfConsistentScheduledNaturalCausalRawWindowL1Coefficient_nonneg
      mdp varianceProxy)
    (Real.sqrt_pos.2 (by exact_mod_cast hbaseRounds))
    (sqrt_baseRounds_le_sqrt_add baseRounds offset)

omit [DecidableEq State] [DecidableEq Action]
    [MeasurableSingletonClass State] [MeasurableSingletonClass Action]
    [Nonempty State] [Nonempty Action] in
/-- A parameterized finite raw-window L1 budget is nonnegative. -/
theorem
    selfConsistentScheduledNaturalCausalRateControlledRawWindowStoppingL1Budget_nonneg
    (mdp : MDP State Action) (varianceProxy : NNReal)
    (baseVisitFloor : Real) (baseRounds windowWidth : Nat -> Nat)
    (scheduleIndex : Nat) :
    0 <=
      selfConsistentScheduledNaturalCausalRateControlledRawWindowStoppingL1Budget
        mdp varianceProxy baseVisitFloor baseRounds windowWidth scheduleIndex := by
  exact Finset.sum_nonneg fun offset _ =>
    selfConsistentScheduledNaturalCausalAverageRealizedBehaviorRegretL1Envelope_nonneg
      mdp varianceProxy baseVisitFloor (baseRounds scheduleIndex + offset)

omit [DecidableEq State] [DecidableEq Action]
    [MeasurableSingletonClass State] [MeasurableSingletonClass Action]
    [Nonempty State] [Nonempty Action] in
/-- The candidate sum is bounded by candidate count times the base envelope. -/
theorem
    selfConsistentScheduledNaturalCausalRateControlledRawWindowStoppingL1Budget_le_rate
    (mdp : MDP State Action) (varianceProxy : NNReal)
    (baseVisitFloor : Real) (baseRounds windowWidth : Nat -> Nat)
    (hbaseRounds : forall scheduleIndex, 0 < baseRounds scheduleIndex)
    (scheduleIndex : Nat) :
    selfConsistentScheduledNaturalCausalRateControlledRawWindowStoppingL1Budget
        mdp varianceProxy baseVisitFloor baseRounds windowWidth scheduleIndex <=
      selfConsistentScheduledNaturalCausalRateControlledRawWindowStoppingL1Rate
        mdp varianceProxy baseRounds windowWidth scheduleIndex := by
  calc
    selfConsistentScheduledNaturalCausalRateControlledRawWindowStoppingL1Budget
        mdp varianceProxy baseVisitFloor baseRounds windowWidth scheduleIndex <=
      (Finset.range (windowWidth scheduleIndex + 1)).sum (fun _ =>
        selfConsistentScheduledNaturalCausalRawWindowL1Coefficient
            mdp varianceProxy /
          Real.sqrt (baseRounds scheduleIndex : Real)) := by
      unfold selfConsistentScheduledNaturalCausalRateControlledRawWindowStoppingL1Budget
      apply Finset.sum_le_sum
      intro offset _hoffset
      have hrounds : 0 < baseRounds scheduleIndex + offset :=
        Nat.add_pos_left (hbaseRounds scheduleIndex) offset
      exact
        (selfConsistentScheduledNaturalCausalAverageRealizedBehaviorRegretL1Envelope_le_rawWindowInverseSqrtL1Envelope
          mdp varianceProxy baseVisitFloor
            (baseRounds scheduleIndex + offset) hrounds).trans
          (selfConsistentScheduledNaturalCausalRawWindowInverseSqrtL1Envelope_add_le_base
            mdp varianceProxy (baseRounds scheduleIndex) offset
              (hbaseRounds scheduleIndex))
    _ =
      selfConsistentScheduledNaturalCausalRateControlledRawWindowStoppingL1Rate
        mdp varianceProxy baseRounds windowWidth scheduleIndex := by
      unfold selfConsistentScheduledNaturalCausalRateControlledRawWindowStoppingL1Rate
      simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      ring

omit [DecidableEq State] [DecidableEq Action]
    [MeasurableSingletonClass State] [MeasurableSingletonClass Action]
    [Nonempty State] [Nonempty Action] in
/-- A vanishing candidate-count/base-square-root ratio gives a vanishing rate. -/
theorem
    selfConsistentScheduledNaturalCausalRateControlledRawWindowStoppingL1Rate_tendsto_zero
    (mdp : MDP State Action) (varianceProxy : NNReal)
    (baseRounds windowWidth : Nat -> Nat)
    (hcandidateRate : Tendsto
      (fun scheduleIndex =>
        (((windowWidth scheduleIndex + 1 : Nat) : Real) /
          Real.sqrt (baseRounds scheduleIndex : Real)))
      atTop (nhds 0)) :
    Tendsto
      (selfConsistentScheduledNaturalCausalRateControlledRawWindowStoppingL1Rate
        mdp varianceProxy baseRounds windowWidth) atTop (nhds 0) := by
  unfold selfConsistentScheduledNaturalCausalRateControlledRawWindowStoppingL1Rate
  simpa only [mul_zero] using tendsto_const_nhds.mul hcandidateRate

omit [DecidableEq State] [DecidableEq Action]
    [MeasurableSingletonClass State] [MeasurableSingletonClass Action]
    [Nonempty State] [Nonempty Action] in
/-- The parameterized raw-window L1 budget tends to zero under the rate contract. -/
theorem
    selfConsistentScheduledNaturalCausalRateControlledRawWindowStoppingL1Budget_tendsto_zero
    (mdp : MDP State Action) (varianceProxy : NNReal)
    (baseVisitFloor : Real) (baseRounds windowWidth : Nat -> Nat)
    (hbaseRounds : forall scheduleIndex, 0 < baseRounds scheduleIndex)
    (hcandidateRate : Tendsto
      (fun scheduleIndex =>
        (((windowWidth scheduleIndex + 1 : Nat) : Real) /
          Real.sqrt (baseRounds scheduleIndex : Real)))
      atTop (nhds 0)) :
    Tendsto
      (selfConsistentScheduledNaturalCausalRateControlledRawWindowStoppingL1Budget
        mdp varianceProxy baseVisitFloor baseRounds windowWidth)
      atTop (nhds 0) := by
  apply squeeze_zero'
  · exact Filter.Eventually.of_forall fun scheduleIndex =>
      selfConsistentScheduledNaturalCausalRateControlledRawWindowStoppingL1Budget_nonneg
        mdp varianceProxy baseVisitFloor baseRounds windowWidth scheduleIndex
  · exact Filter.Eventually.of_forall fun scheduleIndex =>
      selfConsistentScheduledNaturalCausalRateControlledRawWindowStoppingL1Budget_le_rate
        mdp varianceProxy baseVisitFloor baseRounds windowWidth hbaseRounds
          scheduleIndex
  · exact
      selfConsistentScheduledNaturalCausalRateControlledRawWindowStoppingL1Rate_tendsto_zero
        mdp varianceProxy baseRounds windowWidth hcandidateRate

/-- WithTop bounds select one candidate in a parameterized raw window. -/
theorem exists_rateControlledRawWindow_offset_untopA_eq
    {Omega : Type*} (stoppingPrefix : Nat -> Omega -> WithTop Nat)
    (baseRounds windowWidth : Nat -> Nat)
    (hstoppingLower : forall scheduleIndex trajectory,
      (baseRounds scheduleIndex : WithTop Nat) <=
        stoppingPrefix scheduleIndex trajectory)
    (hstoppingUpper : forall scheduleIndex trajectory,
      stoppingPrefix scheduleIndex trajectory <=
        (baseRounds scheduleIndex + windowWidth scheduleIndex : WithTop Nat))
    (scheduleIndex : Nat) (trajectory : Omega) :
    exists offset, offset ∈ Finset.range (windowWidth scheduleIndex + 1) /\
      (stoppingPrefix scheduleIndex trajectory).untopA =
        baseRounds scheduleIndex + offset := by
  exact exists_window_offset_untopA_eq_of_withTop_bounds
    (stoppingPrefix scheduleIndex) (baseRounds scheduleIndex)
      (windowWidth scheduleIndex) (hstoppingLower scheduleIndex)
        (hstoppingUpper scheduleIndex) trajectory

omit [DecidableEq State] [DecidableEq Action]
    [MeasurableSingletonClass State] [MeasurableSingletonClass Action]
    [Nonempty State] [Nonempty Action] in
/-- The fourth-power base with width `n` satisfies the generic rate contract. -/
theorem explicitHighProbabilityRawWindowCandidateRate_tendsto_zero :
    Tendsto
      (fun scheduleIndex =>
        (((scheduleIndex + 1 : Nat) : Real) /
          Real.sqrt (explicitHighProbabilityRounds scheduleIndex : Real)))
      atTop (nhds 0) := by
  have hrewrite :
      (fun scheduleIndex =>
        (((scheduleIndex + 1 : Nat) : Real) /
          Real.sqrt (explicitHighProbabilityRounds scheduleIndex : Real))) =
      (fun scheduleIndex =>
        1 / (explicitHighProbabilityScale scheduleIndex : Real)) := by
    funext scheduleIndex
    let s : Real := explicitHighProbabilityScale scheduleIndex
    have hs : 0 < s := by
      dsimp [s]
      exact_mod_cast explicitHighProbabilityScale_pos scheduleIndex
    have hrounds :
        (explicitHighProbabilityRounds scheduleIndex : Real) = s ^ 4 := by
      simp [explicitHighProbabilityRounds, explicitHighProbabilityScale, s]
    have hscale : ((scheduleIndex + 1 : Nat) : Real) = s := by
      simp [explicitHighProbabilityScale, s]
    have hscaleDef :
        (explicitHighProbabilityScale scheduleIndex : Real) = s := by
      rfl
    rw [hrounds, show s ^ 4 = (s ^ 2) ^ 2 by ring,
      Real.sqrt_sq (sq_nonneg s), hscale, hscaleDef]
    field_simp [ne_of_gt hs]
  rw [hrewrite]
  exact tendsto_const_nhds.div_atTop
    explicitHighProbabilityScale_real_tendsto_atTop

omit [DecidableEq State] [DecidableEq Action]
    [MeasurableSingletonClass State] [MeasurableSingletonClass Action]
    [Nonempty State] [Nonempty Action] in
/-- The fourth-power base also supports the strictly wider raw width `2*n+1`. -/
theorem explicitHighProbabilityDoubleLinearRawWindowCandidateRate_tendsto_zero :
    Tendsto
      (fun scheduleIndex =>
        ((((2 * scheduleIndex + 1) + 1 : Nat) : Real) /
          Real.sqrt (explicitHighProbabilityRounds scheduleIndex : Real)))
      atTop (nhds 0) := by
  have hrewrite :
      (fun scheduleIndex =>
        ((((2 * scheduleIndex + 1) + 1 : Nat) : Real) /
          Real.sqrt (explicitHighProbabilityRounds scheduleIndex : Real))) =
      (fun scheduleIndex =>
        2 / (explicitHighProbabilityScale scheduleIndex : Real)) := by
    funext scheduleIndex
    let s : Real := explicitHighProbabilityScale scheduleIndex
    have hs : 0 < s := by
      dsimp [s]
      exact_mod_cast explicitHighProbabilityScale_pos scheduleIndex
    have hrounds :
        (explicitHighProbabilityRounds scheduleIndex : Real) = s ^ 4 := by
      simp [explicitHighProbabilityRounds, explicitHighProbabilityScale, s]
    have hwidth :
        ((((2 * scheduleIndex + 1) + 1 : Nat) : Real)) = 2 * s := by
      simp [explicitHighProbabilityScale, s]
      ring
    have hscaleDef :
        (explicitHighProbabilityScale scheduleIndex : Real) = s := by
      rfl
    rw [hrounds, show s ^ 4 = (s ^ 2) ^ 2 by ring,
      Real.sqrt_sq (sq_nonneg s), hwidth, hscaleDef]
    field_simp [ne_of_gt hs]
  rw [hrewrite]
  exact tendsto_const_nhds.div_atTop
    explicitHighProbabilityScale_real_tendsto_atTop

/-- Expected absolute value of a rate-controlled raw-window stopped process. -/
noncomputable def
    selfConsistentScheduledNaturalCausalExpectedAbsoluteRateControlledRawWindowStoppingAverageRealizedBehaviorRegret
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

/-- Every rate-controlled raw-window stopped coordinate belongs to `L1`. -/
theorem
    memLp_one_selfConsistentScheduledNaturalCausalRateControlledRawWindowStoppingAverageRealizedBehaviorRegret
    (mdp : MDP State Action) (initialState : Measure State)
    [IsProbabilityMeasure initialState]
    [StandardBorelSpace State] [StandardBorelSpace Action]
    (rewardSource : mdp.MeanCompatibleRewardKernel)
    (varianceProxy : NNReal)
    (law : rewardSource.UniformSubgaussianRewardLaw varianceProxy)
    (initialTable : DeterministicMarkovPolicyTable mdp)
    (defaultState : State) (baseVisitFloor : Real)
    (hrewardBound : forall state action, |mdp.reward state action| <= 1)
    (baseRounds windowWidth : Nat -> Nat)
    (stoppingPrefix : Nat ->
      HeterogeneousStochasticEpisodeBatchTrajectory mdp
        (fun t =>
          AdaptiveStochasticEpisodeBatchSource.selfConsistentScheduledEpisodes
            mdp varianceProxy baseVisitFloor t) -> WithTop Nat)
    (hstopping : forall scheduleIndex, IsStoppingTime
      (selfConsistentScheduledNaturalCausalTrajectoryFiltration mdp initialState
        rewardSource initialTable defaultState varianceProxy baseVisitFloor)
      (stoppingPrefix scheduleIndex))
    (hstoppingUpper : forall scheduleIndex trajectory,
      stoppingPrefix scheduleIndex trajectory <=
        (baseRounds scheduleIndex + windowWidth scheduleIndex : WithTop Nat))
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
    (hstoppingUpper scheduleIndex)

/-- Expected absolute rate-controlled stopped regret is nonnegative. -/
theorem
    selfConsistentScheduledNaturalCausalExpectedAbsoluteRateControlledRawWindowStoppingAverageRealizedBehaviorRegret_nonneg
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
      selfConsistentScheduledNaturalCausalExpectedAbsoluteRateControlledRawWindowStoppingAverageRealizedBehaviorRegret
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor stoppingPrefix scheduleIndex := by
  unfold selfConsistentScheduledNaturalCausalExpectedAbsoluteRateControlledRawWindowStoppingAverageRealizedBehaviorRegret
  exact integral_nonneg fun _ => abs_nonneg _

/-- The selected raw coordinate is bounded by the full finite candidate budget. -/
theorem
    selfConsistentScheduledNaturalCausalExpectedAbsoluteRateControlledRawWindowStoppingAverageRealizedBehaviorRegret_le_budget
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
    (baseRounds windowWidth : Nat -> Nat)
    (stoppingPrefix : Nat ->
      HeterogeneousStochasticEpisodeBatchTrajectory mdp
        (fun t =>
          AdaptiveStochasticEpisodeBatchSource.selfConsistentScheduledEpisodes
            mdp varianceProxy baseVisitFloor t) -> WithTop Nat)
    (hstopping : forall scheduleIndex, IsStoppingTime
      (selfConsistentScheduledNaturalCausalTrajectoryFiltration mdp initialState
        rewardSource initialTable defaultState varianceProxy baseVisitFloor)
      (stoppingPrefix scheduleIndex))
    (hstoppingLower : forall scheduleIndex trajectory,
      (baseRounds scheduleIndex : WithTop Nat) <=
        stoppingPrefix scheduleIndex trajectory)
    (hstoppingUpper : forall scheduleIndex trajectory,
      stoppingPrefix scheduleIndex trajectory <=
        (baseRounds scheduleIndex + windowWidth scheduleIndex : WithTop Nat))
    (scheduleIndex : Nat) :
    selfConsistentScheduledNaturalCausalExpectedAbsoluteRateControlledRawWindowStoppingAverageRealizedBehaviorRegret
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor stoppingPrefix scheduleIndex <=
      selfConsistentScheduledNaturalCausalRateControlledRawWindowStoppingL1Budget
        mdp varianceProxy baseVisitFloor baseRounds windowWidth scheduleIndex := by
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
        (Finset.range (windowWidth scheduleIndex + 1)).sum fun offset =>
          |process (baseRounds scheduleIndex + offset) trajectory|) mu := by
    exact IntegrabilitySums.integrable_finset_sum mu
      (Finset.range (windowWidth scheduleIndex + 1))
      (fun offset trajectory =>
        |process (baseRounds scheduleIndex + offset) trajectory|)
      (fun offset _ =>
        hcoordinateIntegrable (baseRounds scheduleIndex + offset))
  have hstoppedIntegrable : Integrable
      (fun trajectory => |stoppedProcess scheduleIndex trajectory|) mu := by
    have hmem :=
      memLp_one_selfConsistentScheduledNaturalCausalRateControlledRawWindowStoppingAverageRealizedBehaviorRegret
        mdp initialState rewardSource varianceProxy law initialTable defaultState
          baseVisitFloor hrewardBound baseRounds windowWidth stoppingPrefix
            hstopping hstoppingUpper scheduleIndex
    rw [memLp_one_iff_integrable] at hmem
    exact hmem.abs
  have hpoint : forall trajectory,
      |stoppedProcess scheduleIndex trajectory| <=
        (Finset.range (windowWidth scheduleIndex + 1)).sum fun offset =>
          |process (baseRounds scheduleIndex + offset) trajectory| := by
    intro trajectory
    obtain ⟨offset, hoffset, hoffsetEq⟩ :=
      exists_rateControlledRawWindow_offset_untopA_eq stoppingPrefix
        baseRounds windowWidth hstoppingLower hstoppingUpper scheduleIndex
          trajectory
    change |process (stoppingPrefix scheduleIndex trajectory).untopA trajectory| <= _
    rw [hoffsetEq]
    exact Finset.single_le_sum
      (fun candidate _ => abs_nonneg
        (process (baseRounds scheduleIndex + candidate) trajectory)) hoffset
  calc
    selfConsistentScheduledNaturalCausalExpectedAbsoluteRateControlledRawWindowStoppingAverageRealizedBehaviorRegret
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor stoppingPrefix scheduleIndex =
        integral mu (fun trajectory => |stoppedProcess scheduleIndex trajectory|) := by
      rfl
    _ <= integral mu (fun trajectory =>
        (Finset.range (windowWidth scheduleIndex + 1)).sum fun offset =>
          |process (baseRounds scheduleIndex + offset) trajectory|) :=
      integral_mono hstoppedIntegrable hsumIntegrable hpoint
    _ = (Finset.range (windowWidth scheduleIndex + 1)).sum fun offset =>
        integral mu (fun trajectory =>
          |process (baseRounds scheduleIndex + offset) trajectory|) := by
      exact ExpectationBochnerSums.integral_finset_sum mu
        (Finset.range (windowWidth scheduleIndex + 1))
        (fun offset trajectory =>
          |process (baseRounds scheduleIndex + offset) trajectory|)
        (fun offset _ =>
          hcoordinateIntegrable (baseRounds scheduleIndex + offset))
    _ <= (Finset.range (windowWidth scheduleIndex + 1)).sum fun offset =>
        selfConsistentScheduledNaturalCausalAverageRealizedBehaviorRegretL1Envelope
          mdp varianceProxy baseVisitFloor
            (baseRounds scheduleIndex + offset) := by
      apply Finset.sum_le_sum
      intro offset _
      simpa [process, mu, source,
        selfConsistentScheduledNaturalCausalExpectedAbsoluteAverageRealizedBehaviorRegret]
        using
          selfConsistentScheduledNaturalCausalExpectedAbsoluteAverageRealizedBehaviorRegret_le_L1Envelope
            mdp initialState rewardSource varianceProxy hvarianceProxy law
              initialTable defaultState support baseVisitFloor hbaseFloor
                hrewardBound hhorizon hbaseVisitFloor
                  (baseRounds scheduleIndex + offset)
    _ =
      selfConsistentScheduledNaturalCausalRateControlledRawWindowStoppingL1Budget
        mdp varianceProxy baseVisitFloor baseRounds windowWidth scheduleIndex := rfl

/-- Expected absolute rate-controlled stopped regret tends to zero. -/
theorem
    selfConsistentScheduledNaturalCausalExpectedAbsoluteRateControlledRawWindowStoppingAverageRealizedBehaviorRegret_tendsto_zero
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
    (baseRounds windowWidth : Nat -> Nat)
    (hbaseRounds : forall scheduleIndex, 0 < baseRounds scheduleIndex)
    (hcandidateRate : Tendsto
      (fun scheduleIndex =>
        (((windowWidth scheduleIndex + 1 : Nat) : Real) /
          Real.sqrt (baseRounds scheduleIndex : Real)))
      atTop (nhds 0))
    (stoppingPrefix : Nat ->
      HeterogeneousStochasticEpisodeBatchTrajectory mdp
        (fun t =>
          AdaptiveStochasticEpisodeBatchSource.selfConsistentScheduledEpisodes
            mdp varianceProxy baseVisitFloor t) -> WithTop Nat)
    (hstopping : forall scheduleIndex, IsStoppingTime
      (selfConsistentScheduledNaturalCausalTrajectoryFiltration mdp initialState
        rewardSource initialTable defaultState varianceProxy baseVisitFloor)
      (stoppingPrefix scheduleIndex))
    (hstoppingLower : forall scheduleIndex trajectory,
      (baseRounds scheduleIndex : WithTop Nat) <=
        stoppingPrefix scheduleIndex trajectory)
    (hstoppingUpper : forall scheduleIndex trajectory,
      stoppingPrefix scheduleIndex trajectory <=
        (baseRounds scheduleIndex + windowWidth scheduleIndex : WithTop Nat)) :
    Tendsto
      (selfConsistentScheduledNaturalCausalExpectedAbsoluteRateControlledRawWindowStoppingAverageRealizedBehaviorRegret
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor stoppingPrefix) atTop (nhds 0) := by
  apply squeeze_zero'
  · exact Filter.Eventually.of_forall fun scheduleIndex =>
      selfConsistentScheduledNaturalCausalExpectedAbsoluteRateControlledRawWindowStoppingAverageRealizedBehaviorRegret_nonneg
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor stoppingPrefix scheduleIndex
  · exact Filter.Eventually.of_forall fun scheduleIndex =>
      selfConsistentScheduledNaturalCausalExpectedAbsoluteRateControlledRawWindowStoppingAverageRealizedBehaviorRegret_le_budget
        mdp initialState rewardSource varianceProxy hvarianceProxy law initialTable
          defaultState support baseVisitFloor hbaseFloor hrewardBound hhorizon
            hbaseVisitFloor baseRounds windowWidth stoppingPrefix hstopping
              hstoppingLower hstoppingUpper scheduleIndex
  · exact
      selfConsistentScheduledNaturalCausalRateControlledRawWindowStoppingL1Budget_tendsto_zero
        mdp varianceProxy baseVisitFloor baseRounds windowWidth hbaseRounds
          hcandidateRate

/-- At exponent one, the stopped norm is its expected absolute value. -/
theorem
    eLpNorm_one_selfConsistentScheduledNaturalCausalRateControlledRawWindowStoppingAverageRealizedBehaviorRegret_eq
    (mdp : MDP State Action) (initialState : Measure State)
    [IsProbabilityMeasure initialState]
    [StandardBorelSpace State] [StandardBorelSpace Action]
    (rewardSource : mdp.MeanCompatibleRewardKernel)
    (varianceProxy : NNReal)
    (law : rewardSource.UniformSubgaussianRewardLaw varianceProxy)
    (initialTable : DeterministicMarkovPolicyTable mdp)
    (defaultState : State) (baseVisitFloor : Real)
    (hrewardBound : forall state action, |mdp.reward state action| <= 1)
    (baseRounds windowWidth : Nat -> Nat)
    (stoppingPrefix : Nat ->
      HeterogeneousStochasticEpisodeBatchTrajectory mdp
        (fun t =>
          AdaptiveStochasticEpisodeBatchSource.selfConsistentScheduledEpisodes
            mdp varianceProxy baseVisitFloor t) -> WithTop Nat)
    (hstopping : forall scheduleIndex, IsStoppingTime
      (selfConsistentScheduledNaturalCausalTrajectoryFiltration mdp initialState
        rewardSource initialTable defaultState varianceProxy baseVisitFloor)
      (stoppingPrefix scheduleIndex))
    (hstoppingUpper : forall scheduleIndex trajectory,
      stoppingPrefix scheduleIndex trajectory <=
        (baseRounds scheduleIndex + windowWidth scheduleIndex : WithTop Nat))
    (scheduleIndex : Nat) :
    eLpNorm
        (selfConsistentScheduledNaturalCausalStoppingTimeAverageRealizedBehaviorRegretProcess
          mdp initialState rewardSource initialTable defaultState varianceProxy
            baseVisitFloor stoppingPrefix scheduleIndex)
        1
        (selfConsistentScheduledCausalSource mdp initialState rewardSource
          initialTable defaultState varianceProxy baseVisitFloor).trajectoryMeasure =
      ENNReal.ofReal
        (selfConsistentScheduledNaturalCausalExpectedAbsoluteRateControlledRawWindowStoppingAverageRealizedBehaviorRegret
          mdp initialState rewardSource initialTable defaultState varianceProxy
            baseVisitFloor stoppingPrefix scheduleIndex) := by
  rw [MemLp.eLpNorm_eq_integral_rpow_norm one_ne_zero ENNReal.one_ne_top
    (memLp_one_selfConsistentScheduledNaturalCausalRateControlledRawWindowStoppingAverageRealizedBehaviorRegret
      mdp initialState rewardSource varianceProxy law initialTable defaultState
        baseVisitFloor hrewardBound baseRounds windowWidth stoppingPrefix
          hstopping hstoppingUpper scheduleIndex)]
  simp [
    selfConsistentScheduledNaturalCausalExpectedAbsoluteRateControlledRawWindowStoppingAverageRealizedBehaviorRegret,
    Real.norm_eq_abs]

/-- The rate-controlled stopped process converges to zero in `L1`. -/
theorem
    eLpNorm_one_selfConsistentScheduledNaturalCausalRateControlledRawWindowStoppingAverageRealizedBehaviorRegret_sub_zero_tendsto_zero
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
    (baseRounds windowWidth : Nat -> Nat)
    (hbaseRounds : forall scheduleIndex, 0 < baseRounds scheduleIndex)
    (hcandidateRate : Tendsto
      (fun scheduleIndex =>
        (((windowWidth scheduleIndex + 1 : Nat) : Real) /
          Real.sqrt (baseRounds scheduleIndex : Real)))
      atTop (nhds 0))
    (stoppingPrefix : Nat ->
      HeterogeneousStochasticEpisodeBatchTrajectory mdp
        (fun t =>
          AdaptiveStochasticEpisodeBatchSource.selfConsistentScheduledEpisodes
            mdp varianceProxy baseVisitFloor t) -> WithTop Nat)
    (hstopping : forall scheduleIndex, IsStoppingTime
      (selfConsistentScheduledNaturalCausalTrajectoryFiltration mdp initialState
        rewardSource initialTable defaultState varianceProxy baseVisitFloor)
      (stoppingPrefix scheduleIndex))
    (hstoppingLower : forall scheduleIndex trajectory,
      (baseRounds scheduleIndex : WithTop Nat) <=
        stoppingPrefix scheduleIndex trajectory)
    (hstoppingUpper : forall scheduleIndex trajectory,
      stoppingPrefix scheduleIndex trajectory <=
        (baseRounds scheduleIndex + windowWidth scheduleIndex : WithTop Nat)) :
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
    selfConsistentScheduledNaturalCausalExpectedAbsoluteRateControlledRawWindowStoppingAverageRealizedBehaviorRegret_tendsto_zero
      mdp initialState rewardSource varianceProxy hvarianceProxy law initialTable
        defaultState support baseVisitFloor hbaseFloor hrewardBound hhorizon
          hbaseVisitFloor baseRounds windowWidth hbaseRounds hcandidateRate
            stoppingPrefix hstopping hstoppingLower hstoppingUpper
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
          (selfConsistentScheduledNaturalCausalExpectedAbsoluteRateControlledRawWindowStoppingAverageRealizedBehaviorRegret
            mdp initialState rewardSource initialTable defaultState varianceProxy
              baseVisitFloor stoppingPrefix scheduleIndex)) := by
      funext scheduleIndex
      exact
        eLpNorm_one_selfConsistentScheduledNaturalCausalRateControlledRawWindowStoppingAverageRealizedBehaviorRegret_eq
          mdp initialState rewardSource varianceProxy law initialTable defaultState
            baseVisitFloor hrewardBound baseRounds windowWidth stoppingPrefix
              hstopping hstoppingUpper scheduleIndex
    rw [hnormEq]
    simpa only [Function.comp_apply, ENNReal.ofReal_zero] using hofReal
  convert hnorm using 1
  funext scheduleIndex
  apply eLpNorm_congr_ae
  exact Filter.Eventually.of_forall fun trajectory => by simp

/-
Terminal L1 theorem for deterministic parameterized raw windows satisfying the
candidate-count/base-square-root rate and natural-prefix growth contracts.
-/
theorem
    selfConsistentScheduledCausalSource_rateControlledRawWindowStoppingTimeNaturalAverageRealizedBehaviorRegret_L1_consistency
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
    (baseRounds windowWidth : Nat -> Nat)
    (hbaseRounds : forall scheduleIndex, 0 < baseRounds scheduleIndex)
    (hindexBase : forall scheduleIndex, scheduleIndex <= baseRounds scheduleIndex)
    (hcandidateRate : Tendsto
      (fun scheduleIndex =>
        (((windowWidth scheduleIndex + 1 : Nat) : Real) /
          Real.sqrt (baseRounds scheduleIndex : Real)))
      atTop (nhds 0))
    (stoppingPrefix : Nat ->
      HeterogeneousStochasticEpisodeBatchTrajectory mdp
        (fun t =>
          AdaptiveStochasticEpisodeBatchSource.selfConsistentScheduledEpisodes
            mdp varianceProxy baseVisitFloor t) -> WithTop Nat)
    (hstopping : forall scheduleIndex, IsStoppingTime
      (selfConsistentScheduledNaturalCausalTrajectoryFiltration mdp initialState
        rewardSource initialTable defaultState varianceProxy baseVisitFloor)
      (stoppingPrefix scheduleIndex))
    (hstoppingLower : forall scheduleIndex trajectory,
      (baseRounds scheduleIndex : WithTop Nat) <=
        stoppingPrefix scheduleIndex trajectory)
    (hstoppingUpper : forall scheduleIndex trajectory,
      stoppingPrefix scheduleIndex trajectory <=
        (baseRounds scheduleIndex + windowWidth scheduleIndex : WithTop Nat)) :
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
        mdp varianceProxy baseVisitFloor baseRounds windowWidth
    let rate :=
      selfConsistentScheduledNaturalCausalRateControlledRawWindowStoppingL1Rate
        mdp varianceProxy baseRounds windowWidth
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
      mdp varianceProxy baseVisitFloor baseRounds windowWidth
  let rate :=
    selfConsistentScheduledNaturalCausalRateControlledRawWindowStoppingL1Rate
      mdp varianceProxy baseRounds windowWidth
  have hmem := fun scheduleIndex =>
    memLp_one_selfConsistentScheduledNaturalCausalRateControlledRawWindowStoppingAverageRealizedBehaviorRegret
      mdp initialState rewardSource varianceProxy law initialTable defaultState
        baseVisitFloor hrewardBound baseRounds windowWidth stoppingPrefix
          hstopping hstoppingUpper scheduleIndex
  have heLp :=
    eLpNorm_one_selfConsistentScheduledNaturalCausalRateControlledRawWindowStoppingAverageRealizedBehaviorRegret_sub_zero_tendsto_zero
      mdp initialState rewardSource varianceProxy hvarianceProxy law initialTable
        defaultState support baseVisitFloor hbaseFloor hrewardBound hhorizon
          hbaseVisitFloor baseRounds windowWidth hbaseRounds hcandidateRate
            stoppingPrefix hstopping hstoppingLower hstoppingUpper
  have hlowerNat : forall scheduleIndex trajectory,
      scheduleIndex <= (stoppingPrefix scheduleIndex trajectory).untopA := by
    intro scheduleIndex trajectory
    obtain ⟨offset, _hoffset, hoffsetEq⟩ :=
      exists_rateControlledRawWindow_offset_untopA_eq stoppingPrefix
        baseRounds windowWidth hstoppingLower hstoppingUpper scheduleIndex
          trajectory
    rw [hoffsetEq]
    exact (hindexBase scheduleIndex).trans
      (Nat.le_add_right (baseRounds scheduleIndex) offset)
  have haeParent :=
    selfConsistentScheduledCausalSource_stoppingTimeNaturalAverageRealizedBehaviorRegret_tendstoAlmostEverywhere_zero_of_nat_le
      mdp initialState rewardSource varianceProxy hvarianceProxy law initialTable
        defaultState support baseVisitFloor hbaseFloor hrewardBound hhorizon
          hbaseVisitFloor stoppingPrefix hstopping hlowerNat
  refine ⟨
    tendsto_id,
    selfConsistentScheduledNaturalCausalAverageRealizedBehaviorRegretProcess_stronglyAdapted
      mdp initialState rewardSource initialTable defaultState varianceProxy
        baseVisitFloor,
    fun scheduleIndex =>
      measurable_selfConsistentScheduledNaturalCausalStoppingTimeAverageRealizedBehaviorRegretProcess
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor stoppingPrefix scheduleIndex (hstopping scheduleIndex),
    hmem,
    fun scheduleIndex =>
      selfConsistentScheduledNaturalCausalExpectedAbsoluteRateControlledRawWindowStoppingAverageRealizedBehaviorRegret_le_budget
        mdp initialState rewardSource varianceProxy hvarianceProxy law initialTable
          defaultState support baseVisitFloor hbaseFloor hrewardBound hhorizon
            hbaseVisitFloor baseRounds windowWidth stoppingPrefix hstopping
              hstoppingLower hstoppingUpper scheduleIndex,
    fun scheduleIndex =>
      selfConsistentScheduledNaturalCausalRateControlledRawWindowStoppingL1Budget_le_rate
        mdp varianceProxy baseVisitFloor baseRounds windowWidth hbaseRounds
          scheduleIndex,
    selfConsistentScheduledNaturalCausalRateControlledRawWindowStoppingL1Budget_tendsto_zero
      mdp varianceProxy baseVisitFloor baseRounds windowWidth hbaseRounds
        hcandidateRate,
    selfConsistentScheduledNaturalCausalExpectedAbsoluteRateControlledRawWindowStoppingAverageRealizedBehaviorRegret_tendsto_zero
      mdp initialState rewardSource varianceProxy hvarianceProxy law initialTable
        defaultState support baseVisitFloor hbaseFloor hrewardBound hhorizon
          hbaseVisitFloor baseRounds windowWidth hbaseRounds hcandidateRate
            stoppingPrefix hstopping hstoppingLower hstoppingUpper,
    heLp,
    ?_,
    haeParent.2.2⟩
  exact tendstoInMeasure_of_tendsto_eLpNorm one_ne_zero
    (fun scheduleIndex => (hmem scheduleIndex).aestronglyMeasurable)
    (by fun_prop) (by simpa [stoppedProcess, source] using heLp)

end AdaptiveStochasticSampledEmpiricalOptimisticSource

end BanditRLProof.FiniteHorizonRL
