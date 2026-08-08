import BanditRLProof.RL.FiniteHorizonAdaptiveStochasticRewardSampledEmpiricalOptimisticSelfConsistentCausalCommonSpaceBehaviorExpectedRegretInMeasureConsistency
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Natural-causal behavior expected-regret L1 consistency

This module upgrades the actual exploratory `source.successorPolicyAt`
expected-regret process from a.e./in-measure convergence to `L1` on the same
genuine heterogeneous dependent causal trajectory measure. Every coordinate
is measurable, nonnegative, and bounded by the deterministic `2 * horizon`
policy envelope. Mathlib dominated convergence therefore gives expected
absolute convergence directly; no realized-return MGF, independent-window
coupling, or extra uniform-integrability assumption is used.

Lean packages coordinate `Integrable` and `MemLp 1`, the exact exponent-one
`eLpNorm`, a named `Lp Real 1` process tending to zero, the existing
`TendstoInMeasure`, and a joint behavior-expected/realized `L1` terminal on the
same source. Coordinate integrability only needs the finite measurable source
contracts, a probability initial law, and bounded mean rewards. Convergence
retains the a.e. parent's finite nonempty Standard Borel State/Action,
positive horizon/base visit floor/reward proxy, uniform mean-compatible
selected-reward sub-Gaussianity, and full-exploration path support.

Failure policy: preserve the actual exploratory behavior policy, the
recommendation/behavior distinction, one dependent source, actual samples,
`n`-prefix to `n+1` selection, scheduled budgets, initial exclusion, and the
separate realized-return centering. This proves behavior expected-regret
`L1`, but not an explicit integrated finite-round rate, convergence on every
trajectory, anytime control, state reachability, minimax/optimal rates, or
complete UCB-VI.
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

/-- The actual successor behavior's expected regret has the global `2H` envelope. -/
theorem selfConsistentScheduledNaturalCausalSuccessorPolicyExpectedRegretProcess_le_two_mul_horizon
    (mdp : MDP State Action) (initialState : Measure State)
    [IsProbabilityMeasure initialState]
    (rewardSource : mdp.MeanCompatibleRewardKernel)
    (initialTable : DeterministicMarkovPolicyTable mdp)
    (defaultState : State) (varianceProxy : NNReal)
    (baseVisitFloor : Real) (hrewardBound : forall state action,
      |mdp.reward state action| <= 1)
    (t : Nat)
    (trajectory : HeterogeneousStochasticEpisodeBatchTrajectory mdp
      (fun s =>
        AdaptiveStochasticEpisodeBatchSource.selfConsistentScheduledEpisodes
          mdp varianceProxy baseVisitFloor s)) :
    selfConsistentScheduledNaturalCausalSuccessorPolicyExpectedRegretProcess
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor t trajectory <=
      2 * (mdp.horizon : Real) := by
  unfold selfConsistentScheduledNaturalCausalSuccessorPolicyExpectedRegretProcess
  exact MarkovPolicy.expectedRegret_le_two_mul_horizon_of_rewardBound
    _ initialState hrewardBound

/-- Every behavior expected-regret coordinate is integrable on the causal source. -/
theorem integrable_selfConsistentScheduledNaturalCausalSuccessorPolicyExpectedRegretProcess
    (mdp : MDP State Action) (initialState : Measure State)
    [IsProbabilityMeasure initialState]
    (rewardSource : mdp.MeanCompatibleRewardKernel)
    (initialTable : DeterministicMarkovPolicyTable mdp)
    (defaultState : State) (varianceProxy : NNReal)
    (baseVisitFloor : Real) (hrewardBound : forall state action,
      |mdp.reward state action| <= 1)
    (t : Nat) :
    Integrable
      (selfConsistentScheduledNaturalCausalSuccessorPolicyExpectedRegretProcess
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor t)
      (selfConsistentScheduledCausalSource mdp initialState rewardSource
        initialTable defaultState varianceProxy baseVisitFloor).trajectoryMeasure := by
  refine Integrable.of_bound
    (measurable_selfConsistentScheduledNaturalCausalSuccessorPolicyExpectedRegretProcess
      mdp initialState rewardSource initialTable defaultState varianceProxy
        baseVisitFloor t).aestronglyMeasurable
    (2 * (mdp.horizon : Real)) ?_
  filter_upwards [] with trajectory
  rw [Real.norm_eq_abs, abs_of_nonneg
    (selfConsistentScheduledNaturalCausalSuccessorPolicyExpectedRegretProcess_nonneg
      mdp initialState rewardSource initialTable defaultState varianceProxy
        baseVisitFloor t trajectory)]
  exact
    selfConsistentScheduledNaturalCausalSuccessorPolicyExpectedRegretProcess_le_two_mul_horizon
      mdp initialState rewardSource initialTable defaultState varianceProxy
        baseVisitFloor hrewardBound t trajectory

/-- Expected absolute behavior regret at one natural-causal coordinate. -/
noncomputable def selfConsistentScheduledNaturalCausalExpectedAbsoluteBehaviorRegret
    (mdp : MDP State Action) (initialState : Measure State)
    [IsProbabilityMeasure initialState]
    (rewardSource : mdp.MeanCompatibleRewardKernel)
    (initialTable : DeterministicMarkovPolicyTable mdp)
    (defaultState : State) (varianceProxy : NNReal)
    (baseVisitFloor : Real) (t : Nat) : Real :=
  integral
    (selfConsistentScheduledCausalSource mdp initialState rewardSource
      initialTable defaultState varianceProxy baseVisitFloor).trajectoryMeasure
    (fun trajectory =>
      |selfConsistentScheduledNaturalCausalSuccessorPolicyExpectedRegretProcess
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor t trajectory|)

/-- Expected absolute behavior regret converges to zero on the same causal source. -/
theorem selfConsistentScheduledNaturalCausalExpectedAbsoluteBehaviorRegret_tendsto_zero
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
      (selfConsistentScheduledNaturalCausalExpectedAbsoluteBehaviorRegret mdp
        initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor)
      atTop (nhds 0) := by
  let source := selfConsistentScheduledCausalSource mdp initialState
    rewardSource initialTable defaultState varianceProxy baseVisitFloor
  let process := fun t =>
    selfConsistentScheduledNaturalCausalSuccessorPolicyExpectedRegretProcess
      mdp initialState rewardSource initialTable defaultState varianceProxy
        baseVisitFloor t
  have hmeas : forall t, AEStronglyMeasurable (process t)
      source.trajectoryMeasure := fun t =>
    (measurable_selfConsistentScheduledNaturalCausalSuccessorPolicyExpectedRegretProcess
      mdp initialState rewardSource initialTable defaultState varianceProxy
        baseVisitFloor t).aestronglyMeasurable
  have hbound : exists C : Real, ∀ᶠ t in atTop,
      ∀ᵐ trajectory ∂source.trajectoryMeasure,
        ‖process t trajectory‖ <= C := by
    refine ⟨2 * (mdp.horizon : Real), Filter.Eventually.of_forall fun t =>
      Filter.Eventually.of_forall fun trajectory => ?_⟩
    rw [Real.norm_eq_abs, abs_of_nonneg
      (selfConsistentScheduledNaturalCausalSuccessorPolicyExpectedRegretProcess_nonneg
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor t trajectory)]
    exact
      selfConsistentScheduledNaturalCausalSuccessorPolicyExpectedRegretProcess_le_two_mul_horizon
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor hrewardBound t trajectory
  have hlimit :=
    selfConsistentScheduledCausalSource_successorPolicyExpectedRegret_tendstoAlmostEverywhere_zero
      mdp initialState rewardSource varianceProxy hvarianceProxy law initialTable
        defaultState support baseVisitFloor hbaseFloor hrewardBound hhorizon
          hbaseVisitFloor
  have hintegral :
      Tendsto (fun t => integral source.trajectoryMeasure (process t))
        atTop (nhds 0) := by
    simpa [source, process] using
      (tendsto_integral_filter_of_norm_le_const
        (l := atTop) (μ := source.trajectoryMeasure)
        (F := process) (f := fun _ => (0 : Real))
        (Filter.Eventually.of_forall hmeas) hbound hlimit)
  change Tendsto
    (fun t => integral source.trajectoryMeasure
      (fun trajectory => |process t trajectory|)) atTop (nhds 0)
  have habs :
      (fun t => integral source.trajectoryMeasure
        (fun trajectory => |process t trajectory|)) =
      fun t => integral source.trajectoryMeasure (process t) := by
    funext t
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun trajectory =>
      abs_of_nonneg
        (selfConsistentScheduledNaturalCausalSuccessorPolicyExpectedRegretProcess_nonneg
          mdp initialState rewardSource initialTable defaultState varianceProxy
            baseVisitFloor t trajectory)
  rw [habs]
  exact hintegral

/-- Every coordinate of the behavior expected-regret process belongs to `L1`. -/
theorem memLp_one_selfConsistentScheduledNaturalCausalSuccessorPolicyExpectedRegretProcess
    (mdp : MDP State Action) (initialState : Measure State)
    [IsProbabilityMeasure initialState]
    (rewardSource : mdp.MeanCompatibleRewardKernel)
    (initialTable : DeterministicMarkovPolicyTable mdp)
    (defaultState : State) (varianceProxy : NNReal)
    (baseVisitFloor : Real)
    (hrewardBound : forall state action, |mdp.reward state action| <= 1)
    (t : Nat) :
    MemLp
      (selfConsistentScheduledNaturalCausalSuccessorPolicyExpectedRegretProcess
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor t)
      1
      (selfConsistentScheduledCausalSource mdp initialState rewardSource
        initialTable defaultState varianceProxy baseVisitFloor).trajectoryMeasure := by
  rw [memLp_one_iff_integrable]
  exact
    integrable_selfConsistentScheduledNaturalCausalSuccessorPolicyExpectedRegretProcess
      mdp initialState rewardSource initialTable defaultState varianceProxy
        baseVisitFloor hrewardBound t

/-- The exponent-one extended norm is the lifted expected absolute behavior regret. -/
theorem eLpNorm_one_selfConsistentScheduledNaturalCausalSuccessorPolicyExpectedRegretProcess_eq
    (mdp : MDP State Action) (initialState : Measure State)
    [IsProbabilityMeasure initialState]
    (rewardSource : mdp.MeanCompatibleRewardKernel)
    (initialTable : DeterministicMarkovPolicyTable mdp)
    (defaultState : State) (varianceProxy : NNReal)
    (baseVisitFloor : Real)
    (hrewardBound : forall state action, |mdp.reward state action| <= 1)
    (t : Nat) :
    eLpNorm
        (selfConsistentScheduledNaturalCausalSuccessorPolicyExpectedRegretProcess
          mdp initialState rewardSource initialTable defaultState varianceProxy
            baseVisitFloor t)
        1
        (selfConsistentScheduledCausalSource mdp initialState rewardSource
          initialTable defaultState varianceProxy baseVisitFloor).trajectoryMeasure =
      ENNReal.ofReal
        (selfConsistentScheduledNaturalCausalExpectedAbsoluteBehaviorRegret mdp
          initialState rewardSource initialTable defaultState varianceProxy
            baseVisitFloor t) := by
  rw [MemLp.eLpNorm_eq_integral_rpow_norm one_ne_zero ENNReal.one_ne_top
    (memLp_one_selfConsistentScheduledNaturalCausalSuccessorPolicyExpectedRegretProcess
      mdp initialState rewardSource initialTable defaultState varianceProxy
        baseVisitFloor hrewardBound t)]
  simp [selfConsistentScheduledNaturalCausalExpectedAbsoluteBehaviorRegret,
    Real.norm_eq_abs]

/-- The exponent-one extended norm of the behavior process tends to zero. -/
theorem eLpNorm_one_selfConsistentScheduledNaturalCausalSuccessorPolicyExpectedRegretProcess_tendsto_zero
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
      (fun t => eLpNorm
        (selfConsistentScheduledNaturalCausalSuccessorPolicyExpectedRegretProcess
          mdp initialState rewardSource initialTable defaultState varianceProxy
            baseVisitFloor t)
        1
        (selfConsistentScheduledCausalSource mdp initialState rewardSource
          initialTable defaultState varianceProxy baseVisitFloor).trajectoryMeasure)
      atTop (nhds 0) := by
  have hexpected :=
    selfConsistentScheduledNaturalCausalExpectedAbsoluteBehaviorRegret_tendsto_zero
      mdp initialState rewardSource varianceProxy hvarianceProxy law initialTable
        defaultState support baseVisitFloor hbaseFloor hrewardBound hhorizon
          hbaseVisitFloor
  have hofReal := (ENNReal.continuous_ofReal.tendsto 0).comp hexpected
  simpa only [ENNReal.ofReal_zero,
    eLpNorm_one_selfConsistentScheduledNaturalCausalSuccessorPolicyExpectedRegretProcess_eq
      mdp initialState rewardSource initialTable defaultState varianceProxy
        baseVisitFloor hrewardBound] using hofReal

/-- Canonical exponent-one norm-of-the-difference convergence. -/
theorem eLpNorm_one_selfConsistentScheduledNaturalCausalSuccessorPolicyExpectedRegretProcess_sub_zero_tendsto_zero
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
      (fun t => eLpNorm
        (selfConsistentScheduledNaturalCausalSuccessorPolicyExpectedRegretProcess
            mdp initialState rewardSource initialTable defaultState varianceProxy
              baseVisitFloor t -
          (fun _ => 0))
        1
        (selfConsistentScheduledCausalSource mdp initialState rewardSource
          initialTable defaultState varianceProxy baseVisitFloor).trajectoryMeasure)
      atTop (nhds 0) := by
  have h :=
    eLpNorm_one_selfConsistentScheduledNaturalCausalSuccessorPolicyExpectedRegretProcess_tendsto_zero
      mdp initialState rewardSource varianceProxy hvarianceProxy law initialTable
        defaultState support baseVisitFloor hbaseFloor hrewardBound hhorizon
          hbaseVisitFloor
  convert h using 1
  funext t
  apply eLpNorm_congr_ae
  exact Filter.Eventually.of_forall fun trajectory => by simp

/-- The behavior expected-regret process as an `Lp Real 1` value. -/
noncomputable def selfConsistentScheduledNaturalCausalBehaviorExpectedRegretLp
    (mdp : MDP State Action) (initialState : Measure State)
    [IsProbabilityMeasure initialState]
    (rewardSource : mdp.MeanCompatibleRewardKernel)
    (initialTable : DeterministicMarkovPolicyTable mdp)
    (defaultState : State) (varianceProxy : NNReal)
    (baseVisitFloor : Real)
    (hrewardBound : forall state action, |mdp.reward state action| <= 1)
    (t : Nat) :
    Lp Real 1
      (selfConsistentScheduledCausalSource mdp initialState rewardSource
        initialTable defaultState varianceProxy baseVisitFloor).trajectoryMeasure :=
  (memLp_one_selfConsistentScheduledNaturalCausalSuccessorPolicyExpectedRegretProcess
    mdp initialState rewardSource initialTable defaultState varianceProxy
      baseVisitFloor hrewardBound t).toLp
    (selfConsistentScheduledNaturalCausalSuccessorPolicyExpectedRegretProcess
      mdp initialState rewardSource initialTable defaultState varianceProxy
        baseVisitFloor t)

/-- The named `Lp` coordinate represents the behavior expected-regret process a.e. -/
theorem selfConsistentScheduledNaturalCausalBehaviorExpectedRegretLp_coeFn_ae_eq
    (mdp : MDP State Action) (initialState : Measure State)
    [IsProbabilityMeasure initialState]
    (rewardSource : mdp.MeanCompatibleRewardKernel)
    (initialTable : DeterministicMarkovPolicyTable mdp)
    (defaultState : State) (varianceProxy : NNReal)
    (baseVisitFloor : Real)
    (hrewardBound : forall state action, |mdp.reward state action| <= 1)
    (t : Nat) :
    (selfConsistentScheduledNaturalCausalBehaviorExpectedRegretLp mdp
        initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor hrewardBound t :
      HeterogeneousStochasticEpisodeBatchTrajectory mdp
        (fun s =>
          AdaptiveStochasticEpisodeBatchSource.selfConsistentScheduledEpisodes
            mdp varianceProxy baseVisitFloor s) -> Real) =ᵐ[
      (selfConsistentScheduledCausalSource mdp initialState rewardSource
        initialTable defaultState varianceProxy baseVisitFloor).trajectoryMeasure]
      selfConsistentScheduledNaturalCausalSuccessorPolicyExpectedRegretProcess
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor t := by
  exact
    (memLp_one_selfConsistentScheduledNaturalCausalSuccessorPolicyExpectedRegretProcess
      mdp initialState rewardSource initialTable defaultState varianceProxy
        baseVisitFloor hrewardBound t).coeFn_toLp

/-- The named behavior expected-regret `Lp Real 1` process converges to zero. -/
theorem selfConsistentScheduledNaturalCausalBehaviorExpectedRegretLp_tendsto_zero
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
      (selfConsistentScheduledNaturalCausalBehaviorExpectedRegretLp mdp
        initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor hrewardBound)
      atTop (nhds 0) := by
  let source := selfConsistentScheduledCausalSource mdp initialState
    rewardSource initialTable defaultState varianceProxy baseVisitFloor
  let process := fun t =>
    selfConsistentScheduledNaturalCausalSuccessorPolicyExpectedRegretProcess
      mdp initialState rewardSource initialTable defaultState varianceProxy
        baseVisitFloor t
  have hmem : forall t, MemLp (process t) 1 source.trajectoryMeasure := fun t =>
    memLp_one_selfConsistentScheduledNaturalCausalSuccessorPolicyExpectedRegretProcess
      mdp initialState rewardSource initialTable defaultState varianceProxy
        baseVisitFloor hrewardBound t
  have hzero : MemLp
      (fun _ : HeterogeneousStochasticEpisodeBatchTrajectory mdp
        (fun s =>
          AdaptiveStochasticEpisodeBatchSource.selfConsistentScheduledEpisodes
            mdp varianceProxy baseVisitFloor s) => (0 : Real))
      1 source.trajectoryMeasure := MemLp.zero'
  have hnorm :=
    eLpNorm_one_selfConsistentScheduledNaturalCausalSuccessorPolicyExpectedRegretProcess_sub_zero_tendsto_zero
      mdp initialState rewardSource varianceProxy hvarianceProxy law initialTable
        defaultState support baseVisitFloor hbaseFloor hrewardBound hhorizon
          hbaseVisitFloor
  have hLp :=
    (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' process hmem (fun _ => (0 : Real))
      hzero).2 (by simpa [process, source] using hnorm)
  simpa [selfConsistentScheduledNaturalCausalBehaviorExpectedRegretLp,
    process, source] using hLp

/-- Full behavior expected-regret `L1` terminal on the genuine causal source. -/
theorem selfConsistentScheduledCausalSource_behaviorExpectedRegret_memLp_eLpNorm_L1_tendsto_zero
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
    (forall t, Integrable
      (selfConsistentScheduledNaturalCausalSuccessorPolicyExpectedRegretProcess
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor t) source.trajectoryMeasure) /\
    (forall t, MemLp
      (selfConsistentScheduledNaturalCausalSuccessorPolicyExpectedRegretProcess
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor t) 1 source.trajectoryMeasure) /\
    (forall t, eLpNorm
        (selfConsistentScheduledNaturalCausalSuccessorPolicyExpectedRegretProcess
          mdp initialState rewardSource initialTable defaultState varianceProxy
            baseVisitFloor t) 1 source.trajectoryMeasure =
      ENNReal.ofReal
        (selfConsistentScheduledNaturalCausalExpectedAbsoluteBehaviorRegret mdp
          initialState rewardSource initialTable defaultState varianceProxy
            baseVisitFloor t)) /\
    Tendsto
      (selfConsistentScheduledNaturalCausalExpectedAbsoluteBehaviorRegret mdp
        initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor) atTop (nhds 0) /\
    Tendsto
      (selfConsistentScheduledNaturalCausalBehaviorExpectedRegretLp mdp
        initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor hrewardBound) atTop (nhds 0) /\
    TendstoInMeasure source.trajectoryMeasure
      (selfConsistentScheduledNaturalCausalSuccessorPolicyExpectedRegretProcess
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor) atTop (fun _ => 0) := by
  dsimp only
  refine ⟨fun t =>
      integrable_selfConsistentScheduledNaturalCausalSuccessorPolicyExpectedRegretProcess
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor hrewardBound t,
    fun t =>
      memLp_one_selfConsistentScheduledNaturalCausalSuccessorPolicyExpectedRegretProcess
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor hrewardBound t,
    fun t =>
      eLpNorm_one_selfConsistentScheduledNaturalCausalSuccessorPolicyExpectedRegretProcess_eq
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor hrewardBound t,
    selfConsistentScheduledNaturalCausalExpectedAbsoluteBehaviorRegret_tendsto_zero
      mdp initialState rewardSource varianceProxy hvarianceProxy law initialTable
        defaultState support baseVisitFloor hbaseFloor hrewardBound hhorizon
          hbaseVisitFloor,
    selfConsistentScheduledNaturalCausalBehaviorExpectedRegretLp_tendsto_zero
      mdp initialState rewardSource varianceProxy hvarianceProxy law initialTable
        defaultState support baseVisitFloor hbaseFloor hrewardBound hhorizon
          hbaseVisitFloor,
    (selfConsistentScheduledCausalSource_successorPolicyExpectedRegret_tendstoInMeasure_zero
      mdp initialState rewardSource varianceProxy hvarianceProxy law initialTable
        defaultState support baseVisitFloor hbaseFloor hrewardBound hhorizon
          hbaseVisitFloor).2⟩

/-- Actual behavior expected and realized regret converge jointly in `L1`. -/
theorem selfConsistentScheduledCausalSource_behaviorExpected_and_realizedRegret_L1_tendsto_zero
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
    ((Tendsto
        (selfConsistentScheduledNaturalCausalBehaviorExpectedRegretLp mdp
          initialState rewardSource initialTable defaultState varianceProxy
            baseVisitFloor hrewardBound) atTop (nhds 0)) /\
      TendstoInMeasure source.trajectoryMeasure
        (selfConsistentScheduledNaturalCausalSuccessorPolicyExpectedRegretProcess
          mdp initialState rewardSource initialTable defaultState varianceProxy
            baseVisitFloor) atTop (fun _ => 0)) /\
    ((Tendsto
        (selfConsistentScheduledNaturalCausalRealizedRegretLp mdp initialState
          rewardSource varianceProxy law initialTable defaultState
            baseVisitFloor hrewardBound) atTop (nhds 0)) /\
      TendstoInMeasure source.trajectoryMeasure
        (selfConsistentScheduledNaturalCausalRealizedRegretProcess mdp
          initialState rewardSource initialTable defaultState varianceProxy
            baseVisitFloor) atTop (fun _ => 0)) := by
  dsimp only
  exact ⟨⟨
      selfConsistentScheduledNaturalCausalBehaviorExpectedRegretLp_tendsto_zero
        mdp initialState rewardSource varianceProxy hvarianceProxy law initialTable
          defaultState support baseVisitFloor hbaseFloor hrewardBound hhorizon
            hbaseVisitFloor,
      (selfConsistentScheduledCausalSource_successorPolicyExpectedRegret_tendstoInMeasure_zero
        mdp initialState rewardSource varianceProxy hvarianceProxy law initialTable
          defaultState support baseVisitFloor hbaseFloor hrewardBound hhorizon
            hbaseVisitFloor).2⟩,
    ⟨selfConsistentScheduledNaturalCausalRealizedRegretLp_tendsto_zero mdp
        initialState rewardSource varianceProxy hvarianceProxy law initialTable
          defaultState support baseVisitFloor hbaseFloor hrewardBound hhorizon
            hbaseVisitFloor,
      selfConsistentScheduledCausalSource_realizedRegret_tendstoInMeasure_zero
        mdp initialState rewardSource varianceProxy hvarianceProxy law initialTable
          defaultState support baseVisitFloor hbaseFloor hrewardBound hhorizon
            hbaseVisitFloor |>.2⟩⟩

end AdaptiveStochasticSampledEmpiricalOptimisticSource

end BanditRLProof.FiniteHorizonRL
