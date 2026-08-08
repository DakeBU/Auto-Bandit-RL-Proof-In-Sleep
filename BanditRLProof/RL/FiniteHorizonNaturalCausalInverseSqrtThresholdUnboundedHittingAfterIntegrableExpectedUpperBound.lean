import BanditRLProof.UnboundedStoppingTimeL2CoordinateIntegrability
import BanditRLProof.RL.FiniteHorizonNaturalCausalBoundedStoppingTimeExplicitDeterministicMomentExpectedAverageRealizedBehaviorRegret
import BanditRLProof.RL.FiniteHorizonNaturalCausalInverseSqrtThresholdUnboundedHittingAfterSquareIntegrableFiniteStoppingTime

/-!
# Expected upper bound at an uncapped inverse-sqrt hitting time

For each fixed threshold index, the genuine Mathlib `hittingAfter` has an L2
round count. Uniform deterministic-coordinate second moments therefore make
the exact stopped average realized behavior regret integrable. Finite-hit
membership then gives the expected threshold upper bound. This is a stopping-
fiber argument, not optional stopping, and no lower expectation bound is
claimed.
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

/-- A round-independent second-moment envelope for every deterministic exact
natural-causal average realized behavior-regret coordinate. -/
noncomputable def
    selfConsistentScheduledNaturalCausalAverageRealizedBehaviorRegretUniformSecondMomentEnvelope
    (mdp : MDP State Action) (varianceProxy : NNReal) : Real :=
  8 * (mdp.horizon : Real) ^ 2 +
    8 * (mdp.globalReturnDeviationPerEpisodeVarianceProxy 1 varianceProxy : Real) *
      Real.exp (1 / 2 : Real)

/-- The uniform deterministic-coordinate second-moment envelope is
nonnegative. -/
theorem
    selfConsistentScheduledNaturalCausalAverageRealizedBehaviorRegretUniformSecondMomentEnvelope_nonneg
    (mdp : MDP State Action) (varianceProxy : NNReal) :
    0 <=
      selfConsistentScheduledNaturalCausalAverageRealizedBehaviorRegretUniformSecondMomentEnvelope
        mdp varianceProxy := by
  unfold
    selfConsistentScheduledNaturalCausalAverageRealizedBehaviorRegretUniformSecondMomentEnvelope
  positivity

/-- The explicit fixed-index stopping-fiber budget used to control the
absolute first moment at an uncapped inverse-sqrt hitting time. -/
noncomputable def
    selfConsistentScheduledNaturalCausalInverseSqrtThresholdUnboundedHittingAfterStoppingFiberAbsoluteFirstMomentBudget
    (mdp : MDP State Action) (initialState : Measure State)
    [IsProbabilityMeasure initialState]
    (rewardSource : mdp.MeanCompatibleRewardKernel)
    (initialTable : DeterministicMarkovPolicyTable mdp)
    (defaultState : State) (varianceProxy : NNReal) (baseVisitFloor : Real)
    (scheduleIndex : Nat) : Real :=
  let source := selfConsistentScheduledCausalSource mdp initialState
    rewardSource initialTable defaultState varianceProxy baseVisitFloor
  let stoppingPrefix :=
    selfConsistentScheduledNaturalCausalInverseSqrtThresholdUnboundedHittingAfterStoppingPrefix
      mdp initialState rewardSource initialTable defaultState varianceProxy
        baseVisitFloor
  Real.sqrt
      (selfConsistentScheduledNaturalCausalAverageRealizedBehaviorRegretUniformSecondMomentEnvelope
        mdp varianceProxy) *
    ∑' rounds : Nat,
      Real.sqrt
        (source.trajectoryMeasure.real
          {trajectory |
            stoppingPrefix scheduleIndex trajectory =
              (rounds : WithTop Nat)})

/-- The fixed-index absolute first-moment budget after eliminating the
stopping-fiber sum in favor of the actual stopping-round second moment and the
universal inverse-square series. -/
noncomputable def
    selfConsistentScheduledNaturalCausalInverseSqrtThresholdUnboundedHittingAfterStoppingRoundSecondMomentAbsoluteFirstMomentBudget
    (mdp : MDP State Action) (initialState : Measure State)
    [IsProbabilityMeasure initialState]
    (rewardSource : mdp.MeanCompatibleRewardKernel)
    (initialTable : DeterministicMarkovPolicyTable mdp)
    (defaultState : State) (varianceProxy : NNReal) (baseVisitFloor : Real)
    (scheduleIndex : Nat) : Real :=
  let source := selfConsistentScheduledCausalSource mdp initialState
    rewardSource initialTable defaultState varianceProxy baseVisitFloor
  let stoppingPrefix :=
    selfConsistentScheduledNaturalCausalInverseSqrtThresholdUnboundedHittingAfterStoppingPrefix
      mdp initialState rewardSource initialTable defaultState varianceProxy
        baseVisitFloor
  Real.sqrt
      (selfConsistentScheduledNaturalCausalAverageRealizedBehaviorRegretUniformSecondMomentEnvelope
        mdp varianceProxy) *
    ((1 / 2 : Real) *
      (integral source.trajectoryMeasure
          (fun trajectory =>
            ((((stoppingPrefix scheduleIndex trajectory).untopA + 1 : Nat) :
                Real)) ^ 2) +
        ∑' rounds : Nat,
          1 / (((rounds + 1 : Nat) : Real) ^ 2)))

/-- Deterministic fixed-index absolute first-moment budget obtained by
replacing the actual stopping-round second moment with the canonical
checkpoint/failure-series upper bound. -/
noncomputable def
    selfConsistentScheduledNaturalCausalInverseSqrtThresholdUnboundedHittingAfterDeterministicStoppingRoundSecondMomentAbsoluteFirstMomentBudget
    (mdp : MDP State Action) (varianceProxy : NNReal)
    (baseVisitFloor : Real) (scheduleIndex : Nat) : Real :=
  Real.sqrt
      (selfConsistentScheduledNaturalCausalAverageRealizedBehaviorRegretUniformSecondMomentEnvelope
        mdp varianceProxy) *
    ((1 / 2 : Real) *
      (inverseSqrtThresholdUnboundedHittingAfterStoppingRoundSecondMomentBudget
          mdp varianceProxy baseVisitFloor scheduleIndex +
        ∑' rounds : Nat,
          1 / (((rounds + 1 : Nat) : Real) ^ 2)))

/-- Every deterministic coordinate has second moment bounded by one constant,
including the zero-round coordinate. -/
theorem
    integral_sq_selfConsistentScheduledNaturalCausalAverageRealizedBehaviorRegretProcess_le_uniformSecondMomentEnvelope
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
          selfConsistentScheduledNaturalCausalAverageRealizedBehaviorRegretProcess
            mdp initialState rewardSource initialTable defaultState varianceProxy
              baseVisitFloor rounds trajectory ^ 2) <=
      selfConsistentScheduledNaturalCausalAverageRealizedBehaviorRegretUniformSecondMomentEnvelope
        mdp varianceProxy := by
  by_cases hrounds : rounds = 0
  · subst rounds
    have hprocessZero :
        selfConsistentScheduledNaturalCausalAverageRealizedBehaviorRegretProcess
            mdp initialState rewardSource initialTable defaultState varianceProxy
              baseVisitFloor 0 = fun _ => 0 := by
      funext trajectory
      rw [selfConsistentScheduledNaturalCausalAverageRealizedBehaviorRegretProcess_eq_expected_sub_deviation]
      simp
    rw [hprocessZero]
    simpa using
      selfConsistentScheduledNaturalCausalAverageRealizedBehaviorRegretUniformSecondMomentEnvelope_nonneg
        mdp varianceProxy
  · have hroundsPos : 0 < rounds := Nat.pos_of_ne_zero hrounds
    have hcoordinate :=
      integral_sq_selfConsistentScheduledNaturalCausalAverageRealizedBehaviorRegretProcess_le_secondMomentEnvelope
        mdp initialState rewardSource varianceProxy law initialTable defaultState
          baseVisitFloor hrewardBound rounds hroundsPos
    apply hcoordinate.trans
    let r : Real := rounds
    let proxy : Real :=
      selfConsistentScheduledNaturalCausalCumulativeReturnVarianceProxy
        mdp varianceProxy baseVisitFloor rounds
    let globalProxy : Real :=
      mdp.globalReturnDeviationPerEpisodeVarianceProxy 1 varianceProxy
    let exponential : Real := Real.exp (1 / 2 : Real)
    have hr : 1 <= r := by
      dsimp [r]
      exact_mod_cast hroundsPos
    have hrPos : 0 < r := lt_of_lt_of_le (by norm_num) hr
    have hproxy : proxy <= r * globalProxy := by
      dsimp [proxy, r, globalProxy]
      exact_mod_cast
        selfConsistentScheduledNaturalCausalCumulativeReturnVarianceProxy_le_rounds_mul
          mdp varianceProxy baseVisitFloor rounds
    have hproxyNonneg : 0 <= proxy := by
      dsimp [proxy]
      positivity
    have hglobalNonneg : 0 <= globalProxy := by
      dsimp [globalProxy]
      positivity
    have hexponentialPos : 0 < exponential := by
      dsimp [exponential]
      exact Real.exp_pos _
    have hreturnTerm :
        (2 / r ^ 2) * (4 * proxy * exponential) <=
          8 * globalProxy * exponential := by
      calc
        (2 / r ^ 2) * (4 * proxy * exponential) <=
            (2 / r ^ 2) * (4 * (r * globalProxy) * exponential) := by
              gcongr
        _ = (8 * globalProxy * exponential) / r := by
          field_simp
          ring
        _ <= 8 * globalProxy * exponential := by
          apply (div_le_iff₀ hrPos).2
          have hnonneg : 0 <= 8 * globalProxy * exponential := by positivity
          nlinarith
    unfold
      selfConsistentScheduledNaturalCausalAverageRealizedBehaviorRegretSecondMomentEnvelope
      selfConsistentScheduledNaturalCausalAverageRealizedBehaviorRegretUniformSecondMomentEnvelope
    change
      8 * (mdp.horizon : Real) ^ 2 +
            (2 / r ^ 2) * (4 * proxy * exponential) <=
        8 * (mdp.horizon : Real) ^ 2 + 8 * globalProxy * exponential
    simpa only [add_comm] using
      add_le_add_left hreturnTerm (8 * (mdp.horizon : Real) ^ 2)

/-- For every fixed threshold index, the exact average realized behavior
regret stopped at the genuine uncapped inverse-sqrt first passage is integrable
and its expectation is at most the hit threshold. -/
theorem
    selfConsistentScheduledCausalSource_inverseSqrtThresholdUnboundedHittingAfter_stoppedAverageRealizedBehaviorRegret_integrable_and_integral_le_threshold
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
    (hhorizon : 4 < mdp.horizon) (hbaseVisitFloor : 0 < baseVisitFloor)
    (scheduleIndex : Nat) :
    let source := selfConsistentScheduledCausalSource mdp initialState
      rewardSource initialTable defaultState varianceProxy baseVisitFloor
    let stoppingPrefix :=
      selfConsistentScheduledNaturalCausalInverseSqrtThresholdUnboundedHittingAfterStoppingPrefix
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor
    let stoppedProcess :=
      selfConsistentScheduledNaturalCausalStoppingTimeAverageRealizedBehaviorRegretProcess
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor stoppingPrefix scheduleIndex
    Integrable stoppedProcess source.trajectoryMeasure /\
      integral source.trajectoryMeasure stoppedProcess <=
        selfConsistentScheduledNaturalCausalInverseSqrtFirstPassageThreshold
          scheduleIndex := by
  dsimp only
  let source := selfConsistentScheduledCausalSource mdp initialState
    rewardSource initialTable defaultState varianceProxy baseVisitFloor
  let stoppingPrefix :=
    selfConsistentScheduledNaturalCausalInverseSqrtThresholdUnboundedHittingAfterStoppingPrefix
      mdp initialState rewardSource initialTable defaultState varianceProxy
        baseVisitFloor
  let process :=
    selfConsistentScheduledNaturalCausalAverageRealizedBehaviorRegretProcess
      mdp initialState rewardSource initialTable defaultState varianceProxy
        baseVisitFloor
  let stoppedProcess :=
    selfConsistentScheduledNaturalCausalStoppingTimeAverageRealizedBehaviorRegretProcess
      mdp initialState rewardSource initialTable defaultState varianceProxy
        baseVisitFloor stoppingPrefix scheduleIndex
  have hstopping : IsStoppingTime
      (selfConsistentScheduledNaturalCausalTrajectoryFiltration mdp initialState
        rewardSource initialTable defaultState varianceProxy baseVisitFloor)
      (stoppingPrefix scheduleIndex) := by
    simpa only [stoppingPrefix] using
      selfConsistentScheduledNaturalCausalInverseSqrtThresholdUnboundedHittingAfterStoppingPrefix_isStoppingTime
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor scheduleIndex
  have hstop : BanditRLProof.OFUL.SquareIntegrableFiniteStoppingTime
      source.trajectoryMeasure (stoppingPrefix scheduleIndex) := by
    simpa only [source, stoppingPrefix] using
      selfConsistentScheduledCausalSource_inverseSqrtThresholdUnboundedHittingAfter_squareIntegrableFiniteStoppingTime
        mdp initialState rewardSource varianceProxy hvarianceProxy law initialTable
          defaultState support baseVisitFloor hbaseFloor hrewardBound hhorizon
            hbaseVisitFloor scheduleIndex
  have hstoppedMeasurable : Measurable stoppedProcess := by
    simpa only [stoppedProcess] using
      measurable_selfConsistentScheduledNaturalCausalStoppingTimeAverageRealizedBehaviorRegretProcess
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor stoppingPrefix scheduleIndex hstopping
  have hstoppedIntegrable :
      Integrable stoppedProcess source.trajectoryMeasure := by
    have htransport :=
      BanditRLProof.integrable_stoppedValue_of_uniform_secondMoment_of_memLp_two_rounds
        source.trajectoryMeasure (stoppingPrefix scheduleIndex)
          hstopping.measurable' hstop.finite_ae hstop.memLp_rounds process
            (by simpa only [stoppedProcess, process] using hstoppedMeasurable)
            (selfConsistentScheduledNaturalCausalAverageRealizedBehaviorRegretUniformSecondMomentEnvelope
              mdp varianceProxy)
            (fun rounds => by
              simpa only [process, source] using
                memLp_two_selfConsistentScheduledNaturalCausalAverageRealizedBehaviorRegretProcess
                  mdp initialState rewardSource varianceProxy law initialTable
                    defaultState baseVisitFloor hrewardBound rounds)
            (fun rounds => by
              simpa only [process, source] using
                integral_sq_selfConsistentScheduledNaturalCausalAverageRealizedBehaviorRegretProcess_le_uniformSecondMomentEnvelope
                  mdp initialState rewardSource varianceProxy law initialTable
                    defaultState baseVisitFloor hrewardBound rounds)
    simpa only [stoppedProcess, process,
      selfConsistentScheduledNaturalCausalStoppingTimeAverageRealizedBehaviorRegretProcess]
      using htransport
  have hpoint : ∀ᵐ trajectory ∂source.trajectoryMeasure,
      stoppedProcess trajectory <=
        selfConsistentScheduledNaturalCausalInverseSqrtFirstPassageThreshold
          scheduleIndex := by
    filter_upwards [hstop.finite_ae] with trajectory hfinite
    simpa only [stoppedProcess, stoppingPrefix,
      selfConsistentScheduledNaturalCausalStoppingTimeAverageRealizedBehaviorRegretProcess_apply]
      using
        selfConsistentScheduledNaturalCausalAverageRealizedBehaviorRegretProcess_untopA_unboundedHittingAfter_le_threshold
          mdp initialState rewardSource initialTable defaultState varianceProxy
            baseVisitFloor scheduleIndex trajectory hfinite
  refine ⟨hstoppedIntegrable, ?_⟩
  calc
    integral source.trajectoryMeasure stoppedProcess <=
        integral source.trajectoryMeasure
          (fun _ =>
            selfConsistentScheduledNaturalCausalInverseSqrtFirstPassageThreshold
              scheduleIndex) :=
      integral_mono_ae hstoppedIntegrable (integrable_const _) hpoint
    _ = selfConsistentScheduledNaturalCausalInverseSqrtFirstPassageThreshold
          scheduleIndex := by simp

/-- For each fixed threshold index, the exact stopped average realized
behavior regret has an explicit absolute first-moment bound given by the
summable square-root masses of the genuine stopping fibers. The bound is not
uniform in the threshold index and does not use optional stopping. -/
theorem
    selfConsistentScheduledCausalSource_inverseSqrtThresholdUnboundedHittingAfter_stoppedAverageRealizedBehaviorRegret_integrable_and_integral_abs_le_stoppingFiberBudget
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
    (hhorizon : 4 < mdp.horizon) (hbaseVisitFloor : 0 < baseVisitFloor)
    (scheduleIndex : Nat) :
    let source := selfConsistentScheduledCausalSource mdp initialState
      rewardSource initialTable defaultState varianceProxy baseVisitFloor
    let stoppingPrefix :=
      selfConsistentScheduledNaturalCausalInverseSqrtThresholdUnboundedHittingAfterStoppingPrefix
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor
    let stoppedProcess :=
      selfConsistentScheduledNaturalCausalStoppingTimeAverageRealizedBehaviorRegretProcess
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor stoppingPrefix scheduleIndex
    Integrable stoppedProcess source.trajectoryMeasure /\
      integral source.trajectoryMeasure
          (fun trajectory => |stoppedProcess trajectory|) <=
        selfConsistentScheduledNaturalCausalInverseSqrtThresholdUnboundedHittingAfterStoppingFiberAbsoluteFirstMomentBudget
          mdp initialState rewardSource initialTable defaultState varianceProxy
            baseVisitFloor scheduleIndex := by
  dsimp only
  let source := selfConsistentScheduledCausalSource mdp initialState
    rewardSource initialTable defaultState varianceProxy baseVisitFloor
  let stoppingPrefix :=
    selfConsistentScheduledNaturalCausalInverseSqrtThresholdUnboundedHittingAfterStoppingPrefix
      mdp initialState rewardSource initialTable defaultState varianceProxy
        baseVisitFloor
  let process :=
    selfConsistentScheduledNaturalCausalAverageRealizedBehaviorRegretProcess
      mdp initialState rewardSource initialTable defaultState varianceProxy
        baseVisitFloor
  let stoppedProcess :=
    selfConsistentScheduledNaturalCausalStoppingTimeAverageRealizedBehaviorRegretProcess
      mdp initialState rewardSource initialTable defaultState varianceProxy
        baseVisitFloor stoppingPrefix scheduleIndex
  have hstopping : IsStoppingTime
      (selfConsistentScheduledNaturalCausalTrajectoryFiltration mdp initialState
        rewardSource initialTable defaultState varianceProxy baseVisitFloor)
      (stoppingPrefix scheduleIndex) := by
    simpa only [stoppingPrefix] using
      selfConsistentScheduledNaturalCausalInverseSqrtThresholdUnboundedHittingAfterStoppingPrefix_isStoppingTime
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor scheduleIndex
  have hstop : BanditRLProof.OFUL.SquareIntegrableFiniteStoppingTime
      source.trajectoryMeasure (stoppingPrefix scheduleIndex) := by
    simpa only [source, stoppingPrefix] using
      selfConsistentScheduledCausalSource_inverseSqrtThresholdUnboundedHittingAfter_squareIntegrableFiniteStoppingTime
        mdp initialState rewardSource varianceProxy hvarianceProxy law initialTable
          defaultState support baseVisitFloor hbaseFloor hrewardBound hhorizon
            hbaseVisitFloor scheduleIndex
  have hparent :=
    selfConsistentScheduledCausalSource_inverseSqrtThresholdUnboundedHittingAfter_stoppedAverageRealizedBehaviorRegret_integrable_and_integral_le_threshold
      mdp initialState rewardSource varianceProxy hvarianceProxy law initialTable
        defaultState support baseVisitFloor hbaseFloor hrewardBound hhorizon
          hbaseVisitFloor scheduleIndex
  have hstoppedIntegrable :
      Integrable stoppedProcess source.trajectoryMeasure := by
    simpa only [stoppedProcess, source, stoppingPrefix] using hparent.1
  have habsolute :=
    BanditRLProof.integral_abs_stoppedValue_le_uniformSecondMoment_mul_tsum_sqrt_stoppingFiberRealMeasure_of_memLp_two_rounds
      source.trajectoryMeasure (stoppingPrefix scheduleIndex)
        hstopping.measurable' hstop.finite_ae hstop.memLp_rounds process
          (selfConsistentScheduledNaturalCausalAverageRealizedBehaviorRegretUniformSecondMomentEnvelope
            mdp varianceProxy)
          (fun rounds => by
            simpa only [process, source] using
              memLp_two_selfConsistentScheduledNaturalCausalAverageRealizedBehaviorRegretProcess
                mdp initialState rewardSource varianceProxy law initialTable
                  defaultState baseVisitFloor hrewardBound rounds)
          (fun rounds => by
            simpa only [process, source] using
              integral_sq_selfConsistentScheduledNaturalCausalAverageRealizedBehaviorRegretProcess_le_uniformSecondMomentEnvelope
                mdp initialState rewardSource varianceProxy law initialTable
                  defaultState baseVisitFloor hrewardBound rounds)
  refine ⟨hstoppedIntegrable, ?_⟩
  simpa only [stoppedProcess, process,
    selfConsistentScheduledNaturalCausalStoppingTimeAverageRealizedBehaviorRegretProcess,
    selfConsistentScheduledNaturalCausalInverseSqrtThresholdUnboundedHittingAfterStoppingFiberAbsoluteFirstMomentBudget,
    source, stoppingPrefix] using habsolute

/-- For each fixed threshold index, the exact stopped average realized
behavior regret is integrable and its absolute first moment is controlled by
the actual stopping-round second moment plus the universal inverse-square
series. This is not a schedule-index-uniform or asymptotic estimate. -/
theorem
    selfConsistentScheduledCausalSource_inverseSqrtThresholdUnboundedHittingAfter_stoppedAverageRealizedBehaviorRegret_integrable_and_integral_abs_le_stoppingRoundSecondMomentBudget
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
    (hhorizon : 4 < mdp.horizon) (hbaseVisitFloor : 0 < baseVisitFloor)
    (scheduleIndex : Nat) :
    let source := selfConsistentScheduledCausalSource mdp initialState
      rewardSource initialTable defaultState varianceProxy baseVisitFloor
    let stoppingPrefix :=
      selfConsistentScheduledNaturalCausalInverseSqrtThresholdUnboundedHittingAfterStoppingPrefix
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor
    let stoppedProcess :=
      selfConsistentScheduledNaturalCausalStoppingTimeAverageRealizedBehaviorRegretProcess
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor stoppingPrefix scheduleIndex
    Integrable stoppedProcess source.trajectoryMeasure /\
      integral source.trajectoryMeasure
          (fun trajectory => |stoppedProcess trajectory|) <=
        selfConsistentScheduledNaturalCausalInverseSqrtThresholdUnboundedHittingAfterStoppingRoundSecondMomentAbsoluteFirstMomentBudget
          mdp initialState rewardSource initialTable defaultState varianceProxy
            baseVisitFloor scheduleIndex := by
  dsimp only
  let source := selfConsistentScheduledCausalSource mdp initialState
    rewardSource initialTable defaultState varianceProxy baseVisitFloor
  let stoppingPrefix :=
    selfConsistentScheduledNaturalCausalInverseSqrtThresholdUnboundedHittingAfterStoppingPrefix
      mdp initialState rewardSource initialTable defaultState varianceProxy
        baseVisitFloor
  let process :=
    selfConsistentScheduledNaturalCausalAverageRealizedBehaviorRegretProcess
      mdp initialState rewardSource initialTable defaultState varianceProxy
        baseVisitFloor
  let stoppedProcess :=
    selfConsistentScheduledNaturalCausalStoppingTimeAverageRealizedBehaviorRegretProcess
      mdp initialState rewardSource initialTable defaultState varianceProxy
        baseVisitFloor stoppingPrefix scheduleIndex
  have hstopping : IsStoppingTime
      (selfConsistentScheduledNaturalCausalTrajectoryFiltration mdp initialState
        rewardSource initialTable defaultState varianceProxy baseVisitFloor)
      (stoppingPrefix scheduleIndex) := by
    simpa only [stoppingPrefix] using
      selfConsistentScheduledNaturalCausalInverseSqrtThresholdUnboundedHittingAfterStoppingPrefix_isStoppingTime
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor scheduleIndex
  have hstop : BanditRLProof.OFUL.SquareIntegrableFiniteStoppingTime
      source.trajectoryMeasure (stoppingPrefix scheduleIndex) := by
    simpa only [source, stoppingPrefix] using
      selfConsistentScheduledCausalSource_inverseSqrtThresholdUnboundedHittingAfter_squareIntegrableFiniteStoppingTime
        mdp initialState rewardSource varianceProxy hvarianceProxy law initialTable
          defaultState support baseVisitFloor hbaseFloor hrewardBound hhorizon
            hbaseVisitFloor scheduleIndex
  have hparent :=
    selfConsistentScheduledCausalSource_inverseSqrtThresholdUnboundedHittingAfter_stoppedAverageRealizedBehaviorRegret_integrable_and_integral_abs_le_stoppingFiberBudget
      mdp initialState rewardSource varianceProxy hvarianceProxy law initialTable
        defaultState support baseVisitFloor hbaseFloor hrewardBound hhorizon
          hbaseVisitFloor scheduleIndex
  have hstoppedIntegrable :
      Integrable stoppedProcess source.trajectoryMeasure := by
    simpa only [stoppedProcess, source, stoppingPrefix] using hparent.1
  have habsolute :=
    BanditRLProof.integral_abs_stoppedValue_le_uniformSecondMoment_mul_half_roundSecondMoment_add_inverseSquareTsum_of_memLp_two_rounds
      source.trajectoryMeasure (stoppingPrefix scheduleIndex)
        hstopping.measurable' hstop.finite_ae hstop.memLp_rounds process
          (selfConsistentScheduledNaturalCausalAverageRealizedBehaviorRegretUniformSecondMomentEnvelope
            mdp varianceProxy)
          (fun rounds => by
            simpa only [process, source] using
              memLp_two_selfConsistentScheduledNaturalCausalAverageRealizedBehaviorRegretProcess
                mdp initialState rewardSource varianceProxy law initialTable
                  defaultState baseVisitFloor hrewardBound rounds)
          (fun rounds => by
            simpa only [process, source] using
              integral_sq_selfConsistentScheduledNaturalCausalAverageRealizedBehaviorRegretProcess_le_uniformSecondMomentEnvelope
                mdp initialState rewardSource varianceProxy law initialTable
                  defaultState baseVisitFloor hrewardBound rounds)
  refine ⟨hstoppedIntegrable, ?_⟩
  simpa only [stoppedProcess, process,
    selfConsistentScheduledNaturalCausalStoppingTimeAverageRealizedBehaviorRegretProcess,
    selfConsistentScheduledNaturalCausalInverseSqrtThresholdUnboundedHittingAfterStoppingRoundSecondMomentAbsoluteFirstMomentBudget,
    source, stoppingPrefix] using habsolute

/-- For each fixed threshold index, the exact stopped average realized
behavior regret is integrable and its absolute first moment is controlled by a
fully deterministic checkpoint/failure-series budget. The endpoint contains
no unevaluated stopping-time integral. -/
theorem
    selfConsistentScheduledCausalSource_inverseSqrtThresholdUnboundedHittingAfter_stoppedAverageRealizedBehaviorRegret_integrable_and_integral_abs_le_deterministicStoppingRoundSecondMomentBudget
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
    (hhorizon : 4 < mdp.horizon) (hbaseVisitFloor : 0 < baseVisitFloor)
    (scheduleIndex : Nat) :
    let source := selfConsistentScheduledCausalSource mdp initialState
      rewardSource initialTable defaultState varianceProxy baseVisitFloor
    let stoppingPrefix :=
      selfConsistentScheduledNaturalCausalInverseSqrtThresholdUnboundedHittingAfterStoppingPrefix
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor
    let stoppedProcess :=
      selfConsistentScheduledNaturalCausalStoppingTimeAverageRealizedBehaviorRegretProcess
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor stoppingPrefix scheduleIndex
    Integrable stoppedProcess source.trajectoryMeasure /\
      integral source.trajectoryMeasure
          (fun trajectory => |stoppedProcess trajectory|) <=
        selfConsistentScheduledNaturalCausalInverseSqrtThresholdUnboundedHittingAfterDeterministicStoppingRoundSecondMomentAbsoluteFirstMomentBudget
          mdp varianceProxy baseVisitFloor scheduleIndex := by
  dsimp only
  let source := selfConsistentScheduledCausalSource mdp initialState
    rewardSource initialTable defaultState varianceProxy baseVisitFloor
  let stoppingPrefix :=
    selfConsistentScheduledNaturalCausalInverseSqrtThresholdUnboundedHittingAfterStoppingPrefix
      mdp initialState rewardSource initialTable defaultState varianceProxy
        baseVisitFloor
  let stoppedProcess :=
    selfConsistentScheduledNaturalCausalStoppingTimeAverageRealizedBehaviorRegretProcess
      mdp initialState rewardSource initialTable defaultState varianceProxy
        baseVisitFloor stoppingPrefix scheduleIndex
  have hparent :=
    selfConsistentScheduledCausalSource_inverseSqrtThresholdUnboundedHittingAfter_stoppedAverageRealizedBehaviorRegret_integrable_and_integral_abs_le_stoppingRoundSecondMomentBudget
      mdp initialState rewardSource varianceProxy hvarianceProxy law initialTable
        defaultState support baseVisitFloor hbaseFloor hrewardBound hhorizon
          hbaseVisitFloor scheduleIndex
  have hround :=
    selfConsistentScheduledCausalSource_inverseSqrtThresholdUnboundedHittingAfter_integral_stoppingRound_sq_le_budget
      mdp initialState rewardSource varianceProxy hvarianceProxy law initialTable
        defaultState support baseVisitFloor hbaseFloor hrewardBound hhorizon
          hbaseVisitFloor scheduleIndex
  dsimp only at hround
  have hbudgetLe :
      selfConsistentScheduledNaturalCausalInverseSqrtThresholdUnboundedHittingAfterStoppingRoundSecondMomentAbsoluteFirstMomentBudget
          mdp initialState rewardSource initialTable defaultState varianceProxy
            baseVisitFloor scheduleIndex <=
        selfConsistentScheduledNaturalCausalInverseSqrtThresholdUnboundedHittingAfterDeterministicStoppingRoundSecondMomentAbsoluteFirstMomentBudget
          mdp varianceProxy baseVisitFloor scheduleIndex := by
    unfold
      selfConsistentScheduledNaturalCausalInverseSqrtThresholdUnboundedHittingAfterStoppingRoundSecondMomentAbsoluteFirstMomentBudget
      selfConsistentScheduledNaturalCausalInverseSqrtThresholdUnboundedHittingAfterDeterministicStoppingRoundSecondMomentAbsoluteFirstMomentBudget
    dsimp only
    apply mul_le_mul_of_nonneg_left
    · apply mul_le_mul_of_nonneg_left
      · exact add_le_add hround le_rfl
      · norm_num
    · exact Real.sqrt_nonneg _
  refine ⟨?_, ?_⟩
  · simpa only [stoppedProcess, source, stoppingPrefix] using hparent.1
  · simpa only [stoppedProcess, source, stoppingPrefix] using
      hparent.2.trans hbudgetLe

end AdaptiveStochasticSampledEmpiricalOptimisticSource
end BanditRLProof.FiniteHorizonRL
