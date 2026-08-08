import BanditRLProof.MeasureL2Indicator
import BanditRLProof.RL.FiniteHorizonNaturalCausalAverageRealizedBehaviorRegretL1Consistency
import BanditRLProof.RL.FiniteHorizonNaturalCausalBoundedStoppingTimeExplicitThreeQuarterGoodEventAverageRealizedBehaviorRegret

/-!
# Expected natural-causal realized regret at a bounded stopping time

The fixed-confidence three-quarter event is integrated using an exact `L2`
second moment. The expectation proof is a pointwise event decomposition and a
`2,2` Holder bound, not optional stopping.
-/

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal ProbabilityTheory

namespace BanditRLProof.FiniteHorizonRL

universe u v

variable {State : Type u} {Action : Type v}
    [MeasurableSpace State] [MeasurableSpace Action]
    [Fintype State] [Fintype Action]
    [DecidableEq State] [DecidableEq Action]
    [MeasurableSingletonClass State] [MeasurableSingletonClass Action]
    [Nonempty State] [Nonempty Action]

namespace AdaptiveStochasticSampledEmpiricalOptimisticSource

/-- The cumulative behavior expected-regret process belongs to `L2` under its
deterministic finite-prefix envelope. -/
theorem memLp_two_selfConsistentScheduledNaturalCausalCumulativeBehaviorExpectedRegretProcess
    (mdp : MDP State Action) (initialState : Measure State)
    [IsProbabilityMeasure initialState]
    (rewardSource : mdp.MeanCompatibleRewardKernel)
    (initialTable : DeterministicMarkovPolicyTable mdp)
    (defaultState : State) (varianceProxy : NNReal)
    (baseVisitFloor : Real)
    (hrewardBound : forall state action, |mdp.reward state action| <= 1)
    (rounds : Nat) :
    MemLp
      (selfConsistentScheduledNaturalCausalCumulativeBehaviorExpectedRegretProcess
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor rounds)
      2
      (selfConsistentScheduledCausalSource mdp initialState rewardSource
        initialTable defaultState varianceProxy baseVisitFloor).trajectoryMeasure := by
  let process :=
    selfConsistentScheduledNaturalCausalCumulativeBehaviorExpectedRegretProcess
      mdp initialState rewardSource initialTable defaultState varianceProxy
        baseVisitFloor rounds
  have hmeasurable : Measurable process := by
    simpa [process] using
      measurable_selfConsistentScheduledNaturalCausalCumulativeBehaviorExpectedRegretProcess
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor rounds
  refine MemLp.of_bound hmeasurable.aestronglyMeasurable
    ((rounds : Real) * (2 * (mdp.horizon : Real))) ?_
  exact Filter.Eventually.of_forall fun trajectory => by
    rw [Real.norm_eq_abs, abs_of_nonneg
      (selfConsistentScheduledNaturalCausalCumulativeBehaviorExpectedRegretProcess_nonneg
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor rounds trajectory)]
    change
      (Finset.range rounds).sum (fun t =>
          selfConsistentScheduledNaturalCausalSuccessorPolicyExpectedRegretProcess
            mdp initialState rewardSource initialTable defaultState varianceProxy
              baseVisitFloor t trajectory) <=
        (rounds : Real) * (2 * (mdp.horizon : Real))
    calc
      (Finset.range rounds).sum (fun t =>
          selfConsistentScheduledNaturalCausalSuccessorPolicyExpectedRegretProcess
            mdp initialState rewardSource initialTable defaultState varianceProxy
              baseVisitFloor t trajectory) <=
          (Finset.range rounds).sum (fun _ => 2 * (mdp.horizon : Real)) := by
        exact Finset.sum_le_sum fun t _ =>
          selfConsistentScheduledNaturalCausalSuccessorPolicyExpectedRegretProcess_le_two_mul_horizon
            mdp initialState rewardSource initialTable defaultState varianceProxy
              baseVisitFloor hrewardBound t trajectory
      _ = (rounds : Real) * (2 * (mdp.horizon : Real)) := by simp

/-- Every deterministic-prefix average realized behavior-regret coordinate is
in `L2`: the behavior component is bounded and the centered return component
is sub-Gaussian. -/
theorem memLp_two_selfConsistentScheduledNaturalCausalAverageRealizedBehaviorRegretProcess
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
      2
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
  have hexpected : MemLp expected 2 mu := by
    simpa [expected, mu] using
      memLp_two_selfConsistentScheduledNaturalCausalCumulativeBehaviorExpectedRegretProcess
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor hrewardBound rounds
  have hdeviation : MemLp deviation 2 mu := by
    exact
      (selfConsistentScheduledNaturalCausalCumulativeReturnDeviationProcess_hasSubgaussianMGF
        mdp initialState rewardSource varianceProxy law initialTable defaultState
          baseVisitFloor hrewardBound rounds).memLp 2
  have hquotient : MemLp
      (fun trajectory => (expected trajectory - deviation trajectory) /
        (rounds : Real)) 2 mu := by
    simpa [div_eq_mul_inv] using
      (hexpected.sub hdeviation).mul_const (((rounds : Real))⁻¹)
  refine hquotient.congr_norm
    (measurable_selfConsistentScheduledNaturalCausalAverageRealizedBehaviorRegretProcess
      mdp initialState rewardSource initialTable defaultState varianceProxy
        baseVisitFloor rounds).aestronglyMeasurable ?_
  exact Filter.Eventually.of_forall fun trajectory => by
    rw [selfConsistentScheduledNaturalCausalAverageRealizedBehaviorRegretProcess_eq_expected_sub_deviation]

/-- Mathlib bounded-stopping transport gives `L2` for the exact stopped
average realized behavior regret. -/
theorem memLp_two_selfConsistentScheduledNaturalCausalStoppedAverageRealizedBehaviorRegret
    (mdp : MDP State Action) (initialState : Measure State)
    [IsProbabilityMeasure initialState]
    [StandardBorelSpace State] [StandardBorelSpace Action]
    (rewardSource : mdp.MeanCompatibleRewardKernel)
    (varianceProxy : NNReal)
    (law : rewardSource.UniformSubgaussianRewardLaw varianceProxy)
    (initialTable : DeterministicMarkovPolicyTable mdp)
    (defaultState : State) (baseVisitFloor : Real)
    (hrewardBound : forall state action, |mdp.reward state action| <= 1)
    (tau : HeterogeneousStochasticEpisodeBatchTrajectory mdp
      (fun t =>
        AdaptiveStochasticEpisodeBatchSource.selfConsistentScheduledEpisodes
          mdp varianceProxy baseVisitFloor t) -> WithTop Nat)
    (htau : IsStoppingTime
      (selfConsistentScheduledNaturalCausalTrajectoryFiltration mdp initialState
        rewardSource initialTable defaultState varianceProxy baseVisitFloor) tau)
    (maxRounds : Nat)
    (htau_le : forall trajectory, tau trajectory <= (maxRounds : WithTop Nat)) :
    MemLp
      (selfConsistentScheduledNaturalCausalStoppedAverageRealizedBehaviorRegret
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor tau)
      2
      (selfConsistentScheduledCausalSource mdp initialState rewardSource
        initialTable defaultState varianceProxy baseVisitFloor).trajectoryMeasure := by
  exact memLp_stoppedValue htau
    (fun rounds =>
      memLp_two_selfConsistentScheduledNaturalCausalAverageRealizedBehaviorRegretProcess
        mdp initialState rewardSource varianceProxy law initialTable defaultState
          baseVisitFloor hrewardBound rounds)
    htau_le

/-- Every deterministic logarithmic average-rate coordinate is nonnegative. -/
theorem selfConsistentScheduledNaturalCausalRealizedAverageLogarithmicRate_nonneg
    (mdp : MDP State Action) (varianceProxy : NNReal)
    (baseVisitFloor : Real) (rounds : Nat) (returnDelta : Real) :
    0 <= selfConsistentScheduledNaturalCausalRealizedAverageLogarithmicRate
      mdp varianceProxy baseVisitFloor rounds returnDelta := by
  unfold selfConsistentScheduledNaturalCausalRealizedAverageLogarithmicRate
    selfConsistentScheduledNaturalCausalRealizedCumulativeLogarithmicRate
  exact div_nonneg
    (add_nonneg
      (selfConsistentScheduledNaturalCausalLogarithmicCumulativeIntegratedBehaviorExpectedRegretRate_nonneg
        mdp rounds)
      (Concentration.subGaussianSumConfidenceRadius_nonneg _ _))
    (Nat.cast_nonneg rounds)

/-- Deterministic finite sum which dominates the logarithmic rate selected by
any positive stopping time bounded by `maxRounds`. -/
noncomputable def selfConsistentScheduledNaturalCausalBoundedStoppingExplicitExpectedRateBudget
    (mdp : MDP State Action) (varianceProxy : NNReal)
    (baseVisitFloor : Real) (maxRounds : Nat) : Real :=
  Finset.sum (Finset.Icc 1 maxRounds) fun rounds =>
    selfConsistentScheduledNaturalCausalRealizedAverageLogarithmicRate
      mdp varianceProxy baseVisitFloor rounds
        (selfConsistentScheduledNaturalCausalBoundedStoppingEqualReturnShare
          maxRounds (1 / 8 : Real))

/-- The finite expected-rate budget is nonnegative. -/
theorem selfConsistentScheduledNaturalCausalBoundedStoppingExplicitExpectedRateBudget_nonneg
    (mdp : MDP State Action) (varianceProxy : NNReal)
    (baseVisitFloor : Real) (maxRounds : Nat) :
    0 <= selfConsistentScheduledNaturalCausalBoundedStoppingExplicitExpectedRateBudget
      mdp varianceProxy baseVisitFloor maxRounds := by
  unfold selfConsistentScheduledNaturalCausalBoundedStoppingExplicitExpectedRateBudget
  exact Finset.sum_nonneg fun rounds _ =>
    selfConsistentScheduledNaturalCausalRealizedAverageLogarithmicRate_nonneg
      mdp varianceProxy baseVisitFloor rounds _

/-- The stopped logarithmic rate is charged to the finite positive-prefix
rate budget without assuming endpoint monotonicity. -/
theorem selfConsistentScheduledNaturalCausalStoppedRealizedAverageLogarithmicRate_le_explicitExpectedRateBudget
    (mdp : MDP State Action) (initialState : Measure State)
    [IsProbabilityMeasure initialState]
    (rewardSource : mdp.MeanCompatibleRewardKernel)
    (initialTable : DeterministicMarkovPolicyTable mdp)
    (defaultState : State) (varianceProxy : NNReal)
    (baseVisitFloor : Real)
    (tau : HeterogeneousStochasticEpisodeBatchTrajectory mdp
      (fun t =>
        AdaptiveStochasticEpisodeBatchSource.selfConsistentScheduledEpisodes
          mdp varianceProxy baseVisitFloor t) -> WithTop Nat)
    (maxRounds : Nat)
    (htau_pos : forall trajectory, (1 : WithTop Nat) <= tau trajectory)
    (htau_le : forall trajectory, tau trajectory <= (maxRounds : WithTop Nat))
    (trajectory : HeterogeneousStochasticEpisodeBatchTrajectory mdp
      (fun t =>
        AdaptiveStochasticEpisodeBatchSource.selfConsistentScheduledEpisodes
          mdp varianceProxy baseVisitFloor t)) :
    selfConsistentScheduledNaturalCausalStoppedRealizedAverageLogarithmicRate
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor
          (fun _ =>
            selfConsistentScheduledNaturalCausalBoundedStoppingEqualReturnShare
              maxRounds (1 / 8 : Real))
          tau trajectory <=
      selfConsistentScheduledNaturalCausalBoundedStoppingExplicitExpectedRateBudget
        mdp varianceProxy baseVisitFloor maxRounds := by
  have hrange := one_le_untopA_and_untopA_le_of_withTop_bounds
    tau maxRounds htau_pos htau_le trajectory
  rw [selfConsistentScheduledNaturalCausalStoppedRealizedAverageLogarithmicRate_apply]
  unfold selfConsistentScheduledNaturalCausalBoundedStoppingExplicitExpectedRateBudget
  exact Finset.single_le_sum
    (fun rounds _ =>
      selfConsistentScheduledNaturalCausalRealizedAverageLogarithmicRate_nonneg
        mdp varianceProxy baseVisitFloor rounds _)
    (Finset.mem_Icc.mpr hrange)

/-- Exact stopped second moment on the generated causal trajectory measure. -/
noncomputable def selfConsistentScheduledNaturalCausalStoppedAverageRealizedBehaviorRegretSecondMoment
    (mdp : MDP State Action) (initialState : Measure State)
    [IsProbabilityMeasure initialState]
    (rewardSource : mdp.MeanCompatibleRewardKernel)
    (initialTable : DeterministicMarkovPolicyTable mdp)
    (defaultState : State) (varianceProxy : NNReal)
    (baseVisitFloor : Real)
    (tau : HeterogeneousStochasticEpisodeBatchTrajectory mdp
      (fun t =>
        AdaptiveStochasticEpisodeBatchSource.selfConsistentScheduledEpisodes
          mdp varianceProxy baseVisitFloor t) -> WithTop Nat) : Real :=
  integral
    (selfConsistentScheduledCausalSource mdp initialState rewardSource
      initialTable defaultState varianceProxy baseVisitFloor).trajectoryMeasure
    (fun trajectory =>
      selfConsistentScheduledNaturalCausalStoppedAverageRealizedBehaviorRegret
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor tau trajectory ^ 2)

/-- The exact stopped second moment is nonnegative. -/
theorem selfConsistentScheduledNaturalCausalStoppedAverageRealizedBehaviorRegretSecondMoment_nonneg
    (mdp : MDP State Action) (initialState : Measure State)
    [IsProbabilityMeasure initialState]
    (rewardSource : mdp.MeanCompatibleRewardKernel)
    (initialTable : DeterministicMarkovPolicyTable mdp)
    (defaultState : State) (varianceProxy : NNReal)
    (baseVisitFloor : Real)
    (tau : HeterogeneousStochasticEpisodeBatchTrajectory mdp
      (fun t =>
        AdaptiveStochasticEpisodeBatchSource.selfConsistentScheduledEpisodes
          mdp varianceProxy baseVisitFloor t) -> WithTop Nat) :
    0 <=
      selfConsistentScheduledNaturalCausalStoppedAverageRealizedBehaviorRegretSecondMoment
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor tau := by
  unfold selfConsistentScheduledNaturalCausalStoppedAverageRealizedBehaviorRegretSecondMoment
  exact integral_nonneg fun _ => sq_nonneg _

/-
Terminal expected-regret route. The bad-event contribution is charged through
the exact stopped second moment; no optional-stopping theorem is used.
-/
theorem
    selfConsistentScheduledCausalSource_boundedStoppingTimeExplicitExpectedAverageRealizedBehaviorRegret
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
    (tau : HeterogeneousStochasticEpisodeBatchTrajectory mdp
      (fun t =>
        AdaptiveStochasticEpisodeBatchSource.selfConsistentScheduledEpisodes
          mdp varianceProxy baseVisitFloor t) -> WithTop Nat)
    (htau : IsStoppingTime
      (selfConsistentScheduledNaturalCausalTrajectoryFiltration mdp initialState
        rewardSource initialTable defaultState varianceProxy baseVisitFloor) tau)
    (maxRounds : Nat) (hmaxRounds : 0 < maxRounds)
    (htau_pos : forall trajectory, (1 : WithTop Nat) <= tau trajectory)
    (htau_le : forall trajectory, tau trajectory <= (maxRounds : WithTop Nat)) :
    let source := selfConsistentScheduledCausalSource mdp initialState
      rewardSource initialTable defaultState varianceProxy baseVisitFloor
    let returnDeltaAt := fun _ : Nat =>
      selfConsistentScheduledNaturalCausalBoundedStoppingEqualReturnShare
        maxRounds (1 / 8 : Real)
    let event :=
      selfConsistentScheduledNaturalCausalBoundedStoppingSingleModelReturnBadEvent
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor maxRounds (1 / 8 : Real)
    let goodEvent := event.compl
    let stoppedRegret :=
      selfConsistentScheduledNaturalCausalStoppedAverageRealizedBehaviorRegret
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor tau
    let stoppedRate :=
      selfConsistentScheduledNaturalCausalStoppedRealizedAverageLogarithmicRate
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor returnDeltaAt tau
    let rateBudget :=
      selfConsistentScheduledNaturalCausalBoundedStoppingExplicitExpectedRateBudget
        mdp varianceProxy baseVisitFloor maxRounds
    let secondMoment :=
      selfConsistentScheduledNaturalCausalStoppedAverageRealizedBehaviorRegretSecondMoment
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor tau
    MemLp stoppedRegret 2 source.trajectoryMeasure /\
      MeasurableSet event /\
      source.trajectoryMeasure event <= ENNReal.ofReal (1 / 4 : Real) /\
      (3 / 4 : Real) <= source.trajectoryMeasure.real goodEvent /\
      0 <= rateBudget /\
      0 <= secondMoment /\
      integral source.trajectoryMeasure
          (event.indicator (fun trajectory => |stoppedRegret trajectory|)) <=
        (1 / 2 : Real) * Real.sqrt secondMoment /\
      integral source.trajectoryMeasure stoppedRegret <=
        rateBudget + (1 / 2 : Real) * Real.sqrt secondMoment /\
      forall trajectory, trajectory ∈ goodEvent ->
        stoppedRegret trajectory <= stoppedRate trajectory := by
  dsimp only
  let source := selfConsistentScheduledCausalSource mdp initialState
    rewardSource initialTable defaultState varianceProxy baseVisitFloor
  let returnDeltaAt := fun _ : Nat =>
    selfConsistentScheduledNaturalCausalBoundedStoppingEqualReturnShare
      maxRounds (1 / 8 : Real)
  let event :=
    selfConsistentScheduledNaturalCausalBoundedStoppingSingleModelReturnBadEvent
      mdp initialState rewardSource initialTable defaultState varianceProxy
        baseVisitFloor maxRounds (1 / 8 : Real)
  let goodEvent := event.compl
  let stoppedRegret :=
    selfConsistentScheduledNaturalCausalStoppedAverageRealizedBehaviorRegret
      mdp initialState rewardSource initialTable defaultState varianceProxy
        baseVisitFloor tau
  let stoppedRate :=
    selfConsistentScheduledNaturalCausalStoppedRealizedAverageLogarithmicRate
      mdp initialState rewardSource initialTable defaultState varianceProxy
        baseVisitFloor returnDeltaAt tau
  let rateBudget :=
    selfConsistentScheduledNaturalCausalBoundedStoppingExplicitExpectedRateBudget
      mdp varianceProxy baseVisitFloor maxRounds
  let secondMoment :=
    selfConsistentScheduledNaturalCausalStoppedAverageRealizedBehaviorRegretSecondMoment
      mdp initialState rewardSource initialTable defaultState varianceProxy
        baseVisitFloor tau
  have hparent :=
    selfConsistentScheduledCausalSource_boundedStoppingTimeExplicitThreeQuarterGoodEventAverageRealizedBehaviorRegret
      mdp initialState rewardSource varianceProxy hvarianceProxy law initialTable
        defaultState support baseVisitFloor hbaseFloor hrewardBound hhorizon
          hbaseVisitFloor tau htau maxRounds hmaxRounds htau_pos htau_le
  rcases hparent with
    ⟨_hstoppedMeasurable, heventMeasurable, _hgoodMeasurable, _hsubset,
      _hmodel, heventTail, _hstoppedTail, hgoodMass, hpathwise⟩
  have hmem : MemLp stoppedRegret 2 source.trajectoryMeasure := by
    simpa [source, stoppedRegret] using
      memLp_two_selfConsistentScheduledNaturalCausalStoppedAverageRealizedBehaviorRegret
        mdp initialState rewardSource varianceProxy law initialTable defaultState
          baseVisitFloor hrewardBound tau htau maxRounds htau_le
  have hrateBudget : 0 <= rateBudget := by
    simpa [rateBudget] using
      selfConsistentScheduledNaturalCausalBoundedStoppingExplicitExpectedRateBudget_nonneg
        mdp varianceProxy baseVisitFloor maxRounds
  have hsecondMoment : 0 <= secondMoment := by
    simpa [secondMoment] using
      selfConsistentScheduledNaturalCausalStoppedAverageRealizedBehaviorRegretSecondMoment_nonneg
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor tau
  have hbadReal : source.trajectoryMeasure.real event <= (1 / 4 : Real) := by
    apply ENNReal.toReal_le_of_le_ofReal (by norm_num)
    simpa [source, event] using heventTail
  have hsqrtBad : Real.sqrt (source.trajectoryMeasure.real event) <= (1 / 2 : Real) := by
    calc
      Real.sqrt (source.trajectoryMeasure.real event) <= Real.sqrt (1 / 4 : Real) :=
        Real.sqrt_le_sqrt hbadReal
      _ = (1 / 2 : Real) := by
        rw [show (1 / 4 : Real) = (1 / 2 : Real) ^ 2 by norm_num]
        exact Real.sqrt_sq (by norm_num)
  have hholder :
      integral source.trajectoryMeasure
          (event.indicator (fun trajectory => |stoppedRegret trajectory|)) <=
        Real.sqrt secondMoment *
          Real.sqrt (source.trajectoryMeasure.real event) := by
    have hraw :=
      BanditRLProof.integral_indicator_le_sqrt_secondMoment_mul_sqrt_real_measure
        source.trajectoryMeasure (fun trajectory => |stoppedRegret trajectory|)
          (fun trajectory => abs_nonneg (stoppedRegret trajectory)) hmem.abs event
          (by simpa [event] using heventMeasurable)
    simpa only [secondMoment,
      selfConsistentScheduledNaturalCausalStoppedAverageRealizedBehaviorRegretSecondMoment,
      stoppedRegret, sq_abs] using hraw
  have hoverflow :
      integral source.trajectoryMeasure
          (event.indicator (fun trajectory => |stoppedRegret trajectory|)) <=
        (1 / 2 : Real) * Real.sqrt secondMoment := by
    calc
      integral source.trajectoryMeasure
          (event.indicator (fun trajectory => |stoppedRegret trajectory|)) <=
          Real.sqrt secondMoment *
            Real.sqrt (source.trajectoryMeasure.real event) := hholder
      _ <= Real.sqrt secondMoment * (1 / 2 : Real) :=
        mul_le_mul_of_nonneg_left hsqrtBad (Real.sqrt_nonneg secondMoment)
      _ = (1 / 2 : Real) * Real.sqrt secondMoment := by ring
  have hgapIntegrable : Integrable stoppedRegret source.trajectoryMeasure :=
    hmem.integrable (by norm_num)
  have hoverflowIntegrable : Integrable
      (event.indicator (fun trajectory => |stoppedRegret trajectory|))
      source.trajectoryMeasure :=
    hgapIntegrable.abs.indicator (by simpa [event] using heventMeasurable)
  have hpoint : forall trajectory,
      stoppedRegret trajectory <=
        rateBudget + event.indicator
          (fun trajectory => |stoppedRegret trajectory|) trajectory := by
    intro trajectory
    by_cases htrajectory : trajectory ∈ event
    · calc
        stoppedRegret trajectory <= |stoppedRegret trajectory| := le_abs_self _
        _ <= rateBudget + |stoppedRegret trajectory| := by linarith
        _ = rateBudget + event.indicator
            (fun trajectory => |stoppedRegret trajectory|) trajectory := by
          rw [Set.indicator_of_mem htrajectory]
    · have hgood : trajectory ∈ goodEvent := by
        simpa [goodEvent] using htrajectory
      have hgoodBound : stoppedRegret trajectory <= stoppedRate trajectory := by
        simpa [stoppedRegret, stoppedRate, returnDeltaAt, goodEvent, event] using
          hpathwise trajectory hgood
      have hrateBound : stoppedRate trajectory <= rateBudget := by
        simpa [stoppedRate, rateBudget, returnDeltaAt] using
          selfConsistentScheduledNaturalCausalStoppedRealizedAverageLogarithmicRate_le_explicitExpectedRateBudget
            mdp initialState rewardSource initialTable defaultState varianceProxy
              baseVisitFloor tau maxRounds htau_pos htau_le trajectory
      calc
        stoppedRegret trajectory <= stoppedRate trajectory := hgoodBound
        _ <= rateBudget := hrateBound
        _ = rateBudget + event.indicator
            (fun trajectory => |stoppedRegret trajectory|) trajectory := by
          simp [Set.indicator_of_notMem htrajectory]
  have hexpectRaw :
      integral source.trajectoryMeasure stoppedRegret <=
        rateBudget + integral source.trajectoryMeasure
          (event.indicator (fun trajectory => |stoppedRegret trajectory|)) := by
    calc
      integral source.trajectoryMeasure stoppedRegret <=
          integral source.trajectoryMeasure (fun trajectory =>
            rateBudget + event.indicator
              (fun trajectory => |stoppedRegret trajectory|) trajectory) :=
        integral_mono hgapIntegrable
          ((integrable_const rateBudget).add hoverflowIntegrable) hpoint
      _ = rateBudget + integral source.trajectoryMeasure
          (event.indicator (fun trajectory => |stoppedRegret trajectory|)) := by
        rw [integral_add (integrable_const rateBudget) hoverflowIntegrable,
          integral_const]
        simp [MeasureTheory.probReal_univ]
  have hexpect :
      integral source.trajectoryMeasure stoppedRegret <=
        rateBudget + (1 / 2 : Real) * Real.sqrt secondMoment :=
    hexpectRaw.trans (add_le_add (le_refl rateBudget) hoverflow)
  refine ⟨hmem, ?_, ?_, ?_, hrateBudget, hsecondMoment, hoverflow,
    hexpect, ?_⟩
  · simpa [event] using heventMeasurable
  · simpa [source, event] using heventTail
  · simpa [source, goodEvent, event] using hgoodMass
  · intro trajectory htrajectory
    simpa [stoppedRegret, stoppedRate, returnDeltaAt, goodEvent, event] using
      hpathwise trajectory htrajectory

end AdaptiveStochasticSampledEmpiricalOptimisticSource
end BanditRLProof.FiniteHorizonRL
