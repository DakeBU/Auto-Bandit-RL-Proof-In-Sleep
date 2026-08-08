import BanditRLProof.RL.FiniteHorizonNaturalCausalStoppingTimeAverageRealizedBehaviorRegretAlmostSureConsistency
import BanditRLProof.RL.FiniteHorizonNaturalCausalRealizedBehaviorRegretHighProbabilityLogRate
import BanditRLProof.ProbabilityUnionBound

/-!
# Bounded stopping-time high-probability natural causal realized regret

The exact natural average realized behavior-regret process and its scheduled
fixed-prefix logarithmic rate are evaluated at one positive bounded Mathlib
stopping time. The stopped violation is measurable at the deterministic bound
and is covered pathwise by the finite union of fixed-prefix violations.

The probability proof is finite subadditivity. It does not use optional
stopping, an expectation identity, or independence between prefix events.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal ProbabilityTheory

namespace BanditRLProof.FiniteHorizonRL

universe u v

variable {State : Type u} {Action : Type v}
    [MeasurableSpace State] [MeasurableSpace Action]
    [Fintype State] [Fintype Action]
    [DecidableEq State] [DecidableEq Action]
    [MeasurableSingletonClass State] [MeasurableSingletonClass Action]
    [Nonempty State] [Nonempty Action]

namespace AdaptiveStochasticSampledEmpiricalOptimisticSource

/-- A positive `WithTop Nat` time bounded by a finite horizon has a positive
finite `untopA` value in the same deterministic range. -/
theorem one_le_untopA_and_untopA_le_of_withTop_bounds
    {Omega : Type*} (tau : Omega -> WithTop Nat) (maxRounds : Nat)
    (htau_pos : forall omega, (1 : WithTop Nat) <= tau omega)
    (htau_le : forall omega, tau omega <= (maxRounds : WithTop Nat))
    (omega : Omega) :
    1 <= (tau omega).untopA /\ (tau omega).untopA <= maxRounds := by
  have hne : tau omega ≠ (⊤ : WithTop Nat) :=
    ne_top_of_le_ne_top WithTop.coe_ne_top (htau_le omega)
  have hcoe : (((tau omega).untopA : Nat) : WithTop Nat) = tau omega := by
    rw [WithTop.untopA_eq_untop hne]
    exact WithTop.coe_untop _ hne
  have hlower :
      ((1 : Nat) : WithTop Nat) <=
        (((tau omega).untopA : Nat) : WithTop Nat) := by
    rw [hcoe]
    exact htau_pos omega
  have hupper :
      (((tau omega).untopA : Nat) : WithTop Nat) <=
        ((maxRounds : Nat) : WithTop Nat) := by
    rw [hcoe]
    exact htau_le omega
  exact And.intro (WithTop.coe_le_coe.mp hlower)
    (WithTop.coe_le_coe.mp hupper)

/-- The prefix-scheduled deterministic logarithmic rate is strongly adapted
to the natural trajectory filtration. -/
theorem selfConsistentScheduledNaturalCausalRealizedAverageLogarithmicRate_stronglyAdapted
    (mdp : MDP State Action) (initialState : Measure State)
    [IsProbabilityMeasure initialState]
    (rewardSource : mdp.MeanCompatibleRewardKernel)
    (initialTable : DeterministicMarkovPolicyTable mdp)
    (defaultState : State) (varianceProxy : NNReal)
    (baseVisitFloor : Real) (returnDeltaAt : Nat -> Real) :
    StronglyAdapted
      (selfConsistentScheduledNaturalCausalTrajectoryFiltration mdp initialState
        rewardSource initialTable defaultState varianceProxy baseVisitFloor)
      (fun rounds
          (_trajectory : HeterogeneousStochasticEpisodeBatchTrajectory mdp
            (fun t =>
              AdaptiveStochasticEpisodeBatchSource.selfConsistentScheduledEpisodes
                mdp varianceProxy baseVisitFloor t)) =>
        selfConsistentScheduledNaturalCausalRealizedAverageLogarithmicRate
          mdp varianceProxy baseVisitFloor rounds (returnDeltaAt rounds)) := by
  intro rounds
  exact stronglyMeasurable_const

/-- Exact natural average realized behavior regret evaluated at one stopping
time. -/
noncomputable def selfConsistentScheduledNaturalCausalStoppedAverageRealizedBehaviorRegret
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
    HeterogeneousStochasticEpisodeBatchTrajectory mdp
        (fun t =>
          AdaptiveStochasticEpisodeBatchSource.selfConsistentScheduledEpisodes
            mdp varianceProxy baseVisitFloor t) -> Real :=
  stoppedValue
    (selfConsistentScheduledNaturalCausalAverageRealizedBehaviorRegretProcess
      mdp initialState rewardSource initialTable defaultState varianceProxy
        baseVisitFloor)
    tau

@[simp]
theorem selfConsistentScheduledNaturalCausalStoppedAverageRealizedBehaviorRegret_apply
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
    (trajectory : HeterogeneousStochasticEpisodeBatchTrajectory mdp
      (fun t =>
        AdaptiveStochasticEpisodeBatchSource.selfConsistentScheduledEpisodes
          mdp varianceProxy baseVisitFloor t)) :
    selfConsistentScheduledNaturalCausalStoppedAverageRealizedBehaviorRegret
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor tau trajectory =
      selfConsistentScheduledNaturalCausalAverageRealizedBehaviorRegretProcess
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor (tau trajectory).untopA trajectory :=
  rfl

/-- The scheduled logarithmic average rate evaluated at the same stopping
time. -/
noncomputable def selfConsistentScheduledNaturalCausalStoppedRealizedAverageLogarithmicRate
    (mdp : MDP State Action) (initialState : Measure State)
    [IsProbabilityMeasure initialState]
    (rewardSource : mdp.MeanCompatibleRewardKernel)
    (initialTable : DeterministicMarkovPolicyTable mdp)
    (defaultState : State) (varianceProxy : NNReal)
    (baseVisitFloor : Real) (returnDeltaAt : Nat -> Real)
    (tau : HeterogeneousStochasticEpisodeBatchTrajectory mdp
      (fun t =>
        AdaptiveStochasticEpisodeBatchSource.selfConsistentScheduledEpisodes
          mdp varianceProxy baseVisitFloor t) -> WithTop Nat) :
    HeterogeneousStochasticEpisodeBatchTrajectory mdp
        (fun t =>
          AdaptiveStochasticEpisodeBatchSource.selfConsistentScheduledEpisodes
            mdp varianceProxy baseVisitFloor t) -> Real :=
  stoppedValue
    (fun rounds
        (_trajectory : HeterogeneousStochasticEpisodeBatchTrajectory mdp
          (fun t =>
            AdaptiveStochasticEpisodeBatchSource.selfConsistentScheduledEpisodes
              mdp varianceProxy baseVisitFloor t)) =>
      selfConsistentScheduledNaturalCausalRealizedAverageLogarithmicRate
        mdp varianceProxy baseVisitFloor rounds (returnDeltaAt rounds))
    tau

@[simp]
theorem selfConsistentScheduledNaturalCausalStoppedRealizedAverageLogarithmicRate_apply
    (mdp : MDP State Action) (initialState : Measure State)
    [IsProbabilityMeasure initialState]
    (rewardSource : mdp.MeanCompatibleRewardKernel)
    (initialTable : DeterministicMarkovPolicyTable mdp)
    (defaultState : State) (varianceProxy : NNReal)
    (baseVisitFloor : Real) (returnDeltaAt : Nat -> Real)
    (tau : HeterogeneousStochasticEpisodeBatchTrajectory mdp
      (fun t =>
        AdaptiveStochasticEpisodeBatchSource.selfConsistentScheduledEpisodes
          mdp varianceProxy baseVisitFloor t) -> WithTop Nat)
    (trajectory : HeterogeneousStochasticEpisodeBatchTrajectory mdp
      (fun t =>
        AdaptiveStochasticEpisodeBatchSource.selfConsistentScheduledEpisodes
          mdp varianceProxy baseVisitFloor t)) :
    selfConsistentScheduledNaturalCausalStoppedRealizedAverageLogarithmicRate
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor returnDeltaAt tau trajectory =
      selfConsistentScheduledNaturalCausalRealizedAverageLogarithmicRate
        mdp varianceProxy baseVisitFloor (tau trajectory).untopA
          (returnDeltaAt (tau trajectory).untopA) :=
  rfl

/-- One-sided violation of the stopped logarithmic average-rate certificate. -/
noncomputable def selfConsistentScheduledNaturalCausalBoundedStoppingTimeAverageRealizedBehaviorRegretViolationSet
    (mdp : MDP State Action) (initialState : Measure State)
    [IsProbabilityMeasure initialState]
    (rewardSource : mdp.MeanCompatibleRewardKernel)
    (initialTable : DeterministicMarkovPolicyTable mdp)
    (defaultState : State) (varianceProxy : NNReal)
    (baseVisitFloor : Real) (returnDeltaAt : Nat -> Real)
    (tau : HeterogeneousStochasticEpisodeBatchTrajectory mdp
      (fun t =>
        AdaptiveStochasticEpisodeBatchSource.selfConsistentScheduledEpisodes
          mdp varianceProxy baseVisitFloor t) -> WithTop Nat) :
    Set (HeterogeneousStochasticEpisodeBatchTrajectory mdp
      (fun t =>
        AdaptiveStochasticEpisodeBatchSource.selfConsistentScheduledEpisodes
          mdp varianceProxy baseVisitFloor t)) :=
  {trajectory |
    selfConsistentScheduledNaturalCausalStoppedRealizedAverageLogarithmicRate
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor returnDeltaAt tau trajectory <
      selfConsistentScheduledNaturalCausalStoppedAverageRealizedBehaviorRegret
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor tau trajectory}

/-- A bounded stopping-time violation is measurable at the deterministic
natural-filtration bound. -/
theorem measurableSet_selfConsistentScheduledNaturalCausalBoundedStoppingTimeAverageRealizedBehaviorRegretViolationSet
    (mdp : MDP State Action) (initialState : Measure State)
    [IsProbabilityMeasure initialState]
    (rewardSource : mdp.MeanCompatibleRewardKernel)
    (initialTable : DeterministicMarkovPolicyTable mdp)
    (defaultState : State) (varianceProxy : NNReal)
    (baseVisitFloor : Real) (returnDeltaAt : Nat -> Real)
    (tau : HeterogeneousStochasticEpisodeBatchTrajectory mdp
      (fun t =>
        AdaptiveStochasticEpisodeBatchSource.selfConsistentScheduledEpisodes
          mdp varianceProxy baseVisitFloor t) -> WithTop Nat)
    (htau : IsStoppingTime
      (selfConsistentScheduledNaturalCausalTrajectoryFiltration mdp initialState
        rewardSource initialTable defaultState varianceProxy baseVisitFloor) tau)
    (maxRounds : Nat)
    (htau_le : forall trajectory, tau trajectory <= (maxRounds : WithTop Nat)) :
    MeasurableSet[
      selfConsistentScheduledNaturalCausalTrajectoryFiltration mdp initialState
        rewardSource initialTable defaultState varianceProxy baseVisitFloor
          maxRounds]
      (selfConsistentScheduledNaturalCausalBoundedStoppingTimeAverageRealizedBehaviorRegretViolationSet
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor returnDeltaAt tau) := by
  have hrateProgressive :=
    (selfConsistentScheduledNaturalCausalRealizedAverageLogarithmicRate_stronglyAdapted
      mdp initialState rewardSource initialTable defaultState varianceProxy
        baseVisitFloor returnDeltaAt).progMeasurable_of_discrete
  have hregretProgressive :=
    (selfConsistentScheduledNaturalCausalAverageRealizedBehaviorRegretProcess_stronglyAdapted
      mdp initialState rewardSource initialTable defaultState varianceProxy
        baseVisitFloor).progMeasurable_of_discrete
  have hrateStopped :=
    stronglyMeasurable_stoppedValue_of_le hrateProgressive htau htau_le
  have hregretStopped :=
    stronglyMeasurable_stoppedValue_of_le hregretProgressive htau htau_le
  exact measurableSet_lt hrateStopped.measurable hregretStopped.measurable

/-- Finite union of all positive fixed-prefix average-regret violations through
the deterministic stopping-time bound. -/
noncomputable def selfConsistentScheduledNaturalCausalPositivePrefixAverageRealizedBehaviorRegretViolationWindow
    (mdp : MDP State Action) (initialState : Measure State)
    [IsProbabilityMeasure initialState]
    (rewardSource : mdp.MeanCompatibleRewardKernel)
    (initialTable : DeterministicMarkovPolicyTable mdp)
    (defaultState : State) (varianceProxy : NNReal)
    (baseVisitFloor : Real) (maxRounds : Nat)
    (returnDeltaAt : Nat -> Real) :
    Set (HeterogeneousStochasticEpisodeBatchTrajectory mdp
      (fun t =>
        AdaptiveStochasticEpisodeBatchSource.selfConsistentScheduledEpisodes
          mdp varianceProxy baseVisitFloor t)) :=
  ⋃ rounds ∈ Finset.Icc 1 maxRounds,
    selfConsistentScheduledNaturalCausalAverageRealizedBehaviorRegretLogarithmicViolationSet
      mdp initialState rewardSource initialTable defaultState varianceProxy
        baseVisitFloor rounds (returnDeltaAt rounds)

/-- The finite positive-prefix violation window is ambient measurable. -/
theorem measurableSet_selfConsistentScheduledNaturalCausalPositivePrefixAverageRealizedBehaviorRegretViolationWindow
    (mdp : MDP State Action) (initialState : Measure State)
    [IsProbabilityMeasure initialState]
    (rewardSource : mdp.MeanCompatibleRewardKernel)
    (initialTable : DeterministicMarkovPolicyTable mdp)
    (defaultState : State) (varianceProxy : NNReal)
    (baseVisitFloor : Real) (maxRounds : Nat)
    (returnDeltaAt : Nat -> Real) :
    MeasurableSet
      (selfConsistentScheduledNaturalCausalPositivePrefixAverageRealizedBehaviorRegretViolationWindow
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor maxRounds returnDeltaAt) := by
  exact (Finset.Icc 1 maxRounds).measurableSet_biUnion fun rounds _ =>
    measurableSet_selfConsistentScheduledNaturalCausalAverageRealizedBehaviorRegretLogarithmicViolationSet
      mdp initialState rewardSource initialTable defaultState varianceProxy
        baseVisitFloor rounds (returnDeltaAt rounds)

/-- Every positive bounded stopped violation occurs at one fixed prefix in the
finite window. -/
theorem selfConsistentScheduledNaturalCausalBoundedStoppingTimeAverageRealizedBehaviorRegretViolationSet_subset_positivePrefixWindow
    (mdp : MDP State Action) (initialState : Measure State)
    [IsProbabilityMeasure initialState]
    (rewardSource : mdp.MeanCompatibleRewardKernel)
    (initialTable : DeterministicMarkovPolicyTable mdp)
    (defaultState : State) (varianceProxy : NNReal)
    (baseVisitFloor : Real) (returnDeltaAt : Nat -> Real)
    (tau : HeterogeneousStochasticEpisodeBatchTrajectory mdp
      (fun t =>
        AdaptiveStochasticEpisodeBatchSource.selfConsistentScheduledEpisodes
          mdp varianceProxy baseVisitFloor t) -> WithTop Nat)
    (maxRounds : Nat)
    (htau_pos : forall trajectory, (1 : WithTop Nat) <= tau trajectory)
    (htau_le : forall trajectory, tau trajectory <= (maxRounds : WithTop Nat)) :
    selfConsistentScheduledNaturalCausalBoundedStoppingTimeAverageRealizedBehaviorRegretViolationSet
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor returnDeltaAt tau ⊆
      selfConsistentScheduledNaturalCausalPositivePrefixAverageRealizedBehaviorRegretViolationWindow
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor maxRounds returnDeltaAt := by
  intro trajectory htrajectory
  have hrange := one_le_untopA_and_untopA_le_of_withTop_bounds
    tau maxRounds htau_pos htau_le trajectory
  rw [selfConsistentScheduledNaturalCausalPositivePrefixAverageRealizedBehaviorRegretViolationWindow]
  refine Set.mem_iUnion.mpr (Exists.intro (tau trajectory).untopA ?_)
  refine Set.mem_iUnion.mpr (Exists.intro (Finset.mem_Icc.mpr hrange) ?_)
  simpa only [
    selfConsistentScheduledNaturalCausalBoundedStoppingTimeAverageRealizedBehaviorRegretViolationSet,
    selfConsistentScheduledNaturalCausalStoppedRealizedAverageLogarithmicRate_apply,
    selfConsistentScheduledNaturalCausalStoppedAverageRealizedBehaviorRegret_apply,
    selfConsistentScheduledNaturalCausalAverageRealizedBehaviorRegretLogarithmicViolationSet,
    Set.mem_setOf_eq] using htrajectory

/-- The positive-prefix violation window has the exact finite sum of the
per-prefix model and return failure budgets. -/
theorem selfConsistentScheduledCausalSource_trajectoryMeasure_positivePrefixAverageRealizedBehaviorRegretViolationWindow_le
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
    (maxRounds : Nat) (returnDeltaAt : Nat -> Real)
    (hreturnDeltaAt : forall rounds, rounds ∈ Finset.Icc 1 maxRounds ->
      0 < returnDeltaAt rounds /\ returnDeltaAt rounds <= 1) :
    let source := selfConsistentScheduledCausalSource mdp initialState
      rewardSource initialTable defaultState varianceProxy baseVisitFloor
    source.trajectoryMeasure
        (selfConsistentScheduledNaturalCausalPositivePrefixAverageRealizedBehaviorRegretViolationWindow
          mdp initialState rewardSource initialTable defaultState varianceProxy
            baseVisitFloor maxRounds returnDeltaAt) <=
      ∑ rounds ∈ Finset.Icc 1 maxRounds,
        (selfConsistentScheduledCausalModelFailureBudget mdp rounds +
          ENNReal.ofReal (returnDeltaAt rounds)) := by
  dsimp only
  let source := selfConsistentScheduledCausalSource mdp initialState
    rewardSource initialTable defaultState varianceProxy baseVisitFloor
  calc
    source.trajectoryMeasure
        (selfConsistentScheduledNaturalCausalPositivePrefixAverageRealizedBehaviorRegretViolationWindow
          mdp initialState rewardSource initialTable defaultState varianceProxy
            baseVisitFloor maxRounds returnDeltaAt) <=
      ∑ rounds ∈ Finset.Icc 1 maxRounds,
        source.trajectoryMeasure
          (selfConsistentScheduledNaturalCausalAverageRealizedBehaviorRegretLogarithmicViolationSet
            mdp initialState rewardSource initialTable defaultState varianceProxy
              baseVisitFloor rounds (returnDeltaAt rounds)) := by
        simpa [selfConsistentScheduledNaturalCausalPositivePrefixAverageRealizedBehaviorRegretViolationWindow]
          using ProbabilityUnionBound.measure_biUnion_finset_le
            source.trajectoryMeasure (Finset.Icc 1 maxRounds)
              (fun rounds =>
                selfConsistentScheduledNaturalCausalAverageRealizedBehaviorRegretLogarithmicViolationSet
                  mdp initialState rewardSource initialTable defaultState varianceProxy
                    baseVisitFloor rounds (returnDeltaAt rounds))
    _ <= ∑ rounds ∈ Finset.Icc 1 maxRounds,
        (selfConsistentScheduledCausalModelFailureBudget mdp rounds +
          ENNReal.ofReal (returnDeltaAt rounds)) := by
      have hterm : forall rounds, rounds ∈ Finset.Icc 1 maxRounds ->
          source.trajectoryMeasure
              (selfConsistentScheduledNaturalCausalAverageRealizedBehaviorRegretLogarithmicViolationSet
                mdp initialState rewardSource initialTable defaultState varianceProxy
                  baseVisitFloor rounds (returnDeltaAt rounds)) <=
            selfConsistentScheduledCausalModelFailureBudget mdp rounds +
              ENNReal.ofReal (returnDeltaAt rounds) := by
        intro rounds hrounds
        have hrounds_pos : 0 < rounds := (Finset.mem_Icc.mp hrounds).1
        have hsubset :=
          selfConsistentScheduledNaturalCausalAverageRealizedBehaviorRegretLogarithmicViolationSet_subset_modelReturnBadEvent
            mdp initialState rewardSource varianceProxy hvarianceProxy law initialTable
              defaultState support baseVisitFloor hbaseFloor hrewardBound hhorizon
                hbaseVisitFloor rounds hrounds_pos (returnDeltaAt rounds)
        have htail :=
          selfConsistentScheduledCausalSource_trajectoryMeasure_naturalModelReturnBadEvent_le
            mdp initialState rewardSource varianceProxy hvarianceProxy law initialTable
              defaultState support baseVisitFloor hbaseFloor hrewardBound hhorizon
                hbaseVisitFloor rounds hrounds_pos (returnDeltaAt rounds)
                  (hreturnDeltaAt rounds hrounds).1
                  (hreturnDeltaAt rounds hrounds).2
        exact (measure_mono hsubset).trans htail.2
      exact Finset.sum_le_sum hterm

/-- The stopped violation inherits the same explicit finite-window budget. -/
theorem selfConsistentScheduledCausalSource_trajectoryMeasure_boundedStoppingTimeAverageRealizedBehaviorRegretViolationSet_le
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
    (maxRounds : Nat)
    (htau_pos : forall trajectory, (1 : WithTop Nat) <= tau trajectory)
    (htau_le : forall trajectory, tau trajectory <= (maxRounds : WithTop Nat))
    (returnDeltaAt : Nat -> Real)
    (hreturnDeltaAt : forall rounds, rounds ∈ Finset.Icc 1 maxRounds ->
      0 < returnDeltaAt rounds /\ returnDeltaAt rounds <= 1) :
    let source := selfConsistentScheduledCausalSource mdp initialState
      rewardSource initialTable defaultState varianceProxy baseVisitFloor
    source.trajectoryMeasure
        (selfConsistentScheduledNaturalCausalBoundedStoppingTimeAverageRealizedBehaviorRegretViolationSet
          mdp initialState rewardSource initialTable defaultState varianceProxy
            baseVisitFloor returnDeltaAt tau) <=
      ∑ rounds ∈ Finset.Icc 1 maxRounds,
        (selfConsistentScheduledCausalModelFailureBudget mdp rounds +
          ENNReal.ofReal (returnDeltaAt rounds)) := by
  dsimp only
  have hsubset :
      selfConsistentScheduledNaturalCausalBoundedStoppingTimeAverageRealizedBehaviorRegretViolationSet
          mdp initialState rewardSource initialTable defaultState varianceProxy
            baseVisitFloor returnDeltaAt tau ⊆
        selfConsistentScheduledNaturalCausalPositivePrefixAverageRealizedBehaviorRegretViolationWindow
          mdp initialState rewardSource initialTable defaultState varianceProxy
            baseVisitFloor maxRounds returnDeltaAt :=
      selfConsistentScheduledNaturalCausalBoundedStoppingTimeAverageRealizedBehaviorRegretViolationSet_subset_positivePrefixWindow
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor returnDeltaAt tau maxRounds htau_pos htau_le
  have hwindow :=
      selfConsistentScheduledCausalSource_trajectoryMeasure_positivePrefixAverageRealizedBehaviorRegretViolationWindow_le
        mdp initialState rewardSource varianceProxy hvarianceProxy law initialTable
          defaultState support baseVisitFloor hbaseFloor hrewardBound hhorizon
            hbaseVisitFloor maxRounds returnDeltaAt hreturnDeltaAt
  exact (measure_mono hsubset).trans hwindow

/-
The terminal packages filtered stopped-event measurability, ambient window
measurability, pathwise containment, exact finite-sum probability bounds, and
the stopped logarithmic certificate outside the finite violation window.
-/
theorem selfConsistentScheduledCausalSource_boundedStoppingTimeHighProbabilityAverageRealizedBehaviorRegret
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
    (maxRounds : Nat)
    (htau_pos : forall trajectory, (1 : WithTop Nat) <= tau trajectory)
    (htau_le : forall trajectory, tau trajectory <= (maxRounds : WithTop Nat))
    (returnDeltaAt : Nat -> Real)
    (hreturnDeltaAt : forall rounds, rounds ∈ Finset.Icc 1 maxRounds ->
      0 < returnDeltaAt rounds /\ returnDeltaAt rounds <= 1) :
    let source := selfConsistentScheduledCausalSource mdp initialState
      rewardSource initialTable defaultState varianceProxy baseVisitFloor
    let stoppedViolation :=
      selfConsistentScheduledNaturalCausalBoundedStoppingTimeAverageRealizedBehaviorRegretViolationSet
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor returnDeltaAt tau
    let violationWindow :=
      selfConsistentScheduledNaturalCausalPositivePrefixAverageRealizedBehaviorRegretViolationWindow
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor maxRounds returnDeltaAt
    let failureBudget :=
      ∑ rounds ∈ Finset.Icc 1 maxRounds,
        (selfConsistentScheduledCausalModelFailureBudget mdp rounds +
          ENNReal.ofReal (returnDeltaAt rounds))
    MeasurableSet[
        selfConsistentScheduledNaturalCausalTrajectoryFiltration mdp initialState
          rewardSource initialTable defaultState varianceProxy baseVisitFloor
            maxRounds] stoppedViolation /\
      MeasurableSet violationWindow /\
      stoppedViolation ⊆ violationWindow /\
      source.trajectoryMeasure violationWindow <= failureBudget /\
      source.trajectoryMeasure stoppedViolation <= failureBudget /\
      (failureBudget < 1 -> source.trajectoryMeasure stoppedViolation < 1) /\
      forall trajectory, trajectory ∉ violationWindow ->
        selfConsistentScheduledNaturalCausalStoppedAverageRealizedBehaviorRegret
            mdp initialState rewardSource initialTable defaultState varianceProxy
              baseVisitFloor tau trajectory <=
          selfConsistentScheduledNaturalCausalStoppedRealizedAverageLogarithmicRate
            mdp initialState rewardSource initialTable defaultState varianceProxy
              baseVisitFloor returnDeltaAt tau trajectory := by
  dsimp only
  let source := selfConsistentScheduledCausalSource mdp initialState
    rewardSource initialTable defaultState varianceProxy baseVisitFloor
  let stoppedViolation :=
    selfConsistentScheduledNaturalCausalBoundedStoppingTimeAverageRealizedBehaviorRegretViolationSet
      mdp initialState rewardSource initialTable defaultState varianceProxy
        baseVisitFloor returnDeltaAt tau
  let violationWindow :=
    selfConsistentScheduledNaturalCausalPositivePrefixAverageRealizedBehaviorRegretViolationWindow
      mdp initialState rewardSource initialTable defaultState varianceProxy
        baseVisitFloor maxRounds returnDeltaAt
  let failureBudget :=
    ∑ rounds ∈ Finset.Icc 1 maxRounds,
      (selfConsistentScheduledCausalModelFailureBudget mdp rounds +
        ENNReal.ofReal (returnDeltaAt rounds))
  have hstoppedMeasurable :
      MeasurableSet[
        selfConsistentScheduledNaturalCausalTrajectoryFiltration mdp initialState
          rewardSource initialTable defaultState varianceProxy baseVisitFloor
            maxRounds] stoppedViolation := by
    simpa [stoppedViolation] using
      measurableSet_selfConsistentScheduledNaturalCausalBoundedStoppingTimeAverageRealizedBehaviorRegretViolationSet
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor returnDeltaAt tau htau maxRounds htau_le
  have hwindowMeasurable : MeasurableSet violationWindow := by
    simpa [violationWindow] using
      measurableSet_selfConsistentScheduledNaturalCausalPositivePrefixAverageRealizedBehaviorRegretViolationWindow
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor maxRounds returnDeltaAt
  have hsubset : stoppedViolation ⊆ violationWindow := by
    simpa [stoppedViolation, violationWindow] using
      selfConsistentScheduledNaturalCausalBoundedStoppingTimeAverageRealizedBehaviorRegretViolationSet_subset_positivePrefixWindow
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor returnDeltaAt tau maxRounds htau_pos htau_le
  have hwindowTail : source.trajectoryMeasure violationWindow <= failureBudget := by
    simpa [source, violationWindow, failureBudget] using
      selfConsistentScheduledCausalSource_trajectoryMeasure_positivePrefixAverageRealizedBehaviorRegretViolationWindow_le
        mdp initialState rewardSource varianceProxy hvarianceProxy law initialTable
          defaultState support baseVisitFloor hbaseFloor hrewardBound hhorizon
            hbaseVisitFloor maxRounds returnDeltaAt hreturnDeltaAt
  have hstoppedTail : source.trajectoryMeasure stoppedViolation <= failureBudget :=
    (measure_mono hsubset).trans hwindowTail
  refine And.intro hstoppedMeasurable ?_
  refine And.intro hwindowMeasurable ?_
  refine And.intro hsubset ?_
  refine And.intro hwindowTail ?_
  refine And.intro hstoppedTail ?_
  refine And.intro (fun hbudget => hstoppedTail.trans_lt hbudget) ?_
  intro trajectory htrajectory
  have hnotStopped : trajectory ∉ stoppedViolation := fun h =>
    htrajectory (hsubset h)
  apply le_of_not_gt
  intro hlt
  exact hnotStopped (by simpa [stoppedViolation] using hlt)

end AdaptiveStochasticSampledEmpiricalOptimisticSource

end BanditRLProof.FiniteHorizonRL
