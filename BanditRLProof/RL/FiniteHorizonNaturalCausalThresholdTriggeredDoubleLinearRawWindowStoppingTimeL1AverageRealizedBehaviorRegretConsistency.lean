import BanditRLProof.RL.FiniteHorizonNaturalCausalRateControlledRawWindowStoppingTimeL1AverageRealizedBehaviorRegretConsistency

/-!
# Threshold-triggered double-linear raw-window stopping-time L1 consistency

At schedule index `n`, this module observes the compiled natural average
realized behavior-regret process at the fourth-power prefix `(n+1)^4`. It
stops at that prefix when the observation is at most a deterministic threshold
and otherwise waits exactly `2*n+1` additional raw prefixes.

The early-stop event is measurable in the exact natural filtration at the base
prefix, so Mathlib's piecewise-constant constructor yields a genuine stopping
time. The rate-controlled raw-window parent then gives the full L1,
in-measure, and almost-everywhere consistency package. No optional-stopping
identity or independence assumption is used.
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

/-- Event on which the observed base-prefix average regret triggers early stopping. -/
noncomputable def
    selfConsistentScheduledNaturalCausalThresholdTriggeredDoubleLinearRawWindowEarlyStopSet
    (mdp : MDP State Action) (initialState : Measure State)
    [IsProbabilityMeasure initialState]
    (rewardSource : mdp.MeanCompatibleRewardKernel)
    (initialTable : DeterministicMarkovPolicyTable mdp)
    (defaultState : State) (varianceProxy : NNReal)
    (baseVisitFloor : Real) (threshold : Nat -> Real)
    (scheduleIndex : Nat) :
    Set (HeterogeneousStochasticEpisodeBatchTrajectory mdp
      (fun t =>
        AdaptiveStochasticEpisodeBatchSource.selfConsistentScheduledEpisodes
          mdp varianceProxy baseVisitFloor t)) :=
  {trajectory |
    selfConsistentScheduledNaturalCausalAverageRealizedBehaviorRegretProcess
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor (explicitHighProbabilityRounds scheduleIndex)
          trajectory <=
      threshold scheduleIndex}

/-- Stop at the observed fourth-power prefix, or wait exactly `2*n+1` more prefixes. -/
noncomputable def
    selfConsistentScheduledNaturalCausalThresholdTriggeredDoubleLinearRawWindowStoppingPrefix
    (mdp : MDP State Action) (initialState : Measure State)
    [IsProbabilityMeasure initialState]
    (rewardSource : mdp.MeanCompatibleRewardKernel)
    (initialTable : DeterministicMarkovPolicyTable mdp)
    (defaultState : State) (varianceProxy : NNReal)
    (baseVisitFloor : Real) (threshold : Nat -> Real)
    (scheduleIndex : Nat) :
    HeterogeneousStochasticEpisodeBatchTrajectory mdp
        (fun t =>
          AdaptiveStochasticEpisodeBatchSource.selfConsistentScheduledEpisodes
            mdp varianceProxy baseVisitFloor t) -> WithTop Nat := by
  classical
  exact
    (selfConsistentScheduledNaturalCausalThresholdTriggeredDoubleLinearRawWindowEarlyStopSet
      mdp initialState rewardSource initialTable defaultState varianceProxy
        baseVisitFloor threshold scheduleIndex).piecewise
      (fun _ => (explicitHighProbabilityRounds scheduleIndex : WithTop Nat))
      (fun _ =>
        (explicitHighProbabilityRounds scheduleIndex +
          (2 * scheduleIndex + 1) : WithTop Nat))

/-- The threshold-success branch stops at the observed base prefix. -/
theorem
    selfConsistentScheduledNaturalCausalThresholdTriggeredDoubleLinearRawWindowStoppingPrefix_eq_base_of_le
    (mdp : MDP State Action) (initialState : Measure State)
    [IsProbabilityMeasure initialState]
    (rewardSource : mdp.MeanCompatibleRewardKernel)
    (initialTable : DeterministicMarkovPolicyTable mdp)
    (defaultState : State) (varianceProxy : NNReal)
    (baseVisitFloor : Real) (threshold : Nat -> Real)
    (scheduleIndex : Nat) (trajectory)
    (hthreshold :
      selfConsistentScheduledNaturalCausalAverageRealizedBehaviorRegretProcess
          mdp initialState rewardSource initialTable defaultState varianceProxy
            baseVisitFloor (explicitHighProbabilityRounds scheduleIndex)
            trajectory <=
        threshold scheduleIndex) :
    selfConsistentScheduledNaturalCausalThresholdTriggeredDoubleLinearRawWindowStoppingPrefix
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor threshold scheduleIndex trajectory =
      (explicitHighProbabilityRounds scheduleIndex : WithTop Nat) := by
  simp [
    selfConsistentScheduledNaturalCausalThresholdTriggeredDoubleLinearRawWindowStoppingPrefix,
    selfConsistentScheduledNaturalCausalThresholdTriggeredDoubleLinearRawWindowEarlyStopSet,
    hthreshold]

/-- The threshold-failure branch waits to the right endpoint. -/
theorem
    selfConsistentScheduledNaturalCausalThresholdTriggeredDoubleLinearRawWindowStoppingPrefix_eq_right_of_lt
    (mdp : MDP State Action) (initialState : Measure State)
    [IsProbabilityMeasure initialState]
    (rewardSource : mdp.MeanCompatibleRewardKernel)
    (initialTable : DeterministicMarkovPolicyTable mdp)
    (defaultState : State) (varianceProxy : NNReal)
    (baseVisitFloor : Real) (threshold : Nat -> Real)
    (scheduleIndex : Nat) (trajectory)
    (hthreshold : threshold scheduleIndex <
      selfConsistentScheduledNaturalCausalAverageRealizedBehaviorRegretProcess
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor (explicitHighProbabilityRounds scheduleIndex)
          trajectory) :
    selfConsistentScheduledNaturalCausalThresholdTriggeredDoubleLinearRawWindowStoppingPrefix
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor threshold scheduleIndex trajectory =
      (explicitHighProbabilityRounds scheduleIndex +
        (2 * scheduleIndex + 1) : WithTop Nat) := by
  have hnle : ¬
      selfConsistentScheduledNaturalCausalAverageRealizedBehaviorRegretProcess
          mdp initialState rewardSource initialTable defaultState varianceProxy
            baseVisitFloor (explicitHighProbabilityRounds scheduleIndex)
            trajectory <=
        threshold scheduleIndex := not_le.mpr hthreshold
  simp [
    selfConsistentScheduledNaturalCausalThresholdTriggeredDoubleLinearRawWindowStoppingPrefix,
    selfConsistentScheduledNaturalCausalThresholdTriggeredDoubleLinearRawWindowEarlyStopSet,
    hnle]

/-- The early-stop event is known at the fourth-power base prefix. -/
theorem
    measurableSet_selfConsistentScheduledNaturalCausalThresholdTriggeredDoubleLinearRawWindowEarlyStopSet
    (mdp : MDP State Action) (initialState : Measure State)
    [IsProbabilityMeasure initialState]
    (rewardSource : mdp.MeanCompatibleRewardKernel)
    (initialTable : DeterministicMarkovPolicyTable mdp)
    (defaultState : State) (varianceProxy : NNReal)
    (baseVisitFloor : Real) (threshold : Nat -> Real)
    (scheduleIndex : Nat) :
    MeasurableSet[
      selfConsistentScheduledNaturalCausalTrajectoryFiltration mdp initialState
        rewardSource initialTable defaultState varianceProxy baseVisitFloor
          (explicitHighProbabilityRounds scheduleIndex)]
      (selfConsistentScheduledNaturalCausalThresholdTriggeredDoubleLinearRawWindowEarlyStopSet
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor threshold scheduleIndex) := by
  let filtration := selfConsistentScheduledNaturalCausalTrajectoryFiltration
    mdp initialState rewardSource initialTable defaultState varianceProxy
      baseVisitFloor
  let process :=
    selfConsistentScheduledNaturalCausalAverageRealizedBehaviorRegretProcess mdp
      initialState rewardSource initialTable defaultState varianceProxy
        baseVisitFloor
  have hprocess : StronglyAdapted filtration process :=
    selfConsistentScheduledNaturalCausalAverageRealizedBehaviorRegretProcess_stronglyAdapted
      mdp initialState rewardSource initialTable defaultState varianceProxy
        baseVisitFloor
  have hmeasurable : Measurable[filtration
      (explicitHighProbabilityRounds scheduleIndex)]
      (process (explicitHighProbabilityRounds scheduleIndex)) :=
    (hprocess (explicitHighProbabilityRounds scheduleIndex)).measurable
  simpa [
    selfConsistentScheduledNaturalCausalThresholdTriggeredDoubleLinearRawWindowEarlyStopSet,
    filtration, process] using
      measurableSet_le hmeasurable measurable_const

/-- The threshold-triggered two-endpoint rule is an exact natural-filtration stopping time. -/
theorem
    selfConsistentScheduledNaturalCausalThresholdTriggeredDoubleLinearRawWindowStoppingPrefix_isStoppingTime
    (mdp : MDP State Action) (initialState : Measure State)
    [IsProbabilityMeasure initialState]
    (rewardSource : mdp.MeanCompatibleRewardKernel)
    (initialTable : DeterministicMarkovPolicyTable mdp)
    (defaultState : State) (varianceProxy : NNReal)
    (baseVisitFloor : Real) (threshold : Nat -> Real)
    (scheduleIndex : Nat) :
    IsStoppingTime
      (selfConsistentScheduledNaturalCausalTrajectoryFiltration mdp initialState
        rewardSource initialTable defaultState varianceProxy baseVisitFloor)
      (selfConsistentScheduledNaturalCausalThresholdTriggeredDoubleLinearRawWindowStoppingPrefix
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor threshold scheduleIndex) := by
  classical
  let filtration := selfConsistentScheduledNaturalCausalTrajectoryFiltration
    mdp initialState rewardSource initialTable defaultState varianceProxy
      baseVisitFloor
  have hset :
      MeasurableSet[filtration (explicitHighProbabilityRounds scheduleIndex)]
        (selfConsistentScheduledNaturalCausalThresholdTriggeredDoubleLinearRawWindowEarlyStopSet
          mdp initialState rewardSource initialTable defaultState varianceProxy
            baseVisitFloor threshold scheduleIndex) :=
    measurableSet_selfConsistentScheduledNaturalCausalThresholdTriggeredDoubleLinearRawWindowEarlyStopSet
      mdp initialState rewardSource initialTable defaultState varianceProxy
        baseVisitFloor threshold scheduleIndex
  have hle : explicitHighProbabilityRounds scheduleIndex <=
      explicitHighProbabilityRounds scheduleIndex +
        (2 * scheduleIndex + 1) :=
    Nat.le_add_right _ _
  simpa [
    selfConsistentScheduledNaturalCausalThresholdTriggeredDoubleLinearRawWindowStoppingPrefix,
    filtration] using
      isStoppingTime_piecewise_const (𝒢 := filtration) hle hset

/-- The threshold rule never stops before its observed base prefix. -/
theorem
    selfConsistentScheduledNaturalCausalThresholdTriggeredDoubleLinearRawWindowStoppingPrefix_lower
    (mdp : MDP State Action) (initialState : Measure State)
    [IsProbabilityMeasure initialState]
    (rewardSource : mdp.MeanCompatibleRewardKernel)
    (initialTable : DeterministicMarkovPolicyTable mdp)
    (defaultState : State) (varianceProxy : NNReal)
    (baseVisitFloor : Real) (threshold : Nat -> Real)
    (scheduleIndex : Nat) (trajectory) :
    (explicitHighProbabilityRounds scheduleIndex : WithTop Nat) <=
      selfConsistentScheduledNaturalCausalThresholdTriggeredDoubleLinearRawWindowStoppingPrefix
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor threshold scheduleIndex trajectory := by
  classical
  unfold selfConsistentScheduledNaturalCausalThresholdTriggeredDoubleLinearRawWindowStoppingPrefix
  by_cases htrajectory : trajectory ∈
      selfConsistentScheduledNaturalCausalThresholdTriggeredDoubleLinearRawWindowEarlyStopSet
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor threshold scheduleIndex
  · simp [htrajectory]
  · simp [htrajectory]

/-- The threshold rule never exceeds the double-linear right endpoint. -/
theorem
    selfConsistentScheduledNaturalCausalThresholdTriggeredDoubleLinearRawWindowStoppingPrefix_upper
    (mdp : MDP State Action) (initialState : Measure State)
    [IsProbabilityMeasure initialState]
    (rewardSource : mdp.MeanCompatibleRewardKernel)
    (initialTable : DeterministicMarkovPolicyTable mdp)
    (defaultState : State) (varianceProxy : NNReal)
    (baseVisitFloor : Real) (threshold : Nat -> Real)
    (scheduleIndex : Nat) (trajectory) :
    selfConsistentScheduledNaturalCausalThresholdTriggeredDoubleLinearRawWindowStoppingPrefix
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor threshold scheduleIndex trajectory <=
      (explicitHighProbabilityRounds scheduleIndex +
        (2 * scheduleIndex + 1) : WithTop Nat) := by
  classical
  unfold selfConsistentScheduledNaturalCausalThresholdTriggeredDoubleLinearRawWindowStoppingPrefix
  by_cases htrajectory : trajectory ∈
      selfConsistentScheduledNaturalCausalThresholdTriggeredDoubleLinearRawWindowEarlyStopSet
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor threshold scheduleIndex
  · simp [htrajectory]
  · simp [htrajectory]

/-
Terminal L1 theorem for the threshold-triggered choice between the fourth-power
base prefix and its `2*n+1`-wider right endpoint.
-/
theorem
    selfConsistentScheduledCausalSource_thresholdTriggeredDoubleLinearRawWindowStoppingTimeNaturalAverageRealizedBehaviorRegret_L1_consistency
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
    (threshold : Nat -> Real) :
    let stoppingPrefix :=
      selfConsistentScheduledNaturalCausalThresholdTriggeredDoubleLinearRawWindowStoppingPrefix
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor threshold
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
  let stoppingPrefix :=
    selfConsistentScheduledNaturalCausalThresholdTriggeredDoubleLinearRawWindowStoppingPrefix
      mdp initialState rewardSource initialTable defaultState varianceProxy
        baseVisitFloor threshold
  have hindexBase : forall scheduleIndex,
      scheduleIndex <= explicitHighProbabilityRounds scheduleIndex := by
    intro scheduleIndex
    unfold explicitHighProbabilityRounds explicitHighProbabilityScale
    calc
      scheduleIndex <= scheduleIndex + 1 := Nat.le_succ _
      _ <= (scheduleIndex + 1) ^ 4 := Nat.le_pow (by norm_num)
  have hparent :=
    selfConsistentScheduledCausalSource_rateControlledRawWindowStoppingTimeNaturalAverageRealizedBehaviorRegret_L1_consistency
      mdp initialState rewardSource varianceProxy hvarianceProxy law initialTable
        defaultState support baseVisitFloor hbaseFloor hrewardBound hhorizon
          hbaseVisitFloor explicitHighProbabilityRounds
            (fun scheduleIndex => 2 * scheduleIndex + 1)
              explicitHighProbabilityRounds_pos hindexBase
                explicitHighProbabilityDoubleLinearRawWindowCandidateRate_tendsto_zero
                  stoppingPrefix
                    (fun scheduleIndex =>
                      selfConsistentScheduledNaturalCausalThresholdTriggeredDoubleLinearRawWindowStoppingPrefix_isStoppingTime
                        mdp initialState rewardSource initialTable defaultState
                          varianceProxy baseVisitFloor threshold scheduleIndex)
                    (fun scheduleIndex trajectory =>
                      selfConsistentScheduledNaturalCausalThresholdTriggeredDoubleLinearRawWindowStoppingPrefix_lower
                        mdp initialState rewardSource initialTable defaultState
                          varianceProxy baseVisitFloor threshold scheduleIndex
                            trajectory)
                    (fun scheduleIndex trajectory =>
                      selfConsistentScheduledNaturalCausalThresholdTriggeredDoubleLinearRawWindowStoppingPrefix_upper
                        mdp initialState rewardSource initialTable defaultState
                          varianceProxy baseVisitFloor threshold scheduleIndex
                            trajectory)
  simpa only [stoppingPrefix] using hparent

end AdaptiveStochasticSampledEmpiricalOptimisticSource

end BanditRLProof.FiniteHorizonRL
