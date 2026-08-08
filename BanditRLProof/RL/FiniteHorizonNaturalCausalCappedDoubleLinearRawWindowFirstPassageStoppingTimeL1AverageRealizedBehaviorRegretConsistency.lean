import BanditRLProof.RL.FiniteHorizonNaturalCausalRateControlledRawWindowStoppingTimeL1AverageRealizedBehaviorRegretConsistency
import Mathlib.Probability.Process.HittingTime

/-!
# Capped double-linear raw-window first-passage stopping-time L1 consistency

At schedule index `n`, this module scans the exact natural average realized
behavior-regret process from the fourth-power prefix `(n+1)^4` through the
right endpoint `(n+1)^4+(2*n+1)`. It stops at the first prefix where the
process is at most a deterministic threshold, or at the right endpoint if no
earlier prefix crosses the threshold.

Mathlib's `hittingBtwn` supplies the finite first-passage construction and its
stopping-time theorem. The compiled rate-controlled raw-window parent then
gives the full L1, in-measure, and almost-everywhere consistency package. No
optional-stopping identity or independence assumption is used.
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

/--
The first natural prefix in the double-linear raw window whose observed
average regret is at most the deterministic threshold, with right-end fallback.
-/
noncomputable def
    selfConsistentScheduledNaturalCausalCappedDoubleLinearRawWindowFirstPassagePrefixNat
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
            mdp varianceProxy baseVisitFloor t) -> Nat :=
  MeasureTheory.hittingBtwn
    (selfConsistentScheduledNaturalCausalAverageRealizedBehaviorRegretProcess
      mdp initialState rewardSource initialTable defaultState varianceProxy
        baseVisitFloor)
    (Set.Iic (threshold scheduleIndex))
    (explicitHighProbabilityRounds scheduleIndex)
    (explicitHighProbabilityRounds scheduleIndex + (2 * scheduleIndex + 1))

/-- The `WithTop Nat` surface consumed by Mathlib stopped-process APIs. -/
noncomputable def
    selfConsistentScheduledNaturalCausalCappedDoubleLinearRawWindowFirstPassageStoppingPrefix
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
            mdp varianceProxy baseVisitFloor t) -> WithTop Nat :=
  fun trajectory =>
    (selfConsistentScheduledNaturalCausalCappedDoubleLinearRawWindowFirstPassagePrefixNat
      mdp initialState rewardSource initialTable defaultState varianceProxy
        baseVisitFloor threshold scheduleIndex trajectory : WithTop Nat)

/-- A specified first threshold hit is exactly the Mathlib finite hitting time. -/
theorem
    selfConsistentScheduledNaturalCausalCappedDoubleLinearRawWindowFirstPassagePrefixNat_eq_of_first_hit
    (mdp : MDP State Action) (initialState : Measure State)
    [IsProbabilityMeasure initialState]
    (rewardSource : mdp.MeanCompatibleRewardKernel)
    (initialTable : DeterministicMarkovPolicyTable mdp)
    (defaultState : State) (varianceProxy : NNReal)
    (baseVisitFloor : Real) (threshold : Nat -> Real)
    (scheduleIndex candidate : Nat) (trajectory)
    (hcandidateLower : explicitHighProbabilityRounds scheduleIndex <= candidate)
    (hcandidateUpper : candidate <=
      explicitHighProbabilityRounds scheduleIndex + (2 * scheduleIndex + 1))
    (hhit :
      selfConsistentScheduledNaturalCausalAverageRealizedBehaviorRegretProcess
          mdp initialState rewardSource initialTable defaultState varianceProxy
            baseVisitFloor candidate trajectory <=
        threshold scheduleIndex)
    (hfirst : forall earlier,
      explicitHighProbabilityRounds scheduleIndex <= earlier ->
      earlier < candidate ->
      threshold scheduleIndex <
        selfConsistentScheduledNaturalCausalAverageRealizedBehaviorRegretProcess
          mdp initialState rewardSource initialTable defaultState varianceProxy
            baseVisitFloor earlier trajectory) :
    selfConsistentScheduledNaturalCausalCappedDoubleLinearRawWindowFirstPassagePrefixNat
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor threshold scheduleIndex trajectory = candidate := by
  let process :=
    selfConsistentScheduledNaturalCausalAverageRealizedBehaviorRegretProcess mdp
      initialState rewardSource initialTable defaultState varianceProxy
        baseVisitFloor
  let base := explicitHighProbabilityRounds scheduleIndex
  let right := base + (2 * scheduleIndex + 1)
  have hbaseRight : base <= right := Nat.le_add_right _ _
  unfold selfConsistentScheduledNaturalCausalCappedDoubleLinearRawWindowFirstPassagePrefixNat
  apply le_antisymm
  · exact MeasureTheory.hittingBtwn_le_of_mem hcandidateLower hcandidateUpper hhit
  · by_contra hcandidate
    have hlt :
        MeasureTheory.hittingBtwn process (Set.Iic (threshold scheduleIndex))
            base right trajectory < candidate :=
      Nat.lt_of_not_ge hcandidate
    have hbaseHit : base <=
        MeasureTheory.hittingBtwn process (Set.Iic (threshold scheduleIndex))
          base right trajectory :=
      MeasureTheory.le_hittingBtwn hbaseRight trajectory
    have hhitRight :
        MeasureTheory.hittingBtwn process (Set.Iic (threshold scheduleIndex))
            base right trajectory < right :=
      hlt.trans_le hcandidateUpper
    have hmem :=
      MeasureTheory.hittingBtwn_mem_set_of_hittingBtwn_lt hhitRight
    exact (not_lt_of_ge hmem)
      (hfirst _ hbaseHit hlt)

/-- If the base observation crosses the threshold, first passage is immediate. -/
theorem
    selfConsistentScheduledNaturalCausalCappedDoubleLinearRawWindowFirstPassagePrefixNat_eq_base_of_le
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
    selfConsistentScheduledNaturalCausalCappedDoubleLinearRawWindowFirstPassagePrefixNat
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor threshold scheduleIndex trajectory =
      explicitHighProbabilityRounds scheduleIndex := by
  apply
    selfConsistentScheduledNaturalCausalCappedDoubleLinearRawWindowFirstPassagePrefixNat_eq_of_first_hit
  · exact le_rfl
  · exact Nat.le_add_right _ _
  · exact hthreshold
  · intro earlier hlower hlt
    exact False.elim ((not_lt_of_ge hlower) hlt)

/-- Without an earlier crossing, the capped first-passage rule returns the right endpoint. -/
theorem
    selfConsistentScheduledNaturalCausalCappedDoubleLinearRawWindowFirstPassagePrefixNat_eq_right_of_forall_lt
    (mdp : MDP State Action) (initialState : Measure State)
    [IsProbabilityMeasure initialState]
    (rewardSource : mdp.MeanCompatibleRewardKernel)
    (initialTable : DeterministicMarkovPolicyTable mdp)
    (defaultState : State) (varianceProxy : NNReal)
    (baseVisitFloor : Real) (threshold : Nat -> Real)
    (scheduleIndex : Nat) (trajectory)
    (hbefore : forall earlier,
      explicitHighProbabilityRounds scheduleIndex <= earlier ->
      earlier < explicitHighProbabilityRounds scheduleIndex +
        (2 * scheduleIndex + 1) ->
      threshold scheduleIndex <
        selfConsistentScheduledNaturalCausalAverageRealizedBehaviorRegretProcess
          mdp initialState rewardSource initialTable defaultState varianceProxy
            baseVisitFloor earlier trajectory) :
    selfConsistentScheduledNaturalCausalCappedDoubleLinearRawWindowFirstPassagePrefixNat
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor threshold scheduleIndex trajectory =
      explicitHighProbabilityRounds scheduleIndex + (2 * scheduleIndex + 1) := by
  let process :=
    selfConsistentScheduledNaturalCausalAverageRealizedBehaviorRegretProcess mdp
      initialState rewardSource initialTable defaultState varianceProxy
        baseVisitFloor
  let base := explicitHighProbabilityRounds scheduleIndex
  let right := base + (2 * scheduleIndex + 1)
  have hbaseRight : base <= right := Nat.le_add_right _ _
  unfold selfConsistentScheduledNaturalCausalCappedDoubleLinearRawWindowFirstPassagePrefixNat
  apply le_antisymm
  · exact MeasureTheory.hittingBtwn_le trajectory
  · by_contra hright
    have hlt :
        MeasureTheory.hittingBtwn process (Set.Iic (threshold scheduleIndex))
            base right trajectory < right :=
      Nat.lt_of_not_ge hright
    have hbaseHit : base <=
        MeasureTheory.hittingBtwn process (Set.Iic (threshold scheduleIndex))
          base right trajectory :=
      MeasureTheory.le_hittingBtwn hbaseRight trajectory
    have hmem :=
      MeasureTheory.hittingBtwn_mem_set_of_hittingBtwn_lt hlt
    exact (not_lt_of_ge hmem)
      (hbefore _ hbaseHit hlt)

/-- Every strict pre-stopping prefix in the window is above the threshold. -/
theorem
    selfConsistentScheduledNaturalCausalCappedDoubleLinearRawWindowFirstPassagePrefixNat_before_gt
    (mdp : MDP State Action) (initialState : Measure State)
    [IsProbabilityMeasure initialState]
    (rewardSource : mdp.MeanCompatibleRewardKernel)
    (initialTable : DeterministicMarkovPolicyTable mdp)
    (defaultState : State) (varianceProxy : NNReal)
    (baseVisitFloor : Real) (threshold : Nat -> Real)
    (scheduleIndex earlier : Nat) (trajectory)
    (hlower : explicitHighProbabilityRounds scheduleIndex <= earlier)
    (hearlier : earlier <
      selfConsistentScheduledNaturalCausalCappedDoubleLinearRawWindowFirstPassagePrefixNat
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor threshold scheduleIndex trajectory) :
    threshold scheduleIndex <
      selfConsistentScheduledNaturalCausalAverageRealizedBehaviorRegretProcess
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor earlier trajectory := by
  unfold selfConsistentScheduledNaturalCausalCappedDoubleLinearRawWindowFirstPassagePrefixNat at hearlier
  exact lt_of_not_ge
    (MeasureTheory.notMem_of_lt_hittingBtwn hearlier hlower)

/-- A strict stop before the cap is an actual threshold hit. -/
theorem
    selfConsistentScheduledNaturalCausalCappedDoubleLinearRawWindowFirstPassagePrefixNat_le_threshold_of_lt_right
    (mdp : MDP State Action) (initialState : Measure State)
    [IsProbabilityMeasure initialState]
    (rewardSource : mdp.MeanCompatibleRewardKernel)
    (initialTable : DeterministicMarkovPolicyTable mdp)
    (defaultState : State) (varianceProxy : NNReal)
    (baseVisitFloor : Real) (threshold : Nat -> Real)
    (scheduleIndex : Nat) (trajectory)
    (hstopping :
      selfConsistentScheduledNaturalCausalCappedDoubleLinearRawWindowFirstPassagePrefixNat
          mdp initialState rewardSource initialTable defaultState varianceProxy
            baseVisitFloor threshold scheduleIndex trajectory <
        explicitHighProbabilityRounds scheduleIndex + (2 * scheduleIndex + 1)) :
    selfConsistentScheduledNaturalCausalAverageRealizedBehaviorRegretProcess
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor
          (selfConsistentScheduledNaturalCausalCappedDoubleLinearRawWindowFirstPassagePrefixNat
            mdp initialState rewardSource initialTable defaultState varianceProxy
              baseVisitFloor threshold scheduleIndex trajectory)
          trajectory <=
      threshold scheduleIndex := by
  unfold selfConsistentScheduledNaturalCausalCappedDoubleLinearRawWindowFirstPassagePrefixNat at hstopping ⊢
  exact MeasureTheory.hittingBtwn_mem_set_of_hittingBtwn_lt hstopping

/-- The capped first-passage rule is an exact natural-filtration stopping time. -/
theorem
    selfConsistentScheduledNaturalCausalCappedDoubleLinearRawWindowFirstPassageStoppingPrefix_isStoppingTime
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
      (selfConsistentScheduledNaturalCausalCappedDoubleLinearRawWindowFirstPassageStoppingPrefix
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
  simpa [
    selfConsistentScheduledNaturalCausalCappedDoubleLinearRawWindowFirstPassageStoppingPrefix,
    selfConsistentScheduledNaturalCausalCappedDoubleLinearRawWindowFirstPassagePrefixNat,
    filtration, process] using
      hprocess.adapted.isStoppingTime_hittingBtwn
        (s := Set.Iic (threshold scheduleIndex)) measurableSet_Iic

/-- The capped first-passage rule never stops before its fourth-power base. -/
theorem
    selfConsistentScheduledNaturalCausalCappedDoubleLinearRawWindowFirstPassageStoppingPrefix_lower
    (mdp : MDP State Action) (initialState : Measure State)
    [IsProbabilityMeasure initialState]
    (rewardSource : mdp.MeanCompatibleRewardKernel)
    (initialTable : DeterministicMarkovPolicyTable mdp)
    (defaultState : State) (varianceProxy : NNReal)
    (baseVisitFloor : Real) (threshold : Nat -> Real)
    (scheduleIndex : Nat) (trajectory) :
    (explicitHighProbabilityRounds scheduleIndex : WithTop Nat) <=
      selfConsistentScheduledNaturalCausalCappedDoubleLinearRawWindowFirstPassageStoppingPrefix
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor threshold scheduleIndex trajectory := by
  have hbaseRight : explicitHighProbabilityRounds scheduleIndex <=
      explicitHighProbabilityRounds scheduleIndex + (2 * scheduleIndex + 1) :=
    Nat.le_add_right _ _
  have hbound :=
    (MeasureTheory.hittingBtwn_mem_Icc
      (u := selfConsistentScheduledNaturalCausalAverageRealizedBehaviorRegretProcess
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor)
      (s := Set.Iic (threshold scheduleIndex)) hbaseRight trajectory).1
  unfold selfConsistentScheduledNaturalCausalCappedDoubleLinearRawWindowFirstPassageStoppingPrefix
  unfold selfConsistentScheduledNaturalCausalCappedDoubleLinearRawWindowFirstPassagePrefixNat
  exact_mod_cast hbound

/-- The capped first-passage rule never exceeds its double-linear endpoint. -/
theorem
    selfConsistentScheduledNaturalCausalCappedDoubleLinearRawWindowFirstPassageStoppingPrefix_upper
    (mdp : MDP State Action) (initialState : Measure State)
    [IsProbabilityMeasure initialState]
    (rewardSource : mdp.MeanCompatibleRewardKernel)
    (initialTable : DeterministicMarkovPolicyTable mdp)
    (defaultState : State) (varianceProxy : NNReal)
    (baseVisitFloor : Real) (threshold : Nat -> Real)
    (scheduleIndex : Nat) (trajectory) :
    selfConsistentScheduledNaturalCausalCappedDoubleLinearRawWindowFirstPassageStoppingPrefix
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor threshold scheduleIndex trajectory <=
      (explicitHighProbabilityRounds scheduleIndex +
        (2 * scheduleIndex + 1) : WithTop Nat) := by
  have hbaseRight : explicitHighProbabilityRounds scheduleIndex <=
      explicitHighProbabilityRounds scheduleIndex + (2 * scheduleIndex + 1) :=
    Nat.le_add_right _ _
  have hbound :=
    (MeasureTheory.hittingBtwn_mem_Icc
      (u := selfConsistentScheduledNaturalCausalAverageRealizedBehaviorRegretProcess
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor)
      (s := Set.Iic (threshold scheduleIndex)) hbaseRight trajectory).2
  unfold selfConsistentScheduledNaturalCausalCappedDoubleLinearRawWindowFirstPassageStoppingPrefix
  unfold selfConsistentScheduledNaturalCausalCappedDoubleLinearRawWindowFirstPassagePrefixNat
  exact_mod_cast hbound

/-
Terminal L1 theorem for the genuine first-passage scan of the fourth-power
base through its `2*n+1`-wider raw endpoint.
-/
theorem
    selfConsistentScheduledCausalSource_cappedDoubleLinearRawWindowFirstPassageStoppingTimeNaturalAverageRealizedBehaviorRegret_L1_consistency
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
      selfConsistentScheduledNaturalCausalCappedDoubleLinearRawWindowFirstPassageStoppingPrefix
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
    selfConsistentScheduledNaturalCausalCappedDoubleLinearRawWindowFirstPassageStoppingPrefix
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
                      selfConsistentScheduledNaturalCausalCappedDoubleLinearRawWindowFirstPassageStoppingPrefix_isStoppingTime
                        mdp initialState rewardSource initialTable defaultState
                          varianceProxy baseVisitFloor threshold scheduleIndex)
                    (fun scheduleIndex trajectory =>
                      selfConsistentScheduledNaturalCausalCappedDoubleLinearRawWindowFirstPassageStoppingPrefix_lower
                        mdp initialState rewardSource initialTable defaultState
                          varianceProxy baseVisitFloor threshold scheduleIndex
                            trajectory)
                    (fun scheduleIndex trajectory =>
                      selfConsistentScheduledNaturalCausalCappedDoubleLinearRawWindowFirstPassageStoppingPrefix_upper
                        mdp initialState rewardSource initialTable defaultState
                          varianceProxy baseVisitFloor threshold scheduleIndex
                            trajectory)
  simpa only [stoppingPrefix] using hparent

end AdaptiveStochasticSampledEmpiricalOptimisticSource

end BanditRLProof.FiniteHorizonRL
