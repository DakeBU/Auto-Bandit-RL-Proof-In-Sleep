import BanditRLProof.RL.FiniteHorizonNaturalCausalRandomPrefixAverageRealizedBehaviorRegretAlmostSureConsistency
import Mathlib.Probability.Process.Stopping

/-!
# Diverging stopping-time almost-sure natural causal consistency

This module equips the heterogeneous causal batch trajectory with its dependent
`Filtration.piLE` natural filtration. The exact per-batch-normalized,
equal-round-weighted average realized behavior-regret process is strongly
adapted to that filtration: its value at prefix `r` uses only successor batches
with coordinates at most `r`.

Mathlib's `measurable_stoppedValue` then makes evaluation at every stopping
time measurable. The compiled all-prefix almost-sure theorem is transported
through a sequence of stopping times whose `untopA` values diverge. Mathlib
maps `⊤.untopA` to an arbitrary natural default, so this divergence premise
implies that the sequence is eventually finite while still permitting finitely
many `⊤` values. This is pathwise stopped-subsequence consistency, not optional
stopping and not an anytime finite-sample rate.
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

namespace HeterogeneousAdaptiveStochasticEpisodeBatchSource

/-- The dependent coordinate filtration through the current batch coordinate. -/
def naturalTrajectoryFiltration
    {mdp : MDP State Action} {initialState : Measure State}
    [IsProbabilityMeasure initialState] {episodes : Nat -> Nat}
    (_source : HeterogeneousAdaptiveStochasticEpisodeBatchSource
      mdp initialState episodes) :
    Filtration Nat
      (inferInstance : MeasurableSpace
        (HeterogeneousStochasticEpisodeBatchTrajectory mdp episodes)) :=
  Filtration.piLE
    (X := fun n : Nat => StochasticEpisodeBatch mdp (episodes n))

omit [DecidableEq State] [DecidableEq Action]
    [MeasurableSingletonClass State] [MeasurableSingletonClass Action]
    [Nonempty State] [Nonempty Action] in
@[simp]
theorem naturalTrajectoryFiltration_apply
    {mdp : MDP State Action} {initialState : Measure State}
    [IsProbabilityMeasure initialState] {episodes : Nat -> Nat}
    (source : HeterogeneousAdaptiveStochasticEpisodeBatchSource
      mdp initialState episodes) (n : Nat) :
    (source.naturalTrajectoryFiltration n :
      MeasurableSpace
        (HeterogeneousStochasticEpisodeBatchTrajectory mdp episodes)) =
      Filtration.piLE
        (X := fun n : Nat => StochasticEpisodeBatch mdp (episodes n)) n :=
  rfl

omit [DecidableEq State] [DecidableEq Action]
    [MeasurableSingletonClass State] [MeasurableSingletonClass Action]
    [Nonempty State] [Nonempty Action] in
/-- A trajectory coordinate is measurable at every later natural-filtration level. -/
theorem measurable_naturalTrajectory_coordinate_of_le
    {mdp : MDP State Action} {initialState : Measure State}
    [IsProbabilityMeasure initialState] {episodes : Nat -> Nat}
    (source : HeterogeneousAdaptiveStochasticEpisodeBatchSource
      mdp initialState episodes) {coordinate horizon : Nat}
    (hcoordinate : coordinate <= horizon) :
    @Measurable
      (HeterogeneousStochasticEpisodeBatchTrajectory mdp episodes)
      (StochasticEpisodeBatch mdp (episodes coordinate))
      (source.naturalTrajectoryFiltration horizon) inferInstance
      (fun trajectory => trajectory coordinate) := by
  have hprefix :
      @Measurable
        (HeterogeneousStochasticEpisodeBatchTrajectory mdp episodes)
        ((i : Finset.Iic horizon) ->
          StochasticEpisodeBatch mdp (episodes i))
        (source.naturalTrajectoryFiltration horizon) inferInstance
        (Preorder.frestrictLe horizon) := by
    rw [naturalTrajectoryFiltration_apply,
      Filtration.piLE_eq_comap_frestrictLe]
    exact Measurable.of_comap_le le_rfl
  let index : Finset.Iic horizon :=
    ⟨coordinate, Finset.mem_Iic.mpr hcoordinate⟩
  have heval :
      Measurable
        (fun history : (i : Finset.Iic horizon) ->
            StochasticEpisodeBatch mdp (episodes i) =>
          history index) :=
    measurable_pi_apply index
  simpa [index, Preorder.frestrictLe] using heval.comp hprefix

omit [DecidableEq State] [DecidableEq Action]
    [MeasurableSingletonClass State] [MeasurableSingletonClass Action]
    [Nonempty State] in
/-- One successor-batch realized-regret coordinate is measurable at its batch time. -/
theorem measurable_naturalSuccessorBatchAverageRealizedRegret_naturalTrajectoryFiltration
    {mdp : MDP State Action} {initialState : Measure State}
    [IsProbabilityMeasure initialState] {episodes : Nat -> Nat}
    (source : HeterogeneousAdaptiveStochasticEpisodeBatchSource
      mdp initialState episodes) (t : Nat) :
    @Measurable
      (HeterogeneousStochasticEpisodeBatchTrajectory mdp episodes) Real
      (source.naturalTrajectoryFiltration (t + 1)) inferInstance
      (fun trajectory =>
        source.naturalSuccessorBatchAverageRealizedRegret trajectory t) := by
  unfold naturalSuccessorBatchAverageRealizedRegret
  exact measurable_const.sub
    (((mdp.measurable_sampledCumulativeRewardSum (episodes (t + 1))).comp
      (source.measurable_naturalTrajectory_coordinate_of_le le_rfl)).div_const
        (episodes (t + 1) : Real))

omit [DecidableEq State] [DecidableEq Action]
    [MeasurableSingletonClass State] [MeasurableSingletonClass Action]
    [Nonempty State] in
/-- The cumulative realized-regret prefix is measurable at its prefix level. -/
theorem measurable_naturalCumulativeRealizedBehaviorRegret_naturalTrajectoryFiltration
    {mdp : MDP State Action} {initialState : Measure State}
    [IsProbabilityMeasure initialState] {episodes : Nat -> Nat}
    (source : HeterogeneousAdaptiveStochasticEpisodeBatchSource
      mdp initialState episodes) (rounds : Nat) :
    @Measurable
      (HeterogeneousStochasticEpisodeBatchTrajectory mdp episodes) Real
      (source.naturalTrajectoryFiltration rounds) inferInstance
      (fun trajectory =>
        source.naturalCumulativeRealizedBehaviorRegret trajectory rounds) := by
  unfold naturalCumulativeRealizedBehaviorRegret
  refine Finset.measurable_sum (Finset.range rounds) fun t ht => ?_
  have ht_succ : t + 1 <= rounds :=
    Nat.succ_le_iff.mpr (Finset.mem_range.mp ht)
  exact
    (source.measurable_naturalSuccessorBatchAverageRealizedRegret_naturalTrajectoryFiltration
      t).mono (source.naturalTrajectoryFiltration.mono ht_succ) le_rfl

omit [DecidableEq State] [DecidableEq Action]
    [MeasurableSingletonClass State] [MeasurableSingletonClass Action]
    [Nonempty State] in
/-- The exact average realized-regret prefix is measurable at its prefix level. -/
theorem measurable_naturalAverageRealizedBehaviorRegret_naturalTrajectoryFiltration
    {mdp : MDP State Action} {initialState : Measure State}
    [IsProbabilityMeasure initialState] {episodes : Nat -> Nat}
    (source : HeterogeneousAdaptiveStochasticEpisodeBatchSource
      mdp initialState episodes) (rounds : Nat) :
    @Measurable
      (HeterogeneousStochasticEpisodeBatchTrajectory mdp episodes) Real
      (source.naturalTrajectoryFiltration rounds) inferInstance
      (fun trajectory =>
        source.naturalAverageRealizedBehaviorRegret trajectory rounds) := by
  unfold naturalAverageRealizedBehaviorRegret
  exact
    (source.measurable_naturalCumulativeRealizedBehaviorRegret_naturalTrajectoryFiltration
      rounds).div_const (rounds : Real)

omit [DecidableEq State] [DecidableEq Action]
    [MeasurableSingletonClass State] [MeasurableSingletonClass Action]
    [Nonempty State] in
/-- The exact natural average realized-regret process is strongly adapted. -/
theorem naturalAverageRealizedBehaviorRegret_stronglyAdapted_naturalTrajectoryFiltration
    {mdp : MDP State Action} {initialState : Measure State}
    [IsProbabilityMeasure initialState] {episodes : Nat -> Nat}
    (source : HeterogeneousAdaptiveStochasticEpisodeBatchSource
      mdp initialState episodes) :
    StronglyAdapted source.naturalTrajectoryFiltration
      (fun rounds trajectory =>
        source.naturalAverageRealizedBehaviorRegret trajectory rounds) := by
  intro rounds
  exact
    (source.measurable_naturalAverageRealizedBehaviorRegret_naturalTrajectoryFiltration
      rounds).stronglyMeasurable

end HeterogeneousAdaptiveStochasticEpisodeBatchSource

namespace AdaptiveStochasticSampledEmpiricalOptimisticSource

/-- Natural filtration of the self-consistent heterogeneous causal source. -/
noncomputable def selfConsistentScheduledNaturalCausalTrajectoryFiltration
    (mdp : MDP State Action) (initialState : Measure State)
    [IsProbabilityMeasure initialState]
    (rewardSource : mdp.MeanCompatibleRewardKernel)
    (initialTable : DeterministicMarkovPolicyTable mdp)
    (defaultState : State) (varianceProxy : NNReal)
    (baseVisitFloor : Real) :
    Filtration Nat
      (inferInstance : MeasurableSpace
        (HeterogeneousStochasticEpisodeBatchTrajectory mdp
          (fun t =>
            AdaptiveStochasticEpisodeBatchSource.selfConsistentScheduledEpisodes
              mdp varianceProxy baseVisitFloor t))) :=
  (selfConsistentScheduledCausalSource mdp initialState rewardSource
    initialTable defaultState varianceProxy baseVisitFloor).naturalTrajectoryFiltration

/-- The exact self-consistent natural average process is strongly adapted. -/
theorem selfConsistentScheduledNaturalCausalAverageRealizedBehaviorRegretProcess_stronglyAdapted
    (mdp : MDP State Action) (initialState : Measure State)
    [IsProbabilityMeasure initialState]
    (rewardSource : mdp.MeanCompatibleRewardKernel)
    (initialTable : DeterministicMarkovPolicyTable mdp)
    (defaultState : State) (varianceProxy : NNReal)
    (baseVisitFloor : Real) :
    StronglyAdapted
      (selfConsistentScheduledNaturalCausalTrajectoryFiltration mdp initialState
        rewardSource initialTable defaultState varianceProxy baseVisitFloor)
      (selfConsistentScheduledNaturalCausalAverageRealizedBehaviorRegretProcess
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor) := by
  let source := selfConsistentScheduledCausalSource mdp initialState
    rewardSource initialTable defaultState varianceProxy baseVisitFloor
  simpa [selfConsistentScheduledNaturalCausalTrajectoryFiltration,
    selfConsistentScheduledNaturalCausalAverageRealizedBehaviorRegretProcess,
    source] using
      source.naturalAverageRealizedBehaviorRegret_stronglyAdapted_naturalTrajectoryFiltration

/-- The exact average realized-regret process evaluated at a stopping time. -/
noncomputable def selfConsistentScheduledNaturalCausalStoppingTimeAverageRealizedBehaviorRegretProcess
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
    HeterogeneousStochasticEpisodeBatchTrajectory mdp
        (fun t =>
          AdaptiveStochasticEpisodeBatchSource.selfConsistentScheduledEpisodes
            mdp varianceProxy baseVisitFloor t) -> Real :=
  stoppedValue
    (selfConsistentScheduledNaturalCausalAverageRealizedBehaviorRegretProcess
      mdp initialState rewardSource initialTable defaultState varianceProxy
        baseVisitFloor)
    (stoppingPrefix scheduleIndex)

@[simp]
theorem selfConsistentScheduledNaturalCausalStoppingTimeAverageRealizedBehaviorRegretProcess_apply
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
    (scheduleIndex : Nat)
    (trajectory : HeterogeneousStochasticEpisodeBatchTrajectory mdp
      (fun t =>
        AdaptiveStochasticEpisodeBatchSource.selfConsistentScheduledEpisodes
          mdp varianceProxy baseVisitFloor t)) :
    selfConsistentScheduledNaturalCausalStoppingTimeAverageRealizedBehaviorRegretProcess
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor stoppingPrefix scheduleIndex trajectory =
      selfConsistentScheduledNaturalCausalAverageRealizedBehaviorRegretProcess
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor (stoppingPrefix scheduleIndex trajectory).untopA trajectory :=
  rfl

/-- Mathlib stopped-value measurability for the exact adapted process. -/
theorem measurable_selfConsistentScheduledNaturalCausalStoppingTimeAverageRealizedBehaviorRegretProcess
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
    (scheduleIndex : Nat)
    (hstopping : IsStoppingTime
      (selfConsistentScheduledNaturalCausalTrajectoryFiltration mdp initialState
        rewardSource initialTable defaultState varianceProxy baseVisitFloor)
      (stoppingPrefix scheduleIndex)) :
    Measurable
      (selfConsistentScheduledNaturalCausalStoppingTimeAverageRealizedBehaviorRegretProcess
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor stoppingPrefix scheduleIndex) := by
  have hprogressive :
      ProgMeasurable
        (selfConsistentScheduledNaturalCausalTrajectoryFiltration mdp initialState
          rewardSource initialTable defaultState varianceProxy baseVisitFloor)
        (selfConsistentScheduledNaturalCausalAverageRealizedBehaviorRegretProcess
          mdp initialState rewardSource initialTable defaultState varianceProxy
            baseVisitFloor) :=
    (selfConsistentScheduledNaturalCausalAverageRealizedBehaviorRegretProcess_stronglyAdapted
      mdp initialState rewardSource initialTable defaultState varianceProxy
        baseVisitFloor).progMeasurable_of_discrete
  exact
    (measurable_stoppedValue hprogressive hstopping).mono
      hstopping.measurableSpace_le le_rfl

/-
The stopping times are used for adapted stopped-value measurability. The limit
itself is pathwise composition of the compiled all-prefix theorem, so no
optional-stopping expectation identity is invoked.
-/
/-- Diverging stopping times preserve almost-sure natural average consistency. -/
theorem selfConsistentScheduledCausalSource_stoppingTimeNaturalAverageRealizedBehaviorRegret_tendstoAlmostEverywhere_zero
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
    (hstopping : forall n, IsStoppingTime
      (selfConsistentScheduledNaturalCausalTrajectoryFiltration mdp initialState
        rewardSource initialTable defaultState varianceProxy baseVisitFloor)
      (stoppingPrefix n))
    (hstoppingDiverges :
      let source := selfConsistentScheduledCausalSource mdp initialState
        rewardSource initialTable defaultState varianceProxy baseVisitFloor
      ∀ᵐ trajectory ∂source.trajectoryMeasure,
        Tendsto (fun n => (stoppingPrefix n trajectory).untopA) atTop atTop) :
    let source := selfConsistentScheduledCausalSource mdp initialState
      rewardSource initialTable defaultState varianceProxy baseVisitFloor
    StronglyAdapted
        (selfConsistentScheduledNaturalCausalTrajectoryFiltration mdp initialState
          rewardSource initialTable defaultState varianceProxy baseVisitFloor)
        (selfConsistentScheduledNaturalCausalAverageRealizedBehaviorRegretProcess
          mdp initialState rewardSource initialTable defaultState varianceProxy
            baseVisitFloor) /\
      (forall n,
        Measurable
          (selfConsistentScheduledNaturalCausalStoppingTimeAverageRealizedBehaviorRegretProcess
            mdp initialState rewardSource initialTable defaultState varianceProxy
              baseVisitFloor stoppingPrefix n)) /\
      ∀ᵐ trajectory ∂source.trajectoryMeasure,
        Tendsto
          (fun n =>
            selfConsistentScheduledNaturalCausalStoppingTimeAverageRealizedBehaviorRegretProcess
              mdp initialState rewardSource initialTable defaultState varianceProxy
                baseVisitFloor stoppingPrefix n trajectory)
          atTop (nhds 0) := by
  dsimp only
  refine ⟨
    selfConsistentScheduledNaturalCausalAverageRealizedBehaviorRegretProcess_stronglyAdapted
      mdp initialState rewardSource initialTable defaultState varianceProxy
        baseVisitFloor, ?_, ?_⟩
  · intro n
    exact
      measurable_selfConsistentScheduledNaturalCausalStoppingTimeAverageRealizedBehaviorRegretProcess
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor stoppingPrefix n (hstopping n)
  · have hparent :=
      selfConsistentScheduledCausalSource_randomPrefixNaturalAverageRealizedBehaviorRegret_tendstoAlmostEverywhere_zero
        mdp initialState rewardSource varianceProxy hvarianceProxy law initialTable
          defaultState support baseVisitFloor hbaseFloor hrewardBound hhorizon
            hbaseVisitFloor
            (fun n trajectory => (stoppingPrefix n trajectory).untopA)
            (fun n => (hstopping n).measurable'.untopA)
            hstoppingDiverges
    simpa [
      selfConsistentScheduledNaturalCausalStoppingTimeAverageRealizedBehaviorRegretProcess,
      selfConsistentScheduledNaturalCausalRandomPrefixAverageRealizedBehaviorRegretProcess,
      stoppedValue] using hparent.2

/-- The practical lower envelope `n <= tau_n` forces the stopped prefixes to diverge. -/
theorem selfConsistentScheduledCausalSource_stoppingTimeNaturalAverageRealizedBehaviorRegret_tendstoAlmostEverywhere_zero_of_nat_le
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
    (hstopping : forall n, IsStoppingTime
      (selfConsistentScheduledNaturalCausalTrajectoryFiltration mdp initialState
        rewardSource initialTable defaultState varianceProxy baseVisitFloor)
      (stoppingPrefix n))
    (hstoppingLower : forall n trajectory,
      n <= (stoppingPrefix n trajectory).untopA) :
    let source := selfConsistentScheduledCausalSource mdp initialState
      rewardSource initialTable defaultState varianceProxy baseVisitFloor
    StronglyAdapted
        (selfConsistentScheduledNaturalCausalTrajectoryFiltration mdp initialState
          rewardSource initialTable defaultState varianceProxy baseVisitFloor)
        (selfConsistentScheduledNaturalCausalAverageRealizedBehaviorRegretProcess
          mdp initialState rewardSource initialTable defaultState varianceProxy
            baseVisitFloor) /\
      (forall n,
        Measurable
          (selfConsistentScheduledNaturalCausalStoppingTimeAverageRealizedBehaviorRegretProcess
            mdp initialState rewardSource initialTable defaultState varianceProxy
              baseVisitFloor stoppingPrefix n)) /\
      ∀ᵐ trajectory ∂source.trajectoryMeasure,
        Tendsto
          (fun n =>
            selfConsistentScheduledNaturalCausalStoppingTimeAverageRealizedBehaviorRegretProcess
              mdp initialState rewardSource initialTable defaultState varianceProxy
                baseVisitFloor stoppingPrefix n trajectory)
          atTop (nhds 0) := by
  apply
    selfConsistentScheduledCausalSource_stoppingTimeNaturalAverageRealizedBehaviorRegret_tendstoAlmostEverywhere_zero
      mdp initialState rewardSource varianceProxy hvarianceProxy law initialTable
        defaultState support baseVisitFloor hbaseFloor hrewardBound hhorizon
          hbaseVisitFloor stoppingPrefix hstopping
  exact Filter.Eventually.of_forall fun trajectory =>
    tendsto_randomPrefix_atTop_of_nat_le
      (fun n trajectory => (stoppingPrefix n trajectory).untopA)
      hstoppingLower trajectory

end AdaptiveStochasticSampledEmpiricalOptimisticSource

end BanditRLProof.FiniteHorizonRL
