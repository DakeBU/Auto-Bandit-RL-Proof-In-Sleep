import BanditRLProof.RL.FiniteHorizonNaturalCausalAverageRealizedBehaviorRegretAlmostSureConsistency

/-!
# Diverging random-prefix almost-sure natural causal consistency

This module consumes the compiled deterministic all-prefix almost-sure theorem
for the exact per-batch-normalized, equal-round-weighted natural average
realized behavior-regret process. A countable random-index measurability
wrapper makes every random-prefix evaluation measurable, while pathwise
composition transports the limit through any measurable random-prefix
schedule which diverges almost everywhere.

This is random-subsequence transport on one dependent causal measure. It does
not use optional stopping and does not prove an anytime confidence sequence,
a stopping-time rate, raw single-episode regret, behavior/recommended-policy
equality, minimax reachability, or complete UCB-VI.
-/

open Filter MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal ProbabilityTheory Topology

namespace BanditRLProof

universe w x

/-- A countable random coordinate of a measurable process is measurable. -/
theorem measurable_apply_randomNat
    {Omega : Type w} {Beta : Type x}
    [MeasurableSpace Omega] [MeasurableSpace Beta]
    (process : Nat -> Omega -> Beta) (randomIndex : Omega -> Nat)
    (hprocess : forall n, Measurable (process n))
    (hrandomIndex : Measurable randomIndex) :
    Measurable (fun omega => process (randomIndex omega) omega) := by
  have hjoint : Measurable (fun input : Omega × Nat => process input.2 input.1) := by
    apply measurable_from_prod_countable_left
    intro n
    simpa using hprocess n
  exact hjoint.comp (measurable_id.prodMk hrandomIndex)

/-- An almost-everywhere limit survives an almost-everywhere diverging random prefix. -/
theorem ae_tendsto_apply_randomPrefix
    {Omega : Type w} {Beta : Type x}
    [MeasurableSpace Omega] [TopologicalSpace Beta]
    {mu : Measure Omega} {process : Nat -> Omega -> Beta}
    {randomPrefix : Nat -> Omega -> Nat} {z : Beta}
    (hprocess : ∀ᵐ omega ∂mu,
      Tendsto (fun n => process n omega) atTop (nhds z))
    (hrandomPrefix : ∀ᵐ omega ∂mu,
      Tendsto (fun n => randomPrefix n omega) atTop atTop) :
    ∀ᵐ omega ∂mu,
      Tendsto (fun n => process (randomPrefix n omega) omega) atTop (nhds z) := by
  filter_upwards [hprocess, hrandomPrefix] with omega hprocessOmega hrandomPrefixOmega
  exact hprocessOmega.comp hrandomPrefixOmega

/-- A pointwise deterministic lower envelope forces a Nat-valued random prefix to diverge. -/
theorem tendsto_randomPrefix_atTop_of_nat_le
    {Omega : Type w} (randomPrefix : Nat -> Omega -> Nat)
    (hlower : forall n omega, n <= randomPrefix n omega) (omega : Omega) :
    Tendsto (fun n => randomPrefix n omega) atTop atTop := by
  refine tendsto_atTop.2 (fun threshold => ?_)
  filter_upwards [eventually_ge_atTop threshold] with n hn
  exact hn.trans (hlower n omega)

namespace FiniteHorizonRL

universe u v

variable {State : Type u} {Action : Type v}
    [MeasurableSpace State] [MeasurableSpace Action]
    [Fintype State] [Fintype Action]
    [DecidableEq State] [DecidableEq Action]
    [MeasurableSingletonClass State] [MeasurableSingletonClass Action]
    [Nonempty State] [Nonempty Action]

namespace AdaptiveStochasticSampledEmpiricalOptimisticSource

/-- The exact natural average realized behavior regret at a random prefix. -/
noncomputable def selfConsistentScheduledNaturalCausalRandomPrefixAverageRealizedBehaviorRegretProcess
    (mdp : MDP State Action) (initialState : Measure State)
    [IsProbabilityMeasure initialState]
    (rewardSource : mdp.MeanCompatibleRewardKernel)
    (initialTable : DeterministicMarkovPolicyTable mdp)
    (defaultState : State) (varianceProxy : NNReal)
    (baseVisitFloor : Real)
    (randomPrefix : Nat ->
      HeterogeneousStochasticEpisodeBatchTrajectory mdp
        (fun t =>
          AdaptiveStochasticEpisodeBatchSource.selfConsistentScheduledEpisodes
            mdp varianceProxy baseVisitFloor t) -> Nat)
    (scheduleIndex : Nat) :
    HeterogeneousStochasticEpisodeBatchTrajectory mdp
        (fun t =>
          AdaptiveStochasticEpisodeBatchSource.selfConsistentScheduledEpisodes
            mdp varianceProxy baseVisitFloor t) -> Real :=
  fun trajectory =>
    selfConsistentScheduledNaturalCausalAverageRealizedBehaviorRegretProcess
      mdp initialState rewardSource initialTable defaultState varianceProxy
        baseVisitFloor (randomPrefix scheduleIndex trajectory) trajectory

@[simp]
theorem selfConsistentScheduledNaturalCausalRandomPrefixAverageRealizedBehaviorRegretProcess_apply
    (mdp : MDP State Action) (initialState : Measure State)
    [IsProbabilityMeasure initialState]
    (rewardSource : mdp.MeanCompatibleRewardKernel)
    (initialTable : DeterministicMarkovPolicyTable mdp)
    (defaultState : State) (varianceProxy : NNReal)
    (baseVisitFloor : Real)
    (randomPrefix : Nat ->
      HeterogeneousStochasticEpisodeBatchTrajectory mdp
        (fun t =>
          AdaptiveStochasticEpisodeBatchSource.selfConsistentScheduledEpisodes
            mdp varianceProxy baseVisitFloor t) -> Nat)
    (scheduleIndex : Nat)
    (trajectory : HeterogeneousStochasticEpisodeBatchTrajectory mdp
      (fun t =>
        AdaptiveStochasticEpisodeBatchSource.selfConsistentScheduledEpisodes
          mdp varianceProxy baseVisitFloor t)) :
    selfConsistentScheduledNaturalCausalRandomPrefixAverageRealizedBehaviorRegretProcess
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor randomPrefix scheduleIndex trajectory =
      selfConsistentScheduledNaturalCausalAverageRealizedBehaviorRegretProcess
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor (randomPrefix scheduleIndex trajectory) trajectory := by
  rfl

/-- Every coordinate of the exact random-prefix process is measurable. -/
theorem measurable_selfConsistentScheduledNaturalCausalRandomPrefixAverageRealizedBehaviorRegretProcess
    (mdp : MDP State Action) (initialState : Measure State)
    [IsProbabilityMeasure initialState]
    (rewardSource : mdp.MeanCompatibleRewardKernel)
    (initialTable : DeterministicMarkovPolicyTable mdp)
    (defaultState : State) (varianceProxy : NNReal)
    (baseVisitFloor : Real)
    (randomPrefix : Nat ->
      HeterogeneousStochasticEpisodeBatchTrajectory mdp
        (fun t =>
          AdaptiveStochasticEpisodeBatchSource.selfConsistentScheduledEpisodes
            mdp varianceProxy baseVisitFloor t) -> Nat)
    (scheduleIndex : Nat) (hrandomPrefix : Measurable (randomPrefix scheduleIndex)) :
    Measurable
      (selfConsistentScheduledNaturalCausalRandomPrefixAverageRealizedBehaviorRegretProcess
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor randomPrefix scheduleIndex) := by
  unfold selfConsistentScheduledNaturalCausalRandomPrefixAverageRealizedBehaviorRegretProcess
  exact measurable_apply_randomNat
    (fun rounds =>
      selfConsistentScheduledNaturalCausalAverageRealizedBehaviorRegretProcess
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor rounds)
    (randomPrefix scheduleIndex)
    (fun rounds =>
      measurable_selfConsistentScheduledNaturalCausalAverageRealizedBehaviorRegretProcess
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor rounds)
    hrandomPrefix

/--
The exact natural average realized behavior regret remains almost-surely
consistent at every measurable random prefix which diverges almost everywhere.
-/
theorem selfConsistentScheduledCausalSource_randomPrefixNaturalAverageRealizedBehaviorRegret_tendstoAlmostEverywhere_zero
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
    (randomPrefix : Nat ->
      HeterogeneousStochasticEpisodeBatchTrajectory mdp
        (fun t =>
          AdaptiveStochasticEpisodeBatchSource.selfConsistentScheduledEpisodes
            mdp varianceProxy baseVisitFloor t) -> Nat)
    (hrandomPrefixMeasurable : forall n, Measurable (randomPrefix n))
    (hrandomPrefixDiverges :
      ∀ᵐ trajectory ∂
        (selfConsistentScheduledCausalSource mdp initialState rewardSource
          initialTable defaultState varianceProxy baseVisitFloor).trajectoryMeasure,
        Tendsto (fun n => randomPrefix n trajectory) atTop atTop) :
    let source := selfConsistentScheduledCausalSource mdp initialState
      rewardSource initialTable defaultState varianceProxy baseVisitFloor
    (forall n,
      Measurable
        (selfConsistentScheduledNaturalCausalRandomPrefixAverageRealizedBehaviorRegretProcess
          mdp initialState rewardSource initialTable defaultState varianceProxy
            baseVisitFloor randomPrefix n)) /\
      ∀ᵐ trajectory ∂source.trajectoryMeasure,
        Tendsto
          (fun n =>
            selfConsistentScheduledNaturalCausalRandomPrefixAverageRealizedBehaviorRegretProcess
              mdp initialState rewardSource initialTable defaultState
                varianceProxy baseVisitFloor randomPrefix n trajectory)
          atTop (nhds 0) := by
  dsimp only
  refine ⟨fun n =>
    measurable_selfConsistentScheduledNaturalCausalRandomPrefixAverageRealizedBehaviorRegretProcess
      mdp initialState rewardSource initialTable defaultState varianceProxy
        baseVisitFloor randomPrefix n (hrandomPrefixMeasurable n), ?_⟩
  have hparent :=
    selfConsistentScheduledCausalSource_naturalAverageRealizedBehaviorRegret_tendstoAlmostEverywhere_zero
      mdp initialState rewardSource varianceProxy hvarianceProxy law initialTable
        defaultState support baseVisitFloor hbaseFloor hrewardBound hhorizon
          hbaseVisitFloor
  have hcomposed :=
    ae_tendsto_apply_randomPrefix
      (process := fun rounds trajectory =>
        selfConsistentScheduledNaturalCausalAverageRealizedBehaviorRegretProcess
          mdp initialState rewardSource initialTable defaultState varianceProxy
            baseVisitFloor rounds trajectory)
      (randomPrefix := randomPrefix) hparent.2 hrandomPrefixDiverges
  simpa [selfConsistentScheduledNaturalCausalRandomPrefixAverageRealizedBehaviorRegretProcess]
    using hcomposed

/-- A pointwise lower envelope is a practical sufficient random-prefix contract. -/
theorem selfConsistentScheduledCausalSource_randomPrefixNaturalAverageRealizedBehaviorRegret_tendstoAlmostEverywhere_zero_of_nat_le
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
    (randomPrefix : Nat ->
      HeterogeneousStochasticEpisodeBatchTrajectory mdp
        (fun t =>
          AdaptiveStochasticEpisodeBatchSource.selfConsistentScheduledEpisodes
            mdp varianceProxy baseVisitFloor t) -> Nat)
    (hrandomPrefixMeasurable : forall n, Measurable (randomPrefix n))
    (hrandomPrefixLower : forall n trajectory, n <= randomPrefix n trajectory) :
    let source := selfConsistentScheduledCausalSource mdp initialState
      rewardSource initialTable defaultState varianceProxy baseVisitFloor
    (forall n,
      Measurable
        (selfConsistentScheduledNaturalCausalRandomPrefixAverageRealizedBehaviorRegretProcess
          mdp initialState rewardSource initialTable defaultState varianceProxy
            baseVisitFloor randomPrefix n)) /\
      ∀ᵐ trajectory ∂source.trajectoryMeasure,
        Tendsto
          (fun n =>
            selfConsistentScheduledNaturalCausalRandomPrefixAverageRealizedBehaviorRegretProcess
              mdp initialState rewardSource initialTable defaultState
                varianceProxy baseVisitFloor randomPrefix n trajectory)
          atTop (nhds 0) := by
  apply
    selfConsistentScheduledCausalSource_randomPrefixNaturalAverageRealizedBehaviorRegret_tendstoAlmostEverywhere_zero
      mdp initialState rewardSource varianceProxy hvarianceProxy law initialTable
        defaultState support baseVisitFloor hbaseFloor hrewardBound hhorizon
          hbaseVisitFloor randomPrefix hrandomPrefixMeasurable
  exact Filter.Eventually.of_forall fun trajectory =>
    tendsto_randomPrefix_atTop_of_nat_le randomPrefix hrandomPrefixLower trajectory

end AdaptiveStochasticSampledEmpiricalOptimisticSource

end FiniteHorizonRL

end BanditRLProof
