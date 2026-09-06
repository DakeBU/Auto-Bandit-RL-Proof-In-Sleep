import BanditRLProof.RL.FiniteHorizonAdaptiveStochasticRewardSampledEmpiricalOptimisticSelfConsistentExplicitRate
import BanditRLProof.KernelTrajectoryPrefix

/-!
# Heterogeneous causal source for the actual-sampled self-consistent schedule

The compiled self-consistent finite-window theorems vary the batch size and
algorithm parameters with the outer window index. Their laws therefore are not
prefixes of one fixed adaptive source. This module defines the distinct causal
algorithm in which those parameters vary at each trajectory coordinate.

The coordinate type itself is dependent: coordinate `n` contains a stochastic
episode batch of size `episodes n`. Mathlib's dependent `Kernel.trajMeasure`
then constructs one Ionescu-Tulcea law. The terminal theorem records the exact
initial law, every selected next-batch conditional law, the prefix/next
`compProd` factorization, and projective consistency of all finite marginals.

Local APIs/imports are the actual-sampled measurable optimistic table,
`exploratoryIIDStochasticEpisodeBatchKernel`, dependent
`Kernel.trajMeasure`, `Kernel.condDistrib_trajMeasure`,
`map_frestrictLe_trajMeasure_compProd_eq_map_trajMeasure`, and measurable
finite restrictions. Retrieval found no existing heterogeneous actual-sampled
causal-source route; `KernelTrajectoryPrefix.trajMeasure_map_frestrictLe_congr`
is supporting local evidence.

Regularity for the law construction is finite measurable nonempty State and
Action with equality and measurable singletons plus a probability initial law.
Standard Borel State/Action is needed only for the `condDistrib` endpoint.

Failure policy: this is a new round-varying algorithm. It preserves actual
sampled rewards and uses only the latest completed batch, but it does not have
the old fixed-window laws as marginals and does not inherit their confidence,
optimism, regret, or rate theorem. Those require new heterogeneous
concentration and regret transports. No pathwise, almost-sure, anytime,
minimax, reachability, or complete-UCB-VI claim is made here.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal ProbabilityTheory

universe u v

namespace BanditRLProof.FiniteHorizonRL

variable {State : Type u} {Action : Type v}
    [MeasurableSpace State] [MeasurableSpace Action]
    [Fintype State] [Fintype Action]
    [DecidableEq State] [DecidableEq Action]
    [MeasurableSingletonClass State] [MeasurableSingletonClass Action]
    [Nonempty State] [Nonempty Action]

/-- A trajectory whose complete stochastic batch size may vary by coordinate. -/
abbrev HeterogeneousStochasticEpisodeBatchTrajectory
    (mdp : MDP State Action) (episodes : Nat -> Nat) :=
  (n : Nat) -> StochasticEpisodeBatch mdp (episodes n)

/-- A finite dependent batch history through coordinate `n`. -/
abbrev HeterogeneousStochasticEpisodeBatchPrefix
    (mdp : MDP State Action) (episodes : Nat -> Nat) (n : Nat) :=
  (i : Finset.Iic n) -> StochasticEpisodeBatch mdp (episodes i)

/--
An adaptive source of stochastic episode batches with coordinate-dependent
batch sizes.
-/
structure HeterogeneousAdaptiveStochasticEpisodeBatchSource
    (mdp : MDP State Action) (initialState : Measure State)
    [IsProbabilityMeasure initialState] (episodes : Nat -> Nat) where
  rewardSource : mdp.MeanCompatibleRewardKernel
  initialPolicy : MarkovPolicy mdp
  successorPolicy : (n : Nat) ->
    HeterogeneousStochasticEpisodeBatchPrefix mdp episodes n -> MarkovPolicy mdp
  batchKernel : (n : Nat) -> Kernel
    (HeterogeneousStochasticEpisodeBatchPrefix mdp episodes n)
    (StochasticEpisodeBatch mdp (episodes (n + 1)))
  batchKernel_isMarkov : forall n, IsMarkovKernel (batchKernel n)
  batchKernel_eq_iidStochasticTrajectoryFamilyMeasure : forall n history,
    batchKernel n history =
      rewardSource.iidStochasticTrajectoryFamilyMeasure
        (successorPolicy n history) initialState (episodes (n + 1))
  measurable_successorSampledReturnDeviation : forall n,
    Measurable fun pair :
        HeterogeneousStochasticEpisodeBatchPrefix mdp episodes n ×
          StochasticEpisodeBatch mdp (episodes (n + 1)) =>
      mdp.sampledCumulativeReturnDeviationSum
        (successorPolicy n pair.1) (episodes (n + 1)) pair.2

namespace HeterogeneousAdaptiveStochasticEpisodeBatchSource

instance instBatchKernelIsMarkov
    {mdp : MDP State Action} {initialState : Measure State}
    [IsProbabilityMeasure initialState] {episodes : Nat -> Nat}
    (source : HeterogeneousAdaptiveStochasticEpisodeBatchSource
      mdp initialState episodes) (n : Nat) :
    IsMarkovKernel (source.batchKernel n) :=
  source.batchKernel_isMarkov n

/-- The one-process dependent Ionescu-Tulcea trajectory law. -/
noncomputable def trajectoryMeasure
    {mdp : MDP State Action} {initialState : Measure State}
    [IsProbabilityMeasure initialState] {episodes : Nat -> Nat}
    (source : HeterogeneousAdaptiveStochasticEpisodeBatchSource
      mdp initialState episodes) :
    Measure (HeterogeneousStochasticEpisodeBatchTrajectory mdp episodes) :=
  Kernel.trajMeasure
    (X := fun n : Nat => StochasticEpisodeBatch mdp (episodes n))
    (source.rewardSource.iidStochasticTrajectoryFamilyMeasure
      source.initialPolicy initialState (episodes 0))
    source.batchKernel

instance instTrajectoryMeasureIsProbabilityMeasure
    {mdp : MDP State Action} {initialState : Measure State}
    [IsProbabilityMeasure initialState] {episodes : Nat -> Nat}
    (source : HeterogeneousAdaptiveStochasticEpisodeBatchSource
      mdp initialState episodes) :
    IsProbabilityMeasure source.trajectoryMeasure := by
  unfold trajectoryMeasure
  infer_instance

omit [DecidableEq State] [DecidableEq Action]
    [MeasurableSingletonClass State] [MeasurableSingletonClass Action]
    [Nonempty State] [Nonempty Action] in
/-- Coordinate zero has the configured initial stochastic batch law. -/
theorem trajectoryMeasure_map_eval_zero
    {mdp : MDP State Action} {initialState : Measure State}
    [IsProbabilityMeasure initialState] {episodes : Nat -> Nat}
    (source : HeterogeneousAdaptiveStochasticEpisodeBatchSource
      mdp initialState episodes) :
    source.trajectoryMeasure.map (Function.eval 0) =
      source.rewardSource.iidStochasticTrajectoryFamilyMeasure
        source.initialPolicy initialState (episodes 0) := by
  unfold trajectoryMeasure
  exact RewardKernel.trajMeasure_map_eval_zero
    (X := fun n : Nat => StochasticEpisodeBatch mdp (episodes n))
    (source.rewardSource.iidStochasticTrajectoryFamilyMeasure
      source.initialPolicy initialState (episodes 0))
    source.batchKernel

omit [DecidableEq State] [DecidableEq Action]
    [MeasurableSingletonClass State] [MeasurableSingletonClass Action]
    [Nonempty State] [Nonempty Action] in
/-- Every prefix/next marginal has the configured causal `compProd` law. -/
theorem trajectoryMeasure_prefix_compProd
    {mdp : MDP State Action} {initialState : Measure State}
    [IsProbabilityMeasure initialState] {episodes : Nat -> Nat}
    (source : HeterogeneousAdaptiveStochasticEpisodeBatchSource
      mdp initialState episodes) (n : Nat) :
    source.trajectoryMeasure.map (Preorder.frestrictLe n) ⊗ₘ
        source.batchKernel n =
      source.trajectoryMeasure.map
        (fun trajectory =>
          (Preorder.frestrictLe n trajectory, trajectory (n + 1))) := by
  unfold trajectoryMeasure
  exact Kernel.map_frestrictLe_trajMeasure_compProd_eq_map_trajMeasure
    (X := fun n : Nat => StochasticEpisodeBatch mdp (episodes n))
    (μ₀ := source.rewardSource.iidStochasticTrajectoryFamilyMeasure
      source.initialPolicy initialState (episodes 0))
    (κ := source.batchKernel) (a := n)

omit [DecidableEq State] [DecidableEq Action]
    [MeasurableSingletonClass State] [MeasurableSingletonClass Action]
    [Nonempty State] [Nonempty Action] in
/-- The regular conditional law of coordinate `n + 1` is its source kernel. -/
theorem trajectoryMeasure_condDistrib_nextBatch
    {mdp : MDP State Action} {initialState : Measure State}
    [IsProbabilityMeasure initialState] {episodes : Nat -> Nat}
    (source : HeterogeneousAdaptiveStochasticEpisodeBatchSource
      mdp initialState episodes) (n : Nat)
    [StandardBorelSpace (StochasticEpisodeBatch mdp (episodes (n + 1)))]
    [Nonempty (StochasticEpisodeBatch mdp (episodes (n + 1)))] :
    condDistrib (fun trajectory :
        HeterogeneousStochasticEpisodeBatchTrajectory mdp episodes =>
          trajectory (n + 1))
        (Preorder.frestrictLe n) source.trajectoryMeasure =ᵐ[
          source.trajectoryMeasure.map (Preorder.frestrictLe n)]
      source.batchKernel n := by
  unfold trajectoryMeasure
  exact Kernel.condDistrib_trajMeasure
    (X := fun n : Nat => StochasticEpisodeBatch mdp (episodes n))
    (κ := source.batchKernel)
    (μ₀ := source.rewardSource.iidStochasticTrajectoryFamilyMeasure
      source.initialPolicy initialState (episodes 0))
    (a := n)

omit [DecidableEq State] [DecidableEq Action]
    [MeasurableSingletonClass State] [MeasurableSingletonClass Action]
    [Nonempty State] [Nonempty Action] in
/-- Finite marginals of the causal law form a projective family. -/
theorem trajectoryMeasure_map_prefix_projective
    {mdp : MDP State Action} {initialState : Measure State}
    [IsProbabilityMeasure initialState] {episodes : Nat -> Nat}
    (source : HeterogeneousAdaptiveStochasticEpisodeBatchSource
      mdp initialState episodes) {m n : Nat} (hmn : m <= n) :
    (source.trajectoryMeasure.map (Preorder.frestrictLe n)).map
        (Preorder.frestrictLe₂
          (π := fun k : Nat => StochasticEpisodeBatch mdp (episodes k)) hmn) =
      source.trajectoryMeasure.map (Preorder.frestrictLe m) := by
  rw [Measure.map_map
    (Preorder.measurable_frestrictLe₂
      (X := fun k : Nat => StochasticEpisodeBatch mdp (episodes k)) hmn)
    (Preorder.measurable_frestrictLe n)]
  rfl

end HeterogeneousAdaptiveStochasticEpisodeBatchSource

namespace AdaptiveStochasticSampledEmpiricalOptimisticSource

/-- The latest batch in a dependent finite history. -/
def heterogeneousLatestBatch
    {mdp : MDP State Action} {episodes : Nat -> Nat} {n : Nat}
    (history : HeterogeneousStochasticEpisodeBatchPrefix mdp episodes n) :
    StochasticEpisodeBatch mdp (episodes n) :=
  history ⟨n, Finset.mem_Iic.mpr le_rfl⟩

omit [DecidableEq State] [DecidableEq Action]
    [MeasurableSingletonClass State] [MeasurableSingletonClass Action]
    [Nonempty State] [Nonempty Action] in
theorem measurable_heterogeneousLatestBatch
    {mdp : MDP State Action} {episodes : Nat -> Nat} {n : Nat} :
    Measurable
      (heterogeneousLatestBatch :
        HeterogeneousStochasticEpisodeBatchPrefix mdp episodes n ->
          StochasticEpisodeBatch mdp (episodes n)) :=
  measurable_pi_apply
    (⟨n, Finset.mem_Iic.mpr le_rfl⟩ : Finset.Iic n)

/-- The actual-sampled optimistic table selected from dependent history. -/
noncomputable def heterogeneousSuccessorTable
    {mdp : MDP State Action} {episodes : Nat -> Nat}
    (defaultState : State) (rewardBudget transitionBudget : Nat -> Real)
    (n : Nat)
    (history : HeterogeneousStochasticEpisodeBatchPrefix mdp episodes n) :
    DeterministicMarkovPolicyTable mdp :=
  (heterogeneousLatestBatch history).sampledEmpiricalOptimisticPolicyTable
    defaultState (rewardBudget n) (transitionBudget n)

theorem measurable_heterogeneousSuccessorTable
    {mdp : MDP State Action} {episodes : Nat -> Nat}
    (defaultState : State) (rewardBudget transitionBudget : Nat -> Real)
    (n : Nat) :
    Measurable
      (heterogeneousSuccessorTable (mdp := mdp) (episodes := episodes)
        defaultState rewardBudget transitionBudget n) :=
  (StochasticEpisodeBatch.measurable_sampledEmpiricalOptimisticPolicyTable
    defaultState (rewardBudget n) (transitionBudget n)).comp
      measurable_heterogeneousLatestBatch

/--
Actual-sampled exploratory source with coordinate-dependent batch sizes,
budgets, and exploration rates.
-/
noncomputable def heterogeneousExploratorySource
    (mdp : MDP State Action) (initialState : Measure State)
    [IsProbabilityMeasure initialState] (episodes : Nat -> Nat)
    (rewardSource : mdp.MeanCompatibleRewardKernel)
    (initialTable : DeterministicMarkovPolicyTable mdp)
    (defaultState : State) (rewardBudget transitionBudget : Nat -> Real)
    (explorationRate : Nat -> NNReal)
    (hexplorationRate : forall n, explorationRate n <= 1) :
    HeterogeneousAdaptiveStochasticEpisodeBatchSource
      mdp initialState episodes where
  rewardSource := rewardSource
  initialPolicy := initialTable.exploratoryPolicy
    (explorationRate 0) (hexplorationRate 0)
  successorPolicy n history :=
    (heterogeneousSuccessorTable defaultState rewardBudget transitionBudget
      n history).exploratoryPolicy
        (explorationRate (n + 1)) (hexplorationRate (n + 1))
  batchKernel n :=
    (DeterministicMarkovPolicyTable.exploratoryIIDStochasticEpisodeBatchKernel
      rewardSource initialState (episodes (n + 1))
        (explorationRate (n + 1)) (hexplorationRate (n + 1))).comap
      (heterogeneousSuccessorTable defaultState rewardBudget transitionBudget n)
      (measurable_heterogeneousSuccessorTable
        defaultState rewardBudget transitionBudget n)
  batchKernel_isMarkov n := by
    exact Kernel.IsMarkovKernel.comap _
      (measurable_heterogeneousSuccessorTable
        defaultState rewardBudget transitionBudget n)
  batchKernel_eq_iidStochasticTrajectoryFamilyMeasure n history := by
    rw [Kernel.comap_apply]
    rfl
  measurable_successorSampledReturnDeviation n := by
    exact
      AdaptiveStochasticEmpiricalOptimisticSource.measurable_selectedExploratorySampledReturnDeviation
        (heterogeneousSuccessorTable defaultState rewardBudget transitionBudget n)
        (measurable_heterogeneousSuccessorTable
          defaultState rewardBudget transitionBudget n)
        (explorationRate (n + 1)) (hexplorationRate (n + 1))

/-- The genuinely causal round-varying self-consistent scheduled source. -/
noncomputable def selfConsistentScheduledCausalSource
    (mdp : MDP State Action) (initialState : Measure State)
    [IsProbabilityMeasure initialState]
    (rewardSource : mdp.MeanCompatibleRewardKernel)
    (initialTable : DeterministicMarkovPolicyTable mdp)
    (defaultState : State) (varianceProxy : NNReal)
    (baseVisitFloor : Real) :
    HeterogeneousAdaptiveStochasticEpisodeBatchSource mdp initialState
      (fun n =>
        AdaptiveStochasticEpisodeBatchSource.selfConsistentScheduledEpisodes
          mdp varianceProxy baseVisitFloor n) :=
  heterogeneousExploratorySource mdp initialState
    (fun n =>
      AdaptiveStochasticEpisodeBatchSource.selfConsistentScheduledEpisodes
        mdp varianceProxy baseVisitFloor n)
    rewardSource initialTable defaultState
    (fun n =>
      AdaptiveStochasticEpisodeBatchSource.selfConsistentScheduledRewardBudget
        mdp varianceProxy baseVisitFloor n)
    (fun n =>
      AdaptiveStochasticEpisodeBatchSource.selfConsistentScheduledTransitionBudget
        mdp varianceProxy baseVisitFloor n)
    AdaptiveEpisodeBatchSource.decayingExplorationRate
    AdaptiveEpisodeBatchSource.decayingExplorationRate_le_one

/-
The theorem deliberately identifies this source as a new causal algorithm.
It does not equate any prefix marginal with the old constant-parameter window
laws, whose coordinate types and step kernels differ.
-/
/-- Exact conditional and projective laws of the self-consistent causal source. -/
theorem selfConsistentScheduledCausalSource_trajectoryMeasure_exactLaws_and_projective
    (mdp : MDP State Action) (initialState : Measure State)
    [IsProbabilityMeasure initialState]
    [StandardBorelSpace State] [StandardBorelSpace Action]
    (rewardSource : mdp.MeanCompatibleRewardKernel)
    (initialTable : DeterministicMarkovPolicyTable mdp)
    (defaultState : State) (varianceProxy : NNReal)
    (baseVisitFloor : Real) :
    let episodes := fun n =>
      AdaptiveStochasticEpisodeBatchSource.selfConsistentScheduledEpisodes
        mdp varianceProxy baseVisitFloor n
    let source := selfConsistentScheduledCausalSource mdp initialState
      rewardSource initialTable defaultState varianceProxy baseVisitFloor
    source.trajectoryMeasure.map (Function.eval 0) =
        rewardSource.iidStochasticTrajectoryFamilyMeasure
          (initialTable.exploratoryPolicy
            (AdaptiveEpisodeBatchSource.decayingExplorationRate 0)
            (AdaptiveEpisodeBatchSource.decayingExplorationRate_le_one 0))
          initialState (episodes 0) /\
      (forall n history,
        source.batchKernel n history =
          rewardSource.iidStochasticTrajectoryFamilyMeasure
            ((heterogeneousSuccessorTable defaultState
              (fun k =>
                AdaptiveStochasticEpisodeBatchSource.selfConsistentScheduledRewardBudget
                  mdp varianceProxy baseVisitFloor k)
              (fun k =>
                AdaptiveStochasticEpisodeBatchSource.selfConsistentScheduledTransitionBudget
                  mdp varianceProxy baseVisitFloor k)
              n history).exploratoryPolicy
                (AdaptiveEpisodeBatchSource.decayingExplorationRate (n + 1))
                (AdaptiveEpisodeBatchSource.decayingExplorationRate_le_one
                  (n + 1)))
            initialState (episodes (n + 1))) /\
      (forall n,
        condDistrib
            (fun trajectory :
              HeterogeneousStochasticEpisodeBatchTrajectory mdp episodes =>
                trajectory (n + 1))
            (Preorder.frestrictLe n) source.trajectoryMeasure =ᵐ[
              source.trajectoryMeasure.map (Preorder.frestrictLe n)]
          source.batchKernel n) /\
      (forall n,
        source.trajectoryMeasure.map (Preorder.frestrictLe n) ⊗ₘ
            source.batchKernel n =
          source.trajectoryMeasure.map
            (fun trajectory =>
              (Preorder.frestrictLe n trajectory, trajectory (n + 1)))) /\
      (forall m n (hmn : m <= n),
        (source.trajectoryMeasure.map (Preorder.frestrictLe n)).map
            (Preorder.frestrictLe₂
              (π := fun k : Nat => StochasticEpisodeBatch mdp (episodes k))
              hmn) =
          source.trajectoryMeasure.map (Preorder.frestrictLe m)) := by
  dsimp only
  let source := selfConsistentScheduledCausalSource mdp initialState
    rewardSource initialTable defaultState varianceProxy baseVisitFloor
  refine ⟨source.trajectoryMeasure_map_eval_zero, ?_, ?_, ?_, ?_⟩
  · intro n history
    exact source.batchKernel_eq_iidStochasticTrajectoryFamilyMeasure n history
  · intro n
    exact source.trajectoryMeasure_condDistrib_nextBatch n
  · intro n
    exact source.trajectoryMeasure_prefix_compProd n
  · intro m n hmn
    exact source.trajectoryMeasure_map_prefix_projective hmn

end AdaptiveStochasticSampledEmpiricalOptimisticSource

end BanditRLProof.FiniteHorizonRL
