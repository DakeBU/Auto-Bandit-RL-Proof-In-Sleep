import BanditRLProof.RL.FiniteHorizonAdaptiveEpisodeBatchLaw

/-!
# Adaptive empirical-transition optimistic batch source

This module constructs the measurable source left abstract by
`FiniteHorizonAdaptiveEpisodeBatchLaw`.  Every observed batch is compressed to
its finite family of transition counts.  Those counts define a normalized
empirical transition kernel, which is combined with the known deterministic
MDP reward and a fixed transition bonus.  The resulting optimistic action
table is a measurable function of the batch because the count-summary space is
countable with measurable singletons.

The table-indexed iid batch laws form a Markov kernel by
`Kernel.ofFunOfCountable`.  Comapping that kernel along the measurable
history-to-table selector gives an `AdaptiveEpisodeBatchSource` with the exact
selected-policy law by construction.  The final theorem therefore exposes the
adaptive simultaneous count-confidence conclusion without a caller-supplied
kernel law or selected-event measurability proof.

This route uses only the most recently observed batch, known rewards, and a
fixed transition bonus.  It does not yet prove that the empirical plan is
confident, sum bonuses across rounds, or identify cumulative online regret.
-/

open MeasureTheory
open scoped ENNReal ProbabilityTheory

universe u v

namespace BanditRLProof
namespace FiniteHorizonRL

variable {State : Type u} {Action : Type v}
    [MeasurableSpace State] [MeasurableSpace Action]
    [Fintype State] [Fintype Action]
    [DecidableEq State] [DecidableEq Action]
    [MeasurableSingletonClass State] [MeasurableSingletonClass Action]
    [Nonempty State] [Nonempty Action]

/-- All stage/state/action/next-state transition counts from one batch. -/
abbrev TransitionCountSummary (mdp : MDP State Action) :=
  Fin mdp.horizon -> State -> Action -> State -> Nat

namespace EpisodeBatch

/-- Compress an episode batch to the transition counts used by the planner. -/
def transitionCountSummary
    {mdp : MDP State Action} {episodes : Nat}
    (batch : EpisodeBatch mdp episodes) : TransitionCountSummary mdp :=
  fun stage state action nextState =>
    batch.transitionCount stage state action nextState

omit [Nonempty State] [Nonempty Action] in
/-- The complete transition-count summary is measurable. -/
theorem measurable_transitionCountSummary
    {mdp : MDP State Action} {episodes : Nat} :
    Measurable
      (transitionCountSummary :
        EpisodeBatch mdp episodes -> TransitionCountSummary mdp) := by
  refine measurable_pi_lambda _ fun stage => ?_
  refine measurable_pi_lambda _ fun state => ?_
  refine measurable_pi_lambda _ fun action => ?_
  refine measurable_pi_lambda _ fun nextState => ?_
  apply (MeasurableEmbedding.natCast (α := Real)).measurable_comp_iff.mp
  simpa [Function.comp_def, transitionCountSummary] using
    (MarkovPolicy.measurable_cast_transitionCount
      (episodes := episodes) stage state action nextState)

end EpisodeBatch

namespace TransitionCountSummary

/-- Total visits represented by one state-action transition-count row. -/
def visitCount {mdp : MDP State Action}
    (summary : TransitionCountSummary mdp) (stage : Fin mdp.horizon)
    (state : State) (action : Action) : Nat :=
  ∑ nextState, summary stage state action nextState

/-- Normalized empirical transition PMF, with an explicit zero-count fallback. -/
noncomputable def empiricalTransitionPMF
    {mdp : MDP State Action} (summary : TransitionCountSummary mdp)
    (defaultState : State) (stage : Fin mdp.horizon)
    (state : State) (action : Action) : PMF State :=
  if hzero : summary.visitCount stage state action = 0 then
    PMF.pure defaultState
  else
    PMF.ofFintype
      (fun nextState =>
        (summary stage state action nextState : ENNReal) /
          (summary.visitCount stage state action : ENNReal))
      (by
        have sum_div_visitCount (states : Finset State) :
            (∑ nextState ∈ states,
                (summary stage state action nextState : ENNReal) /
                  (summary.visitCount stage state action : ENNReal)) =
              (∑ nextState ∈ states,
                  (summary stage state action nextState : ENNReal)) /
                (summary.visitCount stage state action : ENNReal) := by
          classical
          induction states using Finset.induction_on with
          | empty => simp
          | @insert nextState states hnext ih =>
              simp only [Finset.sum_insert hnext]
              rw [ih, ENNReal.add_div]
        calc
          (∑ nextState,
              (summary stage state action nextState : ENNReal) /
                (summary.visitCount stage state action : ENNReal)) =
              (∑ nextState,
                (summary stage state action nextState : ENNReal)) /
                  (summary.visitCount stage state action : ENNReal) := by
            simpa using sum_div_visitCount (Finset.univ : Finset State)
          _ = (summary.visitCount stage state action : ENNReal) /
                (summary.visitCount stage state action : ENNReal) := by
            congr 1
            simp [visitCount]
          _ = 1 :=
            ENNReal.div_self (by exact_mod_cast hzero)
              (ENNReal.natCast_ne_top _))

/-- The summary-indexed empirical transition kernel. -/
noncomputable def empiricalTransitionKernel
    {mdp : MDP State Action} (summary : TransitionCountSummary mdp)
    (defaultState : State) (stage : Fin mdp.horizon) :
    ProbabilityTheory.Kernel (State × Action) State :=
  ProbabilityTheory.Kernel.ofFunOfCountable fun pair =>
    (summary.empiricalTransitionPMF defaultState stage pair.1 pair.2).toMeasure

omit [DecidableEq Action] [Nonempty State] [Nonempty Action] in
theorem empiricalTransitionKernel_isMarkov
    {mdp : MDP State Action} (summary : TransitionCountSummary mdp)
    (defaultState : State) (stage : Fin mdp.horizon) :
    ProbabilityTheory.IsMarkovKernel
      (summary.empiricalTransitionKernel defaultState stage) where
  isProbabilityMeasure pair := by
    change IsProbabilityMeasure
      ((summary.empiricalTransitionPMF defaultState stage pair.1 pair.2).toMeasure)
    infer_instance

/--
Known-reward empirical-transition plan with zero reward radius and one fixed
transition bonus at every coordinate.
-/
noncomputable def optimisticPlan
    (mdp : MDP State Action) (summary : TransitionCountSummary mdp)
    (defaultState : State) (transitionBonus : Real) :
    mdp.EstimatedModelPlan where
  estimatedReward _stage := mdp.reward
  measurable_estimatedReward _stage := mdp.measurable_reward
  estimatedTransition stage := summary.empiricalTransitionKernel defaultState stage
  estimatedTransition_isMarkov stage :=
    summary.empiricalTransitionKernel_isMarkov defaultState stage
  rewardRadius _stage _state _action := 0
  measurable_rewardRadius _stage := measurable_const
  transitionRadius _stage _state _action := transitionBonus
  measurable_transitionRadius _stage := measurable_const

end TransitionCountSummary

/-- A deterministic action choice at every stage and state. -/
abbrev DeterministicMarkovPolicyTable (mdp : MDP State Action) :=
  Fin mdp.horizon -> State -> Action

namespace DeterministicMarkovPolicyTable

/-- Interpret a deterministic action table as a Markov policy. -/
noncomputable def toMarkovPolicy
    {mdp : MDP State Action} (table : DeterministicMarkovPolicyTable mdp) :
    MarkovPolicy mdp where
  actionKernel stage :=
    ProbabilityTheory.Kernel.deterministic (table stage) (measurable_of_finite _)
  actionKernel_isMarkov _stage := by infer_instance

end DeterministicMarkovPolicyTable

namespace TransitionCountSummary

/-- The deterministic optimistic action table computed from a count summary. -/
noncomputable def optimisticPolicyTable
    (mdp : MDP State Action) (summary : TransitionCountSummary mdp)
    (defaultState : State) (transitionBonus : Real) :
    DeterministicMarkovPolicyTable mdp :=
  fun stage =>
    (summary.optimisticPlan mdp defaultState transitionBonus).optimisticActionAt stage

omit [DecidableEq Action] [Nonempty State] in
/-- The action-table interpretation is exactly the plan's optimistic policy. -/
theorem optimisticPolicyTable_toMarkovPolicy
    (mdp : MDP State Action) (summary : TransitionCountSummary mdp)
    (defaultState : State) (transitionBonus : Real) :
    (summary.optimisticPolicyTable mdp defaultState transitionBonus).toMarkovPolicy =
      (summary.optimisticPlan mdp defaultState transitionBonus).optimisticPolicy := by
  rfl

end TransitionCountSummary

namespace EpisodeBatch

/-- The empirical optimistic action table computed from one observed batch. -/
noncomputable def empiricalOptimisticPolicyTable
    {mdp : MDP State Action} {episodes : Nat}
    (batch : EpisodeBatch mdp episodes) (defaultState : State)
    (transitionBonus : Real) : DeterministicMarkovPolicyTable mdp :=
  batch.transitionCountSummary.optimisticPolicyTable
    mdp defaultState transitionBonus

omit [Nonempty State] in
/-- The empirical optimistic table is measurable in the raw batch. -/
theorem measurable_empiricalOptimisticPolicyTable
    {mdp : MDP State Action} {episodes : Nat} (defaultState : State)
    (transitionBonus : Real) :
    Measurable fun batch : EpisodeBatch mdp episodes =>
      batch.empiricalOptimisticPolicyTable defaultState transitionBonus := by
  exact
    (measurable_of_countable
      (fun summary : TransitionCountSummary mdp =>
        summary.optimisticPolicyTable mdp defaultState transitionBonus)).comp
      measurable_transitionCountSummary

end EpisodeBatch

namespace DeterministicMarkovPolicyTable

/-- Iid generated episode-batch law indexed by a deterministic policy table. -/
noncomputable def iidEpisodeBatchKernel
    {mdp : MDP State Action} (initialState : Measure State)
    [IsProbabilityMeasure initialState] (episodes : Nat) :
    ProbabilityTheory.Kernel (DeterministicMarkovPolicyTable mdp)
      (EpisodeBatch mdp episodes) :=
  ProbabilityTheory.Kernel.ofFunOfCountable fun table =>
    table.toMarkovPolicy.iidEpisodeBatchMeasure initialState episodes

omit [DecidableEq State] [DecidableEq Action]
    [Nonempty State] [Nonempty Action] in
@[simp]
theorem iidEpisodeBatchKernel_apply
    {mdp : MDP State Action} (initialState : Measure State)
    [IsProbabilityMeasure initialState] (episodes : Nat)
    (table : DeterministicMarkovPolicyTable mdp) :
    iidEpisodeBatchKernel initialState episodes table =
      table.toMarkovPolicy.iidEpisodeBatchMeasure initialState episodes :=
  rfl

instance instIIDEpisodeBatchKernelIsMarkov
    {mdp : MDP State Action} (initialState : Measure State)
    [IsProbabilityMeasure initialState] (episodes : Nat) :
    ProbabilityTheory.IsMarkovKernel
      (iidEpisodeBatchKernel (mdp := mdp) initialState episodes) where
  isProbabilityMeasure table := by
    rw [iidEpisodeBatchKernel_apply]
    infer_instance

end DeterministicMarkovPolicyTable

namespace AdaptiveEmpiricalOptimisticSource

/-- The latest observed batch in a finite nonempty prefix. -/
def latestBatch
    {mdp : MDP State Action} {episodes n : Nat}
    (history : EpisodeBatchPrefix mdp episodes n) : EpisodeBatch mdp episodes :=
  history (⟨n, Finset.mem_Iic.mpr le_rfl⟩ : Finset.Iic n)

omit [DecidableEq State] [DecidableEq Action]
    [MeasurableSingletonClass State] [MeasurableSingletonClass Action]
    [Nonempty State] [Nonempty Action] in
theorem measurable_latestBatch
    {mdp : MDP State Action} {episodes n : Nat} :
    Measurable
      (latestBatch : EpisodeBatchPrefix mdp episodes n -> EpisodeBatch mdp episodes) :=
  measurable_pi_apply (⟨n, Finset.mem_Iic.mpr le_rfl⟩ : Finset.Iic n)

/-- Optimistic table selected from the latest batch in a finite prefix. -/
noncomputable def successorTable
    {mdp : MDP State Action} {episodes : Nat} (defaultState : State)
    (transitionBonus : Real) (n : Nat)
    (history : EpisodeBatchPrefix mdp episodes n) :
    DeterministicMarkovPolicyTable mdp :=
  (latestBatch history).empiricalOptimisticPolicyTable
    defaultState transitionBonus

omit [Nonempty State] in
theorem measurable_successorTable
    {mdp : MDP State Action} {episodes : Nat} (defaultState : State)
    (transitionBonus : Real) (n : Nat) :
    Measurable
      (successorTable (mdp := mdp) (episodes := episodes)
        defaultState transitionBonus n) :=
  (EpisodeBatch.measurable_empiricalOptimisticPolicyTable
      defaultState transitionBonus).comp measurable_latestBatch

/--
Concrete adaptive source: after every batch, recompute the known-reward
empirical-transition optimistic table from that batch and sample the next iid
batch under the selected deterministic policy.
-/
noncomputable def source
    (mdp : MDP State Action) (initialState : Measure State)
    [IsProbabilityMeasure initialState] (episodes : Nat)
    (initialTable : DeterministicMarkovPolicyTable mdp)
    (defaultState : State) (transitionBonus : Real) :
    AdaptiveEpisodeBatchSource mdp initialState episodes where
  initialPolicy := initialTable.toMarkovPolicy
  successorPolicy n history :=
    (successorTable defaultState transitionBonus n history).toMarkovPolicy
  batchKernel n :=
    (DeterministicMarkovPolicyTable.iidEpisodeBatchKernel
      initialState episodes).comap
        (successorTable defaultState transitionBonus n)
        (measurable_successorTable defaultState transitionBonus n)
  batchKernel_isMarkov n := by
    exact ProbabilityTheory.Kernel.IsMarkovKernel.comap _
      (measurable_successorTable defaultState transitionBonus n)
  batchKernel_eq_iidEpisodeBatchMeasure n history := by
    rw [ProbabilityTheory.Kernel.comap_apply]
    rfl

omit [Nonempty State] in
/-- The selected policy is exactly the latest batch's optimistic plan policy. -/
theorem source_successorPolicy_eq_optimisticPolicy
    {mdp : MDP State Action} {initialState : Measure State}
    [IsProbabilityMeasure initialState] {episodes : Nat}
    (initialTable : DeterministicMarkovPolicyTable mdp)
    (defaultState : State) (transitionBonus : Real) (n : Nat)
    (history : EpisodeBatchPrefix mdp episodes n) :
    (source mdp initialState episodes initialTable defaultState transitionBonus).successorPolicy
        n history =
      ((latestBatch history).transitionCountSummary.optimisticPlan
        mdp defaultState transitionBonus).optimisticPolicy := by
  exact TransitionCountSummary.optimisticPolicyTable_toMarkovPolicy
    mdp (latestBatch history).transitionCountSummary defaultState transitionBonus

omit [Nonempty State] [Nonempty Action] in
/--
Measurability of a selected count event for any measurable finite policy-table
selector.  This discharges the regularity premise of the adaptive union route.
-/
theorem measurableSet_selectedSimultaneousCountBadEvent
    {mdp : MDP State Action} {initialState : Measure State}
    [IsProbabilityMeasure initialState] {episodes : Nat}
    {History : Type*} [MeasurableSpace History]
    (selector : History -> DeterministicMarkovPolicyTable mdp)
    (hselector : Measurable selector) (delta : Real) :
    MeasurableSet
      {pair : History × EpisodeBatch mdp episodes |
        pair.2 ∈ (selector pair.1).toMarkovPolicy.simultaneousCountBadEvent
          initialState episodes delta} := by
  rw [show
      {pair : History × EpisodeBatch mdp episodes |
          pair.2 ∈ (selector pair.1).toMarkovPolicy.simultaneousCountBadEvent
            initialState episodes delta} =
        ⋃ table : DeterministicMarkovPolicyTable mdp,
          (selector ⁻¹' {table}) ×ˢ
            table.toMarkovPolicy.simultaneousCountBadEvent
              initialState episodes delta by
    ext pair
    simp]
  exact MeasurableSet.iUnion fun table =>
    (hselector (measurableSet_singleton table)).prod
      (table.toMarkovPolicy.measurableSet_simultaneousCountBadEvent
        initialState episodes delta)

omit [Nonempty State] in
/-- Every selected successor count event of the concrete source is measurable. -/
theorem source_measurableSet_successorSimultaneousCountBadEvent
    {mdp : MDP State Action} {initialState : Measure State}
    [IsProbabilityMeasure initialState] {episodes : Nat}
    (initialTable : DeterministicMarkovPolicyTable mdp)
    (defaultState : State) (transitionBonus : Real)
    (rounds : Nat) (delta : Real) (n : Nat) :
    MeasurableSet
      (AdaptiveEpisodeBatchSource.successorSimultaneousCountBadEvent
        (source mdp initialState episodes initialTable defaultState transitionBonus)
        rounds delta n) := by
  change MeasurableSet
    {pair : EpisodeBatchPrefix mdp episodes n × EpisodeBatch mdp episodes |
      pair.2 ∈
        MarkovPolicy.simultaneousCountBadEvent
          (successorTable defaultState transitionBonus n pair.1).toMarkovPolicy
          initialState episodes (multiBatchLocalDelta rounds delta)}
  exact measurableSet_selectedSimultaneousCountBadEvent
    (successorTable defaultState transitionBonus n)
    (measurable_successorTable defaultState transitionBonus n)
    (multiBatchLocalDelta rounds delta)

/-- The concrete source's next-batch conditional law is its latest empirical optimistic policy law. -/
theorem source_trajectoryMeasure_condDistrib_eq_empiricalOptimisticPolicyBatchLaw
    {mdp : MDP State Action} {initialState : Measure State}
    [IsProbabilityMeasure initialState] {episodes : Nat}
    [StandardBorelSpace (EpisodeBatch mdp episodes)]
    (initialTable : DeterministicMarkovPolicyTable mdp)
    (defaultState : State) (transitionBonus : Real) (n : Nat) :
    let concreteSource :=
      source mdp initialState episodes initialTable defaultState transitionBonus
    Filter.EventuallyEq
      (ae (concreteSource.trajectoryMeasure.map (Preorder.frestrictLe n)))
      (ProbabilityTheory.condDistrib
        (fun trajectory : EpisodeBatchTrajectory mdp episodes =>
          trajectory (n + 1))
        (Preorder.frestrictLe n) concreteSource.trajectoryMeasure)
      (fun history =>
        MarkovPolicy.iidEpisodeBatchMeasure
          ((latestBatch history).transitionCountSummary.optimisticPlan
            mdp defaultState transitionBonus).optimisticPolicy
          initialState episodes) := by
  dsimp only
  filter_upwards [
    AdaptiveEpisodeBatchSource.trajectoryMeasure_condDistrib_eq_iidEpisodeBatchMeasure
        (source mdp initialState episodes initialTable defaultState transitionBonus) n]
      with history hhistory
  rw [hhistory]
  congr 1

omit [Nonempty State] in
/--
Concrete adaptive count-confidence terminal for the empirical optimistic
source.  No selected-law or successor-event measurability premise remains.
-/
theorem source_trajectoryMeasure_adaptiveSimultaneousCountConfidence
    {mdp : MDP State Action} {initialState : Measure State}
    [IsProbabilityMeasure initialState] {episodes : Nat}
    (initialTable : DeterministicMarkovPolicyTable mdp)
    (defaultState : State) (transitionBonus : Real)
    (rounds : Nat) (hrounds : 0 < rounds)
    (hepisodes : 0 < episodes) (delta : Real) (hdelta : 0 < delta)
    (hdelta_le_one : delta <= 1) :
    let concreteSource :=
      source mdp initialState episodes initialTable defaultState transitionBonus
    MeasurableSet
        (concreteSource.adaptiveSimultaneousCountBadEvent rounds delta) ∧
      concreteSource.trajectoryMeasure
          (concreteSource.adaptiveSimultaneousCountBadEvent rounds delta) <=
        ENNReal.ofReal delta ∧
      forall trajectory,
        trajectory ∉ concreteSource.adaptiveSimultaneousCountBadEvent rounds delta ->
        forall round : Fin rounds, forall coordinate : CountCoordinate mdp,
          |coordinate.deviation (concreteSource.policyAt trajectory round)
              initialState (trajectory round)| <
            simultaneousCountConfidenceRadius mdp episodes
              (multiBatchLocalDelta rounds delta) := by
  dsimp only
  exact AdaptiveEpisodeBatchSource.trajectoryMeasure_adaptiveSimultaneousCountConfidence
      (source mdp initialState episodes initialTable defaultState transitionBonus)
      rounds hrounds hepisodes delta hdelta hdelta_le_one
      (fun n _hn =>
        source_measurableSet_successorSimultaneousCountBadEvent
          initialTable defaultState transitionBonus rounds delta n)

end AdaptiveEmpiricalOptimisticSource
end FiniteHorizonRL
end BanditRLProof
