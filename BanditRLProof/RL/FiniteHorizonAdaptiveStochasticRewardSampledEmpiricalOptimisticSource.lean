import BanditRLProof.RL.FiniteHorizonAdaptiveStochasticRewardEmpiricalOptimisticProjection
import BanditRLProof.RL.FiniteHorizonStochasticRewardIIDAllCoordinateEmpiricalModelConfidence
import Mathlib.Probability.Kernel.MeasurableIntegral

/-!
# Adaptive sampled-reward empirical optimistic source

This module constructs a genuinely sampled-reward adaptive optimistic source.
The successor table is computed from the latest complete stochastic batch,
including its observed rewards, rather than from the known-mean projection.

The main regularity obligation is measurability of the finite-horizon dynamic
program as a function of the sampled batch.  The explicit finite argmax and a
batch-indexed empirical transition kernel discharge that obligation.  The
resulting source has the exact selected-policy iid stochastic batch law in
every history fiber by construction.
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

namespace EpisodeBatch

omit [Nonempty State] [Nonempty Action] in
/-- A fixed sampled-reward sum is measurable on raw episode batches. -/
theorem measurable_rewardSum
    {mdp : MDP State Action} {episodes : Nat}
    (stage : Fin mdp.horizon) (state : State) (action : Action) :
    Measurable fun batch : EpisodeBatch mdp episodes =>
      batch.rewardSum stage state action := by
  classical
  refine Finset.measurable_sum Finset.univ fun episode _ => ?_
  let step : EpisodeBatch mdp episodes -> EpisodeStep State Action :=
    fun batch => batch episode stage
  have hstep : Measurable step :=
    (measurable_pi_apply stage).comp (measurable_pi_apply episode)
  have hstate : Measurable fun batch : EpisodeBatch mdp episodes =>
      (step batch).state := EpisodeStep.measurable_state.comp hstep
  have haction : Measurable fun batch : EpisodeBatch mdp episodes =>
      (step batch).action := EpisodeStep.measurable_action.comp hstep
  have hreward : Measurable fun batch : EpisodeBatch mdp episodes =>
      (step batch).reward := EpisodeStep.measurable_reward.comp hstep
  exact Measurable.ite
    ((measurableSet_eq_fun hstate measurable_const).inter
      (measurableSet_eq_fun haction measurable_const))
    hreward measurable_const

omit [Nonempty State] [Nonempty Action] in
/-- A fixed empirical sampled-reward mean is measurable on raw batches. -/
theorem measurable_empiricalReward
    {mdp : MDP State Action} {episodes : Nat}
    (stage : Fin mdp.horizon) (state : State) (action : Action) :
    Measurable fun batch : EpisodeBatch mdp episodes =>
      batch.empiricalReward stage state action := by
  exact (measurable_rewardSum stage state action).div
    (MarkovPolicy.measurable_cast_visitCount
      (episodes := episodes) stage state action)

end EpisodeBatch

namespace TransitionCountSummary

/-- A fixed empirical next-state law as a kernel in the count summary. -/
noncomputable def stateKernel
    {mdp : MDP State Action} (defaultState : State)
    (stage : Fin mdp.horizon) (state : State) (action : Action) :
    ProbabilityTheory.Kernel (TransitionCountSummary mdp) State :=
  ProbabilityTheory.Kernel.ofFunOfCountable fun summary =>
    summary.empiricalTransitionKernel defaultState stage (state, action)

omit [DecidableEq Action] [Nonempty State] in
instance instStateKernelIsMarkov
    {mdp : MDP State Action} (defaultState : State)
    (stage : Fin mdp.horizon) (state : State) (action : Action) :
    ProbabilityTheory.IsMarkovKernel
      (stateKernel (mdp := mdp) defaultState stage state action) where
  isProbabilityMeasure summary := by
    change IsProbabilityMeasure
      (summary.empiricalTransitionKernel defaultState stage (state, action))
    letI : ProbabilityTheory.IsMarkovKernel
        (summary.empiricalTransitionKernel defaultState stage) :=
      summary.empiricalTransitionKernel_isMarkov defaultState stage
    infer_instance

end TransitionCountSummary

namespace EpisodeBatch

/-- The raw-batch empirical next-state law as a Markov kernel in the batch. -/
noncomputable def empiricalTransitionStateKernel
    {mdp : MDP State Action} {episodes : Nat} (defaultState : State)
    (stage : Fin mdp.horizon) (state : State) (action : Action) :
    ProbabilityTheory.Kernel (EpisodeBatch mdp episodes) State :=
  (TransitionCountSummary.stateKernel
      (mdp := mdp) defaultState stage state action).comap
    transitionCountSummary measurable_transitionCountSummary

omit [Nonempty State] [Nonempty Action] in
instance instEmpiricalTransitionStateKernelIsMarkov
    {mdp : MDP State Action} {episodes : Nat} (defaultState : State)
    (stage : Fin mdp.horizon) (state : State) (action : Action) :
    ProbabilityTheory.IsMarkovKernel
      (empiricalTransitionStateKernel (episodes := episodes)
        defaultState stage state action) := by
  exact ProbabilityTheory.Kernel.IsMarkovKernel.comap _
    measurable_transitionCountSummary

omit [Nonempty State] [Nonempty Action] in
@[simp]
theorem empiricalTransitionStateKernel_apply
    {mdp : MDP State Action} {episodes : Nat}
    (batch : EpisodeBatch mdp episodes) (defaultState : State)
    (stage : Fin mdp.horizon) (state : State) (action : Action) :
    empiricalTransitionStateKernel (episodes := episodes)
        defaultState stage state action batch =
      batch.empiricalTransitionKernel defaultState stage (state, action) := by
  rw [empiricalTransitionStateKernel,
    ProbabilityTheory.Kernel.comap_apply]
  change
    (batch.transitionCountSummary.empiricalTransitionPMF
      defaultState stage state action).toMeasure =
        (batch.empiricalTransitionPMF
          defaultState stage state action).toMeasure
  rw [batch.transitionCountSummary_empiricalTransitionPMF]

omit [Nonempty State] [Nonempty Action] in
/-- Finite-state coordinatewise measurability yields joint measurability. -/
theorem measurable_uncurry_of_forall_measurable
    {Omega : Type*} [MeasurableSpace Omega]
    (value : Omega -> State -> Real)
    (hvalue : forall nextState : State,
      Measurable fun omega => value omega nextState) :
    Measurable (Function.uncurry value) := by
  classical
  have hsum : Measurable fun pair : Omega × State =>
      ∑ nextState : State,
        if pair.2 = nextState then value pair.1 nextState else 0 := by
    refine Finset.measurable_sum Finset.univ fun nextState _ => ?_
    exact Measurable.ite
      (measurableSet_eq_fun measurable_snd measurable_const)
      ((hvalue nextState).comp measurable_fst) measurable_const
  convert hsum using 1
  funext pair
  simp [Function.uncurry]

omit [Nonempty State] [Nonempty Action] in
/--
The empirical transition integral is measurable when every continuation-value
coordinate is measurable in the same raw batch.
-/
theorem measurable_empiricalTransitionValue
    {mdp : MDP State Action} {episodes : Nat}
    (defaultState : State) (stage : Fin mdp.horizon)
    (state : State) (action : Action)
    (value : EpisodeBatch mdp episodes -> State -> Real)
    (hvalue : forall nextState : State,
      Measurable fun batch => value batch nextState) :
    Measurable fun batch : EpisodeBatch mdp episodes =>
      ∫ nextState, value batch nextState
        ∂batch.empiricalTransitionKernel defaultState stage (state, action) := by
  have hjoint : Measurable (Function.uncurry value) :=
    measurable_uncurry_of_forall_measurable value hvalue
  have hintegral :=
    hjoint.stronglyMeasurable.integral_kernel_prod_right
      (κ := empiricalTransitionStateKernel
        (episodes := episodes) defaultState stage state action)
  simpa only [empiricalTransitionStateKernel_apply] using hintegral.measurable

end EpisodeBatch

namespace MDP

omit [Nonempty State] [Nonempty Action] in
/-- Every sampled empirical optimistic action-value coordinate is measurable. -/
theorem measurable_stochasticAllCoordinateEmpiricalOptimisticQ
    (mdp : MDP State Action) (episodes : Nat)
    (defaultState : State) (rewardBudget transitionBudget : Real)
    (stage : Fin mdp.horizon) (state : State) (action : Action)
    (value : EpisodeBatch mdp episodes -> State -> Real)
    (hvalue : forall nextState : State,
      Measurable fun batch => value batch nextState) :
    Measurable fun batch : EpisodeBatch mdp episodes =>
      let model := mdp.stochasticAllCoordinateEmpiricalFiniteBatchModel
        episodes batch defaultState rewardBudget transitionBudget
      model.plan.optimisticQ stage (value batch) state action := by
  have hreward := EpisodeBatch.measurable_empiricalReward
    (episodes := episodes) stage state action
  have htransition := EpisodeBatch.measurable_empiricalTransitionValue
    (episodes := episodes) defaultState stage state action value hvalue
  simpa [stochasticAllCoordinateEmpiricalFiniteBatchModel,
    FiniteBatchModel.plan, EstimatedModelPlan.optimisticQ,
    EstimatedModelPlan.bellmanQ, EstimatedModelPlan.transitionValue] using
      (((hreward.add htransition).add measurable_const).add measurable_const)

omit [Nonempty State] in
/-- The sampled empirical optimistic value recursion is batch-measurable. -/
theorem measurable_stochasticAllCoordinateEmpiricalUpperValueRemaining
    (mdp : MDP State Action) (episodes : Nat)
    (defaultState : State) (rewardBudget transitionBudget : Real) :
    forall (remaining : Nat) (hremaining : remaining <= mdp.horizon)
      (state : State),
      Measurable fun batch : EpisodeBatch mdp episodes =>
        let model := mdp.stochasticAllCoordinateEmpiricalFiniteBatchModel
          episodes batch defaultState rewardBudget transitionBudget
        model.plan.upperValueRemaining remaining hremaining state
  | 0, _hremaining, state => by
      simp [EstimatedModelPlan.upperValueRemaining]
  | remaining + 1, hremaining, state => by
      let stage := mdp.decisionStageRemaining remaining hremaining
      let value := fun batch : EpisodeBatch mdp episodes =>
        let model := mdp.stochasticAllCoordinateEmpiricalFiniteBatchModel
          episodes batch defaultState rewardBudget transitionBudget
        model.plan.upperValueRemaining remaining (by omega)
      have hvalue : forall nextState : State,
          Measurable fun batch => value batch nextState := by
        intro nextState
        exact measurable_stochasticAllCoordinateEmpiricalUpperValueRemaining
          mdp episodes defaultState rewardBudget transitionBudget
            remaining (by omega) nextState
      let scores := fun batch : EpisodeBatch mdp episodes => fun action : Action =>
        let model := mdp.stochasticAllCoordinateEmpiricalFiniteBatchModel
          episodes batch defaultState rewardBudget transitionBudget
        model.plan.optimisticQ stage (value batch) state action
      have hscores : forall action : Action,
          Measurable fun batch => scores batch action := by
        intro action
        exact mdp.measurable_stochasticAllCoordinateEmpiricalOptimisticQ
          episodes defaultState rewardBudget transitionBudget stage state action
            value hvalue
      have hselected : Measurable fun batch : EpisodeBatch mdp episodes =>
          FiniteRealArgmax.choose (scores batch) :=
        FiniteRealArgmax.measurable_choose_of_forall_measurable scores hscores
      have hselectedScore : Measurable fun batch : EpisodeBatch mdp episodes =>
          scores batch (FiniteRealArgmax.choose (scores batch)) :=
        FiniteRealArgmax.measurable_selected_score_of_forall_measurable
          scores hscores _ hselected
      simpa [EstimatedModelPlan.upperValueRemaining,
        EstimatedModelPlan.optimisticBellman,
        EstimatedModelPlan.optimisticAction, scores, value, stage] using
          hselectedScore

omit [Nonempty State] in
/-- Every chronological sampled empirical optimistic action is measurable. -/
theorem measurable_stochasticAllCoordinateEmpiricalOptimisticActionAt
    (mdp : MDP State Action) (episodes : Nat)
    (defaultState : State) (rewardBudget transitionBudget : Real)
    (stage : Fin mdp.horizon) (state : State) :
    Measurable fun batch : EpisodeBatch mdp episodes =>
      let model := mdp.stochasticAllCoordinateEmpiricalFiniteBatchModel
        episodes batch defaultState rewardBudget transitionBudget
      model.plan.optimisticActionAt stage state := by
  let remaining := mdp.horizon - (stage.val + 1)
  let value := fun batch : EpisodeBatch mdp episodes =>
    let model := mdp.stochasticAllCoordinateEmpiricalFiniteBatchModel
      episodes batch defaultState rewardBudget transitionBudget
    model.plan.upperValueRemaining remaining (Nat.sub_le _ _)
  let scores := fun batch : EpisodeBatch mdp episodes => fun action : Action =>
    let model := mdp.stochasticAllCoordinateEmpiricalFiniteBatchModel
      episodes batch defaultState rewardBudget transitionBudget
    model.plan.optimisticQ stage (value batch) state action
  have hvalue : forall nextState : State,
      Measurable fun batch => value batch nextState := by
    intro nextState
    exact mdp.measurable_stochasticAllCoordinateEmpiricalUpperValueRemaining
      episodes defaultState rewardBudget transitionBudget remaining
        (Nat.sub_le _ _) nextState
  have hscores : forall action : Action,
      Measurable fun batch => scores batch action := by
    intro action
    exact mdp.measurable_stochasticAllCoordinateEmpiricalOptimisticQ
      episodes defaultState rewardBudget transitionBudget stage state action
        value hvalue
  simpa [EstimatedModelPlan.optimisticActionAt,
    EstimatedModelPlan.optimisticAction, scores, value, remaining] using
      (FiniteRealArgmax.measurable_choose_of_forall_measurable scores hscores)

omit [Nonempty State] in
/-- The complete sampled empirical optimistic policy table is measurable. -/
theorem measurable_stochasticAllCoordinateEmpiricalOptimisticPolicyTable
    (mdp : MDP State Action) (episodes : Nat)
    (defaultState : State) (rewardBudget transitionBudget : Real) :
    Measurable fun batch : EpisodeBatch mdp episodes =>
      fun stage state =>
        (mdp.stochasticAllCoordinateEmpiricalFiniteBatchModel
          episodes batch defaultState rewardBudget transitionBudget).plan
            |>.optimisticActionAt stage state := by
  refine measurable_pi_lambda _ fun stage => ?_
  refine measurable_pi_lambda _ fun state => ?_
  exact mdp.measurable_stochasticAllCoordinateEmpiricalOptimisticActionAt
    episodes defaultState rewardBudget transitionBudget stage state

end MDP

namespace StochasticEpisodeBatch

/-- Optimistic table computed from the actual sampled rewards in one batch. -/
noncomputable def sampledEmpiricalOptimisticPolicyTable
    {mdp : MDP State Action} {episodes : Nat}
    (batch : StochasticEpisodeBatch mdp episodes) (defaultState : State)
    (rewardBudget transitionBudget : Real) :
    DeterministicMarkovPolicyTable mdp :=
  fun stage state =>
    (mdp.stochasticAllCoordinateEmpiricalFiniteBatchModel episodes
      (mdp.sampledEpisodeBatchOfStochasticTrajectories episodes batch)
      defaultState rewardBudget transitionBudget).plan.optimisticActionAt stage state

/-- The sampled-reward optimistic table is measurable in the stochastic batch. -/
theorem measurable_sampledEmpiricalOptimisticPolicyTable
    {mdp : MDP State Action} {episodes : Nat} (defaultState : State)
    (rewardBudget transitionBudget : Real) :
    Measurable fun batch : StochasticEpisodeBatch mdp episodes =>
      batch.sampledEmpiricalOptimisticPolicyTable
        defaultState rewardBudget transitionBudget := by
  exact
    (mdp.measurable_stochasticAllCoordinateEmpiricalOptimisticPolicyTable
      episodes defaultState rewardBudget transitionBudget).comp
        (mdp.measurable_sampledEpisodeBatchOfStochasticTrajectories episodes)

end StochasticEpisodeBatch

namespace AdaptiveStochasticSampledEmpiricalOptimisticSource

/-- The latest complete stochastic batch in a finite nonempty prefix. -/
def latestBatch
    {mdp : MDP State Action} {episodes n : Nat}
    (history : StochasticEpisodeBatchPrefix mdp episodes n) :
    StochasticEpisodeBatch mdp episodes :=
  history ⟨n, Finset.mem_Iic.mpr le_rfl⟩

omit [DecidableEq State] [DecidableEq Action]
    [MeasurableSingletonClass State] [MeasurableSingletonClass Action]
    [Nonempty State] [Nonempty Action] in
theorem measurable_latestBatch
    {mdp : MDP State Action} {episodes n : Nat} :
    Measurable
      (latestBatch : StochasticEpisodeBatchPrefix mdp episodes n ->
        StochasticEpisodeBatch mdp episodes) :=
  measurable_pi_apply
    (⟨n, Finset.mem_Iic.mpr le_rfl⟩ : Finset.Iic n)

/-- Sampled-reward optimistic table selected from the latest stochastic batch. -/
noncomputable def successorTable
    {mdp : MDP State Action} {episodes : Nat} (defaultState : State)
    (rewardBudget transitionBudget : Real) (n : Nat)
    (history : StochasticEpisodeBatchPrefix mdp episodes n) :
    DeterministicMarkovPolicyTable mdp :=
  (latestBatch history).sampledEmpiricalOptimisticPolicyTable
    defaultState rewardBudget transitionBudget

theorem measurable_successorTable
    {mdp : MDP State Action} {episodes : Nat} (defaultState : State)
    (rewardBudget transitionBudget : Real) (n : Nat) :
    Measurable
      (successorTable (mdp := mdp) (episodes := episodes)
        defaultState rewardBudget transitionBudget n) :=
  (StochasticEpisodeBatch.measurable_sampledEmpiricalOptimisticPolicyTable
    defaultState rewardBudget transitionBudget).comp measurable_latestBatch

/--
Adaptive exploratory source whose successor policy uses actual sampled rewards.
-/
noncomputable def exploratorySource
    (mdp : MDP State Action) (initialState : Measure State)
    [IsProbabilityMeasure initialState] (episodes : Nat)
    (rewardSource : mdp.MeanCompatibleRewardKernel)
    (initialTable : DeterministicMarkovPolicyTable mdp)
    (defaultState : State) (rewardBudget transitionBudget : Real)
    (explorationRate : NNReal) (hexplorationRate : explorationRate <= 1) :
    AdaptiveStochasticEpisodeBatchSource mdp initialState episodes where
  rewardSource := rewardSource
  initialPolicy := initialTable.exploratoryPolicy
    explorationRate hexplorationRate
  successorPolicy n history :=
    (successorTable defaultState rewardBudget transitionBudget n history)
      |>.exploratoryPolicy explorationRate hexplorationRate
  batchKernel n :=
    (DeterministicMarkovPolicyTable.exploratoryIIDStochasticEpisodeBatchKernel
      rewardSource initialState episodes explorationRate hexplorationRate).comap
        (successorTable defaultState rewardBudget transitionBudget n)
        (measurable_successorTable defaultState rewardBudget transitionBudget n)
  batchKernel_isMarkov n := by
    exact ProbabilityTheory.Kernel.IsMarkovKernel.comap _
      (measurable_successorTable defaultState rewardBudget transitionBudget n)
  batchKernel_eq_iidStochasticTrajectoryFamilyMeasure n history := by
    rw [ProbabilityTheory.Kernel.comap_apply]
    rfl
  measurable_successorSampledReturnDeviation n := by
    exact
      AdaptiveStochasticEmpiricalOptimisticSource.measurable_selectedExploratorySampledReturnDeviation
          (successorTable defaultState rewardBudget transitionBudget n)
          (measurable_successorTable
            defaultState rewardBudget transitionBudget n)
          explorationRate hexplorationRate

/-- Every history fiber has the exact iid stochastic law of its selected policy. -/
theorem exploratorySource_batchKernel_eq_selectedPolicy_iidLaw
    {mdp : MDP State Action} {initialState : Measure State}
    [IsProbabilityMeasure initialState] {episodes : Nat}
    (rewardSource : mdp.MeanCompatibleRewardKernel)
    (initialTable : DeterministicMarkovPolicyTable mdp)
    (defaultState : State) (rewardBudget transitionBudget : Real)
    (explorationRate : NNReal) (hexplorationRate : explorationRate <= 1)
    (n : Nat) (history : StochasticEpisodeBatchPrefix mdp episodes n) :
    let source := exploratorySource mdp initialState episodes rewardSource
      initialTable defaultState rewardBudget transitionBudget
        explorationRate hexplorationRate
    source.batchKernel n history =
      rewardSource.iidStochasticTrajectoryFamilyMeasure
        ((successorTable defaultState rewardBudget transitionBudget n history)
          |>.exploratoryPolicy explorationRate hexplorationRate)
        initialState episodes := by
  rfl

end AdaptiveStochasticSampledEmpiricalOptimisticSource
end FiniteHorizonRL
end BanditRLProof
