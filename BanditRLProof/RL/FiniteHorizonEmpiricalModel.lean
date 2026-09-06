import BanditRLProof.RL.FiniteHorizonCoordinateModelConfidence
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.Probability.ProbabilityMassFunction.Monad

/-!
# Finite-batch empirical models for finite-horizon RL

This module builds a genuine finite-state empirical transition kernel from a
finite family of recorded episode steps. Positive visit counts are normalized
into a finite PMF; zero visit counts use an explicit default-state Dirac PMF.
The resulting empirical reward and transition model is then connected to the
compiled coordinate-confidence optimistic-regret route.
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

/-- One recorded finite-horizon transition with its observed reward. -/
structure EpisodeStep (State : Type u) (Action : Type v) where
  state : State
  action : Action
  reward : Real
  nextState : State

namespace EpisodeStep

/-- Product-coordinate measurable structure for one empirical episode step. -/
instance instMeasurableSpace : MeasurableSpace (EpisodeStep State Action) :=
  MeasurableSpace.comap
    (fun step => (step.state, step.action, step.reward, step.nextState))
    inferInstance

omit [Fintype State] [Fintype Action]
    [DecidableEq State] [DecidableEq Action]
    [MeasurableSingletonClass State] [MeasurableSingletonClass Action]
    [Nonempty State] [Nonempty Action] in
theorem measurable_state : Measurable (fun step : EpisodeStep State Action => step.state) := by
  have hencode : Measurable
      (fun step : EpisodeStep State Action =>
        (step.state, step.action, step.reward, step.nextState)) :=
    comap_measurable _
  exact measurable_fst.comp hencode

omit [Fintype State] [Fintype Action]
    [DecidableEq State] [DecidableEq Action]
    [MeasurableSingletonClass State] [MeasurableSingletonClass Action]
    [Nonempty State] [Nonempty Action] in
theorem measurable_action : Measurable (fun step : EpisodeStep State Action => step.action) := by
  have hencode : Measurable
      (fun step : EpisodeStep State Action =>
        (step.state, step.action, step.reward, step.nextState)) :=
    comap_measurable _
  exact measurable_fst.comp (measurable_snd.comp hencode)

omit [Fintype State] [Fintype Action]
    [DecidableEq State] [DecidableEq Action]
    [MeasurableSingletonClass State] [MeasurableSingletonClass Action]
    [Nonempty State] [Nonempty Action] in
theorem measurable_reward : Measurable (fun step : EpisodeStep State Action => step.reward) := by
  have hencode : Measurable
      (fun step : EpisodeStep State Action =>
        (step.state, step.action, step.reward, step.nextState)) :=
    comap_measurable _
  exact measurable_fst.comp (measurable_snd.comp (measurable_snd.comp hencode))

omit [Fintype State] [Fintype Action]
    [DecidableEq State] [DecidableEq Action]
    [MeasurableSingletonClass State] [MeasurableSingletonClass Action]
    [Nonempty State] [Nonempty Action] in
theorem measurable_nextState :
    Measurable (fun step : EpisodeStep State Action => step.nextState) := by
  have hencode : Measurable
      (fun step : EpisodeStep State Action =>
        (step.state, step.action, step.reward, step.nextState)) :=
    comap_measurable _
  exact measurable_snd.comp (measurable_snd.comp (measurable_snd.comp hencode))

end EpisodeStep

/--
A finite table with one record at each valid stage of every episode.  This raw
type does not enforce cross-stage state continuity or identify the records with
samples from the MDP trajectory law; those are downstream probabilistic laws.
-/
abbrev EpisodeBatch (mdp : MDP State Action) (episodes : Nat) :=
  Fin episodes -> Fin mdp.horizon -> EpisodeStep State Action

namespace EpisodeBatch

/-- Number of batch episodes visiting a state-action pair at one stage. -/
def visitCount {mdp : MDP State Action} {episodes : Nat}
    (batch : EpisodeBatch mdp episodes) (stage : Fin mdp.horizon)
    (state : State) (action : Action) : Nat :=
  ∑ episode, if (batch episode stage).state = state /\
      (batch episode stage).action = action then 1 else 0

/-- Sum of rewards recorded at a state-action pair and stage. -/
def rewardSum {mdp : MDP State Action} {episodes : Nat}
    (batch : EpisodeBatch mdp episodes) (stage : Fin mdp.horizon)
    (state : State) (action : Action) : Real :=
  ∑ episode, if (batch episode stage).state = state /\
      (batch episode stage).action = action then
        (batch episode stage).reward else 0

/-- Empirical reward mean, with the conventional zero value at zero visits. -/
noncomputable def empiricalReward {mdp : MDP State Action} {episodes : Nat}
    (batch : EpisodeBatch mdp episodes) (stage : Fin mdp.horizon)
    (state : State) (action : Action) : Real :=
  batch.rewardSum stage state action /
    (batch.visitCount stage state action : Real)

/-- Number of matching transitions to a fixed next state. -/
def transitionCount {mdp : MDP State Action} {episodes : Nat}
    (batch : EpisodeBatch mdp episodes) (stage : Fin mdp.horizon)
    (state : State) (action : Action) (nextState : State) : Nat :=
  ∑ episode, if (batch episode stage).state = state /\
      (batch episode stage).action = action /\
      (batch episode stage).nextState = nextState then 1 else 0

omit [MeasurableSingletonClass State] [MeasurableSingletonClass Action]
    [Nonempty State] [Nonempty Action] in
/-- Next-state transition counts partition the state-action visit count. -/
theorem sum_transitionCount_eq_visitCount
    {mdp : MDP State Action} {episodes : Nat}
    (batch : EpisodeBatch mdp episodes) (stage : Fin mdp.horizon)
    (state : State) (action : Action) :
    ∑ nextState, batch.transitionCount stage state action nextState =
      batch.visitCount stage state action := by
  classical
  unfold transitionCount visitCount
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro episode _
  by_cases hstate : (batch episode stage).state = state
  · by_cases haction : (batch episode stage).action = action
    · simp [hstate, haction]
    · simp [haction]
  · simp [hstate]

/-- Empirical next-state PMF with an explicit zero-visit fallback state. -/
noncomputable def empiricalTransitionPMF
    {mdp : MDP State Action} {episodes : Nat}
    (batch : EpisodeBatch mdp episodes) (defaultState : State)
    (stage : Fin mdp.horizon) (state : State) (action : Action) : PMF State :=
  if hzero : batch.visitCount stage state action = 0 then
    PMF.pure defaultState
  else
    PMF.ofFintype
      (fun nextState =>
        (batch.transitionCount stage state action nextState : ENNReal) /
          (batch.visitCount stage state action : ENNReal))
      (by
        have sum_div_visitCount (states : Finset State) :
            (∑ nextState ∈ states,
                (batch.transitionCount stage state action nextState : ENNReal) /
                  (batch.visitCount stage state action : ENNReal)) =
              (∑ nextState ∈ states,
                  (batch.transitionCount stage state action nextState : ENNReal)) /
                (batch.visitCount stage state action : ENNReal) := by
          classical
          induction states using Finset.induction_on with
          | empty => simp
          | @insert nextState states hnext ih =>
              simp only [Finset.sum_insert hnext]
              rw [ih, ENNReal.add_div]
        calc
          ∑ nextState,
              (batch.transitionCount stage state action nextState : ENNReal) /
                (batch.visitCount stage state action : ENNReal) =
              (∑ nextState,
                (batch.transitionCount stage state action nextState : ENNReal)) /
                (batch.visitCount stage state action : ENNReal) := by
            simpa using sum_div_visitCount (Finset.univ : Finset State)
          _ = (batch.visitCount stage state action : ENNReal) /
                (batch.visitCount stage state action : ENNReal) := by
            congr 1
            exact_mod_cast batch.sum_transitionCount_eq_visitCount stage state action
          _ = 1 :=
            ENNReal.div_self (by exact_mod_cast hzero) (ENNReal.natCast_ne_top _))

/-- Real singleton mass of the empirical transition PMF. -/
noncomputable def empiricalTransitionMass
    {mdp : MDP State Action} {episodes : Nat}
    (batch : EpisodeBatch mdp episodes) (defaultState : State)
    (stage : Fin mdp.horizon) (state : State) (action : Action)
    (nextState : State) : Real :=
  (batch.empiricalTransitionPMF defaultState stage state action nextState).toReal

omit [MeasurableSingletonClass State] [MeasurableSingletonClass Action]
    [Nonempty State] [Nonempty Action] in
/-- Zero-visit state-action pairs use the declared fallback distribution. -/
theorem empiricalTransitionPMF_eq_pure_of_visitCount_eq_zero
    {mdp : MDP State Action} {episodes : Nat}
    (batch : EpisodeBatch mdp episodes) (defaultState : State)
    (stage : Fin mdp.horizon) (state : State) (action : Action)
    (hzero : batch.visitCount stage state action = 0) :
    batch.empiricalTransitionPMF defaultState stage state action =
      PMF.pure defaultState := by
  simp [empiricalTransitionPMF, hzero]

omit [MeasurableSingletonClass State] [MeasurableSingletonClass Action]
    [Nonempty State] [Nonempty Action] in
/-- At a positive visit count, empirical PMF mass is normalized count. -/
theorem empiricalTransitionPMF_apply_of_visitCount_ne_zero
    {mdp : MDP State Action} {episodes : Nat}
    (batch : EpisodeBatch mdp episodes) (defaultState : State)
    (stage : Fin mdp.horizon) (state : State) (action : Action)
    (nextState : State)
    (hvisit : batch.visitCount stage state action ≠ 0) :
    batch.empiricalTransitionPMF defaultState stage state action nextState =
      (batch.transitionCount stage state action nextState : ENNReal) /
        (batch.visitCount stage state action : ENNReal) := by
  simp [empiricalTransitionPMF, hvisit]

omit [MeasurableSingletonClass State] [MeasurableSingletonClass Action]
    [Nonempty State] [Nonempty Action] in
/-- Real empirical singleton mass is the usual count divided by visit count. -/
theorem empiricalTransitionMass_eq_div_of_visitCount_ne_zero
    {mdp : MDP State Action} {episodes : Nat}
    (batch : EpisodeBatch mdp episodes) (defaultState : State)
    (stage : Fin mdp.horizon) (state : State) (action : Action)
    (nextState : State)
    (hvisit : batch.visitCount stage state action ≠ 0) :
    batch.empiricalTransitionMass defaultState stage state action nextState =
      (batch.transitionCount stage state action nextState : Real) /
        (batch.visitCount stage state action : Real) := by
  unfold empiricalTransitionMass
  rw [batch.empiricalTransitionPMF_apply_of_visitCount_ne_zero
    defaultState stage state action nextState hvisit]
  simp

/-- State-action indexed empirical PMFs form a measurable finite-state kernel. -/
noncomputable def empiricalTransitionKernel
    {mdp : MDP State Action} {episodes : Nat}
    (batch : EpisodeBatch mdp episodes) (defaultState : State)
    (stage : Fin mdp.horizon) :
    ProbabilityTheory.Kernel (State × Action) State :=
  ProbabilityTheory.Kernel.ofFunOfCountable fun pair =>
    (batch.empiricalTransitionPMF defaultState stage pair.1 pair.2).toMeasure

omit [Nonempty State] [Nonempty Action] in
@[simp]
theorem empiricalTransitionKernel_apply
    {mdp : MDP State Action} {episodes : Nat}
    (batch : EpisodeBatch mdp episodes) (defaultState : State)
    (stage : Fin mdp.horizon) (state : State) (action : Action) :
    batch.empiricalTransitionKernel defaultState stage (state, action) =
      (batch.empiricalTransitionPMF defaultState stage state action).toMeasure :=
  rfl

omit [Nonempty State] [Nonempty Action] in
/-- Every section of the empirical transition kernel is a probability law. -/
theorem empiricalTransitionKernel_isMarkov
    {mdp : MDP State Action} {episodes : Nat}
    (batch : EpisodeBatch mdp episodes) (defaultState : State)
    (stage : Fin mdp.horizon) :
    ProbabilityTheory.IsMarkovKernel
      (batch.empiricalTransitionKernel defaultState stage) where
  isProbabilityMeasure pair := by
    change IsProbabilityMeasure
      ((batch.empiricalTransitionPMF defaultState stage pair.1 pair.2).toMeasure)
    infer_instance

omit [Nonempty State] [Nonempty Action] in
/-- Kernel singleton mass agrees with the named empirical transition mass. -/
theorem empiricalTransitionKernel_real_singleton
    {mdp : MDP State Action} {episodes : Nat}
    (batch : EpisodeBatch mdp episodes) (defaultState : State)
    (stage : Fin mdp.horizon) (state : State) (action : Action)
    (nextState : State) :
    (batch.empiricalTransitionKernel defaultState stage
        (state, action)).real {nextState} =
      batch.empiricalTransitionMass defaultState stage state action nextState := by
  rw [empiricalTransitionKernel_apply]
  unfold empiricalTransitionMass
  rw [measureReal_def]
  rw [PMF.toMeasure_apply_singleton _ _ (MeasurableSet.singleton nextState)]

end EpisodeBatch

namespace MDP

/--
A finite batch together with reward and transition radii.  The empirical reward
and transition model are derived from `batch`; zero transition counts use the
explicit `defaultState` fallback rather than an implicit arbitrary law.
-/
structure FiniteBatchModel (mdp : MDP State Action) (episodes : Nat) where
  batch : EpisodeBatch mdp episodes
  defaultState : State
  rewardRadius : Fin mdp.horizon -> State -> Action -> Real
  transitionRadius : Fin mdp.horizon -> State -> Action -> Real

namespace FiniteBatchModel

/-- The estimated-model plan canonically generated by a finite episode batch. -/
noncomputable def plan {mdp : MDP State Action} {episodes : Nat}
    (model : FiniteBatchModel mdp episodes) : EstimatedModelPlan mdp where
  estimatedReward := model.batch.empiricalReward
  measurable_estimatedReward _ := measurable_of_finite _
  estimatedTransition stage :=
    model.batch.empiricalTransitionKernel model.defaultState stage
  estimatedTransition_isMarkov stage :=
    model.batch.empiricalTransitionKernel_isMarkov model.defaultState stage
  rewardRadius := model.rewardRadius
  measurable_rewardRadius _ := measurable_of_finite _
  transitionRadius := model.transitionRadius
  measurable_transitionRadius _ := measurable_of_finite _

/--
Raw finite-batch confidence contracts.  Reward errors and singleton-frequency
errors are stated directly on the empirical statistics, while the envelope and
radius-cover fields discharge the value-dependent coordinate transport.
-/
structure Confidence {mdp : MDP State Action} {episodes : Nat}
    (model : FiniteBatchModel mdp episodes) where
  transitionCoordinateRadius :
    Fin mdp.horizon -> State -> Action -> State -> Real
  valueEnvelope : Nat -> Real
  rewardError_le_radius : forall (stage : Fin mdp.horizon)
    (state : State) (action : Action),
    |model.batch.empiricalReward stage state action - mdp.reward state action| <=
      model.rewardRadius stage state action
  transitionFrequencyError_le_radius : forall (remaining : Nat)
    (hremaining : remaining + 1 <= mdp.horizon)
    (state : State) (action : Action) (nextState : State),
    |model.batch.empiricalTransitionMass model.defaultState
          (mdp.decisionStageRemaining remaining hremaining)
          state action nextState -
        (mdp.transition (state, action)).real {nextState}| <=
      transitionCoordinateRadius
        (mdp.decisionStageRemaining remaining hremaining)
        state action nextState
  upperValue_abs_le_envelope : forall (remaining : Nat)
    (hremaining : remaining + 1 <= mdp.horizon) (state : State),
    |model.plan.upperValueRemaining remaining (by omega) state| <=
      valueEnvelope remaining
  transitionRadius_cover : forall (remaining : Nat)
    (hremaining : remaining + 1 <= mdp.horizon)
    (state : State) (action : Action),
    (∑ nextState,
        transitionCoordinateRadius
            (mdp.decisionStageRemaining remaining hremaining)
            state action nextState *
          valueEnvelope remaining) <=
      model.transitionRadius
        (mdp.decisionStageRemaining remaining hremaining) state action

/-- Raw empirical-statistic confidence gives coordinate model confidence. -/
noncomputable def Confidence.toCoordinateConfidence
    {mdp : MDP State Action} {episodes : Nat}
    {model : FiniteBatchModel mdp episodes}
    (confidence : model.Confidence) : model.plan.CoordinateConfidence where
  transitionCoordinateRadius := confidence.transitionCoordinateRadius
  valueEnvelope := confidence.valueEnvelope
  rewardError_le_radius stage state action := by
    exact confidence.rewardError_le_radius stage state action
  transitionCoordinateError_le_radius remaining hremaining state action nextState := by
    change
      |(model.batch.empiricalTransitionKernel model.defaultState
            (mdp.decisionStageRemaining remaining hremaining)
            (state, action)).real {nextState} -
          (mdp.transition (state, action)).real {nextState}| <=
        confidence.transitionCoordinateRadius
          (mdp.decisionStageRemaining remaining hremaining)
          state action nextState
    rw [EpisodeBatch.empiricalTransitionKernel_real_singleton]
    exact confidence.transitionFrequencyError_le_radius
      remaining hremaining state action nextState
  upperValue_abs_le_envelope remaining hremaining state :=
    confidence.upperValue_abs_le_envelope remaining hremaining state
  transitionRadius_cover remaining hremaining state action :=
    confidence.transitionRadius_cover remaining hremaining state action

omit [Nonempty State] in
/--
Route endpoint: finite-batch reward and singleton-frequency confidence imply
global optimism and the compiled selected-radius expected-regret bound.
-/
theorem Confidence.optimism_and_expectedRegret_le_two_occupancySelectedRadiusRemaining
    {mdp : MDP State Action} {episodes : Nat}
    {model : FiniteBatchModel mdp episodes}
    (confidence : model.Confidence) (initialState : Measure State)
    [IsProbabilityMeasure initialState] :
    (forall state,
      mdp.optimalValueRemaining mdp.horizon le_rfl state <=
        model.plan.upperValueRemaining mdp.horizon le_rfl state) /\
      model.plan.optimisticPolicy.expectedRegret initialState <=
        model.plan.optimisticPolicy.occupancySumRemaining
          (fun remaining hremaining state =>
            2 * model.plan.selectedRadiusRemaining remaining hremaining state)
          mdp.horizon le_rfl initialState :=
  confidence.toCoordinateConfidence
    |>.optimism_and_expectedRegret_le_two_occupancySelectedRadiusRemaining
      initialState

end FiniteBatchModel
end MDP
end FiniteHorizonRL
end BanditRLProof
