import BanditRLProof.FiniteRealArgmax
import BanditRLProof.RL.FiniteHorizonOptimisticCertificate

/-!
# Estimated finite-horizon models produce optimistic certificates

This module connects a stage-indexed estimated reward/transition model to the
compiled deterministic optimistic-certificate route.  Separate two-sided
reward and transition-expectation radii are required only on the recursively
generated tail upper values.  They produce a true Bellman certificate.  The
deterministic policy greedy for the estimated optimistic backup then has true
Bellman residual at most twice its selected reward-plus-transition radius, so
the existing occupancy theorem gives a single-episode expected-regret bound.
-/

open MeasureTheory
open scoped ProbabilityTheory

universe u v

namespace BanditRLProof
namespace FiniteHorizonRL

variable {State : Type u} {Action : Type v}
    [MeasurableSpace State] [MeasurableSpace Action]
    [Fintype State] [Fintype Action]
    [MeasurableSingletonClass State] [Nonempty Action]

namespace MDP

/-- Chronological stage corresponding to a successor remaining-horizon index. -/
def decisionStageRemaining (mdp : MDP State Action) (remaining : Nat)
    (hremaining : remaining + 1 <= mdp.horizon) : Fin mdp.horizon :=
  ⟨mdp.horizon - (remaining + 1), by omega⟩

/--
A stage-indexed estimated MDP together with separate reward and transition
confidence radii.  Confidence itself is a downstream proposition because the
transition error is evaluated on the recursively generated upper value.
-/
structure EstimatedModelPlan (mdp : MDP State Action) where
  estimatedReward : Fin mdp.horizon -> State -> Action -> Real
  measurable_estimatedReward : forall stage,
    Measurable (Function.uncurry (estimatedReward stage))
  estimatedTransition : Fin mdp.horizon ->
    ProbabilityTheory.Kernel (State × Action) State
  estimatedTransition_isMarkov : forall stage,
    ProbabilityTheory.IsMarkovKernel (estimatedTransition stage)
  rewardRadius : Fin mdp.horizon -> State -> Action -> Real
  measurable_rewardRadius : forall stage,
    Measurable (Function.uncurry (rewardRadius stage))
  transitionRadius : Fin mdp.horizon -> State -> Action -> Real
  measurable_transitionRadius : forall stage,
    Measurable (Function.uncurry (transitionRadius stage))

namespace EstimatedModelPlan

instance instEstimatedTransitionIsMarkovKernel
    {mdp : MDP State Action} (plan : EstimatedModelPlan mdp)
    (stage : Fin mdp.horizon) :
    ProbabilityTheory.IsMarkovKernel (plan.estimatedTransition stage) :=
  plan.estimatedTransition_isMarkov stage

/-- The true MDP with zero radii is the canonical exact estimated plan. -/
def exactModelPlan (mdp : MDP State Action) : EstimatedModelPlan mdp where
  estimatedReward _ := mdp.reward
  measurable_estimatedReward _ := mdp.measurable_reward
  estimatedTransition _ := mdp.transition
  estimatedTransition_isMarkov _ := mdp.transition_isMarkov
  rewardRadius _ := fun _ _ => 0
  measurable_rewardRadius _ := measurable_const
  transitionRadius _ := fun _ _ => 0
  measurable_transitionRadius _ := measurable_const

/-- Estimated next-state expectation of a continuation value. -/
noncomputable def transitionValue
    {mdp : MDP State Action} (plan : EstimatedModelPlan mdp)
    (stage : Fin mdp.horizon) (value : State -> Real)
    (state : State) (action : Action) : Real :=
  ∫ nextState, value nextState ∂plan.estimatedTransition stage (state, action)

/-- Estimated one-step reward plus continuation value. -/
noncomputable def bellmanQ
    {mdp : MDP State Action} (plan : EstimatedModelPlan mdp)
    (stage : Fin mdp.horizon) (value : State -> Real)
    (state : State) (action : Action) : Real :=
  plan.estimatedReward stage state action +
    plan.transitionValue stage value state action

/-- Estimated Bellman action value enlarged by both confidence radii. -/
noncomputable def optimisticQ
    {mdp : MDP State Action} (plan : EstimatedModelPlan mdp)
    (stage : Fin mdp.horizon) (value : State -> Real)
    (state : State) (action : Action) : Real :=
  plan.bellmanQ stage value state action +
    plan.rewardRadius stage state action +
    plan.transitionRadius stage state action

omit [MeasurableSingletonClass State] [Nonempty Action] in
/-- The estimated transition-value surface is measurable in the state-action pair. -/
theorem measurable_transitionValue
    {mdp : MDP State Action} (plan : EstimatedModelPlan mdp)
    (stage : Fin mdp.horizon) {value : State -> Real}
    (hvalue : Measurable value) :
    Measurable (Function.uncurry (plan.transitionValue stage value)) := by
  exact hvalue.stronglyMeasurable.integral_kernel.measurable

omit [MeasurableSingletonClass State] [Nonempty Action] in
/-- The optimistic estimated action-value surface is measurable. -/
theorem measurable_optimisticQ
    {mdp : MDP State Action} (plan : EstimatedModelPlan mdp)
    (stage : Fin mdp.horizon) {value : State -> Real}
    (hvalue : Measurable value) :
    Measurable (Function.uncurry (plan.optimisticQ stage value)) := by
  exact
    (plan.measurable_estimatedReward stage).add
      (plan.measurable_transitionValue stage hvalue) |>.add
      (plan.measurable_rewardRadius stage) |>.add
      (plan.measurable_transitionRadius stage)

/-- A finite action maximizing the estimated optimistic action value. -/
noncomputable def optimisticAction
    {mdp : MDP State Action} (plan : EstimatedModelPlan mdp)
    (stage : Fin mdp.horizon) (value : State -> Real) (state : State) : Action :=
  FiniteRealArgmax.choose
    (fun action => plan.optimisticQ stage value state action)

omit [MeasurableSingletonClass State] in
/-- Every action is bounded by the selected optimistic estimated action value. -/
theorem optimisticQ_le_optimisticAction
    {mdp : MDP State Action} (plan : EstimatedModelPlan mdp)
    (stage : Fin mdp.horizon) (value : State -> Real)
    (state : State) (action : Action) :
    plan.optimisticQ stage value state action <=
      plan.optimisticQ stage value state
        (plan.optimisticAction stage value state) := by
  exact FiniteRealArgmax.score_le_choose
    (fun selected => plan.optimisticQ stage value state selected) action

/-- Pointwise maximum of the estimated optimistic action values. -/
noncomputable def optimisticBellman
    {mdp : MDP State Action} (plan : EstimatedModelPlan mdp)
    (stage : Fin mdp.horizon) (value : State -> Real) (state : State) : Real :=
  plan.optimisticQ stage value state
    (plan.optimisticAction stage value state)

/-- The finite-state estimated optimistic selector is measurable. -/
theorem measurable_optimisticAction
    {mdp : MDP State Action} (plan : EstimatedModelPlan mdp)
    (stage : Fin mdp.horizon) (value : State -> Real) :
    Measurable (plan.optimisticAction stage value) :=
  measurable_of_finite _

/-- Recursive estimated optimistic value indexed by decisions remaining. -/
noncomputable def upperValueRemaining
    {mdp : MDP State Action} (plan : EstimatedModelPlan mdp) :
    (remaining : Nat) -> remaining <= mdp.horizon -> State -> Real
  | 0, _ => fun _ => 0
  | remaining + 1, hremaining =>
      plan.optimisticBellman (mdp.decisionStageRemaining remaining hremaining)
        (plan.upperValueRemaining remaining (by omega))

omit [MeasurableSingletonClass State] in
/-- Transport the dependent upper-value recursion across equal remaining horizons. -/
theorem upperValueRemaining_eq_of_eq
    {mdp : MDP State Action} (plan : EstimatedModelPlan mdp)
    {left right : Nat} (hleft : left <= mdp.horizon)
    (hright : right <= mdp.horizon) (h : left = right) :
    plan.upperValueRemaining left hleft =
      plan.upperValueRemaining right hright := by
  subst right
  rfl

/-- Every recursively generated upper-value surface is measurable. -/
theorem measurable_upperValueRemaining
    {mdp : MDP State Action} (plan : EstimatedModelPlan mdp)
    (remaining : Nat) (hremaining : remaining <= mdp.horizon) :
    Measurable (plan.upperValueRemaining remaining hremaining) :=
  measurable_of_finite _

/--
Two-sided model confidence on the recursive upper-value route.  The transition
contract is deliberately not quantified over arbitrary unbounded values.
-/
structure Confidence
    {mdp : MDP State Action} (plan : EstimatedModelPlan mdp) : Prop where
  rewardError_le_radius : forall (stage : Fin mdp.horizon)
    (state : State) (action : Action),
    |plan.estimatedReward stage state action - mdp.reward state action| <=
      plan.rewardRadius stage state action
  transitionError_le_radius : forall (remaining : Nat)
    (hremaining : remaining + 1 <= mdp.horizon)
    (state : State) (action : Action),
    |plan.transitionValue (mdp.decisionStageRemaining remaining hremaining)
          (plan.upperValueRemaining remaining (by omega)) state action -
        mdp.transitionValue
          (plan.upperValueRemaining remaining (by omega)) state action| <=
      plan.transitionRadius
        (mdp.decisionStageRemaining remaining hremaining) state action

omit [MeasurableSingletonClass State] in
/-- The canonical exact estimated plan satisfies confidence by reflexivity. -/
theorem exactModelPlan_confidence (mdp : MDP State Action) :
    (exactModelPlan mdp).Confidence := by
  constructor
  · intro stage state action
    simp [exactModelPlan]
  · intro remaining hremaining state action
    simp [exactModelPlan, transitionValue, MDP.transitionValue]

omit [MeasurableSingletonClass State] in
/-- Two-sided confidence makes every true action value optimistic. -/
theorem Confidence.trueBellmanQ_le_optimisticQ
    {mdp : MDP State Action} {plan : EstimatedModelPlan mdp}
    (confidence : plan.Confidence) (remaining : Nat)
    (hremaining : remaining + 1 <= mdp.horizon)
    (state : State) (action : Action) :
    mdp.bellmanQ (plan.upperValueRemaining remaining (by omega)) state action <=
      plan.optimisticQ (mdp.decisionStageRemaining remaining hremaining)
        (plan.upperValueRemaining remaining (by omega)) state action := by
  have hreward :=
    (abs_le.mp (confidence.rewardError_le_radius
      (mdp.decisionStageRemaining remaining hremaining) state action)).1
  have htransition :=
    (abs_le.mp (confidence.transitionError_le_radius
      remaining hremaining state action)).1
  unfold MDP.bellmanQ optimisticQ bellmanQ
  linarith

/-- The recursive estimated optimistic values form a true Bellman certificate. -/
noncomputable def certificate
    {mdp : MDP State Action} (plan : EstimatedModelPlan mdp)
    (confidence : plan.Confidence) : mdp.OptimisticBellmanCertificate where
  upperValueRemaining := plan.upperValueRemaining
  upperValueRemaining_zero := rfl
  optimalBellman_le_upperValueRemaining_succ := by
    intro remaining hremaining state
    calc
      mdp.optimalBellman
          (plan.upperValueRemaining remaining (by omega)) state =
          mdp.bellmanQ (plan.upperValueRemaining remaining (by omega)) state
            (mdp.optimalAction
              (plan.upperValueRemaining remaining (by omega)) state) := rfl
      _ <= plan.optimisticQ
          (mdp.decisionStageRemaining remaining hremaining)
          (plan.upperValueRemaining remaining (by omega)) state
          (mdp.optimalAction
            (plan.upperValueRemaining remaining (by omega)) state) :=
        confidence.trueBellmanQ_le_optimisticQ remaining hremaining state _
      _ <= plan.optimisticBellman
          (mdp.decisionStageRemaining remaining hremaining)
          (plan.upperValueRemaining remaining (by omega)) state :=
        plan.optimisticQ_le_optimisticAction _ _ _ _
      _ = plan.upperValueRemaining (remaining + 1) hremaining state := by
        rw [upperValueRemaining]

/-- Estimated-model confidence implies pointwise global optimism. -/
theorem Confidence.optimalValueRemaining_le_upperValueRemaining
    {mdp : MDP State Action} {plan : EstimatedModelPlan mdp}
    (confidence : plan.Confidence) (remaining : Nat)
    (hremaining : remaining <= mdp.horizon) (state : State) :
    mdp.optimalValueRemaining remaining hremaining state <=
      plan.upperValueRemaining remaining hremaining state :=
  (plan.certificate confidence).optimalValueRemaining_le_upperValueRemaining
    remaining hremaining state

/-- Estimated optimistic action at a chronological stage. -/
noncomputable def optimisticActionAt
    {mdp : MDP State Action} (plan : EstimatedModelPlan mdp)
    (stage : Fin mdp.horizon) : State -> Action :=
  plan.optimisticAction stage
    (plan.upperValueRemaining
      (mdp.horizon - (stage.val + 1)) (Nat.sub_le _ _))

/-- The chronological estimated optimistic selector is measurable. -/
theorem measurable_optimisticActionAt
    {mdp : MDP State Action} (plan : EstimatedModelPlan mdp)
    (stage : Fin mdp.horizon) :
    Measurable (plan.optimisticActionAt stage) :=
  plan.measurable_optimisticAction _ _

/-- Deterministic Markov policy greedy for each estimated optimistic backup. -/
noncomputable def optimisticPolicy
    {mdp : MDP State Action} (plan : EstimatedModelPlan mdp) :
    MarkovPolicy mdp where
  actionKernel stage :=
    ProbabilityTheory.Kernel.deterministic
      (plan.optimisticActionAt stage)
      (plan.measurable_optimisticActionAt stage)
  actionKernel_isMarkov := by
    intro stage
    infer_instance

omit [MeasurableSingletonClass State] in
/-- Remaining-horizon and chronological selectors agree exactly. -/
theorem optimisticActionAt_decisionStageRemaining
    {mdp : MDP State Action} (plan : EstimatedModelPlan mdp)
    (remaining : Nat) (hremaining : remaining + 1 <= mdp.horizon) :
    plan.optimisticActionAt (mdp.decisionStageRemaining remaining hremaining) =
      plan.optimisticAction (mdp.decisionStageRemaining remaining hremaining)
        (plan.upperValueRemaining remaining (by omega)) := by
  unfold optimisticActionAt
  apply congrArg
    (fun value => plan.optimisticAction
      (mdp.decisionStageRemaining remaining hremaining) value)
  apply plan.upperValueRemaining_eq_of_eq
  simp only [MDP.decisionStageRemaining]
  omega

/-- The deterministic estimated-greedy policy Bellman integral selects its action. -/
theorem optimisticPolicy_bellman_eq_bellmanQ
    {mdp : MDP State Action} (plan : EstimatedModelPlan mdp)
    (stage : Fin mdp.horizon) (value : State -> Real) (state : State) :
    plan.optimisticPolicy.bellman stage value state =
      mdp.bellmanQ value state (plan.optimisticActionAt stage state) := by
  unfold MarkovPolicy.bellman optimisticPolicy
  rw [ProbabilityTheory.Kernel.deterministic_apply]
  rw [integral_dirac']
  exact
    ((mdp.measurable_bellmanQ (measurable_of_finite value)).comp
      (measurable_const.prodMk measurable_id)).stronglyMeasurable

/-- Reward-plus-transition radius selected by the estimated optimistic policy. -/
noncomputable def selectedRadiusRemaining
    {mdp : MDP State Action} (plan : EstimatedModelPlan mdp)
    (remaining : Nat) (hremaining : remaining + 1 <= mdp.horizon)
    (state : State) : Real :=
  let stage := mdp.decisionStageRemaining remaining hremaining
  let action := plan.optimisticAction stage
    (plan.upperValueRemaining remaining (by omega)) state
  plan.rewardRadius stage state action +
    plan.transitionRadius stage state action

omit [MeasurableSingletonClass State] in
/-- Every selected radius is nonnegative under the two-sided confidence contract. -/
theorem Confidence.selectedRadiusRemaining_nonneg
    {mdp : MDP State Action} {plan : EstimatedModelPlan mdp}
    (confidence : plan.Confidence) (remaining : Nat)
    (hremaining : remaining + 1 <= mdp.horizon) (state : State) :
    0 <= plan.selectedRadiusRemaining remaining hremaining state := by
  let stage := mdp.decisionStageRemaining remaining hremaining
  let action := plan.optimisticAction stage
    (plan.upperValueRemaining remaining (by omega)) state
  have hreward := confidence.rewardError_le_radius stage state action
  have htransition := confidence.transitionError_le_radius
    remaining hremaining state action
  unfold selectedRadiusRemaining
  dsimp only
  exact add_nonneg (abs_nonneg _ |>.trans hreward)
    (abs_nonneg _ |>.trans htransition)

/--
The estimated-greedy policy residual is at most twice its selected model
confidence radius.  One side of each absolute-error bound produced optimism;
the other side controls the remaining selected-action overestimate.
-/
theorem Confidence.policyBellmanResidual_le_two_selectedRadiusRemaining
    {mdp : MDP State Action} {plan : EstimatedModelPlan mdp}
    (confidence : plan.Confidence) (remaining : Nat)
    (hremaining : remaining + 1 <= mdp.horizon) (state : State) :
    (plan.certificate confidence).policyBellmanResidual
        plan.optimisticPolicy remaining hremaining state <=
      2 * plan.selectedRadiusRemaining remaining hremaining state := by
  change
    plan.upperValueRemaining (remaining + 1) hremaining state -
        plan.optimisticPolicy.bellman
          (mdp.decisionStageRemaining remaining hremaining)
          (plan.upperValueRemaining remaining (by omega)) state <=
      2 * plan.selectedRadiusRemaining remaining hremaining state
  rw [upperValueRemaining]
  rw [plan.optimisticPolicy_bellman_eq_bellmanQ]
  rw [congrFun
    (plan.optimisticActionAt_decisionStageRemaining remaining hremaining) state]
  have hreward :=
    (abs_le.mp (confidence.rewardError_le_radius
      (mdp.decisionStageRemaining remaining hremaining) state
      (plan.optimisticAction
        (mdp.decisionStageRemaining remaining hremaining)
        (plan.upperValueRemaining remaining (by omega)) state))).2
  have htransition :=
    (abs_le.mp (confidence.transitionError_le_radius
      remaining hremaining state
      (plan.optimisticAction
        (mdp.decisionStageRemaining remaining hremaining)
        (plan.upperValueRemaining remaining (by omega)) state))).2
  unfold optimisticBellman selectedRadiusRemaining optimisticQ bellmanQ
    MDP.bellmanQ
  dsimp only
  linarith

/-- Full residual chain for the estimated-greedy policy under a probability initial law. -/
theorem Confidence.expectedRegret_le_two_occupancySelectedRadiusRemaining
    {mdp : MDP State Action} {plan : EstimatedModelPlan mdp}
    (confidence : plan.Confidence) (initialState : Measure State)
    [IsProbabilityMeasure initialState] :
    0 <= (plan.certificate confidence).residualOccupancyRemaining
        plan.optimisticPolicy mdp.horizon le_rfl initialState /\
      plan.optimisticPolicy.expectedRegret initialState <=
        (plan.certificate confidence).residualOccupancyRemaining
          plan.optimisticPolicy mdp.horizon le_rfl initialState /\
      (plan.certificate confidence).residualOccupancyRemaining
          plan.optimisticPolicy mdp.horizon le_rfl initialState <=
        plan.optimisticPolicy.occupancySumRemaining
          (fun remaining hremaining state =>
            2 * plan.selectedRadiusRemaining remaining hremaining state)
          mdp.horizon le_rfl initialState /\
      plan.optimisticPolicy.expectedRegret initialState <=
        plan.optimisticPolicy.occupancySumRemaining
          (fun remaining hremaining state =>
            2 * plan.selectedRadiusRemaining remaining hremaining state)
          mdp.horizon le_rfl initialState := by
  exact
    (plan.certificate confidence).expectedRegret_le_residual_le_occupancyBonusRemaining
      plan.optimisticPolicy initialState
      (fun remaining hremaining state =>
        2 * plan.selectedRadiusRemaining remaining hremaining state)
      (fun remaining hremaining state =>
        confidence.policyBellmanResidual_le_two_selectedRadiusRemaining
          remaining hremaining state)

/--
Route endpoint: estimated-model confidence simultaneously gives global
optimism and the selected-radius single-episode expected-regret bound.
-/
theorem Confidence.optimism_and_expectedRegret_le_two_occupancySelectedRadiusRemaining
    {mdp : MDP State Action} {plan : EstimatedModelPlan mdp}
    (confidence : plan.Confidence) (initialState : Measure State)
    [IsProbabilityMeasure initialState] :
    (forall state,
      mdp.optimalValueRemaining mdp.horizon le_rfl state <=
        plan.upperValueRemaining mdp.horizon le_rfl state) /\
      plan.optimisticPolicy.expectedRegret initialState <=
        plan.optimisticPolicy.occupancySumRemaining
          (fun remaining hremaining state =>
            2 * plan.selectedRadiusRemaining remaining hremaining state)
          mdp.horizon le_rfl initialState := by
  constructor
  · exact fun state =>
      confidence.optimalValueRemaining_le_upperValueRemaining
        mdp.horizon le_rfl state
  · exact
      (confidence.expectedRegret_le_two_occupancySelectedRadiusRemaining
        initialState).2.2.2

end EstimatedModelPlan
end MDP
end FiniteHorizonRL
end BanditRLProof
