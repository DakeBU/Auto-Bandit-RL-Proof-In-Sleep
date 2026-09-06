import BanditRLProof.RL.FiniteHorizonEstimatedModelCertificate

/-!
# Coordinate confidence for finite-horizon estimated models

This module turns finite-state singleton transition-mass errors into the
transition-expectation confidence consumed by the estimated-model optimistic
regret route.  The only value regularity required is an absolute envelope for
the recursively generated tail upper value.
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

/--
On a finite measurable space, coordinate bounds on singleton masses control
the expectation error of every pointwise-enveloped real value.
-/
theorem abs_integral_sub_integral_le_sum_coordinateRadius_mul_envelope
    (estimated trueMeasure : Measure State)
    [IsFiniteMeasure estimated] [IsFiniteMeasure trueMeasure]
    (value coordinateRadius : State -> Real) (envelope : Real)
    (hcoordinate : forall state,
      |estimated.real {state} - trueMeasure.real {state}| <=
        coordinateRadius state)
    (hvalue : forall state, |value state| <= envelope) :
    |(∫ state, value state ∂estimated) -
        ∫ state, value state ∂trueMeasure| <=
      ∑ state, coordinateRadius state * envelope := by
  rw [integral_fintype
    (integrable_of_fintype _ _ (measurable_of_finite value))]
  rw [integral_fintype
    (integrable_of_fintype _ _ (measurable_of_finite value))]
  simp only [smul_eq_mul]
  calc
    |(∑ state, estimated.real {state} * value state) -
        ∑ state, trueMeasure.real {state} * value state| =
        |∑ state,
          (estimated.real {state} - trueMeasure.real {state}) *
            value state| := by
      congr 1
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro state _
      ring
    _ <= ∑ state,
        |(estimated.real {state} - trueMeasure.real {state}) *
          value state| :=
      Finset.abs_sum_le_sum_abs _ _
    _ <= ∑ state, coordinateRadius state * envelope := by
      apply Finset.sum_le_sum
      intro state _
      rw [abs_mul]
      calc
        |estimated.real {state} - trueMeasure.real {state}| *
              |value state| <=
            coordinateRadius state * |value state| :=
          mul_le_mul_of_nonneg_right (hcoordinate state) (abs_nonneg _)
        _ <= coordinateRadius state * envelope :=
          mul_le_mul_of_nonneg_left (hvalue state)
            ((abs_nonneg _).trans (hcoordinate state))

namespace MDP
namespace EstimatedModelPlan

/--
Finite-state coordinate confidence sufficient for the recursive optimistic
model route.  The transition radius may be any upper bound on the displayed
coordinate sum, so later concentration producers can choose their own radii.
-/
structure CoordinateConfidence
    {mdp : MDP State Action} (plan : EstimatedModelPlan mdp) where
  transitionCoordinateRadius :
    Fin mdp.horizon -> State -> Action -> State -> Real
  valueEnvelope : Nat -> Real
  rewardError_le_radius : forall (stage : Fin mdp.horizon)
    (state : State) (action : Action),
    |plan.estimatedReward stage state action - mdp.reward state action| <=
      plan.rewardRadius stage state action
  transitionCoordinateError_le_radius : forall (remaining : Nat)
    (hremaining : remaining + 1 <= mdp.horizon)
    (state : State) (action : Action) (nextState : State),
    |(plan.estimatedTransition
          (mdp.decisionStageRemaining remaining hremaining)
          (state, action)).real {nextState} -
        (mdp.transition (state, action)).real {nextState}| <=
      transitionCoordinateRadius
        (mdp.decisionStageRemaining remaining hremaining)
        state action nextState
  upperValue_abs_le_envelope : forall (remaining : Nat)
    (hremaining : remaining + 1 <= mdp.horizon) (state : State),
    |plan.upperValueRemaining remaining (by omega) state| <=
      valueEnvelope remaining
  transitionRadius_cover : forall (remaining : Nat)
    (hremaining : remaining + 1 <= mdp.horizon)
    (state : State) (action : Action),
    (∑ nextState,
        transitionCoordinateRadius
            (mdp.decisionStageRemaining remaining hremaining)
            state action nextState *
          valueEnvelope remaining) <=
      plan.transitionRadius
        (mdp.decisionStageRemaining remaining hremaining) state action

/-- Coordinate transition confidence implies the recursive Bellman error bound. -/
theorem CoordinateConfidence.transitionError_le_radius
    {mdp : MDP State Action} {plan : EstimatedModelPlan mdp}
    (confidence : plan.CoordinateConfidence) (remaining : Nat)
    (hremaining : remaining + 1 <= mdp.horizon)
    (state : State) (action : Action) :
    |plan.transitionValue (mdp.decisionStageRemaining remaining hremaining)
          (plan.upperValueRemaining remaining (by omega)) state action -
        mdp.transitionValue
          (plan.upperValueRemaining remaining (by omega)) state action| <=
      plan.transitionRadius
        (mdp.decisionStageRemaining remaining hremaining) state action := by
  unfold transitionValue MDP.transitionValue
  exact
    (abs_integral_sub_integral_le_sum_coordinateRadius_mul_envelope
      (plan.estimatedTransition
        (mdp.decisionStageRemaining remaining hremaining) (state, action))
      (mdp.transition (state, action))
      (plan.upperValueRemaining remaining (by omega))
      (confidence.transitionCoordinateRadius
        (mdp.decisionStageRemaining remaining hremaining) state action)
      (confidence.valueEnvelope remaining)
      (confidence.transitionCoordinateError_le_radius
        remaining hremaining state action)
      (confidence.upperValue_abs_le_envelope remaining hremaining)).trans
        (confidence.transitionRadius_cover
          remaining hremaining state action)

/-- Package coordinate confidence as the existing estimated-model confidence. -/
def CoordinateConfidence.toConfidence
    {mdp : MDP State Action} {plan : EstimatedModelPlan mdp}
    (confidence : plan.CoordinateConfidence) : plan.Confidence where
  rewardError_le_radius := confidence.rewardError_le_radius
  transitionError_le_radius := confidence.transitionError_le_radius

/--
Route endpoint: coordinate model confidence gives global optimism and the
compiled selected-radius single-episode expected-regret bound.
-/
theorem CoordinateConfidence.optimism_and_expectedRegret_le_two_occupancySelectedRadiusRemaining
    {mdp : MDP State Action} {plan : EstimatedModelPlan mdp}
    (confidence : plan.CoordinateConfidence) (initialState : Measure State)
    [IsProbabilityMeasure initialState] :
    (forall state,
      mdp.optimalValueRemaining mdp.horizon le_rfl state <=
        plan.upperValueRemaining mdp.horizon le_rfl state) /\
      plan.optimisticPolicy.expectedRegret initialState <=
        plan.optimisticPolicy.occupancySumRemaining
          (fun remaining hremaining state =>
            2 * plan.selectedRadiusRemaining remaining hremaining state)
          mdp.horizon le_rfl initialState :=
  confidence.toConfidence
    |>.optimism_and_expectedRegret_le_two_occupancySelectedRadiusRemaining
      initialState

end EstimatedModelPlan
end MDP
end FiniteHorizonRL
end BanditRLProof
