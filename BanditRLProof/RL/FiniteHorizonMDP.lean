import Mathlib.Probability.Kernel.MeasurableIntegral

/-!
# Finite-horizon MDP kernel surface

This module fixes the dependency layer for the first finite-horizon RL leaf.
A finite MDP uses Mathlib Markov kernels for transitions and a measurable Real
reward.  The only derived objects here are the one-step continuation value and
Bellman action value.  Policies, trajectories, value recursion, optimality, and
regret remain downstream.
-/

open MeasureTheory

universe u v

namespace BanditRLProof
namespace FiniteHorizonRL

/--
A finite-state, finite-action, finite-horizon MDP backed by a Mathlib Markov
transition kernel.  The reward is allowed to depend on the current state and
action; stochastic rewards can be added later through a separate reward kernel.
-/
structure MDP
    (State : Type u) (Action : Type v)
    [MeasurableSpace State] [MeasurableSpace Action]
    [Fintype State] [Fintype Action] where
  horizon : Nat
  transition : ProbabilityTheory.Kernel (State × Action) State
  transition_isMarkov : ProbabilityTheory.IsMarkovKernel transition
  reward : State → Action → Real
  measurable_reward : Measurable (Function.uncurry reward)

variable {State : Type u} {Action : Type v}
    [MeasurableSpace State] [MeasurableSpace Action]
    [Fintype State] [Fintype Action]

namespace MDP

instance instTransitionIsMarkovKernel (mdp : MDP State Action) :
    ProbabilityTheory.IsMarkovKernel mdp.transition :=
  mdp.transition_isMarkov

/-- Expected continuation value after taking `action` in `state`. -/
noncomputable def transitionValue
    (mdp : MDP State Action) (value : State → Real)
    (state : State) (action : Action) : Real :=
  ∫ nextState, value nextState ∂mdp.transition (state, action)

/-- One-step Bellman action value `r(s,a) + E[V(S') | s,a]`. -/
noncomputable def bellmanQ
    (mdp : MDP State Action) (value : State → Real)
    (state : State) (action : Action) : Real :=
  mdp.reward state action + mdp.transitionValue value state action

/-- The continuation-value surface is measurable in the state-action pair. -/
theorem measurable_transitionValue
    (mdp : MDP State Action) {value : State → Real}
    (hvalue : Measurable value) :
    Measurable (Function.uncurry (mdp.transitionValue value)) := by
  exact hvalue.stronglyMeasurable.integral_kernel.measurable

/-- The one-step Bellman action value is measurable in the state-action pair. -/
theorem measurable_bellmanQ
    (mdp : MDP State Action) {value : State → Real}
    (hvalue : Measurable value) :
    Measurable (Function.uncurry (mdp.bellmanQ value)) := by
  exact mdp.measurable_reward.add (mdp.measurable_transitionValue hvalue)

/-- With zero continuation value, the Bellman action value is the reward. -/
@[simp]
theorem bellmanQ_zero (mdp : MDP State Action)
    (state : State) (action : Action) :
    mdp.bellmanQ (fun _ => 0) state action = mdp.reward state action := by
  simp [bellmanQ, transitionValue]

end MDP
end FiniteHorizonRL
end BanditRLProof
