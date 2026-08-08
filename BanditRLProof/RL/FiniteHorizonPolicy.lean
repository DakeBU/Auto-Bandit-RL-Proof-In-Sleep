import BanditRLProof.RL.FiniteHorizonMDP
import Mathlib.Probability.Kernel.Composition.CompProd
import Mathlib.Probability.Kernel.Composition.MapComap

/-!
# Finite-horizon Markov policy evaluation

This module defines a Markov action kernel at every valid decision stage of a
finite-horizon MDP.  It constructs the induced next-state kernel, the policy
Bellman operator, and the backward finite-horizon policy value.  The terminal
and Bellman recursion theorems are policy-evaluation facts; no maximization,
optimality, occupancy, or regret statement is made here.
-/

open MeasureTheory

universe u v

namespace BanditRLProof
namespace FiniteHorizonRL

variable {State : Type u} {Action : Type v}
    [MeasurableSpace State] [MeasurableSpace Action]
    [Fintype State] [Fintype Action]

/-- A Markov action kernel for every decision stage before `mdp.horizon`. -/
structure MarkovPolicy (mdp : MDP State Action) where
  actionKernel : (stage : Fin mdp.horizon) ->
    ProbabilityTheory.Kernel State Action
  actionKernel_isMarkov : forall stage,
    ProbabilityTheory.IsMarkovKernel (actionKernel stage)

namespace MarkovPolicy

instance instActionKernelIsMarkovKernel
    {mdp : MDP State Action} (policy : MarkovPolicy mdp)
    (stage : Fin mdp.horizon) :
    ProbabilityTheory.IsMarkovKernel (policy.actionKernel stage) :=
  policy.actionKernel_isMarkov stage

/-- State transition kernel induced by sampling the policy action and then the MDP transition. -/
noncomputable def inducedStateKernel
    {mdp : MDP State Action} (policy : MarkovPolicy mdp)
    (stage : Fin mdp.horizon) :
  ProbabilityTheory.Kernel State State :=
  (ProbabilityTheory.Kernel.compProd
      (policy.actionKernel stage) mdp.transition).map Prod.snd

instance instInducedStateKernelIsMarkovKernel
    {mdp : MDP State Action} (policy : MarkovPolicy mdp)
    (stage : Fin mdp.horizon) :
    ProbabilityTheory.IsMarkovKernel (policy.inducedStateKernel stage) := by
  unfold inducedStateKernel
  exact ProbabilityTheory.Kernel.IsMarkovKernel.map _ measurable_snd

/-- Bellman expectation under one stage of the supplied Markov policy. -/
noncomputable def bellman
    {mdp : MDP State Action} (policy : MarkovPolicy mdp)
    (stage : Fin mdp.horizon) (value : State -> Real)
    (state : State) : Real :=
  ∫ action, mdp.bellmanQ value state action
    ∂policy.actionKernel stage state

/-- A measurable continuation value gives a measurable policy Bellman value. -/
theorem measurable_bellman
    {mdp : MDP State Action} (policy : MarkovPolicy mdp)
    (stage : Fin mdp.horizon) {value : State -> Real}
    (hvalue : Measurable value) :
    Measurable (policy.bellman stage value) := by
  exact (mdp.measurable_bellmanQ hvalue).stronglyMeasurable
    |>.integral_kernel_prod_right.measurable

/--
Backward policy value indexed by the number of decisions remaining.  The first
kernel used at `remaining` is chronological stage `horizon - remaining`.
-/
noncomputable def valueRemaining
    {mdp : MDP State Action} (policy : MarkovPolicy mdp) :
    (remaining : Nat) -> remaining <= mdp.horizon -> State -> Real
  | 0, _ => fun _ => 0
  | remaining + 1, hremaining =>
      policy.bellman
        ⟨mdp.horizon - (remaining + 1), by omega⟩
        (policy.valueRemaining remaining (by omega))

/-- The backward policy value is measurable for every valid remaining horizon. -/
theorem measurable_valueRemaining
    {mdp : MDP State Action} (policy : MarkovPolicy mdp)
    (remaining : Nat) (hremaining : remaining <= mdp.horizon) :
    Measurable (policy.valueRemaining remaining hremaining) := by
  induction remaining with
  | zero =>
      simp [valueRemaining]
  | succ remaining ih =>
      rw [valueRemaining]
      exact policy.measurable_bellman _ (ih (by omega))

/-- Policy value at a chronological stage `stage <= horizon`. -/
noncomputable def valueAt
    {mdp : MDP State Action} (policy : MarkovPolicy mdp)
    (stage : Nat) (_hstage : stage <= mdp.horizon) : State -> Real :=
  policy.valueRemaining (mdp.horizon - stage) (Nat.sub_le _ _)

/-- Every chronological policy-value surface is measurable. -/
theorem measurable_valueAt
    {mdp : MDP State Action} (policy : MarkovPolicy mdp)
    (stage : Nat) (hstage : stage <= mdp.horizon) :
    Measurable (policy.valueAt stage hstage) :=
  policy.measurable_valueRemaining _ _

/-- Transport `valueRemaining` across equality of the remaining horizon. -/
theorem valueRemaining_eq_of_eq
    {mdp : MDP State Action} (policy : MarkovPolicy mdp)
    {left right : Nat} (hleft : left <= mdp.horizon)
    (hright : right <= mdp.horizon) (h : left = right) :
    policy.valueRemaining left hleft =
      policy.valueRemaining right hright := by
  subst right
  rfl

/-- The finite-horizon policy value is zero at the terminal stage. -/
@[simp]
theorem valueAt_horizon
    {mdp : MDP State Action} (policy : MarkovPolicy mdp) :
    policy.valueAt mdp.horizon le_rfl = fun _ => 0 := by
  unfold valueAt
  calc
    policy.valueRemaining (mdp.horizon - mdp.horizon) _ =
        policy.valueRemaining 0 (Nat.zero_le _) := by
      apply policy.valueRemaining_eq_of_eq
      exact Nat.sub_self mdp.horizon
    _ = (fun _ => 0) := rfl

/--
Finite-horizon policy evaluation satisfies the Bellman recursion at every
decision stage.
-/
theorem valueAt_bellman
    {mdp : MDP State Action} (policy : MarkovPolicy mdp)
    (stage : Nat) (hstage : stage < mdp.horizon) :
    policy.valueAt stage (Nat.le_of_lt hstage) =
      policy.bellman ⟨stage, hstage⟩
        (policy.valueAt (stage + 1) (by omega)) := by
  have hremaining : mdp.horizon - stage =
      (mdp.horizon - (stage + 1)) + 1 := by
    omega
  have hstageIndex :
      (⟨mdp.horizon - ((mdp.horizon - (stage + 1)) + 1), by omega⟩ :
          Fin mdp.horizon) = ⟨stage, hstage⟩ := by
    apply Fin.ext
    simp
    omega
  calc
    policy.valueAt stage (Nat.le_of_lt hstage) =
        policy.valueRemaining
          ((mdp.horizon - (stage + 1)) + 1) (by omega) := by
      apply policy.valueRemaining_eq_of_eq
      exact hremaining
    _ = policy.bellman
          ⟨mdp.horizon - ((mdp.horizon - (stage + 1)) + 1), by omega⟩
          (policy.valueRemaining (mdp.horizon - (stage + 1)) (by omega)) := by
      rw [valueRemaining]
    _ = policy.bellman ⟨stage, hstage⟩
          (policy.valueAt (stage + 1) (by omega)) := by
      rw [hstageIndex]
      rfl

end MarkovPolicy
end FiniteHorizonRL
end BanditRLProof
