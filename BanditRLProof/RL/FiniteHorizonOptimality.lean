import BanditRLProof.RL.FiniteHorizonTrajectory

/-!
# Finite-horizon Bellman optimality

This module adds finite-action maximization to the compiled policy-evaluation
route.  On a finite discrete state space, the pointwise finite argmax is a
measurable deterministic selector.  The resulting greedy Markov policy attains
the backward optimal value, which dominates every Markov policy value.
-/

open MeasureTheory

universe u v

namespace BanditRLProof
namespace FiniteHorizonRL

variable {State : Type u} {Action : Type v}
    [MeasurableSpace State] [MeasurableSpace Action]
    [Fintype State] [Fintype Action]
    [MeasurableSingletonClass State] [Nonempty Action]

namespace MDP

/-- A finite action maximizing the one-step Bellman action value. -/
noncomputable def optimalAction (mdp : MDP State Action)
    (value : State -> Real) (state : State) : Action :=
  Classical.choose
    (Finite.exists_max (fun action => mdp.bellmanQ value state action))

omit [MeasurableSingletonClass State] in
/-- The selected finite action dominates every Bellman action value. -/
theorem bellmanQ_le_optimalAction
    (mdp : MDP State Action) (value : State -> Real)
    (state : State) (action : Action) :
    mdp.bellmanQ value state action <=
      mdp.bellmanQ value state (mdp.optimalAction value state) := by
  exact Classical.choose_spec
    (Finite.exists_max (fun action => mdp.bellmanQ value state action)) action

/-- The finite-state maximizing selector is measurable. -/
theorem measurable_optimalAction
    (mdp : MDP State Action) (value : State -> Real) :
    Measurable (mdp.optimalAction value) :=
  measurable_of_finite _

/-- Pointwise finite-action Bellman maximum. -/
noncomputable def optimalBellman (mdp : MDP State Action)
    (value : State -> Real) (state : State) : Real :=
  mdp.bellmanQ value state (mdp.optimalAction value state)

omit [MeasurableSingletonClass State] in
/-- Every action value is bounded by the finite-action Bellman maximum. -/
theorem bellmanQ_le_optimalBellman
    (mdp : MDP State Action) (value : State -> Real)
    (state : State) (action : Action) :
    mdp.bellmanQ value state action <= mdp.optimalBellman value state :=
  mdp.bellmanQ_le_optimalAction value state action

/-- The optimal Bellman value is measurable on the finite discrete state space. -/
theorem measurable_optimalBellman
    (mdp : MDP State Action) (value : State -> Real) :
    Measurable (mdp.optimalBellman value) :=
  measurable_of_finite _

omit [Nonempty Action] in
/-- Transition expectation is monotone in the continuation value. -/
theorem transitionValue_mono
    (mdp : MDP State Action) {left right : State -> Real}
    (hle : forall state, left state <= right state)
    (state : State) (action : Action) :
    mdp.transitionValue left state action <=
      mdp.transitionValue right state action := by
  unfold transitionValue
  apply integral_mono
  · exact integrable_of_fintype _ _ (measurable_of_finite _)
  · exact integrable_of_fintype _ _ (measurable_of_finite _)
  · exact hle

omit [Nonempty Action] in
/-- Bellman action values are monotone in their continuation value. -/
theorem bellmanQ_mono
    (mdp : MDP State Action) {left right : State -> Real}
    (hle : forall state, left state <= right state)
    (state : State) (action : Action) :
    mdp.bellmanQ left state action <= mdp.bellmanQ right state action := by
  unfold bellmanQ
  exact add_le_add (le_refl _) (mdp.transitionValue_mono hle state action)

/-- Backward optimal value indexed by the number of decisions remaining. -/
noncomputable def optimalValueRemaining (mdp : MDP State Action) :
    (remaining : Nat) -> remaining <= mdp.horizon -> State -> Real
  | 0, _ => fun _ => 0
  | remaining + 1, hremaining =>
      mdp.optimalBellman
        (mdp.optimalValueRemaining remaining (by omega))

/-- Every backward optimal-value surface is measurable. -/
theorem measurable_optimalValueRemaining
    (mdp : MDP State Action) (remaining : Nat)
    (hremaining : remaining <= mdp.horizon) :
    Measurable (mdp.optimalValueRemaining remaining hremaining) :=
  measurable_of_finite _

/-- Optimal value at chronological stage `stage <= horizon`. -/
noncomputable def optimalValueAt (mdp : MDP State Action)
    (stage : Nat) (_hstage : stage <= mdp.horizon) : State -> Real :=
  mdp.optimalValueRemaining (mdp.horizon - stage) (Nat.sub_le _ _)

/-- Every chronological optimal-value surface is measurable. -/
theorem measurable_optimalValueAt
    (mdp : MDP State Action) (stage : Nat)
    (hstage : stage <= mdp.horizon) :
    Measurable (mdp.optimalValueAt stage hstage) :=
  measurable_of_finite _

omit [MeasurableSingletonClass State] in
/-- Transport the dependent optimal-value recursion across equal remaining horizons. -/
theorem optimalValueRemaining_eq_of_eq
    (mdp : MDP State Action) {left right : Nat}
    (hleft : left <= mdp.horizon) (hright : right <= mdp.horizon)
    (h : left = right) :
    mdp.optimalValueRemaining left hleft =
      mdp.optimalValueRemaining right hright := by
  subst right
  rfl

omit [MeasurableSingletonClass State] in
/-- The optimal value is zero at the terminal stage. -/
@[simp]
theorem optimalValueAt_horizon (mdp : MDP State Action) :
    mdp.optimalValueAt mdp.horizon le_rfl = fun _ => 0 := by
  unfold optimalValueAt
  calc
    mdp.optimalValueRemaining (mdp.horizon - mdp.horizon) _ =
        mdp.optimalValueRemaining 0 (Nat.zero_le _) := by
      apply mdp.optimalValueRemaining_eq_of_eq
      exact Nat.sub_self mdp.horizon
    _ = (fun _ => 0) := rfl

omit [MeasurableSingletonClass State] in
/-- Finite-action Bellman recursion for the chronological optimal value. -/
theorem optimalValueAt_bellman
    (mdp : MDP State Action) (stage : Nat)
    (hstage : stage < mdp.horizon) :
    mdp.optimalValueAt stage (Nat.le_of_lt hstage) =
      mdp.optimalBellman
        (mdp.optimalValueAt (stage + 1) (by omega)) := by
  have hremaining : mdp.horizon - stage =
      (mdp.horizon - (stage + 1)) + 1 := by
    omega
  calc
    mdp.optimalValueAt stage (Nat.le_of_lt hstage) =
        mdp.optimalValueRemaining
          ((mdp.horizon - (stage + 1)) + 1) (by omega) := by
      apply mdp.optimalValueRemaining_eq_of_eq
      exact hremaining
    _ = mdp.optimalBellman
          (mdp.optimalValueRemaining
            (mdp.horizon - (stage + 1)) (by omega)) := by
      rw [optimalValueRemaining]
    _ = mdp.optimalBellman
          (mdp.optimalValueAt (stage + 1) (by omega)) := rfl

end MDP

namespace MarkovPolicy

omit [Nonempty Action] in
/-- Policy Bellman expectation is monotone in the continuation value. -/
theorem bellman_mono
    {mdp : MDP State Action} (policy : MarkovPolicy mdp)
    (stage : Fin mdp.horizon) {left right : State -> Real}
    (hle : forall state, left state <= right state) (state : State) :
    policy.bellman stage left state <= policy.bellman stage right state := by
  unfold bellman
  have hleft : Measurable
      (fun action => mdp.bellmanQ left state action) :=
    (mdp.measurable_bellmanQ (measurable_of_finite left)).comp
      (measurable_const.prodMk measurable_id)
  have hright : Measurable
      (fun action => mdp.bellmanQ right state action) :=
    (mdp.measurable_bellmanQ (measurable_of_finite right)).comp
      (measurable_const.prodMk measurable_id)
  apply integral_mono
  · exact integrable_of_fintype _ _ hleft
  · exact integrable_of_fintype _ _ hright
  · exact fun action => mdp.bellmanQ_mono hle state action

/-- Every policy Bellman expectation is bounded by the finite-action maximum. -/
theorem bellman_le_optimalBellman
    {mdp : MDP State Action} (policy : MarkovPolicy mdp)
    (stage : Fin mdp.horizon) (value : State -> Real) (state : State) :
    policy.bellman stage value state <= mdp.optimalBellman value state := by
  unfold bellman
  have hvalue : Measurable
      (fun action => mdp.bellmanQ value state action) :=
    (mdp.measurable_bellmanQ (measurable_of_finite value)).comp
      (measurable_const.prodMk measurable_id)
  calc
    (∫ action, mdp.bellmanQ value state action
        ∂policy.actionKernel stage state) <=
        ∫ _action, mdp.optimalBellman value state
          ∂policy.actionKernel stage state := by
      apply integral_mono
      · exact integrable_of_fintype _ _ hvalue
      · exact integrable_const _
      · exact fun action => mdp.bellmanQ_le_optimalBellman value state action
    _ = mdp.optimalBellman value state := by simp

/-- Every Markov policy value is pointwise bounded by the optimal value. -/
theorem valueAt_le_optimalValueAt
    {mdp : MDP State Action} (policy : MarkovPolicy mdp)
    (stage : Nat) (hstage : stage <= mdp.horizon) (state : State) :
    policy.valueAt stage hstage state <=
      mdp.optimalValueAt stage hstage state := by
  exact Nat.decreasingInduction
    (n := mdp.horizon)
    (motive := fun stage hstage => forall state,
      policy.valueAt stage hstage state <=
        mdp.optimalValueAt stage hstage state)
    (fun current hcurrent ih state => by
      rw [policy.valueAt_bellman current hcurrent]
      rw [mdp.optimalValueAt_bellman current hcurrent]
      exact
        (policy.bellman_mono ⟨current, hcurrent⟩
          (fun nextState => ih nextState) state).trans
        (policy.bellman_le_optimalBellman ⟨current, hcurrent⟩
          (mdp.optimalValueAt (current + 1) (by omega)) state))
    (by
      intro state
      rw [policy.valueAt_horizon, mdp.optimalValueAt_horizon])
    hstage state

end MarkovPolicy

namespace MDP

/-- Greedy deterministic Markov policy for the backward optimal value. -/
noncomputable def optimalPolicy (mdp : MDP State Action) : MarkovPolicy mdp where
  actionKernel stage :=
    ProbabilityTheory.Kernel.deterministic
      (mdp.optimalAction
        (mdp.optimalValueAt (stage + 1) (Nat.succ_le_of_lt stage.isLt)))
      (mdp.measurable_optimalAction _)
  actionKernel_isMarkov := by
    intro stage
    infer_instance

/-- One greedy-policy Bellman step is exactly the finite-action maximum. -/
theorem optimalPolicy_bellman_eq_optimalBellman
    (mdp : MDP State Action) (stage : Fin mdp.horizon) (state : State) :
    mdp.optimalPolicy.bellman stage
        (mdp.optimalValueAt (stage + 1) (Nat.succ_le_of_lt stage.isLt)) state =
      mdp.optimalBellman
        (mdp.optimalValueAt (stage + 1) (Nat.succ_le_of_lt stage.isLt)) state := by
  unfold MarkovPolicy.bellman optimalPolicy
  rw [ProbabilityTheory.Kernel.deterministic_apply]
  rw [integral_dirac']
  · rfl
  · exact
      ((mdp.measurable_bellmanQ
          (mdp.measurable_optimalValueAt (stage + 1)
            (Nat.succ_le_of_lt stage.isLt))).comp
        (measurable_const.prodMk measurable_id)).stronglyMeasurable

/-- The measurable greedy deterministic policy attains the optimal value at every stage. -/
theorem optimalPolicy_valueAt_eq_optimalValueAt
    (mdp : MDP State Action) (stage : Nat)
    (hstage : stage <= mdp.horizon) :
    mdp.optimalPolicy.valueAt stage hstage =
      mdp.optimalValueAt stage hstage := by
  exact Nat.decreasingInduction
    (n := mdp.horizon)
    (motive := fun stage hstage =>
      mdp.optimalPolicy.valueAt stage hstage =
        mdp.optimalValueAt stage hstage)
    (fun current hcurrent ih => by
      change mdp.optimalPolicy.valueAt current _ =
        mdp.optimalValueAt current _
      rw [mdp.optimalPolicy.valueAt_bellman current hcurrent]
      rw [mdp.optimalValueAt_bellman current hcurrent]
      rw [ih]
      funext state
      exact mdp.optimalPolicy_bellman_eq_optimalBellman
        ⟨current, hcurrent⟩ state)
    (by
      change mdp.optimalPolicy.valueAt mdp.horizon _ =
        mdp.optimalValueAt mdp.horizon _
      rw [mdp.optimalPolicy.valueAt_horizon, mdp.optimalValueAt_horizon])
    hstage

/--
Route endpoint: the backward Bellman value dominates every Markov policy and
is attained by the measurable greedy deterministic policy.
-/
theorem optimalValueAt_dominates_and_is_attained
    (mdp : MDP State Action) :
    (forall (policy : MarkovPolicy mdp) (stage : Nat)
      (hstage : stage <= mdp.horizon) (state : State),
        policy.valueAt stage hstage state <=
          mdp.optimalValueAt stage hstage state) /\
      (exists policy : MarkovPolicy mdp,
        forall (stage : Nat) (hstage : stage <= mdp.horizon),
          policy.valueAt stage hstage = mdp.optimalValueAt stage hstage) := by
  constructor
  · intro policy stage hstage state
    exact policy.valueAt_le_optimalValueAt stage hstage state
  · exact ⟨mdp.optimalPolicy, mdp.optimalPolicy_valueAt_eq_optimalValueAt⟩

end MDP
end FiniteHorizonRL
end BanditRLProof
