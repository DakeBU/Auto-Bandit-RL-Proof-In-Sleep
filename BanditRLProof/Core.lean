import Std

/-!
# Core bandit vocabulary

This file keeps the first project layer dependency-light.  It provides a
small executable language for finite action traces, pull counts, reward sums,
and finite-arm mean models.  Strong probabilistic statements can later import
Mathlib or external libraries without changing this public surface.
-/

namespace BanditRLProof

universe u v

/-- A sequence of actions chosen by a bandit algorithm. -/
abbrev ActionTrace (Action : Type u) := Nat → Action

/-- A sequence of observed rewards. -/
abbrev RewardTrace (Reward : Type v) := Nat → Reward

/-- Number of pulls of action `a` before time `t`. -/
def pullCount [DecidableEq Action] (action : ActionTrace Action) (a : Action) : Nat → Nat
  | 0 => 0
  | t + 1 => pullCount action a t + if action t = a then 1 else 0

@[simp] theorem pullCount_zero [DecidableEq Action]
    (action : ActionTrace Action) (a : Action) :
    pullCount action a 0 = 0 := rfl

@[simp] theorem pullCount_succ [DecidableEq Action]
    (action : ActionTrace Action) (a : Action) (t : Nat) :
    pullCount action a (t + 1) =
      pullCount action a t + if action t = a then 1 else 0 := rfl

/-- Sum of rewards obtained from action `a` before time `t`. -/
def sumRewards [DecidableEq Action] [OfNat Reward 0] [HAdd Reward Reward Reward]
    (action : ActionTrace Action) (reward : RewardTrace Reward) (a : Action) :
    Nat → Reward
  | 0 => 0
  | t + 1 =>
      sumRewards action reward a t + if action t = a then reward t else 0

@[simp] theorem sumRewards_zero [DecidableEq Action] [OfNat Reward 0]
    [HAdd Reward Reward Reward]
    (action : ActionTrace Action) (reward : RewardTrace Reward) (a : Action) :
    sumRewards action reward a 0 = 0 := rfl

@[simp] theorem sumRewards_succ [DecidableEq Action] [OfNat Reward 0]
    [HAdd Reward Reward Reward]
    (action : ActionTrace Action) (reward : RewardTrace Reward) (a : Action) (t : Nat) :
    sumRewards action reward a (t + 1) =
      sumRewards action reward a t + if action t = a then reward t else 0 := rfl

/-- A finite stochastic bandit model represented by the mean reward of each arm. -/
structure FiniteBanditModel (K : Nat) where
  hK : 0 < K
  mean : Fin K → Rat

namespace FiniteBanditModel

/-- A computable argmax-style selector for the best arm. -/
noncomputable def bestArm (model : FiniteBanditModel K) : Fin K :=
  (List.finRange K).foldl
    (fun best arm => if model.mean best < model.mean arm then arm else best)
    ⟨0, model.hK⟩

/-- The mean reward of `bestArm`. -/
noncomputable def bestMean (model : FiniteBanditModel K) : Rat :=
  model.mean model.bestArm

/-- The gap of an arm relative to the selected best arm. -/
noncomputable def gap (model : FiniteBanditModel K) (arm : Fin K) : Rat :=
  if arm = model.bestArm then 0 else model.bestMean - model.mean arm

@[simp] theorem gap_bestArm (model : FiniteBanditModel K) :
    model.gap model.bestArm = 0 := by
  simp [gap]

end FiniteBanditModel

/-- A named policy surface that agents can map to a concrete Lean definition. -/
structure PolicySketch (K : Nat) where
  name : String
  action : Nat → Fin K

/-- Status of a theorem or candidate in the harness memory. -/
inductive CertificateStatus where
  | insight
  | typedContract
  | proofObligation
  | leanCompiled
  | rejected
deriving Repr, DecidableEq

end BanditRLProof
