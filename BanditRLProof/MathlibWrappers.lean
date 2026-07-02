import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Field.Rat
import Mathlib.Data.Finset.Card
import BanditRLProof.LeafLemmas

/-!
# Mathlib-backed finite bookkeeping wrappers

This module is the first intentional Mathlib interop layer.  The dependency-light
lemmas remain in `BanditRLProof.LeafLemmas`; this file only bridges those local
recursive definitions to Mathlib-facing finite containers.
-/

namespace BanditRLProof

section PullCountFinset

variable {Action : Type u} [DecidableEq Action]
variable (action : ActionTrace Action) (a : Action) (t : Nat)

/--
The recursive pull count equals the cardinality of the matching arm times in
`Finset.range t`.

This is the first Mathlib-backed wrapper leaf.  It is intentionally kept
separate from the dependency-light `List.range` bridge.
-/
theorem pullCount_eq_finset_filter_card :
    pullCount action a t =
      ((Finset.range t).filter (fun s : Nat => action s = a)).card := by
  induction t with
  | zero =>
      simp [pullCount]
  | succ t ih =>
      rw [pullCount_succ, ih]
      by_cases h : action t = a
      · have ht :
            Not (Membership.mem
              ((Finset.range t).filter (fun s : Nat => action s = a)) t) := by
          simp [Finset.mem_range]
        simp [Finset.range_add_one, Finset.filter_insert, h, ht]
      · simp [Finset.range_add_one, Finset.filter_insert, h]

end PullCountFinset

section SumRewardsFinset

variable {Action Reward : Type u} [DecidableEq Action]
variable [AddCommMonoid Reward]
variable (action : ActionTrace Action) (reward : RewardTrace Reward)
variable (a : Action) (t : Nat)

/--
The recursive selected reward sum equals the Mathlib finite sum over selected
time points in `Finset.range t`.

The local recursive definition only needs weak `0` and `+` operations.  This
Mathlib-facing wrapper strengthens the algebra contract to `AddCommMonoid`
because `Finset.sum` is commutative and the insertion proof swaps summand
order.
-/
theorem sumRewards_eq_finset_filter_sum :
    sumRewards action reward a t =
      ((Finset.range t).filter (fun s : Nat => action s = a)).sum
        (fun s : Nat => reward s) := by
  induction t with
  | zero =>
      simp [sumRewards]
  | succ t ih =>
      rw [sumRewards_succ, ih]
      by_cases h : action t = a
      · have ht :
            Not (Membership.mem
              ((Finset.range t).filter (fun s : Nat => action s = a)) t) := by
          simp [Finset.mem_range]
        simp [Finset.range_add_one, Finset.filter_insert, h, ht, add_comm]
      · simp [Finset.range_add_one, Finset.filter_insert, h]

end SumRewardsFinset

section PseudoRegretFinset

variable (model : FiniteBanditModel K) (action : Nat -> Fin K) (t : Nat)

/--
The recursive pseudo-regret equals the Mathlib finite sum of selected gaps over
`Finset.range t`.

This is the Rat-valued finite-sum wrapper.  It deliberately comes before the
generic reward-sum wrapper because `Finset.sum` only needs the Mathlib
`AddCommMonoid Rat` instance supplied by the Rat algebra imports.
-/
theorem pseudoRegret_eq_finset_sum :
    pseudoRegret model action t =
      (Finset.range t).sum (fun s : Nat => model.gap (action s)) := by
  induction t with
  | zero =>
      simp [pseudoRegret]
  | succ t ih =>
      rw [pseudoRegret_succ, ih]
      simp [Finset.sum_range_succ]

end PseudoRegretFinset

end BanditRLProof
