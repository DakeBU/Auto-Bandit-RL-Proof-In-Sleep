import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import BanditRLProof.MathlibWrappers

/-!
# Pull-count decompositions over finite action spaces

This module contains deterministic count identities that consume the
Mathlib-backed `Finset.range` wrappers.  It stays below the probability and
algorithm-specific layers.
-/

namespace BanditRLProof

section PullCountPartition

variable {Action : Type u} [Fintype Action] [DecidableEq Action]
variable (action : ActionTrace Action) (t : Nat)

/--
The pull counts over a finite action space partition the time horizon.

This is the deterministic `PULLCOUNT-SUM-TIME` leaf.  It consumes the compiled
`pullCount` Finset wrapper and Mathlib's finite fiber-cardinality theorem.
-/
theorem finset_sum_pullCount_eq_time :
    (Finset.univ : Finset Action).sum
      (fun a : Action => pullCount action a t) = t := by
  calc
    (Finset.univ : Finset Action).sum
        (fun a : Action => pullCount action a t)
        = (Finset.univ : Finset Action).sum
            (fun a : Action =>
              ((Finset.range t).filter (fun s : Nat => action s = a)).card) := by
          apply Finset.sum_congr rfl
          intro a _ha
          rw [pullCount_eq_finset_filter_card]
    _ = (Finset.range t).card := by
          exact (Finset.card_eq_sum_card_fiberwise
            (f := action)
            (s := Finset.range t)
            (t := (Finset.univ : Finset Action))
            (by intro _s _hs; simp)).symm
    _ = t := by
          simp

/--
Reindex a sum over action times by arm and the arm's prior pull count.

At a time `s`, the value `pullCount action (action s) s` is the zero-based
index of that pull among occurrences of the selected arm. This is the local
Mathlib-backed counterpart of LML's `sum_comp_pullCount` bookkeeping lemma.
-/
theorem finset_sum_comp_pullCount
    {R : Type v} [AddCommMonoid R] (f : Nat -> R) :
    ∑ s ∈ Finset.range t, f (pullCount action (action s) s) =
      ∑ a : Action, ∑ j ∈ Finset.range (pullCount action a t), f j := by
  induction t with
  | zero => simp
  | succ n ih =>
      have hf : f (pullCount action (action n) n) =
          ∑ a : Action,
            if action n = a then f (pullCount action a n) else 0 := by
        exact (Fintype.sum_ite_eq (action n)
          (fun a => f (pullCount action a n))).symm
      simp_rw [Finset.sum_range_succ, ih, hf,
        ← Finset.sum_add_distrib, pullCount_succ]
      apply Finset.sum_congr rfl
      intro a _ha
      by_cases h : action n = a
      · simp [h, Finset.sum_range_succ]
      · simp [h]

end PullCountPartition

end BanditRLProof
