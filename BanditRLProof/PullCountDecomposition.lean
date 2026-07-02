import Mathlib.Data.Fintype.Basic
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

end PullCountPartition

end BanditRLProof
