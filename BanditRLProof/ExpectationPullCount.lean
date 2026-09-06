import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Nat.Cast.Basic
import BanditRLProof.ExpectationSums
import BanditRLProof.LeafLemmas

/-!
# Lower-integral pull-count identities

This module connects the `ENNReal` finite-sum lower-integral bridge back to the
local recursive `pullCount` quantity.  It remains before Bochner expectation,
expected regret, filtrations, kernels, or concentration.
-/

universe u v

open MeasureTheory
open scoped ENNReal

namespace BanditRLProof

private theorem ennreal_natCast_pullCount_eq_finset_range_indicator_one
    {Omega : Type u} {Action : Type v} [DecidableEq Action]
    (action : Omega -> ActionTrace Action) (a : Action) (n : Nat)
    (omega : Omega) :
    ((pullCount (action omega) a n : Nat) : ENNReal) =
      (Finset.range n).sum
        (fun t : Nat =>
          (({omega' : Omega | action omega' t = a} : Set Omega).indicator
            (1 : Omega -> ENNReal)) omega) := by
  induction n with
  | zero =>
      simp [pullCount]
  | succ n ih =>
      by_cases h : action omega n = a
      · simp [pullCount_succ, Finset.sum_range_succ, h, ih, Nat.cast_add]
      · simp [pullCount_succ, Finset.sum_range_succ, h, ih]

/--
The lower integral of the scalar-casted local pull count is the finite sum of
the corresponding action-event measures.

This is the `EXP-PULLCOUNT-LINTEGRAL` bridge.  It connects the compiled
finite-sum lower-integral identity to the recursive `pullCount` surface without
choosing a Bochner expectation or probability-measure interface.
-/
theorem lintegral_natCast_pullCount_eq_sum_measure_actionTrace_eval_eq
    {Omega : Type u} {Action : Type v}
    [MeasurableSpace Omega] [MeasurableSpace Action]
    [MeasurableSingletonClass Action] [DecidableEq Action]
    (mu : Measure Omega)
    (action : Omega -> ActionTrace Action)
    (haction : forall t : Nat,
      Measurable (fun omega : Omega => action omega t))
    (a : Action) (n : Nat) :
    MeasureTheory.lintegral mu
      (fun omega : Omega =>
        ((pullCount (action omega) a n : Nat) : ENNReal))
      =
    (Finset.range n).sum
      (fun t : Nat =>
        mu {omega : Omega | action omega t = a}) := by
  have hfun :
      (fun omega : Omega =>
          ((pullCount (action omega) a n : Nat) : ENNReal))
        =
      (fun omega : Omega =>
        (Finset.range n).sum
          (fun t : Nat =>
            (({omega' : Omega | action omega' t = a} : Set Omega).indicator
              (1 : Omega -> ENNReal)) omega)) := by
    funext omega
    exact ennreal_natCast_pullCount_eq_finset_range_indicator_one
      action a n omega
  rw [hfun]
  exact lintegral_finset_sum_actionTrace_eval_eq_indicator_one
    (mu := mu)
    (action := action)
    (haction := haction)
    (a := a)
    (s := Finset.range n)

end BanditRLProof
