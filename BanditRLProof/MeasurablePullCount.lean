import Mathlib.MeasureTheory.Group.Arithmetic
import BanditRLProof.MeasureFoundation
import BanditRLProof.LeafLemmas

/-!
# Measurability of local pull counts

This module proves that the recursive pull-count process is measurable when the
action trace is timewise measurable.  It stays before expectation and before
scalar-cast pull-count identities.
-/

universe u v

namespace BanditRLProof

/--
The local recursive pull count is measurable at each finite horizon.

This is the `MEAS-PULLCOUNT` bridge.  It prepares expected pull-count leaves
without introducing measures, integration, filtration, or concentration.
-/
theorem measurable_pullCount
    {Omega : Type u} {Action : Type v}
    [MeasurableSpace Omega] [MeasurableSpace Action]
    [MeasurableSingletonClass Action]
    [MeasurableSpace Nat] [MeasurableAdd₂ Nat]
    [DecidableEq Action]
    (action : Omega -> ActionTrace Action)
    (haction : forall t : Nat,
      Measurable (fun omega : Omega => action omega t))
    (a : Action) (n : Nat) :
    Measurable
      (fun omega : Omega => pullCount (action omega) a n) := by
  induction n with
  | zero =>
      simp [pullCount]
  | succ n ih =>
      have hevent :
          MeasurableSet {omega : Omega | action omega n = a} :=
        measurableSet_actionTrace_eval_eq action haction a n
      have hind :
          Measurable
            (fun omega : Omega =>
              if action omega n = a then (1 : Nat) else 0) :=
        Measurable.ite hevent measurable_const measurable_const
      have hadd :
          Measurable
            (fun omega : Omega =>
              pullCount (action omega) a n
                + if action omega n = a then (1 : Nat) else 0) :=
        ih.add hind
      simpa [pullCount_succ] using hadd

end BanditRLProof
