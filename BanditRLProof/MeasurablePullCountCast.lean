import Mathlib.Data.Nat.Cast.Basic
import Mathlib.MeasureTheory.Group.Arithmetic
import BanditRLProof.MeasurablePullCount

/-!
# Measurability of scalar-casted pull counts

This module proves scalar-valued measurability of local pull counts.  It stays
before expectation, while matching the scalar form used by regret decompositions.
-/

universe u v w

namespace BanditRLProof

/--
The local recursive pull count, cast into an additive scalar, is measurable at
each finite horizon.

This is the `MEAS-PULLCOUNT-CAST` bridge.  Later expectation leaves can
instantiate `Beta := Rat` without changing the proof.
-/
theorem measurable_natCast_pullCount
    {Omega : Type u} {Action : Type v} {Beta : Type w}
    [MeasurableSpace Omega] [MeasurableSpace Action]
    [MeasurableSingletonClass Action]
    [MeasurableSpace Beta] [AddCommMonoidWithOne Beta] [MeasurableAdd₂ Beta]
    [DecidableEq Action]
    (action : Omega -> ActionTrace Action)
    (haction : forall t : Nat,
      Measurable (fun omega : Omega => action omega t))
    (a : Action) (n : Nat) :
    Measurable
      (fun omega : Omega =>
        ((pullCount (action omega) a n : Nat) : Beta)) := by
  induction n with
  | zero =>
      simp [pullCount]
  | succ n ih =>
      have hevent :
          MeasurableSet {omega : Omega | action omega n = a} :=
        measurableSet_actionTrace_eval_eq action haction a n
      have hinc :
          Measurable
            (fun omega : Omega =>
              if action omega n = a then (1 : Beta) else 0) :=
        Measurable.ite hevent measurable_const measurable_const
      have hadd :
          Measurable
            (fun omega : Omega =>
              ((pullCount (action omega) a n : Nat) : Beta)
                + (if action omega n = a then (1 : Beta) else 0)) :=
        ih.add hinc
      have hfun :
          (fun omega : Omega =>
              ((pullCount (action omega) a (Nat.succ n) : Nat) : Beta))
            =
          (fun omega : Omega =>
              ((pullCount (action omega) a n : Nat) : Beta)
                + (if action omega n = a then (1 : Beta) else 0)) := by
        funext omega
        by_cases h : action omega n = a
        · simp [pullCount_succ, h]
        · simp [pullCount_succ, h]
      rw [hfun]
      exact hadd

end BanditRLProof
