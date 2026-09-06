import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import BanditRLProof.ExpectationFoundation

/-!
# Lower-integral finite sums of pull-event indicators

This module proves the finite-sum lower-integral bridge for pull-event
indicators.  It stays in `ENNReal` and arbitrary measures, before Bochner
expectation, pull-count identities, filtrations, kernels, or concentration.
-/

universe u v

open MeasureTheory
open scoped ENNReal

namespace BanditRLProof

/--
The lower integral of a finite sum of pull-event indicators is the finite sum
of the corresponding event measures.

This is the `EXP-FINSET-INDICATOR-PULL` bridge.  It isolates lower-integral
finite-additivity before connecting the finite sum to `pullCount`.
-/
theorem lintegral_finset_sum_actionTrace_eval_eq_indicator_one
    {Omega : Type u} {Action : Type v}
    [MeasurableSpace Omega] [MeasurableSpace Action]
    [MeasurableSingletonClass Action]
    (mu : Measure Omega)
    (action : Omega -> ActionTrace Action)
    (haction : forall t : Nat,
      Measurable (fun omega : Omega => action omega t))
    (a : Action) (s : Finset Nat) :
    MeasureTheory.lintegral mu
      (fun omega : Omega =>
        s.sum
          (fun t : Nat =>
            (({omega' : Omega | action omega' t = a} : Set Omega).indicator
              (1 : Omega -> ENNReal)) omega))
      =
    s.sum
      (fun t : Nat =>
        mu {omega : Omega | action omega t = a}) := by
  have hmeas :
      forall t : Nat, t ∈ s ->
        Measurable
          (fun omega : Omega =>
            (({omega' : Omega | action omega' t = a} : Set Omega).indicator
              (1 : Omega -> ENNReal)) omega) := by
    intro t _ht
    exact measurable_actionTrace_eval_eq_indicator_const
      (action := action)
      (hmeas := haction)
      (a := a)
      (t := t)
      (c := (1 : ENNReal))
  calc
    MeasureTheory.lintegral mu
      (fun omega : Omega =>
        s.sum
          (fun t : Nat =>
            (({omega' : Omega | action omega' t = a} : Set Omega).indicator
              (1 : Omega -> ENNReal)) omega))
        =
      s.sum
        (fun t : Nat =>
          MeasureTheory.lintegral mu
            (fun omega : Omega =>
              (({omega' : Omega | action omega' t = a} : Set Omega).indicator
                (1 : Omega -> ENNReal)) omega)) := by
          simpa [Finset.sum_apply] using
            (@MeasureTheory.lintegral_finset_sum
              Omega Nat _ mu s
              (f := fun t omega =>
                (({omega' : Omega | action omega' t = a} : Set Omega).indicator
                  (1 : Omega -> ENNReal)) omega)
              hmeas)
    _ =
      s.sum
        (fun t : Nat =>
          mu {omega : Omega | action omega t = a}) := by
          apply Finset.sum_congr rfl
          intro t _ht
          exact lintegral_actionTrace_eval_eq_indicator_one
            (mu := mu)
            (action := action)
            (haction := haction)
            (a := a)
            (t := t)

end BanditRLProof
