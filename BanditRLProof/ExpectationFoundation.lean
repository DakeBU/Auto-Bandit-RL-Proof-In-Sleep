import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import BanditRLProof.MeasureFoundation

/-!
# Minimal expectation and integration foundations

This module introduces the first integration canary through the lower Lebesgue
integral of a pull-event indicator.  It deliberately avoids Bochner
expectation, probability measures, conditional expectation, filtrations,
kernels, and concentration assumptions.
-/

universe u v

open MeasureTheory
open scoped ENNReal

namespace BanditRLProof

/--
The lower integral of the indicator of a measurable pull event is the measure
of that event.

This is the `EXP-INDICATOR-PULL` canary.  It uses an arbitrary measure and an
`ENNReal` indicator, so it does not choose a Bochner expectation or probability
measure interface yet.
-/
theorem lintegral_actionTrace_eval_eq_indicator_one
    {Omega : Type u} {Action : Type v}
    [MeasurableSpace Omega] [MeasurableSpace Action]
    [MeasurableSingletonClass Action]
    (mu : Measure Omega)
    (action : Omega -> ActionTrace Action)
    (haction : forall t : Nat,
      Measurable (fun omega : Omega => action omega t))
    (a : Action) (t : Nat) :
    MeasureTheory.lintegral mu
      (fun omega : Omega =>
        (({omega' : Omega | action omega' t = a} : Set Omega).indicator
          (1 : Omega -> ENNReal)) omega)
      =
    mu {omega : Omega | action omega t = a} := by
  simpa using
    (@MeasureTheory.lintegral_indicator_one
      Omega _ mu {omega : Omega | action omega t = a}
      (measurableSet_actionTrace_eval_eq action haction a t))

end BanditRLProof
