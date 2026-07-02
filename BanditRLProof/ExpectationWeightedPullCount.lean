import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.MeasureTheory.Group.Arithmetic
import BanditRLProof.ExpectationPullCount
import BanditRLProof.MeasurablePullCountCast

/-!
# Weighted lower-integral pull-count identities

This module proves the nonnegative weighted-count lower-integral bridge.  It
remains in `ENNReal`, with an arbitrary finite action set and arbitrary
nonnegative gap weights, before any `Rat`/`Real` or Bochner-expectation route.
-/

universe u v

open MeasureTheory
open scoped ENNReal

namespace BanditRLProof

/--
The lower integral of a finite weighted sum of scalar-casted pull counts equals
the same finite weighted sum of the corresponding action-event measures.

This is the `EXP-WEIGHTED-PULLCOUNT-LINTEGRAL` bridge.  It is shaped like a
nonnegative expected-regret identity, but it deliberately avoids
`FiniteBanditModel`, `Rat`, `Real`, Bochner expectation, filtrations, kernels,
and concentration assumptions.
-/
theorem lintegral_finset_sum_gap_mul_natCast_pullCount_eq
    {Omega : Type u} {Action : Type v}
    [MeasurableSpace Omega] [MeasurableSpace Action]
    [MeasurableSingletonClass Action] [DecidableEq Action]
    (mu : Measure Omega)
    (action : Omega -> ActionTrace Action)
    (haction : forall t : Nat,
      Measurable (fun omega : Omega => action omega t))
    (gap : Action -> ENNReal) (arms : Finset Action) (n : Nat) :
    MeasureTheory.lintegral mu
      (fun omega : Omega =>
        arms.sum
          (fun a : Action =>
            gap a *
              ((pullCount (action omega) a n : Nat) : ENNReal)))
      =
    arms.sum
      (fun a : Action =>
        gap a *
          (Finset.range n).sum
            (fun t : Nat =>
              mu {omega : Omega | action omega t = a})) := by
  have hmeas :
      forall a : Action, a ∈ arms ->
        Measurable
          (fun omega : Omega =>
            gap a *
              ((pullCount (action omega) a n : Nat) : ENNReal)) := by
    intro a _ha
    exact
      (measurable_natCast_pullCount
        (Beta := ENNReal)
        (action := action)
        (haction := haction)
        (a := a)
        (n := n)).const_mul (gap a)
  calc
    MeasureTheory.lintegral mu
      (fun omega : Omega =>
        arms.sum
          (fun a : Action =>
            gap a *
              ((pullCount (action omega) a n : Nat) : ENNReal)))
        =
      arms.sum
        (fun a : Action =>
          MeasureTheory.lintegral mu
            (fun omega : Omega =>
              gap a *
                ((pullCount (action omega) a n : Nat) : ENNReal))) := by
          simpa [Finset.sum_apply] using
            (@MeasureTheory.lintegral_finset_sum
              Omega Action _ mu arms
              (f := fun a omega =>
                gap a *
                  ((pullCount (action omega) a n : Nat) : ENNReal))
              hmeas)
    _ =
      arms.sum
        (fun a : Action =>
          gap a *
            (Finset.range n).sum
              (fun t : Nat =>
                mu {omega : Omega | action omega t = a})) := by
          apply Finset.sum_congr rfl
          intro a _ha
          calc
            MeasureTheory.lintegral mu
              (fun omega : Omega =>
                gap a *
                  ((pullCount (action omega) a n : Nat) : ENNReal))
                =
              gap a *
                MeasureTheory.lintegral mu
                  (fun omega : Omega =>
                    ((pullCount (action omega) a n : Nat) : ENNReal)) := by
                  exact
                    MeasureTheory.lintegral_const_mul
                      (μ := mu)
                      (r := gap a)
                      (measurable_natCast_pullCount
                        (Beta := ENNReal)
                        (action := action)
                        (haction := haction)
                        (a := a)
                        (n := n))
            _ =
              gap a *
                (Finset.range n).sum
                  (fun t : Nat =>
                    mu {omega : Omega | action omega t = a}) := by
                  rw [lintegral_natCast_pullCount_eq_sum_measure_actionTrace_eval_eq
                    (mu := mu)
                    (action := action)
                    (haction := haction)
                    (a := a)
                    (n := n)]

end BanditRLProof
