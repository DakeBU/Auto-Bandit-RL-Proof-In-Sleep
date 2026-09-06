import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import BanditRLProof.ExpectationWeightedPullCount
import BanditRLProof.ExpectationPullCountBounds

/-!
# Weighted lower-integral pull-count bounds

This module proves the finite weighted-count budget bound under a probability
measure.  It stays in `ENNReal`; no `Rat`/`Real`, Bochner expectation,
filtration, kernel, or concentration interface is selected here.
-/

universe u v

open MeasureTheory
open scoped ENNReal

namespace BanditRLProof

/--
The lower integral of a finite weighted sum of scalar-casted pull counts is
bounded by the corresponding weighted horizon budget under a probability
measure.

This is the `EXP-WEIGHTED-PULLCOUNT-LE-TIME` bridge.  It is an `ENNReal`
probability-count budget bound, not a Bochner expected-regret theorem.
-/
theorem lintegral_finset_sum_gap_mul_natCast_pullCount_le_sum_gap_mul_time
    {Omega : Type u} {Action : Type v}
    [MeasurableSpace Omega] [MeasurableSpace Action]
    [MeasurableSingletonClass Action] [DecidableEq Action]
    (mu : Measure Omega) [MeasureTheory.IsProbabilityMeasure mu]
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
      <=
    arms.sum
      (fun a : Action =>
        gap a * (n : ENNReal)) := by
  rw [lintegral_finset_sum_gap_mul_natCast_pullCount_eq
    (mu := mu)
    (action := action)
    (haction := haction)
    (gap := gap)
    (arms := arms)
    (n := n)]
  apply Finset.sum_le_sum
  intro a _ha
  have hcount :
      (Finset.range n).sum
          (fun t : Nat =>
            mu {omega : Omega | action omega t = a})
        <= (n : ENNReal) := by
    have h :=
      lintegral_natCast_pullCount_le_time
        (mu := mu)
        (action := action)
        (haction := haction)
        (a := a)
        (n := n)
    rw [lintegral_natCast_pullCount_eq_sum_measure_actionTrace_eval_eq
      (mu := mu)
      (action := action)
      (haction := haction)
      (a := a)
      (n := n)] at h
    exact h
  exact mul_le_mul_right hcount (gap a)

end BanditRLProof
