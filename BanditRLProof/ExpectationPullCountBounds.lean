import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import BanditRLProof.ExpectationPullCount

/-!
# Lower-integral pull-count bounds

This module proves the first probability-measure corollary of the local
pull-count lower-integral identity.  It stays in `ENNReal` and only uses the
probability mass bound for measurable sets.
-/

universe u v

open MeasureTheory
open scoped ENNReal

namespace BanditRLProof

/--
The lower integral of a scalar-casted pull count is bounded by the horizon
under a probability measure.

This is the `EXP-PULLCOUNT-LE-TIME` bridge.  It is a probability-facing budget
bound for expected pull counts, not a Bochner expectation or expected-regret
theorem.
-/
theorem lintegral_natCast_pullCount_le_time
    {Omega : Type u} {Action : Type v}
    [MeasurableSpace Omega] [MeasurableSpace Action]
    [MeasurableSingletonClass Action] [DecidableEq Action]
    (mu : Measure Omega) [MeasureTheory.IsProbabilityMeasure mu]
    (action : Omega -> ActionTrace Action)
    (haction : forall t : Nat,
      Measurable (fun omega : Omega => action omega t))
    (a : Action) (n : Nat) :
    MeasureTheory.lintegral mu
      (fun omega : Omega =>
        ((pullCount (action omega) a n : Nat) : ENNReal))
      <= (n : ENNReal) := by
  rw [lintegral_natCast_pullCount_eq_sum_measure_actionTrace_eval_eq
    (mu := mu)
    (action := action)
    (haction := haction)
    (a := a)
    (n := n)]
  calc
    (Finset.range n).sum
        (fun t : Nat =>
          mu {omega : Omega | action omega t = a})
        <=
      (Finset.range n).sum
        (fun _t : Nat => (1 : ENNReal)) := by
          apply Finset.sum_le_sum
          intro _t _ht
          exact MeasureTheory.prob_le_one
    _ = (n : ENNReal) := by
          simp

end BanditRLProof
