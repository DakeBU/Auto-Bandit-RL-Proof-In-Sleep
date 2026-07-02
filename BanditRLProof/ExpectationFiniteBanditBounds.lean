import Mathlib.Data.Fintype.Basic
import BanditRLProof.ExpectationWeightedPullCountBounds

/-!
# Finite-bandit lower-integral bounds

This module specializes the generic finite-action weighted pull-count budget
bound to the canonical finite action type `Fin K` and `Finset.univ`.
-/

universe u

open MeasureTheory
open scoped ENNReal

namespace BanditRLProof

/--
The `Fin K`/`Finset.univ` specialization of the `ENNReal` weighted pull-count
budget bound under a probability measure.

This is the `EXP-WEIGHTED-PULLCOUNT-LE-TIME-FIN` bridge.  It is still only an
`ENNReal` finite-action probability-count bound; it does not introduce
`FiniteBanditModel`, `Rat`/`Real`, or Bochner expectation.
-/
theorem lintegral_univ_sum_gap_mul_natCast_pullCount_le_sum_gap_mul_time
    {Omega : Type u} {K : Nat}
    [MeasurableSpace Omega]
    [MeasurableSpace (Fin K)] [MeasurableSingletonClass (Fin K)]
    (mu : Measure Omega) [MeasureTheory.IsProbabilityMeasure mu]
    (action : Omega -> ActionTrace (Fin K))
    (haction : forall t : Nat,
      Measurable (fun omega : Omega => action omega t))
    (gap : Fin K -> ENNReal) (n : Nat) :
    MeasureTheory.lintegral mu
      (fun omega : Omega =>
        (Finset.univ : Finset (Fin K)).sum
          (fun a : Fin K =>
            gap a *
              ((pullCount (action omega) a n : Nat) : ENNReal)))
      <=
    (Finset.univ : Finset (Fin K)).sum
      (fun a : Fin K =>
        gap a * (n : ENNReal)) := by
  simpa using
    (lintegral_finset_sum_gap_mul_natCast_pullCount_le_sum_gap_mul_time
      (mu := mu)
      (action := action)
      (haction := haction)
      (gap := gap)
      (arms := (Finset.univ : Finset (Fin K)))
      (n := n))

end BanditRLProof
