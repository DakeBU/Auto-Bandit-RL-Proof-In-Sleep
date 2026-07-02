import Mathlib.Data.ENNReal.Real
import Mathlib.Algebra.Field.Rat
import BanditRLProof.ExpectationFiniteBanditBounds

/-!
# Finite-bandit model lower-integral bounds

This module connects the finite-action `ENNReal` pull-count budget bound to the
current `FiniteBanditModel.gap : Fin K -> Rat` surface through
`ENNReal.ofReal`.  This is a scalar-conversion canary only: because
`ENNReal.ofReal` clamps negative real values to zero, this file does not prove
faithfulness for Rat-valued pseudo-regret.
-/

universe u

open MeasureTheory
open scoped ENNReal

namespace BanditRLProof

/--
The finite-arm weighted pull-count budget bound instantiated with the
`ENNReal.ofReal` image of the local model gap.

This is the `EXP-MODEL-GAP-OFREAL-BOUND` bridge.  It is an executable
Rat-to-`ENNReal` model-gap wrapper, not a Bochner expected-regret theorem and
not a proof that Rat-valued pseudo-regret equals this lower integral.
-/
theorem lintegral_univ_sum_model_gap_ofReal_mul_natCast_pullCount_le_sum_model_gap_ofReal_mul_time
    {Omega : Type u} {K : Nat}
    [MeasurableSpace Omega]
    [MeasurableSpace (Fin K)] [MeasurableSingletonClass (Fin K)]
    (mu : Measure Omega) [MeasureTheory.IsProbabilityMeasure mu]
    (model : FiniteBanditModel K)
    (action : Omega -> ActionTrace (Fin K))
    (haction : forall t : Nat,
      Measurable (fun omega : Omega => action omega t))
    (n : Nat) :
    MeasureTheory.lintegral mu
      (fun omega : Omega =>
        (Finset.univ : Finset (Fin K)).sum
          (fun a : Fin K =>
            ENNReal.ofReal (((model.gap a : Rat) : Real)) *
              ((pullCount (action omega) a n : Nat) : ENNReal)))
      <=
    (Finset.univ : Finset (Fin K)).sum
      (fun a : Fin K =>
        ENNReal.ofReal (((model.gap a : Rat) : Real)) *
          (n : ENNReal)) := by
  simpa using
    (lintegral_univ_sum_gap_mul_natCast_pullCount_le_sum_gap_mul_time
      (mu := mu)
      (action := action)
      (haction := haction)
      (gap := fun a : Fin K =>
        ENNReal.ofReal (((model.gap a : Rat) : Real)))
      (n := n))

end BanditRLProof
