import Mathlib.Data.Rat.Cast.Order
import BanditRLProof.ExpectationPseudoRegretOfRealBounds
import BanditRLProof.FiniteBanditModelInvariants

/-!
# Rat-level contracts for `ENNReal.ofReal` pseudo-regret bounds

This module adapts the lower-integral `ENNReal.ofReal` pseudo-regret bound to
a more natural Rat-valued model-gap nonnegativity contract, then discharges
that contract from the local finite-bandit model invariant.
-/

universe u

open MeasureTheory

namespace BanditRLProof

/--
The `ENNReal.ofReal` lower-integral pseudo-regret bound under a Rat-level
nonnegativity contract for model gaps.

This is the `EXP-OFREAL-PSEUDOREGRET-BOUND-OF-RAT-GAP-NONNEG` adapter.  It
does not prove model-derived gap nonnegativity and is not a Bochner expected
regret theorem.
-/
theorem lintegral_ofReal_pseudoRegret_le_sum_model_gap_ofReal_mul_time_of_rat_gap_nonneg
    {Omega : Type u} {K : Nat}
    [MeasurableSpace Omega]
    [MeasurableSpace (Fin K)] [MeasurableSingletonClass (Fin K)]
    (mu : Measure Omega) [MeasureTheory.IsProbabilityMeasure mu]
    (model : FiniteBanditModel K)
    (action : Omega -> ActionTrace (Fin K))
    (haction : forall t : Nat,
      Measurable (fun omega : Omega => action omega t))
    (hgap : forall a : Fin K,
      (0 : Rat) <= model.gap a)
    (n : Nat) :
    MeasureTheory.lintegral mu
      (fun omega : Omega =>
        ENNReal.ofReal
          (((pseudoRegret model (action omega) n : Rat) : Real)))
      <=
    (Finset.univ : Finset (Fin K)).sum
      (fun a : Fin K =>
        ENNReal.ofReal (((model.gap a : Rat) : Real)) *
          (n : ENNReal)) := by
  exact
    lintegral_ofReal_pseudoRegret_le_sum_model_gap_ofReal_mul_time_of_nonneg
      (mu := mu)
      (model := model)
      (action := action)
      (haction := haction)
      (hgap := by
        intro a
        have ha : (0 : Rat) <= model.gap a := hgap a
        simpa using
          ((Rat.cast_nonneg (K := Real)).mpr ha))
      (n := n)

/--
The `ENNReal.ofReal` lower-integral pseudo-regret bound with model-derived
gap nonnegativity.

This is the `EXP-OFREAL-PSEUDOREGRET-BOUND-MODEL-GAP` adapter.  It consumes
`FiniteBanditModel.gap_nonneg`; it is still an `ENNReal.ofReal` lower-integral
surrogate, not a Rat-valued or Bochner expected-regret theorem.
-/
theorem lintegral_ofReal_pseudoRegret_le_sum_model_gap_ofReal_mul_time
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
        ENNReal.ofReal
          (((pseudoRegret model (action omega) n : Rat) : Real)))
      <=
    (Finset.univ : Finset (Fin K)).sum
      (fun a : Fin K =>
        ENNReal.ofReal (((model.gap a : Rat) : Real)) *
          (n : ENNReal)) := by
  exact
    lintegral_ofReal_pseudoRegret_le_sum_model_gap_ofReal_mul_time_of_rat_gap_nonneg
      (mu := mu)
      (model := model)
      (action := action)
      (haction := haction)
      (hgap := fun a => FiniteBanditModel.gap_nonneg model a)
      (n := n)

end BanditRLProof
