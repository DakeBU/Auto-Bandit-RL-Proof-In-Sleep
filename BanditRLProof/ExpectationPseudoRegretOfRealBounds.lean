import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import BanditRLProof.ExpectationFiniteBanditModelBounds
import BanditRLProof.ScalarPseudoRegret

/-!
# Lower-integral bounds for `ENNReal.ofReal` pseudo-regret

This module lifts the pointwise scalar/model pseudo-regret faithfulness bridge
to the existing `ENNReal` lower-integral model-gap budget bound.  It remains an
`ENNReal.ofReal` lower-integral theorem, not a Rat-valued or Bochner expected
regret statement.
-/

universe u

open MeasureTheory

namespace BanditRLProof

/--
Under explicit nonnegativity of model gaps, the lower integral of
`ENNReal.ofReal` pseudo-regret is bounded by the finite-arm model-gap horizon
budget.

This is the `EXP-OFREAL-PSEUDOREGRET-BOUND` leaf.  It consumes the pointwise
scalar/model pseudo-regret bridge and the existing finite-bandit model-gap
lower-integral bound; it does not prove gap nonnegativity, Bochner expectation,
filtration, or concentration results.
-/
theorem lintegral_ofReal_pseudoRegret_le_sum_model_gap_ofReal_mul_time_of_nonneg
    {Omega : Type u} {K : Nat}
    [MeasurableSpace Omega]
    [MeasurableSpace (Fin K)] [MeasurableSingletonClass (Fin K)]
    (mu : Measure Omega) [MeasureTheory.IsProbabilityMeasure mu]
    (model : FiniteBanditModel K)
    (action : Omega -> ActionTrace (Fin K))
    (haction : forall t : Nat,
      Measurable (fun omega : Omega => action omega t))
    (hgap : forall a : Fin K,
      0 <= (((model.gap a : Rat) : Real)))
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
  calc
    MeasureTheory.lintegral mu
      (fun omega : Omega =>
        ENNReal.ofReal
          (((pseudoRegret model (action omega) n : Rat) : Real)))
        =
      MeasureTheory.lintegral mu
        (fun omega : Omega =>
          (Finset.univ : Finset (Fin K)).sum
            (fun a : Fin K =>
              ENNReal.ofReal (((model.gap a : Rat) : Real)) *
                ((pullCount (action omega) a n : Nat) : ENNReal))) := by
          apply MeasureTheory.lintegral_congr
          intro omega
          exact
            BanditRLProof.ENNReal.ofReal_pseudoRegret_eq_univ_sum_model_gap_ofReal_mul_natCast_pullCount_of_nonneg
              (model := model)
              (action := action omega)
              (hgap := hgap)
              (n := n)
    _ <=
      (Finset.univ : Finset (Fin K)).sum
        (fun a : Fin K =>
          ENNReal.ofReal (((model.gap a : Rat) : Real)) *
            (n : ENNReal)) := by
          exact
            lintegral_univ_sum_model_gap_ofReal_mul_natCast_pullCount_le_sum_model_gap_ofReal_mul_time
              (mu := mu)
              (model := model)
              (action := action)
              (haction := haction)
              (n := n)

end BanditRLProof
