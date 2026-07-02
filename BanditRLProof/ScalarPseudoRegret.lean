import Mathlib.Algebra.Field.Rat
import Mathlib.Data.Rat.BigOperators
import Mathlib.Data.Fintype.Basic
import BanditRLProof.ScalarENNReal
import BanditRLProof.RegretDecomposition

/-!
# Scalar pseudo-regret `ENNReal.ofReal` bridges

This module is still pointwise scalar algebra.  It connects the deterministic
pull-count regret decomposition to the scalar `ENNReal.ofReal` finite-sum
faithfulness lemma under an explicit nonnegativity contract on model gaps.
-/

namespace BanditRLProof

private theorem real_pseudoRegret_eq_univ_sum_model_gap_mul_natCast_pullCount
    {K : Nat}
    (model : FiniteBanditModel K)
    (action : ActionTrace (Fin K))
    (n : Nat) :
    (((pseudoRegret model action n : Rat) : Real))
      =
    (Finset.univ : Finset (Fin K)).sum
      (fun a : Fin K =>
        (((model.gap a : Rat) : Real) *
          (((pullCount action a n : Nat) : Real)))) := by
  simp [pseudoRegret_eq_finset_sum_gap_mul_pullCount]

namespace ENNReal

/--
Pointwise pseudo-regret is faithfully represented by the `ENNReal.ofReal`
weighted pull-count expression when all model gaps are explicitly nonnegative
after casting from `Rat` to `Real`.

This is the `OFREAL-PSEUDOREGRET-PULLCOUNT-FAITHFULNESS` scalar/model bridge.
It is not an expectation theorem and does not introduce measures,
filtrations, kernels, or concentration assumptions.
-/
theorem ofReal_pseudoRegret_eq_univ_sum_model_gap_ofReal_mul_natCast_pullCount_of_nonneg
    {K : Nat}
    (model : FiniteBanditModel K)
    (action : ActionTrace (Fin K))
    (hgap : forall a : Fin K,
      0 <= (((model.gap a : Rat) : Real)))
    (n : Nat) :
    ENNReal.ofReal (((pseudoRegret model action n : Rat) : Real))
      =
    (Finset.univ : Finset (Fin K)).sum
      (fun a : Fin K =>
        ENNReal.ofReal (((model.gap a : Rat) : Real)) *
          ((pullCount action a n : Nat) : ENNReal)) := by
  rw [real_pseudoRegret_eq_univ_sum_model_gap_mul_natCast_pullCount
    (model := model)
    (action := action)
    (n := n)]
  exact
    BanditRLProof.ENNReal.ofReal_finset_sum_mul_natCast_of_nonneg
      (s := (Finset.univ : Finset (Fin K)))
      (gap := fun a : Fin K => (((model.gap a : Rat) : Real)))
      (count := fun a : Fin K => pullCount action a n)
      (hgap := by
        intro a _ha
        exact hgap a)

end ENNReal

end BanditRLProof
