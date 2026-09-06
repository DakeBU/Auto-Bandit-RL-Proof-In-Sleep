import Mathlib.Data.ENNReal.BigOperators
import Mathlib.Data.ENNReal.Real
import Mathlib.Data.Nat.Cast.Basic

/-!
# Scalar `ENNReal.ofReal` bridges

This module contains scalar conversion leaves used before any probability or
bandit-specific expectation statement.  The lemmas here are deliberately
independent of `FiniteBanditModel`, traces, integrals, and filtrations.
-/

universe u

namespace BanditRLProof

namespace ENNReal

/--
For a finite sum of nonnegative real weights times natural counts, `ofReal`
commutes with the weighted sum and turns the counts into `ENNReal` casts.

This is the `OFREAL-FINSET-WEIGHTED-NAT-FAITHFULNESS` scalar leaf.  It is a
faithfulness lemma under explicit pointwise nonnegativity of the real weights;
it is not an expectation theorem.
-/
theorem ofReal_finset_sum_mul_natCast_of_nonneg
    {ι : Type u}
    (s : Finset ι) (gap : ι -> Real) (count : ι -> Nat)
    (hgap : forall i : ι, i ∈ s -> 0 <= gap i) :
    ENNReal.ofReal
      (s.sum (fun i : ι => gap i * ((count i : Nat) : Real)))
      =
    s.sum
      (fun i : ι =>
        ENNReal.ofReal (gap i) * ((count i : Nat) : ENNReal)) := by
  have hterm :
      forall i : ι, i ∈ s ->
        0 <= gap i * ((count i : Nat) : Real) := by
    intro i hi
    exact mul_nonneg (hgap i hi) (Nat.cast_nonneg (count i))
  calc
    ENNReal.ofReal
      (s.sum (fun i : ι => gap i * ((count i : Nat) : Real)))
        =
      s.sum
        (fun i : ι =>
          ENNReal.ofReal
            (gap i * ((count i : Nat) : Real))) := by
          simpa using
            (ENNReal.ofReal_sum_of_nonneg
              (s := s)
              (f := fun i : ι =>
                gap i * ((count i : Nat) : Real))
              hterm)
    _ =
      s.sum
        (fun i : ι =>
          ENNReal.ofReal (gap i) *
            ((count i : Nat) : ENNReal)) := by
          apply Finset.sum_congr rfl
          intro i _hi
          have hcount : 0 <= ((count i : Nat) : Real) :=
            Nat.cast_nonneg (count i)
          simpa [ENNReal.ofReal_natCast] using
            (ENNReal.ofReal_mul'
              (p := gap i)
              (q := ((count i : Nat) : Real))
              hcount)

end ENNReal

end BanditRLProof
