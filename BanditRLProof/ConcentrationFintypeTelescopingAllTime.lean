import BanditRLProof.ConcentrationFintypeGeometricAllTime

/-!
# Finite-index telescoping all-time confidence union

This module specializes the reusable finite-index/countable-time outer-measure
union bound to the confidence schedule
`delta / ((n+1)(n+2))`.  Its reciprocal grows polynomially, so logarithmic
confidence radii retain logarithmic time growth.  The theorem only composes
supplied event bounds; it is not a stochastic-process or UCB result.
-/

namespace BanditRLProof.Concentration

open MeasureTheory
open scoped ENNReal

universe u v

/-- Equal per-index telescoping shares at every time compose to the original
outer confidence budget. -/
theorem measure_iUnion_iUnion_fintype_le_delta_of_telescopingConfidenceShare
    {Omega : Type u} {Idx : Type v}
    [MeasurableSpace Omega] [Fintype Idx] [Nonempty Idx]
    (mu : Measure Omega)
    (bad : Nat -> Idx -> Set Omega)
    (delta : Real) (hdelta : 0 <= delta)
    (hbad : forall n i,
      mu (bad n i) <= ENNReal.ofReal
        (telescopingConfidenceShare delta n / (Fintype.card Idx : Real))) :
    mu (⋃ n, ⋃ i, bad n i) <= ENNReal.ofReal delta := by
  calc
    mu (⋃ n, ⋃ i, bad n i) <=
        ∑' n, ENNReal.ofReal (telescopingConfidenceShare delta n) :=
      measure_iUnion_iUnion_fintype_le_tsum_of_uniform
        mu bad (telescopingConfidenceShare delta) hbad
    _ = ENNReal.ofReal delta :=
      tsum_ofReal_telescopingConfidenceShare hdelta

end BanditRLProof.Concentration
