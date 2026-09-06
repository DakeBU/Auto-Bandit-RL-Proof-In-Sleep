import BanditRLProof.OFULEllipticalPotential

/-!
# Standard OFUL elliptical-potential endpoint

This module packages the determinant-growth and clipped inverse-quadratic
conclusions of the deterministic OFUL linear-algebra route in one
theorem-facing statement.  It is the handoff expected by a later
self-normalized concentration and confidence-ellipsoid proof.
-/

namespace BanditRLProof
namespace OFUL

universe u

/--
Standard logarithmic determinant and elliptical-potential bounds.

For a positive scalar regularization and uniformly bounded squared feature
norms, the terminal regularized Gram determinant and the cumulative clipped
inverse-quadratic updates are controlled by
`d * log (1 + T * L2 / (d * lambda))`.
-/
theorem standardLogDeterminantAndEllipticalPotential
    {Feature : Type u}
    [Fintype Feature] [DecidableEq Feature] [Nonempty Feature]
    (lambda : Real) (hlambda : 0 < lambda)
    (history : Nat -> Feature -> Real) (T : Nat) (L2 : Real)
    (hL2 : 0 <= L2)
    (hbound : forall t : Nat, t < T ->
      dotProduct (history t) (history t) <= L2) :
    (regularizedPrefixFeatureGram lambda history T).det <=
        lambda ^ Fintype.card Feature *
          Real.exp ((Fintype.card Feature : Real) *
            Real.log (1 +
              (T * L2) /
                ((Fintype.card Feature : Real) * lambda))) /\
      (Finset.range T).sum
          (fun t => min 1 (dotProduct (history t)
            (Matrix.mulVec
              ((regularizedPrefixFeatureGram lambda history t)⁻¹)
              (history t)))) <=
        2 * ((Fintype.card Feature : Real) *
          Real.log (1 +
            (T * L2) /
              ((Fintype.card Feature : Real) * lambda))) := by
  constructor
  · exact det_regularizedPrefixFeatureGram_le_mul_exp_trace_average_log
      lambda hlambda history T L2 hL2 hbound
  · exact sum_range_min_prefix_update_le_two_trace_average_log
      lambda hlambda history T L2 hL2 hbound

end OFUL
end BanditRLProof
