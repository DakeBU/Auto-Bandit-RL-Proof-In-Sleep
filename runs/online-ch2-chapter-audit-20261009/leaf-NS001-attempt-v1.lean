/-
Orabona arXiv:1912.13213v10, Section2.2 opening paragraph, printed16/PDF28.
The shifted absolute and labelled hinge illustrate convex losses with genuine
ambient kinks. The exact pointwise criteria below distinguish an exceptional
point from global differentiability. The unrestricted hinge sentence needs
an explicit qualification: zero effective normal gives the constant1 loss.
The pinned source is unchanged; this qualification was separately reviewed,
and is not an author-endorsed erratum. Center10 is generalized to every real c.
Finite-dimensional real inner-product instances include all source Euclidean
dimensions, including0. These examples do not close Chapter2 or the book.
-/
import Mathlib.Analysis.Calculus.Deriv.Abs
import BanditRLProof.OnlineHinge
import BanditRLProof.OnlineSubgradientDifferentiability

noncomputable section
open Set
open scoped InnerProductSpace
namespace BanditRL.OnlineConvex

theorem shifted_absolute_convex_differentiable_iff (c : ℝ) :
    ConvexOn ℝ Set.univ (fun x : ℝ => |x - c|) ∧
      ∀ x : ℝ, DifferentiableAt ℝ (fun w : ℝ => |w - c|) x ↔ x ≠ c := by
  constructor
  · simpa [Function.comp_def, Real.norm_eq_abs] using
      (convexOn_univ_norm (E := ℝ)).comp_affineMap
        (AffineMap.id ℝ ℝ - AffineMap.const ℝ ℝ c)
  · intro x
    constructor
    · intro hd hxc
      subst x
      have ht : DifferentiableAt ℝ (fun t : ℝ => t + c) 0 :=
        differentiableAt_id.add_const c
      have hd' : DifferentiableAt ℝ (fun w : ℝ => |w - c|) ((fun t : ℝ => t + c) 0) := by
        simpa using hd
      apply not_differentiableAt_abs_zero
      simpa [Function.comp_def] using hd'.comp 0 ht
    · intro hxc
      exact (differentiableAt_id.sub_const c).abs (sub_ne_zero.mpr hxc)

end BanditRL.OnlineConvex
