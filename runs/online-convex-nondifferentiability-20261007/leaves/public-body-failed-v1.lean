/-
Orabona arXiv1912.13213v10, printed19/PDF31: the unnumbered example
after Theorem2.30 and before Section2.2.2 Analysis with Subgradients.
The real-valued function |x1| on the actual Euclidean plane is globally
convex and has no ambient Frechet derivative at any point of the closed
segment from (0,0) to (0,1), including both endpoints.
Lean index0 is the source first coordinate. The entire-axis lemma is an
explicit stronger library leaf. The vertical restriction is constant and
differentiable; its derivative is a different predicate.
The separate uncountability consequence and all remaining maintext remain
required. These declarations alone do not close the whole paragraph,
Chapter2, or the persistent Chapters1-16 Goal. No merge/live claim.
-/
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Calculus.Deriv.Abs
import Mathlib.Analysis.Normed.Module.Convex

namespace BanditRL.OnlineConvex

def coordinateAbsolute (x : EuclideanSpace ℝ (Fin 2)) : ℝ := |x 0|

theorem coordinate_absolute_convex :
    ConvexOn ℝ Set.univ coordinateAbsolute := by
  have h := (convexOn_univ_norm (E := ℝ)).comp_linearMap
    (PiLp.projₗ 2 (fun _ : Fin 2 => ℝ) 0 : EuclideanSpace ℝ (Fin 2) →ₗ[ℝ] ℝ)
  simpa only [Set.preimage_univ, Function.comp_def, Real.norm_eq_abs] using h

theorem coordinate_absolute_not_differentiable (x : EuclideanSpace ℝ (Fin 2))
    (hx : x 0 = 0) : ¬ DifferentiableAt ℝ coordinateAbsolute x := by
  intro hd
  let e : EuclideanSpace ℝ (Fin 2) := PiLp.single 2 0 1
  have hc : DifferentiableAt ℝ (fun t : ℝ => x + t • e) 0 :=
    differentiableAt_const.add (differentiableAt_id.smul_const e)
  have hd' : DifferentiableAt ℝ coordinateAbsolute ((fun t : ℝ => x + t • e) 0) := by
    simpa only [zero_smul, add_zero] using hd
  have hcomp := hd'.comp 0 hc
  apply not_differentiableAt_abs_zero
  simpa [Function.comp_def, coordinateAbsolute, e, hx] using hcomp

theorem convex_nondifferentiable_segment :
    ConvexOn ℝ Set.univ coordinateAbsolute ∧
    ∀ x ∈ segment ℝ (0 : EuclideanSpace ℝ (Fin 2)) (PiLp.single 2 1 1),
      ¬ DifferentiableAt ℝ coordinateAbsolute x := by
  refine ⟨coordinate_absolute_convex, ?_⟩
  intro x hx
  apply coordinate_absolute_not_differentiable x
  rcases hx with ⟨a, b, _, _, _, rfl⟩
  simp [PiLp.single_apply]

end BanditRL.OnlineConvex
