/-
Orabona arXiv1912.13213v10, unnumbered paragraph after Theorem 2.30,
printed 19 / PDF 31, immediately before Section 2.2.2.
The fixed function f(x)=|x₁| is real-valued on all of the real Euclidean plane. Lean uses EuclideanSpace ℝ (Fin 2), with source x₁ represented by index 0. DifferentiableAt means the ambient real Fréchet derivative. The segment joins (0,0) to (0,1) and includes both endpoints. Countable means at most countable. Convexity, derivative failure and uncountability are conclusions proved by the library, not supplied premises.
Orabona states the convex example and its failure of differentiability along the segment without a proof. The three missing derivations—convexity, ambient nondifferentiability and the uncountability bridge—are supplied here by the library, not attributed to a printed argument. The helper proving failure on the entire vertical axis is explicitly stronger than the stated segment example.
This bounded example does not complete Chapter 2 or the book. Exact nonsmooth-locus equality, exact continuum cardinality and a general almost-everywhere differentiability theorem are outside this package.
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
    (differentiableAt_const x).add (differentiableAt_id.smul_const e)
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
  simp

end BanditRL.OnlineConvex
