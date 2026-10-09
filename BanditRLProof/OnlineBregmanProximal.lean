import BanditRLProof.OnlineProximalComparison
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Calculus.FDeriv.Linear
import Mathlib.Analysis.Calculus.Gradient.Basic

/-!
Canonical Bregman algebra and a real-valued proximal comparison for the required
Chapter 2 prescient forward dependency in Orabona v10. The second argument of
`divergence` is the base. Its total `fderiv` formula alone does not imply positivity
at a nondifferentiable base. These helpers do not assert attainment or construct
the source's causal sequence; the source-domain and extended-real bridges remain
separate obligations. See `docs/contracts/online-ch2-bregman-v1/stabilized-v1.json`.
-/

noncomputable section

open Set

namespace BanditRL.OnlineBregman

section Normed

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Ordered divergence formed from the actual Fréchet derivative at its base. -/
def divergence (ψ : E → ℝ) (x y : E) : ℝ :=
  ψ x - ψ y - fderiv ℝ ψ y (x - y)

/-- Algebraic self identity; no positivity or differentiability is inferred. -/
theorem divergence_self (ψ : E → ℝ) (x : E) :
    divergence ψ x x = 0 := by
  simp [divergence]

/-- The orientation of Orabona v10 Lemma 6.7, as a continuous-dual identity. -/
theorem three_point_identity (ψ : E → ℝ) (x y z : E) :
    divergence ψ z x + divergence ψ x y - divergence ψ z y =
      (fderiv ℝ ψ y - fderiv ℝ ψ x) (z - x) := by
  simp only [divergence, ContinuousLinearMap.sub_apply, map_sub]
  ring

/-- Convex support gives nonnegativity at an actual differentiable base. -/
theorem divergence_nonneg (X : Set E) (ψ : E → ℝ) (hψ : ConvexOn ℝ X ψ)
    (x y : E) (hx : x ∈ X) (hy : y ∈ X) (hd : DifferentiableAt ℝ ψ y) :
    0 ≤ divergence ψ x y := by
  have hline : HasDerivAt (AffineMap.lineMap y x : ℝ → E) (x - y) 0 := by
    simpa only [AffineMap.lineMap_apply_module', one_smul] using
      ((hasDerivAt_id (0 : ℝ)).smul_const (x - y)).add_const y
  have hfd : HasFDerivAt ψ (fderiv ℝ ψ y) (AffineMap.lineMap y x (0 : ℝ)) := by
    simpa using hd.hasFDerivAt
  have hc := hψ.comp_affineMap (AffineMap.lineMap y x : ℝ →ᵃ[ℝ] E)
  have hb := hc.le_slope_of_hasDerivAt (by simpa using hy) (by simpa using hx)
    (by norm_num : (0 : ℝ) < 1) (hfd.comp_hasDerivAt 0 hline)
  simp only [slope_def_field, Function.comp_apply, AffineMap.lineMap_apply_zero,
    AffineMap.lineMap_apply_one, sub_zero, div_one] at hb
  dsimp [divergence]
  linarith only [hb]

/-- A supplied current-loss minimum yields both signed Bregman residuals.
The previous point may lie outside `V`. Both base derivatives are explicit for
source instantiation; only the derivative at the selected point is needed in
the penalty differentiation. No differentiability of `f` is required. -/
theorem proximal_one_step (V : Set E) (f ψ : E → ℝ) (η : ℝ) (hη : 0 < η)
    (x p : E) (hp : p ∈ V) (hf : ConvexOn ℝ V f)
    (hdx : DifferentiableAt ℝ ψ x) (hdp : DifferentiableAt ℝ ψ p)
    (hmin : IsMinOn (fun z => f z + η⁻¹ * divergence ψ z x) V p) :
    ∀ u ∈ V, η * (f p - f u) ≤
      divergence ψ u x - divergence ψ u p - divergence ψ p x := by
  clear hdx
  have hlin : HasFDerivAt (fun z : E => fderiv ℝ ψ x (z - x)) (fderiv ℝ ψ x) p := by
    simpa only [Function.comp_def, ContinuousLinearMap.comp_id] using
      (fderiv ℝ ψ x).hasFDerivAt.comp p ((hasFDerivAt_id p).sub_const x)
  have hpen : HasFDerivAt (fun z => η⁻¹ * divergence ψ z x)
      (η⁻¹ • (fderiv ℝ ψ p - fderiv ℝ ψ x)) p := by
    simpa only [divergence, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] using
      ((hdp.hasFDerivAt.sub_const (ψ x)).sub hlin).const_smul η⁻¹
  intro u hu
  have hb := OnlineProximal.convex_minimizer_comparison V f
    (fun z => η⁻¹ * divergence ψ z x) p hp hf hmin
    (η⁻¹ • (fderiv ℝ ψ p - fderiv ℝ ψ x)) hpen u hu
  have hmul := mul_le_mul_of_nonneg_left hb (le_of_lt hη)
  simp only [ContinuousLinearMap.smul_apply, smul_eq_mul, ← mul_assoc,
    mul_inv_cancel₀ (ne_of_gt hη), one_mul, ContinuousLinearMap.sub_apply] at hmul
  have ht := three_point_identity ψ p x u
  simp only [ContinuousLinearMap.sub_apply] at ht
  linarith only [hmul, ht]

end Normed

section Inner

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- In complete real inner-product spaces the dual formula is the source gradient formula. -/
theorem divergence_eq_gradient (ψ : E → ℝ) (x y : E)
    (hd : DifferentiableAt ℝ ψ y) :
    divergence ψ x y = ψ x - ψ y - inner ℝ (gradient ψ y) (x - y) := by
  rw [divergence, hd.hasGradientAt.fderiv_apply]

end Inner

end BanditRL.OnlineBregman
