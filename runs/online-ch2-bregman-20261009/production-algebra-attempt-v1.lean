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

end Normed

end BanditRL.OnlineBregman
