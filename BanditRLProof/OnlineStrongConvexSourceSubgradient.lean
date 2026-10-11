import BanditRLProof.OnlineStrongConvexSupport
import BanditRLProof.OnlineSubgradientBasic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Module.FiniteDimension

noncomputable section
open Set
namespace BanditRL.OnlineConvex

theorem stronglyConvex_sourceSubgradient_growth {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (d : ℕ) (e : E ≃ₗ[ℝ] EuclideanSpace ℝ (Fin d))
    (f : E → EReal) (V : Set E) (lam : ℝ)
    (hf : SourceProper f) (hV : Convex ℝ V)
    (hdom : V ⊆ effectiveDomain f) (hlam : 0 ≤ lam)
    (hstrong : ∀ x ∈ V, ∀ y ∈ V, ∀ a : ℝ, 0 < a → a < 1 →
      f (a • x + (1 - a) • y) ≤
        (a : EReal) * f x + ((1 - a : ℝ) : EReal) * f y -
          (((lam / 2) * a * (1 - a) * ‖x - y‖ ^ 2 : ℝ) : EReal))
    (p : E) (hp : p ∈ V) (g : EuclideanSpace ℝ (Fin d))
    (hg : g ∈ SourceSubdifferential (fun u => f (e.symm u)) (e p))
    (q : E) (hq : q ∈ V) :
    (f p).toReal + inner ℝ g (e (q - p)) +
      (lam / 2) * ‖q - p‖ ^ 2 ≤ (f q).toReal := by
  letI : FiniteDimensional ℝ E := e.symm.finiteDimensional
  let L : E →ₗ[ℝ] ℝ :=
    (innerₗ (EuclideanSpace ℝ (Fin d)) g).comp e.toLinearMap
  let G : E →L[ℝ] ℝ := L.toContinuousLinearMap
  have hG (z : E) : G z = inner ℝ g (e z) := rfl
  have hs : ∀ z ∈ V, f p + (G (z - p) : EReal) ≤ f z := by
    intro z hz
    have h := hg (e z)
    change f (e.symm (e p)) + (inner ℝ g (e z - e p) : EReal) ≤
      f (e.symm (e z)) at h
    simpa only [LinearEquiv.symm_apply_apply, hG, map_sub] using h
  have h := stronglyConvex_support_growth f V lam hf hV hdom hlam hstrong
    p hp G hs q hq
  simpa only [hG] using h

end BanditRL.OnlineConvex
