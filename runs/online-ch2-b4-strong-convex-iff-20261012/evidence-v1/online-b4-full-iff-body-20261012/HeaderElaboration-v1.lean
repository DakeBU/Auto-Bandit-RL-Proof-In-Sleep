import BanditRLProof.OnlineStrongConvexSourceSubgradient

noncomputable section
open Set
namespace BanditRL.OnlineConvex

#check ∀ {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (d : ℕ) (e : E ≃ₗ[ℝ] EuclideanSpace ℝ (Fin d))
    (f : E → EReal) (V : Set E) (lam : ℝ)
    (hf : SourceProper f) (hV : Convex ℝ V) (hlam : 0 ≤ lam)
    (hsub : ∀ p ∈ V,
      (SourceSubdifferential (fun u => f (e.symm u)) (e p)).Nonempty),
    (∀ x ∈ V, ∀ y ∈ V, ∀ a : ℝ, 0 < a → a < 1 →
      f (a • x + (1 - a) • y) ≤
        (a : EReal) * f x + ((1 - a : ℝ) : EReal) * f y -
          (((lam / 2) * a * (1 - a) * ‖x - y‖ ^ 2 : ℝ) : EReal)) ↔
    (∀ p ∈ V, ∀ q ∈ V, ∀ g : EuclideanSpace ℝ (Fin d),
      g ∈ SourceSubdifferential (fun u => f (e.symm u)) (e p) →
        (f p).toReal + inner ℝ g (e (q - p)) +
          (lam / 2) * ‖q - p‖ ^ 2 ≤ (f q).toReal)

end BanditRL.OnlineConvex
