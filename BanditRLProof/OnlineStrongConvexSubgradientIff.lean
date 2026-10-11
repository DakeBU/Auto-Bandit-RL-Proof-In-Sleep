import BanditRLProof.OnlineStrongConvexSourceSubgradient

noncomputable section
open Set
namespace BanditRL.OnlineConvex

theorem stronglyConvex_iff_sourceSubgradient_growth {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (d : ℕ) (e : E ≃ₗ[ℝ] EuclideanSpace ℝ (Fin d))
    (f : E → EReal) (V : Set E) (lam : ℝ)
    (hf : SourceProper f) (hV : Convex ℝ V) (hlam : 0 ≤ lam)
    (hsub : ∀ p ∈ V,
      (SourceSubdifferential (fun u => f (e.symm u)) (e p)).Nonempty) :
    (∀ x ∈ V, ∀ y ∈ V, ∀ a : ℝ, 0 < a → a < 1 →
      f (a • x + (1 - a) • y) ≤
        (a : EReal) * f x + ((1 - a : ℝ) : EReal) * f y -
          (((lam / 2) * a * (1 - a) * ‖x - y‖ ^ 2 : ℝ) : EReal)) ↔
    (∀ p ∈ V, ∀ q ∈ V, ∀ g : EuclideanSpace ℝ (Fin d),
      g ∈ SourceSubdifferential (fun u => f (e.symm u)) (e p) →
        (f p).toReal + inner ℝ g (e (q - p)) +
          (lam / 2) * ‖q - p‖ ^ 2 ≤ (f q).toReal) := by
  have hfcoord : SourceProper (fun u => f (e.symm u)) := by
    refine ⟨fun u => hf.1 (e.symm u), ?_⟩
    obtain ⟨w, r, hr⟩ := hf.2
    exact ⟨e w, r, by simpa only [LinearEquiv.symm_apply_apply] using hr⟩
  have hdom : V ⊆ effectiveDomain f := by
    intro p hp
    obtain ⟨g, hg⟩ := hsub p hp
    have hd := subgradient_point_finite (fun u => f (e.symm u)) hfcoord (e p) g hg
    simpa only [effectiveDomain, mem_setOf_eq, LinearEquiv.symm_apply_apply] using hd
  have hfinite (p : E) (hp : p ∈ V) : ((f p).toReal : EReal) = f p :=
    EReal.coe_toReal (ne_of_lt (hdom hp)) (hf.1 p)
  constructor
  · intro hstrong p hp q hq g hg
    exact stronglyConvex_sourceSubgradient_growth d e f V lam hf hV hdom hlam
      hstrong p hp g hg q hq
  · intro hgrowth x hx y hy a ha ha1
    have hb : 0 ≤ 1 - a := by linarith
    let z : E := a • x + (1 - a) • y
    have hz : z ∈ V := hV hx hy ha.le hb (by ring)
    obtain ⟨g, hg⟩ := hsub z hz
    have h1 := hgrowth z hz x hx g hg
    have h2 := hgrowth z hz y hy g hg
    have h1w := mul_le_mul_of_nonneg_left h1 ha.le
    have h2w := mul_le_mul_of_nonneg_left h2 hb
    have hv : a • (x - z) + (1 - a) • (y - z) = (0 : E) := by
      dsimp [z]
      module
    have hpair : a * inner ℝ g (e (x - z)) +
        (1 - a) * inner ℝ g (e (y - z)) = 0 := by
      have he := congrArg (fun v : E => inner ℝ g (e v)) hv
      simpa only [map_add, map_smul, inner_add_right, real_inner_smul_right,
        map_zero, inner_zero_right] using he
    have hxz : x - z = (1 - a) • (x - y) := by
      dsimp [z]
      module
    have hyz : y - z = (-a) • (x - y) := by
      dsimp [z]
      module
    have hnx : ‖x - z‖ ^ 2 = (1 - a) ^ 2 * ‖x - y‖ ^ 2 := by
      rw [hxz, norm_smul, Real.norm_eq_abs, abs_of_nonneg hb, mul_pow]
    have hny : ‖y - z‖ ^ 2 = a ^ 2 * ‖x - y‖ ^ 2 := by
      rw [hyz, norm_smul, Real.norm_eq_abs, abs_neg, abs_of_nonneg ha.le, mul_pow]
    have hweights : a * ((lam / 2) * ‖x - z‖ ^ 2) +
        (1 - a) * ((lam / 2) * ‖y - z‖ ^ 2) =
        (lam / 2) * a * (1 - a) * ‖x - y‖ ^ 2 := by
      rw [hnx, hny]
      ring
    have hr : (f z).toReal ≤ a * (f x).toReal + (1 - a) * (f y).toReal -
        (lam / 2) * a * (1 - a) * ‖x - y‖ ^ 2 := by
      nlinarith [h1w, h2w, hpair, hweights]
    change f z ≤ (a : EReal) * f x + ((1 - a : ℝ) : EReal) * f y -
      (((lam / 2) * a * (1 - a) * ‖x - y‖ ^ 2 : ℝ) : EReal)
    rw [← hfinite z hz, ← hfinite x hx, ← hfinite y hy]
    exact_mod_cast hr


end BanditRL.OnlineConvex
