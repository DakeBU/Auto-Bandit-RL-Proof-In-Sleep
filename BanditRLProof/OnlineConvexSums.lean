import BanditRLProof.OnlineConvexClosures

noncomputable section
open Set
namespace BanditRL.OnlineConvex

/-- Convex-analysis addition: positive infinity dominates mixed infinities. -/
def upperAdd (a b : EReal) : EReal := -(-a + -b)

theorem upperAdd_coe (a b : ℝ) : upperAdd (a : EReal) (b : EReal) = ((a + b : ℝ) : EReal) := by
  simp [upperAdd, ← EReal.coe_neg, ← EReal.coe_add, add_comm]

theorem upperAdd_top (a : EReal) : upperAdd a ⊤ = ⊤ := by
  simp [upperAdd]

theorem top_upperAdd (a : EReal) : upperAdd ⊤ a = ⊤ := by
  simp [upperAdd]

theorem upperAdd_le_coe_iff (a b : EReal) (h : ℝ) :
    upperAdd a b ≤ (h : EReal) ↔
      ∃ r s : ℝ, a ≤ (r : EReal) ∧ b ≤ (s : EReal) ∧ r + s ≤ h := by
  cases a <;> cases b <;>
    simp [upperAdd, ← EReal.coe_neg, ← EReal.coe_add]
  · exact ⟨0, h, by simp⟩
  · rename_i b
    exact ⟨h - b, b, le_rfl, by linarith⟩
  · rename_i a
    exact ⟨a, le_rfl, h - a, by linarith⟩
  · rename_i a b
    constructor
    · intro hab
      exact ⟨a, le_rfl, b, le_rfl, by linarith⟩
    · rintro ⟨r, har, t, hbt, hrt⟩
      linarith

theorem convex_upperAdd {E : Type*} [AddCommGroup E] [Module ℝ E]
    (f g : E → EReal) (hf : IsConvexExtended f) (hg : IsConvexExtended g) :
    IsConvexExtended (fun x => upperAdd (f x) (g x)) := by
  intro x hx y hy a b ha hb hab
  obtain ⟨r₁, s₁, hfr₁, hgs₁, h₁⟩ := (upperAdd_le_coe_iff _ _ _).mp hx
  obtain ⟨r₂, s₂, hfr₂, hgs₂, h₂⟩ := (upperAdd_le_coe_iff _ _ _).mp hy
  apply (upperAdd_le_coe_iff _ _ _).mpr
  refine ⟨a * r₁ + b * r₂, a * s₁ + b * s₂, ?_, ?_, ?_⟩
  · exact hf (show (x.1, r₁) ∈ realEpigraph f from hfr₁)
      (show (y.1, r₂) ∈ realEpigraph f from hfr₂) ha hb hab
  · exact hg (show (x.1, s₁) ∈ realEpigraph g from hgs₁)
      (show (y.1, s₂) ∈ realEpigraph g from hgs₂) ha hb hab
  · change a * r₁ + b * r₂ + (a * s₁ + b * s₂) ≤ a * x.2 + b * y.2
    nlinarith [mul_le_mul_of_nonneg_left h₁ ha, mul_le_mul_of_nonneg_left h₂ hb]

theorem positive_mul_le_coe_iff (a : ℝ) (ha : 0 < a) (z : EReal) (h : ℝ) :
    (a : EReal) * z ≤ (h : EReal) ↔ z ≤ ((h / a : ℝ) : EReal) := by
  cases z with
  | bot => simp [EReal.coe_mul_bot_of_pos ha]
  | top => simp [EReal.coe_mul_top_of_pos ha]
  | coe z =>
    rw [← EReal.coe_mul, EReal.coe_le_coe_iff, EReal.coe_le_coe_iff]
    simpa only [mul_comm] using (le_div_iff₀ ha : z ≤ h / a ↔ z * a ≤ h).symm

theorem convex_nonneg_mul {E : Type*} [AddCommGroup E] [Module ℝ E]
    (f : E → EReal) (hf : IsConvexExtended f) (a : ℝ) (ha : 0 ≤ a) :
    IsConvexExtended (fun x => (a : EReal) * f x) := by
  rcases ha.eq_or_lt with ha | ha
  · subst a
    simpa using (convexExtended_coe_iff (fun _ : E => (0 : ℝ))).mpr
      (convexOn_const (c := (0 : ℝ)) convex_univ)
  · intro x hx y hy c d hc hd hcd
    have hx' := (positive_mul_le_coe_iff a ha _ _).mp hx
    have hy' := (positive_mul_le_coe_iff a ha _ _).mp hy
    apply (positive_mul_le_coe_iff a ha _ _).mpr
    have h := hf (show (x.1, x.2 / a) ∈ realEpigraph f from hx')
      (show (y.1, y.2 / a) ∈ realEpigraph f from hy') hc hd hcd
    change f (c • x.1 + d • y.1) ≤ ((c * (x.2 / a) + d * (y.2 / a) : ℝ) : EReal) at h
    change f (c • x.1 + d • y.1) ≤ (((c * x.2 + d * y.2) / a : ℝ) : EReal)
    convert h using 1 <;> congr 1 <;> ring

theorem convex_nonneg_linear_combination {E : Type*} [AddCommGroup E] [Module ℝ E]
    (f g : E → EReal) (hf : IsConvexExtended f) (hg : IsConvexExtended g)
    (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    IsConvexExtended (fun x => upperAdd ((a : EReal) * f x) ((b : EReal) * g x)) := by
  exact convex_upperAdd _ _ (convex_nonneg_mul f hf a ha) (convex_nonneg_mul g hg b hb)

end BanditRL.OnlineConvex
