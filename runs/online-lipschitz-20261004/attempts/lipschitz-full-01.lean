import BanditRLProof.OnlineSubgradientDifferentiability
noncomputable section
open Set
open scoped Topology NNReal
namespace BanditRL.OnlineConvex
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Finite values on V and the actual all-pairs Lipschitz inequality.
The constant is explicitly nonnegative, including zero. -/
def SourceLipschitzOn (f : E → EReal) (V : Set E) (L : ℝ≥0) : Prop :=
  (∀ x ∈ V, ∃ a : ℝ, f x = (a : EReal)) ∧
    ∀ x ∈ V, ∀ y ∈ V, |(f x).toReal - (f y).toReal| ≤ (L : ℝ) * ‖x - y‖

theorem theorem_2_30 [FiniteDimensional ℝ E]
    (f : E → EReal) (hp : SourceProper f) (hc : IsConvexExtended f) (L : ℝ≥0) :
    SourceLipschitzOn f (interior (effectiveDomain f)) L ↔
      ∀ x ∈ interior (effectiveDomain f), ∀ g ∈ SourceSubdifferential f x,
        ‖g‖ ≤ (L : ℝ) := by
  constructor
  · intro hl x hx g hg
    obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp (isOpen_interior.mem_nhds hx)
    apply subgradient_norm_le_lipschitz_ball f x r hr L ?_ ?_ g hg
    · intro y hy
      exact hl.1 y (hball hy)
    · apply LipschitzOnWith.of_dist_le_mul
      intro y hy z hz
      simpa only [Real.dist_eq, dist_eq_norm] using hl.2 y (hball hy) z (hball hz)
  · intro hb
    refine ⟨?_, ?_⟩
    · intro x hx
      exact ⟨(f x).toReal,
        (EReal.coe_toReal (ne_of_lt (interior_subset hx)) (hp.1 x)).symm⟩
    · intro x hx y hy
      obtain ⟨gx, hgx⟩ := subgradient_exists_of_domain_interior f hp hc x hx
      obtain ⟨gy, hgy⟩ := subgradient_exists_of_domain_interior f hp hc y hy
      have hxv := EReal.coe_toReal (ne_of_lt (interior_subset hx)) (hp.1 x)
      have hyv := EReal.coe_toReal (ne_of_lt (interior_subset hy)) (hp.1 y)
      have hxy := hgx y
      have hyx := hgy x
      rw [← hxv, ← hyv, ← EReal.coe_add] at hxy
      rw [← hyv, ← hxv, ← EReal.coe_add] at hyx
      have hxyR := EReal.coe_le_coe_iff.mp hxy
      have hyxR := EReal.coe_le_coe_iff.mp hyx
      have hxg : -(inner ℝ gx (y - x)) ≤ (L : ℝ) * ‖x - y‖ := calc
        -(inner ℝ gx (y - x)) ≤ |inner ℝ gx (y - x)| := neg_le_abs _
        _ ≤ ‖gx‖ * ‖y - x‖ := abs_real_inner_le_norm _ _
        _ ≤ (L : ℝ) * ‖y - x‖ := mul_le_mul_of_nonneg_right (hb x hx gx hgx) (norm_nonneg _)
        _ = (L : ℝ) * ‖x - y‖ := by rw [norm_sub_rev]
      have hyg : -(inner ℝ gy (x - y)) ≤ (L : ℝ) * ‖x - y‖ := calc
        -(inner ℝ gy (x - y)) ≤ |inner ℝ gy (x - y)| := neg_le_abs _
        _ ≤ ‖gy‖ * ‖x - y‖ := abs_real_inner_le_norm _ _
        _ ≤ (L : ℝ) * ‖x - y‖ := mul_le_mul_of_nonneg_right (hb y hy gy hgy) (norm_nonneg _)
      apply abs_le.mpr
      constructor <;> linarith

#print axioms BanditRL.OnlineConvex.theorem_2_30
end BanditRL.OnlineConvex
