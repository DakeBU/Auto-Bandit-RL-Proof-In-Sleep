import BanditRLProof.OnlineSubgradientMax
noncomputable section
open Set
namespace BanditRL.OnlineConvex
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
def sourceHinge (z x : E) : EReal := ((max (1 - inner ℝ z x) 0 : ℝ) : EReal)

theorem affine_subdifferential (a : E) (b : ℝ) (x : E) :
    SourceSubdifferential (fun y => ((inner ℝ a y + b : ℝ) : EReal)) x = {a} := by
  ext g
  change (∀ y, ((inner ℝ a x + b : ℝ) : EReal) +
    (inner ℝ g (y - x) : EReal) ≤ ((inner ℝ a y + b : ℝ) : EReal)) ↔ g = a
  constructor
  · intro hg
    have h := hg (x + (g - a))
    rw [← EReal.coe_add] at h
    have hr := EReal.coe_le_coe_iff.mp h
    simp only [add_sub_cancel_left, inner_add_right] at hr
    have hd : inner ℝ (g - a) (g - a) ≤ 0 := by
      rw [inner_sub_left]
      linarith
    have hz : g - a = 0 := inner_self_eq_zero.mp
      (le_antisymm hd real_inner_self_nonneg)
    exact sub_eq_zero.mp hz
  · intro hg
    subst g
    intro y
    rw [← EReal.coe_add]
    apply EReal.coe_le_coe_iff.mpr
    rw [inner_sub_right]
    linarith

#print axioms BanditRL.OnlineConvex.affine_subdifferential
end BanditRL.OnlineConvex
