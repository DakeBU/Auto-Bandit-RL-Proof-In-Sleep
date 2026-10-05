import BanditRLProof
import Tests.OnlineConvexBarycenterCanary

noncomputable section
open Set BanditRL.OnlineConvex
namespace Tests.OnlineConvexMinorant
open Tests.OnlineConvexBarycenter
local instance : DecidablePred (fun p : ℝ × ℝ => p ∈ ray) := Classical.decPred _

def loss (p : ℝ × ℝ) : EReal := upperAdd (p.1 : EReal) (extendedIndicator ray p)

theorem loss_formula (p : ℝ × ℝ) : loss p = if p ∈ ray then (p.1 : EReal) else ⊤ := by
  classical
  by_cases hp : p ∈ ray
  · simp [loss, extendedIndicator, hp, upperAdd, ← EReal.coe_neg, ← EReal.coe_add]
  · simp [loss, extendedIndicator, hp, upperAdd_top]

theorem loss_noBot (p : ℝ × ℝ) : loss p ≠ ⊥ := by
  rw [loss_formula]
  split <;> simp

theorem loss_convex : IsConvexExtended loss := by
  apply convex_upperAdd _ _ _ ((convex_indicator_iff ray).mpr ray_convex)
  apply (convexExtended_coe_iff _).mpr
  exact (LinearMap.fst ℝ ℝ ℝ).convexOn convex_univ

theorem loss_domain : effectiveDomain loss = ray := by
  ext p
  simp only [effectiveDomain, mem_setOf_eq, loss_formula]
  split <;> simp_all

theorem global_minorant : ∃ (a : (ℝ × ℝ) →L[ℝ] ℝ) (b : ℝ),
    ∀ p, ((a p + b : ℝ) : EReal) ≤ loss p := by
  apply convex_affine_minorant loss loss_noBot loss_convex
  rw [loss_domain]
  exact ⟨(1, 0), by norm_num [ray]⟩

theorem nondegenerate_nonclosed : loss (1, 0) = 1 ∧ loss (3, 0) = 3 ∧
    loss (0, 1) = ⊤ ∧ ¬ IsClosed (effectiveDomain loss) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · norm_num [loss_formula, ray] <;> rfl
  · norm_num [loss_formula, ray] <;> rfl
  · norm_num [loss_formula, ray] <;> rfl
  · rw [loss_domain]; exact ray_not_closed

#print axioms BanditRL.OnlineConvex.affine_minorant_of_domain_interior
#print axioms BanditRL.OnlineConvex.convex_affine_minorant
#print axioms global_minorant
#print axioms nondegenerate_nonclosed
end Tests.OnlineConvexMinorant
