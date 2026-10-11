import BanditRLProof

noncomputable section
open Set Filter BanditRL.OnlineConvex
open scoped Topology
namespace Tests.OnlineConvexFirstOrder

def loss (x : ℝ) : EReal := if 0 < x then (x : EReal) else ⊤

theorem loss_noBot (x : ℝ) : loss x ≠ ⊥ := by
  by_cases hx : 0 < x <;> simp [loss, hx]

theorem loss_domain : effectiveDomain loss = Ioi (0 : ℝ) := by
  ext x
  by_cases hx : 0 < x <;> simp [effectiveDomain, loss, hx]

theorem loss_convex : IsConvexExtended loss := by
  have hl : IsConvexExtended (fun x : ℝ => (x : EReal)) :=
    (convexExtended_coe_iff _).mpr (convexOn_id convex_univ)
  have h := convex_add_indicator (fun x : ℝ => (x : EReal))
    (fun x => EReal.coe_ne_bot x) hl (Ioi (0 : ℝ)) (convex_Ioi 0)
  have he : (fun x : ℝ => (x : EReal) + extendedIndicator (Ioi (0 : ℝ)) x) = loss := by
    funext x
    by_cases hx : 0 < x <;>
      simp [loss, extendedIndicator, hx, EReal.add_top_of_ne_bot (EReal.coe_ne_bot x)]
  rw [he] at h
  exact h

theorem interior_one : (1 : ℝ) ∈ interior (effectiveDomain loss) := by
  rw [loss_domain]
  norm_num

theorem loss_hasDeriv : HasDerivAt (fun x => (loss x).toReal) 1 (1 : ℝ) := by
  have he : (fun x => (loss x).toReal) =ᶠ[𝓝 (1 : ℝ)] (fun x => x) := by
    filter_upwards [isOpen_Ioi.mem_nhds (show (1 : ℝ) ∈ Ioi 0 by norm_num)] with z hz
    simp [loss, show 0 < z from hz]
  exact (hasDerivAt_id (1 : ℝ)).congr_of_eventuallyEq he

theorem loss_gradient : gradient (fun x => (loss x).toReal) (1 : ℝ) = 1 :=
  loss_hasDeriv.hasGradientAt'.gradient

theorem instantiated_bound (y : ℝ) : loss 1 + ((y - 1 : ℝ) : EReal) ≤ loss y := by
  have h := theorem_2_7 loss loss_noBot loss_convex 1 interior_one loss_hasDeriv.differentiableAt y
  rw [loss_gradient] at h
  have hi : inner ℝ (1 : ℝ) (y - 1) = y - 1 := by
    change (y - 1) * 1 = y - 1
    ring
  simpa only [hi] using h

theorem nondegenerate : loss 1 = ((1 : ℝ) : EReal) ∧
    loss 2 = ((2 : ℝ) : EReal) ∧ loss (-1) = ⊤ ∧
    gradient (fun x => (loss x).toReal) (1 : ℝ) ≠ 0 := by
  rw [loss_gradient]
  norm_num [loss]

example : loss 1 + ((-2 : ℝ) : EReal) ≤ loss (-1) := by
  simpa only [show (-1 : ℝ) - 1 = -2 by norm_num] using instantiated_bound (-1)

#print axioms BanditRL.OnlineConvex.finitePart_eventually
#print axioms BanditRL.OnlineConvex.convex_gradient_lower_bound
#print axioms BanditRL.OnlineConvex.theorem_2_7
#print axioms loss_hasDeriv
#print axioms instantiated_bound
#print axioms nondegenerate
end Tests.OnlineConvexFirstOrder
