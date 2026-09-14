import Tests.OnlineConvexFirstOrderCanary
import BanditRLProof
import Mathlib.Analysis.Convex.Mul

noncomputable section
open Set Filter BanditRL.OnlineConvex
open scoped Topology
namespace Tests.OnlineConvexOptimality
open Tests.OnlineConvexFirstOrder

theorem loss_finite (z : ℝ) (hz : z ∈ Ioi (0 : ℝ)) : loss z ≠ ⊤ ∧ loss z ≠ ⊥ := by
  simp [loss, show 0 < z from hz]

theorem loss_differentiable : DifferentiableOn ℝ (fun z => (loss z).toReal) (Ioi (0 : ℝ)) := by
  intro x hx
  have he : (fun z => (loss z).toReal) =ᶠ[𝓝 x] (fun z => z) := by
    filter_upwards [isOpen_Ioi.mem_nhds hx] with z hz
    simp [loss, show 0 < z from hz]
  exact ((hasDerivAt_id x).congr_of_eventuallyEq he).differentiableAt.differentiableWithinAt

theorem loss_convex_on_open : ConvexOn ℝ (Ioi (0 : ℝ)) (fun z => (loss z).toReal) := by
  rw [← loss_domain]
  exact (convexExtended_iff_toReal loss loss_noBot).mp loss_convex

theorem boundary_minimum : IsMinOn loss (Ici (1 : ℝ)) 1 := by
  have hVU : Ici (1 : ℝ) ⊆ Ioi (0 : ℝ) := by intro z hz; change 0 < z; exact lt_of_lt_of_le zero_lt_one hz
  -- Instantiate the source's convexity-on-open-neighborhood premise by restriction.
  apply (theorem_2_8 loss (Ici 1) (Ioi 0) (convex_Ici 1) ⟨1, by simp⟩ 1 (by simp)
    isOpen_Ioi hVU loss_finite (loss_convex_on_open.subset hVU (convex_Ici 1))
    loss_differentiable).mpr
  intro y hy
  rw [loss_gradient]
  change 0 ≤ (y - 1) * 1
  simpa only [mul_one] using sub_nonneg.mpr (show (1 : ℝ) ≤ y from hy)

theorem boundary_nondegenerate : IsMinOn loss (Ici (1 : ℝ)) 1 ∧
    gradient (fun z => (loss z).toReal) (1 : ℝ) = 1 ∧
    loss (1 / 2) < loss 1 ∧ loss 2 > loss 1 := by
  refine ⟨boundary_minimum, loss_gradient, ?_, ?_⟩
  · change (if (0 : ℝ) < 1 / 2 then ((1 / 2 : ℝ) : EReal) else ⊤) <
      (if (0 : ℝ) < 1 then ((1 : ℝ) : EReal) else ⊤)
    rw [if_pos (by norm_num), if_pos (by norm_num), EReal.coe_lt_coe_iff]
    norm_num
  · change (if (0 : ℝ) < 1 then ((1 : ℝ) : EReal) else ⊤) <
      (if (0 : ℝ) < 2 then ((2 : ℝ) : EReal) else ⊤)
    rw [if_pos (by norm_num), if_pos (by norm_num), EReal.coe_lt_coe_iff]
    norm_num

def quadratic (x : ℝ) : EReal := ((x ^ 2 : ℝ) : EReal)

theorem quadratic_gradient : gradient (fun z => (quadratic z).toReal) (0 : ℝ) = 0 := by
  have hd : HasDerivAt (fun z : ℝ => z ^ 2) 0 0 := by
    convert (hasDerivAt_id (0 : ℝ)).pow 2 using 1 <;> norm_num
  simpa [quadratic] using hd.hasGradientAt'.gradient

theorem interior_minimum : IsMinOn quadratic (Ioi (-1 : ℝ)) 0 := by
  have hf : ConvexOn ℝ (univ : Set ℝ) (fun z => (quadratic z).toReal) := by
    simpa [quadratic] using (show Even (2 : ℕ) from ⟨1, by norm_num⟩).convexOn_pow (𝕜 := ℝ)
  have hd : DifferentiableOn ℝ (fun z => (quadratic z).toReal) (univ : Set ℝ) := by
    simpa [quadratic] using (differentiable_id.pow 2).differentiableOn
  apply (interior_min_iff_gradient_zero quadratic (Ioi (-1)) univ (convex_Ioi (-1))
    ⟨0, by norm_num⟩ 0 (by norm_num) (by simp)
    isOpen_univ (subset_univ _) (by intro z hz; exact ⟨EReal.coe_ne_top _, EReal.coe_ne_bot _⟩)
    (hf.subset (subset_univ _) (convex_Ioi (-1))) hd).mpr
  exact quadratic_gradient

theorem interior_nondegenerate : IsMinOn quadratic (Ioi (-1 : ℝ)) 0 ∧
    quadratic 0 = 0 ∧ quadratic 1 = 1 ∧ gradient (fun z => (quadratic z).toReal) 0 = 0 := by
  exact ⟨interior_minimum, by norm_num [quadratic], by norm_num [quadratic], quadratic_gradient⟩

#print axioms BanditRL.OnlineConvex.minOn_real_iff_gradient
#print axioms BanditRL.OnlineConvex.minOn_finitePart_iff
#print axioms BanditRL.OnlineConvex.theorem_2_8
#print axioms BanditRL.OnlineConvex.interior_min_iff_gradient_zero
#print axioms boundary_nondegenerate
#print axioms interior_nondegenerate
end Tests.OnlineConvexOptimality
