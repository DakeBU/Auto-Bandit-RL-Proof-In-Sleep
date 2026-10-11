import BanditRLProof
import Tests.OnlineSubgradientBasicCanary

namespace ForwardSubgradientProbe
open BanditRL.OnlineConvex Set Filter
open scoped Topology

theorem constrained_interval_singleton :
    SourceSubdifferential (extendedIndicator (Icc (0 : ℝ) 2)) 1 = {(0 : ℝ)} := by
  have hi : (1 : ℝ) ∈ interior (Icc (0 : ℝ) 2) := by
    rw [interior_Icc]
    norm_num
  have he : (fun _ : ℝ => ((0 : ℝ) : EReal)) =ᶠ[𝓝 (1 : ℝ)]
      extendedIndicator (Icc (0 : ℝ) 2) := by
    filter_upwards [isOpen_interior.mem_nhds hi] with y hy
    have hymem := interior_subset hy
    simp only [extendedIndicator, if_pos hymem, EReal.coe_zero]
  have hc := (convex_indicator_iff (Icc (0 : ℝ) 2)).mpr (convex_Icc 0 2)
  have hx : ∃ r : ℝ, extendedIndicator (Icc (0 : ℝ) 2) 1 = (r : EReal) := by
    refine ⟨0, ?_⟩
    norm_num [extendedIndicator]
  simpa only [gradient_fun_const] using
    theorem_2_22_gradient _ hc 1 hx (fun _ => (0 : ℝ)) he (differentiableAt_const 0)

theorem quadratic_singleton_nonzero :
    SourceSubdifferential (fun y : ℝ => ((y^2 : ℝ) : EReal)) 1 = {(2 : ℝ)} := by
  let f : ℝ → EReal := fun y => ((y^2 : ℝ) : EReal)
  have hbot : ∀ y, f y ≠ ⊥ := fun y => EReal.coe_ne_bot _
  have hdom : effectiveDomain f = univ := by
    ext y
    simp only [effectiveDomain, mem_setOf_eq, mem_univ, iff_true]
    exact EReal.coe_lt_top _
  have hc : IsConvexExtended f := by
    apply (convexExtended_iff_toReal f hbot).mpr
    rw [hdom]
    simpa only [f, EReal.toReal_coe] using SubgradientProbe.square_convex
  have hset := theorem_2_22_gradient f hc 1 ⟨1, by norm_num [f]⟩
    (fun y : ℝ => y^2) (Eventually.of_forall (fun y => rfl))
    (differentiableAt_id.pow 2)
  have hm : (2 : ℝ) ∈ SourceSubdifferential f 1 := by
    simpa only [f, mul_one] using SubgradientProbe.square_support 1
  rw [hset, mem_singleton_iff] at hm
  change SourceSubdifferential f 1 = {(2 : ℝ)}
  rw [hset, hm]

#print axioms constrained_interval_singleton
#print axioms quadratic_singleton_nonzero
end ForwardSubgradientProbe

namespace DifferentiabilityProbe
open BanditRL.OnlineConvex Set Filter
open scoped Topology

theorem constrained_interval_differentiable :
    SourceDifferentiableAt (extendedIndicator (Icc (0 : ℝ) 2)) 1 := by
  apply (theorem_2_22 _ ((convex_indicator_iff _).mpr (convex_Icc 0 2)) 1
    ⟨0, by norm_num [extendedIndicator]⟩).mpr
  exact ⟨0, ForwardSubgradientProbe.constrained_interval_singleton⟩

theorem quadratic_derivative_nonzero :
    HasGradientAt (fun y : ℝ => y^2) 2 1 := by
  let f : ℝ → EReal := fun y => ((y^2 : ℝ) : EReal)
  have hbot : ∀ y, f y ≠ ⊥ := fun y => EReal.coe_ne_bot _
  have hdom : effectiveDomain f = univ := by
    ext y
    simp only [effectiveDomain, mem_setOf_eq, mem_univ, iff_true]
    exact EReal.coe_lt_top _
  have hc : IsConvexExtended f := by
    apply (convexExtended_iff_toReal f hbot).mpr
    rw [hdom]
    simpa only [f, EReal.toReal_coe] using SubgradientProbe.square_convex
  simpa only [f, EReal.toReal_coe] using
    singleton_subdifferential_hasGradientAt f hc 1 ⟨1, by norm_num [f]⟩ 2
      ForwardSubgradientProbe.quadratic_singleton_nonzero

theorem interval_boundary_supports (g : ℝ) (hg : g ≤ 0) :
    g ∈ SourceSubdifferential (extendedIndicator (Icc (0 : ℝ) 2)) 0 := by
  intro y
  have hz : (0 : ℝ) ∈ Icc (0 : ℝ) 2 := by norm_num
  simp only [extendedIndicator, if_pos hz]
  by_cases hy : y ∈ Icc (0 : ℝ) 2
  · rw [if_pos hy, ← EReal.coe_zero, ← EReal.coe_add]
    apply EReal.coe_le_coe
    change 0 + (y - 0) * g ≤ 0
    nlinarith [hy.1]
  · rw [if_neg hy]
    exact le_top

theorem interval_boundary_not_differentiable :
    ¬ SourceDifferentiableAt (extendedIndicator (Icc (0 : ℝ) 2)) 0 := by
  intro hd
  obtain ⟨g, hg⟩ := (theorem_2_22 _
    ((convex_indicator_iff _).mpr (convex_Icc 0 2)) 0
    ⟨0, by norm_num [extendedIndicator]⟩).mp hd
  have hzero := interval_boundary_supports 0 (by norm_num)
  have hneg := interval_boundary_supports (-1) (by norm_num)
  rw [hg, mem_singleton_iff] at hzero hneg
  linarith

#print axioms constrained_interval_differentiable
#print axioms quadratic_derivative_nonzero
#print axioms interval_boundary_supports
#print axioms interval_boundary_not_differentiable
#print axioms BanditRL.OnlineConvex.theorem_2_22
#print axioms BanditRL.OnlineConvex.theorem_2_22_gradient
end DifferentiabilityProbe
