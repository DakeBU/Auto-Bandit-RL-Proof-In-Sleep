import BanditRLProof
import Tests.OnlineConvexMinorantCanary

noncomputable section
open Set BanditRL.OnlineConvex
open scoped Topology
namespace Tests.OnlineRelativeSubgradient

theorem ray_relative_contact :
    ∃ x ∈ intrinsicInterior ℝ (effectiveDomain Tests.OnlineConvexMinorant.loss),
      ∃ (a : (ℝ × ℝ) →L[ℝ] ℝ) (b : ℝ),
        ((a x + b : ℝ) : EReal) = Tests.OnlineConvexMinorant.loss x ∧
        ∀ y, ((a y + b : ℝ) : EReal) ≤ Tests.OnlineConvexMinorant.loss y := by
  have hne : (effectiveDomain Tests.OnlineConvexMinorant.loss).Nonempty := by
    rw [Tests.OnlineConvexMinorant.loss_domain]
    exact ⟨(1, 0), by norm_num [Tests.OnlineConvexBarycenter.ray]⟩
  obtain ⟨x, hx⟩ := hne.intrinsicInterior
    (convex_effectiveDomain _ Tests.OnlineConvexMinorant.loss_convex)
  obtain ⟨a, b, htouch, hminor⟩ := affine_support_of_relative_domain_interior
    Tests.OnlineConvexMinorant.loss Tests.OnlineConvexMinorant.loss_noBot
    Tests.OnlineConvexMinorant.loss_convex x hx
  exact ⟨x, hx, a, b, htouch, hminor⟩


theorem singleton_relative_support :
    (SourceSubdifferential (extendedIndicator ({1} : Set ℝ)) 1).Nonempty := by
  apply subgradient_exists_of_relative_domain_interior
  · exact (sourceProper_indicator_iff _).mpr ⟨1, by simp⟩
  · exact (convex_indicator_iff _).mpr (convex_singleton (1 : ℝ))
  · rw [effectiveDomain_indicator, intrinsicInterior_singleton]
    simp


theorem singleton_boundary :
    extendedIndicator ({1} : Set ℝ) 1 = 0 ∧
    extendedIndicator ({1} : Set ℝ) 0 = ⊤ ∧
    interior (effectiveDomain (extendedIndicator ({1} : Set ℝ))) = ∅ := by
  classical
  refine ⟨?_, ?_, ?_⟩
  · simp [extendedIndicator]
  · norm_num [extendedIndicator]
  · rw [effectiveDomain_indicator, interior_singleton]

end Tests.OnlineRelativeSubgradient
