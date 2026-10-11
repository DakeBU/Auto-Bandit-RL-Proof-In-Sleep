import BanditRLProof.OnlineNormalCone
import Mathlib.Analysis.InnerProductSpace.PiL2

namespace NormalIndicatorProbe
open BanditRL.OnlineConvex Set

theorem interval_boundary_and_outside_canary :
    (-1 : ℝ) ∈ SourceSubdifferential (extendedIndicator (Icc (0 : ℝ) 1)) 0 ∧
    (1 : ℝ) ∉ SourceSubdifferential (extendedIndicator (Icc (0 : ℝ) 1)) 0 ∧
    SourceSubdifferential (extendedIndicator (Icc (0 : ℝ) 1)) 2 = ∅ := by
  have hVn : (Icc (0 : ℝ) 1).Nonempty := ⟨0, by norm_num⟩
  rw [indicator_subdifferential_eq_normalCone _ hVn (convex_Icc 0 1) 0,
      indicator_subdifferential_eq_normalCone _ hVn (convex_Icc 0 1) 2]
  constructor
  · refine ⟨by norm_num, ?_⟩
    intro y hy
    change (y - 0) * (-1) ≤ 0
    nlinarith [hy.1]
  constructor
  · intro hg
    have h := hg.2 1 (by norm_num)
    change (1 - 0) * (1 : ℝ) ≤ 0 at h
    norm_num at h
  · ext g
    simp [SourceNormalCone]

theorem thin_singleton_all_normals_canary :
    SourceSubdifferential (extendedIndicator ({(0 : ℝ)} : Set ℝ)) 0 = univ ∧
    (7 : ℝ) ∈ SourceSubdifferential (extendedIndicator ({(0 : ℝ)} : Set ℝ)) 0 := by
  have hVn : ({(0 : ℝ)} : Set ℝ).Nonempty := ⟨0, rfl⟩
  rw [indicator_subdifferential_eq_normalCone _ hVn (convex_singleton (0 : ℝ)) 0]
  have h : SourceNormalCone ({(0 : ℝ)} : Set ℝ) 0 = univ := by
    ext g
    simp [SourceNormalCone]
  simp [h]

#print axioms interval_boundary_and_outside_canary
#print axioms thin_singleton_all_normals_canary
end NormalIndicatorProbe

namespace NormalGeometryProbe
open BanditRL.OnlineConvex Set

theorem interval_interior_canary :
    SourceSubdifferential (extendedIndicator (Icc (0 : ℝ) 1)) (1 / 2 : ℝ) = {0} := by
  have hVn : (Icc (0 : ℝ) 1).Nonempty := ⟨0, by norm_num⟩
  rw [indicator_subdifferential_eq_normalCone _ hVn (convex_Icc 0 1)]
  exact normalCone_interior_eq_zero _ hVn (convex_Icc 0 1) _ (by
    rw [interior_Icc]
    norm_num)

noncomputable def e0 : EuclideanSpace ℝ (Fin 2) := PiLp.single 2 0 1
noncomputable def e1 : EuclideanSpace ℝ (Fin 2) := PiLp.single 2 1 1

theorem two_dimensional_unit_boundary_canary :
    (2 : ℝ) • e0 ∈ SourceNormalCone {y : EuclideanSpace ℝ (Fin 2) | ‖y‖ ≤ 1} e0 ∧
    (0 : EuclideanSpace ℝ (Fin 2)) ∈ SourceNormalCone {y : EuclideanSpace ℝ (Fin 2) | ‖y‖ ≤ 1} e0 ∧
    e1 ∉ SourceNormalCone {y : EuclideanSpace ℝ (Fin 2) | ‖y‖ ≤ 1} e0 ∧
    -e0 ∉ SourceNormalCone {y : EuclideanSpace ℝ (Fin 2) | ‖y‖ ≤ 1} e0 := by
  rw [normalCone_unitBall_boundary e0 (by simp [e0])]
  refine ⟨⟨2, by norm_num, rfl⟩, ⟨0, le_rfl, by simp⟩, ?_, ?_⟩
  · rintro ⟨a, ha, he⟩
    have h := congrArg (fun v : EuclideanSpace ℝ (Fin 2) => v 1) he
    simp [e0, e1] at h
  · rintro ⟨a, ha, he⟩
    have h := congrArg (fun v : EuclideanSpace ℝ (Fin 2) => v 0) he
    simp [e0] at h
    linarith

#print axioms interval_interior_canary
#print axioms two_dimensional_unit_boundary_canary
end NormalGeometryProbe
