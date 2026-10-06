import BanditRLProof
namespace Tests.OnlineDifferentiabilityBoundary
open BanditRL.OnlineConvex Set Filter
open scoped Topology

theorem singleton_toReal_differentiable :
    DifferentiableAt ℝ (fun y : ℝ => (extendedIndicator ({1} : Set ℝ) y).toReal) 1 := by
  have hzero : (fun y : ℝ => (extendedIndicator ({1} : Set ℝ) y).toReal) =
      (fun _ : ℝ => (0 : ℝ)) := by
    funext y
    by_cases hy : y ∈ ({1} : Set ℝ)
    · simp [extendedIndicator, hy]
    · simp [extendedIndicator, hy]
  rw [hzero]
  exact differentiableAt_const 0

theorem singleton_not_sourceDifferentiable :
    ¬ SourceDifferentiableAt (extendedIndicator ({1} : Set ℝ)) 1 := by
  intro hd
  have hi := (sourceDifferentiableAt_regular _ _ hd).2.1
  rw [effectiveDomain_indicator, interior_singleton] at hi
  simpa using hi

theorem singleton_global_supports (g : ℝ) :
    g ∈ SourceSubdifferential (extendedIndicator ({1} : Set ℝ)) 1 := by
  intro y
  have hx : (1 : ℝ) ∈ ({1} : Set ℝ) := mem_singleton 1
  by_cases hy : y ∈ ({1} : Set ℝ)
  · have hey : y = 1 := mem_singleton_iff.mp hy
    subst y
    simp [extendedIndicator]
  · simp only [extendedIndicator, if_pos hx, if_neg hy]
    exact le_top

end Tests.OnlineDifferentiabilityBoundary
