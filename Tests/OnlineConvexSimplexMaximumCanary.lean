import BanditRLProof.OnlineGammaSimplexMaximum

namespace BanditRL.OnlineGamma.Canary

theorem coordinate_projection_mass_two_isGreatest :
  let G : (Fin 2 → ℝ) → ℝ := fun x => x (0 : Fin 2)
  IsGreatest (G '' nonnegativeMassSimplex 2 (2 : ℝ)) (2 : ℝ) ∧
    massSimplexVertex (2 : ℝ) (0 : Fin 2) ∈ nonnegativeMassSimplex 2 (2 : ℝ) ∧
    G (massSimplexVertex (2 : ℝ) (1 : Fin 2)) = (0 : ℝ) := by
  dsimp only
  let G : (Fin 2 → ℝ) → ℝ := fun x => x (0 : Fin 2)
  have hG : ConvexOn ℝ (nonnegativeMassSimplex 2 (2 : ℝ)) G := by
    constructor
    · exact (continuousOn_and_convexOn_sum_simplexLogFactor 2 (by decide) 2 (by norm_num)).2.1
    · intro x hx y hy a b ha hb hab
      exact le_rfl
  have hv0 := massSimplexVertex_mem (2 : ℝ) (by norm_num) (0 : Fin 2)
  obtain ⟨j, hj⟩ := convexOn_exists_isGreatest_massSimplexVertex 2 2
    (by decide) (by norm_num) G hG
  have hgreatest : IsGreatest (G '' nonnegativeMassSimplex 2 (2 : ℝ)) (2 : ℝ) := by
    fin_cases j
    · simpa [G, massSimplexVertex] using hj
    · have h := hj.2 ⟨massSimplexVertex (2 : ℝ) (0 : Fin 2), hv0, rfl⟩
      norm_num [G, massSimplexVertex] at h
  exact ⟨hgreatest, hv0, by simp [G, massSimplexVertex]⟩

end BanditRL.OnlineGamma.Canary
