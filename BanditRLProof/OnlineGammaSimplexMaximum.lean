import BanditRLProof.OnlineGammaSimplex

namespace BanditRL.OnlineGamma

theorem isGreatest_simplexGammaProduct_image (n : ℕ) (T : ℝ) (hn : 1 ≤ n) (hT : 1 ≤ T) :
    IsGreatest ((simplexGammaProduct n) '' (nonnegativeMassSimplex n T))
      (T ^ T / (Real.Gamma (T + 1/2) * Real.Gamma (1/2) ^ (n - 1))) := by
  let j : Fin n := ⟨0, by omega⟩
  have hv := massSimplexVertex_mem T (le_trans (by norm_num : (0 : ℝ) ≤ 1) hT) j
  have hval := (simplexGammaProduct_le_vertex_and_value n T hn hT
    (massSimplexVertex T j) hv j).2.2
  constructor
  · exact ⟨massSimplexVertex T j, hv, hval⟩
  · rintro y ⟨x, hx, rfl⟩
    have hb := simplexGammaProduct_le_vertex_and_value n T hn hT x hx j
    exact hb.2.1.trans_eq hb.2.2

end BanditRL.OnlineGamma
