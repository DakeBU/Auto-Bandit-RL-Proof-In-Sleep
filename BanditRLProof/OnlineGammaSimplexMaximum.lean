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

namespace BanditRL.OnlineGamma

theorem convexOn_exists_isGreatest_massSimplexVertex
    (n : ℕ) (T : ℝ) (hn : 1 ≤ n) (hT : 1 ≤ T)
    (G : (Fin n → ℝ) → ℝ)
    (hG : ConvexOn ℝ (nonnegativeMassSimplex n T) G) :
    ∃ j : Fin n,
      IsGreatest (G '' nonnegativeMassSimplex n T) (G (massSimplexVertex T j)) := by
  classical
  have ht : 0 < T := lt_of_lt_of_le zero_lt_one hT
  let j0 : Fin n := ⟨0, by omega⟩
  have hnonempty : (Finset.univ : Finset (Fin n)).Nonempty :=
    ⟨j0, Finset.mem_univ j0⟩
  obtain ⟨j, _hj, hmax⟩ := Finset.exists_max_image Finset.univ
    (fun i : Fin n => G (massSimplexVertex T i)) hnonempty
  have hv := massSimplexVertex_mem T ht.le j
  refine ⟨j, ?_, ?_⟩
  · exact ⟨massSimplexVertex T j, hv, rfl⟩
  · rintro y ⟨x, hx, rfl⟩
    have hmass : ∑ i, x i / T = 1 := by
      rw [← Finset.sum_div, hx.2, div_self ht.ne']
    calc
      G x ≤ ∑ i, (x i / T) * G (massSimplexVertex T i) :=
        convexOn_le_sum_massSimplexVertex n T hn hT G hG x hx
      _ ≤ ∑ i, (x i / T) * G (massSimplexVertex T j) := by
        apply Finset.sum_le_sum
        intro i _hi
        exact mul_le_mul_of_nonneg_left (hmax i (Finset.mem_univ i))
          (div_nonneg (hx.1 i) ht.le)
      _ = G (massSimplexVertex T j) := by
        rw [← Finset.sum_mul, hmass, one_mul]

end BanditRL.OnlineGamma
