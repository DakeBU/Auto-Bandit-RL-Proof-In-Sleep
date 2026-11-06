import BanditRLProof.OnlineGammaSimplexGeometry

open Set Finset
namespace BanditRL.OnlineGamma
noncomputable section

theorem massSimplexVertex_mem {n : ℕ} (T : ℝ) (hT : 0 ≤ T) (j : Fin n) :
    massSimplexVertex T j ∈ nonnegativeMassSimplex n T := by
  constructor
  · intro i
    simp only [massSimplexVertex, Pi.single_apply]
    split <;> positivity
  · simp [massSimplexVertex, Pi.single_apply]

theorem simplexGammaProduct_le_vertex_and_value :
  ∀ (n : ℕ) (T : ℝ), 1 ≤ n → 1 ≤ T →
    ∀ (x : Fin n → ℝ), x ∈ nonnegativeMassSimplex n T →
      ∀ j : Fin n, massSimplexVertex T j ∈ nonnegativeMassSimplex n T ∧
        simplexGammaProduct n x ≤ simplexGammaProduct n (massSimplexVertex T j) ∧
        simplexGammaProduct n (massSimplexVertex T j) =
          T ^ T / (Real.Gamma (T + 1/2) * Real.Gamma (1/2) ^ (n - 1)) := by
  intro n T hn hT x hx j
  have ht : 0 < T := lt_of_lt_of_le zero_lt_one hT
  have hver (i : Fin n) := massSimplexVertex_mem T ht.le i
  let M := T ^ T / (Real.Gamma (T + 1/2) * Real.Gamma (1/2) ^ (n - 1))
  have value (i : Fin n) : simplexGammaProduct n (massSimplexVertex T i) = M := by
    let f := fun k : Fin n => (massSimplexVertex T i k) ^ (massSimplexVertex T i k) /
      Real.Gamma (massSimplexVertex T i k + 1/2)
    change (∏ k, f k) = M
    rw [← Finset.mul_prod_erase Finset.univ f (Finset.mem_univ i)]
    have rest : (∏ k ∈ Finset.univ.erase i, f k) =
        ∏ _k ∈ Finset.univ.erase i, (1 / Real.Gamma (1/2)) := by
      apply Finset.prod_congr rfl
      intro k hk
      have hki := (Finset.mem_erase.mp hk).1
      simp [f, massSimplexVertex, Pi.single_apply, hki, Ne.symm hki]
    rw [rest]
    simp [f, massSimplexVertex, M, Finset.card_erase_of_mem, div_eq_mul_inv,
      mul_assoc, mul_left_comm, mul_comm]
  let G : (Fin n → ℝ) → ℝ := fun y => ∑ i, simplexLogFactor (y i)
  have geom := continuousOn_and_convexOn_sum_simplexLogFactor n hn T hT
  have hj := convexOn_le_sum_massSimplexVertex n T hn hT G geom.2 x hx
  have hlog (i : Fin n) : G (massSimplexVertex T i) = Real.log M := by
    rw [← value i]
    exact (simplexGammaProduct_pos_and_log n _ (hver i).1).2.symm
  have hmass : ∑ i, x i / T = 1 := by rw [← Finset.sum_div, hx.2, div_self ht.ne']
  simp only [hlog, ← Finset.sum_mul, hmass, one_mul] at hj
  obtain ⟨hpos, heq⟩ := simplexGammaProduct_pos_and_log n x hx.1
  refine ⟨hver j, (Real.log_le_log_iff hpos (simplexGammaProduct_pos_and_log n _ (hver j).1).1).mp ?_, value j⟩
  rw [value j, heq]
  exact hj

end
end BanditRL.OnlineGamma
