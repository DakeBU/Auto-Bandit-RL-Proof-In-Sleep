import BanditRLProof.OnlineGammaSimplex

open Set Finset
open BanditRL.OnlineGamma
namespace BanditRL.OnlineGamma.Canary
noncomputable section

theorem one_dimensional_unit_mass_vertex :
  let j : Fin 1 := 0
  let v := massSimplexVertex (1 : ℝ) j
  v ∈ nonnegativeMassSimplex 1 1 ∧
    simplexGammaProduct 1 v = 1 / Real.Gamma (3/2) ∧
    simplexGammaProduct 1 v = 2 / Real.sqrt Real.pi ∧
    Real.Gamma (1/2) ^ (1 - 1 : ℕ) = 1 := by
  dsimp only
  let j : Fin 1 := 0
  let v := massSimplexVertex (1 : ℝ) j
  have hv := massSimplexVertex_mem (1 : ℝ) zero_le_one j
  have q := simplexGammaProduct_le_vertex_and_value 1 1 (by decide) le_rfl v hv j
  have heq : simplexGammaProduct 1 v = 1 / Real.Gamma (3/2) := by
    convert q.2.2 using 1 <;> norm_num
  refine ⟨q.1, heq, ?_, by norm_num⟩
  rw [heq]
  have hg := Real.Gamma_add_one (s := (1/2 : ℝ)) (by norm_num)
  rw [Real.Gamma_one_half_eq] at hg
  rw [show (3/2 : ℝ) = 1/2 + 1 by norm_num, hg]
  ring_nf

theorem three_dimensional_fractional_mass_boundary :
  let T := (3/2 : ℝ)
  let x : Fin 3 → ℝ := ![0, 1/2, 1]
  x ∈ nonnegativeMassSimplex 3 T ∧
    simplexGammaProduct 3 x ≤ T ^ T / Real.pi ∧
    ∀ j : Fin 3, massSimplexVertex T j ∈ nonnegativeMassSimplex 3 T ∧ simplexGammaProduct 3 (massSimplexVertex T j) = T ^ T / Real.pi := by
  dsimp only
  let T : ℝ := 3/2
  let x : Fin 3 → ℝ := ![0, 1/2, 1]
  have hx : x ∈ nonnegativeMassSimplex 3 T := by
    constructor
    · intro i
      fin_cases i <;> norm_num [x]
    · norm_num [x, T, Fin.sum_univ_succ]
  have q (j : Fin 3) := simplexGammaProduct_le_vertex_and_value 3 T (by decide)
    (by norm_num [T]) x hx j
  have hden : Real.Gamma (T + 1/2) * Real.Gamma (1/2) ^ (3 - 1 : ℕ) = Real.pi := by
    rw [show T + 1/2 = 2 by norm_num [T], Real.Gamma_one_half_eq]
    norm_num [Real.Gamma_nat_eq_factorial, Real.sq_sqrt Real.pi_pos.le]
  refine ⟨hx, ?_, ?_⟩
  · exact (q 0).2.1.trans_eq (by simpa only [hden] using (q 0).2.2)
  · intro j
    exact ⟨(q j).1, by simpa only [hden] using (q j).2.2⟩

end
end BanditRL.OnlineGamma.Canary
