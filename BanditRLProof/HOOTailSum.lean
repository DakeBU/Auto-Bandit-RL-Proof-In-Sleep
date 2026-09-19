import BanditRLProof.HeavyTailTailSum

/-! Summable confidence failures after the HOO path/depth union. -/
namespace BanditRLProof.HOO

noncomputable def selectionFailureBudget (n : ℕ) : ℝ :=
  ((n:ℝ)+2)*n*Real.exp (-4*Real.log (max (n:ℝ) 2))

theorem selection_failure_exp_eq (n : ℕ) :
    Real.exp (-4*Real.log (max (n:ℝ) 2)) = 1/(max (n:ℝ) 2)^4 := by
  simpa [HeavyTail.confidenceLog, neg_mul] using HeavyTail.scheduled_exp_eq n

theorem selection_failure_le_telescope (n : ℕ) (hn : 2 ≤ n) :
    selectionFailureBudget n ≤ 2 * (1/((n:ℝ)-1) - 1/n) := by
  have hnR : (2:ℝ) ≤ n := by exact_mod_cast hn
  have hp : (0:ℝ) < n := by linarith
  have hm : (0:ℝ) < (n:ℝ)-1 := by linarith
  unfold selectionFailureBudget
  rw [selection_failure_exp_eq, max_eq_left hnR]
  apply (mul_le_mul_iff_left₀ (show 0 < (n:ℝ)^3*((n:ℝ)-1) by positivity)).mp
  field_simp
  nlinarith [sq_nonneg ((n:ℝ)-1)]

theorem selection_failure_sum_le_three (N : ℕ) :
    (∑ n ∈ Finset.range N, selectionFailureBudget n) ≤ 3 := by
  have hshift (N : ℕ) : (∑ s ∈ Finset.range N, selectionFailureBudget (s+2)) ≤ 2 := by
    calc
      _ ≤ ∑ s ∈ Finset.range N, 2*(1/((s:ℝ)+1)-1/((s:ℝ)+2)) := by
        apply Finset.sum_le_sum
        intro s _
        have he : (s:ℝ)+2-1=s+1 := by ring
        simpa only [Nat.cast_add, Nat.cast_ofNat, he] using
          selection_failure_le_telescope (s+2) (by omega)
      _ = 2*(1-1/((N:ℝ)+1)) := by rw [← Finset.mul_sum, HeavyTail.reciprocal_telescope]
      _ ≤ 2 := by
        have hh : 0 ≤ 1/((N:ℝ)+1) := by positivity
        linarith
  have hzero : selectionFailureBudget 0 = 0 := by simp [selectionFailureBudget]
  have hone : selectionFailureBudget 1 = 3/16 := by
    simp only [selectionFailureBudget, selection_failure_exp_eq]
    norm_num
  rcases N with _ | _ | N
  · norm_num
  · norm_num [Finset.sum_range_succ, hzero]
  · rw [show N+1+1=2+N by omega, Finset.sum_range_add]
    have hh := hshift N
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, hzero, hone,
      Nat.add_comm 2]
    linarith

end BanditRLProof.HOO
