import BanditRLProof.Algorithms.MOSSOptimism

noncomputable section
open Real Finset
namespace BanditRLProof.MOSS

def fixedLogRadius (δ gap : ℝ) (s : ℕ) : ℝ :=
  sqrt (4/(s : ℝ)*logPlus (gap^2/δ))

theorem sampleRadius_le_fixedLogRadius (δ gap : ℝ) (s : ℕ)
    (hδ : 0 < δ) (hg : 0 < gap) (hs : 0 < s) (hlarge : 1 ≤ (s : ℝ)*gap^2) :
    sqrt (4/(s : ℝ)*logPlus (1/((s : ℝ)*δ))) ≤ fixedLogRadius δ gap s := by
  have hsR : 0 < (s : ℝ) := Nat.cast_pos.mpr hs
  apply sqrt_le_sqrt
  apply mul_le_mul_of_nonneg_left (logPlus_mono ?_) (by positivity)
  apply (div_le_div_iff₀ (mul_pos hsR hδ) hδ).mpr
  nlinarith [mul_le_mul_of_nonneg_right hlarge hδ.le]

def indexExceedanceCount (mean : ℕ → ℝ) (δ gap : ℝ) (n : ℕ) : ℝ :=
  ∑ s ∈ range n, if gap/2 ≤ mean (s+1) +
    sqrt (4/((s+1 : ℕ) : ℝ)*logPlus (1/(((s+1 : ℕ) : ℝ)*δ))) then 1 else 0

def fixedLogExceedanceCount (mean : ℕ → ℝ) (δ gap : ℝ) (n : ℕ) : ℝ :=
  ∑ s ∈ range n, if gap/2 ≤ mean (s+1) + fixedLogRadius δ gap (s+1) then 1 else 0

def smallSampleCount (gap : ℝ) (n : ℕ) : ℝ :=
  ∑ s ∈ range n, if ((s+1 : ℕ) : ℝ)*gap^2 < 1 then 1 else 0

/-- Source correction step before applying Lemma 8.2, with no stochastic premise. -/
theorem indexExceedanceCount_le_small_add_fixed (mean : ℕ → ℝ)
    (δ gap : ℝ) (hδ : 0 < δ) (hg : 0 < gap) (n : ℕ) :
    indexExceedanceCount mean δ gap n ≤
      smallSampleCount gap n + fixedLogExceedanceCount mean δ gap n := by
  unfold indexExceedanceCount smallSampleCount fixedLogExceedanceCount
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro s hs
  by_cases hsmall : ((s+1 : ℕ) : ℝ)*gap^2 < 1
  · simp only [hsmall, ite_true]
    split_ifs <;> norm_num
  · have hr := sampleRadius_le_fixedLogRadius δ gap (s+1) hδ hg (by omega)
      (le_of_not_gt hsmall)
    simp only [hsmall, ite_false, zero_add]
    split_ifs <;> norm_num <;> linarith

theorem smallSampleCount_le_horizon (gap : ℝ) (n : ℕ) :
    smallSampleCount gap n ≤ (n : ℝ) := by
  unfold smallSampleCount
  calc
    _ ≤ ∑ _s ∈ range n, (1 : ℝ) := Finset.sum_le_sum (fun s _ => by split_ifs <;> norm_num)
    _ = _ := by simp

theorem smallSampleCount_le_inv_sq (gap : ℝ) (hg : 0 < gap) (n : ℕ) :
    smallSampleCount gap n ≤ 1/gap^2 := by
  have hg2 : 0 < gap^2 := sq_pos_of_pos hg
  induction n with
  | zero => simpa only [smallSampleCount, Finset.range_zero, Finset.sum_empty] using
      (le_of_lt (div_pos zero_lt_one hg2))
  | succ n ih =>
    by_cases h : ((n+1 : ℕ) : ℝ)*gap^2 < 1
    · exact (smallSampleCount_le_horizon gap (n+1)).trans
        ((le_div_iff₀ hg2).mpr h.le)
    · unfold smallSampleCount
      rw [Finset.sum_range_succ, if_neg h, add_zero]
      exact ih

theorem indexExceedanceCount_le_inv_sq_add_fixed (mean : ℕ → ℝ)
    (δ gap : ℝ) (hδ : 0 < δ) (hg : 0 < gap) (n : ℕ) :
    indexExceedanceCount mean δ gap n ≤
      1/gap^2 + fixedLogExceedanceCount mean δ gap n :=
  (indexExceedanceCount_le_small_add_fixed mean δ gap hδ hg n).trans
    (add_le_add (smallSampleCount_le_inv_sq gap hg n) le_rfl)

end BanditRLProof.MOSS
