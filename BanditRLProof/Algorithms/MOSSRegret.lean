import BanditRLProof.Algorithms.MOSSStream
import BanditRLProof.RealMeanRegretPullCount
import BanditRLProof.PullCountDecomposition

noncomputable section
open Real Finset MeasureTheory ProbabilityTheory
namespace BanditRLProof.MOSS

/-- Pathwise regret split with a deterministic large-gap filter for integration. -/
theorem streamTrace_gapSum_le {Ω : Type*} [MeasurableSpace Ω]
    {k : ℕ} (hk : 0 < k) (n : ℕ) (hkn : k ≤ n)
    (mean : Fin k → ℝ) (X : Fin k → ℕ → Ω → ℝ) (ω : Ω) (best : Fin k)
    (hbest : ∀ a, mean a ≤ mean best) :
    (∑ a, (mean best - mean a) * (pullCount (streamTrace hk n mean X ω) a n : ℝ)) ≤
      (8*sqrt ((k : ℝ)/(n : ℝ)) + 2*optimismDeficit (X best) ((k : ℝ)/(n : ℝ)) n ω)*(n : ℝ) +
      ∑ a, if 8*sqrt ((k : ℝ)/(n : ℝ)) ≤ mean best - mean a then
        (mean best - mean a) * (1 + indexExceedanceCount (streamMean (X a) ω)
          ((k : ℝ)/(n : ℝ)) (mean best - mean a) n) else 0 := by
  classical
  let δ : ℝ := (k : ℝ)/(n : ℝ)
  let Z := optimismDeficit (X best) δ n ω
  have hZ : 0 ≤ Z := optimismDeficit_nonneg _ _ _ _
  have hbase : 0 ≤ 8*sqrt δ + 2*Z := by positivity
  have hterm (a : Fin k) :
      (mean best - mean a) * (pullCount (streamTrace hk n mean X ω) a n : ℝ) ≤
      (8*sqrt δ+2*Z)*(pullCount (streamTrace hk n mean X ω) a n : ℝ) +
      (if 8*sqrt δ ≤ mean best - mean a then
        (mean best - mean a)*(1+indexExceedanceCount (streamMean (X a) ω) δ (mean best-mean a) n)
        else 0) := by
    have hg : 0 ≤ mean best - mean a := sub_nonneg.mpr (hbest a)
    have hc : 0 ≤ indexExceedanceCount (streamMean (X a) ω) δ (mean best-mean a) n := by
      unfold indexExceedanceCount
      apply sum_nonneg
      intro s _
      split_ifs <;> norm_num
    by_cases hl : 8*sqrt δ ≤ mean best - mean a
    · rw [if_pos hl]
      by_cases hz : 2*Z < mean best - mean a
      · have ht := mul_le_mul_of_nonneg_left
          (streamTrace_pullCount_le hk n hkn mean X ω best a hz) hg
        have hb := mul_nonneg hbase (Nat.cast_nonneg (α := ℝ) (pullCount (streamTrace hk n mean X ω) a n))
        linarith
      · have hsmall : mean best - mean a ≤ 8*sqrt δ+2*Z := by
          nlinarith [sqrt_nonneg δ]
        have ht := mul_le_mul_of_nonneg_right hsmall
          (Nat.cast_nonneg (α := ℝ) (pullCount (streamTrace hk n mean X ω) a n))
        have hr := mul_nonneg hg (show 0 ≤ 1+indexExceedanceCount (streamMean (X a) ω) δ (mean best-mean a) n by linarith)
        linarith
    · rw [if_neg hl, add_zero]
      apply mul_le_mul_of_nonneg_right _ (Nat.cast_nonneg _)
      linarith
  have hsum := sum_le_sum (fun a (_ : a ∈ (univ : Finset (Fin k))) => hterm a)
  rw [sum_add_distrib, ← mul_sum] at hsum
  have hcount : (∑ a, (pullCount (streamTrace hk n mean X ω) a n : ℝ)) = n := by
    exact_mod_cast finset_sum_pullCount_eq_time (streamTrace hk n mean X ω) n
  rw [hcount] at hsum
  exact hsum

theorem streamTrace_realMeanRegret_le {Ω : Type*} [MeasurableSpace Ω]
    {k : ℕ} (hk : 0 < k) (n : ℕ) (hkn : k ≤ n)
    (mean : Fin k → ℝ) (X : Fin k → ℕ → Ω → ℝ) (ω : Ω) (best : Fin k)
    (hbest : ∀ a, mean a ≤ mean best) :
    realMeanRegret mean (streamTrace hk n mean X ω) n ≤
      (8*sqrt ((k : ℝ)/(n : ℝ)) + 2*optimismDeficit (X best) ((k : ℝ)/(n : ℝ)) n ω)*(n : ℝ) +
      ∑ a, if 8*sqrt ((k : ℝ)/(n : ℝ)) ≤ mean best - mean a then
        (mean best - mean a) * (1 + indexExceedanceCount (streamMean (X a) ω)
          ((k : ℝ)/(n : ℝ)) (mean best - mean a) n) else 0 := by
  letI : Nonempty (Fin k) := ⟨best⟩
  have hsup : (⨆ a, mean a) = mean best :=
    le_antisymm (ciSup_le hbest) (le_ciSup (Finite.bddAbove_range mean) best)
  rw [realMeanRegret_eq_sum_gap_mul_pullCount]
  simp only [realMeanGap, hsup]
  exact streamTrace_gapSum_le hk n hkn mean X ω best hbest

/-- Integrated large-gap contribution, with the single initialization gap term. -/
theorem integral_largeGapCountSum_le {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {k : ℕ}
    (mean : Fin k → ℝ) (X : Fin k → ℕ → Ω → ℝ) (best : Fin k)
    (hbest : ∀ a, mean a ≤ mean best)
    (hXm : ∀ a i, StronglyMeasurable (X a i))
    (hind : ∀ a, iIndepFun (X a) μ)
    (hmean : ∀ a i, ∫ ω, X a i ω ∂μ = 0)
    (hsubG : ∀ a i, HasSubgaussianMGF (X a i) 1 μ)
    (δ : ℝ) (hδ : 0 < δ) (n : ℕ) :
    (∫ ω, ∑ a, if 8*sqrt δ ≤ mean best - mean a then
      (mean best - mean a)*(1+indexExceedanceCount (streamMean (X a) ω) δ (mean best-mean a) n)
      else 0 ∂μ) ≤ (∑ a, (mean best-mean a)) + (k : ℝ)*(15/sqrt δ) := by
  classical
  let f : Fin k → Ω → ℝ := fun a ω => if 8*sqrt δ ≤ mean best-mean a then
    (mean best-mean a)*(1+indexExceedanceCount (streamMean (X a) ω) δ (mean best-mean a) n) else 0
  have hi (a : Fin k) : Integrable (f a) μ := by
    dsimp [f]
    split_ifs
    · exact ((integrable_const 1).add (integrable_indexExceedanceCount (X a) (hXm a) δ _ n)).const_mul _
    · exact integrable_const 0
  have hb (a : Fin k) : (∫ ω, f a ω ∂μ) ≤ mean best-mean a + 15/sqrt δ := by
    have hg : 0 ≤ mean best-mean a := sub_nonneg.mpr (hbest a)
    dsimp [f]
    split_ifs with hl
    · have hgp : 0 < mean best-mean a := lt_of_lt_of_le (by positivity) hl
      have hc := gap_mul_integral_indexExceedanceCount_le_sharp (X a) (hXm a) (hind a)
        (hmean a) (hsubG a) δ (mean best-mean a) hδ hgp hl n
      rw [integral_const_mul]
      rw [integral_add (integrable_const 1) (integrable_indexExceedanceCount (X a) (hXm a) δ _ n)]
      simp only [integral_const, probReal_univ, one_smul]
      nlinarith
    · simp only [integral_zero]
      positivity
  change (∫ ω, ∑ a, f a ω ∂μ) ≤ _
  rw [integral_finset_sum _ (fun a _ => hi a)]
  calc
    _ ≤ ∑ a, (mean best-mean a+15/sqrt δ) := sum_le_sum (fun a _ => hb a)
    _ = _ := by simp [sum_add_distrib, mul_comm]

end BanditRLProof.MOSS
