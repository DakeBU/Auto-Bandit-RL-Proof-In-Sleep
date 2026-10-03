import BanditRLProof.HeavyTailTuning
import BanditRLProof.HeavyTailClippedConfidence

/-! The actual algorithm's scheduled radius, produced from raw moments. -/
namespace BanditRLProof.HeavyTail
open MeasureTheory ProbabilityTheory

theorem scheduled_clipped_mean_tail {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : ℕ → Ω → ℝ)
    (ε u mean : ℝ) (t n : ℕ) (hn : 0 < n)
    (hXm : ∀ i, Measurable (X i)) (hi : iIndepFun X μ)
    (hε0 : 0 ≤ ε) (hε : ε ≤ 1) (hu0 : 0 < u)
    (hX : ∀ i, Integrable (X i) μ)
    (hmean : ∀ i, (∫ ω, X i ω ∂μ) = mean)
    (hm : ∀ i, Integrable (fun ω => |X i ω| ^ (1 + ε)) μ)
    (hu : ∀ i, (∫ ω, |X i ω| ^ (1 + ε) ∂μ) ≤ u) :
    μ.real {ω | confidenceRadius ε u t n ≤
      |(∑ s ∈ Finset.range n, clip (sampleThreshold ε u t s) (X s ω)) / n - mean|} ≤
        2 * Real.exp (-confidenceLog t) := by
  let b := 2 * (u*n/confidenceLog t)^(1/(1+ε))
  have hb : 0 < b := mul_pos (by norm_num)
    (Real.rpow_pos_of_pos (div_pos (mul_pos hu0 (Nat.cast_pos.mpr hn)) (confidenceLog_pos t)) _)
  have htail := clipped_mean_tail μ X (sampleThreshold ε u t) ε u b (confidenceLog t) mean n hn
    hXm hi (sampleThreshold_pos ε u hu0 t) hε0 hε hu0.le hb (confidenceLog_pos t).le
    (fun s hs => mul_le_mul_of_nonneg_left
      (sampleThreshold_le_terminal ε u hε0 hu0.le t n s (Finset.mem_range.mp hs)) (by norm_num))
    hX hmean hm hu
  change μ.real {ω | _ ≤ |(∑ s ∈ Finset.range n, clip (sampleThreshold ε u t s) (X s ω)) / n - mean|} ≤ _ at htail
  refine (measureReal_mono ?_ (by finiteness)).trans htail
  intro ω hω
  exact (tuned_radius_le ε u hε0 hε hu0 t n hn).trans hω

/-- Union over deterministic prefix sizes. The adaptive count is never asserted IID. -/
theorem scheduled_adaptive_clipped_mean_tail {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : ℕ → Ω → ℝ)
    (count : Ω → ℕ) (ε u mean : ℝ) (t : ℕ)
    (hXm : ∀ i, Measurable (X i)) (hi : iIndepFun X μ)
    (hε0 : 0 ≤ ε) (hε : ε ≤ 1) (hu0 : 0 < u)
    (hX : ∀ i, Integrable (X i) μ)
    (hmean : ∀ i, (∫ ω, X i ω ∂μ) = mean)
    (hm : ∀ i, Integrable (fun ω => |X i ω| ^ (1 + ε)) μ)
    (hu : ∀ i, (∫ ω, |X i ω| ^ (1 + ε) ∂μ) ≤ u) :
    μ.real {ω | 0 < count ω ∧ count ω ≤ t ∧ confidenceRadius ε u t (count ω) ≤
      |(∑ s ∈ Finset.range (count ω), clip (sampleThreshold ε u t s) (X s ω)) /
        count ω - mean|} ≤ t * (2 * Real.exp (-confidenceLog t)) := by
  let E := fun k => {ω | confidenceRadius ε u t (k+1) ≤
    |(∑ s ∈ Finset.range (k+1), clip (sampleThreshold ε u t s) (X s ω)) / ((k+1 : ℕ) : ℝ) - mean|}
  have hs : {ω | 0 < count ω ∧ count ω ≤ t ∧ confidenceRadius ε u t (count ω) ≤
      |(∑ s ∈ Finset.range (count ω), clip (sampleThreshold ε u t s) (X s ω)) /
        count ω - mean|} ⊆ ⋃ k ∈ Finset.range t, E k := by
    intro ω hω
    rcases hω with ⟨hpos, hle, hbad⟩
    apply Set.mem_iUnion.mpr ⟨count ω - 1, ?_⟩
    apply Set.mem_iUnion.mpr ⟨Finset.mem_range.mpr (by omega), ?_⟩
    have he : count ω - 1 + 1 = count ω := by omega
    simpa only [E, Set.mem_setOf_eq, he] using hbad
  calc
    _ ≤ μ.real (⋃ k ∈ Finset.range t, E k) := measureReal_mono hs (measure_ne_top _ _)
    _ ≤ ∑ k ∈ Finset.range t, μ.real (E k) := measureReal_biUnion_finset_le _ _
    _ ≤ ∑ _k ∈ Finset.range t, 2 * Real.exp (-confidenceLog t) := by
      apply Finset.sum_le_sum
      intro k _
      simpa only [E, Nat.cast_add, Nat.cast_one] using scheduled_clipped_mean_tail μ X ε u mean t (k+1)
        (by omega) hXm hi hε0 hε hu0 hX hmean hm hu
    _ = _ := by simp

end BanditRLProof.HeavyTail
