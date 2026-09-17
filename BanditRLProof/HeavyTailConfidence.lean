import BanditRLProof.HeavyTailFixedTilt

/-! Two-sided, tuned heavy-tail confidence. This closes the fixed-prefix
probability producer before the causal policy and adaptive-count assembly. -/
namespace BanditRLProof.HeavyTail
open MeasureTheory ProbabilityTheory

theorem exists_variance_tilt (V b L : ℝ) (hV : 0 ≤ V) (hb : 0 < b) (hL : 0 ≤ L) :
    ∃ t : ℝ, 0 ≤ t ∧ t * b ≤ 1 ∧
      -t * (2 * Real.sqrt (V * L) + b * L) + t^2 * V ≤ -L := by
  obtain ⟨t, ht, htb, hexp⟩ := Concentration.exists_tilt_fixedMGF_exponent_le_neg
    (V / b) (1 / b) L (div_nonneg hV hb.le) (one_div_pos.mpr hb) hL
  refine ⟨t, ht, (le_div_iff₀ hb).mp htb, ?_⟩
  have hs : (V / b) * L / (1 / b) = V * L := by field_simp
  have hq : (V / b) * (t^2 / (1 / b)) = t^2 * V := by field_simp
  have hl : L / (1 / b) = b * L := by field_simp
  simpa only [hs, hq, hl] using hexp

theorem neg_mgf {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (X : Ω → ℝ) (t v : ℝ)
    (h : Concentration.HasMGFUpperBoundAt X (-t) v μ) :
    Concentration.HasMGFUpperBoundAt (fun ω => -X ω) t v μ := by
  constructor
  · intro s
    simpa only [mul_neg, neg_mul] using h.integrable_exp_mul (-s)
  · simpa only [ProbabilityTheory.mgf, mul_neg, neg_mul] using h.mgf_le

theorem fixed_mgf_abs_tail {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Ω → ℝ)
    (V b L : ℝ) (hV : 0 ≤ V) (hb : 0 < b) (hL : 0 ≤ L)
    (h : ∀ t : ℝ, |t| * b ≤ 1 →
      Concentration.HasMGFUpperBoundAt X t (t^2 * V) μ) :
    μ.real {ω | 2 * Real.sqrt (V * L) + b * L ≤ |X ω|} ≤ 2 * Real.exp (-L) := by
  obtain ⟨t, ht, htb, he⟩ := exists_variance_tilt V b L hV hb hL
  have ha : |t| * b ≤ 1 := by simpa only [abs_of_nonneg ht] using htb
  have hp := (h t ha).measure_ge_le_exp_add (2 * Real.sqrt (V * L) + b * L) ht
  have hn := (neg_mgf μ X t (t^2 * V) (by
    simpa using h (-t) (by simpa using ha))).measure_ge_le_exp_add
      (2 * Real.sqrt (V * L) + b * L) ht
  have he' := Real.exp_le_exp.mpr he
  calc
    μ.real {ω | 2 * Real.sqrt (V * L) + b * L ≤ |X ω|} ≤
      μ.real ({ω | 2 * Real.sqrt (V * L) + b * L ≤ X ω} ∪
        {ω | 2 * Real.sqrt (V * L) + b * L ≤ -X ω}) := by
      refine measureReal_mono ?_ (by finiteness)
      intro ω hw
      rcases le_total (X ω) 0 with hx | hx
      · exact Or.inr (by simpa only [Set.mem_setOf_eq, abs_of_nonpos hx] using hw)
      · exact Or.inl (by simpa only [Set.mem_setOf_eq, abs_of_nonneg hx] using hw)
    _ ≤ μ.real {ω | 2 * Real.sqrt (V * L) + b * L ≤ X ω} +
        μ.real {ω | 2 * Real.sqrt (V * L) + b * L ≤ -X ω} := measureReal_union_le _ _
    _ ≤ 2 * Real.exp (-L) := by linarith

/-- Two-sided centered sum, with variance budget and maximum increment bound
derived from the raw moments and deterministic truncation thresholds. -/
theorem truncated_sum_abs_tail {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : ℕ → Ω → ℝ)
    (B : ℕ → ℝ) (ε u b L : ℝ) (n : ℕ)
    (hXm : ∀ i, Measurable (X i)) (hi : iIndepFun X μ)
    (hB : ∀ i, 0 < B i) (hε : ε ≤ 1) (hu0 : 0 ≤ u) (hb : 0 < b) (hL : 0 ≤ L)
    (hbound : ∀ i ∈ Finset.range n, 2 * B i ≤ b)
    (hm : ∀ i, Integrable (fun ω => |X i ω| ^ (1 + ε)) μ)
    (hu : ∀ i, (∫ ω, |X i ω| ^ (1 + ε) ∂μ) ≤ u) :
    μ.real {ω | 2 * Real.sqrt ((∑ i ∈ Finset.range n, u * (B i)^(1-ε)) * L) + b * L ≤
      |∑ i ∈ Finset.range n,
        (truncate (B i) (X i ω) - ∫ ω, truncate (B i) (X i ω) ∂μ)|} ≤
        2 * Real.exp (-L) := by
  let Y := fun i ω => truncate (B i) (X i ω) - ∫ ω, truncate (B i) (X i ω) ∂μ
  have hYi : iIndepFun Y μ := hi.comp
    (fun i x => truncate (B i) x - ∫ ω, truncate (B i) (X i ω) ∂μ)
    (fun i => (measurable_truncate (B i)).sub measurable_const)
  have hYm : ∀ i, Measurable (Y i) := fun i =>
    ((measurable_truncate (B i)).comp (hXm i)).sub measurable_const
  have hsum := fixed_mgf_abs_tail μ (∑ i ∈ Finset.range n, Y i)
    (∑ i ∈ Finset.range n, u * (B i)^(1-ε)) b L
    (Finset.sum_nonneg fun i _ => mul_nonneg hu0 (Real.rpow_nonneg (hB i).le _)) hb hL
    (fun t ht => by
      have hg := independent_sum_mgf μ Y (Finset.range n) t
        (fun i => t^2 * (u * (B i)^(1-ε))) hYi hYm
        (fun i his => truncated_centered_mgf μ (X i) (B i) ε u t
          (hXm i) (hB i) hε (hm i) (hu i)
          ((mul_le_mul_of_nonneg_left (hbound i his) (abs_nonneg t)).trans ht))
      simpa only [Finset.mul_sum] using hg)
  simpa only [Y, Finset.sum_apply] using hsum

/-- The bias is produced from the same raw moment hypotheses as the fluctuation.
The common mean is a distributional assumption, not a confidence assumption. -/
theorem truncated_sum_mean_tail {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : ℕ → Ω → ℝ)
    (B : ℕ → ℝ) (ε u b L mean : ℝ) (n : ℕ)
    (hXm : ∀ i, Measurable (X i)) (hi : iIndepFun X μ)
    (hB : ∀ i, 0 < B i) (hε0 : 0 ≤ ε) (hε : ε ≤ 1)
    (hu0 : 0 ≤ u) (hb : 0 < b) (hL : 0 ≤ L)
    (hbound : ∀ i ∈ Finset.range n, 2 * B i ≤ b)
    (hX : ∀ i, Integrable (X i) μ)
    (hmean : ∀ i, (∫ ω, X i ω ∂μ) = mean)
    (hm : ∀ i, Integrable (fun ω => |X i ω| ^ (1 + ε)) μ)
    (hu : ∀ i, (∫ ω, |X i ω| ^ (1 + ε) ∂μ) ≤ u) :
    μ.real {ω | (∑ i ∈ Finset.range n, u / (B i)^ε) +
      (2 * Real.sqrt ((∑ i ∈ Finset.range n, u * (B i)^(1-ε)) * L) + b * L) ≤
      |(∑ i ∈ Finset.range n, truncate (B i) (X i ω)) - n * mean|} ≤
        2 * Real.exp (-L) := by
  have hbias : |∑ i ∈ Finset.range n,
      ((∫ ω, truncate (B i) (X i ω) ∂μ) - mean)| ≤
      ∑ i ∈ Finset.range n, u / (B i)^ε := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
    have h := integral_truncate_bias_le μ (X i) (B i) ε u
      (hB i) hε0 (hXm i) (hX i) (hm i) (hu i)
    rw [hmean i, abs_sub_comm] at h
    exact h
  refine (measureReal_mono ?_ (by finiteness)).trans
    (truncated_sum_abs_tail μ X B ε u b L n hXm hi hB hε hu0 hb hL hbound hm hu)
  intro ω hw
  have hid : (∑ i ∈ Finset.range n, truncate (B i) (X i ω)) - n * mean =
      (∑ i ∈ Finset.range n,
        (truncate (B i) (X i ω) - ∫ ω, truncate (B i) (X i ω) ∂μ)) +
      ∑ i ∈ Finset.range n, ((∫ ω, truncate (B i) (X i ω) ∂μ) - mean) := by
    simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    ring
  have htri := abs_add_le
    (∑ i ∈ Finset.range n,
      (truncate (B i) (X i ω) - ∫ ω, truncate (B i) (X i ω) ∂μ))
    (∑ i ∈ Finset.range n, ((∫ ω, truncate (B i) (X i ω) ∂μ) - mean))
  simp only [Set.mem_setOf_eq] at hw ⊢
  rw [hid] at hw
  linarith

/-- Fixed positive sample-size confidence for the actual truncated empirical mean. -/
theorem truncated_mean_tail {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : ℕ → Ω → ℝ)
    (B : ℕ → ℝ) (ε u b L mean : ℝ) (n : ℕ) (hn : 0 < n)
    (hXm : ∀ i, Measurable (X i)) (hi : iIndepFun X μ)
    (hB : ∀ i, 0 < B i) (hε0 : 0 ≤ ε) (hε : ε ≤ 1)
    (hu0 : 0 ≤ u) (hb : 0 < b) (hL : 0 ≤ L)
    (hbound : ∀ i ∈ Finset.range n, 2 * B i ≤ b)
    (hX : ∀ i, Integrable (X i) μ)
    (hmean : ∀ i, (∫ ω, X i ω ∂μ) = mean)
    (hm : ∀ i, Integrable (fun ω => |X i ω| ^ (1 + ε)) μ)
    (hu : ∀ i, (∫ ω, |X i ω| ^ (1 + ε) ∂μ) ≤ u) :
    μ.real {ω | ((∑ i ∈ Finset.range n, u / (B i)^ε) +
      (2 * Real.sqrt ((∑ i ∈ Finset.range n, u * (B i)^(1-ε)) * L) + b * L)) / n ≤
      |(∑ i ∈ Finset.range n, truncate (B i) (X i ω)) / n - mean|} ≤
        2 * Real.exp (-L) := by
  have hn' : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have heq : ∀ z : ℝ, z / n - mean = (z - n * mean) / n := by
    intro z
    field_simp
  simp_rw [heq, abs_div, abs_of_pos hn', div_le_div_iff_of_pos_right hn']
  exact truncated_sum_mean_tail μ X B ε u b L mean n hXm hi hB hε0 hε hu0 hb hL
    hbound hX hmean hm hu

end BanditRLProof.HeavyTail
