import BanditRLProof.HeavyTailUnshiftedMGF
import BanditRLProof.HeavyTailConfidence
import BanditRLProof.HeavyTailTuning

/-! Arbitrary-log-confidence sample-index truncation. The target is the constant
four confidence radius of BCL 2013 Lemma 1; algorithm regret remains separate. -/
namespace BanditRLProof.HeavyTail
open MeasureTheory ProbabilityTheory

noncomputable def sourceTruncationThreshold (ε u L : ℝ) (s : ℕ) : ℝ :=
  (u * (s+1) / L)^(1/(1+ε))

theorem sourceThreshold_pos (ε u L : ℝ) (hu : 0 < u) (hL : 0 < L) (s : ℕ) :
    0 < sourceTruncationThreshold ε u L s :=
  Real.rpow_pos_of_pos (div_pos (mul_pos hu (by positivity)) hL) _

theorem sourceThreshold_le_terminal (ε u L : ℝ) (hε : 0 ≤ ε)
    (hu : 0 ≤ u) (hL : 0 < L) (n s : ℕ) (hs : s < n) :
    sourceTruncationThreshold ε u L s ≤ (u*n/L)^(1/(1+ε)) := by
  apply Real.rpow_le_rpow (div_nonneg (mul_nonneg hu (by positivity)) hL.le)
  · apply div_le_div_of_nonneg_right _ hL.le
    apply mul_le_mul_of_nonneg_left _ hu
    exact_mod_cast hs
  · positivity

theorem sourceThreshold_bias_average (ε u L : ℝ) (hε : 0 ≤ ε)
    (hu : 0 < u) (hL : 0 < L) (n : ℕ) (hn : 0 < n) :
    (∑ s ∈ Finset.range n, u / (sourceTruncationThreshold ε u L s)^ε) / n ≤
      (1+ε)*u^(1/(1+ε))*(L/n)^(ε/(1+ε)) := by
  have hp : 0 < 1+ε := by linarith
  have hf : ∀ s : ℕ, sourceTruncationThreshold ε u L s =
      (u/L)^(1/(1+ε))*((s : ℝ)+1)^(1/(1+ε)) := by
    intro s
    unfold sourceTruncationThreshold
    rw [show u*((s : ℝ)+1)/L = (u/L)*((s : ℝ)+1) by ring]
    exact Real.mul_rpow (div_pos hu hL).le (by positivity)
  have he : (1/(1+ε))*ε = 1-1/(1+ε) := by field_simp; ring
  have hq : 1-1/(1+ε) = ε/(1+ε) := by field_simp; ring
  simp_rw [hf]
  have hs := power_threshold_bias_sum u ((u/L)^(1/(1+ε))) (1/(1+ε)) ε
    hu.le (Real.rpow_pos_of_pos (div_pos hu hL) _) (one_div_pos.mpr hp)
    ((div_le_one hp).mpr (by linarith)) he n
  have h := div_le_div_of_nonneg_right hs (Nat.cast_nonneg n : (0 : ℝ) ≤ n)
  rw [power_scale_bias u L (1/(1+ε)) ε hu hL he,
    power_bias_normalization u L (1/(1+ε)) n hL (Nat.cast_pos.mpr hn),
    one_div_one_div, hq] at h
  exact h

theorem sourceThreshold_variance_sum (ε u L : ℝ) (hε0 : 0 ≤ ε) (hε : ε ≤ 1)
    (hu : 0 < u) (hL : 0 < L) (n : ℕ) :
    (∑ s ∈ Finset.range n, u*(sourceTruncationThreshold ε u L s)^(1-ε)) ≤
      n*u*((u*n/L)^(1/(1+ε)))^(1-ε) := by
  calc
    _ ≤ ∑ _s ∈ Finset.range n, u*((u*n/L)^(1/(1+ε)))^(1-ε) := by
      apply Finset.sum_le_sum
      intro s hs
      exact mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow (sourceThreshold_pos ε u L hu hL s).le
          (sourceThreshold_le_terminal ε u L hε0 hu.le hL n s (Finset.mem_range.mp hs))
          (sub_nonneg.mpr hε)) hu.le
    _ = _ := by simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; ring

/-- One-sided centered-sum bound at the full raw-variable tilt 1/B. -/
theorem source_centered_sum_upper_tail {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : ℕ → Ω → ℝ)
    (ε u L : ℝ) (n : ℕ) (hn : 0 < n)
    (hXm : ∀ i, Measurable (X i)) (hi : iIndepFun X μ)
    (hε0 : 0 ≤ ε) (hε : ε ≤ 1) (hu : 0 < u) (hL : 0 < L)
    (hm : ∀ i, Integrable (fun ω => |X i ω|^(1+ε)) μ)
    (hraw : ∀ i, (∫ ω, |X i ω|^(1+ε) ∂μ) ≤ u) :
    μ.real {ω | 2*(u*n/L)^(1/(1+ε))*L ≤
      ∑ i ∈ Finset.range n, (truncate (sourceTruncationThreshold ε u L i) (X i ω) -
        ∫ ω, truncate (sourceTruncationThreshold ε u L i) (X i ω) ∂μ)} ≤ Real.exp (-L) := by
  let B := (u*n/L)^(1/(1+ε))
  let Y := fun i ω => truncate (sourceTruncationThreshold ε u L i) (X i ω) -
    ∫ ω, truncate (sourceTruncationThreshold ε u L i) (X i ω) ∂μ
  let V := ∑ i ∈ Finset.range n, u*(sourceTruncationThreshold ε u L i)^(1-ε)
  have hN : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hB : 0 < B := Real.rpow_pos_of_pos (div_pos (mul_pos hu hN) hL) _
  have hYi : iIndepFun Y μ := hi.comp
    (fun i x => truncate (sourceTruncationThreshold ε u L i) x -
      ∫ ω, truncate (sourceTruncationThreshold ε u L i) (X i ω) ∂μ)
    (fun i => (measurable_truncate _).sub measurable_const)
  have hYm : ∀ i, Measurable (Y i) := fun i =>
    ((measurable_truncate _).comp (hXm i)).sub measurable_const
  have hg := independent_sum_mgf μ Y (Finset.range n) (1/B)
    (fun i => (1/B)^2*(u*(sourceTruncationThreshold ε u L i)^(1-ε))) hYi hYm
    (fun i his => bounded_centering_mgf_unshifted μ
      (fun ω => truncate (sourceTruncationThreshold ε u L i) (X i ω))
      (sourceTruncationThreshold ε u L i) _ (1/B)
      ((measurable_truncate _).comp (hXm i))
      (fun ω => abs_truncate_le _ _ (sourceThreshold_pos ε u L hu hL i).le)
      (integral_sq_truncate_le μ (X i) _ ε u (sourceThreshold_pos ε u L hu hL i)
        hε (hXm i) (hm i) (hraw i)) (by
        rw [abs_of_pos (one_div_pos.mpr hB)]
        calc
          _ ≤ (1/B)*B := mul_le_mul_of_nonneg_left
            (sourceThreshold_le_terminal ε u L hε0 hu.le hL n i (Finset.mem_range.mp his))
            (one_div_pos.mpr hB).le
          _ = 1 := by field_simp))
  have hv : V ≤ B^2*L := by
    have h := mul_le_mul_of_nonneg_right
      (sourceThreshold_variance_sum ε u L hε0 hε hu hL n) hL.le
    have hp : 0 < 1+ε := by linarith
    rw [threshold_variance_identity u L n ε hu hL hN hp] at h
    change V*L ≤ (B*L)^2 at h
    nlinarith [sq_nonneg B]
  have ht := hg.measure_ge_le_exp_add (2*B*L) (one_div_pos.mpr hB).le
  have he : -(1/B)*(2*B*L) + ∑ i ∈ Finset.range n,
      (1/B)^2*(u*(sourceTruncationThreshold ε u L i)^(1-ε)) ≤ -L := by
    rw [← Finset.mul_sum]
    change -(1/B)*(2*B*L)+(1/B)^2*V ≤ -L
    have hv' := mul_le_mul_of_nonneg_left hv (sq_nonneg (1/B))
    have hc : (1/B)^2*(B^2*L) = L := by field_simp
    have hc2 : -(1/B)*(2*B*L) = -2*L := by field_simp
    rw [hc] at hv'
    rw [hc2]
    linarith
  apply le_trans ?_ (Real.exp_le_exp.mpr he)
  simpa only [Y, B, Finset.sum_apply] using ht


/-- Constant-four upper deviation for arbitrary positive log confidence. -/
theorem source_truncated_mean_upper_tail_log {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : ℕ → Ω → ℝ)
    (ε u L mean : ℝ) (n : ℕ) (hn : 0 < n)
    (hXm : ∀ i, Measurable (X i)) (hi : iIndepFun X μ)
    (hε0 : 0 ≤ ε) (hε : ε ≤ 1) (hu : 0 < u) (hL : 0 < L)
    (hX : ∀ i, Integrable (X i) μ)
    (hmean : ∀ i, (∫ ω, X i ω ∂μ) = mean)
    (hm : ∀ i, Integrable (fun ω => |X i ω|^(1+ε)) μ)
    (hraw : ∀ i, (∫ ω, |X i ω|^(1+ε) ∂μ) ≤ u) :
    μ.real {ω | 4*u^(1/(1+ε))*(L/n)^(ε/(1+ε)) ≤
      (∑ i ∈ Finset.range n, truncate (sourceTruncationThreshold ε u L i) (X i ω))/n - mean}
      ≤ Real.exp (-L) := by
  let B := (u*n/L)^(1/(1+ε))
  let R := u^(1/(1+ε))*(L/n)^(ε/(1+ε))
  let bias := ∑ i ∈ Finset.range n, u/(sourceTruncationThreshold ε u L i)^ε
  have hN : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hp : 0 < 1+ε := by linarith
  have hR : 0 ≤ R := by dsimp [R]; positivity
  have hq : 1-1/(1+ε) = ε/(1+ε) := by field_simp; ring
  have hBL : B*L = n*R := by
    dsimp [B, R]
    rw [threshold_scale_identity u L n (1/(1+ε)) hu.le hL hN, hq]
  have hbias := sourceThreshold_bias_average ε u L hε0 hu hL n hn
  have hbias' : bias / n ≤ (1+ε)*R := by simpa only [bias, R, mul_assoc] using hbias
  have hbudget : bias+2*B*L ≤ n*(4*R) := by
    have hb := (div_le_iff₀ hN).mp hbias'
    have hεR := mul_nonneg (sub_nonneg.mpr hε) (mul_nonneg hN.le hR)
    nlinarith [hBL]
  have hb : |∑ i ∈ Finset.range n,
      ((∫ ω, truncate (sourceTruncationThreshold ε u L i) (X i ω) ∂μ)-mean)| ≤ bias := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
    have h := integral_truncate_bias_le μ (X i) _ ε u
      (sourceThreshold_pos ε u L hu hL i) hε0 (hXm i) (hX i) (hm i) (hraw i)
    rw [hmean i, abs_sub_comm] at h
    exact h
  apply (measureReal_mono ?_ (measure_ne_top _ _)).trans
    (source_centered_sum_upper_tail μ X ε u L n hn hXm hi hε0 hε hu hL hm hraw)
  intro ω hw
  simp only [Set.mem_setOf_eq, mul_assoc] at hw
  change 4*R ≤ _ at hw
  change 2*B*L ≤ _
  have hid : (∑ i ∈ Finset.range n, truncate (sourceTruncationThreshold ε u L i) (X i ω)) - n*mean =
      (∑ i ∈ Finset.range n, (truncate (sourceTruncationThreshold ε u L i) (X i ω) -
        ∫ ω, truncate (sourceTruncationThreshold ε u L i) (X i ω) ∂μ)) +
      ∑ i ∈ Finset.range n, ((∫ ω, truncate (sourceTruncationThreshold ε u L i) (X i ω) ∂μ)-mean) := by
    simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    ring
  have hw' : n*(4*R) ≤
      (∑ i ∈ Finset.range n, truncate (sourceTruncationThreshold ε u L i) (X i ω))-n*mean := by
    have hh := (mul_le_mul_of_nonneg_right hw hN.le)
    rw [sub_mul, div_mul_cancel₀ _ hN.ne'] at hh
    nlinarith
  have hm' := (le_abs_self (∑ i ∈ Finset.range n,
      ((∫ ω, truncate (sourceTruncationThreshold ε u L i) (X i ω) ∂μ)-mean))).trans hb
  linarith

/-- BCL 2013 Lemma 1 upper deviation, retaining its radius constant four.
The non-strict bad event proved here is stronger than a strict upper-tail event. -/
theorem source_truncated_mean_upper_tail {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : ℕ → Ω → ℝ)
    (ε u δ mean : ℝ) (n : ℕ) (hn : 0 < n)
    (hXm : ∀ i, Measurable (X i)) (hi : iIndepFun X μ)
    (hε0 : 0 < ε) (hε : ε ≤ 1) (hu : 0 < u) (hδ : 0 < δ) (hδ1 : δ < 1)
    (hX : ∀ i, Integrable (X i) μ)
    (hmean : ∀ i, (∫ ω, X i ω ∂μ) = mean)
    (hm : ∀ i, Integrable (fun ω => |X i ω|^(1+ε)) μ)
    (hraw : ∀ i, (∫ ω, |X i ω|^(1+ε) ∂μ) ≤ u) :
    μ.real {ω | 4*u^(1/(1+ε))*(Real.log (1/δ)/n)^(ε/(1+ε)) ≤
      (∑ i ∈ Finset.range n,
        truncate (sourceTruncationThreshold ε u (Real.log (1/δ)) i) (X i ω))/n - mean}
      ≤ δ := by
  have hL : 0 < Real.log (1/δ) := Real.log_pos ((lt_div_iff₀ hδ).mpr (by simpa using hδ1))
  have h := source_truncated_mean_upper_tail_log μ X ε u (Real.log (1/δ)) mean n hn
    hXm hi hε0.le hε hu hL hX hmean hm hraw
  have he : Real.exp (-Real.log (1/δ)) = δ := by
    rw [Real.exp_neg, Real.exp_log (one_div_pos.mpr hδ)]
    simp
  rwa [he] at h


theorem truncate_neg (B x : ℝ) : truncate B (-x) = -truncate B x := by
  unfold truncate
  by_cases h : |x| ≤ B <;> simp [abs_neg, h]

/-- Reflection supplies the other one-sided source confidence statement. -/
theorem source_truncated_mean_lower_tail {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : ℕ → Ω → ℝ)
    (ε u δ mean : ℝ) (n : ℕ) (hn : 0 < n)
    (hXm : ∀ i, Measurable (X i)) (hi : iIndepFun X μ)
    (hε0 : 0 < ε) (hε : ε ≤ 1) (hu : 0 < u) (hδ : 0 < δ) (hδ1 : δ < 1)
    (hX : ∀ i, Integrable (X i) μ)
    (hmean : ∀ i, (∫ ω, X i ω ∂μ) = mean)
    (hm : ∀ i, Integrable (fun ω => |X i ω|^(1+ε)) μ)
    (hraw : ∀ i, (∫ ω, |X i ω|^(1+ε) ∂μ) ≤ u) :
    μ.real {ω | 4*u^(1/(1+ε))*(Real.log (1/δ)/n)^(ε/(1+ε)) ≤
      mean - (∑ i ∈ Finset.range n,
        truncate (sourceTruncationThreshold ε u (Real.log (1/δ)) i) (X i ω))/n}
      ≤ δ := by
  have h := source_truncated_mean_upper_tail μ (fun i ω => -X i ω) ε u δ (-mean) n hn
    (fun i => (hXm i).neg) (hi.comp (fun _ x => -x) (fun _ => measurable_neg))
    hε0 hε hu hδ hδ1 (fun i => (hX i).neg)
    (fun i => by rw [integral_neg, hmean i])
    (fun i => by simpa only [abs_neg] using hm i)
    (fun i => by simpa only [abs_neg] using hraw i)
  simpa only [truncate_neg, Finset.sum_neg_distrib, neg_div, sub_neg_eq_add, neg_add_eq_sub]
    using h

end BanditRLProof.HeavyTail
