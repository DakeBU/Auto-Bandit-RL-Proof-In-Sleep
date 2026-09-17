import BanditRLProof.HeavyTailClippedMoments
import BanditRLProof.HeavyTailConfidence
import BanditRLProof.HeavyTailTuning

/-! Clean clipped-mean confidence from raw moments, through shared MGF interfaces. -/
namespace BanditRLProof.HeavyTail
open MeasureTheory ProbabilityTheory

theorem clipped_centered_mgf {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Ω → ℝ)
    (B ε u tilt : ℝ) (hXm : Measurable X) (hB : 0 < B) (hε0 : 0 ≤ ε) (hε : ε ≤ 1)
    (hm : Integrable (fun ω => |X ω|^(1+ε)) μ)
    (hu : (∫ ω, |X ω|^(1+ε) ∂μ) ≤ u) (hsmall : |tilt| * (2*B) ≤ 1) :
    Concentration.HasMGFUpperBoundAt (fun ω => clip B (X ω) - ∫ ω, clip B (X ω) ∂μ)
      tilt (tilt^2*(u*B^(1-ε))) μ :=
  bounded_centering_mgf μ _ B _ tilt ((measurable_clip B).comp hXm)
    (fun ω => abs_clip_le B (X ω) hB.le)
    (integral_sq_clip_le μ X B ε u hB hε0 hε hXm hm hu) hsmall

theorem clipped_sum_abs_tail {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : ℕ → Ω → ℝ)
    (B : ℕ → ℝ) (ε u b L : ℝ) (n : ℕ)
    (hXm : ∀ i, Measurable (X i)) (hi : iIndepFun X μ)
    (hB : ∀ i, 0 < B i) (hε0 : 0 ≤ ε) (hε : ε ≤ 1)
    (hu0 : 0 ≤ u) (hb : 0 < b) (hL : 0 ≤ L)
    (hbound : ∀ i ∈ Finset.range n, 2*B i ≤ b)
    (hm : ∀ i, Integrable (fun ω => |X i ω|^(1+ε)) μ)
    (hu : ∀ i, (∫ ω, |X i ω|^(1+ε) ∂μ) ≤ u) :
    μ.real {ω | 2*Real.sqrt ((∑ i ∈ Finset.range n, u*(B i)^(1-ε))*L)+b*L ≤
      |∑ i ∈ Finset.range n, (clip (B i) (X i ω) - ∫ ω, clip (B i) (X i ω) ∂μ)|} ≤
      2*Real.exp (-L) := by
  let Y := fun i ω => clip (B i) (X i ω) - ∫ ω, clip (B i) (X i ω) ∂μ
  have hYi : iIndepFun Y μ := hi.comp
    (fun i x => clip (B i) x - ∫ ω, clip (B i) (X i ω) ∂μ)
    (fun i => (measurable_clip (B i)).sub measurable_const)
  have hYm : ∀ i, Measurable (Y i) := fun i =>
    ((measurable_clip (B i)).comp (hXm i)).sub measurable_const
  have hsum := fixed_mgf_abs_tail μ (∑ i ∈ Finset.range n, Y i)
    (∑ i ∈ Finset.range n, u*(B i)^(1-ε)) b L
    (Finset.sum_nonneg fun i _ => mul_nonneg hu0 (Real.rpow_nonneg (hB i).le _)) hb hL
    (fun tilt ht => by
      have hg := independent_sum_mgf μ Y (Finset.range n) tilt
        (fun i => tilt^2*(u*(B i)^(1-ε))) hYi hYm
        (fun i his => clipped_centered_mgf μ (X i) (B i) ε u tilt
          (hXm i) (hB i) hε0 hε (hm i) (hu i)
          ((mul_le_mul_of_nonneg_left (hbound i his) (abs_nonneg tilt)).trans ht))
      simpa only [Finset.mul_sum] using hg)
  simpa only [Y, Finset.sum_apply] using hsum

theorem clipped_mean_tail {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : ℕ → Ω → ℝ)
    (B : ℕ → ℝ) (ε u b L mean : ℝ) (n : ℕ) (hn : 0 < n)
    (hXm : ∀ i, Measurable (X i)) (hi : iIndepFun X μ)
    (hB : ∀ i, 0 < B i) (hε0 : 0 ≤ ε) (hε : ε ≤ 1)
    (hu0 : 0 ≤ u) (hb : 0 < b) (hL : 0 ≤ L)
    (hbound : ∀ i ∈ Finset.range n, 2*B i ≤ b)
    (hX : ∀ i, Integrable (X i) μ) (hmean : ∀ i, (∫ ω, X i ω ∂μ) = mean)
    (hm : ∀ i, Integrable (fun ω => |X i ω|^(1+ε)) μ)
    (hu : ∀ i, (∫ ω, |X i ω|^(1+ε) ∂μ) ≤ u) :
    μ.real {ω | ((∑ i ∈ Finset.range n, u/(B i)^ε) +
      (2*Real.sqrt ((∑ i ∈ Finset.range n, u*(B i)^(1-ε))*L)+b*L))/n ≤
      |prefixMean (fun i => clip (B i) (X i ω)) n - mean|} ≤ 2*Real.exp (-L) := by
  have hbias : |∑ i ∈ Finset.range n, ((∫ ω, clip (B i) (X i ω) ∂μ)-mean)| ≤
      ∑ i ∈ Finset.range n, u/(B i)^ε := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
    have h := integral_clip_bias_le μ (X i) (B i) ε u (hB i) hε0 (hXm i) (hX i) (hm i) (hu i)
    rw [hmean i, abs_sub_comm] at h
    exact h
  have htail := sum_mean_tail_of_centered μ (fun i ω => clip (B i) (X i ω)) mean _ _ _ n hbias
    (clipped_sum_abs_tail μ X B ε u b L n hXm hi hB hε0 hε hu0 hb hL hbound hm hu)
  have hn' : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have heq : ∀ z : ℝ, z/n - mean = (z-n*mean)/n := by intro z; field_simp
  simpa only [prefixMean, heq, abs_div, abs_of_pos hn', div_le_div_iff_of_pos_right hn'] using htail

end BanditRLProof.HeavyTail
