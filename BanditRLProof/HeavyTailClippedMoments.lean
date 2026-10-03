import BanditRLProof.HeavyTailClipping
import BanditRLProof.HeavyTailFixedTilt

/-! Clean clipping bias and second moments, produced from raw moments. -/
namespace BanditRLProof.HeavyTail
open MeasureTheory ProbabilityTheory

theorem clip_eq_self (B x : ℝ) (hx : |x| ≤ B) : clip B x = x := by
  rw [clip, min_eq_right (abs_le.mp hx).2, max_eq_right (abs_le.mp hx).1]

theorem abs_clip_le (B x : ℝ) (hB : 0 ≤ B) : |clip B x| ≤ B := by
  rw [abs_le]
  constructor
  · exact le_max_left _ _
  · exact max_le (by linarith) (min_le_left _ _)

theorem abs_clip_le_abs (B x : ℝ) (hB : 0 ≤ B) : |clip B x| ≤ |x| := by
  have hz : clip B 0 = 0 := clip_eq_self B 0 (by simpa using hB)
  simpa only [hz, sub_zero] using abs_clip_sub_clip_le B x 0

theorem abs_sub_clip_le_truncate (B x : ℝ) (hB : 0 ≤ B) :
    |x - clip B x| ≤ |x - truncate B x| := by
  by_cases h : |x| ≤ B
  · simp [clip_eq_self B x h, truncate, h]
  · rw [truncate, if_neg h, sub_zero]
    by_cases hx : x ≤ B
    · have hlo : x < -B := by
        by_contra hh
        exact h (abs_le.mpr ⟨le_of_not_gt hh, hx⟩)
      rw [clip, min_eq_right hx, max_eq_left hlo.le, abs_of_nonpos (by linarith : x - -B ≤ 0),
        abs_of_nonpos (by linarith : x ≤ 0)]
      linarith
    · have hhi : B < x := lt_of_not_ge hx
      rw [clip, min_eq_left hhi.le, max_eq_right (by linarith : -B ≤ B),
        abs_of_nonneg (by linarith : 0 ≤ x-B), abs_of_nonneg (by linarith : 0 ≤ x)]
      linarith

theorem abs_sub_clip_moment_le (B x ε : ℝ) (hB : 0 < B) (hε : 0 ≤ ε) :
    |x - clip B x| ≤ |x|^(1+ε) / B^ε :=
  (abs_sub_clip_le_truncate B x hB.le).trans (abs_sub_truncate_le B x ε hB hε)

theorem sq_clip_moment_le (B x ε : ℝ) (hB : 0 < B) (hε0 : 0 ≤ ε) (hε : ε ≤ 1) :
    (clip B x)^2 ≤ |x|^(1+ε) * B^(1-ε) := by
  by_cases hz : clip B x = 0
  · rw [hz, zero_pow (by decide : 2 ≠ 0)]
    positivity
  have hp : 0 < |clip B x| := abs_pos.mpr hz
  have he : (clip B x)^2 = |clip B x|^(1+ε) * |clip B x|^(1-ε) := by
    rw [← Real.rpow_add hp, show (1+ε)+(1-ε) = (2 : ℝ) by ring, Real.rpow_two, sq_abs]
  rw [he]
  exact mul_le_mul
    (Real.rpow_le_rpow hp.le (abs_clip_le_abs B x hB.le) (by linarith))
    (Real.rpow_le_rpow hp.le (abs_clip_le B x hB.le) (sub_nonneg.mpr hε))
    (Real.rpow_nonneg hp.le _) (Real.rpow_nonneg (abs_nonneg x) _)

theorem measurable_clip (B : ℝ) : Measurable (clip B) :=
  measurable_const.max (measurable_const.min measurable_id)

theorem integral_clip_bias_le {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Ω → ℝ) (B ε u : ℝ)
    (hB : 0 < B) (hε : 0 ≤ ε) (hXm : Measurable X) (hX : Integrable X μ)
    (hm : Integrable (fun ω => |X ω|^(1+ε)) μ)
    (hu : (∫ ω, |X ω|^(1+ε) ∂μ) ≤ u) :
    |(∫ ω, X ω ∂μ) - ∫ ω, clip B (X ω) ∂μ| ≤ u/B^ε := by
  have ht : Integrable (fun ω => clip B (X ω)) μ :=
    (integrable_const B).mono' ((measurable_clip B).comp hXm).aestronglyMeasurable
      (ae_of_all _ fun ω => by simpa only [Real.norm_eq_abs] using abs_clip_le B (X ω) hB.le)
  rw [← integral_sub hX ht]
  calc
    _ ≤ ∫ ω, |X ω - clip B (X ω)| ∂μ := by
      simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm
        (fun ω => X ω - clip B (X ω))
    _ ≤ ∫ ω, |X ω|^(1+ε) / B^ε ∂μ :=
      integral_mono (hX.sub ht).abs (hm.div_const _) (fun ω => abs_sub_clip_moment_le B (X ω) ε hB hε)
    _ = (∫ ω, |X ω|^(1+ε) ∂μ) / B^ε := integral_div _ _
    _ ≤ u/B^ε := div_le_div_of_nonneg_right hu (Real.rpow_nonneg hB.le _)

theorem integral_sq_clip_le {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (X : Ω → ℝ) (B ε u : ℝ)
    (hB : 0 < B) (hε0 : 0 ≤ ε) (hε : ε ≤ 1) (hXm : Measurable X)
    (hm : Integrable (fun ω => |X ω|^(1+ε)) μ)
    (hu : (∫ ω, |X ω|^(1+ε) ∂μ) ≤ u) :
    (∫ ω, (clip B (X ω))^2 ∂μ) ≤ u*B^(1-ε) := by
  have hg := hm.mul_const (B^(1-ε))
  have ht : Integrable (fun ω => (clip B (X ω))^2) μ := by
    apply hg.mono' (((measurable_clip B).comp hXm).pow_const 2).aestronglyMeasurable
    exact Filter.Eventually.of_forall fun ω => by
      simpa only [Real.norm_eq_abs, abs_sq] using
        (sq_clip_moment_le B (X ω) ε hB hε0 hε)
  calc
    _ ≤ ∫ ω, |X ω|^(1+ε)*B^(1-ε) ∂μ := integral_mono ht hg
      (fun ω => sq_clip_moment_le B (X ω) ε hB hε0 hε)
    _ = (∫ ω, |X ω|^(1+ε) ∂μ)*B^(1-ε) := integral_mul_const _ _
    _ ≤ u*B^(1-ε) := mul_le_mul_of_nonneg_right hu (Real.rpow_nonneg hB.le _)

end BanditRLProof.HeavyTail
