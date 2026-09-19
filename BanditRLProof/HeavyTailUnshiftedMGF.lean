import BanditRLProof.HeavyTailFixedTilt

/-! Centering after the exponential bound preserves the raw-variable tilt range.
This uses a raw second moment, not the variance of the centered variable. -/
namespace BanditRLProof.HeavyTail
open MeasureTheory ProbabilityTheory

theorem bounded_centering_mgf_unshifted {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (Y : Ω → ℝ)
    (B v tilt : ℝ) (hYm : Measurable Y) (hbound : ∀ ω, |Y ω| ≤ B)
    (hv : (∫ ω, (Y ω)^2 ∂μ) ≤ v)
    (hsmall : |tilt| * B ≤ 1) :
    Concentration.HasMGFUpperBoundAt
      (fun ω => Y ω - ∫ ω, Y ω ∂μ) tilt (tilt^2 * v) μ := by
  have hYi : Integrable Y μ := (integrable_const B).mono' hYm.aestronglyMeasurable
    (Filter.Eventually.of_forall fun ω => by simpa only [Real.norm_eq_abs] using hbound ω)
  have hsq : Integrable (fun ω => (Y ω)^2) μ := by
    apply (integrable_const (B^2)).mono' (hYm.pow_const 2).aestronglyMeasurable
    exact Filter.Eventually.of_forall fun ω => by
      simp only [Real.norm_eq_abs, abs_sq]
      nlinarith [sq_nonneg (B - |Y ω|), sq_abs (Y ω), hbound ω, abs_nonneg (Y ω)]
  have hexp (s : ℝ) : Integrable (fun ω => Real.exp (s * Y ω)) μ := by
    apply (integrable_const (Real.exp (|s| * B))).mono'
      (hYm.const_mul s).exp.aestronglyMeasurable
    exact Filter.Eventually.of_forall fun ω => by
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      apply Real.exp_le_exp.mpr
      exact (le_abs_self _).trans ((abs_mul s (Y ω)).trans_le
        (mul_le_mul_of_nonneg_left (hbound ω) (abs_nonneg s)))
  have hraw : (∫ ω, Real.exp (tilt * Y ω) ∂μ) ≤
      Real.exp (tilt * (∫ ω, Y ω ∂μ) + tilt^2 * v) := by
    calc
      _ ≤ ∫ ω, (1 + tilt * Y ω) + tilt^2 * (Y ω)^2 ∂μ := by
        apply integral_mono (hexp tilt)
          (((integrable_const 1).add (hYi.const_mul tilt)).add (hsq.const_mul _))
        intro ω
        have h := Concentration.exp_le_one_add_self_add_sq_of_abs_le_one
          (x := tilt * Y ω) (by rw [abs_mul]; exact
            (mul_le_mul_of_nonneg_left (hbound ω) (abs_nonneg _)).trans hsmall)
        simpa only [Pi.add_apply, mul_pow] using h
      _ = 1 + tilt * (∫ ω, Y ω ∂μ) + tilt^2 * (∫ ω, (Y ω)^2 ∂μ) := by
        rw [integral_add (f := fun ω => 1 + tilt * Y ω)
          (g := fun ω => tilt^2 * (Y ω)^2)
          ((integrable_const 1).add (hYi.const_mul tilt)) (hsq.const_mul _),
          integral_add (f := fun _ : Ω => (1 : ℝ)) (g := fun ω => tilt * Y ω)
          (integrable_const 1) (hYi.const_mul tilt)]
        simp [integral_const_mul]
      _ ≤ 1 + tilt * (∫ ω, Y ω ∂μ) + tilt^2 * v := by gcongr
      _ ≤ _ := by linarith [Real.add_one_le_exp (tilt * (∫ ω, Y ω ∂μ) + tilt^2 * v)]
  have he (s : ℝ) (ω : Ω) : Real.exp (s * (Y ω - ∫ ω, Y ω ∂μ)) =
      Real.exp (-(s * ∫ ω, Y ω ∂μ)) * Real.exp (s * Y ω) := by
    rw [← Real.exp_add]
    congr 1
    ring
  constructor
  · intro s
    simp_rw [he]
    exact (hexp s).const_mul _
  · change (∫ ω, Real.exp (tilt * (Y ω - ∫ ω, Y ω ∂μ)) ∂μ) ≤ _
    simp_rw [he]
    rw [integral_const_mul]
    calc
      _ ≤ Real.exp (-(tilt * ∫ ω, Y ω ∂μ)) *
          Real.exp (tilt * (∫ ω, Y ω ∂μ) + tilt^2 * v) :=
        mul_le_mul_of_nonneg_left hraw (Real.exp_pos _).le
      _ = _ := by rw [← Real.exp_add]; congr 1; ring

end BanditRLProof.HeavyTail
