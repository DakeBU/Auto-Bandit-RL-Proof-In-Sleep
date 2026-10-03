import BanditRLProof.Algorithms.CUCBGapCutoff

/-! Exact polynomial-modulus inverse and source threshold expressions. -/
namespace BanditRLProof.CUCB.SourceModel
open MeasureTheory ProbabilityTheory
set_option autoImplicit false
variable {A : Type*} [Fintype A] [Nonempty A] [MeasurableSpace A]
  {m : ℕ} {M : FeedbackModel A m} (S : SourceModel M)

theorem inverseAt_polynomial (γ ω : ℝ) (hγ : 0<γ) (hω : 0<ω)
    (hf : ∀u, 0≤u → S.modulus u=γ*u^ω) {d : ℝ} (hd : d∈S.gapDomain) :
    S.inverseAt d=(d/γ)^(1/ω) := by
  have hx : 0≤d/γ := (div_pos hd.1 hγ).le
  apply S.inverseAt_unique hd (Real.rpow_nonneg hx _)
  rw [hf _ (Real.rpow_nonneg hx _), ← Real.rpow_mul hx,
    div_mul_cancel₀ (1:ℝ) (ne_of_gt hω), Real.rpow_one]
  field_simp

theorem inverseAt_polynomial_square (γ ω : ℝ) (hγ : 0<γ) (hω : 0<ω)
    (hf : ∀u, 0≤u → S.modulus u=γ*u^ω) {d : ℝ} (hd : d∈S.gapDomain) :
    (S.inverseAt d)^2=(d/γ)^(2/ω) := by
  rw [S.inverseAt_polynomial γ ω hγ hω hf hd, ← Real.rpow_natCast,
    ← Real.rpow_mul (div_pos hd.1 hγ).le]
  congr 1
  norm_num
  ring

theorem inverseAt_polynomial_reciprocal (γ ω : ℝ) (hγ : 0<γ) (hω : 0<ω)
    (hf : ∀u, 0≤u → S.modulus u=γ*u^ω) {d : ℝ} (hd : d∈S.gapDomain) :
    ((S.inverseAt d)^2)⁻¹=γ^(2/ω)*d^(-(2/ω)) := by
  rw [S.inverseAt_polynomial_square γ ω hγ hω hf hd,
    Real.div_rpow hd.1.le hγ.le, inv_div, Real.rpow_neg hd.1.le]
  rw [div_eq_mul_inv]

theorem gapThreshold_polynomial_deterministic (H : ℕ) (γ ω : ℝ) (hγ : 0<γ) (hω : 0<ω)
    (hf : ∀u, 0≤u → S.modulus u=γ*u^ω) {d : ℝ} (hd : d∈S.gapDomain) :
    S.gapThreshold H 1 d=6*Real.log (H:ℝ)*γ^(2/ω)*d^(-(2/ω)) := by
  rw [gapThreshold,samplingThreshold_deterministic,div_eq_mul_inv,
    S.inverseAt_polynomial_reciprocal γ ω hγ hω hf hd]
  ring

theorem gapThreshold_polynomial_probabilistic (H : ℕ) (hH : 1≤H)
    (γ ω p : ℝ) (hγ : 0<γ) (hω : 0<ω) (hp : p≠1)
    (hf : ∀u, 0≤u → S.modulus u=γ*u^ω) {d : ℝ} (hd : d∈S.gapDomain) :
    S.gapThreshold H p d=max
      (12*Real.log (H:ℝ)/p*γ^(2/ω)*d^(-(2/ω))) (24*Real.log (H:ℝ)/p) := by
  rw [gapThreshold,samplingThreshold_probabilistic hH hp]
  congr 1
  simp only [div_eq_mul_inv,mul_inv_rev]
  rw [S.inverseAt_polynomial_reciprocal γ ω hγ hω hf hd]
  ring_nf

theorem gapThreshold_polynomial_upper (H : ℕ) (hH : 1≤H) (i : Fin m)
    (γ ω : ℝ) (hγ : 0<γ) (hω : 0<ω)
    (hf : ∀u, 0≤u → S.modulus u=γ*u^ω) {d : ℝ} (hd : d∈S.gapDomain) :
    S.gapThreshold H (M.minTrigger i) d≤
      12*Real.log (H:ℝ)/M.globalMinTrigger*γ^(2/ω)*d^(-(2/ω))+
        24*Real.log (H:ℝ)/M.minTrigger i := by
  have hlog : 0≤Real.log (H:ℝ) := Real.log_nonneg (by exact_mod_cast hH)
  have hp := M.minTrigger_pos i
  have hpstar := M.globalMinTrigger_pos
  have hpow : 0≤γ^(2/ω) := Real.rpow_nonneg hγ.le _
  have hdPow : 0≤d^(-(2/ω)) := Real.rpow_nonneg hd.1.le _
  have hc : 0≤24*Real.log (H:ℝ)/M.minTrigger i := by positivity
  by_cases he : M.minTrigger i=1
  · rw [he,S.gapThreshold_polynomial_deterministic H γ ω hγ hω hf hd]
    have hcoef : 6*Real.log (H:ℝ)≤12*Real.log (H:ℝ)/M.globalMinTrigger := by
      apply (le_div_iff₀ hpstar).mpr
      have h := mul_le_mul_of_nonneg_left M.globalMinTrigger_le_one
        (show 0≤6*Real.log (H:ℝ) by positivity)
      nlinarith
    have hh := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hcoef hpow) hdPow
    have hz : 0≤24*Real.log (H:ℝ)/(1:ℝ) := by positivity
    linarith
  · rw [S.gapThreshold_polynomial_probabilistic H hH γ ω _ hγ hω he hf hd]
    apply max_le
    · have hcoef := div_le_div_of_nonneg_left (show 0≤12*Real.log (H:ℝ) by positivity)
        hpstar (M.globalMinTrigger_le i)
      have hh := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hcoef hpow) hdPow
      linarith
    · have hh : 0≤12*Real.log (H:ℝ)/M.globalMinTrigger*γ^(2/ω)*d^(-(2/ω)) := by positivity
      linarith

end BanditRLProof.CUCB.SourceModel
