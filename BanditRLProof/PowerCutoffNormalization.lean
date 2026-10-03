import BanditRLProof.PowerTailIntegral

/-! Exact normalization of the balanced polynomial cutoff into source powers. -/
namespace BanditRLProof.PowerTailIntegral
set_option autoImplicit false

theorem source_cutoff_normalization (C N γ ω : ℝ) (hC : 0<C) (hN : 0<N)
    (hγ : 0<γ) (hω : 0<ω) (hω1 : ω≤1) :
    (2/ω)/(2/ω-1)*(N*((C*γ^(2/ω))/N)^(1/(2/ω)))=
      (2*γ/(2-ω))*C^(ω/2)*N^(1-ω/2) := by
  have hq : 1<2/ω := (lt_div_iff₀ hω).mpr (by linarith)
  have hrecip : 1/(2/ω)=ω/2 := by field_simp
  have hcoef : (2/ω)/(2/ω-1)=2/(2-ω) := by
    field_simp
  rw [hcoef,hrecip,Real.div_rpow (mul_pos hC (Real.rpow_pos_of_pos hγ _)).le hN.le,
    Real.mul_rpow hC.le (Real.rpow_nonneg hγ.le _),← Real.rpow_mul hγ.le]
  rw [show (2/ω)*(ω/2)=(1:ℝ) by field_simp,Real.rpow_one,Real.rpow_sub hN,Real.rpow_one]
  have hpow : N^(ω/2)≠0 := ne_of_gt (Real.rpow_pos_of_pos hN _)
  field_simp

end BanditRLProof.PowerTailIntegral
