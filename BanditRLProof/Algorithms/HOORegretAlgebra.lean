import BanditRLProof.Algorithms.HOOExpectedRegret

/-! Explicit geometric reduction of the source's three regret sums. -/
namespace BanditRLProof.HOO
set_option autoImplicit false

noncomputable def regretSumConstant (ν₁ ν₂ ρ d K : ℝ) : ℝ :=
  K*ν₂^(-d)*(36*ν₁/Real.log 2+64/(ν₁*ρ^2))

theorem regretSumConstant_pos {ν₁ ν₂ ρ d K : ℝ}
    (h1 : 0<ν₁) (h2 : 0<ν₂) (hr : 0<ρ) (hK : 0<K) :
    0<regretSumConstant ν₁ ν₂ ρ d K := by
  have hlog : 0<Real.log 2 := Real.log_pos (by norm_num)
  unfold regretSumConstant
  positivity

private theorem nat_pow_rpow (r z : ℝ) (hr : 0≤r) (h : ℕ) :
    (r^h)^z=(r^z)^h := by
  rw [← Real.rpow_natCast_mul hr, ← Real.rpow_mul_natCast hr]
  congr 1
  ring

/-- The single-level algebra keeps the child's depth h+1 in the visit
bound, and only then reduces both contributions to one geometric sequence. -/
theorem regret_level_le {ν₁ ν₂ ρ d K L : ℝ}
    (h1 : 0<ν₁) (h2 : 0<ν₂) (hr : 0<ρ) (hr1 : ρ≤1) (hK : 0<K)
    (hL : Real.log 2≤L) (h : ℕ) :
    4*(ν₁*ρ^h)*(K*(ν₂*ρ^h)^(-d)) +
      8*(ν₁*ρ^h)*(K*(ν₂*ρ^h)^(-d))*(8*L/(ν₁*ρ^(h+1))^2+4) ≤
      regretSumConstant ν₁ ν₂ ρ d K * L * (ρ^(-(1+d)))^h := by
  let x := ρ^h
  have hx : 0<x := pow_pos hr _
  have hx1 : x≤1 := pow_le_one₀ hr.le hr1
  have hx2 : x^2≤1 := by nlinarith
  let A := K*ν₂^(-d)
  let Q := x^(-(1+d))
  have hA : 0<A := mul_pos hK (Real.rpow_pos_of_pos h2 _)
  have hQ : 0<Q := Real.rpow_pos_of_pos hx _
  have he : x^(-d)=x*Q := by
    have heq : -d=1+(-(1+d)) := by ring
    rw [heq, Real.rpow_add hx, Real.rpow_one]
  have hpow : (ν₂*ρ^h)^(-d)=ν₂^(-d)*(x*Q) := by
    rw [Real.mul_rpow h2.le (pow_pos hr h).le]
    exact congrArg (fun z => ν₂^(-d)*z) he
  have hgeom : (ρ^(-(1+d)))^h=Q := (nat_pow_rpow _ _ hr.le h).symm
  rw [hpow, hgeom, pow_succ]
  change 4*(ν₁*x)*(K*(ν₂^(-d)*(x*Q))) +
    8*(ν₁*x)*(K*(ν₂^(-d)*(x*Q)))*(8*L/(ν₁*(x*ρ))^2+4) ≤ _
  have hid : 4*(ν₁*x)*(K*(ν₂^(-d)*(x*Q))) +
      8*(ν₁*x)*(K*(ν₂^(-d)*(x*Q)))*(8*L/(ν₁*(x*ρ))^2+4) =
      A*Q*(36*ν₁*x^2+64*L/(ν₁*ρ^2)) := by
    dsimp only [A]
    field_simp
    <;> ring
  rw [hid]
  have hlog : 0<Real.log 2 := Real.log_pos (by norm_num)
  have hscale : 1≤L/Real.log 2 := (one_le_div hlog).mpr hL
  have hmain : 36*ν₁*x^2 ≤ 36*ν₁/Real.log 2*L := by
    have hxL : x^2≤L/Real.log 2 := hx2.trans hscale
    have hh := mul_le_mul_of_nonneg_left hxL (by positivity : 0≤36*ν₁)
    convert hh using 1 <;> ring
  have hh := mul_le_mul_of_nonneg_left
    (add_le_add hmain (le_refl (64*L/(ν₁*ρ^2)))) (mul_pos hA hQ).le
  convert hh using 1 <;> dsimp only [regretSumConstant, A] <;> ring

/-- Finite sums are reduced with an explicit environment-only constant. -/
theorem regret_sums_le {ν₁ ν₂ ρ d K L : ℝ}
    (h1 : 0<ν₁) (h2 : 0<ν₂) (hr : 0<ρ) (hr1 : ρ<1) (hd : 0<d) (hK : 0<K)
    (hL : Real.log 2≤L) (H : ℕ) :
    (∑ h ∈ Finset.range H, 4*(ν₁*ρ^h)*(K*(ν₂*ρ^h)^(-d))) +
    (∑ h ∈ Finset.range H, 8*(ν₁*ρ^h)*(K*(ν₂*ρ^h)^(-d)) *
      (8*L/(ν₁*ρ^(h+1))^2+4)) ≤
      (regretSumConstant ν₁ ν₂ ρ d K / (ρ^(-(1+d))-1))*L*(ρ^H)^(-(1+d)) := by
  let q := ρ^(-(1+d))
  have hq : 1<q := Real.one_lt_rpow_of_pos_of_lt_one_of_neg hr hr1 (by linarith)
  have hB := regretSumConstant_pos (d := d) h1 h2 hr hK
  have hlog : 0<Real.log 2 := Real.log_pos (by norm_num)
  have hLp : 0<L := hlog.trans_le hL
  rw [← Finset.sum_add_distrib]
  calc
    _ ≤ ∑ h ∈ Finset.range H, regretSumConstant ν₁ ν₂ ρ d K * L * q^h :=
      Finset.sum_le_sum (fun h _ => regret_level_le h1 h2 hr hr1.le hK hL h)
    _ = regretSumConstant ν₁ ν₂ ρ d K * L * ((q^H-1)/(q-1)) := by
      rw [← Finset.mul_sum, geom_sum_eq (ne_of_gt hq)]
    _ ≤ regretSumConstant ν₁ ν₂ ρ d K * L * (q^H/(q-1)) := by
      apply mul_le_mul_of_nonneg_left _ (mul_pos hB hLp).le
      exact div_le_div_of_nonneg_right (by linarith) (by linarith)
    _ = _ := by
      rw [nat_pow_rpow ρ (-(1+d)) hr.le H]
      dsimp only [q]
      ring

end BanditRLProof.HOO
