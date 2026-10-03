import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-! Exact power-tail integration and balancing identities. -/
namespace BanditRLProof.PowerTailIntegral
open MeasureTheory
set_option autoImplicit false

theorem integral_power_tail_le (a b q : ℝ) (ha : 0<a) (hab : a≤b) (hq : 1<q) :
    (∫x in a..b, x^(-q))≤a^(1-q)/(q-1) := by
  have hz : (0:ℝ)∉Set.uIcc a b := by
    rw [Set.uIcc_of_le hab]
    intro h
    linarith [h.1]
  rw [integral_rpow (Or.inr ⟨by linarith,hz⟩)]
  have he : (b^(-q+1)-a^(-q+1))/(-q+1)=
      (a^(1-q)-b^(1-q))/(q-1) := by
    rw [show -q+1=1-q by ring]
    field_simp [show 1-q≠0 by linarith, show q-1≠0 by linarith]
    ring
  rw [he]
  apply div_le_div_of_nonneg_right _ (by linarith)
  exact sub_le_self _ (Real.rpow_nonneg (ha.le.trans hab) _)

theorem cutoff_balance (K N q : ℝ) (hK : 0<K) (hN : 0<N) (hq : 0<q) :
    K*((K/N)^(1/q))^(-q)=N := by
  rw [← Real.rpow_mul (div_pos hK hN).le]
  have he : (1/q)*(-q)=(-1:ℝ) := by field_simp
  rw [he,Real.rpow_neg_one,inv_div]
  field_simp

theorem cutoff_objective (K N q : ℝ) (hK : 0<K) (hN : 0<N) (hq : 1<q) :
    N*(K/N)^(1/q)+K*((K/N)^(1/q))^(1-q)/(q-1)=
      q/(q-1)*(N*(K/N)^(1/q)) := by
  have ha : 0<(K/N)^(1/q) := Real.rpow_pos_of_pos (div_pos hK hN) _
  rw [Real.rpow_sub ha,Real.rpow_one]
  have hb := cutoff_balance K N q hK hN (by linarith)
  rw [Real.rpow_neg ha.le] at hb
  have hq1 : q-1≠0 := by linarith
  have hpow : ((K/N)^(1/q))^q≠0 := ne_of_gt (Real.rpow_pos_of_pos ha _)
  field_simp at hb ⊢
  nlinarith

end BanditRLProof.PowerTailIntegral
