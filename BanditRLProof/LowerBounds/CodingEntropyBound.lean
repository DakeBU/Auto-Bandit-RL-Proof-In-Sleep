import BanditRLProof.LowerBounds.InformationTheory

namespace BanditRLProof.LowerBounds

open scoped BigOperators

theorem entropy_term_le_codeLength_remainder {p : ℝ} (hp : 0 ≤ p) (l : ℕ) :
    p * Real.log p⁻¹ ≤ p * l * Real.log 2 + (1 / 2 : ℝ) ^ l - p := by
  rcases eq_or_lt_of_le hp with he | he
  · subst p
    simp only [zero_mul, sub_zero]
    positivity
  have hw : 0 < (1 / 2 : ℝ) ^ l := by positivity
  have h := mul_le_mul_of_nonneg_left
    (Real.log_le_sub_one_of_pos (div_pos hw he)) hp
  rw [Real.log_div hw.ne' he.ne', Real.log_pow, Real.log_div (by norm_num) (by norm_num),
    Real.log_one] at h
  have hc : p * ((1 / 2 : ℝ) ^ l / p - 1) = (1 / 2 : ℝ) ^ l - p := by
    field_simp
  rw [hc] at h
  rw [Real.log_inv]
  nlinarith

/-- The lower half of Eq. (14.2), for every finite binary prefix code. -/
theorem discreteEntropyBaseTwo_le_expectedCodeLength
    {Symbol : Type*} [Fintype Symbol] [DecidableEq Symbol]
    (p : Symbol → ℝ) (hp : ∀ i, 0 ≤ p i) (hsum : ∑ i, p i = 1)
    (code : BinaryPrefixCode Symbol) :
    discreteEntropyBaseTwo Finset.univ p ≤ expectedCodeLength p code := by
  have hk : ∑ i, (1 / 2 : ℝ) ^ (code.encode i).length ≤ 1 := by
    have h := code.kraft_inequality
    rw [BinaryPrefixCode.codebook, Finset.sum_image] at h
    · exact h
    · intro a _ b _ hab
      exact code.injective hab
  have h := Finset.sum_le_sum (s := Finset.univ)
    (fun i _ => entropy_term_le_codeLength_remainder (hp i) (code.encode i).length)
  simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.sum_mul, hsum] at h
  rw [discreteEntropyBaseTwo_eq_div_log_two]
  apply (div_le_iff₀ (Real.log_pos (by norm_num : (1 : ℝ) < 2))).2
  change (∑ i, p i * Real.log (p i)⁻¹) ≤
    (∑ i, p i * (code.encode i).length) * Real.log 2
  linarith

end BanditRLProof.LowerBounds
