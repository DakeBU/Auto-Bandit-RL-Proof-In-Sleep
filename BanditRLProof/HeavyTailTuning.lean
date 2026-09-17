import BanditRLProof.HeavyTailPowerSum
import BanditRLProof.Algorithms.HeavyTailUCB

/-! Algebraic tuning for the sample-index threshold; all exponents remain real. -/
namespace BanditRLProof.HeavyTail

theorem power_threshold_bias_term (u c a ε x : ℝ) (hc : 0 < c) (hx : 0 < x)
    (haε : a * ε = 1-a) :
    u / (c * x^a)^ε = (u / c^ε) * x^(a-1) := by
  rw [Real.mul_rpow hc.le (Real.rpow_nonneg hx.le _), ← Real.rpow_mul hx.le,
    haε]
  rw [show a-1 = -(1-a) by ring, Real.rpow_neg hx.le]
  ring

theorem power_threshold_bias_sum (u c a ε : ℝ) (hu : 0 ≤ u) (hc : 0 < c)
    (ha : 0 < a) (ha1 : a ≤ 1) (haε : a * ε = 1-a) (n : ℕ) :
    (∑ s ∈ Finset.range n, u / (c * ((s : ℝ)+1)^a)^ε) ≤
      (u / c^ε) * ((n : ℝ)^a / a) := by
  have hterm : ∀ s : ℕ, u / (c * ((s : ℝ)+1)^a)^ε =
      (u / c^ε) * ((s : ℝ)+1)^(a-1) := fun s =>
    power_threshold_bias_term u c a ε _ hc (by positivity) haε
  simp_rw [hterm]
  rw [← Finset.mul_sum]
  exact mul_le_mul_of_nonneg_left (sum_shifted_rpow_le a ha ha1 n)
    (div_nonneg hu (Real.rpow_nonneg hc.le _))

theorem sampleThreshold_factor (ε u : ℝ) (hu : 0 ≤ u) (t s : ℕ) :
    sampleThreshold ε u t s =
      (u / confidenceLog t)^(1/(1+ε)) * ((s : ℝ)+1)^(1/(1+ε)) := by
  have hL : 0 < confidenceLog t := by
    unfold confidenceLog
    exact mul_pos (by norm_num) (Real.log_pos (lt_of_lt_of_le (by norm_num) (le_max_right _ _)))
  unfold sampleThreshold
  rw [show u * ((s : ℝ)+1) / confidenceLog t =
      (u / confidenceLog t) * ((s : ℝ)+1) by ring]
  exact Real.mul_rpow (div_nonneg hu hL.le) (by positivity)

theorem sampleThreshold_bias_sum (ε u : ℝ) (hε : 0 ≤ ε) (hu : 0 < u) (t n : ℕ) :
    (∑ s ∈ Finset.range n, u / (sampleThreshold ε u t s)^ε) ≤
      (u / ((u / confidenceLog t)^(1/(1+ε)))^ε) *
        ((n : ℝ)^(1/(1+ε)) / (1/(1+ε))) := by
  have hp : 0 < 1+ε := by linarith
  have hL : 0 < confidenceLog t := by
    unfold confidenceLog
    exact mul_pos (by norm_num) (Real.log_pos (lt_of_lt_of_le (by norm_num) (le_max_right _ _)))
  simp_rw [sampleThreshold_factor ε u hu.le]
  apply power_threshold_bias_sum u _ _ ε hu.le
    (Real.rpow_pos_of_pos (div_pos hu hL) _) (one_div_pos.mpr hp)
    ((div_le_one hp).mpr (by linarith))
  field_simp
  ring

end BanditRLProof.HeavyTail
