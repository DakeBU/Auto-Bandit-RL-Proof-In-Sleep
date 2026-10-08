import BanditRLProof.OnlineGuessingRandomizedIID
open scoped NNReal ENNReal

example : (4 : ℝ≥0∞)⁻¹ + 4⁻¹ + 4⁻¹ + 4⁻¹ = 1 := by
  rw [← ENNReal.coe_ofNat 4, ← ENNReal.coe_inv (by norm_num : (4 : ℝ≥0) ≠ 0)]
  norm_cast
  norm_num

example : (4 : ℝ≥0∞)⁻¹ = (4⁻¹ + 4⁻¹) * (4⁻¹ + 4⁻¹) := by
  rw [← ENNReal.coe_ofNat 4, ← ENNReal.coe_inv (by norm_num : (4 : ℝ≥0) ≠ 0)]
  norm_cast
  norm_num

example : ¬ (4 : ℝ≥0∞)⁻¹ = 4⁻¹ * (4⁻¹ + 4⁻¹) := by
  rw [← ENNReal.coe_ofNat 4, ← ENNReal.coe_inv (by norm_num : (4 : ℝ≥0) ≠ 0)]
  norm_cast
  norm_num
