import BanditRLProof.OnlineGuessingRandomizedIID

example : (4 : ℝ≥0∞)⁻¹ + 4⁻¹ + 4⁻¹ + 4⁻¹ = 1 := by
  norm_num [← ENNReal.coe_ofNat 4, ← ENNReal.coe_inv (by norm_num : (4 : ℝ≥0) ≠ 0),
    ← ENNReal.coe_add, ← ENNReal.coe_mul, ← ENNReal.coe_one, ENNReal.coe_inj]

example : (4 : ℝ≥0∞)⁻¹ = (4⁻¹ + 4⁻¹) * (4⁻¹ + 4⁻¹) := by
  norm_num [← ENNReal.coe_ofNat 4, ← ENNReal.coe_inv (by norm_num : (4 : ℝ≥0) ≠ 0),
    ← ENNReal.coe_add, ← ENNReal.coe_mul, ← ENNReal.coe_one, ENNReal.coe_inj]

example : ¬ (4 : ℝ≥0∞)⁻¹ = 4⁻¹ * (4⁻¹ + 4⁻¹) := by
  norm_num [← ENNReal.coe_ofNat 4, ← ENNReal.coe_inv (by norm_num : (4 : ℝ≥0) ≠ 0),
    ← ENNReal.coe_add, ← ENNReal.coe_mul, ← ENNReal.coe_one, ENNReal.coe_inj]
