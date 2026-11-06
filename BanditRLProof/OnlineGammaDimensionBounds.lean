import BanditRLProof.OnlineGammaRatios

namespace BanditRL.OnlineGamma

private theorem gamma_ratio_raise_dimension (a s denominator : ℝ)
    (ha : 0 < a) (hs : 0 ≤ s)
    (h : Real.Gamma (a + 1 / 2) / denominator ≤ a ^ s) :
    Real.Gamma (a + 1 / 2 + 1) / denominator ≤ (a + 1) ^ (s + 1) := by
  calc
    Real.Gamma (a + 1 / 2 + 1) / denominator =
        (a + 1 / 2) * (Real.Gamma (a + 1 / 2) / denominator) := by
      rw [Real.Gamma_add_one (by linarith : a + 1 / 2 ≠ 0), mul_div_assoc]
    _ ≤ (a + 1 / 2) * a ^ s := mul_le_mul_of_nonneg_left h (by linarith)
    _ ≤ (a + 1) * (a + 1) ^ s := mul_le_mul (by linarith)
      (Real.rpow_le_rpow ha.le (by linarith) hs) (Real.rpow_nonneg ha.le s) (by linarith)
    _ = (a + 1) ^ (s + 1) := by
      rw [Real.rpow_add_one (by linarith : a + 1 ≠ 0)]
      ring

private theorem gamma_ratio_dimension_three (T : ℕ) (hT : 1 ≤ T) :
    Real.Gamma ((T : ℝ) + 3 / 2) / Real.Gamma ((T : ℝ) + 1 / 2) ≤ (T : ℝ) + 1 := by
  have ht : (1 : ℝ) ≤ T := by exact_mod_cast hT
  have hx : 0 < (T : ℝ) + 1 / 2 := by linarith
  have heq : (T : ℝ) + 3 / 2 = ((T : ℝ) + 1 / 2) + 1 := by ring
  rw [heq, Real.Gamma_add_one hx.ne', mul_div_cancel_right₀ _ (Real.Gamma_pos_of_pos hx).ne']
  linarith

theorem gamma_ratio_general_dimension :
  ∀ (T d : ℕ), 1 ≤ T → 2 ≤ d →
    Real.Gamma ((T:ℝ) + (d:ℝ)/2) / Real.Gamma ((T:ℝ) + 1/2) ≤ ((T:ℝ) + (d:ℝ)/2 - 1/2) ^ (((d:ℝ)-1)/2) := by
  intro T d hT hd
  have ht : (1 : ℝ) ≤ T := by exact_mod_cast hT
  have all_dimensions : ∀ n : ℕ, 2 ≤ n →
      Real.Gamma ((T : ℝ) + (n : ℝ) / 2) / Real.Gamma ((T : ℝ) + 1 / 2) ≤
        ((T : ℝ) + (n : ℝ) / 2 - 1 / 2) ^ (((n : ℝ) - 1) / 2) := by
    apply Nat.twoStepInduction
    · intro h; omega
    · intro h; omega
    · intro n ih _ hn2
      by_cases hn : 2 ≤ n
      · have hnreal : (2 : ℝ) ≤ n := by exact_mod_cast hn
        have ha : 0 < (T : ℝ) + (n : ℝ) / 2 - 1 / 2 := by linarith
        have hs : 0 ≤ ((n : ℝ) - 1) / 2 := by linarith
        have hprevious : Real.Gamma (((T : ℝ) + (n : ℝ) / 2 - 1 / 2) + 1 / 2) /
            Real.Gamma ((T : ℝ) + 1 / 2) ≤
            ((T : ℝ) + (n : ℝ) / 2 - 1 / 2) ^ (((n : ℝ) - 1) / 2) := by
          convert ih hn using 1 <;> congr 1 <;> ring
        have step := gamma_ratio_raise_dimension _ _ _ ha hs hprevious
        convert step using 1 <;> push_cast <;> congr 1 <;> ring
      · have hn_cases : n = 0 ∨ n = 1 := by omega
        rcases hn_cases with rfl | rfl
        · convert gamma_ratio_dimension_two T hT using 1 <;> norm_num <;> ring
        · convert gamma_ratio_dimension_three T hT using 1 <;> norm_num <;> ring
  exact all_dimensions d hd

end BanditRL.OnlineGamma
