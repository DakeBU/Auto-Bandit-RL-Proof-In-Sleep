import BanditRLProof

open MeasureTheory

noncomputable section

namespace Tests.OnlineGammaPropertiesCanary

theorem complex_nonreal_integral :
  ((1 : ℂ) + Complex.I).re = 1 ∧
  ((1 : ℂ) + Complex.I).im = 1 ∧
  MeasureTheory.IntegrableOn
    (fun t : ℝ => (Real.exp (-t) : ℂ) * (t : ℂ) ^ (((1 : ℂ) + Complex.I) - 1)) (Set.Ioi 0) ∧
  Complex.Gamma ((1 : ℂ) + Complex.I) =
    ∫ t in Set.Ioi (0 : ℝ), (Real.exp (-t) : ℂ) * (t : ℂ) ^ (((1 : ℂ) + Complex.I) - 1) := by
  have h := BanditRL.OnlineGamma.complexGamma_integral_and_integrable ((1 : ℂ) + Complex.I) (by norm_num)
  exact ⟨by norm_num, by norm_num, h.1, h.2⟩

theorem positive_half_digamma :
  deriv (fun y : ℝ => Real.log (Real.Gamma y)) (1/2 : ℝ) =
    deriv Real.Gamma (1/2 : ℝ) / Real.Gamma (1/2 : ℝ) ∧
  Real.log (1/2 : ℝ) - 1/(1/2 : ℝ) ≤
    deriv (fun y : ℝ => Real.log (Real.Gamma y)) (1/2 : ℝ) ∧
  deriv (fun y : ℝ => Real.log (Real.Gamma y)) (1/2 : ℝ) ≤
    Real.log (1/2 : ℝ) - 1/(2*(1/2 : ℝ)) ∧
  deriv (fun y : ℝ => Real.log (Real.Gamma y)) (1/2 : ℝ) <
    deriv (fun y : ℝ => Real.log (Real.Gamma y)) 1 := by
  have hp : (0 : ℝ) < 1 / 2 := by norm_num
  have bridge := BanditRL.OnlineGamma.logGammaSlope_eq_deriv_and_gamma_quotient (1 / 2 : ℝ) hp
  have bounds := BanditRL.OnlineGamma.logGammaSlope_bounds (1 / 2 : ℝ) hp
  have strict := BanditRL.OnlineGamma.logGamma_deriv_strictMonoOn_and_strictConcaveOn.1
    (show (1 / 2 : ℝ) ∈ Set.Ioi 0 from hp)
    (show (1 : ℝ) ∈ Set.Ioi 0 from by norm_num) (by norm_num : (1 / 2 : ℝ) < 1)
  exact ⟨bridge.1.symm.trans bridge.2, bridge.1 ▸ bounds.1, bridge.1 ▸ bounds.2, strict⟩

theorem batir_boundary_and_noninteger :
  (((1 : ℝ) - 1/2) / Real.exp 1) ^ ((1 : ℝ) - 1/2) * Real.sqrt (2 * Real.exp 1) ≤ Real.Gamma 1 ∧
  (((1 : ℝ) - 1/2) / Real.exp 1) ^ ((1 : ℝ) - 1/2) * Real.sqrt (2 * Real.exp 1) = Real.Gamma 1 ∧
  (((3/2 : ℝ) - 1/2) / Real.exp 1) ^ ((3/2 : ℝ) - 1/2) * Real.sqrt (2 * Real.exp 1) ≤ Real.Gamma (3/2 : ℝ) ∧
  (1 : ℝ) < 3/2 ∧ (3/2 : ℝ) < 2 := by
  have h1 := BanditRL.OnlineGamma.gamma_lower_bound_batir (1 : ℝ) (by norm_num)
  have hthree := BanditRL.OnlineGamma.gamma_lower_bound_batir (3 / 2 : ℝ) (by norm_num)
  have heq : (((1 : ℝ) - 1 / 2) / Real.exp 1) ^ ((1 : ℝ) - 1 / 2) *
      Real.sqrt (2 * Real.exp 1) = Real.Gamma 1 := by
    rw [show (1 : ℝ) - 1 / 2 = 1 / 2 by norm_num, ← Real.sqrt_eq_rpow,
      ← Real.sqrt_mul (by positivity : 0 ≤ (1 / 2 : ℝ) / Real.exp 1)]
    have hexp : Real.exp (1 : ℝ) ≠ 0 := (Real.exp_pos 1).ne'
    rw [show ((1 / 2 : ℝ) / Real.exp 1) * (2 * Real.exp 1) = 1 by field_simp [hexp]]
    rw [Real.sqrt_one, Real.Gamma_one]
  exact ⟨h1, heq, hthree, by norm_num, by norm_num⟩

theorem general_even_odd_dimensions :
  (Real.Gamma ((1:ℝ) + (4:ℝ)/2) / Real.Gamma ((1:ℝ) + 1/2) ≤
    ((1:ℝ) + (4:ℝ)/2 - 1/2) ^ (((4:ℝ)-1)/2)) ∧
  (Real.log (Real.sqrt Real.pi * Real.Gamma ((1:ℝ) + (4:ℝ)/2) /
    (Real.Gamma ((4:ℝ)/2) * Real.Gamma ((1:ℝ)+1/2))) ≤
    (((4:ℝ)-1)/2) * Real.log ((1:ℝ) / (((4:ℝ)-1)/2) + 1) +
      (4:ℝ)/2 - 1 + (1/2:ℝ)*Real.log (Real.pi/2)) ∧
  (Real.Gamma ((1:ℝ) + (5:ℝ)/2) / Real.Gamma ((1:ℝ) + 1/2) ≤
    ((1:ℝ) + (5:ℝ)/2 - 1/2) ^ (((5:ℝ)-1)/2)) ∧
  (Real.log (Real.sqrt Real.pi * Real.Gamma ((1:ℝ) + (5:ℝ)/2) /
    (Real.Gamma ((5:ℝ)/2) * Real.Gamma ((1:ℝ)+1/2))) ≤
    (((5:ℝ)-1)/2) * Real.log ((1:ℝ) / (((5:ℝ)-1)/2) + 1) +
      (5:ℝ)/2 - 1 + (1/2:ℝ)*Real.log (Real.pi/2)) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa only [Nat.cast_one, Nat.cast_ofNat] using
      (BanditRL.OnlineGamma.gamma_ratio_general_dimension 1 4 (by norm_num) (by norm_num))
  · simpa only [Nat.cast_one, Nat.cast_ofNat] using
      (BanditRL.OnlineGamma.log_gamma_ratio_general_dimension 1 4 (by norm_num) (by norm_num))
  · simpa only [Nat.cast_one, Nat.cast_ofNat] using
      (BanditRL.OnlineGamma.gamma_ratio_general_dimension 1 5 (by norm_num) (by norm_num))
  · simpa only [Nat.cast_one, Nat.cast_ofNat] using
      (BanditRL.OnlineGamma.log_gamma_ratio_general_dimension 1 5 (by norm_num) (by norm_num))

end Tests.OnlineGammaPropertiesCanary
