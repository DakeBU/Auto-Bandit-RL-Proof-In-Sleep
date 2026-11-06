import BanditRLProof.OnlineGammaDimensionBounds
import BanditRLProof.OnlineGammaBatir

namespace BanditRL.OnlineGamma

theorem log_gamma_ratio_general_dimension :
  ∀ (T d : ℕ), 1 ≤ T → 2 ≤ d →
    Real.log (Real.sqrt Real.pi * Real.Gamma ((T:ℝ) + (d:ℝ)/2) /
      (Real.Gamma ((d:ℝ)/2) * Real.Gamma ((T:ℝ)+1/2))) ≤
      (((d:ℝ)-1)/2) * Real.log ((T:ℝ) / (((d:ℝ)-1)/2) + 1) +
        (d:ℝ)/2 - 1 + (1/2:ℝ)*Real.log (Real.pi/2)
 := by
  intro T d hT hd
  have ht : (1 : ℝ) ≤ T := by exact_mod_cast hT
  have hdreal : (2 : ℝ) ≤ d := by exact_mod_cast hd
  let m : ℝ := ((d : ℝ) - 1) / 2
  have hm : 0 < m := by dsimp [m]; linarith
  have htm : 0 < (T : ℝ) + m := by linarith
  have hdhalf : 1 ≤ (d : ℝ) / 2 := by linarith
  have hga := Real.Gamma_pos_of_pos (show 0 < (T : ℝ) + (d : ℝ) / 2 by linarith)
  have hgb := Real.Gamma_pos_of_pos (show 0 < (d : ℝ) / 2 by linarith)
  have hgc := Real.Gamma_pos_of_pos (show 0 < (T : ℝ) + 1 / 2 by linarith)
  have hsq := Real.sqrt_pos.2 Real.pi_pos
  have he := Real.exp_pos (1 : ℝ)
  have htwo : 0 < 2 * Real.exp 1 := by positivity
  have hshift : (T : ℝ) + (d : ℝ) / 2 - 1 / 2 = (T : ℝ) + m := by dsimp [m]; ring
  have ha := Real.log_le_log (div_pos hga hgc) (gamma_ratio_general_dimension T d hT hd)
  rw [Real.log_div hga.ne' hgc.ne', hshift, Real.log_rpow htm] at ha
  have hu : (d : ℝ) / 2 - 1 / 2 = m := by dsimp [m]; ring
  have hb0 := gamma_lower_bound_batir ((d : ℝ) / 2) hdhalf
  rw [hu] at hb0
  have hp := Real.rpow_pos_of_pos (div_pos hm he) m
  have hs := Real.sqrt_pos.2 htwo
  have hb := Real.log_le_log (mul_pos hp hs) hb0
  rw [Real.log_mul hp.ne' hs.ne', Real.log_rpow (div_pos hm he),
    Real.log_div hm.ne' he.ne', Real.log_exp, Real.log_sqrt htwo.le,
    Real.log_mul (by norm_num) he.ne', Real.log_exp] at hb
  have hlog : Real.log ((T : ℝ) / m + 1) = Real.log ((T : ℝ) + m) - Real.log m := by
    rw [show (T : ℝ) / m + 1 = ((T : ℝ) + m) / m by
      rw [add_div, div_self hm.ne']]
    exact Real.log_div htm.ne' hm.ne'
  rw [Real.log_div (mul_pos hsq hga).ne' (mul_pos hgb hgc).ne',
    Real.log_mul hsq.ne' hga.ne', Real.log_mul hgb.ne' hgc.ne',
    Real.log_sqrt Real.pi_pos.le,
    Real.log_div Real.pi_pos.ne' (by norm_num)]
  change Real.log Real.pi / 2 + Real.log (Real.Gamma ((T : ℝ) + (d : ℝ) / 2)) -
      (Real.log (Real.Gamma ((d : ℝ) / 2)) + Real.log (Real.Gamma ((T : ℝ) + 1 / 2))) ≤
    m * Real.log ((T : ℝ) / m + 1) + (d : ℝ) / 2 - 1 +
      (1 / 2 : ℝ) * (Real.log Real.pi - Real.log 2)
  rw [hlog]
  change Real.log (Real.Gamma ((T : ℝ) + (d : ℝ) / 2)) -
    Real.log (Real.Gamma ((T : ℝ) + 1 / 2)) ≤ m * Real.log ((T : ℝ) + m) at ha
  have hmval : m = ((d : ℝ) - 1) / 2 := rfl
  nlinarith [ha, hb]

end BanditRL.OnlineGamma
