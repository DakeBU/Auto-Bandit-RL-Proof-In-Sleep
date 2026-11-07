import BanditRLProof.OnlineKTPotential
import BanditRLProof.OnlineGammaSimplex
import BanditRLProof.OnlineEntropyKLBoundary
import BanditRLProof.OnlineGammaRatios
import Mathlib

open Finset
namespace BanditRL.OnlineKT
noncomputable section

private theorem weighted_log_scale (N z : ℝ) (hN : 0 < N) (hz : 0 ≤ z) :
    z * Real.log (z / (N / 2)) =
      z * Real.log z - z * Real.log N + z * Real.log 2 := by
  rcases hz.eq_or_lt with hzero | hpos
  · rw [← hzero]
    simp
  · rw [Real.log_div hpos.ne' (div_pos hN (by norm_num : (0 : ℝ) < 2)).ne',
      Real.log_div hN.ne' (by norm_num : (2 : ℝ) ≠ 0)]
    ring

private theorem binary_scaled_log_identity (N u v : ℝ) (hN : 0 < N)
    (hu : 0 ≤ u) (hv : 0 ≤ v) (hs : u + v = N) :
    N * BanditRLProof.KLUCB.bernoulliKLCore (u / N) (1 / 2) =
      N * Real.log 2 + u * Real.log u + v * Real.log v - N * Real.log N := by
  have hvN : 1 - u / N = v / N := by
    apply (eq_div_iff hN.ne').2
    field_simp [hN.ne']
    linarith
  have harg (z : ℝ) : (z / N) / (1 / 2 : ℝ) = z / (N / 2) := by
    field_simp [hN.ne'] <;> ring
  rw [BanditRLProof.KLUCB.bernoulliKLCore, hvN,
    show (1 : ℝ) - 1 / 2 = 1 / 2 by norm_num, harg u, harg v]
  calc
    N * (u / N * Real.log (u / (N / 2)) + v / N * Real.log (v / (N / 2))) =
        u * Real.log (u / (N / 2)) + v * Real.log (v / (N / 2)) := by
      field_simp [hN.ne'] <;> ring
    _ = u * Real.log u + v * Real.log v - (u + v) * Real.log N +
        (u + v) * Real.log 2 := by
      rw [weighted_log_scale N u hN hu, weighted_log_scale N v hN hv]
      ring
    _ = N * Real.log 2 + u * Real.log u + v * Real.log v - N * Real.log N := by
      rw [hs]
      ring

private theorem gamma_pair_log_lower (N u v : ℝ) (hN : 1 ≤ N)
    (hu : 0 ≤ u) (hv : 0 ≤ v) (hs : u + v = N) :
    u * Real.log u + v * Real.log v - N * Real.log N +
      Real.log (Real.Gamma (N + 1 / 2)) + Real.log (Real.Gamma (1 / 2)) ≤
      Real.log (Real.Gamma (u + 1 / 2)) + Real.log (Real.Gamma (v + 1 / 2)) := by
  have hN0 : 0 < N := by linarith
  let y : Fin 2 → ℝ := ![u, v]
  have hypos : ∀ i, 0 ≤ y i := by
    intro i
    fin_cases i <;> simp [y, hu, hv]
  have hy : y ∈ BanditRL.OnlineGamma.nonnegativeMassSimplex 2 N := by
    refine ⟨hypos, ?_⟩
    simpa [Fin.sum_univ_two, y] using hs
  have hmax := BanditRL.OnlineGamma.simplexGammaProduct_le_vertex_and_value
    2 N (by norm_num) hN y hy (0 : Fin 2)
  have hp := BanditRL.OnlineGamma.simplexGammaProduct_pos_and_log 2 y hypos
  have hbound : BanditRL.OnlineGamma.simplexGammaProduct 2 y ≤
      N ^ N / (Real.Gamma (N + 1 / 2) * Real.Gamma (1 / 2)) := by
    simpa using hmax.2.1.trans_eq hmax.2.2
  have hplog : Real.log (BanditRL.OnlineGamma.simplexGammaProduct 2 y) =
      u * Real.log u + v * Real.log v -
        Real.log (Real.Gamma (u + 1 / 2)) - Real.log (Real.Gamma (v + 1 / 2)) := by
    rw [hp.2, Fin.sum_univ_two]
    dsimp [y, BanditRL.OnlineGamma.simplexLogFactor]
    ring
  have hgN : 0 < Real.Gamma (N + 1 / 2) := Real.Gamma_pos_of_pos (by linarith)
  have hgh : 0 < Real.Gamma (1 / 2 : ℝ) := Real.Gamma_pos_of_pos (by norm_num)
  have hlog := Real.log_le_log hp.1 hbound
  rw [hplog, Real.log_div (Real.rpow_pos_of_pos hN0 N).ne' (mul_pos hgN hgh).ne',
    Real.log_rpow hN0, Real.log_mul hgN.ne' hgh.ne'] at hlog
  linarith

private theorem half_gamma_prefactor_log (N : ℝ) (hN : 0 < N) :
    Real.log (Real.Gamma (N + 1 / 2)) + Real.log (Real.Gamma (1 / 2)) -
      Real.log Real.pi - Real.log (Real.Gamma (N + 1)) =
      -Real.log (Real.sqrt Real.pi * Real.Gamma (N + 1) /
        (Real.Gamma 1 * Real.Gamma (N + 1 / 2))) := by
  have hs : 0 < Real.sqrt Real.pi := Real.sqrt_pos.2 Real.pi_pos
  have hg : 0 < Real.Gamma (N + 1) := Real.Gamma_pos_of_pos (by linarith)
  have hh : 0 < Real.Gamma (N + 1 / 2) := Real.Gamma_pos_of_pos (by linarith)
  rw [Real.Gamma_one_half_eq, Real.Gamma_one, one_mul,
    Real.log_div (mul_pos hs hg).ne' hh.ne', Real.log_mul hs.ne' hg.ne']
  have h := Real.log_sqrt Real.pi_pos.le
  linarith

private theorem ktPotential_pos_and_log (ε : ℝ) (hε : 0 < ε) (n : ℕ)
    (x : ℝ) (hx : |x| ≤ (n : ℝ)) :
    0 < ktPotential ε n x ∧
      Real.log (ktPotential ε n x) = Real.log ε + (n : ℝ) * Real.log 2 +
        Real.log (Real.Gamma (((n : ℝ) + x) / 2 + 1 / 2)) +
        Real.log (Real.Gamma (((n : ℝ) - x) / 2 + 1 / 2)) -
        Real.log Real.pi - Real.log (Real.Gamma ((n : ℝ) + 1)) := by
  obtain ⟨hlo, hhi⟩ := abs_le.mp hx
  have hu : 0 < ((n : ℝ) + x) / 2 + 1 / 2 := by linarith
  have hv : 0 < ((n : ℝ) - x) / 2 + 1 / 2 := by linarith
  have hgu := Real.Gamma_pos_of_pos hu
  have hgv := Real.Gamma_pos_of_pos hv
  have hgn : 0 < Real.Gamma ((n : ℝ) + 1) := Real.Gamma_pos_of_pos (by positivity)
  have hp : 0 < (2 : ℝ)^n := by positivity
  have ha : ((n : ℝ) + 1 + x) / 2 = ((n : ℝ) + x) / 2 + 1 / 2 := by ring
  have hb : ((n : ℝ) + 1 - x) / 2 = ((n : ℝ) - x) / 2 + 1 / 2 := by ring
  constructor
  · rw [ktPotential, ha, hb]
    exact div_pos (mul_pos (mul_pos (mul_pos hε hp) hgu) hgv) (mul_pos Real.pi_pos hgn)
  · rw [ktPotential, ha, hb,
      Real.log_div (mul_pos (mul_pos (mul_pos hε hp) hgu) hgv).ne' (mul_pos Real.pi_pos hgn).ne',
      Real.log_mul (mul_pos (mul_pos hε hp) hgu).ne' hgv.ne',
      Real.log_mul (mul_pos hε hp).ne' hgu.ne', Real.log_mul hε.ne' hp.ne',
      Real.log_mul Real.pi_pos.ne' hgn.ne', Real.log_pow]
    ring

theorem ktPotential_exp_lower (ε : ℝ) (hε : 0 < ε) (n : ℕ) (hn : 1 ≤ n)
    (x : ℝ) (hx : |x| ≤ (n : ℝ)) :
  ε * Real.exp (x^2 / (2 * (n : ℝ)) - Real.log (n : ℝ) / 2 - 1) ≤ ktPotential ε n x := by
  let N : ℝ := (n : ℝ)
  let u : ℝ := (N + x) / 2
  let v : ℝ := (N - x) / 2
  have hN : 1 ≤ N := by exact_mod_cast hn
  have hN0 : 0 < N := by linarith
  obtain ⟨hxlo, hxhi⟩ := abs_le.mp hx
  have hu : 0 ≤ u := by dsimp [u, N]; linarith
  have hv : 0 ≤ v := by dsimp [v, N]; linarith
  have hs : u + v = N := by dsimp [u, v]; ring
  have hp : u / N = 1 / 2 + x / (2 * N) := by
    dsimp [u]
    field_simp [hN0.ne'] <;> ring
  have hpair := gamma_pair_log_lower N u v hN hu hv hs
  have hidentity := binary_scaled_log_identity N u v hN0 hu hv hs
  have hKL := BanditRL.OnlineEntropy.KLBoundary.scaled_binary_use N x hN hx
  rw [← hp] at hKL
  have hratio := BanditRL.OnlineGamma.log_gamma_ratio_dimension_two n hn
  have hR : Real.log (Real.sqrt Real.pi * Real.Gamma (N + 1) /
      (Real.Gamma 1 * Real.Gamma (N + 1 / 2))) ≤ Real.log N / 2 + 1 := by
    change Real.log (Real.sqrt Real.pi * Real.Gamma ((n : ℝ) + 1) /
      (Real.Gamma 1 * Real.Gamma ((n : ℝ) + 1 / 2))) ≤ Real.log (n : ℝ) / 2 + 1
    linarith [hratio.1, hratio.2]
  have hpre := half_gamma_prefactor_log N hN0
  have hF := ktPotential_pos_and_log ε hε n x hx
  change 0 < ktPotential ε n x ∧
    Real.log (ktPotential ε n x) = Real.log ε + N * Real.log 2 +
      Real.log (Real.Gamma (u + 1 / 2)) + Real.log (Real.Gamma (v + 1 / 2)) -
      Real.log Real.pi - Real.log (Real.Gamma (N + 1)) at hF
  have hlog : Real.log ε + (x^2 / (2 * N) - Real.log N / 2 - 1) ≤
      Real.log (ktPotential ε n x) := by
    linarith [hpair, hidentity, hKL, hR, hpre, hF.2]
  calc
    ε * Real.exp (x^2 / (2 * (n : ℝ)) - Real.log (n : ℝ) / 2 - 1) =
        Real.exp (Real.log ε + (x^2 / (2 * N) - Real.log N / 2 - 1)) := by
      rw [Real.exp_add, Real.exp_log hε]
    _ ≤ Real.exp (Real.log (ktPotential ε n x)) := Real.exp_le_exp.mpr hlog
    _ = ktPotential ε n x := Real.exp_log hF.1

end
end BanditRL.OnlineKT
