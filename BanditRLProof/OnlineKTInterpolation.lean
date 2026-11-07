import BanditRLProof.OnlineKTPotential
import BanditRLProof.OnlineGammaSourceInterfaces
import Mathlib

open Finset
namespace BanditRL.OnlineKT
noncomputable section

theorem ktPotential_interpolate (ε : ℝ) (hε : 0 < ε) (t : ℕ) (ht : 1 ≤ t)
    (x c : ℝ) (hx : |x| ≤ (t : ℝ) - 1) (hc : |c| ≤ 1) :
  ktPotential ε t (x + c) ≤ (1 + c * x / (t : ℝ)) * ktPotential ε (t - 1) x := by
  obtain ⟨hxlo, hxhi⟩ := abs_le.mp hx
  obtain ⟨hclo, hchi⟩ := abs_le.mp hc
  let a : ℝ := (1 - c) / 2
  let b : ℝ := (1 + c) / 2
  have ha : 0 ≤ a := by dsimp [a]; linarith
  have hb : 0 ≤ b := by dsimp [b]; linarith
  have hab : a + b = 1 := by dsimp [a, b]; ring
  let A : ℝ → ℝ := fun z => ((t : ℝ) + 1 + (x + z)) / 2
  let B : ℝ → ℝ := fun z => ((t : ℝ) + 1 - (x + z)) / 2
  let L : ℝ → ℝ := fun z => Real.log (Real.Gamma (A z)) + Real.log (Real.Gamma (B z))
  have hApos (z : ℝ) (hz : |z| ≤ 1) : 0 < A z := by
    obtain ⟨hzlo, hzhi⟩ := abs_le.mp hz
    dsimp [A]
    linarith
  have hBpos (z : ℝ) (hz : |z| ≤ 1) : 0 < B z := by
    obtain ⟨hzlo, hzhi⟩ := abs_le.mp hz
    dsimp [B]
    linarith
  have hAa : a * A (-1) + b * A 1 = A c := by dsimp [a, b, A]; ring
  have hBa : a * B (-1) + b * B 1 = B c := by dsimp [a, b, B]; ring
  have hA : Real.log (Real.Gamma (A c)) ≤
      a * Real.log (Real.Gamma (A (-1))) + b * Real.log (Real.Gamma (A 1)) := by
    have h := BanditRL.OnlineGamma.convexOn_logGamma_positive.2
      (show A (-1) ∈ Set.Ioi 0 from hApos (-1) (by norm_num))
      (show A 1 ∈ Set.Ioi 0 from hApos 1 (by norm_num)) ha hb hab
    simpa only [smul_eq_mul, hAa] using h
  have hB : Real.log (Real.Gamma (B c)) ≤
      a * Real.log (Real.Gamma (B (-1))) + b * Real.log (Real.Gamma (B 1)) := by
    have h := BanditRL.OnlineGamma.convexOn_logGamma_positive.2
      (show B (-1) ∈ Set.Ioi 0 from hBpos (-1) (by norm_num))
      (show B 1 ∈ Set.Ioi 0 from hBpos 1 (by norm_num)) ha hb hab
    simpa only [smul_eq_mul, hBa] using h
  have hL : L c ≤ a * L (-1) + b * L 1 := by
    calc
      L c ≤ (a * Real.log (Real.Gamma (A (-1))) + b * Real.log (Real.Gamma (A 1))) +
          (a * Real.log (Real.Gamma (B (-1))) + b * Real.log (Real.Gamma (B 1))) :=
        add_le_add hA hB
      _ = a * L (-1) + b * L 1 := by dsimp [L]; ring
  have hexp : Real.exp (a * L (-1) + b * L 1) ≤
      a * Real.exp (L (-1)) + b * Real.exp (L 1) := by
    simpa only [smul_eq_mul] using
      (Real.convexOn_exp.2 (Set.mem_univ (L (-1))) (Set.mem_univ (L 1)) ha hb hab)
  have hchord := (Real.exp_le_exp.mpr hL).trans hexp
  let K : ℝ := ε * (2 : ℝ)^t / (Real.pi * Real.Gamma ((t : ℝ) + 1))
  have hden : 0 < Real.pi * Real.Gamma ((t : ℝ) + 1) :=
    mul_pos Real.pi_pos (Real.Gamma_pos_of_pos (by positivity))
  have hK : 0 ≤ K := by
    dsimp [K]
    exact div_nonneg (mul_nonneg hε.le (by positivity)) hden.le
  have hrepr (z : ℝ) (hz : |z| ≤ 1) : ktPotential ε t (x + z) = K * Real.exp (L z) := by
    have he : Real.exp (L z) = Real.Gamma (A z) * Real.Gamma (B z) := by
      dsimp [L]
      rw [Real.exp_add, Real.exp_log (Real.Gamma_pos_of_pos (hApos z hz)),
        Real.exp_log (Real.Gamma_pos_of_pos (hBpos z hz))]
    rw [he]
    dsimp [ktPotential, K, A, B]
    ring
  calc
    ktPotential ε t (x + c) = K * Real.exp (L c) := hrepr c hc
    _ ≤ K * (a * Real.exp (L (-1)) + b * Real.exp (L 1)) :=
      mul_le_mul_of_nonneg_left hchord hK
    _ = a * ktPotential ε t (x + (-1)) + b * ktPotential ε t (x + 1) := by
      rw [hrepr (-1) (by norm_num), hrepr 1 (by norm_num)]
      ring
    _ = (1 + c * x / (t : ℝ)) * ktPotential ε (t - 1) x := by
      rw [ktPotential_endpoint ε t ht x (-1) hx (Or.inl rfl),
        ktPotential_endpoint ε t ht x 1 hx (Or.inr rfl)]
      dsimp [a, b]
      ring

end
end BanditRL.OnlineKT
