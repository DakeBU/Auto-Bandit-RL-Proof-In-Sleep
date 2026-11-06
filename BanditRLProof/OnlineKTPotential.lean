import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral

namespace BanditRL.OnlineKT

noncomputable def ktPotential (ε : ℝ) (t : ℕ) (x : ℝ) : ℝ :=
  ε * (2 : ℝ)^t * Real.Gamma (((t : ℝ) + 1 + x) / 2) *
    Real.Gamma (((t : ℝ) + 1 - x) / 2) /
      (Real.pi * Real.Gamma ((t : ℝ) + 1))

theorem ktPotential_initial (ε : ℝ) :
    ktPotential ε 0 0 = ε := by
  simp only [ktPotential, Nat.cast_zero, pow_zero, zero_add, add_zero, sub_zero,
    mul_one, Real.Gamma_one_half_eq, Real.Gamma_one]
  rw [mul_assoc, ← sq, Real.sq_sqrt Real.pi_pos.le]
  exact mul_div_cancel_right₀ ε Real.pi_pos.ne'

theorem ktPotential_endpoint (ε : ℝ) (t : ℕ) (ht : 1 ≤ t)
    (x c : ℝ) (hx : |x| ≤ (t : ℝ) - 1) (hc : c = -1 ∨ c = 1) :
    ktPotential ε t (x + c) = (1 + c * x / (t : ℝ)) * ktPotential ε (t - 1) x := by
  cases t with
  | zero => omega
  | succ n =>
    simp only [Nat.cast_succ] at hx
    have u : 0 < (n:ℝ)+1 := by positivity
    obtain ⟨lo,hi⟩ := abs_le.mp hx
    have ha : 0 < ((n:ℝ)+1+x)/2 := by linarith
    have hb : 0 < ((n:ℝ)+1-x)/2 := by linarith
    have hd := (Real.Gamma_pos_of_pos u).ne'
    rcases hc with rfl | rfl
    · simp only [ktPotential,Nat.succ_sub_one,Nat.cast_succ,pow_succ]
      rw [show ((n:ℝ)+1+1+(x+(-1)))/2 = ((n:ℝ)+1+x)/2 by ring,
          show ((n:ℝ)+1+1-(x+(-1)))/2 = ((n:ℝ)+1-x)/2+1 by ring,
          Real.Gamma_add_one hb.ne',Real.Gamma_add_one u.ne']
      field_simp [u.ne',hd,Real.pi_pos.ne'] <;> ring
    · simp only [ktPotential,Nat.succ_sub_one,Nat.cast_succ,pow_succ]
      rw [show ((n:ℝ)+1+1+(x+1))/2 = ((n:ℝ)+1+x)/2+1 by ring,
          show ((n:ℝ)+1+1-(x+1))/2 = ((n:ℝ)+1-x)/2 by ring,
          Real.Gamma_add_one ha.ne',Real.Gamma_add_one u.ne']
      field_simp [u.ne',hd,Real.pi_pos.ne'] <;> ring

end BanditRL.OnlineKT
