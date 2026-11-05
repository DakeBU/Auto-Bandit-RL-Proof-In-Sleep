import BanditRLProof.OnlineKTPotential

namespace BanditRL.OnlineKT.Canary

theorem first_round_two_outcomes :
    ktPotential 7 1 (-1) = 7 ∧ ktPotential 7 1 1 = 7 := by
  have neg := ktPotential_endpoint 7 1 (by norm_num) 0 (-1) (by norm_num) (Or.inl rfl)
  have pos := ktPotential_endpoint 7 1 (by norm_num) 0 1 (by norm_num) (Or.inr rfl)
  constructor
  · simpa [ktPotential_initial] using neg
  · simpa [ktPotential_initial] using pos

theorem fractional_history_two_outcomes :
    ktPotential 1 3 (3/2) = (7/6 : ℝ) * ktPotential 1 2 (1/2) ∧
    ktPotential 1 3 (-(1/2)) = (5/6 : ℝ) * ktPotential 1 2 (1/2) ∧
    0 < ktPotential 1 3 (-(1/2)) ∧
    ktPotential 1 3 (-(1/2)) < ktPotential 1 3 (3/2) := by
  have pos := ktPotential_endpoint 1 3 (by norm_num) (1/2) 1 (by norm_num) (Or.inr rfl)
  have neg := ktPotential_endpoint 1 3 (by norm_num) (1/2) (-1) (by norm_num) (Or.inl rfl)
  norm_num at pos neg ⊢
  have base : 0 < ktPotential 1 2 (1/2) := by
    unfold ktPotential
    exact div_pos (mul_pos (mul_pos (by norm_num) (Real.Gamma_pos_of_pos (by norm_num)))
      (Real.Gamma_pos_of_pos (by norm_num))) (mul_pos Real.pi_pos (Real.Gamma_pos_of_pos (by norm_num)))
  exact ⟨pos,neg,by linarith only [base,neg],by linarith only [base,pos,neg]⟩

end BanditRL.OnlineKT.Canary
