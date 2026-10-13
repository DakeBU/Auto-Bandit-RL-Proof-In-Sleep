import BanditRLProof

namespace Tests.OnlineGuessingOGD
open BanditRL.OnlineGradientDescent Set
noncomputable def labels (t : ℕ) : ℝ := if t = 0 then 1 else 0
noncomputable def losses (t : ℕ) (x : ℝ) : ℝ := (x-labels t)^2
lemma first_projected : iterate unitInterval 1 losses (1/2) 1 = 1 := by
  change step unitInterval 1 (fun x : ℝ => (x-1)^2) (1/2) = 1
  rw [square_step_clamp]
  norm_num
lemma second_projected : iterate unitInterval 1 losses (1/2) 2 = 0 := by
  change step unitInterval 1 (fun x : ℝ => (x-0)^2) (iterate unitInterval 1 losses (1/2) 1) = 0
  rw [first_projected, square_step_clamp]
  norm_num
lemma source_four_rounds : ∀ u ∈ Icc (0:ℝ) 1,
    regret unitInterval (1/4) losses (1/2) u 4 ≤ 4 := by
  have h := example_2_14 labels (1/2) (by norm_num) 4 (by omega)
    (by intro t ht; unfold labels; split_ifs <;> norm_num)
  norm_num at h
  intro u hu
  exact h u hu.1 hu.2
#print axioms first_projected
#print axioms second_projected
#print axioms source_four_rounds
end Tests.OnlineGuessingOGD

#print axioms BanditRL.OnlineGradientDescent.project_unitInterval
#print axioms BanditRL.OnlineGradientDescent.square_regular
#print axioms BanditRL.OnlineGradientDescent.gradient_square
#print axioms BanditRL.OnlineGradientDescent.gradient_square_bound
#print axioms BanditRL.OnlineGradientDescent.square_step_clamp
#print axioms BanditRL.OnlineGradientDescent.example_2_14