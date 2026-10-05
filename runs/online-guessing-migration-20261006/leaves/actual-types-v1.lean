import BanditRLProof
import Mathlib.Algebra.Order.Archimedean.Basic

open Set Finset BanditRL.OnlineGradientDescent
#check @BanditRL.OnlineGradientDescent.project_unitInterval
#check @BanditRL.OnlineGradientDescent.square_regular
#check @BanditRL.OnlineGradientDescent.gradient_square
#check @BanditRL.OnlineGradientDescent.gradient_square_bound
#check @BanditRL.OnlineGradientDescent.square_step_clamp
#check @BanditRL.OnlineGradientDescent.example_2_14
#check @BanditRL.OnlineGradientDescent.guessing_zero_trajectory
#check @BanditRL.OnlineGradientDescent.guessing_tuned_eta_square
#check @BanditRL.OnlineGradientDescent.guessing_squared_horizon_lower
#check @BanditRL.OnlineGradientDescent.unitInterval
#check @BanditRL.OnlineGradientDescent.iterate_prefix
#check @BanditRL.OnlineGradientDescent.equation_2_1
#check @BanditRL.OnlineLearning.meanPredict
#check @BanditRL.OnlineLearning.meanPredict_prefix
#check @BanditRL.OnlineLearning.theorem_1_3
#check @BanditRL.OnlineLearning.empiricalMean
#check @exists_nat_gt
#check @Finset.sum_ite_eq
#check @Finset.sum_ite_eq'
#check @Finset.mem_range

#check (∀ T : ℕ, 0 < T →
  (∑ t ∈ range T, (BanditRL.OnlineLearning.meanPredict (fun _ : ℕ => (0 : ℝ)) t)^2) = (1/4 : ℝ))
#check (∀ n : ℕ, 0 < n → (n : ℝ)/4 - 1/4 ≤
  regret unitInterval (1/(2*Real.sqrt (((2*n)^2 : ℕ) : ℝ)))
    (fun _ x => (x-0)^2) 1 0 ((2*n)^2) -
  (∑ t ∈ range ((2*n)^2), (BanditRL.OnlineLearning.meanPredict (fun _ : ℕ => (0 : ℝ)) t)^2))
#check (∀ C : ℝ, ∀ N : ℕ, ∃ n : ℕ, N < n ∧
  C < regret unitInterval (1/(2*Real.sqrt (((2*n)^2 : ℕ) : ℝ)))
    (fun _ x => (x-0)^2) 1 0 ((2*n)^2) -
  (∑ t ∈ range ((2*n)^2), (BanditRL.OnlineLearning.meanPredict (fun _ : ℕ => (0 : ℝ)) t)^2))
