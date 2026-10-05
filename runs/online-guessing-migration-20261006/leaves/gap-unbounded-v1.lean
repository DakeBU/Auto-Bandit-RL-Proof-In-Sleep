import BanditRLProof.OnlineGuessingLower
import BanditRLProof.OnlineLearningFTL

open Set Finset
namespace BanditRL.OnlineGradientDescent

theorem meanPredict_zero_cumulativeLoss (T : ℕ) (hT : 0 < T) :
    (∑ t ∈ range T,
      (BanditRL.OnlineLearning.meanPredict (fun _ : ℕ => (0 : ℝ)) t)^2) = 1/4 := by
  have hp (t : ℕ) :
      (BanditRL.OnlineLearning.meanPredict (fun _ : ℕ => (0 : ℝ)) t)^2 =
        if t = 0 then (1/4 : ℝ) else 0 := by
    by_cases ht : t = 0
    · simp [BanditRL.OnlineLearning.meanPredict, ht]
      norm_num
    · simp [BanditRL.OnlineLearning.meanPredict,
        BanditRL.OnlineLearning.empiricalMean, ht]
  simp_rw [hp]
  simpa [hT] using (Finset.sum_ite_eq' (range T) 0 (fun _ => (1/4 : ℝ)))

theorem guessing_vs_mean_lower (n : ℕ) (hn : 0 < n) :
    (n : ℝ)/4 - 1/4 ≤
      regret unitInterval (1/(2*Real.sqrt (((2*n)^2 : ℕ) : ℝ)))
        (fun _ x => (x-0)^2) 1 0 ((2*n)^2) -
      (∑ t ∈ range ((2*n)^2),
        (BanditRL.OnlineLearning.meanPredict (fun _ : ℕ => (0 : ℝ)) t)^2) := by
  rw [meanPredict_zero_cumulativeLoss ((2*n)^2) (by positivity)]
  exact sub_le_sub_right (guessing_squared_horizon_lower n hn) (1/4)

#print axioms meanPredict_zero_cumulativeLoss
#check @meanPredict_zero_cumulativeLoss
#print axioms guessing_vs_mean_lower
#check @guessing_vs_mean_lower
theorem guessing_vs_mean_unbounded (C : ℝ) (N : ℕ) :
    ∃ n : ℕ, N < n ∧
      C < regret unitInterval (1/(2*Real.sqrt (((2*n)^2 : ℕ) : ℝ)))
        (fun _ x => (x-0)^2) 1 0 ((2*n)^2) -
      (∑ t ∈ range ((2*n)^2),
        (BanditRL.OnlineLearning.meanPredict (fun _ : ℕ => (0 : ℝ)) t)^2) := by
  obtain ⟨n, hn⟩ := exists_nat_gt (max (4*C+1) (N : ℝ))
  have hNC : (N : ℝ) < n := lt_of_le_of_lt (le_max_right _ _) hn
  have hN : N < n := by exact_mod_cast hNC
  have hnpos : 0 < n := Nat.lt_of_le_of_lt (Nat.zero_le N) hN
  refine ⟨n, hN, lt_of_lt_of_le ?_ (guessing_vs_mean_lower n hnpos)⟩
  have hC : 4*C+1 < (n : ℝ) := lt_of_le_of_lt (le_max_left _ _) hn
  linarith

#check @guessing_vs_mean_unbounded
#print axioms guessing_vs_mean_unbounded
end BanditRL.OnlineGradientDescent
