import BanditRLProof.OnlineLearningMean

open BanditRL.OnlineLearning

example : empiricalMean (fun t => if t = 0 then 0 else 1) 2 = (1:ℝ)/2 := by
  norm_num [empiricalMean, Finset.sum_range_succ]

example (u : ℝ) :
    (∑ t ∈ Finset.range 2, ((1:ℝ)/2 - (if t = 0 then 0 else 1))^2) ≤
    ∑ t ∈ Finset.range 2, (u - (if t = 0 then 0 else 1))^2 := by
  have h := empiricalMean_minimizes (fun t => if t = 0 then 0 else 1) 2 (by omega) u
  norm_num [empiricalMean, Finset.sum_range_succ] at h ⊢
  exact h

example : empiricalMean (fun t => if t = 0 then 0 else 1) 2 ∈ Set.Icc (0:ℝ) 1 := by
  apply empiricalMean_mem _ _ (by omega)
  intro t ht
  split_ifs <;> norm_num

#print axioms BanditRL.OnlineLearning.empiricalMean_decomposition
#print axioms BanditRL.OnlineLearning.empiricalMean_minimizes
#print axioms BanditRL.OnlineLearning.empiricalMean_mem
