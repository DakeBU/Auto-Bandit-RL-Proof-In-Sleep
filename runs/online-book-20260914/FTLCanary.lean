import BanditRLProof.OnlineLearningFTL
open BanditRL.OnlineLearning

def samples (t : ℕ) : ℝ := if t = 0 then 0 else 1

example : meanPredict samples 0 = 1/2 ∧ meanPredict samples 1 = 0 ∧
    empiricalMean samples 2 = 1/2 := by
  norm_num [meanPredict, empiricalMean, samples, Finset.sum_range_succ]

example : (∑ t ∈ Finset.range 2, (meanPredict samples t - samples t)^2) -
    (∑ t ∈ Finset.range 2, (empiricalMean samples 2 - samples t)^2) = 3/4 := by
  norm_num [meanPredict, empiricalMean, samples, Finset.sum_range_succ]

example : (∑ t ∈ Finset.range 2, (meanPredict samples t - samples t)^2) -
    (∑ t ∈ Finset.range 2, (empiricalMean samples 2 - samples t)^2) ≤
      4 + 4 * Real.log 2 := by
  apply theorem_1_3 samples 2 (by omega)
  intro t ht
  unfold samples
  split_ifs <;> norm_num

#print axioms BanditRL.OnlineLearning.meanPredict_prefix
#print axioms BanditRL.OnlineLearning.meanPredict_stability
#print axioms BanditRL.OnlineLearning.theorem_1_3
