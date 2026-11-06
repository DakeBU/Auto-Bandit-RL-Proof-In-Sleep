import BanditRLProof.ConfidenceIntervals

namespace BanditRLProof.ConfidenceIntervalsCanary
open ConfidenceIntervals

example : |(3 / 5 : ℝ) - 1 / 2| ≤ 1 / 20 + 1 / 20 := by
  apply bias_statistical_composition (ν := (11 / 20 : ℝ)) <;> norm_num

example : (0 : Fin 2) ∈ survivors Finset.univ (fun _ => (1 / 2 : ℝ))
    (fun _ => (1 / 8 : ℝ)) := by
  apply optimal_survives Finset.univ (fun _ => (1 / 2 : ℝ)) _ _ 0
  · simp
  · intro i hi; rfl
  · intro i hi; norm_num

example : (1 : Fin 2) ∉ survivors Finset.univ
    (fun i => if i = 0 then (3 / 4 : ℝ) else 1 / 4) (fun _ => (1 / 16 : ℝ)) := by
  apply large_gap_removed Finset.univ
    (fun i => if i = 0 then (3 / 4 : ℝ) else 1 / 4) _ _ 0 1
    (r := (1 / 16 : ℝ))
  · simp
  · intro j hj; rfl
  · intro j hj; simp
  · norm_num

#print axioms ConfidenceIntervals.bias_statistical_composition
#print axioms ConfidenceIntervals.optimal_survives
#print axioms ConfidenceIntervals.large_gap_removed
end BanditRLProof.ConfidenceIntervalsCanary
