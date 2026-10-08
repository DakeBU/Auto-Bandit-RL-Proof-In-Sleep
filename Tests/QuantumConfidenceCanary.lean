import BanditRLProof.QuantumConfidence
import BanditRLProof.QuantumQueryAccounting

namespace BanditRLProof.QuantumCanary
open QuantumConfidence QuantumQueryAccounting

example : |(3 / 5 : ℝ) - 1 / 2| ≤ 1 / 20 + 1 / 20 := by
  apply bias_statistical_composition (ν := (11 / 20 : ℝ)) <;> norm_num

/-- Equal optimal means survive; no chosen unique best arm is assumed. -/
example : (0 : Fin 2) ∈ survivors Finset.univ (fun _ => (1 / 2 : ℝ))
    (fun _ => (1 / 8 : ℝ)) := by
  apply optimal_survives Finset.univ (fun _ => (1 / 2 : ℝ)) _ _ 0
  · simp
  · intro i hi; rfl
  · intro i hi; norm_num

/-- A genuinely suboptimal arm is removed by the strict interval rule. -/
example : (1 : Fin 2) ∉ survivors Finset.univ
    (fun i => if i = 0 then (3 / 4 : ℝ) else 1 / 4) (fun _ => (1 / 16 : ℝ)) := by
  apply large_gap_removed Finset.univ
    (fun i => if i = 0 then (3 / 4 : ℝ) else 1 / 4) _ _ 0 1
    (r := (1 / 16 : ℝ))
  · simp
  · intro j hj; rfl
  · intro j hj; simp
  · norm_num

def inverseOnly : Block 2 3 := ⟨1, 0, 3, by decide⟩
def mixed : Block 2 3 := ⟨0, 1, 2, by decide⟩

example : (expanded [mixed, inverseOnly]).length = 6 := by decide
example : expanded [mixed, inverseOnly] = [0, 0, 0, 1, 1, 1] := by decide

#eval (expanded [mixed, inverseOnly]).map Fin.val
#print axioms QuantumConfidence.fixed_fidelity_failure_bound
#print axioms QuantumConfidence.large_gap_removed
#print axioms QuantumQueryAccounting.charge_eq_expanded_gap_sum

end BanditRLProof.QuantumCanary
#print axioms BanditRLProof.QuantumQueryAccounting.chargedRegret_eq_realMeanRegret
#print axioms BanditRLProof.QuantumQueryAccounting.chargedRegret_eq_gap_pullCount
#print axioms BanditRLProof.QuantumConfidence.recommend_fixed_fidelity_failure_bound
