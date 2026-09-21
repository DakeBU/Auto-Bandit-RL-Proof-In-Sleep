import BanditRLProof

open MeasureTheory ProbabilityTheory BanditRLProof.HOO
open BanditRLProof.HOO.CantorModel

noncomputable section
namespace HOORateCanary
set_option autoImplicit false

example : Infinite Arm := inferInstance
example (x : Arm) (r : ℝ) : law x ≠ Measure.dirac r := law_not_dirac x r
example : covering.nearOptimalityDimension mean (1/2) 4 ≤ (2:EReal) := dimension_le_two 4

/-- Full-rate consumption with no assumed dimension or confidence premise. -/
example : ∃ γ : ℝ, 0<γ ∧ ∀ N : ℕ, 1≤N →
    (∫ Y, (∑ n ∈ Finset.range N, ((1/2:ℝ)-Y n))
      ∂trajectory 1 (1/2) (covering.toCovering.nodeLaw law)) ≤
      γ*(N:ℝ)^(4/5:ℝ)*(Real.log (max (N:ℝ) 2))^(1/5:ℝ) := expected_actual_rate

#print axioms BanditRLProof.HOO.exists_regret_depth
#print axioms BanditRLProof.HOO.RegularCovering.expected_pseudoRegret_rate
#print axioms BanditRLProof.HOO.integral_trajectory_reward
#print axioms BanditRLProof.HOO.RegularCovering.expected_actual_eq_pseudoRegret
#print axioms BanditRLProof.HOO.RegularCovering.expected_actualRegret_rate
#print axioms BanditRLProof.HOO.CantorModel.dimension_le_two
#print axioms BanditRLProof.HOO.CantorModel.expected_actual_rate

end HOORateCanary
