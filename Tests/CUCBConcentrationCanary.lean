import BanditRLProof.Algorithms.CUCBConfidence

/-! Visibility regression and axiom audits of actual-path concentration.
The noisy final-regret model required by the contract is still separate. -/
namespace Tests.CUCBConcentrationCanary
open BanditRLProof.CUCB

private noncomputable def feedback (hidden : UnitOutcome) (reward : ℝ) : Feedback 2 :=
  (fun i => decide (i.val=0),
    (fun i => if i.val=0 then ⟨1/2, by norm_num⟩ else hidden, reward))

/-- Neither a hidden arm outcome nor an unrelated reward can alter the
algorithm's input, even after arbitrarily many rounds. -/
theorem hidden_value_and_reward_ignored (x y : UnitOutcome) (r s : ℝ) (n : ℕ) :
    oracleInput (fun _ => feedback x r) n = oracleInput (fun _ => feedback y s) n := by
  apply oracleInput_visible
  · intro t ht i
    rfl
  · intro t ht i hi
    simp only [feedback, decide_eq_true_eq] at hi
    have hi' : i=0 := Fin.ext hi
    simp [feedback, hi']

#print axioms oracleInput_visible
#print axioms roundKernel_observedFactor_le_one
#print axioms cucb_condExp_observedCompensated
#print axioms cucb_successor_condMGF
#print axioms cucb_initial_MGF
#print axioms observed_sum_upper_tail
#print axioms observed_sum_lower_tail
#print axioms path_deviation_confidence
#print axioms hidden_value_and_reward_ignored
end Tests.CUCBConcentrationCanary
