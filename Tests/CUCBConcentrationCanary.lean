import BanditRLProof.Algorithms.CUCBNiceEvent

/-! Visibility regression and dependency audits of actual-path concentration.
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

/-- Zero observations are covered even when the true means are at the endpoints. -/
theorem empty_history_nice (means : Fin 2 → ℝ) (hm : ∀i, means i ∈ Set.Icc (0:ℝ) 1)
    (Y : ℕ → Round Unit 2) : Y ∈ NiceEvent means 0 := by
  intro i
  simp only [empiricalMean, observationCount, Finset.range_zero, Finset.sum_empty,
    ↓reduceIte, confidenceRadius]
  rw [abs_of_nonneg (sub_nonneg.mpr (hm i).2)]
  linarith [(hm i).1]

#print axioms empirical_bad_implies_deviation
#print axioms empirical_bad_probability_source
#print axioms niceEvent_complement_probability
#print axioms upperIndex_of_confidence
#print axioms empty_history_nice
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
