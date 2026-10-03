import BanditRLProof

open MeasureTheory ProbabilityTheory BanditRLProof
open BanditRLProof.HeavyTail

namespace HeavyTailSourceCounterexampleCanary

/-- The fixed finite witness is paired with its actual admissible raw moments;
no count cap, confidence event, or target regret hypothesis is supplied. -/
example :
    (∀ a : Fin 2, Integrable (fun x : ℝ => |x|^(1+(1 : ℝ))) (SourceCounterexample.kernel a)) ∧
    (∀ a : Fin 2, (∫ x : ℝ, |x|^(1+(1 : ℝ)) ∂SourceCounterexample.kernel a) ≤ 1) ∧
    (32 * Real.log ((2^50 : ℕ) : ℝ) + 5 <
      ∫ stream, realMeanRegret (realKernelMean SourceCounterexample.kernel)
        (SourcePolicy.robustAction (by decide) 1 1 stream) (2^50)
          ∂UCB.armStreamMeasure SourceCounterexample.kernel) := by
  exact ⟨fun a => (SourceCounterexample.kernel_raw_moment a).1,
    fun a => (SourceCounterexample.kernel_raw_moment a).2,
    SourceCounterexample.printed_coefficient_counterexample⟩

#print axioms SourceCounterexample.kernel_raw_moment
#print axioms SourceCounterexample.finite_count_obstruction
#print axioms SourceCounterexample.printed_coefficient_counterexample
#print axioms SourceCounterexample.literal_printed_bound_false

end HeavyTailSourceCounterexampleCanary
