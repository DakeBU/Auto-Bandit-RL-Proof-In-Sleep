import BanditRLProof

open MeasureTheory ProbabilityTheory BanditRLProof
open BanditRLProof.HeavyTail.GenaltiAudit

namespace HeavyTailRegretCapCanary

/-- A nonempty, positive-regret slice at horizon1000, with its actual moment
witness. This is sharpness over trace laws, not every fixed algorithm. -/
example :
    (∀ i : Fin 2, Integrable (fun x : ℝ => |x|^(1+(1:ℝ))) (extremeKernel i)) ∧
    (∀ i : Fin 2, (∫ x, |x|^(1+(1:ℝ)) ∂extremeKernel i) ≤ 1) ∧
    sSup (normalizedValues 2 1 1000) = (2000 : EReal) := by
  refine ⟨fun i => (extreme_moment i).1, fun i => (extreme_moment i).2, ?_⟩
  rw [normalized_sSup_two_eq]
  norm_num
  rfl

/-- Consume the actual-process adapter using the bad constant action on Unit. -/
example :
    (((∫ _ω : Unit, realMeanRegret (realKernelMean extremeKernel)
      (fun _ => (1:Fin 2)) 1000 ∂Measure.dirac ()) / (1:ℝ)^(1/(1+1:ℝ)) : ℝ) : EReal)
      ∈ normalizedValues 2 1 1000 := by
  exact process_value_mem extremeKernel 1 1 (by norm_num)
    (fun i => (extreme_moment i).1) (fun i => (extreme_moment i).2)
    (Measure.dirac ()) (fun _ _ => 1) (fun _ => measurable_const) 1000

#print axioms normalized_sSup_ne_top
#print axioms process_value_mem
#print axioms normalized_sSup_two_eq
end HeavyTailRegretCapCanary
