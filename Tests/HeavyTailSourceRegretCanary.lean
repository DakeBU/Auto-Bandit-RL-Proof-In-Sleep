import Tests.HeavyTailRegretCanary

open MeasureTheory ProbabilityTheory BanditRLProof BanditRLProof.HeavyTail
namespace HeavyTailSourceRegretCanary
open HeavyTailRegretCanary

-- Actual fixed causal source policy, two noisy arms, gap1/2, million-round horizon.
-- Raw moments are discharged from the law; no supplied confidence/count bound.
theorem regret : (∫ stream, realMeanRegret (realKernelMean kernel)
    (SourcePolicy.robustAction (K := 2) (by decide) 1 2 stream) 1000000
      ∂UCB.armStreamMeasure kernel) ≤
    ∑ arm ∈ Finset.univ.filter (fun arm : Fin 2 => 0 < realMeanGap (realKernelMean kernel) arm),
      realMeanGap (realKernelMean kernel) arm *
        (SourcePolicy.gapBudget 1 2 (realMeanGap (realKernelMean kernel) arm) 1000000 + 5) := by
  apply SourcePolicy.robust_expected_regret (by decide) kernel 1 2 1000000
    (by norm_num) (by norm_num) (by norm_num)
  · intro arm
    exact integrable_law arm _
  · exact moment

#print axioms BanditRLProof.HeavyTail.SourcePolicy.robust_expected_regret
#print axioms BanditRLProof.HeavyTail.SourcePolicy.robust_integral_count_le_budget
#print axioms HeavyTailSourceRegretCanary.regret
end HeavyTailSourceRegretCanary
