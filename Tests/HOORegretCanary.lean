import BanditRLProof

open MeasureTheory ProbabilityTheory BanditRLProof.HOO
open BanditRLProof.HOO.CantorModel

noncomputable section
namespace HOORegretCanary
set_option autoImplicit false

/-- The complete infinite-arm noisy model consumes the actual expected
regret bound at every cutoff and horizon, not just a deterministic tree lemma. -/
theorem expected_regret (H N : ℕ) :
    (∫ Y, (∑ n ∈ Finset.range N, ((1/2:ℝ)-mean (covering.toCovering.arm 1 (1/2) Y n)))
      ∂trajectory 1 (1/2) (covering.toCovering.nodeLaw law)) ≤
    4*((1/2:ℝ)^H)*N +
    (∑ h ∈ Finset.range H, 4*((1/2:ℝ)^h)*(covering.nearOptimalNodes mean (1/2) h).card) +
    ∑ h ∈ Finset.range H, 4*((1/2:ℝ)^h)*(covering.boundaryNodes mean (1/2) h).card *
      (8*Real.log (max (N:ℝ) 2)/((1/2:ℝ)^(h+1))^2+4) := by
  have hr (x : Arm) : mean x ∈ Set.Icc (0:ℝ) 1 := by
    unfold mean; split_ifs <;> norm_num
  have he := covering.expected_regret_partition_bound law mean (1/2) law_mean mean_le_best
    hr global_sup weaklyLipschitz law_bounded H N
  simpa only [covering, one_mul] using he

#print axioms BanditRLProof.HOO.RegularCovering.node_partition_cover
#print axioms BanditRLProof.HOO.RegularCovering.actual_regret_partition
#print axioms BanditRLProof.HOO.RegularCovering.pathwise_regret_le
#print axioms BanditRLProof.HOO.RegularCovering.expected_regret_partition_bound
#print axioms BanditRLProof.HOO.RegularCovering.expected_regret_dimension_sums
#print axioms HOORegretCanary.expected_regret

end HOORegretCanary
