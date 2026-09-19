import Tests.HeavyTailRegretCanary

open MeasureTheory ProbabilityTheory BanditRLProof BanditRLProof.HeavyTail

namespace HeavyTailSourceConfidenceCanary
open HeavyTailRegretCanary

-- One thousand genuinely random observations with mean one, raw second moment two.
-- Arbitrary delta=1/20 is unrelated to the existing algorithm's time schedule.
theorem upper :
    (UCB.armStreamMeasure kernel).real {stream |
      4*(2 : ℝ)^(1/(1+1 : ℝ))*(Real.log (1/(1/20 : ℝ))/1000)^(1/(1+1 : ℝ)) ≤
        (∑ i ∈ Finset.range 1000,
          truncate (sourceTruncationThreshold 1 2 (Real.log (1/(1/20 : ℝ))) i) (stream i 0))/1000 - 1}
      ≤ (1/20 : ℝ) := by
  apply source_truncated_mean_upper_tail (UCB.armStreamMeasure kernel)
    (fun i stream => stream i 0) 1 2 (1/20) 1 1000 (by decide)
    (fun i => (measurable_pi_apply 0).comp (measurable_pi_apply i))
  · simpa only [sub_zero] using UCB.iIndepFun_armStreamMeasure_coord_sub kernel 0 0
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · intro i
    exact arm_coordinate_integrable kernel 0 i (fun x : ℝ => x) (integrable_law 0 _)
  · intro i
    have h := arm_coordinate_integral kernel 0 i (fun x : ℝ => x) measurable_id
    simpa [kernel, Kernel.ofFunOfCountable, law_integral] using h
  · intro i
    exact arm_coordinate_integrable kernel 0 i (fun x : ℝ => |x|^(1+(1 : ℝ))) (integrable_law 0 _)
  · intro i
    rw [arm_coordinate_integral kernel 0 i (fun x => |x|^(1+(1 : ℝ))) (by fun_prop)]
    exact moment 0

#print axioms BanditRLProof.HeavyTail.bounded_centering_mgf_unshifted
#print axioms BanditRLProof.HeavyTail.source_truncated_mean_upper_tail
#print axioms BanditRLProof.HeavyTail.source_truncated_mean_lower_tail

end HeavyTailSourceConfidenceCanary
