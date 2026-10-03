import Tests.HeavyTailRegretCanary

open MeasureTheory ProbabilityTheory BanditRLProof BanditRLProof.HeavyTail
namespace HeavyTailSourceScheduleCanary
open HeavyTailRegretCanary

-- Actual causal policy on the existing two genuinely noisy arms, with mean1 and1/2.

theorem upper_budget :
    (∑ t ∈ Finset.range 1000, (UCB.armStreamMeasure kernel).real {stream | 2 ≤ t ∧
      sourceConfidenceRadius 1 2 t (pullCount (SourcePolicy.robustAction (by decide) 1 2 stream) 0 t) ≤
        SourcePolicy.robustMean (by decide) 1 2 stream 0 t - ∫ x, x ∂kernel 0}) ≤ 2 := by
  exact SourcePolicy.robustMean_upper_tail_sum (by decide) kernel 0 1 2 1000
    (by norm_num) (by norm_num) (by norm_num) (integrable_law 0 _)
    (integrable_law 0 _) (moment 0)

theorem lower_budget :
    (∑ t ∈ Finset.range 1000, (UCB.armStreamMeasure kernel).real {stream | 2 ≤ t ∧
      sourceConfidenceRadius 1 2 t (pullCount (SourcePolicy.robustAction (by decide) 1 2 stream) 0 t) ≤
        (∫ x, x ∂kernel 0) - SourcePolicy.robustMean (by decide) 1 2 stream 0 t}) ≤ 2 := by
  exact SourcePolicy.robustMean_lower_tail_sum (by decide) kernel 0 1 2 1000
    (by norm_num) (by norm_num) (by norm_num) (integrable_law 0 _)
    (integrable_law 0 _) (moment 0)

#print axioms BanditRLProof.HeavyTail.source_adaptive_mean_upper_tail
#print axioms BanditRLProof.HeavyTail.source_schedule_tail_sum_le_two
#print axioms BanditRLProof.HeavyTail.SourcePolicy.robustMean_upper_tail_sum
#print axioms BanditRLProof.HeavyTail.SourcePolicy.robustMean_lower_tail_sum
#print axioms HeavyTailSourceScheduleCanary.upper_budget
#print axioms HeavyTailSourceScheduleCanary.lower_budget
end HeavyTailSourceScheduleCanary
