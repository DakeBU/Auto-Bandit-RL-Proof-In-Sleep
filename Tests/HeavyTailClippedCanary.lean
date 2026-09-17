import Tests.HeavyTailRegretCanary

open MeasureTheory ProbabilityTheory BanditRLProof BanditRLProof.HeavyTail

namespace HeavyTailClippedCanary
open HeavyTailRegretCanary

-- A genuinely random prefix length on the noisy two-arm product law.
noncomputable def count (stream : UCB.ArmRewardStream 2) : ℕ :=
  if stream 0 0 > 0 then 2 else 1

example : (UCB.armStreamMeasure kernel).real {stream |
    0 < count stream ∧ count stream ≤ 2 ∧
    confidenceRadius 1 2 2 (count stream) + 1 / count stream ≤
    |prefixMean (fun s => clip (sampleThreshold 1 2 2 s) (stream s 0 + 1/2))
      (count stream) - ∫ x, x ∂kernel 0|} ≤
      2 * (2 * Real.exp (-confidenceLog 2)) := by
  apply arm_corrupted_clipped_mean_tail kernel 0 count (fun _ _ => 1/2) 1 2 1 2
    (by norm_num) (by norm_num) (by norm_num)
  · exact integrable_law 0 _
  · exact moment 0
  · intro stream
    unfold count
    split <;> norm_num [Finset.sum_range_succ]

-- Nonzero corruption crosses the threshold, so clipping is active.
example : prefixMean (fun _ => clip 1 ((3/4 : ℝ) + 1/2)) 2 = 1 := by
  norm_num [prefixMean, clip, Finset.sum_range_succ]

#print axioms BanditRLProof.HeavyTail.arm_corrupted_clipped_mean_tail
#print axioms BanditRLProof.HeavyTail.observed_corrupted_clipped_mean_tail

end HeavyTailClippedCanary
