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

-- A longer random prefix keeps the conservative confidence radius useful.
-- The count is outcome-dependent and every consumed reward is corrupted.
noncomputable def longCount (stream : UCB.ArmRewardStream 2) : ℕ :=
  if stream 0 0 > 0 then 10000 else 9999

theorem long_corrupted_prefix :
    (UCB.armStreamMeasure kernel).real {stream |
      0 < longCount stream ∧ longCount stream ≤ 10000 ∧
      confidenceRadius 1 2 10000 (longCount stream) + 1 / longCount stream ≤
      |prefixMean (fun s => clip (sampleThreshold 1 2 10000 s)
          (stream s 0 + 1/20000)) (longCount stream) - ∫ x, x ∂kernel 0|} ≤
      10000 * (2 * Real.exp (-confidenceLog 10000)) := by
  apply arm_corrupted_clipped_mean_tail kernel 0 longCount
    (fun _ _ => 1/20000) 1 2 1 10000
    (by norm_num) (by norm_num) (by norm_num)
  · exact integrable_law 0 _
  · exact moment 0
  · intro stream
    unfold longCount
    split <;> simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      <;> norm_num

#print axioms long_corrupted_prefix

#print axioms BanditRLProof.HeavyTail.arm_corrupted_clipped_mean_tail
#print axioms BanditRLProof.HeavyTail.observed_corrupted_clipped_mean_tail

end HeavyTailClippedCanary
