import BanditRLProof

open BanditRLProof BanditRLProof.HeavyTail

-- Nonzero raw-tail example and a corruption crossing the clipping threshold.
example : |(3 : ℝ) - truncate 2 3| ≤ |(3 : ℝ)| ^ (1 + (1/2 : ℝ)) / 2 ^ (1/2 : ℝ) :=
  abs_sub_truncate_le 2 3 (1/2) (by norm_num) (by norm_num)

example : |clip 1 (3/4 + 1/2) - clip 1 (3/4)| ≤ (1/2 : ℝ) := by
  simpa using clip_corruption_le 1 (3/4) (1/2)

-- Nontrivial two-sample corruption budget, rather than an empty-prefix witness.
example : |prefixMean (fun s => clip 1 ((if s = 0 then 3/4 else -2) + 1/2)) 2 -
    prefixMean (fun s => clip 1 (if s = 0 then 3/4 else -2)) 2| ≤ (1/2 : ℝ) := by
  simpa using clipped_prefix_corruption_le
    (fun s => if s = 0 then 3/4 else -2) (fun _ => 1/2) (fun _ => 1) 2 1
    (by norm_num [Finset.sum_range_succ])

example {Ω : Type*} {K : ℕ} (a : Ω → ActionTrace (Fin K))
    (x : Ω → UCB.ArmRewardStream K) (B : ℕ → ℝ) (ω : Ω) (i : Fin K) (t : ℕ) :
    sumRewards (a ω) (fun s => truncate (B (pullCount (a ω) (a ω s) s))
      (UCB.rewardFromArmStream a x ω s)) i t =
    ∑ j ∈ Finset.range (pullCount (a ω) i t), truncate (B j) (x ω j i) :=
  transformed_observed_prefix a x (fun j _ y => truncate (B j) y) ω i t

#print axioms BanditRLProof.HeavyTail.integral_truncate_bias_le
#print axioms BanditRLProof.HeavyTail.integral_sq_truncate_le
#print axioms BanditRLProof.HeavyTail.transformed_observed_prefix
#print axioms BanditRLProof.HeavyTail.corrupted_clipped_estimator_error_le
#print axioms BanditRLProof.HeavyTail.actual_clipped_corruption_le
#print axioms BanditRLProof.HeavyTail.truncated_centered_mgf
#print axioms BanditRLProof.HeavyTail.truncated_sum_tail
#print axioms BanditRLProof.HeavyTail.truncate_not_unit_lipschitz
