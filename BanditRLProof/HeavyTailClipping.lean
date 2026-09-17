import BanditRLProof.HeavyTailTruncation
import Mathlib.Topology.MetricSpace.Lipschitz

/-! Reserved transfer: winsorized estimators under an L1 corruption budget.
The budget is on the consumed prefix. No corruption-robust regret claim. -/
namespace BanditRLProof.HeavyTail

noncomputable def clip (B x : ℝ) : ℝ := max (-B) (min B x)

theorem abs_clip_sub_clip_le (B x y : ℝ) : |clip B x - clip B y| ≤ |x - y| := by
  have h : LipschitzWith 1 (clip B) :=
    (LipschitzWith.id.const_min B).const_max (-B)
  simpa only [Real.dist_eq, NNReal.coe_one, one_mul] using h.dist_le_mul x y

/-- Unlike hard truncation, clipping is stable even when corruption crosses B. -/
theorem clip_corruption_le (B x c : ℝ) : |clip B (x + c) - clip B x| ≤ |c| := by
  simpa using abs_clip_sub_clip_le B (x + c) x

noncomputable def prefixMean (X : ℕ → ℝ) (n : ℕ) : ℝ :=
  (∑ s ∈ Finset.range n, X s) / n

/-- The finite-prefix corruption producer allows index-dependent clipping. -/
theorem clipped_prefix_corruption_le (X c B : ℕ → ℝ) (n : ℕ) (C : ℝ)
    (hC : (∑ s ∈ Finset.range n, |c s|) ≤ C) :
    |prefixMean (fun s => clip (B s) (X s + c s)) n -
      prefixMean (fun s => clip (B s) (X s)) n| ≤ C / n := by
  unfold prefixMean
  rw [← sub_div, ← Finset.sum_sub_distrib, abs_div]
  simp only [Nat.abs_cast]
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg n)
  calc
    |∑ s ∈ Finset.range n, (clip (B s) (X s + c s) - clip (B s) (X s))| ≤
        ∑ s ∈ Finset.range n, |clip (B s) (X s + c s) - clip (B s) (X s)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ s ∈ Finset.range n, |c s| := Finset.sum_le_sum fun s _ =>
      clip_corruption_le (B s) (X s) (c s)
    _ ≤ C := hC

/-- Actual adaptively consumed clipped observations retain the same prefix.
The corruption stream can be arbitrary; this is a pathwise statement. -/
theorem clipped_observed_prefix {Ω : Type*} {K : ℕ}
    (action : Ω → ActionTrace (Fin K)) (stream corruption : Ω → UCB.ArmRewardStream K)
    (B : ℕ → Fin K → ℝ) (ω : Ω) (arm : Fin K) (t : ℕ) :
    sumRewards (action ω)
      (fun s => clip (B (pullCount (action ω) (action ω s) s) (action ω s))
        (UCB.rewardFromArmStream action
          (fun ω j a => stream ω j a + corruption ω j a) ω s)) arm t =
      ∑ j ∈ Finset.range (pullCount (action ω) arm t),
        clip (B j arm) (stream ω j arm + corruption ω j arm) :=
  transformed_observed_prefix action
    (fun ω j a => stream ω j a + corruption ω j a)
    (fun j a x => clip (B j a) x) ω arm t

/-- Combine the new corruption producer with the common error assembly.
Bias and fluctuation are still supplied; no concentration is asserted here. -/
theorem corrupted_clipped_estimator_error_le (X c B : ℕ → ℝ) (n : ℕ)
    (C center mean bias fluctuation : ℝ)
    (hC : (∑ s ∈ Finset.range n, |c s|) ≤ C)
    (hb : |center - mean| ≤ bias)
    (hf : |prefixMean (fun s => clip (B s) (X s)) n - center| ≤ fluctuation) :
    |prefixMean (fun s => clip (B s) (X s + c s)) n - mean| ≤
      bias + fluctuation + C / n := by
  have hclean := estimator_error_le _ _ _ _ _ hb hf
  have hperturb := clipped_prefix_corruption_le X c B n C hC
  have h := estimator_error_le _ _ _ _ _ hclean hperturb
  exact h

/-- Full pathwise transfer to the actually observed estimator. Both reward
streams are compared along the SAME action trace; this does not compare two
policies whose actions changed in response to the corruption. -/
theorem actual_clipped_corruption_le {Ω : Type*} {K : ℕ}
    (action : Ω → ActionTrace (Fin K)) (stream corruption : Ω → UCB.ArmRewardStream K)
    (B : ℕ → Fin K → ℝ) (ω : Ω) (arm : Fin K) (t : ℕ) (C : ℝ)
    (hC : (∑ j ∈ Finset.range (pullCount (action ω) arm t), |corruption ω j arm|) ≤ C) :
    |sumRewards (action ω)
      (fun s => clip (B (pullCount (action ω) (action ω s) s) (action ω s))
        (UCB.rewardFromArmStream action
          (fun ω j a => stream ω j a + corruption ω j a) ω s)) arm t /
        pullCount (action ω) arm t -
     sumRewards (action ω)
      (fun s => clip (B (pullCount (action ω) (action ω s) s) (action ω s))
        (UCB.rewardFromArmStream action stream ω s)) arm t /
        pullCount (action ω) arm t| ≤ C / pullCount (action ω) arm t := by
  rw [clipped_observed_prefix action stream corruption B ω arm t,
    transformed_observed_prefix action stream (fun j a x => clip (B j a) x) ω arm t]
  exact clipped_prefix_corruption_le (fun j => stream ω j arm)
    (fun j => corruption ω j arm) (fun j => B j arm) (pullCount (action ω) arm t) C hC

/-- A concrete discontinuity diagnostic: hard truncation cannot use the same
unit-Lipschitz corruption producer. -/
theorem truncate_not_unit_lipschitz :
    ¬ (∀ x y : ℝ, |truncate 1 x - truncate 1 y| ≤ |x - y|) := by
  intro h
  have hh := h 1 (3 / 2)
  norm_num [truncate] at hh

end BanditRLProof.HeavyTail
