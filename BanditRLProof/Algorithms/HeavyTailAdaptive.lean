import BanditRLProof.HeavyTailArmLaw
import BanditRLProof.HeavyTailGapThreshold

/-! Actual causal observations and their adaptive-count confidence. -/
namespace BanditRLProof.HeavyTail
open MeasureTheory ProbabilityTheory
variable {K : ℕ}

noncomputable def robustMean (hK : 0 < K) (ε u : ℝ)
    (stream : UCB.ArmRewardStream K) (arm : Fin K) (t : ℕ) : ℝ :=
  sumRewards (robustAction hK ε u stream)
    (fun s => truncate (sampleThreshold ε u t (pullCount (robustAction hK ε u stream) arm s))
      (robustReward hK ε u stream s)) arm t /
    pullCount (robustAction hK ε u stream) arm t

theorem robustMean_latent (hK : 0 < K) (ε u : ℝ)
    (stream : UCB.ArmRewardStream K) (arm : Fin K) (t : ℕ) :
    robustMean hK ε u stream arm t =
      (∑ s ∈ Finset.range (pullCount (robustAction hK ε u stream) arm t),
        truncate (sampleThreshold ε u t s) (stream s arm)) /
      pullCount (robustAction hK ε u stream) arm t := by
  unfold robustMean robustReward robustAction ArmStreamPolicy.reward
  rw [truncated_observed_sum]
  rfl

theorem robust_pullCount_pos (hK : 0 < K) (ε u : ℝ)
    (stream : UCB.ArmRewardStream K) (arm : Fin K) (t : ℕ) (ht : K ≤ t) :
    0 < pullCount (robustAction hK ε u stream) arm t := by
  apply pullCount_pos_of_eq_before _ _ (arm.isLt.trans_le ht)
  rw [robustAction_initialization hK ε u stream arm.val arm.isLt]
  apply Fin.ext
  exact Nat.mod_eq_of_lt arm.isLt

theorem robustMean_history (hK : 0 < K) (ε u : ℝ)
    (stream : UCB.ArmRewardStream K) (arm : Fin K) (n : ℕ) :
    historyTruncatedMean (UCB.initializationArm hK 0) (sampleThreshold ε u (n+1)) n
      (ArmStreamPolicy.history (UCB.initializationArm hK 0) (nextArm hK ε u) stream n) arm =
      robustMean hK ε u stream arm (n+1) := by
  rw [historyTruncatedMean_latent, robustMean_latent]
  rfl

theorem robustIndex_history (hK : 0 < K) (ε u : ℝ)
    (stream : UCB.ArmRewardStream K) (arm : Fin K) (n : ℕ) :
    historyIndex (UCB.initializationArm hK 0) ε u n
      (ArmStreamPolicy.history (UCB.initializationArm hK 0) (nextArm hK ε u) stream n) arm =
      robustMean hK ε u stream arm (n+1) +
        confidenceRadius ε u (n+1) (pullCount (robustAction hK ε u stream) arm (n+1)) := by
  unfold historyIndex
  rw [robustMean_history, ArmStreamPolicy.history_eq_trace, history_count_trace]
  · rfl
  · exact le_rfl

theorem robustMean_tail (hK : 0 < K) (ν : Kernel (Fin K) ℝ) [IsMarkovKernel ν]
    (arm : Fin K) (ε u : ℝ) (t : ℕ) (ht : K ≤ t)
    (hε0 : 0 ≤ ε) (hε : ε ≤ 1) (hu0 : 0 < u)
    (hX : Integrable (fun x : ℝ => x) (ν arm))
    (hm : Integrable (fun x : ℝ => |x|^(1+ε)) (ν arm))
    (hu : (∫ x, |x|^(1+ε) ∂ν arm) ≤ u) :
    (UCB.armStreamMeasure ν).real {stream |
      confidenceRadius ε u t (pullCount (robustAction hK ε u stream) arm t) ≤
        |robustMean hK ε u stream arm t - ∫ x, x ∂ν arm|} ≤
      t * (2 * Real.exp (-confidenceLog t)) := by
  have h := arm_adaptive_mean_tail ν arm
    (fun stream => pullCount (robustAction hK ε u stream) arm t) ε u t hε0 hε hu0 hX hm hu
  refine (measureReal_mono ?_ (measure_ne_top _ _)).trans h
  intro stream hs
  refine ⟨robust_pullCount_pos hK ε u stream arm t ht, pullCount_le_time _ _ _, ?_⟩
  simpa only [robustMean_latent] using hs

theorem robust_selected_gap_le (hK : 0 < K) (ε u : ℝ)
    (stream : UCB.ArmRewardStream K) (mean : Fin K → ℝ) (best : Fin K)
    (n : ℕ) (hn : K ≤ n+1)
    (hbest : |robustMean hK ε u stream best (n+1) - mean best| ≤
      confidenceRadius ε u (n+1) (pullCount (robustAction hK ε u stream) best (n+1)))
    (hchosen : |robustMean hK ε u stream (robustAction hK ε u stream (n+1)) (n+1) -
        mean (robustAction hK ε u stream (n+1))| ≤ confidenceRadius ε u (n+1)
        (pullCount (robustAction hK ε u stream) (robustAction hK ε u stream (n+1)) (n+1))) :
    mean best - mean (robustAction hK ε u stream (n+1)) ≤
      2 * confidenceRadius ε u (n+1)
        (pullCount (robustAction hK ε u stream) (robustAction hK ε u stream (n+1)) (n+1)) := by
  have hs := robustAction_maximizes hK ε u stream n hn best
  dsimp only at hs
  simp_rw [robustIndex_history] at hs
  exact UCB.meanGap_le_two_radius_of_confidenceScore_max mean
    (fun a => robustMean hK ε u stream a (n+1))
    (fun a => confidenceRadius ε u (n+1) (pullCount (robustAction hK ε u stream) a (n+1)))
    best (robustAction hK ε u stream (n+1))
    (by have h := (abs_le.mp hbest).1; unfold UCB.confidenceScore; linarith)
    (by have h := (abs_le.mp hchosen).2; linarith) hs

theorem robust_selected_small_radius_tail (hK : 0 < K)
    (ν : Kernel (Fin K) ℝ) [IsMarkovKernel ν] (best arm : Fin K)
    (ε u : ℝ) (t : ℕ) (ht : K ≤ t)
    (hε0 : 0 ≤ ε) (hε : ε ≤ 1) (hu0 : 0 < u)
    (hX : ∀ a, Integrable (fun x : ℝ => x) (ν a))
    (hm : ∀ a, Integrable (fun x : ℝ => |x|^(1+ε)) (ν a))
    (hu : ∀ a, (∫ x, |x|^(1+ε) ∂ν a) ≤ u) :
    (UCB.armStreamMeasure ν).real {stream | robustAction hK ε u stream t = arm ∧
      2 * confidenceRadius ε u t (pullCount (robustAction hK ε u stream) arm t) <
        (∫ x, x ∂ν best) - ∫ x, x ∂ν arm} ≤ 4*t*Real.exp (-confidenceLog t) := by
  let bad := fun a => {stream | confidenceRadius ε u t
    (pullCount (robustAction hK ε u stream) a t) ≤
      |robustMean hK ε u stream a t - ∫ x, x ∂ν a|}
  have hs : {stream | robustAction hK ε u stream t = arm ∧
      2 * confidenceRadius ε u t (pullCount (robustAction hK ε u stream) arm t) <
        (∫ x, x ∂ν best) - ∫ x, x ∂ν arm} ⊆ bad best ∪ bad arm := by
    intro stream hstream
    rcases hstream with ⟨hselected, hgap⟩
    by_contra hbad
    have hgood := not_or.mp hbad
    simp only [bad, Set.mem_setOf_eq] at hgood
    have hb := (lt_of_not_ge hgood.1).le
    have ha := (lt_of_not_ge hgood.2).le
    cases t with
    | zero => omega
    | succ n =>
      have hc := robust_selected_gap_le hK ε u stream (fun a => ∫ x, x ∂ν a) best n ht hb
        (by simpa only [hselected] using ha)
      rw [hselected] at hc
      exact (not_lt_of_ge hc) hgap
  have hb := robustMean_tail hK ν best ε u t ht hε0 hε hu0 (hX best) (hm best) (hu best)
  have ha := robustMean_tail hK ν arm ε u t ht hε0 hε hu0 (hX arm) (hm arm) (hu arm)
  calc
    _ ≤ (UCB.armStreamMeasure ν).real (bad best ∪ bad arm) := measureReal_mono hs (measure_ne_top _ _)
    _ ≤ (UCB.armStreamMeasure ν).real (bad best) + (UCB.armStreamMeasure ν).real (bad arm) :=
      measureReal_union_le _ _
    _ ≤ 4*t*Real.exp (-confidenceLog t) := by dsimp [bad]; linarith

theorem robust_initial_count_zero (hK : 0 < K) (ε u : ℝ)
    (stream : UCB.ArmRewardStream K) (t : ℕ) (ht : t < K) :
    pullCount (robustAction hK ε u stream) (robustAction hK ε u stream t) t = 0 := by
  apply pullCount_eq_zero_of_forall_ne
  intro s hs heq
  rw [robustAction_initialization hK ε u stream s (hs.trans ht),
    robustAction_initialization hK ε u stream t ht] at heq
  have hv := congrArg Fin.val heq
  simp only [UCB.initializationArm, Nat.mod_eq_of_lt (hs.trans ht), Nat.mod_eq_of_lt ht] at hv
  omega

theorem robust_large_count_tail (hK : 0 < K)
    (ν : Kernel (Fin K) ℝ) [IsMarkovKernel ν] (best arm : Fin K)
    (ε u : ℝ) (T t : ℕ) (ht : t ≤ T)
    (hε0 : 0 < ε) (hε : ε ≤ 1) (hu0 : 0 < u)
    (hgap : 0 < (∫ x, x ∂ν best) - ∫ x, x ∂ν arm)
    (hX : ∀ a, Integrable (fun x : ℝ => x) (ν a))
    (hm : ∀ a, Integrable (fun x : ℝ => |x|^(1+ε)) (ν a))
    (hu : ∀ a, (∫ x, |x|^(1+ε) ∂ν a) ≤ u) :
    (UCB.armStreamMeasure ν).real {stream | robustAction hK ε u stream t = arm ∧
      gapThreshold ε u ((∫ x, x ∂ν best) - ∫ x, x ∂ν arm) T ≤
        pullCount (robustAction hK ε u stream) arm t} ≤ 4*t*Real.exp (-confidenceLog t) := by
  by_cases hinit : t < K
  · have he : {stream | robustAction hK ε u stream t = arm ∧
        gapThreshold ε u ((∫ x, x ∂ν best) - ∫ x, x ∂ν arm) T ≤
          pullCount (robustAction hK ε u stream) arm t} = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro stream hs
      rcases hs with ⟨hsel, hcount⟩
      have hz := robust_initial_count_zero hK ε u stream t hinit
      rw [hsel] at hz
      have hp := gapThreshold_pos ε u ((∫ x, x ∂ν best) - ∫ x, x ∂ν arm) T
      omega
    rw [he, measureReal_empty]
    positivity
  · refine (measureReal_mono ?_ (measure_ne_top _ _)).trans
      (robust_selected_small_radius_tail hK ν best arm ε u t (Nat.le_of_not_gt hinit)
        hε0.le hε hu0 hX hm hu)
    intro stream hs
    exact ⟨hs.1, twice_radius_lt_gap ε u _ hε0 hu0 hgap t T _ ht hs.2⟩

end BanditRLProof.HeavyTail
