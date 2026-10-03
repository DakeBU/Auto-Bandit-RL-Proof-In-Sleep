import BanditRLProof.HeavyTailSourceSchedule
import BanditRLProof.HeavyTailArmLaw

/-! Source-parameter robust UCB: round-robin initialization is a tie convention
for unpulled arms; later choices maximize the source radius-four index using
only the observed history. Paper round is zero-based decision time plus one. -/
namespace BanditRLProof.HeavyTail.SourcePolicy
open MeasureTheory ProbabilityTheory
variable {K : ℕ}

noncomputable def sampleThreshold (ε u : ℝ) (t s : ℕ) : ℝ :=
  sourceTruncationThreshold ε u (sourceConfidenceLog t) s

noncomputable def historyIndex (initial : Fin K) (ε u : ℝ) (n : ℕ)
    (h : History.FinitePairHistory (Fin K) ℝ n) (arm : Fin K) : ℝ :=
  historyTruncatedMean initial (sampleThreshold ε u (n+1)) n h arm +
    sourceConfidenceRadius ε u (n+1) (pullCount (historyAction initial n h) arm (n+1))

noncomputable def nextArm (hK : 0 < K) (ε u : ℝ) (n : ℕ)
    (h : History.FinitePairHistory (Fin K) ℝ n) : Fin K :=
  if n+1 < K then UCB.initializationArm hK (n+1) else
    ETC.realLeastEncodedArgmax hK (historyIndex (UCB.initializationArm hK 0) ε u n h)

theorem measurable_historyIndex (initial : Fin K) (ε u : ℝ) (n : ℕ) (arm : Fin K) :
    Measurable (fun h => historyIndex initial ε u n h arm) := by
  exact (measurable_historyTruncatedMean initial _ n arm).add
    ((measurable_of_countable (sourceConfidenceRadius ε u (n+1))).comp
      (measurable_pullCount (historyAction initial n) (measurable_historyAction initial n)
        arm (n+1)))

theorem measurable_nextArm (hK : 0 < K) (ε u : ℝ) (n : ℕ) :
    Measurable (nextArm hK ε u n) := by
  change Measurable (fun h => nextArm hK ε u n h)
  by_cases hn : n+1 < K
  · simp only [nextArm, if_pos hn]
    exact measurable_const
  · simp only [nextArm, if_neg hn, ETC.realLeastEncodedArgmax_eq_realArgmaxCommit]
    apply ETC.measurable_realArgmaxCommit_of_forall_measurable
    exact measurable_historyIndex _ ε u n

noncomputable def robustAction (hK : 0 < K) (ε u : ℝ) :=
  ArmStreamPolicy.action (UCB.initializationArm hK 0) (nextArm hK ε u)

noncomputable def robustReward (hK : 0 < K) (ε u : ℝ) :=
  ArmStreamPolicy.reward (UCB.initializationArm hK 0) (nextArm hK ε u)

theorem measurable_robustAction (hK : 0 < K) (ε u : ℝ) (t : ℕ) :
    Measurable (fun stream => robustAction hK ε u stream t) := by
  exact ArmStreamPolicy.measurable_action _ _ (measurable_nextArm hK ε u) t

theorem robustAction_initialization (hK : 0 < K) (ε u : ℝ)
    (stream : UCB.ArmRewardStream K) (t : ℕ) (ht : t < K) :
    robustAction hK ε u stream t = UCB.initializationArm hK t := by
  cases t with
  | zero => rfl
  | succ t => simp [robustAction, ArmStreamPolicy.action_succ, nextArm, ht]

/-- The selected index is maximal on the actual observed history. -/
theorem robustAction_maximizes (hK : 0 < K) (ε u : ℝ)
    (stream : UCB.ArmRewardStream K) (n : ℕ) (hn : K ≤ n+1) (arm : Fin K) :
    let h := ArmStreamPolicy.history (UCB.initializationArm hK 0) (nextArm hK ε u) stream n
    historyIndex (UCB.initializationArm hK 0) ε u n h arm ≤
      historyIndex (UCB.initializationArm hK 0) ε u n h (robustAction hK ε u stream (n+1)) := by
  dsimp only
  simp only [robustAction, ArmStreamPolicy.action_succ, nextArm, if_neg (not_lt.mpr hn)]
  exact ETC.realLeastEncodedArgmax_spec hK _ arm

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
        sourceConfidenceRadius ε u (n+1) (pullCount (robustAction hK ε u stream) arm (n+1)) := by
  unfold historyIndex
  rw [robustMean_history, ArmStreamPolicy.history_eq_trace, history_count_trace]
  · rfl
  · exact le_rfl


theorem arm_adaptive_upper_tail (ν : Kernel (Fin K) ℝ) [IsMarkovKernel ν]
    (arm : Fin K) (count : UCB.ArmRewardStream K → ℕ) (ε u : ℝ) (t : ℕ)
    (hε0 : 0 ≤ ε) (hε : ε ≤ 1) (hu0 : 0 < u)
    (hX : Integrable (fun x : ℝ => x) (ν arm))
    (hm : Integrable (fun x : ℝ => |x|^(1+ε)) (ν arm))
    (hu : (∫ x, |x|^(1+ε) ∂ν arm) ≤ u) :
    (UCB.armStreamMeasure ν).real {stream | 0 < count stream ∧ count stream ≤ t ∧
      sourceConfidenceRadius ε u t (count stream) ≤
        (∑ s ∈ Finset.range (count stream), truncate (sampleThreshold ε u t s) (stream s arm)) / count stream - ∫ x, x ∂ν arm} ≤ t*Real.exp (-(5/4 : ℝ)*sourceConfidenceLog t) := by
  apply source_adaptive_mean_upper_tail (UCB.armStreamMeasure ν) (fun s stream => stream s arm)
    count ε u (∫ x, x ∂ν arm) t
    (fun i => (measurable_pi_apply arm).comp (measurable_pi_apply i))
  · simpa only [sub_zero] using UCB.iIndepFun_armStreamMeasure_coord_sub ν arm 0
  · exact hε0
  · exact hε
  · exact hu0
  · exact fun i => arm_coordinate_integrable ν arm i _ hX
  · exact fun i => arm_coordinate_integral ν arm i _ measurable_id
  · exact fun i => arm_coordinate_integrable ν arm i _ hm
  · intro i
    rw [arm_coordinate_integral ν arm i (fun x : ℝ => |x|^(1+ε)) (by fun_prop)]
    exact hu

theorem robustMean_upper_tail (hK : 0 < K) (ν : Kernel (Fin K) ℝ) [IsMarkovKernel ν]
    (arm : Fin K) (ε u : ℝ) (t : ℕ) (ht : K ≤ t)
    (hε0 : 0 ≤ ε) (hε : ε ≤ 1) (hu0 : 0 < u)
    (hX : Integrable (fun x : ℝ => x) (ν arm))
    (hm : Integrable (fun x : ℝ => |x|^(1+ε)) (ν arm))
    (hu : (∫ x, |x|^(1+ε) ∂ν arm) ≤ u) :
    (UCB.armStreamMeasure ν).real {stream |
      sourceConfidenceRadius ε u t (pullCount (robustAction hK ε u stream) arm t) ≤
        robustMean hK ε u stream arm t - ∫ x, x ∂ν arm} ≤ t*Real.exp (-(5/4 : ℝ)*sourceConfidenceLog t) := by
  have h := arm_adaptive_upper_tail ν arm
    (fun stream => pullCount (robustAction hK ε u stream) arm t) ε u t hε0 hε hu0 hX hm hu
  refine (measureReal_mono ?_ (measure_ne_top _ _)).trans h
  intro stream hs
  refine ⟨robust_pullCount_pos hK ε u stream arm t ht, pullCount_le_time _ _ _, ?_⟩
  simpa only [robustMean_latent] using hs


theorem arm_adaptive_lower_tail (ν : Kernel (Fin K) ℝ) [IsMarkovKernel ν]
    (arm : Fin K) (count : UCB.ArmRewardStream K → ℕ) (ε u : ℝ) (t : ℕ)
    (hε0 : 0 ≤ ε) (hε : ε ≤ 1) (hu0 : 0 < u)
    (hX : Integrable (fun x : ℝ => x) (ν arm))
    (hm : Integrable (fun x : ℝ => |x|^(1+ε)) (ν arm))
    (hu : (∫ x, |x|^(1+ε) ∂ν arm) ≤ u) :
    (UCB.armStreamMeasure ν).real {stream | 0 < count stream ∧ count stream ≤ t ∧
      sourceConfidenceRadius ε u t (count stream) ≤
        (∫ x, x ∂ν arm) - (∑ s ∈ Finset.range (count stream), truncate (sampleThreshold ε u t s) (stream s arm)) / count stream} ≤ t*Real.exp (-(5/4 : ℝ)*sourceConfidenceLog t) := by
  apply source_adaptive_mean_lower_tail (UCB.armStreamMeasure ν) (fun s stream => stream s arm)
    count ε u (∫ x, x ∂ν arm) t
    (fun i => (measurable_pi_apply arm).comp (measurable_pi_apply i))
  · simpa only [sub_zero] using UCB.iIndepFun_armStreamMeasure_coord_sub ν arm 0
  · exact hε0
  · exact hε
  · exact hu0
  · exact fun i => arm_coordinate_integrable ν arm i _ hX
  · exact fun i => arm_coordinate_integral ν arm i _ measurable_id
  · exact fun i => arm_coordinate_integrable ν arm i _ hm
  · intro i
    rw [arm_coordinate_integral ν arm i (fun x : ℝ => |x|^(1+ε)) (by fun_prop)]
    exact hu

theorem robustMean_lower_tail (hK : 0 < K) (ν : Kernel (Fin K) ℝ) [IsMarkovKernel ν]
    (arm : Fin K) (ε u : ℝ) (t : ℕ) (ht : K ≤ t)
    (hε0 : 0 ≤ ε) (hε : ε ≤ 1) (hu0 : 0 < u)
    (hX : Integrable (fun x : ℝ => x) (ν arm))
    (hm : Integrable (fun x : ℝ => |x|^(1+ε)) (ν arm))
    (hu : (∫ x, |x|^(1+ε) ∂ν arm) ≤ u) :
    (UCB.armStreamMeasure ν).real {stream |
      sourceConfidenceRadius ε u t (pullCount (robustAction hK ε u stream) arm t) ≤
        (∫ x, x ∂ν arm) - robustMean hK ε u stream arm t} ≤ t*Real.exp (-(5/4 : ℝ)*sourceConfidenceLog t) := by
  have h := arm_adaptive_lower_tail ν arm
    (fun stream => pullCount (robustAction hK ε u stream) arm t) ε u t hε0 hε hu0 hX hm hu
  refine (measureReal_mono ?_ (measure_ne_top _ _)).trans h
  intro stream hs
  refine ⟨robust_pullCount_pos hK ε u stream arm t ht, pullCount_le_time _ _ _, ?_⟩
  simpa only [robustMean_latent] using hs

/-- Finite time budget for one signed event of the actual source-parameter policy. -/
theorem robustMean_upper_tail_sum (hK : 0 < K) (ν : Kernel (Fin K) ℝ) [IsMarkovKernel ν]
    (arm : Fin K) (ε u : ℝ) (T : ℕ)
    (hε0 : 0 ≤ ε) (hε : ε ≤ 1) (hu0 : 0 < u)
    (hX : Integrable (fun x : ℝ => x) (ν arm))
    (hm : Integrable (fun x : ℝ => |x|^(1+ε)) (ν arm))
    (hu : (∫ x, |x|^(1+ε) ∂ν arm) ≤ u) :
    (∑ t ∈ Finset.range T, (UCB.armStreamMeasure ν).real {stream | K ≤ t ∧
      sourceConfidenceRadius ε u t (pullCount (robustAction hK ε u stream) arm t) ≤
        robustMean hK ε u stream arm t - ∫ x, x ∂ν arm}) ≤ 2 := by
  apply le_trans (Finset.sum_le_sum fun t _ => ?_) (source_schedule_tail_sum_le_two T)
  by_cases ht : K ≤ t
  · simpa only [ht, true_and] using
      robustMean_upper_tail hK ν arm ε u t ht hε0 hε hu0 hX hm hu
  · simp only [ht, false_and, Set.setOf_false, measureReal_empty]
    positivity

/-- Finite time budget for one signed event of the actual source-parameter policy. -/
theorem robustMean_lower_tail_sum (hK : 0 < K) (ν : Kernel (Fin K) ℝ) [IsMarkovKernel ν]
    (arm : Fin K) (ε u : ℝ) (T : ℕ)
    (hε0 : 0 ≤ ε) (hε : ε ≤ 1) (hu0 : 0 < u)
    (hX : Integrable (fun x : ℝ => x) (ν arm))
    (hm : Integrable (fun x : ℝ => |x|^(1+ε)) (ν arm))
    (hu : (∫ x, |x|^(1+ε) ∂ν arm) ≤ u) :
    (∑ t ∈ Finset.range T, (UCB.armStreamMeasure ν).real {stream | K ≤ t ∧
      sourceConfidenceRadius ε u t (pullCount (robustAction hK ε u stream) arm t) ≤
        (∫ x, x ∂ν arm) - robustMean hK ε u stream arm t}) ≤ 2 := by
  apply le_trans (Finset.sum_le_sum fun t _ => ?_) (source_schedule_tail_sum_le_two T)
  by_cases ht : K ≤ t
  · simpa only [ht, true_and] using
      robustMean_lower_tail hK ν arm ε u t ht hε0 hε hu0 hX hm hu
  · simp only [ht, false_and, Set.setOf_false, measureReal_empty]
    positivity

end BanditRLProof.HeavyTail.SourcePolicy
