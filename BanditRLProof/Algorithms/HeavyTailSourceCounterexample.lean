import BanditRLProof.Algorithms.HeavyTailSourceRegret
import BanditRLProof.PullCountDecomposition

/-! Finite counterexample to the literal BCL13 printed regret coefficient for
the unchanged radius-four policy. Deterministic arms0,-1, raw second moment<=1,
horizon2^50. The corrected upper bound remains a separate theorem. -/

set_option autoImplicit false

namespace BanditRLProof.HeavyTail.SourceCounterexample
open MeasureTheory ProbabilityTheory

noncomputable def dropped (L : ℝ) (n : ℕ) : ℕ := min n (Nat.ceil L - 1)

theorem truncate_neg_one (L : ℝ) (hL : 0 < L) (s : ℕ) :
    truncate (sourceTruncationThreshold 1 1 L s) (-1) =
      if (s : ℝ)+1 < L then 0 else -1 := by
  have hroot : (1 : ℝ) ≤ sourceTruncationThreshold 1 1 L s ↔ L ≤ (s : ℝ)+1 := by
    unfold sourceTruncationThreshold
    norm_num only [one_mul, show (1 / (1+(1 : ℝ))) = 1/2 by norm_num]
    rw [← Real.sqrt_eq_rpow, Real.one_le_sqrt, le_div_iff₀ hL, one_mul]
  unfold truncate
  norm_num only [abs_neg, abs_one]
  simp only [hroot]
  by_cases h : (s : ℝ)+1 < L
  · simp [h, not_le.mpr h]
  · simp [h, le_of_not_gt h]

theorem dropped_filter (L : ℝ) (n : ℕ) :
    (Finset.range n).filter (fun s : ℕ => (s : ℝ)+1 < L) = Finset.range (dropped L n) := by
  ext s
  have h : (s : ℝ)+1 < L ↔ s+1 < Nat.ceil L := by
    simpa only [Nat.cast_add, Nat.cast_one] using (Nat.lt_ceil (a := L) (n := s+1)).symm
  simp only [Finset.mem_filter, Finset.mem_range, h, dropped, lt_min_iff]
  omega

theorem sum_truncate_neg_one (L : ℝ) (hL : 0 < L) (n : ℕ) :
    (∑ s ∈ Finset.range n, truncate (sourceTruncationThreshold 1 1 L s) (-1)) =
      -(n : ℝ) + dropped L n := by
  simp_rw [truncate_neg_one L hL]
  have ht : ∀ s : ℕ, (if (s : ℝ)+1 < L then (0 : ℝ) else -1) =
      -1 + if (s : ℝ)+1 < L then 1 else 0 := by
    intro s
    split <;> norm_num
  simp_rw [ht]
  rw [Finset.sum_add_distrib]
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_neg, mul_one]
  rw [← Finset.sum_filter]
  simp only [Finset.sum_const, nsmul_one, dropped_filter, Finset.card_range]

theorem dropped_ge (L : ℝ) (hL : 0 < L) (n : ℕ) (hn : L ≤ n) :
    L-1 ≤ (dropped L n : ℝ) := by
  have hc : 1 ≤ Nat.ceil L := Nat.one_le_ceil_iff.mpr hL
  have hcn : Nat.ceil L ≤ n := Nat.ceil_le.mpr hn
  rw [dropped, min_eq_right (by omega), Nat.cast_sub hc]
  simpa only [Nat.cast_one] using sub_le_sub_right (Nat.le_ceil L) 1



theorem suboptimal_index_gt (H L n d : ℝ)
    (hH : 30 < H) (hL : 2*H-2 ≤ L) (hn : 0 < n)
    (hnM : n ≤ 32*H+5) (hd : L-1 ≤ d) :
    (1/100 : ℝ) < -1+d/n+4*Real.sqrt (L/n) := by
  have hfrac : (1/17 : ℝ) < (L-1)/n := by
    apply (lt_div_iff₀ hn).mpr
    linarith
  have hdfrac : (1/17 : ℝ) < d/n :=
    hfrac.trans_le (div_le_div_of_nonneg_right hd hn.le)
  have hLpos : 0 < L := by linarith
  have hfrac2 : (6/25 : ℝ)^2 < L/n := by
    apply (lt_div_iff₀ hn).mpr
    nlinarith
  have hroot : (6/25 : ℝ) < Real.sqrt (L/n) := by
    have hs := Real.sq_sqrt (div_pos hLpos hn).le
    have hp := Real.sqrt_nonneg (L/n)
    nlinarith
  linarith

theorem optimal_index_lt (H L m : ℝ) (hH : 0 < H)
    (hL0 : 0 ≤ L) (hL : L ≤ 2*H) (hm : 320000*H < m) :
    4*Real.sqrt (L/m) < (1/100 : ℝ) := by
  have hm0 : 0 < m := by linarith
  have hf : L/m < (1/160000 : ℝ) := by
    apply (div_lt_iff₀ hm0).mpr
    linarith
  have hs := Real.sq_sqrt (div_nonneg hL0 hm0.le)
  have hp := Real.sqrt_nonneg (L/m)
  nlinarith

noncomputable def deterministicStream : UCB.ArmRewardStream 2 :=
  fun _ a => if a = 0 then 0 else -1

noncomputable def trace : ActionTrace (Fin 2) :=
  SourcePolicy.robustAction (by decide) 1 1 deterministicStream

theorem mean_zero (t : ℕ) :
    SourcePolicy.robustMean (by decide) 1 1 deterministicStream 0 t = 0 := by
  rw [SourcePolicy.robustMean_latent]
  simp [deterministicStream, truncate]

theorem mean_one (t : ℕ) (ht : 2 ≤ t) :
    SourcePolicy.robustMean (by decide) 1 1 deterministicStream 1 t =
      -1 + dropped (sourceConfidenceLog t) (pullCount trace 1 t) / pullCount trace 1 t := by
  have hn := SourcePolicy.robust_pullCount_pos (by decide : 0 < 2) 1 1
    deterministicStream 1 t ht
  rw [SourcePolicy.robustMean_latent]
  change (∑ s ∈ Finset.range (pullCount trace 1 t),
    truncate (sourceTruncationThreshold 1 1 (sourceConfidenceLog t) s) (-1)) /
      pullCount trace 1 t = _
  rw [sum_truncate_neg_one _ (sourceConfidenceLog_pos t (by omega)), add_div, neg_div,
    div_self (by exact_mod_cast (Nat.ne_of_gt hn))]

theorem radius_sqrt (t n : ℕ) :
    sourceConfidenceRadius 1 1 t n = 4 * Real.sqrt (sourceConfidenceLog t/n) := by
  norm_num [sourceConfidenceRadius, Real.sqrt_eq_rpow]

theorem source_index_sub_gt (H : ℝ) (t : ℕ) (ht : 2 ≤ t)
    (hH : 30 < H) (hL : 2*H-2 ≤ sourceConfidenceLog t)
    (hnM : (pullCount trace 1 t : ℝ) ≤ 32*H+5) :
    (1/100 : ℝ) < SourcePolicy.robustMean (by decide) 1 1 deterministicStream 1 t +
      sourceConfidenceRadius 1 1 t (pullCount trace 1 t) := by
  have hn := SourcePolicy.robust_pullCount_pos (by decide : 0 < 2) 1 1
    deterministicStream 1 t ht
  have hn0 : (0 : ℝ) < pullCount trace 1 t := by exact_mod_cast hn
  rw [mean_one t ht, radius_sqrt]
  by_cases hsmall : (pullCount trace 1 t : ℝ) < sourceConfidenceLog t
  · have hceil : pullCount trace 1 t < Nat.ceil (sourceConfidenceLog t) := Nat.lt_ceil.mpr hsmall
    have hd : dropped (sourceConfidenceLog t) (pullCount trace 1 t) = pullCount trace 1 t := by
      exact min_eq_left (by omega)
    rw [hd, div_self hn0.ne']
    have hratio : 1 < sourceConfidenceLog t / pullCount trace 1 t :=
      (lt_div_iff₀ hn0).mpr (by simpa using hsmall)
    have hs := Real.sq_sqrt (show 0 ≤ sourceConfidenceLog t / pullCount trace 1 t by linarith)
    have hp := Real.sqrt_nonneg (sourceConfidenceLog t / pullCount trace 1 t)
    nlinarith
  · exact suboptimal_index_gt H _ _ _ hH hL hn0 hnM
      (dropped_ge _ (sourceConfidenceLog_pos t (by omega)) _ (le_of_not_gt hsmall))

theorem source_index_best_lt (H : ℝ) (t : ℕ) (ht : 2 ≤ t) (hH : 0 < H)
    (hL : sourceConfidenceLog t ≤ 2*H)
    (hm : 320000*H < (pullCount trace 0 t : ℝ)) :
    SourcePolicy.robustMean (by decide) 1 1 deterministicStream 0 t +
      sourceConfidenceRadius 1 1 t (pullCount trace 0 t) < (1/100 : ℝ) := by
  rw [mean_zero, zero_add, radius_sqrt]
  exact optimal_index_lt H _ _ hH (sourceConfidenceLog_pos t (by omega)).le hL hm


theorem forced_suboptimal (H : ℝ) (t : ℕ) (ht : 2 ≤ t)
    (hH : 30 < H) (hLlo : 2*H-2 ≤ sourceConfidenceLog t)
    (hLhi : sourceConfidenceLog t ≤ 2*H)
    (hnM : (pullCount trace 1 t : ℝ) ≤ 32*H+5)
    (hm : 320000*H < (pullCount trace 0 t : ℝ)) : trace t = 1 := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : t ≠ 0)
  have hmax := SourcePolicy.robustAction_maximizes (by decide : 0 < 2) 1 1
    deterministicStream n (by omega) 1
  simp only [SourcePolicy.robustIndex_history] at hmax
  have hbad := source_index_sub_gt H (n+1) ht hH hLlo hnM
  have hgood := source_index_best_lt H (n+1) ht (by linarith) hLhi hm
  have hcases : trace (n+1) = 0 ∨ trace (n+1) = 1 := by
    have h := (trace (n+1)).isLt
    have hv : (trace (n+1)).val = 0 ∨ (trace (n+1)).val = 1 := by omega
    rcases hv with h | h
    · left; exact Fin.ext h
    · right; exact Fin.ext h
  rcases hcases with hzero | hone
  · change SourcePolicy.robustMean (by decide) 1 1 deterministicStream 1 (n+1) +
        sourceConfidenceRadius 1 1 (n+1) (pullCount trace 1 (n+1)) ≤ SourcePolicy.robustMean (by decide) 1 1 deterministicStream (trace (n+1)) (n+1) +
        sourceConfidenceRadius 1 1 (n+1) (pullCount trace (trace (n+1)) (n+1)) at hmax
    rw [hzero] at hmax
    linarith
  · exact hone

def horizon : ℕ := 2^50
noncomputable def horizonHeight : ℝ := Real.log (horizon : ℝ)

theorem log_two_bounds : (3/5 : ℝ) < Real.log 2 ∧ Real.log 2 < 1 := by
  have h1 := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 4/3)
  have h2 := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 5/4)
  have h3 := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 6/5)
  have he : Real.log (4/3 : ℝ) + Real.log (5/4 : ℝ) + Real.log (6/5 : ℝ) = Real.log 2 := by
    rw [← Real.log_mul (by norm_num) (by norm_num), ← Real.log_mul (by norm_num) (by norm_num)]
    norm_num
  constructor
  · norm_num at h1 h2 h3
    linarith
  · have h := Real.log_lt_sub_one_of_pos (by norm_num : (0 : ℝ) < 2) (by norm_num)
    linarith

theorem height_bounds : (30 : ℝ) < horizonHeight ∧ horizonHeight < 50 := by
  have he : horizonHeight = 50 * Real.log 2 := by
    unfold horizonHeight horizon
    rw [Nat.cast_pow, Nat.cast_ofNat, Real.log_pow]
    norm_num
  rw [he]
  constructor <;> linarith [log_two_bounds.1, log_two_bounds.2]

theorem late_log_bounds (t : ℕ) (htlo : horizon/2 ≤ t) (hthi : t < horizon) :
    2*horizonHeight-2 ≤ sourceConfidenceLog t ∧ sourceConfidenceLog t ≤ 2*horizonHeight := by
  have hnum : (horizon : ℝ)/2 ≤ (t : ℝ)+1 := by
    have h : (horizon/2 : ℕ) ≤ t := htlo
    norm_num [horizon] at h ⊢
    exact_mod_cast (by omega : 562949953421312 ≤ t+1)
  have hlo := Real.log_le_log (by norm_num [horizon] : (0 : ℝ) < (horizon : ℝ)/2) hnum
  rw [Real.log_div (by norm_num [horizon]) (by norm_num)] at hlo
  have hnumhi : (t : ℝ)+1 ≤ (horizon : ℝ) := by exact_mod_cast (show t+1 ≤ horizon by omega)
  have hhi := Real.log_le_log (by positivity : (0 : ℝ) < (t : ℝ)+1) hnumhi
  unfold sourceConfidenceLog horizonHeight
  constructor <;> linarith [log_two_bounds.2]

theorem late_best_count (t : ℕ) (ht : horizon/2 ≤ t) (hthi : t ≤ horizon)
    (hcount : (pullCount trace 1 horizon : ℝ) ≤ 32*horizonHeight+5) :
    320000*horizonHeight < (pullCount trace 0 t : ℝ) := by
  have hmono : (pullCount trace 1 t : ℝ) ≤ pullCount trace 1 horizon := by
    exact_mod_cast (pullCount_mono trace 1 hthi)
  have hsum : pullCount trace 0 t + pullCount trace 1 t = t := by
    simpa only [Fin.sum_univ_two] using finset_sum_pullCount_eq_time trace t
  have hsumR : (pullCount trace 0 t : ℝ) + pullCount trace 1 t = t := by exact_mod_cast hsum
  have htR : (562949953421312 : ℝ) ≤ t := by
    norm_num [horizon] at ht
    exact_mod_cast ht
  linarith [height_bounds.2]

theorem finite_count_obstruction :
    32*horizonHeight+5 < (pullCount trace 1 horizon : ℝ) := by
  by_contra hn
  have hcount : (pullCount trace 1 horizon : ℝ) ≤ 32*horizonHeight+5 := le_of_not_gt hn
  have hforced : ∀ t, horizon/2 ≤ t → t < horizon → trace t = 1 := by
    intro t htlo hthi
    have ht2 : 2 ≤ t := by norm_num [horizon] at htlo; omega
    apply forced_suboptimal horizonHeight t ht2 height_bounds.1
      (late_log_bounds t htlo hthi).1 (late_log_bounds t htlo hthi).2
    · exact le_trans (by exact_mod_cast (pullCount_mono trace 1 hthi.le)) hcount
    · exact late_best_count t htlo hthi.le hcount
  have hc : (Finset.Ico (horizon/2) horizon).card ≤ pullCount trace 1 horizon := by
    rw [pullCount_eq_finset_filter_card]
    apply Finset.card_le_card
    intro t ht
    have h := Finset.mem_Ico.mp ht
    exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr h.2, hforced t h.1 h.2⟩
  have hcard : (Finset.Ico (horizon/2) horizon).card = 562949953421312 := by
    rw [Nat.card_Ico]
    norm_num [horizon]
  rw [hcard] at hc
  have hcR : (562949953421312 : ℝ) ≤ pullCount trace 1 horizon := by exact_mod_cast hc
  linarith [height_bounds.2]



noncomputable def kernel : Kernel (Fin 2) ℝ :=
  Kernel.ofFunOfCountable (fun a => Measure.dirac (if a = 0 then (0 : ℝ) else -1))

@[simp] theorem kernel_apply (a : Fin 2) :
    kernel a = Measure.dirac (if a = 0 then (0 : ℝ) else -1) := rfl

instance kernel_markov : IsMarkovKernel kernel := by
  constructor
  intro a
  rw [kernel_apply]
  infer_instance

theorem kernel_raw_moment (a : Fin 2) :
    Integrable (fun x : ℝ => |x|^(1+(1 : ℝ))) (kernel a) ∧
      (∫ x : ℝ, |x|^(1+(1 : ℝ)) ∂kernel a) ≤ 1 := by
  rw [kernel_apply]
  constructor
  · exact integrable_dirac (by finiteness)
  · rw [integral_dirac]
    split <;> norm_num

@[simp] theorem kernel_mean (a : Fin 2) :
    realKernelMean kernel a = if a = 0 then 0 else -1 := by
  simp [realKernelMean]

theorem ae_deterministic :
    ∀ᵐ stream ∂UCB.armStreamMeasure kernel, stream = deterministicStream := by
  have hcoord : ∀ (i : ℕ) (a : Fin 2),
      ∀ᵐ stream ∂UCB.armStreamMeasure kernel, stream i a = if a = 0 then 0 else -1 := by
    intro i a
    have hmeas : Measurable (fun stream : UCB.ArmRewardStream 2 => stream i a) :=
      (measurable_pi_apply a).comp (measurable_pi_apply i)
    apply ae_of_ae_map (μ := UCB.armStreamMeasure kernel)
      (p := fun x : ℝ => x = if a = 0 then 0 else -1)
      (f := fun stream : UCB.ArmRewardStream 2 => stream i a) hmeas.aemeasurable
    rw [UCB.armStreamMeasure_map_coord, kernel_apply]
    simp
  have hall : ∀ᵐ stream ∂UCB.armStreamMeasure kernel,
      ∀ (i : ℕ) (a : Fin 2), stream i a = if a = 0 then 0 else -1 :=
    ae_all_iff.mpr (fun i => ae_all_iff.mpr (hcoord i))
  filter_upwards [hall] with stream h
  funext i a
  exact h i a

theorem kernel_best_mean : (⨆ a : Fin 2, realKernelMean kernel a) = 0 := by
  apply le_antisymm
  · apply ciSup_le
    intro a
    rw [kernel_mean]
    split <;> norm_num
  · have h := le_ciSup (Finite.bddAbove_range (realKernelMean kernel)) (0 : Fin 2)
    have hz : realKernelMean kernel (0 : Fin 2) = 0 := by simp
    exact hz.symm.le.trans h

theorem kernel_gap (a : Fin 2) :
    realMeanGap (realKernelMean kernel) a = if a = 0 then 0 else 1 := by
  rw [realMeanGap, kernel_best_mean, kernel_mean]
  split <;> norm_num

theorem regret_eq_count (action : ActionTrace (Fin 2)) (T : ℕ) :
    realMeanRegret (realKernelMean kernel) action T = (pullCount action 1 T : ℝ) := by
  rw [realMeanRegret_eq_sum_gap_mul_pullCount, Fin.sum_univ_two]
  norm_num [kernel_gap]

theorem expected_regret_eq_count :
    (∫ stream, realMeanRegret (realKernelMean kernel)
      (SourcePolicy.robustAction (by decide) 1 1 stream) horizon ∂UCB.armStreamMeasure kernel) =
        (pullCount trace 1 horizon : ℝ) := by
  calc
    _ = ∫ _stream, realMeanRegret (realKernelMean kernel) trace horizon
          ∂UCB.armStreamMeasure kernel := by
      apply integral_congr_ae
      filter_upwards [ae_deterministic] with stream hs
      rw [hs]
      rfl
    _ = realMeanRegret (realKernelMean kernel) trace horizon := by simp
    _ = _ := regret_eq_count trace horizon

/-- The literal printed coefficient fails for the actual source-parameter policy
under valid raw-second-moment stationary two-arm laws at a finite horizon. -/
theorem printed_coefficient_counterexample :
    32 * Real.log (horizon : ℝ) + 5 <
      ∫ stream, realMeanRegret (realKernelMean kernel)
        (SourcePolicy.robustAction (by decide) 1 1 stream) horizon ∂UCB.armStreamMeasure kernel := by
  rw [expected_regret_eq_count]
  exact finite_count_obstruction



theorem printed_gap_sum :
    (∑ a ∈ Finset.univ.filter (fun a : Fin 2 => 0 < realMeanGap (realKernelMean kernel) a),
      (8 * (4 / realMeanGap (realKernelMean kernel) a) ^ (1 / (1 : ℝ)) *
        Real.log (horizon : ℝ) + 5 * realMeanGap (realKernelMean kernel) a)) =
      32 * Real.log (horizon : ℝ) + 5 := by
  classical
  rw [Finset.sum_filter, Fin.sum_univ_two]
  norm_num [kernel_gap]

theorem literal_printed_bound_false :
    ¬ (∫ stream, realMeanRegret (realKernelMean kernel)
        (SourcePolicy.robustAction (by decide) 1 1 stream) horizon ∂UCB.armStreamMeasure kernel) ≤
      ∑ a ∈ Finset.univ.filter (fun a : Fin 2 => 0 < realMeanGap (realKernelMean kernel) a),
        (8 * (4 / realMeanGap (realKernelMean kernel) a) ^ (1 / (1 : ℝ)) *
          Real.log (horizon : ℝ) + 5 * realMeanGap (realKernelMean kernel) a) := by
  rw [printed_gap_sum]
  exact not_le_of_gt printed_coefficient_counterexample

end BanditRLProof.HeavyTail.SourceCounterexample
