import BanditRLProof.Algorithms.ArmStreamPolicy
import BanditRLProof.HeavyTailTruncation

/-! Sample-index truncation computed solely from the finite observed history. -/
namespace BanditRLProof.HeavyTail
open MeasureTheory
variable {K : ℕ}

def historyAction (initial : Fin K) (n : ℕ)
    (h : History.FinitePairHistory (Fin K) ℝ n) : ActionTrace (Fin K) :=
  fun t => if ht : t ≤ n then (h ⟨t, Finset.mem_Iic.mpr ht⟩).1 else initial

def historyReward (n : ℕ) (h : History.FinitePairHistory (Fin K) ℝ n) : RewardTrace ℝ :=
  fun t => if ht : t ≤ n then (h ⟨t, Finset.mem_Iic.mpr ht⟩).2 else 0

theorem measurable_historyAction (initial : Fin K) (n t : ℕ) :
    Measurable (fun h => historyAction initial n h t) := by
  by_cases ht : t ≤ n
  · simpa only [historyAction, dif_pos ht] using
      measurable_fst.comp (measurable_pi_apply (⟨t, Finset.mem_Iic.mpr ht⟩ : Finset.Iic n))
  · simp only [historyAction, dif_neg ht]
    exact measurable_const

theorem measurable_historyReward (n t : ℕ) :
    Measurable (fun h : History.FinitePairHistory (Fin K) ℝ n => historyReward n h t) := by
  by_cases ht : t ≤ n
  · simpa only [historyReward, dif_pos ht] using
      measurable_snd.comp (measurable_pi_apply (⟨t, Finset.mem_Iic.mpr ht⟩ : Finset.Iic n))
  · simp only [historyReward, dif_neg ht]
    exact measurable_const

noncomputable def historyTruncatedMean (initial : Fin K) (B : ℕ → ℝ) (n : ℕ)
    (h : History.FinitePairHistory (Fin K) ℝ n) (arm : Fin K) : ℝ :=
  sumRewards (historyAction initial n h)
    (fun t => truncate (B (pullCount (historyAction initial n h) arm t)) (historyReward n h t))
    arm (n+1) / pullCount (historyAction initial n h) arm (n+1)

theorem measurable_historyTruncatedMean (initial : Fin K) (B : ℕ → ℝ) (n : ℕ)
    (arm : Fin K) : Measurable (fun h => historyTruncatedMean initial B n h arm) := by
  have hc := fun t => measurable_pullCount (historyAction initial n)
    (measurable_historyAction initial n) arm t
  have ht : Measurable (fun p : ℕ × ℝ => truncate (B p.1) p.2) := by
    apply measurable_from_prod_countable_right
    intro i
    exact measurable_truncate (B i)
  have hr := fun t => ht.comp ((hc t).prodMk (measurable_historyReward n t))
  exact (measurable_sumRewards (historyAction initial n) _
    (measurable_historyAction initial n) hr arm (n+1)).div
    ((measurable_of_countable (fun k : ℕ => (k : ℝ))).comp (hc (n+1)))

theorem history_count_trace (initial : Fin K) (a : ActionTrace (Fin K)) (r : RewardTrace ℝ)
    (arm : Fin K) (n t : ℕ) (ht : t ≤ n+1) :
    pullCount (historyAction initial n (History.finitePairHistoryOfTrace a r n)) arm t =
      pullCount a arm t := by
  induction t with
  | zero => rfl
  | succ t ih =>
    rw [pullCount_succ, pullCount_succ, ih (by omega)]
    simp [historyAction, show t ≤ n by omega, History.finitePairHistoryOfTrace]

theorem historyTruncatedMean_trace (initial : Fin K) (B : ℕ → ℝ)
    (a : ActionTrace (Fin K)) (r : RewardTrace ℝ) (arm : Fin K) (n : ℕ) :
    historyTruncatedMean initial B n (History.finitePairHistoryOfTrace a r n) arm =
      sumRewards a (fun t => truncate (B (pullCount a arm t)) (r t)) arm (n+1) /
        pullCount a arm (n+1) := by
  unfold historyTruncatedMean
  rw [history_count_trace initial a r arm n (n+1) le_rfl]
  congr 1
  suffices ∀ t, t ≤ n+1 → sumRewards
      (historyAction initial n (History.finitePairHistoryOfTrace a r n))
      (fun s => truncate (B (pullCount
        (historyAction initial n (History.finitePairHistoryOfTrace a r n)) arm s))
        (historyReward n (History.finitePairHistoryOfTrace a r n) s)) arm t =
      sumRewards a (fun s => truncate (B (pullCount a arm s)) (r s)) arm t from
    this (n+1) le_rfl
  intro t ht
  induction t with
  | zero => rfl
  | succ t ih =>
    rw [sumRewards_succ, sumRewards_succ, ih (by omega),
      history_count_trace initial a r arm n t (by omega)]
    simp [historyAction, historyReward, show t ≤ n by omega, History.finitePairHistoryOfTrace]

/-- On selected observations, the fixed arm count is the selected arm count.
This is the pathwise connection to the latent fixed-prefix confidence theorem. -/
theorem truncated_observed_sum {Ω : Type*} (a : Ω → ActionTrace (Fin K))
    (stream : Ω → UCB.ArmRewardStream K) (B : ℕ → ℝ) (ω : Ω) (arm : Fin K) (n : ℕ) :
    sumRewards (a ω)
      (fun t => truncate (B (pullCount (a ω) arm t))
        (UCB.rewardFromArmStream a stream ω t)) arm n =
      ∑ s ∈ Finset.range (pullCount (a ω) arm n), truncate (B s) (stream ω s arm) := by
  rw [← transformed_observed_prefix a stream (fun s _ x => truncate (B s) x) ω arm n]
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [sumRewards_succ, ih]
    by_cases h : a ω n = arm <;> simp [h]

theorem historyTruncatedMean_latent (initial : Fin K) (select) (B : ℕ → ℝ)
    (stream : UCB.ArmRewardStream K) (arm : Fin K) (n : ℕ) :
    historyTruncatedMean initial B n (ArmStreamPolicy.history initial select stream n) arm =
      (∑ s ∈ Finset.range (pullCount (ArmStreamPolicy.action initial select stream) arm (n+1)),
        truncate (B s) (stream s arm)) /
      pullCount (ArmStreamPolicy.action initial select stream) arm (n+1) := by
  rw [ArmStreamPolicy.history_eq_trace, historyTruncatedMean_trace]
  rw [ArmStreamPolicy.reward, truncated_observed_sum]
  rfl

end BanditRLProof.HeavyTail
