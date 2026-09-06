import BanditRLProof.Algorithms.MOSSCanonicalReward

noncomputable section
open MeasureTheory ProbabilityTheory
namespace BanditRLProof.MOSS

def canonicalAction {k : ℕ} (hk : 0 < k) (n : ℕ) (mean : Fin k → ℝ) :=
  streamTrace hk n mean (centeredRewardTable mean)

/-- Consume the next unused one-based raw reward of the chosen arm. -/
def canonicalReward {k : ℕ} (hk : 0 < k) (n : ℕ) (mean : Fin k → ℝ) :=
  UCB.rewardFromArmStream (canonicalAction hk n mean)
    (fun table : UCB.ArmRewardStream k => fun i a => table (i+1) a)

def canonicalHistory {k : ℕ} (hk : 0 < k) (n : ℕ) (mean : Fin k → ℝ)
    (table : UCB.ArmRewardStream k) (t : ℕ) :=
  History.finitePairHistoryOfTrace (canonicalAction hk n mean table)
    (canonicalReward hk n mean table) t

theorem canonicalHistory_pullCount {k : ℕ} (hk : 0 < k) (n : ℕ) (mean : Fin k → ℝ)
    (table : UCB.ArmRewardStream k) (t : ℕ) (a : Fin k) :
    ETC.realHistoryPullCount t (canonicalHistory hk n mean table t) a =
      pullCount (canonicalAction hk n mean table) a (t+1) :=
  ETC.realHistoryPullCount_finitePairHistoryOfTrace _ _ _ _

theorem canonicalHistory_empiricalMean {k : ℕ} (hk : 0 < k) (n : ℕ) (mean : Fin k → ℝ)
    (table : UCB.ArmRewardStream k) (t : ℕ) (a : Fin k) :
    ETC.realHistoryEmpMean t (canonicalHistory hk n mean table t) a =
      (∑ j ∈ Finset.range (pullCount (canonicalAction hk n mean table) a (t+1)), table (j+1) a) /
        (pullCount (canonicalAction hk n mean table) a (t+1) : ℝ) := by
  rw [canonicalHistory, ETC.realHistoryEmpMean_finitePairHistoryOfTrace]
  rw [canonicalReward, UCB.sumRewards_rewardFromArmStream_eq_armPrefixSum]
  rfl

/-- The realized next action is exactly the common finite-history MOSS selector. -/
theorem canonicalAction_succ_eq_historyAction {k : ℕ} (hk : 0 < k) (n : ℕ)
    (mean : Fin k → ℝ) (table : UCB.ArmRewardStream k) (t : ℕ) :
    canonicalAction hk n mean table (t+1) =
      historyAction hk n t (canonicalHistory hk n mean table t) := by
  unfold historyAction
  have hc : ETC.realHistoryPullCount t (canonicalHistory hk n mean table t) =
      fun a => pullCount (canonicalAction hk n mean table) a (t+1) :=
    funext (canonicalHistory_pullCount hk n mean table t)
  have he : ETC.realHistoryEmpMean t (canonicalHistory hk n mean table t) =
      fun a => (∑ j ∈ Finset.range (pullCount (canonicalAction hk n mean table) a (t+1)), table (j+1) a) /
        (pullCount (canonicalAction hk n mean table) a (t+1) : ℝ) :=
    funext (canonicalHistory_empiricalMean hk n mean table t)
  rw [hc, he]
  exact canonicalReward_action_eq_raw hk n (t+1) mean table

theorem canonicalAction_zero {k : ℕ} (hk : 0 < k) (n : ℕ)
    (mean : Fin k → ℝ) (table : UCB.ArmRewardStream k) :
    canonicalAction hk n mean table 0 = ⟨0, hk⟩ :=
  action_of_lt hk n 0 _ _ hk

theorem measurable_canonicalAction {k : ℕ} (hk : 0 < k) (n : ℕ)
    (mean : Fin k → ℝ) (t : ℕ) : Measurable (fun table => canonicalAction hk n mean table t) := by
  apply measurable_streamTrace
  intro a i
  have h : Measurable (fun table : UCB.ArmRewardStream k => table i a) :=
    (measurable_pi_apply a).comp (measurable_pi_apply i)
  exact (h.sub measurable_const).stronglyMeasurable

theorem measurable_canonicalReward {k : ℕ} (hk : 0 < k) (n : ℕ)
    (mean : Fin k → ℝ) (t : ℕ) : Measurable (fun table => canonicalReward hk n mean table t) := by
  have ha := measurable_canonicalAction hk n mean t
  have hc : Measurable (fun p : UCB.ArmRewardStream k × Fin k =>
      pullCount (canonicalAction hk n mean p.1) p.2 t) := by
    apply measurable_from_prod_countable_left
    intro a
    exact measurable_pullCount _ (measurable_canonicalAction hk n mean) a t
  have hm := hc.comp (measurable_id.prodMk ha)
  exact UCB.measurable_armRewardStream_apply.comp
    (measurable_id.prodMk ((hm.add_const 1).prodMk ha))

theorem measurable_canonicalHistory {k : ℕ} (hk : 0 < k) (n : ℕ)
    (mean : Fin k → ℝ) (t : ℕ) : Measurable (fun table => canonicalHistory hk n mean table t) :=
  History.measurable_finitePairHistoryOfTrace _ _
    (measurable_canonicalAction hk n mean) (measurable_canonicalReward hk n mean) t

theorem canonicalHistory_succ {k : ℕ} (hk : 0 < k) (n : ℕ)
    (mean : Fin k → ℝ) (table : UCB.ArmRewardStream k) (t : ℕ) :
    canonicalHistory hk n mean table (t+1) = History.extendPairHistorySucc
      (canonicalHistory hk n mean table t)
      (historyAction hk n t (canonicalHistory hk n mean table t),
        table (ETC.realHistoryPullCount t (canonicalHistory hk n mean table t)
          (historyAction hk n t (canonicalHistory hk n mean table t))+1)
          (historyAction hk n t (canonicalHistory hk n mean table t))) := by
  conv_lhs => unfold canonicalHistory
  rw [History.finitePairHistoryOfTrace_succ]
  change History.extendPairHistorySucc (canonicalHistory hk n mean table t) _ = _
  congr 1
  rw [← canonicalAction_succ_eq_historyAction]
  rw [canonicalHistory_pullCount]
  rfl

/-- Changing rewards that have not been consumed cannot change the observed history. -/
theorem canonicalHistory_eq_of_eq_consumed {k : ℕ} (hk : 0 < k) (n : ℕ)
    (mean : Fin k → ℝ) (table table' : UCB.ArmRewardStream k) (t : ℕ)
    (hagrees : ∀ a j, j < pullCount (canonicalAction hk n mean table) a (t+1) →
      table (j+1) a = table' (j+1) a) :
    canonicalHistory hk n mean table t = canonicalHistory hk n mean table' t := by
  induction t with
  | zero =>
      have he := hagrees ⟨0, hk⟩ 0 (by simp [pullCount_succ, canonicalAction_zero])
      funext i
      have hi : i.val = 0 := by have := Finset.mem_Iic.mp i.property; omega
      simp [canonicalHistory, History.finitePairHistoryOfTrace, hi,
        canonicalReward, UCB.rewardFromArmStream, canonicalAction_zero, he]
  | succ t ih =>
      have hh := ih (fun a j hj => hagrees a j (lt_of_lt_of_le hj
        (pullCount_mono (canonicalAction hk n mean table) a (Nat.le_succ _))))
      rw [canonicalHistory_succ, canonicalHistory_succ, ← hh]
      congr 2
      apply hagrees
      rw [canonicalHistory_pullCount]
      have hs := canonicalAction_succ_eq_historyAction hk n mean table t
      rw [pullCount_succ_of_eq _ _ _ hs]
      exact Nat.lt_succ_self _

end BanditRLProof.MOSS
