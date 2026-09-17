import BanditRLProof.Algorithms.UCBArmStreamProcess

/-! A measurable history selector driven by the existing latent reward streams.
This generalizes the UCB recursion without changing its reward/count semantics. -/
namespace BanditRLProof.ArmStreamPolicy
open MeasureTheory

variable {K : ℕ}

noncomputable def history (initial : Fin K)
    (select : (n : ℕ) → History.FinitePairHistory (Fin K) ℝ n → Fin K)
    (stream : UCB.ArmRewardStream K) :
    (n : ℕ) → History.FinitePairHistory (Fin K) ℝ n
  | 0 => fun _ => (initial, stream 0 initial)
  | n + 1 =>
    let h := history initial select stream n
    let a := select n h
    History.extendPairHistorySucc h (a, stream (ETC.realHistoryPullCount n h a) a)

noncomputable def action (initial : Fin K)
    (select : (n : ℕ) → History.FinitePairHistory (Fin K) ℝ n → Fin K)
    (stream : UCB.ArmRewardStream K) : ActionTrace (Fin K) :=
  fun t => (history initial select stream t ⟨t, Finset.mem_Iic.mpr le_rfl⟩).1

noncomputable def reward (initial : Fin K)
    (select : (n : ℕ) → History.FinitePairHistory (Fin K) ℝ n → Fin K) :=
  UCB.rewardFromArmStream (action initial select) id

@[simp] theorem action_zero (initial : Fin K) (select) (stream) :
    action initial select stream 0 = initial := rfl

@[simp] theorem action_succ (initial : Fin K) (select) (stream) (n : ℕ) :
    action initial select stream (n+1) = select n (history initial select stream n) := by
  simp [action, history]

theorem history_eq_trace (initial : Fin K) (select) (stream) (n : ℕ) :
    history initial select stream n = History.finitePairHistoryOfTrace
      (action initial select stream) (reward initial select stream) n := by
  induction n with
  | zero =>
    funext i
    have hi : i = ⟨0, Finset.mem_Iic.mpr le_rfl⟩ :=
      Subtype.ext (Nat.eq_zero_of_le_zero (Finset.mem_Iic.mp i.2))
    subst i
    simp [history, action, reward, UCB.rewardFromArmStream]
  | succ n ih =>
    rw [history, History.finitePairHistoryOfTrace_succ, ← ih]
    apply congrArg (History.extendPairHistorySucc (t := n) (history initial select stream n))
    apply Prod.ext
    · simp
    · simp only [reward, UCB.rewardFromArmStream]
      rw [action_succ, ih, ETC.realHistoryPullCount_finitePairHistoryOfTrace]
      rfl

theorem measurable_history (initial : Fin K) (select)
    (hm : ∀ n, Measurable (select n)) (n : ℕ) :
    Measurable (fun stream => history initial select stream n) := by
  induction n with
  | zero =>
    refine measurable_pi_lambda _ (fun _ => ?_)
    exact measurable_const.prodMk
      ((measurable_pi_apply initial).comp (measurable_pi_apply 0))
  | succ n ih =>
    have ha := (hm n).comp ih
    have hc : Measurable (fun p : History.FinitePairHistory (Fin K) ℝ n × Fin K =>
        ETC.realHistoryPullCount n p.1 p.2) := by
      apply measurable_from_prod_countable_left
      exact UCB.measurable_realHistoryPullCount n
    have hr := UCB.measurable_armRewardStream_apply.comp
      (measurable_id.prodMk ((hc.comp (ih.prodMk ha)).prodMk ha))
    simpa only [history, Function.comp_apply] using
      History.measurable_extendPairHistorySucc.comp (ih.prodMk (ha.prodMk hr))

theorem measurable_action (initial : Fin K) (select)
    (hm : ∀ n, Measurable (select n)) (t : ℕ) :
    Measurable (fun stream => action initial select stream t) := by
  exact (measurable_fst.comp (measurable_pi_apply
    (⟨t, Finset.mem_Iic.mpr le_rfl⟩ : Finset.Iic t))).comp
    (measurable_history initial select hm t)

/-- Compatibility is equality of the actual recursively generated histories. -/
theorem history_ucb (hK : 0 < K) (c : ℝ) (stream) (n : ℕ) :
    history (UCB.initializationArm hK 0) (UCB.realHistoryNextArm hK c) stream n =
      UCB.armStreamHistory hK c stream n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [history, UCB.armStreamHistory, ih]

end BanditRLProof.ArmStreamPolicy
