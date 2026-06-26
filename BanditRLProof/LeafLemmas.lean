import BanditRLProof.Regret

/-!
# Dependency-light leaf lemmas

These lemmas are the first compiled ABRL leaf library.  They deliberately avoid
Mathlib imports while exposing stable theorem names that later Mathlib-backed
tasks can replace, generalize, or upstream.
-/

namespace BanditRLProof

section PullCount

variable {Action : Type u} [DecidableEq Action]
variable (action : ActionTrace Action) (a : Action) (t : Nat)

@[simp] theorem pullCount_one :
    pullCount action a 1 = if action 0 = a then 1 else 0 := by
  by_cases h : action 0 = a <;> simp [pullCount, h]

theorem pullCount_succ_of_eq (h : action t = a) :
    pullCount action a (t + 1) = pullCount action a t + 1 := by
  simp [pullCount_succ, h]

theorem pullCount_succ_of_ne (h : action t ≠ a) :
    pullCount action a (t + 1) = pullCount action a t := by
  simp [pullCount_succ, h]

theorem pullCount_le_succ :
    pullCount action a t ≤ pullCount action a (t + 1) := by
  rw [pullCount_succ]
  exact Nat.le_add_right _ _

theorem pullCount_succ_le_succ :
    pullCount action a (t + 1) ≤ pullCount action a t + 1 := by
  rw [pullCount_succ]
  by_cases h : action t = a <;> simp [h]

theorem pullCount_mono {s t : Nat} (h : s ≤ t) :
    pullCount action a s ≤ pullCount action a t := by
  induction h with
  | refl => exact Nat.le_refl _
  | step h ih => exact Nat.le_trans ih (pullCount_le_succ action a _)

theorem pullCount_le_time :
    pullCount action a t ≤ t := by
  induction t with
  | zero => simp
  | succ t ih =>
      rw [pullCount_succ]
      by_cases h : action t = a
      · simp [h]
        exact ih
      · simp [h]
        exact Nat.le_trans ih (Nat.le_succ t)

theorem pullCount_eq_zero_of_forall_ne
    (h : ∀ s, s < t → action s ≠ a) :
    pullCount action a t = 0 := by
  induction t with
  | zero => simp
  | succ t ih =>
      rw [pullCount_succ_of_ne action a t (h t (Nat.lt_succ_self t))]
      exact ih (fun s hs => h s (Nat.lt_trans hs (Nat.lt_succ_self t)))

theorem pullCount_eq_time_of_forall_eq
    (h : ∀ s, s < t → action s = a) :
    pullCount action a t = t := by
  induction t with
  | zero => simp
  | succ t ih =>
      rw [pullCount_succ_of_eq action a t (h t (Nat.lt_succ_self t))]
      rw [ih (fun s hs => h s (Nat.lt_trans hs (Nat.lt_succ_self t)))]

theorem pullCount_pos_of_eq_before {s t : Nat}
    (hst : s < t) (h : action s = a) :
    0 < pullCount action a t := by
  have hstep :
      pullCount action a (s + 1) = pullCount action a s + 1 :=
    pullCount_succ_of_eq action a s h
  have hpos : 0 < pullCount action a (s + 1) := by
    rw [hstep]
    exact Nat.succ_pos _
  exact Nat.lt_of_lt_of_le hpos
    (pullCount_mono action a (Nat.succ_le_of_lt hst))

@[simp] theorem pullCount_const_self (a : Action) (t : Nat) :
    pullCount (fun _ => a) a t = t := by
  apply pullCount_eq_time_of_forall_eq
  intro _s _hs
  rfl

theorem pullCount_const_of_ne (b : Action) (h : b ≠ a) (t : Nat) :
    pullCount (fun _ => b) a t = 0 := by
  apply pullCount_eq_zero_of_forall_ne
  intro _s _hs
  exact h

end PullCount

section SumRewards

variable {Action Reward : Type u} [DecidableEq Action]
variable [OfNat Reward 0] [HAdd Reward Reward Reward]
variable (action : ActionTrace Action) (reward : RewardTrace Reward)
variable (a : Action) (t : Nat)

theorem sumRewards_succ_of_eq (h : action t = a) :
    sumRewards action reward a (t + 1) =
      sumRewards action reward a t + reward t := by
  rw [sumRewards_succ, if_pos h]

theorem sumRewards_succ_of_ne (hzero : ∀ x : Reward, x + 0 = x)
    (h : action t ≠ a) :
    sumRewards action reward a (t + 1) =
      sumRewards action reward a t := by
  rw [sumRewards_succ, if_neg h, hzero]

theorem sumRewards_eq_zero_of_forall_ne (hzero : ∀ x : Reward, x + 0 = x)
    (h : ∀ s, s < t → action s ≠ a) :
    sumRewards action reward a t = 0 := by
  induction t with
  | zero => simp
  | succ t ih =>
      rw [sumRewards_succ_of_ne action reward a t hzero (h t (Nat.lt_succ_self t))]
      exact ih (fun s hs => h s (Nat.lt_trans hs (Nat.lt_succ_self t)))

theorem sumRewards_const_of_ne (hzero : ∀ x : Reward, x + 0 = x)
    (b : Action) (h : b ≠ a) (t : Nat) :
    sumRewards (fun _ => b) reward a t = 0 := by
  apply sumRewards_eq_zero_of_forall_ne
  · exact hzero
  · intro _s _hs
    exact h

end SumRewards

namespace FiniteBanditModel

@[simp] theorem bestMean_eq_mean_bestArm (model : FiniteBanditModel K) :
    model.bestMean = model.mean model.bestArm := rfl

theorem gap_of_ne_bestArm (model : FiniteBanditModel K) (arm : Fin K)
    (h : arm ≠ model.bestArm) :
    model.gap arm = model.bestMean - model.mean arm := by
  simp [gap, h]

end FiniteBanditModel

section Regret

variable (model : FiniteBanditModel K) (action : Nat → Fin K) (t : Nat)

@[simp] theorem pseudoRegret_one :
    pseudoRegret model action 1 = model.gap (action 0) := by
  change (0 : Rat) + model.gap (action 0) = model.gap (action 0)
  exact Rat.zero_add _

theorem pseudoRegret_succ_of_bestArm (h : action t = model.bestArm) :
    pseudoRegret model action (t + 1) = pseudoRegret model action t := by
  rw [pseudoRegret_succ, h, FiniteBanditModel.gap_bestArm]
  exact Rat.add_zero _

theorem pseudoRegret_succ_of_gap_zero (h : model.gap (action t) = 0) :
    pseudoRegret model action (t + 1) = pseudoRegret model action t := by
  rw [pseudoRegret_succ, h]
  exact Rat.add_zero _

theorem pseudoRegret_eq_zero_of_forall_bestArm
    (h : ∀ s, s < t → action s = model.bestArm) :
    pseudoRegret model action t = 0 := by
  induction t with
  | zero => simp
  | succ t ih =>
      rw [pseudoRegret_succ_of_bestArm model action t (h t (Nat.lt_succ_self t))]
      exact ih (fun s hs => h s (Nat.lt_trans hs (Nat.lt_succ_self t)))

theorem pseudoRegret_eq_zero_of_forall_gap_zero
    (h : ∀ s, s < t → model.gap (action s) = 0) :
    pseudoRegret model action t = 0 := by
  induction t with
  | zero => simp
  | succ t ih =>
      rw [pseudoRegret_succ_of_gap_zero model action t (h t (Nat.lt_succ_self t))]
      exact ih (fun s hs => h s (Nat.lt_trans hs (Nat.lt_succ_self t)))

@[simp] theorem pseudoRegret_const_bestArm :
    pseudoRegret model (fun _ => model.bestArm) t = 0 := by
  apply pseudoRegret_eq_zero_of_forall_bestArm
  intro _s _hs
  rfl

theorem pseudoRegret_const_of_gap_zero (arm : Fin K) (h : model.gap arm = 0) :
    pseudoRegret model (fun _ => arm) t = 0 := by
  apply pseudoRegret_eq_zero_of_forall_gap_zero
  intro _s _hs
  exact h

end Regret

end BanditRLProof
