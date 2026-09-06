import BanditRLProof.LeafLemmas
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset

open Finset

namespace BanditRLProof

/-- Each selected round visits exactly one successive pre-pull count. -/
theorem sum_selected_pullCount {Action : Type*} [DecidableEq Action]
    (action : ActionTrace Action) (a : Action) (f : ℕ → ℝ) (T : ℕ) :
    (∑ t ∈ range T, if action t = a then f (pullCount action a t) else 0) =
      ∑ s ∈ range (pullCount action a T), f s := by
  induction T with
  | zero => simp
  | succ T ih =>
      rw [sum_range_succ, ih, pullCount_succ]
      by_cases h : action T = a
      · simp [h, sum_range_succ]
      · simp [h]

/-- Event-count transport retains the first pull, whose pre-pull count is zero.
The event premise must be supplied separately by the algorithm analysis. -/
theorem pullCount_le_one_add_eventCount {Action : Type*} [DecidableEq Action]
    (action : ActionTrace Action) (a : Action) (P : ℕ → Prop) [DecidablePred P]
    (T : ℕ)
    (hselected : ∀ t < T, action t = a → 0 < pullCount action a t →
      P (pullCount action a t)) :
    (pullCount action a T : ℝ) ≤
      1 + ∑ s ∈ range T, if P (s + 1) then (1 : ℝ) else 0 := by
  let f : ℕ → ℝ := fun s => if s = 0 then 1 else if P s then 1 else 0
  have hsum : (pullCount action a T : ℝ) = ∑ s ∈ range (pullCount action a T), f s := by
    have hconst := sum_selected_pullCount action a (fun _ => (1 : ℝ)) T
    have hf := sum_selected_pullCount action a f T
    have heq : (∑ t ∈ range T, if action t = a then (1 : ℝ) else 0) =
        ∑ t ∈ range T, if action t = a then f (pullCount action a t) else 0 := by
      apply sum_congr rfl
      intro t ht
      by_cases h : action t = a
      · by_cases hz : pullCount action a t = 0
        · simp [h, f, hz]
        · have hp := hselected t (mem_range.mp ht) h (Nat.pos_of_ne_zero hz)
          simp [h, f, hz, hp]
      · simp [h]
    simpa using hconst.symm.trans (heq.trans hf)
  rw [hsum]
  have hle : ∑ s ∈ range (pullCount action a T), f s ≤ ∑ s ∈ range (T + 1), f s := by
    apply sum_le_sum_of_subset_of_nonneg
    · exact range_mono (Nat.le_trans (pullCount_le_time action a T) (Nat.le_succ T))
    · intro s _ _
      dsimp [f]
      split_ifs <;> norm_num
  calc
    _ ≤ ∑ s ∈ range (T + 1), f s := hle
    _ = _ := by rw [sum_range_succ']; simp [f, add_comm]

end BanditRLProof
