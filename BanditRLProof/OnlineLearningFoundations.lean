import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset

namespace BanditRL.OnlineLearning

/-- Orabona v10 Lemma 1.2. `leader n` is a hindsight minimizer of the first `n`
losses, not the prediction made before round `n`. -/
theorem lemma_1_2 {X : Type*} (V : Set X) (loss : ℕ → X → ℝ)
    (leader : ℕ → X) (T : ℕ)
    (hmem : ∀ n, 0 < n → n ≤ T → leader n ∈ V)
    (hmin : ∀ n, 0 < n → n ≤ T → ∀ u ∈ V,
      (∑ t ∈ Finset.range n, loss t (leader n)) ≤ ∑ t ∈ Finset.range n, loss t u) :
    (∑ t ∈ Finset.range T, loss t (leader (t + 1))) ≤
      ∑ t ∈ Finset.range T, loss t (leader T) := by
  induction T with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, Finset.sum_range_succ]
    apply add_le_add _ le_rfl
    by_cases hn : n = 0
    · subst n
      simp
    · have hnpos : 0 < n := Nat.pos_of_ne_zero hn
      have hprefix := ih
        (fun k hk hkn => hmem k hk (hkn.trans (Nat.le_succ n)))
        (fun k hk hkn => hmin k hk (hkn.trans (Nat.le_succ n)))
      exact hprefix.trans (hmin n hnpos (Nat.le_succ n) (leader (n + 1))
        (hmem (n + 1) (Nat.zero_lt_succ n) le_rfl))

end BanditRL.OnlineLearning
