import Tests.OnlineLearningChapterOneCanary

namespace FoundationsProbe
open BanditRL.OnlineLearning ChapterOneCase0

theorem prefix_minimizers :
    ∀ n, 0 < n → n ≤ 2 → ∀ u ∈ (Set.univ : Set Bool),
      (∑ t ∈ Finset.range n, demoLoss t (demoLeader n)) ≤
        ∑ t ∈ Finset.range n, demoLoss t u := by
  intro n hn hnt u hu
  interval_cases n <;> cases u <;>
    norm_num [demoLoss, demoLeader, Finset.sum_range_succ]

theorem instantiated_compare :
    (∑ t ∈ Finset.range 2, demoLoss t (demoLeader (t + 1))) ≤
      ∑ t ∈ Finset.range 2, demoLoss t (demoLeader 2) := by
  exact lemma_1_2 Set.univ demoLoss demoLeader 2 (by simp) prefix_minimizers

theorem strict_values :
    (∑ t ∈ Finset.range 2, demoLoss t (demoLeader (t + 1))) = -2 ∧
    (∑ t ∈ Finset.range 2, demoLoss t (demoLeader 2)) = 0 ∧
    (∑ t ∈ Finset.range 2, demoLoss t (demoLeader (t + 1))) <
      ∑ t ∈ Finset.range 2, demoLoss t (demoLeader 2) := by
  norm_num [demoLoss, demoLeader, Finset.sum_range_succ]

theorem zero_horizon {X : Type*} (V : Set X) (loss : ℕ → X → ℝ)
    (leader : ℕ → X) :
    (∑ t ∈ Finset.range 0, loss t (leader (t + 1))) ≤
      ∑ t ∈ Finset.range 0, loss t (leader 0) := by
  exact lemma_1_2 V loss leader 0
    (by intro n hn h; omega) (by intro n hn h; omega)

theorem one_horizon {X : Type*} (loss : ℕ → X → ℝ) (leader : ℕ → X) :
    (∑ t ∈ Finset.range 1, loss t (leader (t + 1))) =
      ∑ t ∈ Finset.range 1, loss t (leader 1) := by
  simp [Finset.sum_range_succ]

theorem without_optimality :
    let leader : ℕ → Bool := fun n => n = 2
    (∀ n, 0 < n → n ≤ 2 → leader n ∈ (Set.univ : Set Bool)) ∧
    (∑ t ∈ Finset.range 1, demoLoss t true) <
      (∑ t ∈ Finset.range 1, demoLoss t (leader 1)) ∧
    (∑ t ∈ Finset.range 2, demoLoss t (leader (t + 1))) >
      ∑ t ∈ Finset.range 2, demoLoss t (leader 2) := by
  dsimp only
  constructor
  · intro n hn hnt
    exact Set.mem_univ _
  · norm_num [demoLoss, Finset.sum_range_succ]

theorem without_feasibility :
    let loss : ℕ → Bool → ℝ := fun t b => if b then if t = 0 then -10 else 5 else 0
    let leader : ℕ → Bool := fun n => n = 2
    let V : Set Bool := {false}
    (∀ n, 0 < n → n ≤ 2 → ∀ u ∈ V,
      (∑ t ∈ Finset.range n, loss t (leader n)) ≤ ∑ t ∈ Finset.range n, loss t u) ∧
    leader 2 ∉ V ∧
    (∑ t ∈ Finset.range 2, loss t (leader (t + 1))) >
      ∑ t ∈ Finset.range 2, loss t (leader 2) := by
  dsimp only
  constructor
  · intro n hn hnt u hu
    have huf : u = false := by simpa only [Set.mem_singleton_iff] using hu
    subst u
    interval_cases n <;> norm_num [Finset.sum_range_succ]
  · norm_num [Finset.sum_range_succ]

end FoundationsProbe
