import BanditRLProof.Algorithms.HOOHistory

/-! Actual selected-path and prefix-closure producers for source Lemma 14. -/
namespace BanditRLProof.HOO

theorem proper_prefix_walk_mem (S : Finset Node) (B : Node → WithTop ℝ)
    (k : ℕ) (v w : Node) (hvw : v <+: w) (hw : w <+: walk S B k v)
    (hne : w ≠ walk S B k v) : w ∈ S := by
  induction k generalizing v with
  | zero =>
    have he : v = w := hvw.eq_of_length_le hw.length_le
    exact False.elim (hne he.symm)
  | succ k ih =>
    by_cases hv : v ∈ S
    · simp only [walk, if_pos hv] at hw hne
      by_cases he : w = v
      · simpa only [he] using hv
      · have hlt : v.length < w.length := by
          have hl := hvw.length_le
          have hh : v.length ≠ w.length := fun h => he (hvw.eq_of_length h).symm
          omega
        have hp : child v (preferred B v) <+: w :=
          List.prefix_of_prefix_length_le (prefix_walk S B k _) hw (by simp; omega)
        exact ih _ hp hw hne
    · simp only [walk, if_neg hv] at hw hne
      exact False.elim (hne (hvw.eq_of_length_le hw.length_le).symm)

theorem proper_prefix_select_mem (S : Finset Node) (U : Node → WithTop ℝ)
    (w : Node) (hw : w <+: select S U) (hne : w ≠ select S U) : w ∈ S :=
  proper_prefix_walk_mem S (bValue S U) _ [] w List.nil_prefix hw hne

/-- The generated tree is prefix closed; it is not assumed to be a valid tree. -/
theorem expanded_history_prefix_closed (ν ρ : ℝ) (Y : ℕ → ℝ) (n : ℕ)
    (w v : Node) (hw : w ∈ expanded (history ν ρ Y n)) (hv : v <+: w) :
    v ∈ expanded (history ν ρ Y n) := by
  induction n with
  | zero =>
    simp [history, expanded] at hw ⊢
    subst w
    exact List.prefix_nil.mp hv
  | succ n ih =>
    rw [history, expanded_step, Finset.mem_insert] at hw ⊢
    rcases hw with hw | hw
    · subst w
      by_cases he : v = next ν ρ (history ν ρ Y n)
      · exact Or.inl he
      · exact Or.inr (proper_prefix_select_mem _ _ v hv he)
    · exact Or.inr (ih hw)

theorem bValue_le_upper (S : Finset Node) (U : Node → WithTop ℝ)
    (v : Node) (hv : v ∈ S) : bValue S U v ≤ U v := by
  rw [bValue_eq S U v hv]
  exact min_le_left _ _

/-- B is nondecreasing at every intermediate node on the actual chosen path. -/
theorem bValue_le_prefix_walk (S : Finset Node) (U : Node → WithTop ℝ)
    (k : ℕ) (v w : Node) (hvw : v <+: w)
    (hw : w <+: walk S (bValue S U) k v) : bValue S U v ≤ bValue S U w := by
  induction k generalizing v with
  | zero =>
    have he : v = w := hvw.eq_of_length_le hw.length_le
    rw [he]
  | succ k ih =>
    by_cases hv : v ∈ S
    · simp only [walk, if_pos hv] at hw
      by_cases he : w = v
      · rw [he]
      · have hlt : v.length < w.length := by
          have hl := hvw.length_le
          have hh : v.length ≠ w.length := fun h => he (hvw.eq_of_length h).symm
          omega
        have hp : child v (preferred (bValue S U) v) <+: w :=
          List.prefix_of_prefix_length_le (prefix_walk S (bValue S U) k _) hw (by simp; omega)
        apply LE.le.trans _ (ih _ hp hw)
        rw [preferred_max (bValue S U) v, bValue_eq S U v hv]
        exact min_le_right _ _
    · simp only [walk, if_neg hv] at hw
      rw [hvw.eq_of_length_le hw.length_le]

end BanditRLProof.HOO
