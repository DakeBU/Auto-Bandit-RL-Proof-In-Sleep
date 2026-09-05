import BanditRLProof.LowerBounds.BlockEntropy

namespace BanditRLProof.LowerBounds

/-- Left endpoint of a symbol's arithmetic-coding partition cell. -/
def arithmeticOffset {k : ℕ} (p : Fin k → ℝ) (a : Fin k) : ℝ :=
  ∑ b ∈ Finset.univ.filter (fun b => b < a), p b

theorem arithmeticOffset_nonneg {k : ℕ} (p : Fin k → ℝ) (hp : ∀ i, 0 ≤ p i)
    (a : Fin k) : 0 ≤ arithmeticOffset p a :=
  Finset.sum_nonneg (fun i _ => hp i)

theorem arithmeticOffset_add_le_one {k : ℕ} (p : Fin k → ℝ)
    (hp : ∀ i, 0 ≤ p i) (hs : ∑ i, p i = 1) (a : Fin k) :
    arithmeticOffset p a + p a ≤ 1 := by
  let s := Finset.univ.filter (fun b => b < a)
  have ha : a ∉ s := by simp [s]
  have he : arithmeticOffset p a + p a = ∑ b ∈ insert a s, p b := by
    rw [Finset.sum_insert ha]
    exact add_comm _ _
  rw [he, ← hs]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun i _ _ => hp i)

/-- Successive affine subdivisions for an arithmetic-coded word. -/
def arithmeticInterval {k : ℕ} (p : Fin k → ℝ) : List (Fin k) → ℝ × ℝ
  | [] => (0, 1)
  | a :: w => (arithmeticOffset p a + p a * (arithmeticInterval p w).1,
      arithmeticOffset p a + p a * (arithmeticInterval p w).2)

theorem arithmeticInterval_width {k : ℕ} (p : Fin k → ℝ) (w : List (Fin k)) :
    (arithmeticInterval p w).2 - (arithmeticInterval p w).1 = (w.map p).prod := by
  induction w with
  | nil => simp [arithmeticInterval]
  | cons a w ih =>
    simp only [arithmeticInterval, List.map_cons, List.prod_cons]
    rw [← ih]
    ring

theorem arithmeticInterval_bounds {k : ℕ} (p : Fin k → ℝ)
    (hp : ∀ i, 0 ≤ p i) (hs : ∑ i, p i = 1) (w : List (Fin k)) :
    0 ≤ (arithmeticInterval p w).1 ∧
      (arithmeticInterval p w).1 ≤ (arithmeticInterval p w).2 ∧
      (arithmeticInterval p w).2 ≤ 1 := by
  induction w with
  | nil => simp [arithmeticInterval]
  | cons a w ih =>
    have ho := arithmeticOffset_nonneg p hp a
    have hu := arithmeticOffset_add_le_one p hp hs a
    simp only [arithmeticInterval]
    constructor
    · exact add_nonneg ho (mul_nonneg (hp a) ih.1)
    constructor
    · exact add_le_add (le_refl _) (mul_le_mul_of_nonneg_left ih.2.1 (hp a))
    · have h := mul_le_mul_of_nonneg_left ih.2.2 (hp a)
      nlinarith

theorem arithmeticOffset_separated {k : ℕ} (p : Fin k → ℝ)
    (hp : ∀ i, 0 ≤ p i) (a b : Fin k) (hab : a < b) :
    arithmeticOffset p a + p a ≤ arithmeticOffset p b := by
  let s := Finset.univ.filter (fun i => i < a)
  have ha : a ∉ s := by simp [s]
  have he : arithmeticOffset p a + p a = ∑ i ∈ insert a s, p i := by
    rw [Finset.sum_insert ha]
    exact add_comm _ _
  rw [he]
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro i hi
    rcases Finset.mem_insert.mp hi with rfl | hi
    · simp [hab]
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ i,
        lt_trans (Finset.mem_filter.mp hi).2 hab⟩
  · intro i _ _
    exact hp i

end BanditRLProof.LowerBounds
