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

theorem arithmeticInterval_head_separated {k : ℕ} (p : Fin k → ℝ)
    (hp : ∀ i, 0 ≤ p i) (hs : ∑ i, p i = 1)
    (a b : Fin k) (u v : List (Fin k)) (hab : a < b) :
    (arithmeticInterval p (a :: u)).2 ≤ (arithmeticInterval p (b :: v)).1 := by
  have hsep := arithmeticOffset_separated p hp a b hab
  have hu := (arithmeticInterval_bounds p hp hs u).2.2
  have hv := (arithmeticInterval_bounds p hp hs v).1
  have hmul := mul_le_mul_of_nonneg_left hu (hp a)
  have hnonneg := mul_nonneg (hp b) hv
  simp only [arithmeticInterval]
  nlinarith

/-- Different equal-length messages occupy cells with disjoint interiors. -/
theorem arithmeticInterval_separated {k : ℕ} (p : Fin k → ℝ)
    (hp : ∀ i, 0 ≤ p i) (hs : ∑ i, p i = 1)
    (u v : List (Fin k)) (hlen : u.length = v.length) (hne : u ≠ v) :
    (arithmeticInterval p u).2 ≤ (arithmeticInterval p v).1 ∨
      (arithmeticInterval p v).2 ≤ (arithmeticInterval p u).1 := by
  induction u generalizing v with
  | nil =>
    have hv : v = [] := List.length_eq_zero_iff.mp hlen.symm
    exact (hne hv.symm).elim
  | cons a u ih =>
    cases v with
    | nil => simp at hlen
    | cons b v =>
      by_cases hab : a = b
      · subst b
        have ht : u ≠ v := by intro he; exact hne (congrArg (List.cons a) he)
        have hl : u.length = v.length := by simpa using hlen
        rcases ih v hl ht with huv | hvu
        · exact Or.inl (add_le_add (le_refl _) (mul_le_mul_of_nonneg_left huv (hp a)))
        · exact Or.inr (add_le_add (le_refl _) (mul_le_mul_of_nonneg_left hvu (hp a)))
      · rcases lt_or_gt_of_ne hab with hab | hba
        · exact Or.inl (arithmeticInterval_head_separated p hp hs a b u v hab)
        · exact Or.inr (arithmeticInterval_head_separated p hp hs b a v u hba)

/-- Any point strictly inside a message cell identifies that message uniquely
among messages of the same length. -/
theorem arithmeticInterval_interior_unique {k : ℕ} (p : Fin k → ℝ)
    (hp : ∀ i, 0 ≤ p i) (hs : ∑ i, p i = 1)
    (u v : List (Fin k)) (hlen : u.length = v.length) (x : ℝ)
    (hu : (arithmeticInterval p u).1 < x ∧ x < (arithmeticInterval p u).2)
    (hv : (arithmeticInterval p v).1 < x ∧ x < (arithmeticInterval p v).2) : u = v := by
  by_contra hne
  rcases arithmeticInterval_separated p hp hs u v hlen hne with h | h <;> linarith

/-- A positive grid cell fits in any nonnegative interval at least twice as wide.
Mathlib-candidate scalar rounding leaf for arithmetic-code dyadic selection. -/
theorem exists_grid_cell_inside (L U δ : ℝ) (hL : 0 ≤ L) (hδ : 0 < δ)
    (hwidth : 2 * δ ≤ U - L) :
    ∃ m : ℕ, L ≤ (m : ℝ) * δ ∧ ((m : ℝ) + 1) * δ < U := by
  refine ⟨⌈L / δ⌉₊, ?_, ?_⟩
  · have h := mul_le_mul_of_nonneg_right (Nat.le_ceil (L / δ)) hδ.le
    simpa [ne_of_gt hδ] using h
  · have h := mul_lt_mul_of_pos_right (Nat.ceil_lt_add_one (div_nonneg hL hδ.le)) hδ
    have he : (L / δ + 1) * δ = L + δ := by
      rw [add_mul, div_mul_cancel₀ _ (ne_of_gt hδ), one_mul]
    rw [he] at h
    nlinarith

end BanditRLProof.LowerBounds
