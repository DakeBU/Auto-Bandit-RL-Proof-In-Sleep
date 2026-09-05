import BanditRLProof.LowerBounds.PrefixCodeSiblings

namespace BanditRLProof.LowerBounds

/-- A deepest leaf with no sibling has a parent incomparable with every other word. -/
theorem deepest_parent_incomparable
    {α : Type*} (code : BinaryPrefixCode α) (a : α) (w : List Bool) (b : Bool)
    (ha : code.encode a = w ++ [b])
    (hmax : ∀ i, (code.encode i).length ≤ (code.encode a).length)
    (hmissing : ∀ i, code.encode i ≠ w ++ [!b]) :
    ∀ i, i ≠ a → (¬ code.encode i <+: w) ∧ (¬ w <+: code.encode i) := by
  intro i hia
  have hleft : ¬ code.encode i <+: w := by
    intro h
    have hp : code.encode i <+: code.encode a := by
      rw [ha]
      exact h.trans (List.prefix_append _ _)
    exact hia (code.prefixFree hp)
  refine ⟨hleft, ?_⟩
  rintro ⟨t, ht⟩
  have hlen := hmax i
  rw [ha, ← ht] at hlen
  simp only [List.length_append, List.length_singleton] at hlen
  cases t with
  | nil =>
    have he : w = code.encode i := by simpa using ht
    exact hleft (by rw [he])
  | cons c t =>
    have ht0 : t = [] := List.length_eq_zero_iff.mp (by simp only [List.length_cons] at hlen; omega)
    subst t
    by_cases hcb : c = b
    · have he : code.encode i = code.encode a := by rw [ha, ← ht, hcb]
      exact hia (code.injective he)
    · have hc : c = !b := by cases b <;> cases c <;> simp_all
      exact hmissing i (by rw [← ht, hc])

/-- Replace one word by an incomparable nonempty word, preserving code validity. -/
def BinaryPrefixCode.replaceWord
    {α : Type*} [DecidableEq α] (code : BinaryPrefixCode α) (a : α) (w : List Bool)
    (hw : w ≠ [])
    (hsep : ∀ i, i ≠ a → (¬ code.encode i <+: w) ∧ (¬ w <+: code.encode i)) :
    BinaryPrefixCode α := by
  let f : α → List Bool := fun i => if i = a then w else code.encode i
  have hf : ∀ i j, f i <+: f j → i = j := by
    intro i j h
    by_cases hi : i = a
    · by_cases hj : j = a
      · exact hi.trans hj.symm
      · exact ((hsep j hj).2 (by simpa [f, hi, hj] using h)).elim
    · by_cases hj : j = a
      · exact ((hsep i hi).1 (by simpa [f, hi, hj] using h)).elim
      · exact code.prefixFree (by simpa [f, hi, hj] using h)
  exact ⟨f, fun i j h => hf i j (by rw [h]),
    fun i => by dsimp [f]; split_ifs; exact hw; exact code.nonempty i,
    fun h => hf _ _ h⟩

/-- Legal deletion of the last bit of a deepest sibling-free leaf. -/
def BinaryPrefixCode.pruneDeepest
    {α : Type*} [DecidableEq α] (code : BinaryPrefixCode α) (a : α) (w : List Bool) (b : Bool)
    (hw : w ≠ []) (ha : code.encode a = w ++ [b])
    (hmax : ∀ i, (code.encode i).length ≤ (code.encode a).length)
    (hmissing : ∀ i, code.encode i ≠ w ++ [!b]) : BinaryPrefixCode α :=
  code.replaceWord a w hw (deepest_parent_incomparable code a w b ha hmax hmissing)

theorem expectedCodeLength_replaceWord
    {α : Type*} [Fintype α] [DecidableEq α] (p : α → ℝ)
    (code : BinaryPrefixCode α) (a : α) (w : List Bool) (hw : w ≠ [])
    (hsep : ∀ i, i ≠ a → (¬ code.encode i <+: w) ∧ (¬ w <+: code.encode i)) :
    expectedCodeLength p (code.replaceWord a w hw hsep) = expectedCodeLength p code +
      p a * (w.length - (code.encode a).length : ℝ) := by
  have ht (i) : p i * ((code.replaceWord a w hw hsep).encode i).length =
      p i * (code.encode i).length +
        (if i = a then p a * (w.length - (code.encode a).length : ℝ) else 0) := by
    by_cases hi : i = a
    · subst i
      simp [BinaryPrefixCode.replaceWord]
      ring
    · simp [BinaryPrefixCode.replaceWord, hi]
  simp only [expectedCodeLength, ht, Finset.sum_add_distrib]
  simp

theorem expectedCodeLength_pruneDeepest
    {α : Type*} [Fintype α] [DecidableEq α] (p : α → ℝ)
    (code : BinaryPrefixCode α) (a : α) (w : List Bool) (b : Bool)
    (hw : w ≠ []) (ha : code.encode a = w ++ [b])
    (hmax : ∀ i, (code.encode i).length ≤ (code.encode a).length)
    (hmissing : ∀ i, code.encode i ≠ w ++ [!b]) :
    expectedCodeLength p (code.pruneDeepest a w b hw ha hmax hmissing) =
      expectedCodeLength p code - p a := by
  rw [BinaryPrefixCode.pruneDeepest, expectedCodeLength_replaceWord, ha]
  simp only [List.length_append, List.length_singleton, Nat.cast_add, Nat.cast_one]
  ring

/-- Pruning remains cost-nonincreasing when the removed symbol has zero mass. -/
theorem expectedCodeLength_pruneDeepest_le
    {α : Type*} [Fintype α] [DecidableEq α] (p : α → ℝ)
    (code : BinaryPrefixCode α) (a : α) (w : List Bool) (b : Bool)
    (hp : 0 ≤ p a) (hw : w ≠ []) (ha : code.encode a = w ++ [b])
    (hmax : ∀ i, (code.encode i).length ≤ (code.encode a).length)
    (hmissing : ∀ i, code.encode i ≠ w ++ [!b]) :
    expectedCodeLength p (code.pruneDeepest a w b hw ha hmax hmissing) ≤ expectedCodeLength p code := by
  rw [expectedCodeLength_pruneDeepest]
  linarith

end BanditRLProof.LowerBounds
