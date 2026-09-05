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

/-- Structural termination measure, independent of source probabilities. -/
def totalCodeLength {α : Type*} [Fintype α] (code : BinaryPrefixCode α) : ℕ :=
  ∑ i, (code.encode i).length

theorem totalCodeLength_pruneDeepest
    {α : Type*} [Fintype α] [DecidableEq α]
    (code : BinaryPrefixCode α) (a : α) (w : List Bool) (b : Bool)
    (hw : w ≠ []) (ha : code.encode a = w ++ [b])
    (hmax : ∀ i, (code.encode i).length ≤ (code.encode a).length)
    (hmissing : ∀ i, code.encode i ≠ w ++ [!b]) :
    totalCodeLength (code.pruneDeepest a w b hw ha hmax hmissing) + 1 = totalCodeLength code := by
  have h := expectedCodeLength_pruneDeepest (fun _ => (1 : ℝ)) code a w b hw ha hmax hmissing
  simp only [expectedCodeLength, one_mul] at h
  have he : (∑ i, (((code.pruneDeepest a w b hw ha hmax hmissing).encode i).length : ℝ)) + 1 =
      ∑ i, ((code.encode i).length : ℝ) := by linarith
  exact_mod_cast he

/-- Choose a structurally minimal no-worse competitor without assuming cost-minimizer existence. -/
theorem exists_minimal_totalCodeLength_competitor
    {α : Type*} [Fintype α] (p : α → ℝ) (original : BinaryPrefixCode α) :
    ∃ code : BinaryPrefixCode α,
      expectedCodeLength p code ≤ expectedCodeLength p original ∧
      ∀ other : BinaryPrefixCode α,
        expectedCodeLength p other ≤ expectedCodeLength p original →
          totalCodeLength code ≤ totalCodeLength other := by
  classical
  let P : ℕ → Prop := fun n => ∃ code : BinaryPrefixCode α,
    expectedCodeLength p code ≤ expectedCodeLength p original ∧ totalCodeLength code = n
  have hex : ∃ n, P n := ⟨totalCodeLength original, original, le_rfl, rfl⟩
  obtain ⟨code, hc, hn⟩ := Nat.find_spec hex
  refine ⟨code, hc, ?_⟩
  intro other ho
  rw [hn]
  exact Nat.find_min' hex ⟨other, ho, rfl⟩

/-- Normalize any competitor so that each deepest leaf has its sibling present. -/
theorem exists_competitor_with_deepest_siblings
    {α : Type*} [Fintype α] [DecidableEq α] [Nontrivial α]
    (p : α → ℝ) (hp : ∀ i, 0 ≤ p i) (original : BinaryPrefixCode α) :
    ∃ code : BinaryPrefixCode α,
      expectedCodeLength p code ≤ expectedCodeLength p original ∧
      ∀ a w b, code.encode a = w ++ [b] →
        (∀ i, (code.encode i).length ≤ (code.encode a).length) →
          ∃ j, code.encode j = w ++ [!b] := by
  classical
  obtain ⟨code, hc, hmin⟩ := exists_minimal_totalCodeLength_competitor p original
  refine ⟨code, hc, ?_⟩
  intro a w b ha hmax
  by_contra h
  have hmissing : ∀ j, code.encode j ≠ w ++ [!b] := by simpa using h
  have hw : w ≠ [] := by
    intro he
    obtain ⟨i, hi⟩ := exists_ne a
    have hn := (deepest_parent_incomparable code a w b ha hmax hmissing i hi).2
    apply hn
    simp [he]
  have hcost := expectedCodeLength_pruneDeepest_le p code a w b (hp a) hw ha hmax hmissing
  have hbound := hmin (code.pruneDeepest a w b hw ha hmax hmissing) (hcost.trans hc)
  have hdrop := totalCodeLength_pruneDeepest code a w b hw ha hmax hmissing
  omega

/-- Every competitor has a no-worse code containing a deepest sibling pair. -/
theorem exists_no_worse_deepest_sibling_pair
    {α : Type*} [Fintype α] [DecidableEq α] [Nontrivial α]
    (p : α → ℝ) (hp : ∀ i, 0 ≤ p i) (original : BinaryPrefixCode α) :
    ∃ code : BinaryPrefixCode α, expectedCodeLength p code ≤ expectedCodeLength p original ∧
      ∃ a j w b, a ≠ j ∧ code.encode a = w ++ [b] ∧ code.encode j = w ++ [!b] ∧
        ∀ i, (code.encode i).length ≤ (code.encode a).length := by
  obtain ⟨code, hc, hf⟩ := exists_competitor_with_deepest_siblings p hp original
  obtain ⟨a, _, hmax⟩ := (Finset.univ : Finset α).exists_max_image
    (fun i => (code.encode i).length) Finset.univ_nonempty
  have hsplit : ∀ v : List Bool, v ≠ [] → ∃ w b, v = w ++ [b] := by
    intro v
    induction v using List.reverseRecOn with
    | nil => simp
    | append_singleton w b _ => exact fun _ => ⟨w, b, rfl⟩
  obtain ⟨w, b, ha⟩ := hsplit (code.encode a) (code.nonempty a)
  have hm : ∀ i, (code.encode i).length ≤ (code.encode a).length :=
    fun i => hmax i (Finset.mem_univ i)
  obtain ⟨j, hj⟩ := hf a w b ha hm
  have haj : a ≠ j := by
    intro he
    have hwords : w ++ [b] = w ++ [!b] := ha.symm.trans (he ▸ hj)
    have hb := List.append_cancel_left hwords
    cases b <;> simp at hb
  exact ⟨code, hc, a, j, w, b, haj, ha, hj, hm⟩

end BanditRLProof.LowerBounds
