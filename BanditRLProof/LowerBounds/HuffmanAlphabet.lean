import BanditRLProof.LowerBounds.HuffmanStep

namespace BanditRLProof.LowerBounds

theorem expectedCodeLength_relabel
    {α β : Type*} [Fintype α] [Fintype β] (p : α → ℝ)
    (code : BinaryPrefixCode α) (e : β ≃ α) :
    expectedCodeLength (p ∘ e) (code.relabel e) = expectedCodeLength p code := by
  exact e.sum_comp (fun i => p i * (code.encode i).length)

/-- Global optimality is independent of the names of the alphabet symbols. -/
theorem IsOptimalPrefixCode.relabel
    {α β : Type*} [Fintype α] [Fintype β] (p : α → ℝ)
    (code : BinaryPrefixCode α) (e : β ≃ α) (hopt : IsOptimalPrefixCode p code) :
    IsOptimalPrefixCode (p ∘ e) (code.relabel e) := by
  intro other
  rw [expectedCodeLength_relabel]
  have ho := hopt (other.relabel e.symm)
  have he := expectedCodeLength_relabel (p ∘ e) other e.symm
  have hp : (p ∘ e) ∘ e.symm = p := by funext i; simp
  rw [hp] at he
  exact ho.trans_eq he

/-- The unmerged symbols, retaining their original labels. -/
def HuffmanRemainder {α : Type*} (a b : α) := {i : α // i ≠ a ∧ i ≠ b}

instance {α : Type*} [Fintype α] [DecidableEq α] (a b : α) :
    Fintype (HuffmanRemainder a b) := inferInstanceAs (Fintype {i : α // i ≠ a ∧ i ≠ b})

/-- Separate two selected symbols as the false and true leaves. -/
def huffmanSplitEquiv {α : Type*} [DecidableEq α] (a b : α) (hab : a ≠ b) :
    HuffmanRemainder a b ⊕ Bool ≃ α where
  toFun := Sum.elim Subtype.val (fun bit => if bit then b else a)
  invFun i := if ha : i = a then .inr false else
    if hb : i = b then .inr true else .inl ⟨i, ha, hb⟩
  left_inv := by
    intro i
    cases i with
    | inl i => simp [i.property.1, i.property.2]
    | inr bit => cases bit <;> simp [hab.symm]
  right_inv := by
    intro i
    by_cases ha : i = a
    · simp [ha]
    · by_cases hb : i = b
      · simp [hb, hab.symm]
      · simp [ha, hb]

@[simp] theorem huffmanSplitEquiv_false {α : Type*} [DecidableEq α]
    (a b : α) (hab : a ≠ b) : huffmanSplitEquiv a b hab (.inr false) = a := rfl

@[simp] theorem huffmanSplitEquiv_true {α : Type*} [DecidableEq α]
    (a b : α) (hab : a ≠ b) : huffmanSplitEquiv a b hab (.inr true) = b := rfl

/-- Merging two distinct symbols reduces the recursive alphabet size by one. -/
theorem huffman_merged_card_lt {α : Type*} [Fintype α] [DecidableEq α]
    (a b : α) (hab : a ≠ b) :
    Fintype.card (Option (HuffmanRemainder a b)) < Fintype.card α := by
  have hc := Fintype.card_congr (huffmanSplitEquiv a b hab)
  simp only [Fintype.card_sum, Fintype.card_bool] at hc
  simp only [Fintype.card_option]
  omega

/-- A finite nontrivial alphabet has two least weights, including ties. -/
theorem exists_two_least_weights {α : Type*} [Fintype α] [DecidableEq α] [Nontrivial α]
    (p : α → ℝ) : ∃ a b, a ≠ b ∧ (∀ i, p a ≤ p i) ∧ (∀ i, i ≠ a → p b ≤ p i) := by
  obtain ⟨a, _, ha⟩ := (Finset.univ : Finset α).exists_min_image p Finset.univ_nonempty
  have hn : ((Finset.univ : Finset α).erase a).Nonempty := by
    obtain ⟨b, hb⟩ := exists_ne a
    exact ⟨b, Finset.mem_erase.mpr ⟨hb, Finset.mem_univ b⟩⟩
  obtain ⟨b, hb, hmin⟩ := ((Finset.univ : Finset α).erase a).exists_min_image p hn
  refine ⟨a, b, (Finset.mem_erase.mp hb).1.symm, fun i => ha i (Finset.mem_univ i), ?_⟩
  intro i hi
  exact hmin i (Finset.mem_erase.mpr ⟨hi, Finset.mem_univ i⟩)

end BanditRLProof.LowerBounds
