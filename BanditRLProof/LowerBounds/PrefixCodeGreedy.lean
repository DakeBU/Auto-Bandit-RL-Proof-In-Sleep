import BanditRLProof.LowerBounds.PrefixCodePruning

namespace BanditRLProof.LowerBounds

/-- The exchange bound also permits an already correctly placed label. -/
theorem expectedCodeLength_swap_le_allow_eq
    {α : Type*} [Fintype α] [DecidableEq α] (p : α → ℝ) (code : BinaryPrefixCode α)
    (a b : α) (hp : p a ≤ p b)
    (hl : (code.encode a).length ≤ (code.encode b).length) :
    expectedCodeLength p (code.relabel (Equiv.swap a b)) ≤ expectedCodeLength p code := by
  by_cases hab : a = b
  · subst b
    simp [expectedCodeLength, BinaryPrefixCode.relabel]
  · exact expectedCodeLength_swap_le p code a b hab hp hl

/-- Huffman's greedy choice: any competitor can place two specified least weights
at deepest sibling leaves without increasing expected length. Ties and zero weights
are permitted, and no existence of an optimal code is assumed. -/
theorem exists_no_worse_least_weight_siblings
    {α : Type*} [Fintype α] [DecidableEq α] [Nontrivial α]
    (p : α → ℝ) (hp : ∀ i, 0 ≤ p i) (original : BinaryPrefixCode α)
    (a b : α) (hab : a ≠ b) (ha : ∀ i, p a ≤ p i)
    (hb : ∀ i, i ≠ a → p b ≤ p i) :
    ∃ code : BinaryPrefixCode α, expectedCodeLength p code ≤ expectedCodeLength p original ∧
      ∃ w bit, code.encode a = w ++ [bit] ∧ code.encode b = w ++ [!bit] ∧
        ∀ i, (code.encode i).length ≤ (code.encode a).length := by
  obtain ⟨c, hc, x, y, w, bit, hxy, hx, hy, hm⟩ :=
    exists_no_worse_deepest_sibling_pair p hp original
  let c₁ := c.relabel (Equiv.swap a x)
  let y₁ := Equiv.swap a x y
  have hc₁ : expectedCodeLength p c₁ ≤ expectedCodeLength p c :=
    expectedCodeLength_swap_le_allow_eq p c a x (ha x) (hm a)
  have h₁a : c₁.encode a = c.encode x := by simp [c₁, BinaryPrefixCode.relabel]
  have h₁y : c₁.encode y₁ = c.encode y := by
    simp [c₁, y₁, BinaryPrefixCode.relabel]
  have hya : y₁ ≠ a := by
    intro he
    have he' := congrArg (Equiv.swap a x) he
    have : y = x := by simpa [y₁] using he'
    exact hxy this.symm
  have hlen : (c.encode y).length = (c.encode x).length := by simp [hx, hy]
  have hm₁ (i : α) : (c₁.encode i).length ≤ (c₁.encode y₁).length := by
    rw [h₁y, hlen]
    exact hm (Equiv.swap a x i)
  let c₂ := c₁.relabel (Equiv.swap b y₁)
  have hc₂ : expectedCodeLength p c₂ ≤ expectedCodeLength p c₁ :=
    expectedCodeLength_swap_le_allow_eq p c₁ b y₁ (hb y₁ hya) (hm₁ b)
  have h₂a : c₂.encode a = c.encode x := by
    simpa [c₂, BinaryPrefixCode.relabel, Equiv.swap_apply_of_ne_of_ne hab hya.symm] using h₁a
  have h₂b : c₂.encode b = c.encode y := by
    simpa [c₂, BinaryPrefixCode.relabel] using h₁y
  refine ⟨c₂, hc₂.trans (hc₁.trans hc), w, bit, h₂a.trans hx, h₂b.trans hy, ?_⟩
  intro i
  rw [h₂a]
  exact hm (Equiv.swap a x (Equiv.swap b y₁ i))

end BanditRLProof.LowerBounds
