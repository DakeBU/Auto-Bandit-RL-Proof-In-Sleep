import BanditRLProof.LowerBounds.PrefixCodeGreedy

namespace BanditRLProof.LowerBounds

/-- Orient an actual pair of sibling leaves without changing its cost. -/
theorem exists_oriented_sibling_code
    {α : Type*} [Fintype α] [DecidableEq α] (p : α ⊕ Bool → ℝ)
    (code : BinaryPrefixCode (α ⊕ Bool)) (w : List Bool) (bit : Bool)
    (hf : code.encode (.inr false) = w ++ [bit])
    (ht : code.encode (.inr true) = w ++ [!bit]) :
    ∃ other : BinaryPrefixCode (α ⊕ Bool), expectedCodeLength p other = expectedCodeLength p code ∧
      ∀ b, other.encode (.inr b) = w ++ [b] := by
  cases bit with
  | false =>
    refine ⟨code, rfl, ?_⟩
    intro b
    cases b
    · exact hf
    · exact ht
  | true =>
    let other := code.relabel (Equiv.swap (.inr false) (.inr true))
    refine ⟨other, ?_, ?_⟩
    · rw [expectedCodeLength_swap p code (.inr false) (.inr true) (by simp)]
      simp [hf, ht]
    · intro b
      cases b <;> simp [other, BinaryPrefixCode.relabel, hf, ht]

/-- The Huffman induction step: expanding an optimal merged code is globally
optimal when the split symbols are the two least weights. -/
theorem IsOptimalPrefixCode.expand_least_weights
    {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α]
    (p : α → ℝ) (q r : ℝ) (hp : ∀ i, 0 ≤ p i) (hq : 0 ≤ q)
    (hqr : q ≤ r) (hr : ∀ i, r ≤ p i)
    (code : BinaryPrefixCode (Option α))
    (hopt : IsOptimalPrefixCode (fun a => a.elim (q + r) p) code) :
    IsOptimalPrefixCode (Sum.elim p (fun b => if b then r else q)) code.expandSibling := by
  letI : Nontrivial (α ⊕ Bool) := ⟨⟨.inr false, .inr true, by simp⟩⟩
  let mass : α ⊕ Bool → ℝ := Sum.elim p (fun b => if b then r else q)
  have hmass : ∀ i, 0 ≤ mass i := by
    intro i
    cases i with
    | inl i => exact hp i
    | inr b => cases b <;> simp [mass] <;> linarith
  have hmin : ∀ i, mass (.inr false) ≤ mass i := by
    intro i
    cases i with
    | inl i => exact hqr.trans (hr i)
    | inr b => cases b <;> simp [mass, hqr]
  have hsecond : ∀ i, i ≠ .inr false → mass (.inr true) ≤ mass i := by
    intro i hi
    cases i with
    | inl i => exact hr i
    | inr b => cases b <;> simp_all [mass]
  intro original
  obtain ⟨c, hc, w, bit, hf, ht, _⟩ := exists_no_worse_least_weight_siblings
    mass hmass original (.inr false) (.inr true) (by simp) hmin hsecond
  obtain ⟨d, hd, hs⟩ := exists_oriented_sibling_code mass c w bit hf ht
  have hw : w ≠ [] := by
    intro he
    obtain ⟨a⟩ := ‹Nonempty α›
    have hn := sibling_parent_not_prefix_other d w hs a
    apply hn
    simp [he]
  have hcontract := expectedCodeLength_contractSibling d w hw hs p q r
  have hbound := hopt (d.contractSibling w hw hs)
  rw [expectedCodeLength_expandSibling]
  change expectedCodeLength mass d = expectedCodeLength mass c at hd
  change _ = expectedCodeLength mass d at hcontract
  linarith

end BanditRLProof.LowerBounds
