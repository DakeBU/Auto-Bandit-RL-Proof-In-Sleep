import BanditRLProof.LowerBounds.HuffmanAlphabet

namespace BanditRLProof.LowerBounds

theorem oneBitCode_optimal {α : Type*} [Fintype α] (p : α → ℝ)
    (hp : ∀ i, 0 ≤ p i) (code : BinaryPrefixCode α)
    (hlen : ∀ i, (code.encode i).length = 1) : IsOptimalPrefixCode p code := by
  intro other
  apply Finset.sum_le_sum
  intro i _
  rw [hlen]
  have hn : 1 ≤ (other.encode i).length := by
    have hz : (other.encode i).length ≠ 0 := by
      intro he
      exact other.nonempty i (List.length_eq_zero_iff.mp he)
    omega
  exact mul_le_mul_of_nonneg_left (by exact_mod_cast hn) (hp i)

def emptyRemainderRoot {α : Type*} [IsEmpty α] : BinaryPrefixCode (α ⊕ Bool) where
  encode := Sum.elim isEmptyElim (fun b => [b])
  injective := by
    intro a b h
    cases a with
    | inl a => exact isEmptyElim a
    | inr a =>
      cases b with
      | inl b => exact isEmptyElim b
      | inr b => exact congrArg Sum.inr (List.singleton_inj.mp h)
  nonempty := by
    intro i
    cases i with
    | inl i => exact isEmptyElim i
    | inr b => simp
  prefixFree := by
    intro a b h
    cases a with
    | inl a => exact isEmptyElim a
    | inr a =>
      cases b with
      | inl b => exact isEmptyElim b
      | inr b =>
        have he := binaryRootPrefixCode.prefixFree h
        exact congrArg Sum.inr he

/-- Huffman's recursive merge-two-least construction, with its correctness proof.
Real-weight choices are classical; the code itself is assembled recursively. -/
noncomputable def huffmanOptimalCode {α : Type*} [Fintype α]
    (p : α → ℝ) (hp : ∀ i, 0 ≤ p i) : {code : BinaryPrefixCode α // IsOptimalPrefixCode p code} := by
  classical
  by_cases hsmall : Subsingleton α
  · letI := hsmall
    exact ⟨singletonPrefixCode α, oneBitCode_optimal p hp _ (fun _ => rfl)⟩
  · letI : Nontrivial α := not_subsingleton_iff_nontrivial.mp hsmall
    let a := Classical.choose (exists_two_least_weights p)
    let b := Classical.choose (Classical.choose_spec (exists_two_least_weights p))
    have hpair := Classical.choose_spec (Classical.choose_spec (exists_two_least_weights p))
    have hab : a ≠ b := hpair.1
    let β := HuffmanRemainder a b
    let e := huffmanSplitEquiv a b hab
    let mass : β ⊕ Bool → ℝ := Sum.elim (fun i => p i.val) (fun bit => if bit then p b else p a)
    have hmass : mass = p ∘ e := by
      funext i
      cases i with
      | inl i => rfl
      | inr bit => cases bit <;> rfl
    by_cases hempty : IsEmpty β
    · letI := hempty
      let root : BinaryPrefixCode (β ⊕ Bool) := emptyRemainderRoot
      have ho : IsOptimalPrefixCode mass root := oneBitCode_optimal mass
        (fun i => by rw [hmass]; exact hp (e i)) root (by
          intro i
          cases i with
          | inl i => exact isEmptyElim i
          | inr bit => rfl)
      refine ⟨root.relabel e.symm, ?_⟩
      have h := ho.relabel mass root e.symm
      simpa [hmass, Function.comp_def] using h
    · letI : Nonempty β := not_isEmpty_iff.mp hempty
      let merged : Option β → ℝ := fun i => i.elim (p a + p b) (fun j => p j.val)
      have hm : ∀ i, 0 ≤ merged i := by
        intro i
        cases i with
        | none => exact add_nonneg (hp a) (hp b)
        | some i => exact hp i.val
      let smaller := huffmanOptimalCode merged hm
      have ho : IsOptimalPrefixCode mass smaller.val.expandSibling :=
        smaller.property.expand_least_weights (fun i : β => p i.val) (p a) (p b)
          (fun i => hp i.val) (hp a) (hpair.2.1 b)
          (fun i => hpair.2.2 i.val i.property.1) smaller.val
      refine ⟨smaller.val.expandSibling.relabel e.symm, ?_⟩
      have h := ho.relabel mass smaller.val.expandSibling e.symm
      simpa [hmass, Function.comp_def] using h
termination_by Fintype.card α
decreasing_by
  classical
  exact huffman_merged_card_lt a b hab

/-- The prefix code produced by recursive Huffman merging. -/
noncomputable def huffmanCode {α : Type*} [Fintype α]
    (p : α → ℝ) (hp : ∀ i, 0 ≤ p i) : BinaryPrefixCode α :=
  (huffmanOptimalCode p hp).val

theorem huffmanCode_optimal {α : Type*} [Fintype α]
    (p : α → ℝ) (hp : ∀ i, 0 ≤ p i) : IsOptimalPrefixCode p (huffmanCode p hp) :=
  (huffmanOptimalCode p hp).property

/-- Chapter 14, Eq. (14.2), for the recursively constructed Huffman code. -/
theorem huffmanCode_entropy_sandwich {α : Type*} [Fintype α]
    (p : α → ℝ) (hp : ∀ i, 0 ≤ p i) (hs : ∑ i, p i = 1) :
    discreteEntropyBaseTwo Finset.univ p ≤ expectedCodeLength p (huffmanCode p hp) ∧
      expectedCodeLength p (huffmanCode p hp) ≤ discreteEntropyBaseTwo Finset.univ p + 1 := by
  classical
  exact (huffmanCode_optimal p hp).entropy_sandwich hp hs

end BanditRLProof.LowerBounds
