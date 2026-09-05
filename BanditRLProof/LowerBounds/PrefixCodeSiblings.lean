import BanditRLProof.LowerBounds.PrefixCodeExchange

namespace BanditRLProof.LowerBounds

theorem BinaryPrefixCode.extended_prefix_parent_eq
    {α : Type*} (code : BinaryPrefixCode α) (a b : α) (u v : List Bool)
    (h : code.encode a ++ u <+: code.encode b ++ v) : a = b := by
  have ha := (List.prefix_append (code.encode a) u).trans h
  have hb := List.prefix_append (code.encode b) v
  rcases List.prefix_or_prefix_of_prefix ha hb with hab | hba
  · exact code.prefixFree hab
  · exact (code.prefixFree hba).symm

def siblingExpandedWord {α : Type*} (code : BinaryPrefixCode (Option α)) : α ⊕ Bool → List Bool
  | .inl a => code.encode (some a)
  | .inr b => code.encode none ++ [b]

theorem siblingExpandedWord_prefixFree {α : Type*} (code : BinaryPrefixCode (Option α))
    {a b : α ⊕ Bool} (h : siblingExpandedWord code a <+: siblingExpandedWord code b) : a = b := by
  cases a with
  | inl a =>
    cases b with
    | inl b =>
      have he := code.prefixFree h
      exact congrArg Sum.inl (Option.some.inj he)
    | inr b =>
      have he := code.extended_prefix_parent_eq (some a) none [] [b] (by simpa [siblingExpandedWord] using h)
      contradiction
  | inr a =>
    cases b with
    | inl b =>
      have he := code.extended_prefix_parent_eq none (some b) [a] [] (by simpa [siblingExpandedWord] using h)
      contradiction
    | inr b =>
      change code.encode none ++ [a] <+: code.encode none ++ [b] at h
      obtain ⟨t, ht⟩ := h
      have hlen := congrArg List.length ht
      simp only [List.length_append, List.length_singleton] at hlen
      have ht0 : t = [] := List.length_eq_zero_iff.mp (by omega)
      simp only [ht0, List.append_nil] at ht
      have he := List.append_cancel_left ht
      simp only [List.singleton_inj] at he
      exact congrArg Sum.inr he

/-- Split a designated merged leaf into two siblings. -/
def BinaryPrefixCode.expandSibling {α : Type*} (code : BinaryPrefixCode (Option α)) :
    BinaryPrefixCode (α ⊕ Bool) where
  encode := siblingExpandedWord code
  injective := fun a b h => siblingExpandedWord_prefixFree code (by rw [h])
  nonempty := by
    intro a
    cases a with
    | inl a => exact code.nonempty (some a)
    | inr b => simp [siblingExpandedWord]
  prefixFree := siblingExpandedWord_prefixFree code

/-- Exact cost recurrence of splitting a merged symbol. -/
theorem expectedCodeLength_expandSibling
    {α : Type*} [Fintype α] (code : BinaryPrefixCode (Option α))
    (p : α → ℝ) (q r : ℝ) :
    expectedCodeLength (Sum.elim p (fun b => if b then r else q)) code.expandSibling =
      expectedCodeLength (fun a => a.elim (q + r) p) code + q + r := by
  simp [expectedCodeLength, BinaryPrefixCode.expandSibling, siblingExpandedWord,
    Fintype.sum_sum_type, Fintype.sum_option, Nat.cast_add, Nat.cast_one]
  ring

theorem sibling_parent_not_prefix_other
    {α : Type*} (code : BinaryPrefixCode (α ⊕ Bool)) (w : List Bool)
    (hs : ∀ b, code.encode (.inr b) = w ++ [b]) (a : α) :
    ¬ w <+: code.encode (.inl a) := by
  rintro ⟨t, ht⟩
  cases t with
  | nil =>
    have he : w = code.encode (.inl a) := by simpa using ht
    have hp : code.encode (.inl a) <+: code.encode (.inr false) := by
      rw [hs false, ← he]
      exact List.prefix_append _ _
    have h := code.prefixFree hp
    contradiction
  | cons b t =>
    have hp : code.encode (.inr b) <+: code.encode (.inl a) := by
      rw [hs b]
      exact ⟨t, by simpa [List.append_assoc] using ht⟩
    have h := code.prefixFree hp
    contradiction

def siblingContractedWord {α : Type*} (code : BinaryPrefixCode (α ⊕ Bool)) (w : List Bool) :
    Option α → List Bool
  | none => w
  | some a => code.encode (.inl a)

theorem siblingContractedWord_prefixFree
    {α : Type*} (code : BinaryPrefixCode (α ⊕ Bool)) (w : List Bool)
    (hs : ∀ b, code.encode (.inr b) = w ++ [b]) {a b : Option α}
    (h : siblingContractedWord code w a <+: siblingContractedWord code w b) : a = b := by
  cases a with
  | none =>
    cases b with
    | none => rfl
    | some b => exact (sibling_parent_not_prefix_other code w hs b h).elim
  | some a =>
    cases b with
    | none =>
      have hp : code.encode (.inl a) <+: code.encode (.inr false) := by
        rw [hs false]
        exact h.trans (List.prefix_append _ _)
      have he := code.prefixFree hp
      contradiction
    | some b =>
      exact congrArg some (Sum.inl.inj (code.prefixFree h))

/-- Merge two actual sibling leaves whose parent is nonempty. -/
def BinaryPrefixCode.contractSibling
    {α : Type*} (code : BinaryPrefixCode (α ⊕ Bool)) (w : List Bool) (hw : w ≠ [])
    (hs : ∀ b, code.encode (.inr b) = w ++ [b]) : BinaryPrefixCode (Option α) where
  encode := siblingContractedWord code w
  injective := fun a b h => siblingContractedWord_prefixFree code w hs (by rw [h])
  nonempty := by
    intro a
    cases a with
    | none => exact hw
    | some a => exact code.nonempty (.inl a)
  prefixFree := siblingContractedWord_prefixFree code w hs

theorem expectedCodeLength_contractSibling
    {α : Type*} [Fintype α] (code : BinaryPrefixCode (α ⊕ Bool))
    (w : List Bool) (hw : w ≠ []) (hs : ∀ b, code.encode (.inr b) = w ++ [b])
    (p : α → ℝ) (q r : ℝ) :
    expectedCodeLength (fun a => a.elim (q + r) p) (code.contractSibling w hw hs) + q + r =
      expectedCodeLength (Sum.elim p (fun b => if b then r else q)) code := by
  simp [expectedCodeLength, BinaryPrefixCode.contractSibling, siblingContractedWord,
    Fintype.sum_sum_type, Fintype.sum_option, hs, Nat.cast_add, Nat.cast_one]
  ring

/-- The two-symbol root code, avoiding an invalid empty parent codeword. -/
def binaryRootPrefixCode : BinaryPrefixCode Bool where
  encode := fun b => [b]
  injective := fun _ _ h => List.singleton_inj.mp h
  nonempty := fun _ => by simp
  prefixFree := by
    intro a b h
    cases a <;> cases b <;> simp_all

theorem binaryRootPrefixCode_optimal (p : Bool → ℝ)
    (hp : ∀ b, 0 ≤ p b) (hs : ∑ b, p b = 1) :
    IsOptimalPrefixCode p binaryRootPrefixCode := by
  intro other
  have he : expectedCodeLength p binaryRootPrefixCode = 1 := by
    simpa [expectedCodeLength, binaryRootPrefixCode] using hs
  rw [he]
  exact one_le_expectedCodeLength p hp hs other

end BanditRLProof.LowerBounds
