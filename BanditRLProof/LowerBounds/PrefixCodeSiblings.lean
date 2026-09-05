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

end BanditRLProof.LowerBounds
