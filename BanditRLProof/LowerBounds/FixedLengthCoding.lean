import BanditRLProof.LowerBounds.DyadicAddresses
import Mathlib.Data.Nat.Log

namespace BanditRLProof.LowerBounds

/-- A finite alphabet fitting in n bits has an actual fixed-length prefix code. -/
theorem exists_fixedLengthPrefixCode {α : Type*} [Fintype α] (n : ℕ)
    (hn : 0 < n) (hcapacity : Fintype.card α ≤ 2 ^ n) :
    ∃ code : BinaryPrefixCode α, ∀ a, (code.encode a).length = n := by
  classical
  let e := Fintype.equivFin α
  have hex (a : α) := exists_binaryAddress n (e a).val ((e a).isLt.trans_le hcapacity)
  choose c hc hv using hex
  have hinj : Function.Injective c := by
    intro a b h
    apply e.injective
    apply Fin.ext
    have he := congrArg binaryAddressValue h
    simpa [hv] using he
  let code : BinaryPrefixCode α := {
    encode := c
    injective := hinj
    nonempty := by
      intro a he
      have h := hc a
      simp [he] at h
      omega
    prefixFree := by
      intro a b h
      exact hinj (h.eq_of_length ((hc a).trans (hc b).symm)) }
  exact ⟨code, hc⟩

/-- The source's ceiling-log binary code, for at least two symbols. -/
theorem exists_ceilingLogPrefixCode {α : Type*} [Fintype α]
    (hcard : 1 < Fintype.card α) :
    ∃ code : BinaryPrefixCode α, ∀ a, (code.encode a).length = Nat.clog 2 (Fintype.card α) := by
  have hcap := Nat.le_pow_clog (by norm_num : 1 < 2) (Fintype.card α)
  have hn : 0 < Nat.clog 2 (Fintype.card α) := by
    by_contra h
    have hz : Nat.clog 2 (Fintype.card α) = 0 := by omega
    simp [hz] at hcap
    omega
  exact exists_fixedLengthPrefixCode _ hn hcap

theorem expectedCodeLength_fixedLength {α : Type*} [Fintype α] (p : α → ℝ)
    (hs : ∑ a, p a = 1) (code : BinaryPrefixCode α) (n : ℕ)
    (hlen : ∀ a, (code.encode a).length = n) : expectedCodeLength p code = n := by
  simp only [expectedCodeLength, hlen, ← Finset.sum_mul, hs, one_mul]

end BanditRLProof.LowerBounds
