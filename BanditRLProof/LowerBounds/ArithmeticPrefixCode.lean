import BanditRLProof.LowerBounds.DyadicAddresses

namespace BanditRLProof.LowerBounds

theorem arithmeticAddress_prefix_forces_eq {k : ℕ} (p : Fin k → ℝ)
    (hp : ∀ i, 0 ≤ p i) (hs : ∑ i, p i = 1)
    (u v : List (Fin k)) (hlen : u.length = v.length) (cu cv : List Bool)
    (huL : (arithmeticInterval p u).1 ≤ dyadicAddressLower cu)
    (huU : dyadicAddressUpper cu < (arithmeticInterval p u).2)
    (hvL : (arithmeticInterval p v).1 ≤ dyadicAddressLower cv)
    (hvU : dyadicAddressUpper cv < (arithmeticInterval p v).2)
    (hprefix : cu <+: cv) : u = v := by
  have hc := dyadicAddress_prefix_contained cu cv hprefix
  have hn := dyadicAddress_nonempty cv
  apply arithmeticInterval_interior_unique p hp hs u v hlen
    ((dyadicAddressLower cv + dyadicAddressUpper cv) / 2)
  · constructor <;> linarith
  · constructor <;> linarith

/-- Assemble arithmetic-cell addresses into a genuine prefix code, preserving
the supplied bit lengths. The width budgets are discharged by later allocation. -/
theorem exists_arithmeticPrefixCode {α : Type*} {k : ℕ} (p : Fin k → ℝ)
    (hp : ∀ i, 0 ≤ p i) (hs : ∑ i, p i = 1)
    (message : α → List (Fin k)) (hinj : Function.Injective message)
    (hlen : ∀ a b, (message a).length = (message b).length) (bits : α → ℕ)
    (hbudget : ∀ a, 2 * (1 / (2 : ℝ) ^ bits a) ≤
      (arithmeticInterval p (message a)).2 - (arithmeticInterval p (message a)).1) :
    ∃ code : BinaryPrefixCode α,
      (∀ a, (code.encode a).length = bits a) ∧
      ∀ a, (arithmeticInterval p (message a)).1 ≤ dyadicAddressLower (code.encode a) ∧
        dyadicAddressUpper (code.encode a) < (arithmeticInterval p (message a)).2 := by
  classical
  have hex (a : α) := exists_dyadicAddress_inside
    (arithmeticInterval p (message a)).1 (arithmeticInterval p (message a)).2 (bits a)
    (arithmeticInterval_bounds p hp hs (message a)).1
    (arithmeticInterval_bounds p hp hs (message a)).2.2 (hbudget a)
  choose c hc hcL hcU using hex
  have hfree {a b : α} (h : c a <+: c b) : a = b := by
    apply hinj
    exact arithmeticAddress_prefix_forces_eq p hp hs (message a) (message b) (hlen a b)
      (c a) (c b) (hcL a) (hcU a) (hcL b) (hcU b) h
  have hnonempty (a : α) : c a ≠ [] := by
    intro he
    have hu := hcU a
    have hb := (arithmeticInterval_bounds p hp hs (message a)).2.2
    simp [he, dyadicAddressUpper, binaryAddressValue] at hu
    linarith
  let code : BinaryPrefixCode α := {
    encode := c
    injective := fun a b h => hfree (by rw [h])
    nonempty := hnonempty
    prefixFree := hfree }
  exact ⟨code, hc, fun a => ⟨hcL a, hcU a⟩⟩

/-- One extra bit beyond strict Shannon length fits a dyadic cell inside the
arithmetic interval, rather than merely meeting a Kraft budget. -/
noncomputable def arithmeticLength (mass : ℝ) : ℕ := shannonLength mass + 1

theorem arithmeticLength_width_budget {mass : ℝ} (hm : 0 < mass) :
    2 * (1 / (2 : ℝ) ^ arithmeticLength mass) < mass := by
  have h := shannonLength_kraft_weight_lt hm
  have he : 2 * (1 / (2 : ℝ) ^ arithmeticLength mass) = (1 / 2 : ℝ) ^ shannonLength mass := by
    simp only [arithmeticLength, pow_succ, div_pow, one_pow]
    field_simp
  rw [he]
  exact h

theorem arithmeticLength_le_information_add_two {mass : ℝ}
    (hm : 0 < mass) (hm1 : mass ≤ 1) :
    (arithmeticLength mass : ℝ) ≤ Real.log mass⁻¹ / Real.log 2 + 2 := by
  have h := shannonLength_le_information_add_one hm hm1
  simp only [arithmeticLength, Nat.cast_add, Nat.cast_one]
  linarith

end BanditRLProof.LowerBounds
