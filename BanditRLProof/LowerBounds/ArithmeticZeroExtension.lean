import BanditRLProof.LowerBounds.ArithmeticPrefixCode
import BanditRLProof.LowerBounds.HuffmanConstruction

namespace BanditRLProof.LowerBounds

noncomputable def supportTaggedWord {α : Type*} (p : α → ℝ)
    (positive : BinaryPrefixCode {a // 0 < p a}) (fallback : BinaryPrefixCode α)
    (a : α) : List Bool := by
  classical
  exact if h : 0 < p a then false :: positive.encode ⟨a, h⟩ else true :: fallback.encode a

theorem supportTaggedWord_prefixFree {α : Type*} (p : α → ℝ)
    (positive : BinaryPrefixCode {a // 0 < p a}) (fallback : BinaryPrefixCode α)
    {a b : α} (h : supportTaggedWord p positive fallback a <+:
      supportTaggedWord p positive fallback b) : a = b := by
  classical
  by_cases ha : 0 < p a <;> by_cases hb : 0 < p b
  · simp only [supportTaggedWord, dif_pos ha, dif_pos hb, List.cons_prefix_cons] at h
    exact congrArg Subtype.val (positive.prefixFree h.2)
  · simp [supportTaggedWord, ha, hb, List.cons_prefix_cons] at h
  · simp [supportTaggedWord, ha, hb, List.cons_prefix_cons] at h
  · simp only [supportTaggedWord, dif_neg ha, dif_neg hb, List.cons_prefix_cons] at h
    exact fallback.prefixFree h.2

/-- Extend an arithmetic support code to all symbols, with a one-bit escape tag. -/
noncomputable def BinaryPrefixCode.extendZeroMass {α : Type*} (p : α → ℝ)
    (positive : BinaryPrefixCode {a // 0 < p a}) (fallback : BinaryPrefixCode α) :
    BinaryPrefixCode α where
  encode := supportTaggedWord p positive fallback
  injective := fun a b h => supportTaggedWord_prefixFree p positive fallback (by rw [h])
  nonempty := by
    classical
    intro a
    by_cases h : 0 < p a <;> simp [supportTaggedWord, h]
  prefixFree := supportTaggedWord_prefixFree p positive fallback

/-- Zero-mass fallback words cost nothing in expectation. The extra support tag
adds only one bit to a support code with information-plus-two length bound. -/
theorem expectedCodeLength_extendZeroMass_le {α : Type*} [Fintype α] (p : α → ℝ)
    (hp : ∀ a, 0 ≤ p a) (hs : ∑ a, p a = 1)
    (positive : BinaryPrefixCode {a // 0 < p a}) (fallback : BinaryPrefixCode α)
    (hpos : ∀ a (ha : 0 < p a), ((positive.encode ⟨a, ha⟩).length : ℝ) ≤
      Real.log (p a)⁻¹ / Real.log 2 + 2) :
    expectedCodeLength p (positive.extendZeroMass p fallback) ≤
      discreteEntropyBaseTwo Finset.univ p + 3 := by
  classical
  have hterm (a : α) : p a * ((supportTaggedWord p positive fallback a).length : ℝ) ≤
      p a * (Real.log (p a)⁻¹ / Real.log 2) + 3 * p a := by
    by_cases ha : 0 < p a
    · have h := mul_le_mul_of_nonneg_left (hpos a ha) (hp a)
      simp only [supportTaggedWord, dif_pos ha, List.length_cons, Nat.cast_add, Nat.cast_one]
      nlinarith
    · have hz : p a = 0 := le_antisymm (not_lt.mp ha) (hp a)
      simp [hz]
  have h := Finset.sum_le_sum (s := Finset.univ) (fun a _ => hterm a)
  simpa [expectedCodeLength, BinaryPrefixCode.extendZeroMass,
    Finset.sum_add_distrib, ← Finset.mul_sum, hs, discreteEntropyBaseTwo] using h

/-- Arithmetic coding on the positive support, extended to every message.
Only the zero-mass escape branch uses the supplied total Huffman fallback. -/
theorem exists_zeroSafe_arithmeticCode {α : Type*} [Fintype α] {k : ℕ}
    (p : Fin k → ℝ) (hp : ∀ i, 0 ≤ p i) (hs : ∑ i, p i = 1)
    (message : α → List (Fin k)) (hinj : Function.Injective message)
    (hlen : ∀ a b, (message a).length = (message b).length)
    (q : α → ℝ) (hq : ∀ a, 0 ≤ q a) (hqs : ∑ a, q a = 1)
    (hmass : ∀ a, ((message a).map p).prod = q a) :
    ∃ positive : BinaryPrefixCode {a // 0 < q a},
      (∀ a, (positive.encode a).length = arithmeticLength (q a.val)) ∧
      expectedCodeLength q (positive.extendZeroMass q (huffmanCode q hq)) ≤
        discreteEntropyBaseTwo Finset.univ q + 3 := by
  classical
  have hbudget (a : {a // 0 < q a}) :
      2 * (1 / (2 : ℝ) ^ arithmeticLength (q a.val)) ≤
        (arithmeticInterval p (message a.val)).2 - (arithmeticInterval p (message a.val)).1 := by
    rw [arithmeticInterval_width, hmass]
    exact (arithmeticLength_width_budget a.property).le
  obtain ⟨positive, hl, _⟩ := exists_arithmeticPrefixCode p hp hs
    (fun a : {a // 0 < q a} => message a.val)
    (fun a b h => Subtype.ext (hinj h))
    (fun a b => hlen a.val b.val) (fun a => arithmeticLength (q a.val)) hbudget
  refine ⟨positive, hl, expectedCodeLength_extendZeroMass_le q hq hqs positive (huffmanCode q hq) ?_⟩
  intro a ha
  rw [hl]
  have hq1 : q a ≤ 1 := by
    rw [← hqs]
    exact Finset.single_le_sum (fun b _ => hq b) (Finset.mem_univ a)
  exact arithmeticLength_le_information_add_two ha hq1

end BanditRLProof.LowerBounds
