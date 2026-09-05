import BanditRLProof.LowerBounds.ArithmeticZeroExtension

namespace BanditRLProof.LowerBounds

def sourceBlockList {α : Type*} : (n : ℕ) → SourceBlock α n → List α
  | 0, _ => []
  | n + 1, x => x.1 :: sourceBlockList n x.2

theorem sourceBlockList_length {α : Type*} (n : ℕ) (x : SourceBlock α n) :
    (sourceBlockList n x).length = n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [sourceBlockList, ih]

theorem sourceBlockList_injective {α : Type*} (n : ℕ) :
    Function.Injective (sourceBlockList (α := α) n) := by
  induction n with
  | zero =>
    change Function.Injective (fun _ : PUnit => ([] : List α))
    intro a b _
    exact Subsingleton.elim a b
  | succ n ih =>
    intro a b h
    have he := List.cons.inj h
    exact Prod.ext he.1 (ih he.2)

theorem sourceBlockList_mass {α : Type*} (p : α → ℝ) (n : ℕ) (x : SourceBlock α n) :
    ((sourceBlockList n x).map p).prod = sourceBlockMass p n x := by
  induction n with
  | zero => rfl
  | succ n ih => simp [sourceBlockList, sourceBlockMass, ih]

theorem exists_arithmeticBlockSupport {k : ℕ} (p : Fin k → ℝ)
    (hp : ∀ i, 0 ≤ p i) (hs : ∑ i, p i = 1) (n : ℕ) :
    ∃ positive : BinaryPrefixCode {x : SourceBlock.{0,0} (Fin k) n // 0 < sourceBlockMass p n x},
      (∀ x, (positive.encode x).length = arithmeticLength (sourceBlockMass p n x.val)) ∧
      (∀ x, (arithmeticInterval p (sourceBlockList n x.val)).1 ≤
        dyadicAddressLower (positive.encode x) ∧
        dyadicAddressUpper (positive.encode x) <
          (arithmeticInterval p (sourceBlockList n x.val)).2) ∧
      expectedCodeLength (sourceBlockMass p n)
        (positive.extendZeroMass (sourceBlockMass p n)
          (huffmanCode (sourceBlockMass p n) (sourceBlockMass_nonneg p hp n))) ≤
        n * discreteEntropyBaseTwo Finset.univ p + 3 := by
  have h := exists_zeroSafe_arithmeticCode p hp hs (sourceBlockList n)
    (sourceBlockList_injective n) (fun a b => (sourceBlockList_length n a).trans
      (sourceBlockList_length n b).symm) (sourceBlockMass p n)
    (sourceBlockMass_nonneg p hp n) (sum_sourceBlockMass p hs n) (sourceBlockList_mass p n)
  simpa [discreteEntropyBaseTwo_sourceBlockMass p hs n] using h

/-- The named arithmetic block code: interval addresses on positive blocks,
with the one-bit tagged fallback on zero-mass blocks. -/
noncomputable def arithmeticBlockCode {k : ℕ} (p : Fin k → ℝ)
    (hp : ∀ i, 0 ≤ p i) (hs : ∑ i, p i = 1) (n : ℕ) :
    BinaryPrefixCode (SourceBlock.{0,0} (Fin k) n) :=
  (Classical.choose (exists_arithmeticBlockSupport p hp hs n)).extendZeroMass
    (sourceBlockMass p n) (huffmanCode (sourceBlockMass p n) (sourceBlockMass_nonneg p hp n))

theorem arithmeticBlockCode_expected_length_le {k : ℕ} (p : Fin k → ℝ)
    (hp : ∀ i, 0 ≤ p i) (hs : ∑ i, p i = 1) (n : ℕ) :
    expectedCodeLength (sourceBlockMass p n) (arithmeticBlockCode p hp hs n) ≤
      n * discreteEntropyBaseTwo Finset.univ p + 3 :=
  (Classical.choose_spec (exists_arithmeticBlockSupport p hp hs n)).2.2

/-- Removing the support tag from a positive block yields an address inside
its actual arithmetic interval. This property belongs to the named code,
not merely to an unrelated witness with the same length. -/
theorem arithmeticBlockCode_payload_interval {k : ℕ} (p : Fin k → ℝ)
    (hp : ∀ i, 0 ≤ p i) (hs : ∑ i, p i = 1) (n : ℕ)
    (x : SourceBlock.{0,0} (Fin k) n) (hx : 0 < sourceBlockMass p n x) :
    (arithmeticInterval p (sourceBlockList n x)).1 ≤
      dyadicAddressLower ((arithmeticBlockCode p hp hs n).encode x).tail ∧
    dyadicAddressUpper ((arithmeticBlockCode p hp hs n).encode x).tail <
      (arithmeticInterval p (sourceBlockList n x)).2 := by
  have h := (Classical.choose_spec (exists_arithmeticBlockSupport p hp hs n)).2.1 ⟨x, hx⟩
  simpa [arithmeticBlockCode, BinaryPrefixCode.extendZeroMass, supportTaggedWord, hx] using h

theorem arithmeticBlockCode_rate_sandwich {k : ℕ} (p : Fin k → ℝ)
    (hp : ∀ i, 0 ≤ p i) (hs : ∑ i, p i = 1) (n : ℕ) (hn : 0 < n) :
    discreteEntropyBaseTwo Finset.univ p ≤
      expectedCodeLength (sourceBlockMass p n) (arithmeticBlockCode p hp hs n) / n ∧
    expectedCodeLength (sourceBlockMass p n) (arithmeticBlockCode p hp hs n) / n ≤
      discreteEntropyBaseTwo Finset.univ p + 3 / n := by
  refine ⟨sourceBlock_code_rate_lower_bound p hp hs n hn _, ?_⟩
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  apply (div_le_iff₀ hnR).mpr
  have he : (discreteEntropyBaseTwo Finset.univ p + 3 / (n : ℝ)) * n =
      n * discreteEntropyBaseTwo Finset.univ p + 3 := by field_simp
  rw [he]
  exact arithmeticBlockCode_expected_length_le p hp hs n

/-- The constructed arithmetic code's expected bits per symbol tend to entropy,
including sources with zero-probability symbols. -/
theorem arithmeticBlockCode_rate_tendsto_entropy {k : ℕ} (p : Fin k → ℝ)
    (hp : ∀ i, 0 ≤ p i) (hs : ∑ i, p i = 1) :
    Filter.Tendsto (fun n : ℕ => expectedCodeLength (sourceBlockMass p (n + 1))
      (arithmeticBlockCode p hp hs (n + 1)) / (n + 1))
      Filter.atTop (nhds (discreteEntropyBaseTwo Finset.univ p)) := by
  have hup : Filter.Tendsto
      (fun n : ℕ => discreteEntropyBaseTwo Finset.univ p + 3 / (n + 1 : ℝ))
      Filter.atTop (nhds (discreteEntropyBaseTwo Finset.univ p)) := by
    have hz := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul (3 : ℝ)
    simpa [mul_div_assoc] using tendsto_const_nhds.add hz
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hup
    (fun n => by simpa using (arithmeticBlockCode_rate_sandwich p hp hs (n + 1) (Nat.succ_pos n)).1)
    (fun n => by simpa using (arithmeticBlockCode_rate_sandwich p hp hs (n + 1) (Nat.succ_pos n)).2)

end BanditRLProof.LowerBounds
