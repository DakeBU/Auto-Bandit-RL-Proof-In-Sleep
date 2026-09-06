import BanditRLProof.LowerBounds.PrefixCodeConstruction

namespace BanditRLProof.LowerBounds

def BinaryPrefixCode.relabel {α β : Type*} (code : BinaryPrefixCode α) (e : β ≃ α) :
    BinaryPrefixCode β where
  encode := fun i => code.encode (e i)
  injective := code.injective.comp e.injective
  nonempty := fun i => code.nonempty (e i)
  prefixFree := fun h => e.injective (code.prefixFree h)

/-- Full optimality against every code, not merely against a chosen candidate family. -/
def IsOptimalPrefixCode {α : Type*} [Fintype α] (p : α → ℝ) (code : BinaryPrefixCode α) : Prop :=
  ∀ other : BinaryPrefixCode α, expectedCodeLength p code ≤ expectedCodeLength p other

theorem expectedCodeLength_swap
    {α : Type*} [Fintype α] [DecidableEq α] (p : α → ℝ) (code : BinaryPrefixCode α)
    (a b : α) (hab : a ≠ b) :
    expectedCodeLength p (code.relabel (Equiv.swap a b)) = expectedCodeLength p code +
      (p a - p b) * ((code.encode b).length - (code.encode a).length : ℝ) := by
  have hterm (i : α) : p i * ((code.encode (Equiv.swap a b i)).length : ℝ) =
      p i * (code.encode i).length +
        (if i = a then p a * ((code.encode b).length - (code.encode a).length : ℝ) else 0) +
        (if i = b then p b * ((code.encode a).length - (code.encode b).length : ℝ) else 0) := by
    by_cases hia : i = a
    · subst i
      simp [hab]
      ring
    by_cases hib : i = b
    · subst i
      simp [hab.symm]
      ring
    · simp [Equiv.swap_apply_of_ne_of_ne hia hib, hia, hib]
  change (∑ i, p i * ((code.encode (Equiv.swap a b i)).length : ℝ)) = _
  simp_rw [hterm]
  simp only [Finset.sum_add_distrib]
  simp [expectedCodeLength]
  ring

/-- Assigning a shorter word to a higher-probability symbol cannot increase cost. -/
theorem expectedCodeLength_swap_le
    {α : Type*} [Fintype α] [DecidableEq α] (p : α → ℝ) (code : BinaryPrefixCode α)
    (a b : α) (hab : a ≠ b) (hp : p a ≤ p b)
    (hl : (code.encode a).length ≤ (code.encode b).length) :
    expectedCodeLength p (code.relabel (Equiv.swap a b)) ≤ expectedCodeLength p code := by
  rw [expectedCodeLength_swap p code a b hab]
  have hlR : ((code.encode a).length : ℝ) ≤ (code.encode b).length := by exact_mod_cast hl
  have h := mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hp) (sub_nonneg.mpr hlR)
  linarith

/-- An optimal code orders lengths opposite to strictly ordered probabilities. -/
theorem IsOptimalPrefixCode.length_antitone
    {α : Type*} [Fintype α] [DecidableEq α] {p : α → ℝ} {code : BinaryPrefixCode α}
    (hopt : IsOptimalPrefixCode p code) (a b : α) (hp : p a < p b) :
    (code.encode b).length ≤ (code.encode a).length := by
  have hab : a ≠ b := by intro h; subst b; exact (lt_irrefl _ hp)
  have ho := hopt (code.relabel (Equiv.swap a b))
  rw [expectedCodeLength_swap p code a b hab] at ho
  by_contra hl
  have hlR : ((code.encode a).length : ℝ) < (code.encode b).length := by
    exact_mod_cast (lt_of_not_ge hl)
  have hm := mul_neg_of_neg_of_pos (sub_neg.mpr hp) (sub_pos.mpr hlR)
  linarith

/-- Any global minimizer inherits the entropy sandwich; this does not assert existence. -/
theorem IsOptimalPrefixCode.entropy_sandwich
    {α : Type*} [Fintype α] [DecidableEq α] {p : α → ℝ} {code : BinaryPrefixCode α}
    (hopt : IsOptimalPrefixCode p code) (hp : ∀ i, 0 ≤ p i) (hs : ∑ i, p i = 1) :
    discreteEntropyBaseTwo Finset.univ p ≤ expectedCodeLength p code ∧
      expectedCodeLength p code ≤ discreteEntropyBaseTwo Finset.univ p + 1 := by
  obtain ⟨other, _, hother⟩ := exists_binaryPrefixCode_entropy_sandwich p hp hs
  exact ⟨discreteEntropyBaseTwo_le_expectedCodeLength p hp hs code, (hopt other).trans hother⟩

/-- The local nonempty-codeword convention forces at least one expected bit. -/
theorem one_le_expectedCodeLength
    {α : Type*} [Fintype α] (p : α → ℝ) (hp : ∀ i, 0 ≤ p i)
    (hs : ∑ i, p i = 1) (code : BinaryPrefixCode α) : 1 ≤ expectedCodeLength p code := by
  rw [← hs]
  apply Finset.sum_le_sum
  intro i _
  have hl : (1 : ℝ) ≤ (code.encode i).length := by
    have hz : (code.encode i).length ≠ 0 := by
      intro h
      exact code.nonempty i (List.length_eq_zero_iff.mp h)
    have hn : 1 ≤ (code.encode i).length := by omega
    exact_mod_cast hn
  nlinarith [hp i]

/-- The singleton alphabet's nonempty one-bit code. -/
def singletonPrefixCode (α : Type*) [Subsingleton α] : BinaryPrefixCode α where
  encode := fun _ => [false]
  injective := fun _ _ _ => Subsingleton.elim _ _
  nonempty := fun _ => by simp
  prefixFree := fun _ => Subsingleton.elim _ _

/-- The singleton base case has a genuine global optimum under the local convention. -/
theorem singletonPrefixCode_optimal
    {α : Type*} [Fintype α] [Subsingleton α] (p : α → ℝ)
    (hp : ∀ i, 0 ≤ p i) (hs : ∑ i, p i = 1) :
    IsOptimalPrefixCode p (singletonPrefixCode α) := by
  intro other
  have he : expectedCodeLength p (singletonPrefixCode α) = 1 := by
    simpa [expectedCodeLength, singletonPrefixCode] using hs
  rw [he]
  exact one_le_expectedCodeLength p hp hs other

end BanditRLProof.LowerBounds
