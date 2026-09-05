import BanditRLProof.LowerBounds.PrefixCodeConstruction

namespace BanditRLProof.LowerBounds

theorem entropy_product_term (p q : ℝ) :
    (p * q) * Real.log (p * q)⁻¹ =
      q * (p * Real.log p⁻¹) + p * (q * Real.log q⁻¹) := by
  by_cases hp : p = 0
  · simp [hp]
  by_cases hq : q = 0
  · simp [hq]
  rw [Real.log_inv, Real.log_mul hp hq, Real.log_inv, Real.log_inv]
  ring

/-- Entropy of a product mass function before normalization. -/
theorem discreteEntropy_prod
    {α β : Type*} [Fintype α] [Fintype β] (p : α → ℝ) (q : β → ℝ) :
    discreteEntropy Finset.univ (fun x : α × β => p x.1 * q x.2) =
      (∑ j, q j) * discreteEntropy Finset.univ p +
      (∑ i, p i) * discreteEntropy Finset.univ q := by
  simp only [discreteEntropy, Fintype.sum_prod_type, entropy_product_term,
    Finset.sum_add_distrib]
  simp_rw [← Finset.mul_sum, ← Finset.sum_mul]
  simp only [← Finset.mul_sum]

theorem discreteEntropy_prod_probability
    {α β : Type*} [Fintype α] [Fintype β] (p : α → ℝ) (q : β → ℝ)
    (hp : ∑ i, p i = 1) (hq : ∑ j, q j = 1) :
    discreteEntropy Finset.univ (fun x : α × β => p x.1 * q x.2) =
      discreteEntropy Finset.univ p + discreteEntropy Finset.univ q := by
  rw [discreteEntropy_prod, hp, hq, one_mul, one_mul]

theorem discreteEntropyBaseTwo_prod_probability
    {α β : Type*} [Fintype α] [Fintype β] (p : α → ℝ) (q : β → ℝ)
    (hp : ∑ i, p i = 1) (hq : ∑ j, q j = 1) :
    discreteEntropyBaseTwo Finset.univ (fun x : α × β => p x.1 * q x.2) =
      discreteEntropyBaseTwo Finset.univ p + discreteEntropyBaseTwo Finset.univ q := by
  simp only [discreteEntropyBaseTwo_eq_div_log_two]
  rw [discreteEntropy_prod_probability p q hp hq, add_div]

/-- An n-symbol source block, represented by a nested product. -/
def SourceBlock (α : Type*) : ℕ → Type _
  | 0 => PUnit
  | n + 1 => α × SourceBlock α n

instance sourceBlockFintype {α : Type*} [Fintype α] (n : ℕ) : Fintype (SourceBlock α n) := by
  induction n with
  | zero => exact inferInstanceAs (Fintype PUnit)
  | succ n ih => exact inferInstanceAs (Fintype (α × SourceBlock α n))

instance sourceBlockDecidableEq {α : Type*} [DecidableEq α] (n : ℕ) :
    DecidableEq (SourceBlock α n) := by
  induction n with
  | zero => exact inferInstanceAs (DecidableEq PUnit)
  | succ n ih => exact inferInstanceAs (DecidableEq (α × SourceBlock α n))

/-- IID product mass, including the empty block of mass one. -/
def sourceBlockMass {α : Type*} (p : α → ℝ) : (n : ℕ) → SourceBlock α n → ℝ
  | 0, _ => 1
  | n + 1, x => p x.1 * sourceBlockMass p n x.2

theorem sourceBlockMass_nonneg {α : Type*} (p : α → ℝ) (hp : ∀ i, 0 ≤ p i)
    (n : ℕ) (x : SourceBlock α n) : 0 ≤ sourceBlockMass p n x := by
  induction n with
  | zero => exact zero_le_one
  | succ n ih => exact mul_nonneg (hp x.1) (ih x.2)

theorem sum_sourceBlockMass {α : Type*} [Fintype α] (p : α → ℝ)
    (hp : ∑ i, p i = 1) (n : ℕ) : ∑ x, sourceBlockMass p n x = 1 := by
  induction n with
  | zero => simp [SourceBlock, sourceBlockMass]
  | succ n ih =>
    change (∑ x : α × SourceBlock α n, p x.1 * sourceBlockMass p n x.2) = 1
    simp [Fintype.sum_prod_type, ← Finset.mul_sum, ih, hp]

theorem discreteEntropyBaseTwo_sourceBlockMass
    {α : Type*} [Fintype α] (p : α → ℝ) (hp : ∑ i, p i = 1) (n : ℕ) :
    discreteEntropyBaseTwo Finset.univ (sourceBlockMass p n) =
      n * discreteEntropyBaseTwo Finset.univ p := by
  induction n with
  | zero => simp [discreteEntropyBaseTwo, SourceBlock, sourceBlockMass]
  | succ n ih =>
    change discreteEntropyBaseTwo Finset.univ
      (fun x : α × SourceBlock α n => p x.1 * sourceBlockMass p n x.2) = _
    rw [discreteEntropyBaseTwo_prod_probability p (sourceBlockMass p n) hp
      (sum_sourceBlockMass p hp n), ih]
    push_cast
    ring

/-- Finite-block source coding with an explicit one-bit total overhead. -/
theorem exists_sourceBlock_code_rate_sandwich
    {α : Type*} [Fintype α] [DecidableEq α] (p : α → ℝ)
    (hp : ∀ i, 0 ≤ p i) (hs : ∑ i, p i = 1) (n : ℕ) (hn : 0 < n) :
    ∃ code : BinaryPrefixCode (SourceBlock α n),
      discreteEntropyBaseTwo Finset.univ p ≤ expectedCodeLength (sourceBlockMass p n) code / n ∧
      expectedCodeLength (sourceBlockMass p n) code / n ≤
        discreteEntropyBaseTwo Finset.univ p + 1 / n := by
  obtain ⟨code, hlo, hhi⟩ := exists_binaryPrefixCode_entropy_sandwich
    (sourceBlockMass p n) (sourceBlockMass_nonneg p hp n) (sum_sourceBlockMass p hs n)
  rw [discreteEntropyBaseTwo_sourceBlockMass p hs n] at hlo hhi
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  refine ⟨code, (le_div_iff₀ hnR).2 (by nlinarith), ?_⟩
  apply (div_le_iff₀ hnR).2
  have he : (discreteEntropyBaseTwo Finset.univ p + 1 / (n : ℝ)) * n =
      n * discreteEntropyBaseTwo Finset.univ p + 1 := by field_simp
  rw [he]
  exact hhi

/-- Every finite block prefix code has rate at least the source entropy. -/
theorem sourceBlock_code_rate_lower_bound
    {α : Type*} [Fintype α] [DecidableEq α] (p : α → ℝ)
    (hp : ∀ i, 0 ≤ p i) (hs : ∑ i, p i = 1) (n : ℕ) (hn : 0 < n)
    (code : BinaryPrefixCode (SourceBlock α n)) :
    discreteEntropyBaseTwo Finset.univ p ≤ expectedCodeLength (sourceBlockMass p n) code / n := by
  have h := discreteEntropyBaseTwo_le_expectedCodeLength (sourceBlockMass p n)
    (sourceBlockMass_nonneg p hp n) (sum_sourceBlockMass p hs n) code
  rw [discreteEntropyBaseTwo_sourceBlockMass p hs n] at h
  apply (le_div_iff₀ (by exact_mod_cast hn : (0 : ℝ) < n)).2
  nlinarith

end BanditRLProof.LowerBounds
