import BanditRLProof.LowerBounds.CodingEntropyBound

namespace BanditRLProof.LowerBounds

noncomputable section

/-- Strict Shannon length, leaving Kraft slack on every positive-mass symbol.
This definition is not a prefix-code constructor. -/
def shannonLength (p : ℝ) : ℕ := ⌊Real.log p⁻¹ / Real.log 2⌋₊ + 1

theorem shannonLength_pos (p : ℝ) : 0 < shannonLength p := by
  exact Nat.succ_pos _

/-- Each positive-mass symbol leaves strict Kraft slack. -/
theorem shannonLength_kraft_weight_lt {p : ℝ} (hp : 0 < p) :
    (1 / 2 : ℝ) ^ shannonLength p < p := by
  apply (Real.log_lt_log_iff (by positivity) hp).1
  rw [Real.log_pow, Real.log_div (by norm_num) (by norm_num), Real.log_one]
  have h := Nat.lt_floor_add_one (Real.log p⁻¹ / Real.log 2)
  have hl : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hcast : (shannonLength p : ℝ) = ⌊Real.log p⁻¹ / Real.log 2⌋₊ + 1 := by
    simp [shannonLength]
  rw [← hcast] at h
  have hm := (div_lt_iff₀ hl).1 h
  rw [Real.log_inv] at hm
  nlinarith

theorem shannonLength_le_information_add_one {p : ℝ} (hp : 0 < p) (hp1 : p ≤ 1) :
    (shannonLength p : ℝ) ≤ Real.log p⁻¹ / Real.log 2 + 1 := by
  have hn : 0 ≤ Real.log p⁻¹ / Real.log 2 :=
    div_nonneg (Real.log_nonneg ((one_le_inv₀ hp).2 hp1))
      (Real.log_pos (by norm_num)).le
  simp only [shannonLength, Nat.cast_add, Nat.cast_one]
  linarith [Nat.floor_le hn]

theorem weighted_shannonLength_le {p : ℝ} (hp : 0 ≤ p) (hp1 : p ≤ 1) :
    p * shannonLength p ≤ p * (Real.log p⁻¹ / Real.log 2) + p := by
  rcases eq_or_lt_of_le hp with he | he
  · subst p
    simp
  · have h := mul_le_mul_of_nonneg_left (shannonLength_le_information_add_one he hp1) hp
    nlinarith

/-- A numerical expected-length bound; realizability by a prefix code is separate. -/
theorem sum_weighted_shannonLength_le_entropy_add_one
    {α : Type*} [Fintype α] (p : α → ℝ)
    (hp : ∀ i, 0 ≤ p i) (hs : ∑ i, p i = 1) :
    (∑ i, p i * shannonLength (p i)) ≤ discreteEntropyBaseTwo Finset.univ p + 1 := by
  have hp1 (i) : p i ≤ 1 := by
    rw [← hs]
    exact Finset.single_le_sum (fun j _ => hp j) (Finset.mem_univ i)
  have h := Finset.sum_le_sum (s := Finset.univ)
    (fun i _ => weighted_shannonLength_le (hp i) (hp1 i))
  simpa only [Finset.sum_add_distrib, hs, discreteEntropyBaseTwo] using h

end
end BanditRLProof.LowerBounds
