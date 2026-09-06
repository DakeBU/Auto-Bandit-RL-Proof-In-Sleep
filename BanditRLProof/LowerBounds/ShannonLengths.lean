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

/-- The positive support occupies strictly less than the available Kraft mass. -/
theorem sum_positive_shannon_weights_lt_one
    {α : Type*} [Fintype α] (p : α → ℝ)
    (hp : ∀ i, 0 ≤ p i) (hs : ∑ i, p i = 1) :
    (∑ i, if 0 < p i then (1 / 2 : ℝ) ^ shannonLength (p i) else 0) < 1 := by
  classical
  have hex : ∃ i, 0 < p i := by
    by_contra h
    have hz (i) : p i = 0 := le_antisymm (not_lt.mp (not_exists.mp h i)) (hp i)
    simp [hz] at hs
  apply lt_of_lt_of_eq ?_ hs
  apply Finset.sum_lt_sum
  · intro i _
    split_ifs with hi
    · exact (shannonLength_kraft_weight_lt hi).le
    · exact hp i
  · obtain ⟨i, hi⟩ := hex
    exact ⟨i, Finset.mem_univ i, by simpa [hi] using shannonLength_kraft_weight_lt hi⟩

/-- Complete length assignment, including zero-mass symbols; codewords are not yet constructed. -/
theorem exists_lengths_kraft_lt_one_entropy_bound
    {α : Type*} [Fintype α] (p : α → ℝ)
    (hp : ∀ i, 0 ≤ p i) (hs : ∑ i, p i = 1) :
    ∃ l : α → ℕ, (∀ i, 0 < l i) ∧
      (∑ i, (1 / 2 : ℝ) ^ l i) < 1 ∧
      (∑ i, p i * l i) ≤ discreteEntropyBaseTwo Finset.univ p + 1 := by
  classical
  let W := ∑ i, if 0 < p i then (1 / 2 : ℝ) ^ shannonLength (p i) else 0
  have hW : W < 1 := sum_positive_shannon_weights_lt_one p hp hs
  let C : ℝ := Fintype.card α + 1
  have hC : 0 < C := by dsimp [C]; positivity
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one
    (div_pos (sub_pos.mpr hW) hC) (by norm_num : (1 / 2 : ℝ) < 1)
  let l : α → ℕ := fun i => if 0 < p i then shannonLength (p i) else n + 1
  refine ⟨l, ?_, ?_, ?_⟩
  · intro i
    dsimp [l]
    split_ifs
    · exact shannonLength_pos _
    · exact Nat.succ_pos _
  · have hsum : (∑ i, (1 / 2 : ℝ) ^ l i) ≤ W + Fintype.card α * (1 / 2 : ℝ) ^ (n + 1) := by
      calc
        _ ≤ ∑ i, ((if 0 < p i then (1 / 2 : ℝ) ^ shannonLength (p i) else 0) +
            (1 / 2 : ℝ) ^ (n + 1)) := by
          apply Finset.sum_le_sum
          intro i _
          dsimp [l]
          split_ifs
          · nlinarith [pow_pos (by norm_num : (0 : ℝ) < 1 / 2) (n + 1)]
          · simp
        _ = _ := by simp [W, Finset.sum_add_distrib]
    have hpow : (1 / 2 : ℝ) ^ (n + 1) ≤ (1 / 2 : ℝ) ^ n := by
      rw [pow_succ]
      nlinarith [pow_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2) n]
    have hmul := (lt_div_iff₀ hC).1 hn
    have hbound := mul_le_mul_of_nonneg_left hpow (Nat.cast_nonneg (Fintype.card α) :
      (0 : ℝ) ≤ Fintype.card α)
    dsimp [C] at hmul
    nlinarith [pow_pos (by norm_num : (0 : ℝ) < 1 / 2) n]
  · have heq : (∑ i, p i * l i) = ∑ i, p i * shannonLength (p i) := by
      apply Finset.sum_congr rfl
      intro i _
      dsimp [l]
      split_ifs with hi
      · rfl
      · have hz : p i = 0 := le_antisymm (not_lt.mp hi) (hp i)
        simp [hz]
    rw [heq]
    exact sum_weighted_shannonLength_le_entropy_add_one p hp hs

end
end BanditRLProof.LowerBounds
