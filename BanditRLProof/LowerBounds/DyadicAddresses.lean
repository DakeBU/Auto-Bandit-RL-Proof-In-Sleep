import BanditRLProof.LowerBounds.ArithmeticIntervals

namespace BanditRLProof.LowerBounds

/-- Big-endian binary address, with leading zeroes retained by the word length. -/
def binaryAddressValue : List Bool → ℕ
  | [] => 0
  | b :: w => (if b then 2 ^ w.length else 0) + binaryAddressValue w

theorem binaryAddressValue_lt (w : List Bool) : binaryAddressValue w < 2 ^ w.length := by
  induction w with
  | nil => simp [binaryAddressValue]
  | cons b w ih =>
    cases b <;> simp only [binaryAddressValue, Bool.false_eq_true, if_false, if_true,
      zero_add, List.length_cons, pow_succ] <;> omega

/-- Every dyadic cell index has a binary address of the specified length. -/
theorem exists_binaryAddress (n m : ℕ) (hm : m < 2 ^ n) :
    ∃ w : List Bool, w.length = n ∧ binaryAddressValue w = m := by
  induction n generalizing m with
  | zero =>
    have hz : m = 0 := by simpa using hm
    exact ⟨[], rfl, hz.symm⟩
  | succ n ih =>
    by_cases hsmall : m < 2 ^ n
    · obtain ⟨w, hw, hv⟩ := ih m hsmall
      exact ⟨false :: w, by simp [hw], by simp [binaryAddressValue, hv]⟩
    · have hrest : m - 2 ^ n < 2 ^ n := by
        rw [pow_succ] at hm
        omega
      obtain ⟨w, hw, hv⟩ := ih (m - 2 ^ n) hrest
      refine ⟨true :: w, by simp [hw], ?_⟩
      simp only [binaryAddressValue, if_true, hw, hv]
      omega

theorem binaryAddressValue_append (u v : List Bool) :
    binaryAddressValue (u ++ v) = binaryAddressValue u * 2 ^ v.length + binaryAddressValue v := by
  induction u with
  | nil => simp [binaryAddressValue]
  | cons b u ih =>
    cases b <;> simp [binaryAddressValue, ih, List.length_append, pow_add] <;> ring

noncomputable def dyadicAddressLower (w : List Bool) : ℝ := (binaryAddressValue w : ℝ) / 2 ^ w.length
noncomputable def dyadicAddressUpper (w : List Bool) : ℝ := ((binaryAddressValue w : ℝ) + 1) / 2 ^ w.length

theorem dyadicAddress_width (w : List Bool) :
    dyadicAddressUpper w - dyadicAddressLower w = 1 / (2 : ℝ) ^ w.length := by
  simp only [dyadicAddressUpper, dyadicAddressLower]
  ring

theorem dyadicAddress_nonempty (w : List Bool) : dyadicAddressLower w < dyadicAddressUpper w := by
  have h := dyadicAddress_width w
  have hp : 0 < 1 / (2 : ℝ) ^ w.length := by positivity
  linarith

theorem dyadicAddress_append_contained (u v : List Bool) :
    dyadicAddressLower u ≤ dyadicAddressLower (u ++ v) ∧
      dyadicAddressUpper (u ++ v) ≤ dyadicAddressUpper u := by
  have hu : 0 < (2 : ℝ) ^ u.length := by positivity
  have hv : 0 < (2 : ℝ) ^ v.length := by positivity
  have hval : (binaryAddressValue v : ℝ) + 1 ≤ (2 : ℝ) ^ v.length := by
    exact_mod_cast (Nat.succ_le_of_lt (binaryAddressValue_lt v))
  have hn : 0 ≤ (binaryAddressValue v : ℝ) := by positivity
  simp only [dyadicAddressLower, dyadicAddressUpper, binaryAddressValue_append,
    List.length_append, pow_add, Nat.cast_add, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
  constructor
  · apply (div_le_div_iff₀ hu (mul_pos hu hv)).mpr
    nlinarith
  · apply (div_le_div_iff₀ (mul_pos hu hv) hu).mpr
    nlinarith

theorem dyadicAddress_prefix_contained (u v : List Bool) (h : u <+: v) :
    dyadicAddressLower u ≤ dyadicAddressLower v ∧ dyadicAddressUpper v ≤ dyadicAddressUpper u := by
  obtain ⟨w, rfl⟩ := h
  exact dyadicAddress_append_contained u w

/-- Select an actual binary word whose dyadic cell fits inside the given interval. -/
theorem exists_dyadicAddress_inside (L U : ℝ) (n : ℕ) (hL : 0 ≤ L) (hU : U ≤ 1)
    (hwidth : 2 * (1 / (2 : ℝ) ^ n) ≤ U - L) :
    ∃ w : List Bool, w.length = n ∧ L ≤ dyadicAddressLower w ∧ dyadicAddressUpper w < U := by
  have hpow : 0 < (2 : ℝ) ^ n := by positivity
  obtain ⟨m, hmL, hmU⟩ := exists_grid_cell_inside L U (1 / (2 : ℝ) ^ n) hL
    (by positivity) hwidth
  have hm1 : ((m : ℝ) + 1) / (2 : ℝ) ^ n < 1 := by
    simpa [div_eq_mul_inv] using hmU.trans_le hU
  have hm2 := (div_lt_iff₀ hpow).mp hm1
  have hmR : (m : ℝ) < (2 : ℝ) ^ n := by linarith
  have hm : m < 2 ^ n := by exact_mod_cast hmR
  obtain ⟨w, hw, hv⟩ := exists_binaryAddress n m hm
  refine ⟨w, hw, ?_, ?_⟩
  · simpa [dyadicAddressLower, hw, hv, div_eq_mul_inv] using hmL
  · simpa [dyadicAddressUpper, hw, hv, div_eq_mul_inv] using hmU

end BanditRLProof.LowerBounds
