import Mathlib.Analysis.Convex.SpecificFunctions.Basic

/-! Finite fractional-power sum needed for the sample-index truncation bias. -/
namespace BanditRLProof.HeavyTail

theorem rpow_increment_lower (x a : ℝ) (hx : 0 ≤ x) (ha : 0 ≤ a) (ha1 : a ≤ 1) :
    a * (x+1)^(a-1) ≤ (x+1)^a - x^a := by
  have hp : 0 < x+1 := by linarith
  have hs : -1 ≤ -(1 / (x+1)) := by
    have h := (div_le_one hp).mpr (show 1 ≤ x+1 by linarith)
    linarith
  have h := rpow_one_add_le_one_add_mul_self hs ha ha1
  have hid : 1 + -(1 / (x+1)) = x / (x+1) := by field_simp; ring
  rw [hid, Real.div_rpow hx hp.le] at h
  have hmul := (div_le_iff₀ (Real.rpow_pos_of_pos hp a)).mp h
  rw [Real.rpow_sub hp, Real.rpow_one]
  nlinarith [show (1 + a * -(1 / (x+1))) * (x+1)^a =
      (x+1)^a - a * ((x+1)^a / (x+1)) by ring]

theorem sum_shifted_rpow_le (a : ℝ) (ha : 0 < a) (ha1 : a ≤ 1) (n : ℕ) :
    (∑ s ∈ Finset.range n, ((s : ℝ)+1)^(a-1)) ≤ (n : ℝ)^a / a := by
  apply (le_div_iff₀ ha).mpr
  induction n with
  | zero => simp [Real.zero_rpow ha.ne']
  | succ n ih =>
    rw [Finset.sum_range_succ, add_mul, Nat.cast_add_one]
    have h := rpow_increment_lower (n : ℝ) a (Nat.cast_nonneg n) ha.le ha1
    nlinarith

end BanditRLProof.HeavyTail
