import BanditRLProof.HeavyTailTuning

/-! Finite uniform budget for the actual two-arm, two-sided confidence union. -/
namespace BanditRLProof.HeavyTail

theorem scheduled_exp_eq (t : ℕ) :
    Real.exp (-confidenceLog t) = 1 / (max (t : ℝ) 2)^4 := by
  have hx : 0 < max (t : ℝ) 2 := lt_of_lt_of_le (by norm_num) (le_max_right _ _)
  unfold confidenceLog
  rw [show -(4 * Real.log (max (t : ℝ) 2)) = Real.log (max (t : ℝ) 2) * (-4 : ℝ) by ring,
    ← Real.rpow_def_of_pos hx]
  norm_num [Real.rpow_neg hx.le, Real.rpow_natCast]

theorem cubic_tail_le_telescope (t : ℕ) (ht : 2 ≤ t) :
    4*t*Real.exp (-confidenceLog t) ≤ 1 / ((t : ℝ)-1) - 1/t := by
  have ht' : (2 : ℝ) ≤ t := by exact_mod_cast ht
  have hp : (0 : ℝ) < t := by linarith
  have hm : (0 : ℝ) < (t : ℝ)-1 := by linarith
  rw [scheduled_exp_eq, max_eq_left ht']
  apply (mul_le_mul_iff_left₀ (show 0 < (t : ℝ)^3 * ((t : ℝ)-1) by positivity)).mp
  field_simp
  nlinarith [sq_nonneg ((t : ℝ)-2)]

theorem reciprocal_telescope (n : ℕ) :
    (∑ s ∈ Finset.range n, (1 / ((s : ℝ)+1) - 1/((s : ℝ)+2))) = 1 - 1/((n : ℝ)+1) := by
  induction n with
  | zero => norm_num
  | succ n ih => rw [Finset.sum_range_succ, ih]; push_cast; ring

theorem scheduled_tail_sum_le_two (T : ℕ) :
    (∑ t ∈ Finset.range T, 4*t*Real.exp (-confidenceLog t)) ≤ 2 := by
  have hshift : ∀ n : ℕ, (∑ s ∈ Finset.range n,
      4*((s+2 : ℕ) : ℝ)*Real.exp (-confidenceLog (s+2))) ≤ 1 := by
    intro n
    calc
      _ ≤ ∑ s ∈ Finset.range n, (1 / ((s : ℝ)+1) - 1/((s : ℝ)+2)) := by
        apply Finset.sum_le_sum
        intro s _
        have he : (s : ℝ)+2-1 = s+1 := by ring
        simpa only [Nat.cast_add, Nat.cast_ofNat, he] using
          cubic_tail_le_telescope (s+2) (by omega)
      _ = 1-1/((n : ℝ)+1) := reciprocal_telescope n
      _ ≤ 1 := sub_le_self _ (by positivity)
  rcases T with _ | _ | T
  · norm_num
  · norm_num [Finset.sum_range_succ, scheduled_exp_eq]
  · rw [show T+1+1 = 2+T by omega, Finset.sum_range_add]
    have h := hshift T
    norm_num [Finset.sum_range_succ, scheduled_exp_eq, Nat.add_comm 2] at *
    linarith

end BanditRLProof.HeavyTail
