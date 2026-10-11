import Mathlib.Algebra.BigOperators.Module
import Mathlib.Tactic

noncomputable section
open Finset
namespace BanditRL.OnlineWeightedPotential

theorem weighted_difference_sum_eq (a w : ℕ → ℝ) (T : ℕ) (hT : 0 < T) :
    (∑ t ∈ range T, (a t - a (t + 1)) * w t) =
      a 0 * w 0 - a T * w (T - 1) +
      ∑ t ∈ range (T - 1), (w (t + 1) - w t) * a (t + 1) := by
  have hparts := Finset.sum_range_by_parts w (fun i => a i - a (i + 1)) T
  simp only [smul_eq_mul, Finset.sum_range_sub'] at hparts
  have hsum : (∑ t ∈ range (T - 1), (w (t + 1) - w t) * (a 0 - a (t + 1))) =
      (w (T - 1) - w 0) * a 0 -
        ∑ t ∈ range (T - 1), (w (t + 1) - w t) * a (t + 1) := by
    simp_rw [mul_sub]
    rw [Finset.sum_sub_distrib, ← Finset.sum_mul, Finset.sum_range_sub]
  calc
    (∑ t ∈ range T, (a t - a (t + 1)) * w t) =
        ∑ t ∈ range T, w t * (a t - a (t + 1)) := by
      apply Finset.sum_congr rfl
      intro t ht
      ring
    _ = _ := hparts
    _ = _ := by rw [hsum]; ring


theorem distance_potential_sum_eq {E : Type*} [NormedAddCommGroup E]
    (x : ℕ → E) (u : E) (η : ℕ → ℝ) (T : ℕ)
    (hT : 0 < T) (hη : ∀ t < T, 0 < η t) :
    (∑ t ∈ range T, (‖x t - u‖ ^ 2 - ‖x (t + 1) - u‖ ^ 2) / (2 * η t)) =
      ‖x 0 - u‖ ^ 2 / (2 * η 0) - ‖x T - u‖ ^ 2 / (2 * η (T - 1)) +
      (1 / 2 : ℝ) * ∑ t ∈ range (T - 1),
        (1 / η (t + 1) - 1 / η t) * ‖x (t + 1) - u‖ ^ 2 := by
  calc
    (∑ t ∈ range T, (‖x t - u‖ ^ 2 - ‖x (t + 1) - u‖ ^ 2) / (2 * η t)) =
        ∑ t ∈ range T, (‖x t - u‖ ^ 2 - ‖x (t + 1) - u‖ ^ 2) * (1 / (2 * η t)) := by
      simp only [div_eq_mul_inv, one_mul]
    _ = ‖x 0 - u‖ ^ 2 * (1 / (2 * η 0)) -
        ‖x T - u‖ ^ 2 * (1 / (2 * η (T - 1))) +
        ∑ t ∈ range (T - 1), (1 / (2 * η (t + 1)) - 1 / (2 * η t)) *
          ‖x (t + 1) - u‖ ^ 2 :=
      weighted_difference_sum_eq (fun t => ‖x t - u‖ ^ 2) (fun t => 1 / (2 * η t)) T hT
    _ = _ := by
      congr 1
      · simp only [div_eq_mul_inv, one_mul]
      · rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro t ht
        simp only [div_eq_mul_inv, one_mul, mul_inv_rev]
        ring

end BanditRL.OnlineWeightedPotential
