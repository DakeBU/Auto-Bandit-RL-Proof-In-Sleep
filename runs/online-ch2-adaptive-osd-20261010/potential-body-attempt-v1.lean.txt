import Mathlib.Algebra.BigOperators.Module
import Mathlib.Tactic

noncomputable section
open Finset

namespace BanditRL.OnlineAdaptivePotential

theorem weighted_potential_sum (a w : ℕ → ℝ) (C : ℝ) (T : ℕ) (hT : 0 < T)
    (hw : ∀ t < T, 0 ≤ w t)
    (hmono : ∀ t, t + 1 < T → w t ≤ w (t + 1))
    (hbound : ∀ t < T, a t ≤ C) :
    (∑ t ∈ range T, (a t - a (t + 1)) * w t) ≤
      C * w (T - 1) - a T * w (T - 1) := by
  have hparts := Finset.sum_range_by_parts w (fun i => a i - a (i + 1)) T
  simp only [smul_eq_mul, Finset.sum_range_sub'] at hparts
  have hlow : (a 0 - C) * (w (T - 1) - w 0) ≤
      ∑ i ∈ range (T - 1), (w (i + 1) - w i) * (a 0 - a (i + 1)) := by
    calc
      (a 0 - C) * (w (T - 1) - w 0) =
          ∑ i ∈ range (T - 1), (w (i + 1) - w i) * (a 0 - C) := by
            rw [← Finset.sum_mul, Finset.sum_range_sub]
            ring
      _ ≤ _ := by
        apply Finset.sum_le_sum
        intro i hi
        have hiT : i + 1 < T := by
          have := Finset.mem_range.mp hi
          omega
        exact mul_le_mul_of_nonneg_left
          (sub_le_sub_left (hbound (i + 1) hiT) (a 0))
          (sub_nonneg.mpr (hmono i hiT))
  have hstart : (a 0 - C) * w 0 ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr (hbound 0 hT)) (hw 0 hT)
  have hcomm : (∑ t ∈ range T, (a t - a (t + 1)) * w t) =
      ∑ t ∈ range T, w t * (a t - a (t + 1)) := by
    apply Finset.sum_congr rfl
    intro i hi
    ring
  rw [hcomm, hparts]
  nlinarith [hlow, hstart]

end BanditRL.OnlineAdaptivePotential
