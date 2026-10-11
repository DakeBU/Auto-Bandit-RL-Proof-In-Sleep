import Mathlib.Algebra.BigOperators.Module
import Mathlib.Tactic
open Finset

#check (∀ (a w : ℕ → ℝ) (C : ℝ) (T : ℕ) (hT : 0 < T)
    (hw : ∀ t < T, 0 ≤ w t)
    (hmono : ∀ t, t + 1 < T → w t ≤ w (t + 1))
    (hbound : ∀ t < T, a t ≤ C),
    (∑ t ∈ range T, (a t - a (t + 1)) * w t) ≤
      C * w (T - 1) - a T * w (T - 1))

#check Finset.sum_range_by_parts
#check Finset.sum_range_sub
#check Finset.sum_range_sub'
