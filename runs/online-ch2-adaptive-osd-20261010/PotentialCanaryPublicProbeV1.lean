import Tests.OnlineAdaptivePotentialCanary
open Finset Tests.OnlineAdaptivePotentialCanary

example :
    (∑ t ∈ range 4, (a t - a (t + 1)) * w t) ≤ 4 * w 3 - a 4 * w 3 ∧
    (∑ t ∈ range 4, (a t - a (t + 1)) * w t) = 1 ∧
    a 4 * w 3 = 2 ∧
    (∑ t ∈ range 4, (a t - a (t + 1)) * w t) < 4 * w 3 - a 4 * w 3 ∧
    w 0 = 0 ∧ w 1 = w 2 ∧ a 1 < a 2 := by
  exact Tests.OnlineAdaptivePotentialCanary.leading_zero_and_stall

#check Tests.OnlineAdaptivePotentialCanary.leading_zero_and_stall
#print axioms Tests.OnlineAdaptivePotentialCanary.leading_zero_and_stall

example :
    (∑ t ∈ range 3, (signed t - signed (t + 1)) * (0 : ℝ)) ≤
      (-2 : ℝ) * 0 - signed 3 * 0 ∧
    (∑ t ∈ range 1, (terminal t - terminal (t + 1)) * (2 : ℝ)) ≤
      (1 : ℝ) * 2 - terminal 1 * 2 ∧
    (∑ t ∈ range 1, (terminal t - terminal (t + 1)) * (2 : ℝ)) = -10 ∧
    (1 : ℝ) * 2 - terminal 1 * 2 = -8 := by
  exact Tests.OnlineAdaptivePotentialCanary.signed_zero_and_free_terminal

#check Tests.OnlineAdaptivePotentialCanary.signed_zero_and_free_terminal
#print axioms Tests.OnlineAdaptivePotentialCanary.signed_zero_and_free_terminal
