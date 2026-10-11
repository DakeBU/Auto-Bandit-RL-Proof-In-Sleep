import BanditRLProof.OnlineAdaptivePotential

noncomputable section
open Finset
namespace Tests.OnlineAdaptivePotentialCanary

def a : ℕ → ℝ
  | 0 => 3
  | 1 => 1
  | 2 => 3
  | 3 => 2
  | _ => 1

def w : ℕ → ℝ
  | 0 => 0
  | 1 => 1
  | 2 => 1
  | _ => 2

def signed : ℕ → ℝ
  | 0 => -3
  | 1 => -2
  | 2 => -4
  | _ => 7

def terminal : ℕ → ℝ
  | 0 => 0
  | _ => 5

#check (
    (∑ t ∈ range 4, (a t - a (t + 1)) * w t) ≤ 4 * w 3 - a 4 * w 3 ∧
    (∑ t ∈ range 4, (a t - a (t + 1)) * w t) = 1 ∧
    a 4 * w 3 = 2 ∧
    (∑ t ∈ range 4, (a t - a (t + 1)) * w t) < 4 * w 3 - a 4 * w 3 ∧
    w 0 = 0 ∧ w 1 = w 2 ∧ a 1 < a 2 )

#check (
    (∑ t ∈ range 3, (signed t - signed (t + 1)) * (0 : ℝ)) ≤
      (-2 : ℝ) * 0 - signed 3 * 0 ∧
    (∑ t ∈ range 1, (terminal t - terminal (t + 1)) * (2 : ℝ)) ≤
      (1 : ℝ) * 2 - terminal 1 * 2 ∧
    (∑ t ∈ range 1, (terminal t - terminal (t + 1)) * (2 : ℝ)) = -10 ∧
    (1 : ℝ) * 2 - terminal 1 * 2 = -8 )

end Tests.OnlineAdaptivePotentialCanary
