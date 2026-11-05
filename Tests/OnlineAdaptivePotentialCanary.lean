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

theorem leading_zero_and_stall :
    (∑ t ∈ range 4, (a t - a (t + 1)) * w t) ≤ 4 * w 3 - a 4 * w 3 ∧
    (∑ t ∈ range 4, (a t - a (t + 1)) * w t) = 1 ∧
    a 4 * w 3 = 2 ∧
    (∑ t ∈ range 4, (a t - a (t + 1)) * w t) < 4 * w 3 - a 4 * w 3 ∧
    w 0 = 0 ∧ w 1 = w 2 ∧ a 1 < a 2 := by
  have hw : ∀ t < 4, 0 ≤ w t := by
    intro t ht
    interval_cases t <;> norm_num [w]
  have hm : ∀ t, t + 1 < 4 → w t ≤ w (t + 1) := by
    intro t ht
    have ht3 : t < 3 := by omega
    interval_cases t <;> norm_num [w]
  have ha4 : ∀ t < 4, a t ≤ 4 := by
    intro t ht
    interval_cases t <;> norm_num [a]
  have ha3 : ∀ t < 4, a t ≤ 3 := by
    intro t ht
    interval_cases t <;> norm_num [a]
  have hb := BanditRL.OnlineAdaptivePotential.weighted_potential_sum
    a w 4 4 (by norm_num) hw hm ha4
  have hs := BanditRL.OnlineAdaptivePotential.weighted_potential_sum
    a w 3 4 (by norm_num) hw hm ha3
  refine ⟨hb, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · norm_num [sum_range_succ, a, w]
  · norm_num [a, w]
  · calc
      _ ≤ 3 * w 3 - a 4 * w 3 := hs
      _ < 4 * w 3 - a 4 * w 3 := by norm_num [a, w]
  · rfl
  · rfl
  · norm_num [a]

theorem signed_zero_and_free_terminal :
    (∑ t ∈ range 3, (signed t - signed (t + 1)) * (0 : ℝ)) ≤
      (-2 : ℝ) * 0 - signed 3 * 0 ∧
    (∑ t ∈ range 1, (terminal t - terminal (t + 1)) * (2 : ℝ)) ≤
      (1 : ℝ) * 2 - terminal 1 * 2 ∧
    (∑ t ∈ range 1, (terminal t - terminal (t + 1)) * (2 : ℝ)) = -10 ∧
    (1 : ℝ) * 2 - terminal 1 * 2 = -8 := by
  have hbound : ∀ t < 3, signed t ≤ -2 := by
    intro t ht
    interval_cases t <;> norm_num [signed]
  have hz := BanditRL.OnlineAdaptivePotential.weighted_potential_sum
    signed (fun _ => 0) (-2) 3 (by norm_num)
    (by intro t ht; norm_num) (by intro t ht; exact le_rfl) hbound
  have ht := BanditRL.OnlineAdaptivePotential.weighted_potential_sum
    terminal (fun _ => 2) 1 1 (by norm_num)
    (by intro t ht; norm_num) (by intro t ht; exact le_rfl)
    (by
      intro t ht
      have h : t = 0 := by omega
      subst t
      norm_num [terminal])
  refine ⟨hz, ht, ?_, ?_⟩
  · norm_num [sum_range_succ, terminal]
  · norm_num [terminal]

end Tests.OnlineAdaptivePotentialCanary
