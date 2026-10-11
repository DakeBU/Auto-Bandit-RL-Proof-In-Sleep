import BanditRLProof.OnlineCumulativePotential
import Mathlib.Algebra.BigOperators.Module
import Mathlib.Tactic

noncomputable section
open Finset
namespace BanditRL.OnlineCumulativePotentialCanary

theorem finite_identity_one_round_positive_gap :
    let psi : ℕ → ℝ → ℝ := fun _ v => v ^ 2 / 2
    let loss : ℕ → ℝ → ℝ := fun _ v => (v - 1) ^ 2 / 2
    let x : ℕ → ℝ := fun _ => 1 / 2
    let u : ℝ := 1 / 2
    let z : ℝ := 2 / 3
    let T : ℕ := 1
    let y : ℕ → ℝ := fun t => if t = T then z else x t
    let G : ℕ → ℝ → ℝ := fun t v => psi t v + ∑ i ∈ range (t + 1), loss i v
    ((∑ t ∈ range T, (loss t (y t) - loss t u)) =
      psi (T - 1) u - psi 0 (y 0) +
      (∑ t ∈ range T, (G t (y t) - G t (y (t + 1)))) +
      (∑ t ∈ range (T - 1),
        (psi t (y (t + 1)) - psi (t + 1) (y (t + 1)))) +
      G (T - 1) z - G (T - 1) u) ∧
    (∑ t ∈ range T, (loss t (y t) - loss t u)) = 0 ∧
    (psi (T - 1) u - psi 0 (y 0)) = 0 ∧
    (∑ t ∈ range T, (G t (y t) - G t (y (t + 1)))) = -(1 / 36 : ℝ) ∧
    (∑ t ∈ range (T - 1),
        (psi t (y (t + 1)) - psi (t + 1) (y (t + 1)))) = 0 ∧
    (G (T - 1) z - G (T - 1) u) = (1 / 36 : ℝ) ∧
    ¬ ((∑ t ∈ range T, (loss t (y t) - loss t u)) ≤
      (psi (T - 1) u - psi 0 (y 0)) + (∑ t ∈ range T, (G t (y t) - G t (y (t + 1)))) +
      (∑ t ∈ range (T - 1),
        (psi t (y (t + 1)) - psi (t + 1) (y (t + 1))))) := by
  dsimp only
  constructor
  · exact BanditRL.OnlineCumulativePotential.finite_regret_identity
      (fun _ v : ℝ => v ^ 2 / 2) (fun _ v : ℝ => (v - 1) ^ 2 / 2)
      (fun _ => (1 / 2 : ℝ)) (1 / 2) (2 / 3) 1 (by decide)
  · norm_num [Finset.sum_range_succ]

theorem finite_identity_two_round_terminal_splice :
    let psi : ℕ → ℝ → ℝ := fun t v => ((t : ℝ) + 1) * v ^ 2 / 2
    let loss : ℕ → ℝ → ℝ := fun t v =>
      if t = 0 then v else if t = 1 then -2 * v + 1 else 0
    let x : ℕ → ℝ := fun t => if t = 0 then 0 else if t = 1 then 1 else 100
    let u : ℝ := 3
    let z : ℝ := 2
    let T : ℕ := 2
    let y : ℕ → ℝ := fun t => if t = T then z else x t
    let G : ℕ → ℝ → ℝ := fun t v => psi t v + ∑ i ∈ range (t + 1), loss i v
    ((∑ t ∈ range T, (loss t (y t) - loss t u)) =
      psi (T - 1) u - psi 0 (y 0) +
      (∑ t ∈ range T, (G t (y t) - G t (y (t + 1)))) +
      (∑ t ∈ range (T - 1),
        (psi t (y (t + 1)) - psi (t + 1) (y (t + 1)))) +
      G (T - 1) z - G (T - 1) u) ∧
    (∑ t ∈ range T, (loss t (y t) - loss t u)) = 1 ∧
    (psi (T - 1) u - psi 0 (y 0)) = 9 ∧
    (∑ t ∈ range T, (G t (y t) - G t (y (t + 1)))) = -(7 / 2 : ℝ) ∧
    (∑ t ∈ range (T - 1),
        (psi t (y (t + 1)) - psi (t + 1) (y (t + 1)))) = -(1 / 2 : ℝ) ∧
    (G (T - 1) z - G (T - 1) u) = -4 ∧
    x 2 = 100 ∧ y 2 = 2 ∧ y 2 ≠ x 2 := by
  dsimp only
  constructor
  · exact BanditRL.OnlineCumulativePotential.finite_regret_identity
      (fun t v : ℝ => ((t : ℝ) + 1) * v ^ 2 / 2)
      (fun t v : ℝ => if t = 0 then v else if t = 1 then -2 * v + 1 else 0)
      (fun t => if t = 0 then (0 : ℝ) else if t = 1 then 1 else 100)
      3 2 2 (by decide)
  · norm_num [Finset.sum_range_succ]

end BanditRL.OnlineCumulativePotentialCanary
