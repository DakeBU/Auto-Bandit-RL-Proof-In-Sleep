import BanditRLProof.OnlineCumulativePotential
import Mathlib.Algebra.BigOperators.Module
import Mathlib.Tactic

noncomputable section
open Finset
namespace BanditRL.OnlineCumulativePotentialCanary

def finite_identity_two_round_terminal_splice_typeprobe : Prop :=
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
    x 2 = 100 ∧ y 2 = 2 ∧ y 2 ≠ x 2

#check finite_identity_two_round_terminal_splice_typeprobe
#print finite_identity_two_round_terminal_splice_typeprobe

end BanditRL.OnlineCumulativePotentialCanary
