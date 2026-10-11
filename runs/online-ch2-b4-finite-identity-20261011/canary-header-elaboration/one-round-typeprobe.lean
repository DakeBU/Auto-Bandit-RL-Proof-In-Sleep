import BanditRLProof.OnlineCumulativePotential
import Mathlib.Algebra.BigOperators.Module
import Mathlib.Tactic

noncomputable section
open Finset
namespace BanditRL.OnlineCumulativePotentialCanary

def finite_identity_one_round_positive_gap_typeprobe : Prop :=
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
        (psi t (y (t + 1)) - psi (t + 1) (y (t + 1)))))

#check finite_identity_one_round_positive_gap_typeprobe
#print finite_identity_one_round_positive_gap_typeprobe

end BanditRL.OnlineCumulativePotentialCanary
