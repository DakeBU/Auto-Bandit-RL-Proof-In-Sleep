import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Real.Basic

noncomputable section
open Finset
namespace BanditRL.OnlineCumulativePotential

def finite_regret_identity_typeprobe {E : Type*}
    (psi loss : ℕ → E → ℝ) (x : ℕ → E) (u z : E)
    (T : ℕ) (hT : 0 < T) : Prop :=
    let y : ℕ → E := fun t => if t = T then z else x t
    let G : ℕ → E → ℝ := fun t v => psi t v + ∑ i ∈ range (t + 1), loss i v
    (∑ t ∈ range T, (loss t (y t) - loss t u)) =
      psi (T - 1) u - psi 0 (y 0) +
      (∑ t ∈ range T, (G t (y t) - G t (y (t + 1)))) +
      (∑ t ∈ range (T - 1),
        (psi t (y (t + 1)) - psi (t + 1) (y (t + 1)))) +
      G (T - 1) z - G (T - 1) u

#check finite_regret_identity_typeprobe
#print finite_regret_identity_typeprobe

end BanditRL.OnlineCumulativePotential
