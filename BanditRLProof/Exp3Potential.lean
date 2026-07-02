import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Tactic.Ring

/-!
# EXP3 potential finite-sum wrappers

This module records the deterministic finite-action potential surface used by
exponential-weights/EXP3 routes.  It deliberately stops before importance
weighted estimators, logarithmic inequalities, learning-rate optimization, or a
regret theorem.
-/

namespace BanditRLProof
namespace Exp3Potential

universe u

/-- Finite-action exponential-weights potential. -/
noncomputable def potential {Action : Type u}
    (arms : Finset Action) (w : Action -> Real) : Real :=
  arms.sum w

/-- Multiplicative exponential-weights update for one action. -/
noncomputable def updatedWeight {Action : Type u}
    (eta : Real) (w loss : Action -> Real) (a : Action) : Real :=
  w a * Real.exp (-eta * loss a)

/-- Potential after applying the exponential-weights update on each action. -/
noncomputable def updatedPotential {Action : Type u}
    (arms : Finset Action) (eta : Real)
    (w loss : Action -> Real) : Real :=
  potential arms (updatedWeight eta w loss)

/-- Unfold the updated potential as an explicit finite sum. -/
theorem updatedPotential_eq_sum {Action : Type u}
    (arms : Finset Action) (eta : Real)
    (w loss : Action -> Real) :
    updatedPotential arms eta w loss =
      arms.sum (fun a => w a * Real.exp (-eta * loss a)) := by
  rfl

/-- Exponential updating preserves nonnegative weights. -/
theorem updatedWeight_nonneg_of_nonneg {Action : Type u}
    (eta : Real) (w loss : Action -> Real) (a : Action)
    (hw : 0 <= w a) :
    0 <= updatedWeight eta w loss a := by
  exact mul_nonneg hw (Real.exp_pos _).le

/-- The updated potential is nonnegative when all current finite weights are. -/
theorem updatedPotential_nonneg_of_nonneg {Action : Type u}
    (arms : Finset Action) (eta : Real)
    (w loss : Action -> Real)
    (hw : forall a, a ∈ arms -> 0 <= w a) :
    0 <= updatedPotential arms eta w loss := by
  exact Finset.sum_nonneg (fun a ha =>
    updatedWeight_nonneg_of_nonneg eta w loss a (hw a ha))

/--
One-step potential increment identity.

This is the algebraic finite-sum surface used before applying any EXP/log
inequality such as `exp x <= 1 + x + x^2`.
-/
theorem updatedPotential_sub_potential_eq_sum_weight_mul_exp_sub_one
    {Action : Type u}
    (arms : Finset Action) (eta : Real)
    (w loss : Action -> Real) :
    updatedPotential arms eta w loss - potential arms w =
      arms.sum (fun a => w a * (Real.exp (-eta * loss a) - 1)) := by
  simp only [updatedPotential, potential, updatedWeight]
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl ?_
  intro a _ha
  ring

/-- Finite-horizon telescoping for a real-valued potential process. -/
theorem sum_range_forward_difference
    (Phi : Nat -> Real) (T : Nat) :
    (Finset.range T).sum (fun t => Phi (t + 1) - Phi t) =
      Phi T - Phi 0 := by
  induction T with
  | zero =>
      simp
  | succ T ih =>
      rw [Finset.sum_range_succ, ih]
      ring

/-- Potential process induced by a time-indexed finite-action weight family. -/
noncomputable def potentialProcess {Action : Type u}
    (arms : Finset Action) (w : Nat -> Action -> Real) (t : Nat) : Real :=
  potential arms (w t)

/--
Finite-horizon telescope specialized to exponential-weights potentials.

This is the compiled local replacement for treating "the potential telescopes"
as only a proof weapon.
-/
theorem potentialProcess_telescope_sum_range {Action : Type u}
    (arms : Finset Action) (w : Nat -> Action -> Real) (T : Nat) :
    (Finset.range T).sum
        (fun t => potentialProcess arms w (t + 1) -
          potentialProcess arms w t) =
      potentialProcess arms w T - potentialProcess arms w 0 := by
  exact sum_range_forward_difference (fun t => potentialProcess arms w t) T

end Exp3Potential
end BanditRLProof
