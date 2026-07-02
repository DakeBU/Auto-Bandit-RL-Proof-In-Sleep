import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# FTRL one-step finite-sum wrapper

This module records the deterministic optimization primitive used by FTRL/OMD
routes.  It consumes an explicit minimizer certificate for the regularized
finite-action objective and returns the one-step linear-loss inequality against
any feasible comparator.

It does not prove convexity, minimizer existence, a Tsallis regularizer, a
stability/penalty decomposition, or a regret theorem.
-/

namespace BanditRLProof
namespace FTRL

universe u

/-- Finite-action linear loss of a weight vector against a loss vector. -/
noncomputable def linearLoss {Action : Type u}
    (arms : Finset Action) (p loss : Action -> Real) : Real :=
  arms.sum (fun a => p a * loss a)

/-- The finite probability-simplex predicate over an explicit action set. -/
def finiteSimplex {Action : Type u}
    (arms : Finset Action) (p : Action -> Real) : Prop :=
  (forall a, a ∈ arms -> 0 <= p a) ∧ arms.sum p = 1

/--
Regularized one-round FTRL objective `eta * <p, loss> + R p`.

The learning-rate positivity contract is kept on the theorem, not the
definition, so future leaves can reuse the objective algebraically.
-/
noncomputable def regularizedObjective {Action : Type u}
    (arms : Finset Action) (eta : Real)
    (regularizer : (Action -> Real) -> Real)
    (loss : Action -> Real) (p : Action -> Real) : Real :=
  eta * linearLoss arms p loss + regularizer p

/-- A point `p` minimizes the regularized objective over a feasible predicate. -/
def IsRegularizedMinimizer {Action : Type u}
    (feasible : (Action -> Real) -> Prop)
    (arms : Finset Action) (eta : Real)
    (regularizer : (Action -> Real) -> Real)
    (loss : Action -> Real) (p : Action -> Real) : Prop :=
  feasible p ∧
    forall q, feasible q ->
      regularizedObjective arms eta regularizer loss p <=
        regularizedObjective arms eta regularizer loss q

/--
FTRL one-step inequality from an explicit regularized-objective minimizer.

The conclusion is the deterministic algebraic form used before later leaves
choose a concrete regularizer or prove a stability/penalty sum.
-/
theorem linearLoss_sub_le_regularizer_sub_div_of_isRegularizedMinimizer
    {Action : Type u}
    (feasible : (Action -> Real) -> Prop)
    (arms : Finset Action) (eta : Real)
    (regularizer : (Action -> Real) -> Real)
    (loss : Action -> Real) (p q : Action -> Real)
    (heta : 0 < eta)
    (hp : IsRegularizedMinimizer feasible arms eta regularizer loss p)
    (hq : feasible q) :
    linearLoss arms p loss - linearLoss arms q loss <=
      (regularizer q - regularizer p) / eta := by
  set Lp := linearLoss arms p loss
  set Lq := linearLoss arms q loss
  set Rp := regularizer p
  set Rq := regularizer q
  have hmin :
      eta * Lp + Rp <= eta * Lq + Rq := by
    simpa [IsRegularizedMinimizer, regularizedObjective, Lp, Lq, Rp, Rq]
      using hp.2 q hq
  have hscaled : eta * Lp - eta * Lq <= Rq - Rp := by
    linarith
  have hmul : (Lp - Lq) * eta <= Rq - Rp := by
    calc
      (Lp - Lq) * eta = eta * Lp - eta * Lq := by
        ring
      _ <= Rq - Rp := hscaled
  have hdiv : Lp - Lq <= (Rq - Rp) / eta :=
    (le_div_iff₀ heta).2 hmul
  simpa [Lp, Lq, Rp, Rq] using hdiv

/-- FTRL one-step inequality specialized to the finite simplex. -/
theorem linearLoss_sub_le_regularizer_sub_div_of_simplex_minimizer
    {Action : Type u}
    (arms : Finset Action) (eta : Real)
    (regularizer : (Action -> Real) -> Real)
    (loss : Action -> Real) (p q : Action -> Real)
    (heta : 0 < eta)
    (hp : IsRegularizedMinimizer (finiteSimplex arms) arms eta
      regularizer loss p)
    (hq : finiteSimplex arms q) :
    linearLoss arms p loss - linearLoss arms q loss <=
      (regularizer q - regularizer p) / eta := by
  exact
    linearLoss_sub_le_regularizer_sub_div_of_isRegularizedMinimizer
      (finiteSimplex arms) arms eta regularizer loss p q heta hp hq

end FTRL
end BanditRLProof
