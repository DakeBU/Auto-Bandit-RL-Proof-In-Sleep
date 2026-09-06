import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Nat.Cast.Order.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Field.Rat
import BanditRLProof.FiniteBanditModelInvariants
import BanditRLProof.RegretDecomposition

/-!
# Deterministic regret/count bounds

This module contains algorithm-neutral deterministic scaffolds that convert
per-arm pull-count upper bounds into pseudo-regret upper bounds.  It stays
below probability, expectation, filtrations, concentration, and algorithm
final theorem work.
-/

namespace BanditRLProof

/--
If every arm's pull count is bounded by `B`, then pseudo-regret is bounded by
the corresponding gap-weighted count budget.

This is the `REGRET-COUNT-BOUND` deterministic scaffold.  It consumes only the
compiled regret decomposition and model-derived gap nonnegativity.
-/
theorem pseudoRegret_le_finset_sum_gap_mul_count_bound
    {K : Nat}
    (model : FiniteBanditModel K)
    (action : ActionTrace (Fin K))
    (n : Nat)
    (B : Fin K -> Rat)
    (hB : forall a : Fin K,
      ((pullCount action a n : Nat) : Rat) <= B a) :
    pseudoRegret model action n <=
      (Finset.univ : Finset (Fin K)).sum
        (fun a : Fin K => model.gap a * B a) := by
  rw [pseudoRegret_eq_finset_sum_gap_mul_pullCount]
  apply Finset.sum_le_sum
  intro a _ha
  exact
    mul_le_mul_of_nonneg_left
      (hB a)
      (FiniteBanditModel.gap_nonneg model a)

/--
Nat-valued per-arm pull-count bounds imply the corresponding gap-weighted
pseudo-regret bound after casting the count budget to `Rat`.

This is the `REGRET-NAT-COUNT-BOUND` adapter.  It is algorithm-neutral and
keeps ETC/UCB-specific count facts out of this file.
-/
theorem pseudoRegret_le_finset_sum_gap_mul_nat_count_bound
    {K : Nat}
    (model : FiniteBanditModel K)
    (action : ActionTrace (Fin K))
    (n : Nat)
    (B : Fin K -> Nat)
    (hB : forall a : Fin K,
      pullCount action a n <= B a) :
    pseudoRegret model action n <=
      (Finset.univ : Finset (Fin K)).sum
        (fun a : Fin K => model.gap a * (((B a : Nat) : Rat))) := by
  exact
    pseudoRegret_le_finset_sum_gap_mul_count_bound
      (model := model)
      (action := action)
      (n := n)
      (B := fun a : Fin K => (((B a : Nat) : Rat)))
      (hB := by
        intro a
        exact (@Nat.cast_le Rat _ _ _ _ _).mpr (hB a))

/--
A uniform Nat-valued pull-count bound implies pseudo-regret is bounded by the
sum of model gaps times that uniform count budget.

This is the `REGRET-UNIFORM-NAT-COUNT-BOUND` adapter.  It is still
algorithm-neutral and does not prove any ETC/UCB-specific count fact.
-/
theorem pseudoRegret_le_sum_gap_mul_uniform_nat_count_bound
    {K : Nat}
    (model : FiniteBanditModel K)
    (action : ActionTrace (Fin K))
    (n B : Nat)
    (hB : forall a : Fin K,
      pullCount action a n <= B) :
    pseudoRegret model action n <=
      ((Finset.univ : Finset (Fin K)).sum
        (fun a : Fin K => model.gap a)) * (((B : Nat) : Rat)) := by
  calc
    pseudoRegret model action n
        <=
      (Finset.univ : Finset (Fin K)).sum
        (fun a : Fin K =>
          model.gap a * (((B : Nat) : Rat))) := by
          exact
            pseudoRegret_le_finset_sum_gap_mul_nat_count_bound
              (model := model)
              (action := action)
              (n := n)
              (B := fun _a : Fin K => B)
              (hB := hB)
    _ =
      ((Finset.univ : Finset (Fin K)).sum
        (fun a : Fin K => model.gap a)) * (((B : Nat) : Rat)) := by
          exact
            (Finset.sum_mul
              (s := (Finset.univ : Finset (Fin K)))
              (f := fun a : Fin K => model.gap a)
              (a := (((B : Nat) : Rat)))).symm

end BanditRLProof
