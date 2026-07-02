1. Next single executable leaf

Do the uniform Nat-bound corollary next, not the first ETC-specific scaffold.

Recommended row:

REGRET-UNIFORM-NAT-COUNT-BOUND

Reason: ETC/UCB count lemmas often first prove a uniform statement of the form:

lean
forall a, pullCount action a n <= B

The existing theorem already handles arm-dependent Nat bounds. The next useful adapter should collapse the constant-bound case into the standard shape:

lean
pseudoRegret model action n
  <= (sum of gaps) * B

This is still algorithm-neutral and keeps the deterministic scaffold clean before ETC-specific work.

2. Exact Lean-facing statement

Add this theorem to the existing file:

BanditRLProof/RegretCountBounds.lean

Recommended theorem:

lean
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

Finset.sum_mul has the exact distributive shape needed here:

lean
(∑ i ∈ s, f i) * a = ∑ i ∈ s, f i * a

and lives in Mathlib.Algebra.BigOperators.Ring.Finset. 
Lean Community

3. Imports

Since this should live in RegretCountBounds.lean, keep the existing imports and add only the ring big-operator import if it is not already available transitively:

lean
import Mathlib.Algebra.BigOperators.Ring.Finset

The file likely now needs at least:

lean
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Nat.Cast.Order.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Field.Rat
import BanditRLProof.RegretDecomposition
import BanditRLProof.FiniteBanditModelInvariants

Do not add probability, expectation, ENNReal, Bochner integration, filtration, kernels, or concentration imports.

4. Local APIs to reuse

Reuse exactly:

lean
pseudoRegret_le_finset_sum_gap_mul_nat_count_bound

Do not reopen:

lean
pseudoRegret_eq_finset_sum_gap_mul_pullCount
FiniteBanditModel.gap_nonneg
pullCount
pseudoRegret

The point of this leaf is only:

arm-dependent Nat bound
  ↓ instantiate B a := B
uniform Nat count bound
  ↓ factor constant out of finite sum
regret ≤ (sum gaps) * B
5. Regularity contracts

Use exactly:

lean
model : FiniteBanditModel K
action : ActionTrace (Fin K)
n B : Nat
hB : forall a : Fin K,
  pullCount action a n <= B

Do not add:

lean
0 < K
Measure
MeasurableSpace
IsProbabilityMeasure
ENNReal
Real
Integrable
Bochner expectation
Filtration
Kernel
Conditional expectation
Concentration assumptions

No 0 < K assumption is needed.

6. Status classification

Classify this as:

REGRET-UNIFORM-NAT-COUNT-BOUND:
  executable deterministic uniform-count regret adapter

It is a prerequisite for:

ETC deterministic count scaffold
UCB deterministic count scaffold
algorithmic regret skeletons using uniform pull-count bounds

It should not close:

ETC regret theorem
UCB regret theorem
EXP-REGRET-PULLCOUNT
COND-EXPECT-REWARD
FILTRATION-HISTORY
MART-DIFF-REWARD
TAIL-SUMMABILITY-UCB
7. Failure policy

Use a fail-closed policy.

If the theorem fails:

First check that this import is present:

lean
import Mathlib.Algebra.BigOperators.Ring.Finset

If the final factorization step is brittle, replace it with:

lean
rw [Finset.sum_mul]

or:

lean
simpa using
  (Finset.sum_mul
    (s := (Finset.univ : Finset (Fin K)))
    (f := fun a : Fin K => model.gap a)
    (a := (((B : Nat) : Rat)))).symm

If Lean has trouble with the constant function instantiation, make it explicit:

lean
(B := fun _a : Fin K => B)

Do not reprove REGRET-COUNT-BOUND or REGRET-NAT-COUNT-BOUND.

Do not start ETC/UCB-specific scaffolding in the same batch.

Do not import probability, expectation, ENNReal, Bochner integration, filtrations, kernels, concentration, or all of Mathlib.

Mark complete only after:

Bash
python3 tools/bandit.py check

passes.

8. Batch size

Complete only:

REGRET-UNIFORM-NAT-COUNT-BOUND

with:

one theorem in BanditRLProof/RegretCountBounds.lean
one consumer test in Tests/Basic.lean
docs/index/local leaf card refresh
python3 tools/bandit.py check

Then ask again. The next review should choose the first ETC-specific count scaffold.