1. Review of REGRET-COUNT-BOUND

REGRET-COUNT-BOUND is reasonable as implemented. It is the right deterministic scaffold:

lean
pseudoRegret model action n
  <= ∑ a, model.gap a * B a

from per-arm count bounds. It correctly consumes:

lean
pseudoRegret_eq_finset_sum_gap_mul_pullCount
FiniteBanditModel.gap_nonneg

and does not introduce probability, expectation, filtration, or concentration. Do not revise it.

2. Next single executable leaf

Do the Nat-bound convenience corollary next.

Recommended row:

REGRET-NAT-COUNT-BOUND

Recommended theorem:

lean
pseudoRegret_le_finset_sum_gap_mul_nat_count_bound

Reason: algorithm-specific count lemmas for ETC/UCB will naturally produce bounds of the form:

lean
pullCount action a n <= B a

where B a : Nat, while the current generic theorem expects:

lean
((pullCount action a n : Nat) : Rat) <= B a

with B a : Rat. The next smallest useful bridge should convert Nat-valued count bounds into the existing Rat-valued regret scaffold.

Do not start the first ETC-specific count scaffold yet. The Nat-bound adapter is algorithm-neutral and will make the ETC/UCB leaves cleaner.

3. File placement

Add this theorem to the existing file:

BanditRLProof/RegretCountBounds.lean

Do not create a new file unless the project convention strongly prefers one leaf per file. This theorem is a direct corollary of the theorem already in that file.

4. Imports

Add one Mathlib import if it is not already available transitively:

lean
import Mathlib.Data.Nat.Cast.Order.Basic

So the file should have at least:

lean
import Mathlib.Data.Nat.Cast.Order.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Field.Rat
import BanditRLProof.RegretDecomposition
import BanditRLProof.FiniteBanditModelInvariants

Mathlib.Data.Nat.Cast.Order.Basic provides Nat.cast_le, the order bridge for natural-number casts; its docs list Nat.cast_le with shape ↑m ≤ ↑n ↔ m ≤ n. 
Lean Community

5. Exact Lean-facing statement
lean
namespace BanditRLProof

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
        exact (Nat.cast_le (α := Rat)).mpr (hB a))

end BanditRLProof

If Lean dislikes the exact .mpr elaboration, use:

lean
      (hB := by
        intro a
        simpa using ((Nat.cast_le (α := Rat)).mpr (hB a)))
6. Local APIs to reuse

Reuse exactly:

lean
pseudoRegret_le_finset_sum_gap_mul_count_bound

Do not reopen:

lean
pseudoRegret
pullCount
pseudoRegret_eq_finset_sum_gap_mul_pullCount
FiniteBanditModel.gap_nonneg

The existing Rat-valued count-bound theorem already encapsulates those dependencies.

7. Mathlib APIs to use

Use:

lean
Nat.cast_le

to turn:

lean
pullCount action a n <= B a

into:

lean
((pullCount action a n : Nat) : Rat) <= ((B a : Nat) : Rat)

Nat.cast_le is available in the Nat-cast order module. 
Lean Community

No new ordered-sum proof should be needed in this corollary. The previous theorem already used Finset.sum_le_sum; that theorem lives in the ordered big-operator finset layer, which is the right boundary for finite-sum inequalities. 
Lean Community

8. Regularity contracts

Use exactly:

lean
model : FiniteBanditModel K
action : ActionTrace (Fin K)
n : Nat
B : Fin K -> Nat
hB : forall a : Fin K,
  pullCount action a n <= B a

Do not add:

lean
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
0 < K

No 0 < K is needed.

9. Status classification

Classify this as:

REGRET-NAT-COUNT-BOUND:
  executable deterministic Nat-count-to-regret adapter

It is a prerequisite for:

ETC count-bound scaffold
UCB count-bound scaffold
algorithmic deterministic regret skeletons

It should not close:

ETC regret theorem
UCB regret theorem
EXP-REGRET-PULLCOUNT
COND-EXPECT-REWARD
FILTRATION-HISTORY
MART-DIFF-REWARD
TAIL-SUMMABILITY-UCB
10. Failure policy

Use a fail-closed policy.

If this leaf fails:

Confirm the import:

lean
import Mathlib.Data.Nat.Cast.Order.Basic

If the cast proof fails, try:

lean
simpa using ((Nat.cast_le (α := Rat)).mpr (hB a))

If Nat.cast_le still does not elaborate for Rat, use a local helper:

lean
private theorem natCast_le_rat_of_le {m n : Nat} (h : m <= n) :
    ((m : Nat) : Rat) <= ((n : Nat) : Rat) := by
  exact (Nat.cast_le (α := Rat)).mpr h

Do not import Mathlib.Tactic just for exact_mod_cast unless the explicit Nat.cast_le route is genuinely blocked.

Do not reprove REGRET-COUNT-BOUND.

Do not start ETC/UCB-specific count facts in this same batch.

Mark complete only after:

Bash
python3 tools/bandit.py check

passes.

11. Batch size

Complete only:

REGRET-NAT-COUNT-BOUND

with:

one theorem in BanditRLProof/RegretCountBounds.lean
one consumer test in Tests/Basic.lean
docs/index/local leaf card refresh
python3 tools/bandit.py check

Then ask again. The next review should choose the first ETC-specific count scaffold or a uniform Nat-bound corollary, depending on which algorithm ledger is next.