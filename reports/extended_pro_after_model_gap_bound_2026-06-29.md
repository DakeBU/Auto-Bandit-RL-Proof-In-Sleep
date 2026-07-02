1. Review

EXP-OFREAL-PSEUDOREGRET-BOUND-MODEL-GAP is the right closure point for the current ENNReal.ofReal / lintegral bridge.

The chain now gives a model-derived, no-extra-hgap theorem:

lean
MeasureTheory.lintegral mu
  (fun omega =>
    ENNReal.ofReal
      (((pseudoRegret model (action omega) n : Rat) : Real)))
  <=
(Finset.univ : Finset (Fin K)).sum
  (fun a =>
    ENNReal.ofReal (((model.gap a : Rat) : Real)) *
      (n : ENNReal))

That is a solid surrogate expectation layer. It should remain classified as lower-integral / ofReal, not Rat-valued or Bochner expected regret.

2. Recommended next direction

Do not start Bochner/integrability yet.

The next single executable leaf should be a non-probabilistic deterministic scaffold that UCB/ETC can consume:

REGRET-COUNT-BOUND

This is the standard deterministic reduction:

if each arm pull count is bounded by Bₐ,
then pseudo-regret is bounded by ∑ₐ Δₐ Bₐ.

This is smaller and safer than a Bochner canary. The Bochner route will require a deliberate scalar choice, probably Real, plus integrability and normed-space contracts. The deterministic count-bound scaffold uses the completed REGRET-PULLCOUNT and FiniteBanditModel.gap_nonneg leaves directly.

3. Exact Lean-facing statement
File

Use a new file:

BanditRLProof/RegretCountBounds.lean

Import it from:

lean
BanditRLProof.lean
Imports
lean
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Field.Rat
import BanditRLProof.RegretDecomposition
import BanditRLProof.FiniteBanditModelInvariants

Mathlib.Algebra.Order.BigOperators.Group.Finset is the relevant ordered finite-sum layer; its docs list Finset.sum_le_sum, which proves a finite-sum inequality from pointwise summand inequalities. 
Lean Community

Theorem

Use a Rat-valued bound function, not a Nat-valued one. This keeps the theorem useful for deterministic ETC bounds and later rationalized UCB-style count bounds.

lean
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Field.Rat
import BanditRLProof.RegretDecomposition
import BanditRLProof.FiniteBanditModelInvariants

namespace BanditRLProof

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
  exact mul_le_mul_of_nonneg_left
    (hB a)
    (FiniteBanditModel.gap_nonneg model a)

end BanditRLProof
4. Why this leaf, not Bochner expectation?

This theorem is the deterministic scaffold that algorithm analyses actually use before probability enters:

regret decomposition
  + count upper bounds
  + gap nonnegativity
  =
regret upper bound

It is also a small, stable consumer of two compiled local declarations:

lean
pseudoRegret_eq_finset_sum_gap_mul_pullCount
FiniteBanditModel.gap_nonneg

By contrast, a Bochner expectation leaf would need a larger design decision around Rat -> Real, integrability, and which expectation notion should become canonical. That should not be mixed into the next batch.

5. Regularity contracts

Use exactly:

lean
model : FiniteBanditModel K
action : ActionTrace (Fin K)
n : Nat
B : Fin K -> Rat
hB : forall a : Fin K,
  ((pullCount action a n : Nat) : Rat) <= B a

Do not add:

lean
Measure
MeasurableSpace
IsProbabilityMeasure
Integrable
Bochner integral
ENNReal
Real
Filtration
Kernel
Conditional expectation
Concentration assumptions
0 < K

No 0 < K is needed. Finset.univ : Finset (Fin K) handles the finite action set.

6. Retrieval evidence

Local declarations to consume:

lean
pseudoRegret_eq_finset_sum_gap_mul_pullCount
FiniteBanditModel.gap_nonneg

Mathlib declaration to consume:

lean
Finset.sum_le_sum

The ordered big-operator docs state the needed shape:

lean
(∀ i ∈ s, f i ≤ g i) ->
  ∑ i ∈ s, f i ≤ ∑ i ∈ s, g i

for ordered additive commutative monoids. 
Lean Community

The ordered rational import is appropriate because the proof uses ordered multiplication over Rat; Mathlib’s Rat order layer defines the ordered-field structure for rational numbers. 
Lean Community

7. Status classification

Classify this as:

REGRET-COUNT-BOUND:
  executable deterministic regret/count scaffold

It is a prerequisite for:

ETC deterministic regret skeleton
UCB count-bound-to-regret skeleton
algorithm-specific count lemmas

It should not close:

EXP-REGRET-PULLCOUNT
UCB regret theorem
ETC regret theorem
COND-EXPECT-REWARD
FILTRATION-HISTORY
MART-DIFF-REWARD
TAIL-SUMMABILITY-UCB
8. Failure policy

Use a fail-closed policy.

If this leaf fails:

If Finset.sum_le_sum is unavailable, keep:

lean
import Mathlib.Algebra.Order.BigOperators.Group.Finset

If ordered multiplication fails, keep:

lean
import Mathlib.Algebra.Order.Field.Rat

If the theorem pseudoRegret_eq_finset_sum_gap_mul_pullCount is not found, import the exact file containing the REGRET-PULLCOUNT declaration. Do not import the project root.

If Lean cannot infer the pointwise inequality, expand it:

lean
have hmul :
    model.gap a * ((pullCount action a n : Nat) : Rat)
      <= model.gap a * B a :=
  mul_le_mul_of_nonneg_left
    (hB a)
    (FiniteBanditModel.gap_nonneg model a)
exact hmul

Do not add probability, expectation, ENNReal, Bochner integration, filtrations, kernels, concentration, or all of Mathlib.

Do not specialize this leaf to ETC/UCB yet. Keep it algorithm-neutral.

Mark complete only after:

Bash
python3 tools/bandit.py check

passes.

9. Minimal batch

Complete only:

REGRET-COUNT-BOUND

with:

BanditRLProof/RegretCountBounds.lean
root import in BanditRLProof.lean
one consumer test in Tests/Basic.lean
docs/index/local leaf card refresh
python3 tools/bandit.py check

Then ask again. The next review should decide between a Nat-bound convenience corollary and the first ETC-specific count scaffold.