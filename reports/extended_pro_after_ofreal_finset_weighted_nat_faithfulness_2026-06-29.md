# Extended Pro Review: After OFREAL-FINSET-WEIGHTED-NAT-FAITHFULNESS

- URL: https://chatgpt.com/c/6a41e1dc-fcf0-83e8-bcb2-27cfa0eab3ad
- Prompt: reports/extended_pro_after_ofreal_finset_weighted_nat_faithfulness_prompt_2026-06-29.md
- Model surface: ChatGPT Pro Extended

## Raw Response

1. Review of OFREAL-FINSET-WEIGHTED-NAT-FAITHFULNESS

OFREAL-FINSET-WEIGHTED-NAT-FAITHFULNESS is reasonable as implemented and correctly classified as scalar algebra only.

It does exactly the missing algebraic job:

lean
ENNReal.ofReal
  (∑ i in s, gap i * (count i : Real))
=
∑ i in s, ENNReal.ofReal (gap i) * (count i : ENNReal)

under explicit nonnegativity of gap. This is the right bridge because ENNReal.ofReal is not a faithful embedding for arbitrary real numbers; it routes through the nonnegative real coercion/clamping layer. Mathlib’s ENNReal big-operator docs expose ENNReal.ofReal_sum_of_nonneg, and the ENNReal/Real docs expose ENNReal.ofReal_mul', which are exactly the APIs your proof used. 
Lean Community
+1

Do not revise the theorem. It is now the clean scalar lemma needed before model-specific pseudo-regret faithfulness.

2. Single best next executable leaf

Do a model-specific pseudo-regret ofReal faithfulness bridge under explicit gap nonnegativity.

Recommended row:

OFREAL-PSEUDOREGRET-PULLCOUNT-FAITHFULNESS

Recommended theorem:

lean
ENNReal.ofReal_pseudoRegret_eq_univ_sum_model_gap_ofReal_mul_natCast_pullCount_of_nonneg

This is better than proving FiniteBanditModel.gap nonnegativity next. Without relying on the internal model ABI, keep nonnegativity as an explicit hypothesis:

lean
hgap : ∀ a : Fin K, 0 ≤ (((model.gap a : Rat) : Real))

Then instantiate the scalar theorem you just compiled using the deterministic regret decomposition:

lean
pseudoRegret_eq_finset_sum_gap_mul_pullCount

Do not start Bochner expectation yet. This leaf is still pointwise scalar algebra; it does not introduce a measure, integrability, expectation, filtrations, kernels, or concentration.

3. Exact Lean-facing leaf
File

Use a new file:

BanditRLProof/ScalarPseudoRegret.lean

Import it from:

lean
BanditRLProof.lean
Imports

Use the local module that exposes the deterministic regret decomposition. If the theorem is in the decomposition file used for REGRET-PULLCOUNT, the import should be:

lean
import Mathlib.Algebra.Field.Rat
import Mathlib.Data.Fintype.Basic
import BanditRLProof.ScalarENNReal
import BanditRLProof.PullCountDecomposition

If pseudoRegret_eq_finset_sum_gap_mul_pullCount lives in a differently named local file, replace only the last import with that file. Do not import the project root from this leaf, because the root will import the new file.

Private helper

First isolate the Rat-to-Real cast of the deterministic regret decomposition:

lean
namespace BanditRLProof

private theorem real_pseudoRegret_eq_univ_sum_model_gap_mul_natCast_pullCount
    {K : Nat}
    (model : FiniteBanditModel K)
    (action : ActionTrace (Fin K))
    (n : Nat) :
    (((pseudoRegret model action n : Rat) : Real))
      =
    (Finset.univ : Finset (Fin K)).sum
      (fun a : Fin K =>
        (((model.gap a : Rat) : Real) *
          (((pullCount action a n : Nat) : Real)))) := by
  have h :=
    congrArg (fun q : Rat => ((q : Rat) : Real))
      (pseudoRegret_eq_finset_sum_gap_mul_pullCount
        (model := model)
        (action := action)
        (t := n))
  simpa using h
Main theorem
lean
theorem ENNReal.ofReal_pseudoRegret_eq_univ_sum_model_gap_ofReal_mul_natCast_pullCount_of_nonneg
    {K : Nat}
    (model : FiniteBanditModel K)
    (action : ActionTrace (Fin K))
    (hgap : forall a : Fin K,
      0 <= (((model.gap a : Rat) : Real)))
    (n : Nat) :
    ENNReal.ofReal (((pseudoRegret model action n : Rat) : Real))
      =
    (Finset.univ : Finset (Fin K)).sum
      (fun a : Fin K =>
        ENNReal.ofReal (((model.gap a : Rat) : Real)) *
          ((pullCount action a n : Nat) : ENNReal)) := by
  rw [real_pseudoRegret_eq_univ_sum_model_gap_mul_natCast_pullCount
    (model := model)
    (action := action)
    (n := n)]

  exact
    BanditRLProof.ENNReal.ofReal_finset_sum_mul_natCast_of_nonneg
      (s := (Finset.univ : Finset (Fin K)))
      (gap := fun a : Fin K => (((model.gap a : Rat) : Real)))
      (count := fun a : Fin K => pullCount action a n)
      (hgap := by
        intro a _ha
        exact hgap a)

end BanditRLProof
4. Local APIs to reuse

Reuse exactly:

lean
pseudoRegret_eq_finset_sum_gap_mul_pullCount
BanditRLProof.ENNReal.ofReal_finset_sum_mul_natCast_of_nonneg

Do not reopen:

lean
pseudoRegret
pullCount
Finset.sum_fiberwise'
lintegral

This leaf should be a pure scalar bridge:

Rat pseudoRegret decomposition
  ↓ Rat-to-Real cast
Real nonnegative weighted sum
  ↓ ENNReal.ofReal finite-sum faithfulness
ENNReal weighted pull-count expression
5. Mathlib retrieval evidence

The scalar proof is supported by the same Mathlib surface you already validated:

Mathlib.Data.ENNReal.BigOperators lists ENNReal.ofReal_sum_of_nonneg, the finite-sum bridge for nonnegative real summands. 
Lean Community

Mathlib.Data.ENNReal.Real lists ENNReal.ofReal_mul', which rewrites ofReal (p * q) when the second factor is nonnegative. 
Lean Community

Mathlib.Algebra.Field.Rat is the right explicit boundary for the Rat field/cast route used by the private helper.

Local retrieval evidence from your current declaration index:

pseudoRegret_eq_finset_sum_gap_mul_pullCount
ENNReal.ofReal_finset_sum_mul_natCast_of_nonneg

Those are the only two nontrivial local declarations this leaf should consume.

6. Regularity contracts

Use exactly:

lean
model : FiniteBanditModel K
action : ActionTrace (Fin K)
hgap : forall a : Fin K,
  0 <= (((model.gap a : Rat) : Real))
n : Nat

Do not add:

lean
Measure
IsProbabilityMeasure
MeasurableSpace
Integrable
Real-valued expectation
Bochner integral
Filtration
Kernel
Conditional expectation
Concentration assumptions

Do not prove gap nonnegativity in this leaf. The hypothesis is explicit and deliberately external.

Also do not require:

lean
0 < K

The theorem is still structurally valid for K = 0; Finset.univ : Finset (Fin K) handles the finite action set.

7. Status classification

Classify this as:

OFREAL-PSEUDOREGRET-PULLCOUNT-FAITHFULNESS:
  executable scalar/model bridge under explicit gap nonnegativity

It is a prerequisite for:

EXP-REGRET-PULLCOUNT
FiniteBanditModel expected-regret bridge
Rat/Real/ENNReal scalar design
UCB/ETC expected-regret scaffolding

It should not close:

EXP-REGRET-PULLCOUNT
COND-EXPECT-REWARD
FILTRATION-HISTORY
ADAPTED-ACTION
MART-DIFF-REWARD
TAIL-SUMMABILITY-UCB

Reason: this is a pointwise scalar identity, not an expectation theorem.

8. Failure policy

Use a fail-closed policy.

If this leaf fails:

If the private Rat-to-Real helper fails, make the cast rewrite more explicit:

lean
have h :=
  congrArg (fun q : Rat => ((q : Rat) : Real))
    (pseudoRegret_eq_finset_sum_gap_mul_pullCount
      (model := model)
      (action := action)
      (t := n))
simpa [map_mul] using h

If needed, also try:

lean
simpa [Finset.sum_apply, map_mul] using h

If the local decomposition theorem is not found, import the exact file containing:

lean
pseudoRegret_eq_finset_sum_gap_mul_pullCount

Do not import BanditRLProof root from this new file.

If the scalar theorem name is awkward because of the nested namespace, call it fully qualified:

lean
BanditRLProof.ENNReal.ofReal_finset_sum_mul_natCast_of_nonneg

If the explicit Real-cast gap nonnegativity hypothesis feels too strong, do not change it in this batch. A later leaf can prove:

lean
(forall a, 0 <= model.gap a)
  ->
(forall a, 0 <= (((model.gap a : Rat) : Real)))

Do not import probability, Bochner integration, conditional expectation, filtrations, kernels, concentration, or all of Mathlib.

Do not weaken the theorem into an inequality. The point is exact faithfulness under nonnegativity.

Mark the leaf complete only after:

python3 tools/bandit.py check

passes.

9. Minimal batch before asking again

Complete only:

OFREAL-PSEUDOREGRET-PULLCOUNT-FAITHFULNESS

with:

BanditRLProof/ScalarPseudoRegret.lean
root import in BanditRLProof.lean
one consumer test in Tests/Basic.lean
unfinished/docs/index refresh
python3 tools/bandit.py check

Then ask again. The next review should decide whether to lift this pointwise identity into the existing lintegral model-gap bound or prove model-gap nonnegativity from FiniteBanditModel internals.
