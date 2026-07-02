# Extended Pro Review: After EXP-OFREAL-PSEUDOREGRET-BOUND

- URL: https://chatgpt.com/c/6a41e1dc-fcf0-83e8-bcb2-27cfa0eab3ad
- Prompt: reports/extended_pro_after_exp_ofreal_pseudoregret_bound_prompt_2026-06-29.md
- Model surface: ChatGPT Pro Extended

## Raw Response

1. Review

EXP-OFREAL-PSEUDOREGRET-BOUND is reasonable as implemented and correctly classified as an ENNReal.ofReal lower-integral bound only.

It does not claim Rat-valued expected regret, Bochner expectation, or model-derived gap nonnegativity. The theorem is exactly the lift of the pointwise scalar/model identity into the already compiled lower-integral model-gap bound.

Keep the classification narrow:

EXP-OFREAL-PSEUDOREGRET-BOUND:
  ENNReal.ofReal / lintegral pseudo-regret bound under explicit gap nonnegativity

Do not revise it.

2. Single best next executable leaf

Do a Rat-level nonnegativity contract wrapper next.

Recommended row:

EXP-OFREAL-PSEUDOREGRET-BOUND-OF-RAT-GAP-NONNEG

Recommended theorem:

lean
lintegral_ofReal_pseudoRegret_le_sum_model_gap_ofReal_mul_time_of_rat_gap_nonneg

Reason: the current theorem requires the slightly awkward hypothesis:

lean
hgap : forall a : Fin K,
  0 <= (((model.gap a : Rat) : Real))

The next useful executable leaf should expose the more natural project-side contract:

lean
hgap : forall a : Fin K,
  (0 : Rat) <= model.gap a

and use Rat.cast_nonneg to discharge the existing Real-cast hypothesis. Mathlib’s Rat.cast_nonneg theorem states that nonnegativity is preserved/reflected by the rational cast into an ordered field, including Real. 
Lean Community

Do not prove FiniteBanditModel.gap nonnegativity from bestArm in this batch. That depends on the exact local model ABI and can sprawl into model semantics. This wrapper gives the eventual model-internal theorem a clean target.

Do not start Bochner expectation yet.

3. Exact Lean-facing statement
File

Use a new file:

BanditRLProof/ExpectationPseudoRegretRatBounds.lean

Import it from:

lean
BanditRLProof.lean
Imports
lean
import Mathlib.Data.Rat.Cast.Order
import BanditRLProof.ExpectationPseudoRegretOfRealBounds

Mathlib.Data.Rat.Cast.Order is the explicit import boundary for order-preserving rational casts such as Rat.cast_nonneg. The docs list Rat.cast_nonneg in that module. 
Lean Community

Theorem
lean
import Mathlib.Data.Rat.Cast.Order
import BanditRLProof.ExpectationPseudoRegretOfRealBounds

namespace BanditRLProof

theorem lintegral_ofReal_pseudoRegret_le_sum_model_gap_ofReal_mul_time_of_rat_gap_nonneg
    {Omega : Type u} {K : Nat}
    [MeasurableSpace Omega]
    [MeasurableSpace (Fin K)] [MeasurableSingletonClass (Fin K)]
    (mu : Measure Omega) [MeasureTheory.IsProbabilityMeasure mu]
    (model : FiniteBanditModel K)
    (action : Omega -> ActionTrace (Fin K))
    (haction : forall t : Nat,
      Measurable (fun omega : Omega => action omega t))
    (hgap : forall a : Fin K,
      (0 : Rat) <= model.gap a)
    (n : Nat) :
    MeasureTheory.lintegral mu
      (fun omega : Omega =>
        ENNReal.ofReal
          (((pseudoRegret model (action omega) n : Rat) : Real)))
      <=
    (Finset.univ : Finset (Fin K)).sum
      (fun a : Fin K =>
        ENNReal.ofReal (((model.gap a : Rat) : Real)) *
          (n : ENNReal)) := by
  exact
    lintegral_ofReal_pseudoRegret_le_sum_model_gap_ofReal_mul_time_of_nonneg
      (mu := mu)
      (model := model)
      (action := action)
      (haction := haction)
      (hgap := by
        intro a
        have ha : (0 : Rat) <= model.gap a := hgap a
        simpa using
          ((Rat.cast_nonneg (K := Real)).mpr ha))
      (n := n)

end BanditRLProof
4. Local APIs to reuse

Reuse exactly:

lean
lintegral_ofReal_pseudoRegret_le_sum_model_gap_ofReal_mul_time_of_nonneg

Do not reopen:

lean
pseudoRegret
pullCount
RegretDecomposition
ENNReal.ofReal_pseudoRegret_eq_univ_sum_model_gap_ofReal_mul_natCast_pullCount_of_nonneg
lintegral_univ_sum_model_gap_ofReal_mul_natCast_pullCount_le_sum_model_gap_ofReal_mul_time

This leaf is only a regularity-contract adapter:

Rat gap nonnegativity
  ↓ Rat.cast_nonneg
Real-cast gap nonnegativity
  ↓ existing EXP-OFREAL-PSEUDOREGRET-BOUND
ENNReal.ofReal lower-integral pseudo-regret bound
5. Regularity contracts

Use exactly:

lean
[MeasurableSpace Omega]
[MeasurableSpace (Fin K)]
[MeasurableSingletonClass (Fin K)]
(mu : Measure Omega)
[MeasureTheory.IsProbabilityMeasure mu]
model : FiniteBanditModel K
action : Omega -> ActionTrace (Fin K)
haction : forall t : Nat,
  Measurable (fun omega : Omega => action omega t)
hgap : forall a : Fin K,
  (0 : Rat) <= model.gap a
n : Nat

Do not add:

lean
0 < K
Integrable
Bochner integral
Real-valued expectation
Filtration
Kernel
Conditional expectation
Concentration assumptions

This theorem is still an ENNReal.ofReal / lintegral result. It just makes the nonnegativity assumption live in Rat, where FiniteBanditModel.gap actually lives.

6. Retrieval evidence

Mathlib evidence:

lean
Rat.cast_nonneg

is listed in Mathlib.Data.Rat.Cast.Order with the shape:

lean
0 ≤ ↑q ↔ 0 ≤ q

for rational casts into ordered fields. 
Lean Community

Local declaration evidence from the compiled chain:

lean
lintegral_ofReal_pseudoRegret_le_sum_model_gap_ofReal_mul_time_of_nonneg

is the only local theorem this leaf should consume.

7. Status classification

Classify this as:

EXP-OFREAL-PSEUDOREGRET-BOUND-OF-RAT-GAP-NONNEG:
  executable Rat-contract wrapper for ENNReal/ofReal pseudo-regret bound

It is a prerequisite for:

FiniteBanditModel.gap_nonneg
EXP-REGRET-PULLCOUNT scalar design
UCB/ETC expected-regret scaffolding

It should not close:

EXP-REGRET-PULLCOUNT
COND-EXPECT-REWARD
FILTRATION-HISTORY
ADAPTED-ACTION
MART-DIFF-REWARD
TAIL-SUMMABILITY-UCB

It also should not be classified as model-derived gap nonnegativity. It assumes Rat-level nonnegativity.

8. Failure policy

Use a fail-closed policy.

If this leaf fails:

If Rat.cast_nonneg is unavailable, keep:

lean
import Mathlib.Data.Rat.Cast.Order

If the cast proof is brittle, replace the simpa block with:

lean
exact_mod_cast hgap a

only if the project already imports the relevant tactic infrastructure. Otherwise prefer the explicit Rat.cast_nonneg route.

If theorem name resolution is brittle, make the existing theorem call fully explicit:

lean
exact
  BanditRLProof.lintegral_ofReal_pseudoRegret_le_sum_model_gap_ofReal_mul_time_of_nonneg
    ...

Do not prove FiniteBanditModel.gap nonnegativity inside this file.

Do not import Bochner integration, conditional expectation, filtrations, kernels, concentration, or all of Mathlib.

Do not weaken the theorem into an inequality over the model-gap sum only; the point is to preserve the existing pseudo-regret lower-integral statement with a cleaner hypothesis.

Mark complete only after:

python3 tools/bandit.py check

passes.

9. Minimal batch

Complete only:

EXP-OFREAL-PSEUDOREGRET-BOUND-OF-RAT-GAP-NONNEG

with:

BanditRLProof/ExpectationPseudoRegretRatBounds.lean
root import in BanditRLProof.lean
one consumer test in Tests/Basic.lean
unfinished/docs/index refresh
python3 tools/bandit.py check

Then ask again. The next review should decide whether the local FiniteBanditModel API supports a direct theorem:

lean
theorem FiniteBanditModel.gap_nonneg
    (model : FiniteBanditModel K) (a : Fin K) :
    (0 : Rat) <= model.gap a

or whether that requires first adding/repairing the model’s best-arm invariant.
