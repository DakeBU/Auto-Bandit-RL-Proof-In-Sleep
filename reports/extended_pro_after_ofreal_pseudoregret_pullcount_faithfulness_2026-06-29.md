# Extended Pro Review: After OFREAL-PSEUDOREGRET-PULLCOUNT-FAITHFULNESS

- URL: https://chatgpt.com/c/6a41e1dc-fcf0-83e8-bcb2-27cfa0eab3ad
- Prompt: reports/extended_pro_after_ofreal_pseudoregret_pullcount_faithfulness_prompt_2026-06-29.md
- Model surface: ChatGPT Pro Extended

## Raw Response

1. Review

OFREAL-PSEUDOREGRET-PULLCOUNT-FAITHFULNESS is reasonable and correctly classified as pointwise scalar/model algebra only.

It proves the exact pointwise bridge:

lean
ENNReal.ofReal (((pseudoRegret model action n : Rat) : Real))
=
∑ a, ENNReal.ofReal (((model.gap a : Rat) : Real)) *
       (pullCount action a n : ENNReal)

under explicit gap nonnegativity. That is the correct faithfulness layer before any expected-regret statement, because ENNReal.ofReal is not a faithful embedding on arbitrary real values; Mathlib defines it through the nonnegative-real route, so nonpositive inputs are clamped at zero. 
Lean Community
+1

Do not revise this theorem.

2. Single best next executable leaf

Next, lift the pointwise scalar theorem into the existing lower-integral model-gap bound.

Recommended row:

EXP-OFREAL-PSEUDOREGRET-BOUND

Recommended theorem:

lean
lintegral_ofReal_pseudoRegret_le_sum_model_gap_ofReal_mul_time_of_nonneg

This is the right next leaf because it consumes exactly the two compiled bridges:

lean
BanditRLProof.ENNReal.ofReal_pseudoRegret_eq_univ_sum_model_gap_ofReal_mul_natCast_pullCount_of_nonneg

lintegral_univ_sum_model_gap_ofReal_mul_natCast_pullCount_le_sum_model_gap_ofReal_mul_time

It should still be classified as an ENNReal / lintegral / ofReal bound, not as Rat-valued or Bochner expected regret.

3. Exact Lean-facing statement
File

Use a new file:

BanditRLProof/ExpectationPseudoRegretOfRealBounds.lean

Import it from:

lean
BanditRLProof.lean
Imports
lean
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import BanditRLProof.ExpectationFiniteBanditModelBounds
import BanditRLProof.ScalarPseudoRegret

Mathlib.MeasureTheory.Integral.Lebesgue.Basic exposes MeasureTheory.lintegral and MeasureTheory.lintegral_congr; the docs state that lintegral_congr rewrites lower integrals from pointwise equality of ENNReal-valued functions. 
Lean Community

Theorem
lean
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import BanditRLProof.ExpectationFiniteBanditModelBounds
import BanditRLProof.ScalarPseudoRegret

namespace BanditRLProof

theorem lintegral_ofReal_pseudoRegret_le_sum_model_gap_ofReal_mul_time_of_nonneg
    {Omega : Type u} {K : Nat}
    [MeasurableSpace Omega]
    [MeasurableSpace (Fin K)] [MeasurableSingletonClass (Fin K)]
    (mu : Measure Omega) [MeasureTheory.IsProbabilityMeasure mu]
    (model : FiniteBanditModel K)
    (action : Omega -> ActionTrace (Fin K))
    (haction : forall t : Nat,
      Measurable (fun omega : Omega => action omega t))
    (hgap : forall a : Fin K,
      0 <= (((model.gap a : Rat) : Real)))
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
  calc
    MeasureTheory.lintegral mu
      (fun omega : Omega =>
        ENNReal.ofReal
          (((pseudoRegret model (action omega) n : Rat) : Real)))
        =
      MeasureTheory.lintegral mu
        (fun omega : Omega =>
          (Finset.univ : Finset (Fin K)).sum
            (fun a : Fin K =>
              ENNReal.ofReal (((model.gap a : Rat) : Real)) *
                ((pullCount (action omega) a n : Nat) : ENNReal))) := by
          apply MeasureTheory.lintegral_congr
          intro omega
          exact
            BanditRLProof.ENNReal.ofReal_pseudoRegret_eq_univ_sum_model_gap_ofReal_mul_natCast_pullCount_of_nonneg
              (model := model)
              (action := action omega)
              (hgap := hgap)
              (n := n)
    _ <=
      (Finset.univ : Finset (Fin K)).sum
        (fun a : Fin K =>
          ENNReal.ofReal (((model.gap a : Rat) : Real)) *
            (n : ENNReal)) := by
          exact
            lintegral_univ_sum_model_gap_ofReal_mul_natCast_pullCount_le_sum_model_gap_ofReal_mul_time
              (mu := mu)
              (model := model)
              (action := action)
              (haction := haction)
              (n := n)

end BanditRLProof
4. Local APIs to reuse

Reuse exactly:

lean
BanditRLProof.ENNReal.ofReal_pseudoRegret_eq_univ_sum_model_gap_ofReal_mul_natCast_pullCount_of_nonneg

and:

lean
lintegral_univ_sum_model_gap_ofReal_mul_natCast_pullCount_le_sum_model_gap_ofReal_mul_time

Do not reopen:

lean
pseudoRegret
pullCount
REGRET-PULLCOUNT
lintegral_finset_sum
ofReal_finset_sum_mul_natCast_of_nonneg

The dependency route should be:

OFREAL-PSEUDOREGRET-PULLCOUNT-FAITHFULNESS
  ↓ pointwise equality under hgap
EXP-MODEL-GAP-OFREAL-BOUND
  ↓ lower-integral model bound
EXP-OFREAL-PSEUDOREGRET-BOUND
5. Regularity contracts

Use exactly:

lean
[MeasurableSpace Omega]
[MeasurableSpace (Fin K)]
[MeasurableSingletonClass (Fin K)]
(mu : Measure Omega)
[MeasureTheory.IsProbabilityMeasure mu]

plus:

lean
model : FiniteBanditModel K
action : Omega -> ActionTrace (Fin K)
haction : forall t : Nat,
  Measurable (fun omega : Omega => action omega t)
hgap : forall a : Fin K,
  0 <= (((model.gap a : Rat) : Real))
n : Nat

Do not add:

lean
Integrable
Bochner integral
Real-valued expectation
Filtration
Kernel
Conditional expectation
Concentration assumptions
0 < K

This theorem still lives in the lower-integral ENNReal layer. Mathlib defines lintegral specifically for ENNReal-valued functions, so this is the correct integration object for the current bridge. 
Lean Community

6. Retrieval evidence

Mathlib evidence:

lean
MeasureTheory.lintegral
MeasureTheory.lintegral_congr

are in Mathlib.MeasureTheory.Integral.Lebesgue.Basic; lintegral_congr has the shape:

lean
(∀ a, f a = g a) ->
  lintegral μ f = lintegral μ g

for ENNReal-valued functions. 
Lean Community

Local declaration evidence from your compiled chain:

lean
BanditRLProof.ENNReal.ofReal_pseudoRegret_eq_univ_sum_model_gap_ofReal_mul_natCast_pullCount_of_nonneg

lintegral_univ_sum_model_gap_ofReal_mul_natCast_pullCount_le_sum_model_gap_ofReal_mul_time

These are exactly the two declarations this leaf should consume.

7. Status classification

Classify this as:

EXP-OFREAL-PSEUDOREGRET-BOUND:
  executable ENNReal/ofReal lower-integral pseudo-regret bound under explicit gap nonnegativity

It is a prerequisite for:

EXP-REGRET-PULLCOUNT
FiniteBanditModel expected-regret bridge
UCB/ETC expected-regret scaffolding

It should not close:

EXP-REGRET-PULLCOUNT
COND-EXPECT-REWARD
FILTRATION-HISTORY
ADAPTED-ACTION
MART-DIFF-REWARD
TAIL-SUMMABILITY-UCB

Reason: this is still an ENNReal.ofReal lower-integral bound. It is not a Bochner expectation theorem and does not prove gap nonnegativity from FiniteBanditModel.

8. Failure policy

Use a fail-closed policy.

If the theorem fails:

If MeasureTheory.lintegral_congr is not found, keep:

lean
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic

If lintegral_congr elaboration is brittle, replace the first calc step with a function equality:

lean
have hfun :
    (fun omega : Omega =>
       ENNReal.ofReal
         (((pseudoRegret model (action omega) n : Rat) : Real)))
      =
    (fun omega : Omega =>
       (Finset.univ : Finset (Fin K)).sum
         (fun a : Fin K =>
           ENNReal.ofReal (((model.gap a : Rat) : Real)) *
             ((pullCount (action omega) a n : Nat) : ENNReal))) := by
  funext omega
  exact
    BanditRLProof.ENNReal.ofReal_pseudoRegret_eq_univ_sum_model_gap_ofReal_mul_natCast_pullCount_of_nonneg
      (model := model)
      (action := action omega)
      (hgap := hgap)
      (n := n)

rw [hfun]
exact
  lintegral_univ_sum_model_gap_ofReal_mul_natCast_pullCount_le_sum_model_gap_ofReal_mul_time
    (mu := mu)
    (model := model)
    (action := action)
    (haction := haction)
    (n := n)

If the pointwise theorem is not found, import:

lean
import BanditRLProof.ScalarPseudoRegret

If the lower-integral model bound is not found, import:

lean
import BanditRLProof.ExpectationFiniteBanditModelBounds

Do not prove FiniteBanditModel.gap nonnegativity inside this leaf.

Do not import Bochner integration, conditional expectation, filtrations, kernels, concentration, or all of Mathlib.

Do not classify this as Rat-valued expected regret.

Mark complete only after:

python3 tools/bandit.py check

passes.

9. Minimal batch

Complete only:

EXP-OFREAL-PSEUDOREGRET-BOUND

with:

BanditRLProof/ExpectationPseudoRegretOfRealBounds.lean
root import in BanditRLProof.lean
one consumer test in Tests/Basic.lean
unfinished/docs/index refresh
python3 tools/bandit.py check

Then ask again. The next review should decide between proving FiniteBanditModel.gap nonnegativity from model internals and beginning a separate Bochner/integrability route.
