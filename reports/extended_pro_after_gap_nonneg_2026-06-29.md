1. Review

Yes. FINITE-BANDIT-GAP-NONNEG is the right semantic closeout for the model layer, and the proof route you used is appropriate.

The important point is that gap was not a plain subtraction definition; it branches on:

lean
if arm = model.bestArm then 0 else ...

so the case split was necessary. The theorem now gives the exact project-side contract needed by the current lower-integral pseudo-regret bound:

lean
forall a : Fin K, (0 : Rat) <= model.gap a

Do not revise FiniteBanditModel.gap_nonneg.

2. Next single executable leaf

Yes: the next leaf should be the adapter that removes the explicit hgap argument from the existing ENNReal.ofReal lower-integral pseudo-regret bound.

Recommended row:

EXP-OFREAL-PSEUDOREGRET-BOUND-MODEL-GAP

Recommended theorem name:

lean
lintegral_ofReal_pseudoRegret_le_sum_model_gap_ofReal_mul_time

This is now a one-step consumer of:

lean
lintegral_ofReal_pseudoRegret_le_sum_model_gap_ofReal_mul_time_of_rat_gap_nonneg
FiniteBanditModel.gap_nonneg

It should still be classified narrowly as an ENNReal.ofReal lower-integral surrogate bound, not Rat-valued or Bochner expected regret.

3. File placement

Put it in the existing file:

BanditRLProof/ExpectationPseudoRegretRatBounds.lean

Reason: this is the no-explicit-hgap version of the theorem already in that file. Keeping the explicit-contract theorem and the model-derived theorem adjacent is better than creating another small expectation file.

Add one import to that file:

lean
import BanditRLProof.FiniteBanditModelInvariants

The file should then have, at minimum:

lean
import Mathlib.Data.Rat.Cast.Order
import BanditRLProof.ExpectationPseudoRegretOfRealBounds
import BanditRLProof.FiniteBanditModelInvariants

No new Mathlib imports should be needed. The probability-measure class is already part of the existing expectation theorem chain; Mathlib defines IsProbabilityMeasure μ as μ Set.univ = 1, with an instance into IsZeroOrProbabilityMeasure, which is what earlier probability bounds used. 
Lean Community
+1

4. Exact Lean-facing statement
lean
namespace BanditRLProof

theorem lintegral_ofReal_pseudoRegret_le_sum_model_gap_ofReal_mul_time
    {Omega : Type u} {K : Nat}
    [MeasurableSpace Omega]
    [MeasurableSpace (Fin K)] [MeasurableSingletonClass (Fin K)]
    (mu : Measure Omega) [MeasureTheory.IsProbabilityMeasure mu]
    (model : FiniteBanditModel K)
    (action : Omega -> ActionTrace (Fin K))
    (haction : forall t : Nat,
      Measurable (fun omega : Omega => action omega t))
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
    lintegral_ofReal_pseudoRegret_le_sum_model_gap_ofReal_mul_time_of_rat_gap_nonneg
      (mu := mu)
      (model := model)
      (action := action)
      (haction := haction)
      (hgap := fun a => FiniteBanditModel.gap_nonneg model a)
      (n := n)

end BanditRLProof
5. Local APIs to reuse

Reuse exactly these two declarations:

lean
lintegral_ofReal_pseudoRegret_le_sum_model_gap_ofReal_mul_time_of_rat_gap_nonneg
FiniteBanditModel.gap_nonneg

Do not reopen:

lean
pseudoRegret
pullCount
gap
bestArm
lintegral
ENNReal.ofReal
Rat.cast_nonneg

The intended dependency route is now:

FINITE-BANDIT-GAP-NONNEG
  ↓
EXP-OFREAL-PSEUDOREGRET-BOUND-OF-RAT-GAP-NONNEG
  ↓
EXP-OFREAL-PSEUDOREGRET-BOUND-MODEL-GAP
6. Regularity contracts

Use exactly the contracts in the proposed theorem:

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

No 0 < K is needed. The model already contains bestArm : Fin K, and the theorem is structurally valid with the existing model type.

7. Retrieval evidence

Local declarations now provide the exact requirements:

lean
FiniteBanditModel.gap_nonneg
lintegral_ofReal_pseudoRegret_le_sum_model_gap_ofReal_mul_time_of_rat_gap_nonneg

Mathlib-side, the only relevant background is already imported through the existing expectation chain. The prior adapter used Rat.cast_nonneg, which Mathlib documents in Mathlib.Data.Rat.Cast.Order as the rational cast nonnegativity equivalence. 
Lean Community

No new Mathlib theorem should be probed for this leaf.

8. Status classification

Classify this as:

EXP-OFREAL-PSEUDOREGRET-BOUND-MODEL-GAP:
  compiled local ENNReal.ofReal lower-integral pseudo-regret bound using model-derived gap nonnegativity

It is still not:

Rat-valued expected regret
Bochner expected regret
EXP-REGRET-PULLCOUNT in the classical Real/Rat sense
UCB/ETC regret theorem
concentration theorem

It is the strongest completed ENNReal.ofReal / lintegral surrogate bound for the current FiniteBanditModel.

9. Failure policy

Use a fail-closed policy.

If this leaf fails:

Confirm ExpectationPseudoRegretRatBounds.lean imports:

lean
import BanditRLProof.FiniteBanditModelInvariants

If theorem resolution is brittle, fully qualify both names:

lean
BanditRLProof.lintegral_ofReal_pseudoRegret_le_sum_model_gap_ofReal_mul_time_of_rat_gap_nonneg
BanditRLProof.FiniteBanditModel.gap_nonneg

If Lean has trouble inferring the hgap lambda, use an explicit block:

lean
(hgap := by
  intro a
  exact FiniteBanditModel.gap_nonneg model a)

Do not reprove gap_nonneg in this file.

Do not import Bochner integration, conditional expectation, filtrations, kernels, concentration, or all of Mathlib.

Do not rename or weaken the existing explicit-hgap theorem; it remains useful as a generic adapter.

Mark complete only after:

Bash
python3 tools/bandit.py check

passes.

10. Batch size

Complete only this adapter:

EXP-OFREAL-PSEUDOREGRET-BOUND-MODEL-GAP

with:

one theorem added to BanditRLProof/ExpectationPseudoRegretRatBounds.lean
one consumer test in Tests/Basic.lean
docs/index/local leaf card refresh
python3 tools/bandit.py check

Then ask again. The next review should decide the next major direction: either a carefully scoped Bochner/integrability canary or a non-probabilistic UCB/ETC deterministic scaffold that consumes the now-complete model-level ofReal bound.