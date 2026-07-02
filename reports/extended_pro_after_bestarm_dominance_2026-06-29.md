1. Review

Yes. FiniteBanditModel.gap_nonneg is the right next single leaf.

You now have the missing semantic prerequisite:

lean
theorem FiniteBanditModel.mean_le_bestArm_mean
    {K : Nat}
    (model : FiniteBanditModel K) (a : Fin K) :
    model.mean a <= model.mean model.bestArm

The next dependency needed by the existing ENNReal.ofReal pseudo-regret bound is exactly:

lean
forall a : Fin K, (0 : Rat) <= model.gap a

So the next leaf should close that model-level nonnegativity obligation. Do not move to expectation, Bochner integration, filtration, or concentration before this.

2. Recommended next leaf
FINITE-BANDIT-GAP-NONNEG
Exact Lean-facing statement
lean
theorem FiniteBanditModel.gap_nonneg
    {K : Nat}
    (model : FiniteBanditModel K) (a : Fin K) :
    (0 : Rat) <= model.gap a

Put it in:

BanditRLProof/FiniteBanditModelInvariants.lean

not in Core or LeafLemmas.

Reason: Core should remain definition-level; LeafLemmas already carries broad deterministic bookkeeping. This theorem is a model-semantic invariant and belongs beside FiniteBanditModel.mean_le_bestArm_mean.

3. Imports

No new imports should be needed beyond the file’s current imports:

lean
import Mathlib.Algebra.Order.Field.Rat
import Mathlib.Data.Fintype.Basic
import BanditRLProof.Core

Mathlib.Algebra.Order.Field.Rat is the appropriate explicit boundary for ordered-field facts over Rat; the Mathlib docs describe it as the rational-number ordered-field layer and show that it imports the ordered/nonnegative field infrastructure. 
Lean Community

If sub_nonneg is not available through this import in local Lean, escalate only to the smallest order import that supplies it; do not import probability, ENNReal, expectation files, or the project root.

4. Intended proof route

Try this first:

lean
namespace BanditRLProof

theorem FiniteBanditModel.gap_nonneg
    {K : Nat}
    (model : FiniteBanditModel K) (a : Fin K) :
    (0 : Rat) <= model.gap a := by
  unfold FiniteBanditModel.gap
  exact sub_nonneg.mpr
    (FiniteBanditModel.mean_le_bestArm_mean model a)

end BanditRLProof

If gap unfolds through bestMean, use only a local definitional expansion:

lean
theorem FiniteBanditModel.gap_nonneg
    {K : Nat}
    (model : FiniteBanditModel K) (a : Fin K) :
    (0 : Rat) <= model.gap a := by
  unfold FiniteBanditModel.gap
  -- If needed:
  -- unfold FiniteBanditModel.bestMean
  exact sub_nonneg.mpr
    (FiniteBanditModel.mean_le_bestArm_mean model a)

If unfold does not expose the subtraction cleanly, use a change after inspecting the actual normal form:

lean
theorem FiniteBanditModel.gap_nonneg
    {K : Nat}
    (model : FiniteBanditModel K) (a : Fin K) :
    (0 : Rat) <= model.gap a := by
  unfold FiniteBanditModel.gap
  change (0 : Rat) <= model.mean model.bestArm - model.mean a
  exact sub_nonneg.mpr
    (FiniteBanditModel.mean_le_bestArm_mean model a)

The theorem should be short. If it grows beyond this, the local definition of gap or bestMean needs inspection.

5. Regularity contracts

Use exactly:

lean
{K : Nat}
(model : FiniteBanditModel K)
(a : Fin K)

Do not add:

lean
0 < K
MeasurableSpace
Measure
IsProbabilityMeasure
ActionTrace
pseudoRegret
pullCount
ENNReal
Real
Integrable
Bochner expectation
Filtration
Kernel
Concentration assumptions

No 0 < K is needed. If FiniteBanditModel K contains bestArm : Fin K, the structure already carries whatever inhabitance burden is necessary.

6. Local APIs to reuse

Use exactly:

lean
FiniteBanditModel.mean_le_bestArm_mean

and the definition of:

lean
FiniteBanditModel.gap

Do not reuse the expectation chain yet:

lean
lintegral_ofReal_pseudoRegret_le_sum_model_gap_ofReal_mul_time_of_rat_gap_nonneg

That should be consumed in the next batch, after gap_nonneg exists.

7. Status classification

Classify this as:

FINITE-BANDIT-GAP-NONNEG:
  executable model-invariant leaf

It is a direct prerequisite for removing the explicit hgap argument from:

lean
lintegral_ofReal_pseudoRegret_le_sum_model_gap_ofReal_mul_time_of_rat_gap_nonneg

It should not close:

EXP-REGRET-PULLCOUNT
EXP-OFREAL-PSEUDOREGRET-BOUND without explicit model assumptions
COND-EXPECT-REWARD
FILTRATION-HISTORY
MART-DIFF-REWARD
TAIL-SUMMABILITY-UCB
8. Failure policy

Use a fail-closed policy.

If the theorem fails:

First inspect the exact reducible shape:

lean
#check FiniteBanditModel.gap
#check FiniteBanditModel.mean_le_bestArm_mean

If gap unfolds to:

lean
model.mean model.bestArm - model.mean a

use:

lean
exact sub_nonneg.mpr
  (FiniteBanditModel.mean_le_bestArm_mean model a)

If gap unfolds to:

lean
model.bestMean - model.mean a

inspect whether bestMean is definitionally equal to model.mean model.bestArm. If yes, unfold it. If not, stop and prove a separate future invariant:

lean
model.bestMean = model.mean model.bestArm

Do not smuggle that fact into gap_nonneg.

If the inequality orientation is reversed, do not rewrite the theorem. Fix the dominance theorem or prove the missing orientation explicitly.

Do not use linarith unless the direct sub_nonneg.mpr route is unexpectedly brittle. If you do use it, keep the import minimal.

Do not add axioms, assumptions, sorry, or a theorem-card-only placeholder.

Do not import expectation, measure, ENNReal, Bochner integration, filtrations, kernels, concentration, or all of Mathlib.

Mark the leaf complete only after:

Bash
python3 tools/bandit.py check

passes.

9. After gap_nonneg

After this leaf compiles, the next likely leaf is the automatic adapter that removes the explicit gap-nonnegativity hypothesis from the existing lower-integral pseudo-regret bound:

lean
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
          (n : ENNReal))

But do not implement that in the same batch. Complete only FINITE-BANDIT-GAP-NONNEG, refresh the docs/index/test, run the full gate, then ask again.