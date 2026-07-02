# Extended Pro Review: After EXP-OFREAL-PSEUDOREGRET-BOUND-OF-RAT-GAP-NONNEG

- URL: https://chatgpt.com/c/6a41e1dc-fcf0-83e8-bcb2-27cfa0eab3ad
- Prompt: reports/extended_pro_after_exp_ofreal_pseudoregret_rat_bound_prompt_2026-06-29.md
- Model surface: ChatGPT Pro Extended

## Raw Response

1. Review of EXP-OFREAL-PSEUDOREGRET-BOUND-OF-RAT-GAP-NONNEG

Yes. The completed adapter is reasonable and correctly classified as a Rat-contract adapter only.

It takes the existing lower-integral ofReal pseudo-regret bound, whose hypothesis was:

lean
forall a : Fin K,
  0 <= (((model.gap a : Rat) : Real))

and exposes the more natural project-side contract:

lean
forall a : Fin K,
  (0 : Rat) <= model.gap a

The use of:

lean
(Rat.cast_nonneg (K := Real)).mpr

is exactly the right Mathlib bridge. Mathlib.Data.Rat.Cast.Order lists Rat.cast_nonneg with the shape 0 ≤ ↑q ↔ 0 ≤ q for rational casts into ordered fields. 
Lean Community

Do not revise this theorem.

2. Does the current FiniteBanditModel.bestArm API support gap_nonneg?

Based only on the declarations and retrieval evidence reported in the prompt, not yet.

The current chain shows compiled scalar and expectation bridges, but it does not show a compiled local invariant of the form:

lean
model.mean a <= model.mean model.bestArm

or:

lean
model.mean a <= model.bestMean

or a field/lemma proving that bestArm actually dominates every arm.

So the next leaf should not jump directly to:

lean
theorem FiniteBanditModel.gap_nonneg ...

The next executable leaf should first prove the best-arm dominance invariant. That leaf will determine whether the existing model API is strong enough, without mixing in gap subtraction or expectation machinery.

3. Next single executable leaf

Recommended row:

FINITE-BANDIT-BESTARM-DOMINATES

Recommended theorem:

lean
FiniteBanditModel.mean_le_bestArm_mean

This is the missing model-semantic invariant needed before FiniteBanditModel.gap_nonneg.

4. Exact Lean-facing statement

Use this if the local selectors are indeed:

lean
model.mean
model.bestArm

as the surrounding API suggests.

lean
import BanditRLProof.Core

namespace BanditRLProof

theorem FiniteBanditModel.mean_le_bestArm_mean
    {K : Nat}
    (model : FiniteBanditModel K) (a : Fin K) :
    model.mean a <= model.mean model.bestArm := by
  exact model.bestArm_spec a

end BanditRLProof

If the proof field is not named bestArm_spec, keep the theorem statement fixed and replace only the final projection with the actual local best-arm certificate, for example:

lean
  exact model.bestArm_is_best a

or:

lean
  exact model.bestArm_least_gap a

Do not change the theorem into a gap theorem in this batch.

5. If the model uses bestMean instead

If inspection shows that FiniteBanditModel.gap is defined using a scalar field such as:

lean
model.bestMean - model.mean a

rather than:

lean
model.mean model.bestArm - model.mean a

then the correct single leaf is the same invariant but with the target scalar used by gap:

lean
theorem FiniteBanditModel.mean_le_bestMean
    {K : Nat}
    (model : FiniteBanditModel K) (a : Fin K) :
    model.mean a <= model.bestMean := by
  exact model.bestMean_spec a

But do not prove both in the same batch. Pick the one matching the actual gap definition.

6. Imports

Start with only:

lean
import BanditRLProof.Core

Escalate only if the best-arm invariant is already in a later local file. For example:

lean
import BanditRLProof.ModelLemmas

Do not import:

lean
BanditRLProof.ExpectationPseudoRegretRatBounds
BanditRLProof.ScalarPseudoRegret
Mathlib.MeasureTheory.*
Mathlib.Data.ENNReal.*

This leaf should be model semantics only.

7. Intended proof route

The proof should be a direct projection or a direct reuse of an existing local certificate:

lean
exact model.bestArm_spec a

No induction. No Finset. No lintegral. No ENNReal. No Rat.cast_nonneg.

If the local API defines bestArm by an argmax construction rather than as a structure field with proof, then the proof should reuse the local argmax theorem. Do not prove a fresh finite argmax theorem in this leaf.

8. Regularity contracts

The theorem should require only:

lean
model : FiniteBanditModel K
a : Fin K

Do not add:

lean
0 < K
Measure
IsProbabilityMeasure
MeasurableSpace
ActionTrace
pseudoRegret
pullCount
Integrable
Bochner integral
Filtration
Kernel
Concentration assumptions

No 0 < K should be necessary. If FiniteBanditModel K contains a bestArm : Fin K, then the model itself carries the necessary inhabitance burden.

9. Retrieval evidence

Local evidence from the reported state:

FiniteBanditModel.gap
FiniteBanditModel.bestArm

are being used conceptually, but no reported compiled declaration yet establishes best-arm dominance. That makes FINITE-BANDIT-BESTARM-DOMINATES the next missing semantic leaf.

Mathlib evidence needed for the previous adapter is already validated through Rat.cast_nonneg; this next leaf should not need Mathlib order-cast APIs. 
Lean Community

10. Status classification

Classify this as:

FINITE-BANDIT-BESTARM-DOMINATES:
  executable model-invariant leaf

It is a prerequisite for:

FINITE-BANDIT-GAP-NONNEG
EXP-OFREAL-PSEUDOREGRET-BOUND without explicit hgap
UCB/ETC model-level expected-regret scaffolding

It should not close:

FINITE-BANDIT-GAP-NONNEG
EXP-REGRET-PULLCOUNT
COND-EXPECT-REWARD
FILTRATION-HISTORY
MART-DIFF-REWARD
TAIL-SUMMABILITY-UCB
11. Failure policy

Use a fail-closed policy.

If this leaf fails:

First inspect the structure fields and available local declarations with targeted checks:

lean
#check FiniteBanditModel.bestArm
#check FiniteBanditModel.gap
#check FiniteBanditModel.mean
#check FiniteBanditModel.bestArm_spec

If no field or lemma proves best-arm dominance, stop. Do not fake the theorem with an axiom or a new assumption.

If the model only stores bestArm as data, with no proof that it is optimal, record the row as blocked by missing model invariant.

If the model stores a different certificate, keep the theorem statement and change only the proof projection.

If the model’s gap uses bestMean rather than mean bestArm, switch to the mean_le_bestMean version and do not also prove the bestArm version in this batch.

Do not start Bochner expectation, integrability, filtrations, kernels, concentration, or algorithm theorem cards to bypass this.

Mark the leaf complete only after:

python3 tools/bandit.py check

passes.

12. Minimal batch

Complete only:

FINITE-BANDIT-BESTARM-DOMINATES

with:

one theorem in a small model-invariant file
root import in BanditRLProof.lean
one consumer test in Tests/Basic.lean
unfinished/docs/index refresh
python3 tools/bandit.py check

Then ask again. The next review should decide whether to prove:

lean
theorem FiniteBanditModel.gap_nonneg

from the dominance invariant and the local definition of gap.
