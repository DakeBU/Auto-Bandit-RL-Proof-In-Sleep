# Extended Pro Review Response: After ETC Phase-Split Regret Bound

- Date: 2026-06-30
- Tool/model: ChatGPT Extended Pro
- URL: https://chatgpt.com/c/6a41e1dc-fcf0-83e8-bcb2-27cfa0eab3ad
- Prompt file: `reports/extended_pro_after_phase_split_bound_candidate_prompt_2026-06-30.md`
- Local gate before review: `python3 tools\bandit.py check`
- Boundary:
  `ETC-ACTION-WITH-COMMIT-PHASE-SPLIT-REGRET-BOUND`
- Recorded from raw response:
  `reports/extended_pro_after_phase_split_bound_raw_response_2026-06-30.txt`

## Reviewer Decision

- Chosen next leaf: FINITE-BANDIT-GAP-BESTARM
- Classification: project-local
- Status: reviewer-approved; already compiled locally in `BanditRLProof.Core`

## Exact Lean-Facing Statement

```lean
@[simp] theorem FiniteBanditModel.gap_bestArm
    {K : Nat}
    (model : FiniteBanditModel K) :
    model.gap model.bestArm = 0
```

## Imports And Local APIs

- Compiled declaration: `FiniteBanditModel.gap_bestArm`.
- Module: `BanditRLProof.Core`.
- Local APIs: `FiniteBanditModel.gap`, `FiniteBanditModel.bestArm`.
- No ETC, regret, empirical mean, probability, filtration, or concentration imports.

## Intended Proof Route

1. Unfold/simplify the local `FiniteBanditModel.gap` definition.
2. Close the reflexive branch `model.bestArm = model.bestArm` by `simp [gap]`.

## Regularity Contracts

- Only `{K : Nat}` and `model : FiniteBanditModel K`.
- No additional positivity, probability, measurability, filtration, integrability,
  concentration, or commit-correctness assumptions.

## Retrieval Evidence

- Local source: `BanditRLProof/Core.lean` already contains
  `@[simp] theorem gap_bestArm`.
- Current uses: `BanditRLProof.LeafLemmas.pseudoRegret_succ_of_bestArm` and
  `Tests/Basic.lean`.
- Extended Pro requested this as the prerequisite before the optimal-commit
  suffix-regret consumer leaf.

## Failure Policy

- Do not duplicate `FiniteBanditModel.gap_bestArm` in
  `FiniteBanditModelInvariants.lean`; keep one canonical theorem.
- If the core `gap` definition changes, repair this theorem first before
  consuming it in ETC regret lemmas.
- Do not prove Candidate A in the same prerequisite-closing step.

## Raw Extended Pro Response

Pick

Reject A/B/C for this batch. Do the smaller prerequisite:

FINITE-BANDIT-GAP-BESTARM

Candidate A is the right next regret theorem, but it should not depend on an uncompiled or implicit fact:

lean
FiniteBanditModel.gap_bestArm

Compile that model invariant first. Then Candidate A becomes a small consumer leaf.

Exact Lean-facing statement

Add to:

BanditRLProof/FiniteBanditModelInvariants.lean
lean
theorem FiniteBanditModel.gap_bestArm
    {K : Nat}
    (model : FiniteBanditModel K) :
    model.gap model.bestArm = 0 := by
  simp [FiniteBanditModel.gap]

If the namespace is already open in that file, this form is also fine:

lean
namespace BanditRLProof

theorem FiniteBanditModel.gap_bestArm
    {K : Nat}
    (model : FiniteBanditModel K) :
    model.gap model.bestArm = 0 := by
  simp [FiniteBanditModel.gap]

end BanditRLProof
Imports and local APIs

Use the existing imports in:

BanditRLProof/FiniteBanditModelInvariants.lean

Likely enough:

lean
import Mathlib.Algebra.Order.Field.Rat
import Mathlib.Data.Fintype.Basic
import BanditRLProof.Core

Use only:

lean
FiniteBanditModel.gap

Do not use:

lean
pseudoRegret
ETC.actionWithCommit
ETC.pseudoRegret_actionWithCommit_explorationPulls_mul_K_add_eq_add_suffix_gap
RegretCountBounds
MeasureTheory
ENNReal
Intended proof route

The proof should be definitional:

Unfold/simplify FiniteBanditModel.gap.

The if model.bestArm = model.bestArm then 0 else ... branch reduces to 0.

Expected proof:

lean
simp [FiniteBanditModel.gap]

If the simplifier needs the equality explicitly:

lean
have h : model.bestArm = model.bestArm := rfl
simp [FiniteBanditModel.gap, h]
Regularity contracts

Require only:

lean
{K : Nat}
(model : FiniteBanditModel K)

Do not add:

lean
0 < K
Measure
MeasurableSpace
Rat-valued expectation
ENNReal
Integrable
Filtration
SubGaussian
Empirical mean assumptions
Commit correctness assumptions
Concentration assumptions

No extra contract is needed. bestArm : Fin K is already part of the model API.

Retrieval evidence and classification

Local evidence:

lean
FiniteBanditModel.gap_nonneg
FiniteBanditModel.mean_le_bestArm_mean

The gap_nonneg proof already showed that the best-arm branch of gap simplifies to zero. This theorem makes that branch public and reusable.

Classification:

FINITE-BANDIT-GAP-BESTARM:
  project-local compiled model-invariant leaf

It is not:

imported
port candidate
Mathlib candidate
theorem-card-only
probability/concentration leaf
empirical-mean leaf
final ETC theorem
Failure policy

If this fails:

Inspect the definition:

lean
#check FiniteBanditModel.gap

If simp [FiniteBanditModel.gap] does not close, try:

lean
unfold FiniteBanditModel.gap
simp

If the theorem goal is oriented opposite to the simplifier result, prove the same statement with:

lean
exact Eq.symm ...

only if necessary.

Do not prove Candidate A in the same batch.

Do not import ETC regret files into FiniteBanditModelInvariants.lean.

Do not introduce empirical means, commit argmax, probability, concentration, filtration, conditional expectation, or final ETC theorem facts.

Mark complete only after:

Bash
python3 tools/bandit.py check

passes.

After this compiles, Candidate A should be the next review target.
