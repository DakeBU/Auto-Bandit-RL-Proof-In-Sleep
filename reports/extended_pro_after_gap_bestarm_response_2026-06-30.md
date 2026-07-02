# Extended Pro Review Response: After Finite-Bandit Gap BestArm Ledger

- Date: 2026-06-30
- Tool/model: ChatGPT Extended Pro
- URL: https://chatgpt.com/c/6a41e1dc-fcf0-83e8-bcb2-27cfa0eab3ad
- Prompt file: `reports/extended_pro_after_gap_bestarm_candidate_prompt_2026-06-30.md`
- Local gate before review: `python3 tools\bandit.py check`
- Boundary:
  `FINITE-BANDIT-GAP-BESTARM`
- Recorded from raw response:
  `reports/extended_pro_after_gap_bestarm_raw_response_2026-06-30.txt`

## Reviewer Decision

- Chosen next leaf: ETC-ACTION-WITH-COMMIT-BESTARM-SUFFIX-NO-REGRET
- Classification: project-local
- Status: reviewer-approved

## Exact Lean-Facing Statement

```lean
theorem ETC.pseudoRegret_actionWithCommit_explorationPulls_mul_K_add_eq_of_commitArm_eq_bestArm
    {K : Nat}
    (spec : ETC.Spec K) (model : FiniteBanditModel K)
    (commitArm : Fin K) (r : Nat)
    (hcommit : commitArm = model.bestArm) :
    pseudoRegret model (ETC.actionWithCommit spec commitArm)
        (spec.explorationPulls * K + r) =
      pseudoRegret model (ETC.actionWithCommit spec commitArm)
        (spec.explorationPulls * K)
```

## Imports And Local APIs

- File: `BanditRLProof/Algorithms/ETCRegretLemmas.lean`.
- Local APIs: `ETC.pseudoRegret_actionWithCommit_explorationPulls_mul_K_add_eq_add_suffix_gap`,
  `FiniteBanditModel.gap_bestArm`.
- Existing imports should suffice through `BanditRLProof.RegretCountBounds`
  and `BanditRLProof.Algorithms.ETCTraceCountLemmas`.
- Do not import probability, ENNReal, filtration, concentration, empirical
  mean, or root project files.

## Intended Proof Route

1. Rewrite with the compiled phase-split equality.
2. Rewrite `commitArm` to `model.bestArm` using `hcommit`.
3. Simplify `model.gap model.bestArm = 0`, `r * 0 = 0`, and `x + 0 = x`.

## Regularity Contracts

- Require only `{K : Nat}`, `spec : ETC.Spec K`,
  `model : FiniteBanditModel K`, `commitArm : Fin K`, `r : Nat`, and
  `hcommit : commitArm = model.bestArm`.
- No empirical means, commit argmax, probability, concentration, filtration,
  conditional expectation, or final ETC theorem assumptions.

## Retrieval Evidence

- Local declaration: `FiniteBanditModel.gap_bestArm`.
- Local declaration:
  `ETC.pseudoRegret_actionWithCommit_explorationPulls_mul_K_add_eq_add_suffix_gap`.
- Extended Pro classified this as a project-local deterministic ETC scaffold.

## Failure Policy

- If `rw [hcommit]` rewrites the wrong way, use `subst commitArm`.
- If the gap rewrite is not found, fully qualify
  `BanditRLProof.FiniteBanditModel.gap_bestArm`.
- Do not prove the best-arm commit trace lemma, generic constant-arm suffix
  lemma, RHS simplification, empirical commit selection, probability, or
  concentration facts in the same batch.

## Raw Extended Pro Response

Pick

Pick Candidate A: Optimal Commit Has No Extra Suffix Regret.

FiniteBanditModel.gap_bestArm is already compiled, so the missing prerequisite is resolved. Candidate B is true and may be useful later, but Candidate A is the more valuable next deterministic regret scaffold. It consumes the already compiled phase-split theorem and the best-arm gap theorem directly.

Leaf
ETC-ACTION-WITH-COMMIT-BESTARM-SUFFIX-NO-REGRET
Exact Lean-facing statement

Add this to:

BanditRLProof/Algorithms/ETCRegretLemmas.lean

after:

lean
ETC.pseudoRegret_actionWithCommit_explorationPulls_mul_K_add_eq_add_suffix_gap

Recommended theorem:

lean
theorem ETC.pseudoRegret_actionWithCommit_explorationPulls_mul_K_add_eq_of_commitArm_eq_bestArm
    {K : Nat}
    (spec : ETC.Spec K) (model : FiniteBanditModel K)
    (commitArm : Fin K) (r : Nat)
    (hcommit : commitArm = model.bestArm) :
    pseudoRegret model (ETC.actionWithCommit spec commitArm)
        (spec.explorationPulls * K + r) =
      pseudoRegret model (ETC.actionWithCommit spec commitArm)
        (spec.explorationPulls * K) := by
  rw [ETC.pseudoRegret_actionWithCommit_explorationPulls_mul_K_add_eq_add_suffix_gap
    (spec := spec)
    (model := model)
    (commitArm := commitArm)
    (r := r)]
  rw [hcommit]
  simp [FiniteBanditModel.gap_bestArm]

If the final simp does not close, use the explicit form:

lean
  rw [FiniteBanditModel.gap_bestArm]
  simp

or:

lean
  rw [FiniteBanditModel.gap_bestArm]
  ring_nf

only if ring normalization is already available in the file. Prefer the non-tactic route first.

Imports and local APIs

ETCRegretLemmas.lean should already import the local ETC trace/regret material. Ensure it can see:

lean
FiniteBanditModel.gap_bestArm
ETC.pseudoRegret_actionWithCommit_explorationPulls_mul_K_add_eq_add_suffix_gap

Expected local imports:

lean
import BanditRLProof.RegretCountBounds
import BanditRLProof.Algorithms.ETCTraceCountLemmas

If FiniteBanditModel.gap_bestArm is in BanditRLProof.Core and not already visible transitively, add the narrow import:

lean
import BanditRLProof.Core

Do not import probability, ENNReal, filtration, concentration, empirical-mean files, or the project root.

Intended proof route

Rewrite the LHS by the compiled phase-split equality:

lean
pseudoRegret ... (exploration horizon + r)
=
pseudoRegret ... exploration horizon
  + ((r : Rat) * model.gap commitArm)

Rewrite:

lean
commitArm = model.bestArm

Use:

lean
FiniteBanditModel.gap_bestArm

Simplify:

lean
((r : Rat) * 0) = 0
x + 0 = x

No induction. No pull-count reasoning. No Finset algebra.

Regularity contracts

Require only:

lean
{K : Nat}
(spec : ETC.Spec K)
(model : FiniteBanditModel K)
(commitArm : Fin K)
(r : Nat)
(hcommit : commitArm = model.bestArm)

Do not add:

lean
0 < K
Measure
MeasurableSpace
IsProbabilityMeasure
ENNReal
Real
Integrable
Filtration
SubGaussian
Empirical mean assumptions
Commit correctness assumptions
Concentration assumptions

The theorem is deterministic and local.

Retrieval evidence

Local declarations already available:

lean
FiniteBanditModel.gap_bestArm
ETC.pseudoRegret_actionWithCommit_explorationPulls_mul_K_add_eq_add_suffix_gap

The theorem should only consume those two local APIs. It should not depend on theorem-card material.

Classification

Classify as:

ETC-ACTION-WITH-COMMIT-BESTARM-SUFFIX-NO-REGRET:
  project-local compiled ETC deterministic regret scaffold

It is not:

imported
port candidate
Mathlib candidate
theorem-card-only
probability/concentration leaf
empirical-mean leaf
final ETC theorem

It is a local deterministic bridge for the idealized case where the commit arm is the true best arm.

Failure policy

Use a fail-closed policy.

If this leaf fails:

First isolate the phase split:

lean
have hsplit :=
  ETC.pseudoRegret_actionWithCommit_explorationPulls_mul_K_add_eq_add_suffix_gap
    (spec := spec)
    (model := model)
    (commitArm := commitArm)
    (r := r)
rw [hsplit]

If rw [hcommit] rewrites in the wrong direction, use:

lean
subst commitArm

immediately after introducing hcommit.

If FiniteBanditModel.gap_bestArm does not rewrite, fully qualify it:

lean
rw [BanditRLProof.FiniteBanditModel.gap_bestArm]

If the zero arithmetic is brittle, avoid broad tactics first:

lean
simp

then only use ring_nf if already available or if a narrow arithmetic import is acceptable.

Do not prove Candidate B in the same batch.

Do not introduce empirical means, commit argmax, probability, concentration, filtration, conditional expectation, or final ETC theorem facts.

Mark complete only after:

Bash
python3 tools/bandit.py check

passes.
