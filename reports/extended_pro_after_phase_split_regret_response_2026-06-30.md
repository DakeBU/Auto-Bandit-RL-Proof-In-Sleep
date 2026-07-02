# Extended Pro Review Response: After ETC Phase-Split Regret

- Date: 2026-06-30
- Tool/model: ChatGPT Extended Pro
- URL: https://chatgpt.com/c/6a41e1dc-fcf0-83e8-bcb2-27cfa0eab3ad
- Prompt file: `reports/extended_pro_after_phase_split_regret_candidate_prompt_2026-06-30.md`
- Local gate before review: `python3 tools\bandit.py check`
- Boundary:
  `ETC-ACTION-WITH-COMMIT-PHASE-SPLIT-REGRET`
- Recorded from raw response:
  `reports/extended_pro_after_phase_split_regret_raw_response_2026-06-30.txt`

## Reviewer Decision

- Chosen next leaf: ETC-ACTION-WITH-COMMIT-PHASE-SPLIT-REGRET-BOUND
- Classification: project-local deterministic ETC regret scaffold
- Status: reviewer-approved

## Exact Lean-Facing Statement

```lean
theorem ETC.pseudoRegret_actionWithCommit_explorationPulls_mul_K_add_le_sum_gap_mul_explorationPulls_add_suffix_gap
    {K : Nat}
    (spec : ETC.Spec K) (model : FiniteBanditModel K)
    (commitArm : Fin K) (r : Nat) :
    pseudoRegret model (ETC.actionWithCommit spec commitArm)
        (spec.explorationPulls * K + r) <=
      ((Finset.univ : Finset (Fin K)).sum
        (fun a : Fin K => model.gap a)) *
        (((spec.explorationPulls : Nat) : Rat)) +
      (((r : Nat) : Rat) * model.gap commitArm)
```

## Imports And Local APIs

- No new imports beyond `BanditRLProof.Algorithms.ETCRegretLemmas`.
- `ETC.pseudoRegret_actionWithCommit_explorationPulls_mul_K_add_eq_add_suffix_gap`
- `ETC.pseudoRegret_actionWithCommit_explorationPulls_mul_K_le_sum_gap_mul_explorationPulls`

## Intended Proof Route

1. Rewrite with the phase-split equality.
2. Apply the exploration-horizon bound.
3. Preserve the suffix term with `add_le_add` and `le_refl`.

## Regularity Contracts

- Only `{K : Nat}`, `spec : ETC.Spec K`, `model : FiniteBanditModel K`,
  `commitArm : Fin K`, and `r : Nat`.
- No empirical means, commit argmax, probability, concentration, filtration,
  conditional expectation, or final ETC theorem facts.

## Retrieval Evidence

- Local compiled phase-split equality and local compiled exploration-horizon
  regret bound.

## Failure Policy

- Fail closed: do not prove the Finset RHS simplification or generic
  constant-arm suffix lemma in the same batch.

## Raw Extended Pro Response

Pick

Pick Candidate A: Phase-Split Bound Consumer.

It is now the smallest useful next leaf. You already compiled the exact phase-split equality and the exploration-horizon regret bound. Candidate A simply composes them. Candidate B is a separate Finset algebra simplification and likely more brittle. Candidate C is reusable but broader and no longer necessary before using the ETC-specific phase split.

Leaf
ETC-ACTION-WITH-COMMIT-PHASE-SPLIT-REGRET-BOUND
Exact Lean-facing statement

Add this theorem to:

BanditRLProof/Algorithms/ETCRegretLemmas.lean

after the phase-split equality theorem.

lean
theorem ETC.pseudoRegret_actionWithCommit_explorationPulls_mul_K_add_le_sum_gap_mul_explorationPulls_add_suffix_gap
    {K : Nat}
    (spec : ETC.Spec K) (model : FiniteBanditModel K)
    (commitArm : Fin K) (r : Nat) :
    pseudoRegret model (ETC.actionWithCommit spec commitArm)
        (spec.explorationPulls * K + r) <=
      ((Finset.univ : Finset (Fin K)).sum
        (fun a : Fin K => model.gap a)) *
        (((spec.explorationPulls : Nat) : Rat)) +
      (((r : Nat) : Rat) * model.gap commitArm) := by
  rw [ETC.pseudoRegret_actionWithCommit_explorationPulls_mul_K_add_eq_add_suffix_gap
    (spec := spec)
    (model := model)
    (commitArm := commitArm)
    (r := r)]
  exact
    add_le_add_right
      (ETC.pseudoRegret_actionWithCommit_explorationPulls_mul_K_le_sum_gap_mul_explorationPulls
        (spec := spec)
        (model := model)
        (commitArm := commitArm))
      ((((r : Nat) : Rat) * model.gap commitArm))
Imports and local APIs

No new import should be needed if this lives in ETCRegretLemmas.lean.

Use exactly:

lean
ETC.pseudoRegret_actionWithCommit_explorationPulls_mul_K_add_eq_add_suffix_gap
ETC.pseudoRegret_actionWithCommit_explorationPulls_mul_K_le_sum_gap_mul_explorationPulls

Do not use or unfold:

lean
pseudoRegret
pullCount
ETC.actionWithCommit
ETC.pullCount_actionWithCommit_explorationPulls_mul_K_add_eq
pseudoRegret_le_finset_sum_gap_mul_nat_count_bound

This should be a pure consumer of the two compiled regret lemmas.

Intended proof route

Rewrite the LHS by the compiled phase-split equality:

lean
pseudoRegret ... (explorationPulls * K + r)
=
pseudoRegret ... (explorationPulls * K)
  + ((r : Rat) * model.gap commitArm)

Apply the exploration-horizon regret bound to the first summand:

lean
pseudoRegret ... (explorationPulls * K)
≤
(sum gaps) * explorationPulls

Preserve the suffix term with:

lean
add_le_add_right

No Rat arithmetic normalization should be needed.

Regularity contracts

Require only:

lean
{K : Nat}
(spec : ETC.Spec K)
(model : FiniteBanditModel K)
(commitArm : Fin K)
(r : Nat)

Do not add:

lean
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
Retrieval evidence and classification

Local declarations consumed:

lean
ETC.pseudoRegret_actionWithCommit_explorationPulls_mul_K_add_eq_add_suffix_gap
ETC.pseudoRegret_actionWithCommit_explorationPulls_mul_K_le_sum_gap_mul_explorationPulls

Classification:

ETC-ACTION-WITH-COMMIT-PHASE-SPLIT-REGRET-BOUND:
  project-local compiled ETC deterministic regret scaffold

It is not:

imported
port candidate
Mathlib candidate
theorem-card-only
probability/concentration leaf
empirical-mean leaf
final ETC theorem
Failure policy

If this leaf fails:

First isolate the exploration bound:

lean
have hexplore :
    pseudoRegret model (ETC.actionWithCommit spec commitArm)
        (spec.explorationPulls * K) <=
      ((Finset.univ : Finset (Fin K)).sum
        (fun a : Fin K => model.gap a)) *
        (((spec.explorationPulls : Nat) : Rat)) :=
  ETC.pseudoRegret_actionWithCommit_explorationPulls_mul_K_le_sum_gap_mul_explorationPulls
    (spec := spec) (model := model) (commitArm := commitArm)

Then:

lean
rw [ETC.pseudoRegret_actionWithCommit_explorationPulls_mul_K_add_eq_add_suffix_gap
  (spec := spec) (model := model) (commitArm := commitArm) (r := r)]
exact add_le_add_right hexplore
  ((((r : Nat) : Rat) * model.gap commitArm))

If theorem resolution is brittle, fully qualify both local theorem names.

If RHS associativity or shape unexpectedly mismatches, do not introduce ring tactics immediately. Use change to align the exact RHS shape with the statement.

Do not prove Candidate B or Candidate C in the same batch.

Do not introduce empirical means, commit argmax, probability, concentration, filtration, conditional expectation, or final ETC theorem facts.

Mark complete only after:

Bash
python3 tools/bandit.py check

passes.
