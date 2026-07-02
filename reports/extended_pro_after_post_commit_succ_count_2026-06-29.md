# Extended Pro Review: After Post-Commit Succ Count Leaf

Prompt file:

- `reports/extended_pro_after_post_commit_succ_count_prompt_2026-06-29.md`

Local verification before review:

```text
python3 tools\bandit.py check
Build completed successfully (1781 jobs).
Build completed successfully (1783 jobs).
$ lake build
$ lake build Tests
check passed
```

## Review Summary

Extended Pro judged
`ETC.pullCount_actionWithCommit_succ_eq_add_if_commitArm_of_ge` to be scoped
correctly and mathematically useful.  It explicitly said the statement is in
the right orientation because `Nat.succ t` matches `pullCount_succ`; do not
restate it as `t + 1` unless a later proof repeatedly needs that convenience
shape.

## Recommended Next Single Leaf

Recommended row:

```text
ETC-ACTION-WITH-COMMIT-SUFFIX-COUNT
```

Recommended theorem name:

```lean
ETC.pullCount_actionWithCommit_explorationPulls_mul_K_add_eq
```

Recommended exact statement:

```lean
theorem ETC.pullCount_actionWithCommit_explorationPulls_mul_K_add_eq
    {K : Nat} (spec : ETC.Spec K) (commitArm a : Fin K) (r : Nat) :
    pullCount (ETC.actionWithCommit spec commitArm) a
        (spec.explorationPulls * K + r) =
      spec.explorationPulls + (if commitArm = a then r else 0)
```

## Intended Route

Add the theorem to:

```text
BanditRLProof/Algorithms/ETCTraceCountLemmas.lean
```

Use induction on `r`.

Base case:

- consume `ETC.pullCount_actionWithCommit_explorationPulls_mul_K_eq`.

Successor case:

- prove `spec.explorationPulls * K <= spec.explorationPulls * K + r`,
  preferably by `Nat.le_add_right`;
- consume
  `ETC.pullCount_actionWithCommit_succ_eq_add_if_commitArm_of_ge`;
- rewrite with `Nat.add_succ`;
- use the induction hypothesis;
- split on `commitArm = a` if arithmetic simplification is brittle.

## Imports And APIs

No new imports should be needed beyond the current
`ETCTraceCountLemmas.lean` imports.

The theorem should use exactly these local proof inputs:

```lean
ETC.pullCount_actionWithCommit_explorationPulls_mul_K_eq
ETC.pullCount_actionWithCommit_succ_eq_add_if_commitArm_of_ge
```

It should not reopen the definitions of `pullCount`, `ETC.actionWithCommit`,
`ETC.exploreArm`, or the phase-boundary lemmas.

## Regularity Contracts

Require only:

```lean
{K : Nat}
(spec : ETC.Spec K)
(commitArm a : Fin K)
(r : Nat)
```

Do not add probability, measure, `Rat`, `ENNReal`, empirical mean,
concentration, filtration, or final regret assumptions.

## Classification

Classification:

```text
project-local compiled ETC deterministic trace/count closed form
```

Not an imported theorem, Mathlib candidate, probability/concentration leaf,
empirical-mean leaf, or final ETC theorem.

## Failure Policy

Keep the public horizon orientation:

```lean
spec.explorationPulls * K + r
```

Do not switch to `r + spec.explorationPulls * K` unless this orientation is
genuinely blocked.  If final arithmetic is brittle, keep an explicit case split:

```lean
by_cases h : commitArm = a
· simp [h, Nat.add_assoc, Nat.succ_eq_add_one]
· simp [h]
```

Do not prove separate commit-arm-only or non-commit-arm-only corollaries in this
batch.  Do not add regret facts, empirical means, commit argmax, probability,
concentration, filtration, conditional expectation, or final ETC theorem facts.

Mark complete only after:

```bash
python3 tools/bandit.py check
```

Then ask again.
