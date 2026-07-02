# Extended Pro Review Prompt: After Non-Commit Suffix Count

ABRL Lean 4 status:

- `ETC-ACTION-WITH-COMMIT-SUFFIX-COUNT` compiles locally.
- `ETC-ACTION-WITH-COMMIT-NONCOMMIT-SUFFIX-COUNT` now also compiles locally.

New theorem:

```lean
theorem ETC.pullCount_actionWithCommit_explorationPulls_mul_K_add_eq_of_ne
    {K : Nat} (spec : ETC.Spec K) {commitArm a : Fin K}
    (hne : commitArm ≠ a) (r : Nat) :
    pullCount (ETC.actionWithCommit spec commitArm) a
        (spec.explorationPulls * K + r) =
      spec.explorationPulls
```

Verification:

```text
python3 tools\bandit.py check
Build completed successfully (1781 jobs).
Build completed successfully (1783 jobs).
$ lake build
$ lake build Tests
check passed
```

`python3 tools\bandit.py unfinished` now says:

- `ETC-ACTION-WITH-COMMIT-NONCOMMIT-SUFFIX-COUNT` is compiled locally.
- Stop and ask reviewer/Extended Pro before proving commit-arm-only corollaries,
  adding phase-splitting helpers, extending `actionWithCommit` regret past the
  exploration horizon, or moving to probability/concentration/final theorem
  routes.

Please recommend the next exact single leaf:

1. Commit-arm-only suffix corollary, phase-splitting helper, or stop ETC count work?
2. Exact Lean-facing statement.
3. Imports/local APIs.
4. Intended proof route.
5. Regularity contracts, retrieval evidence, classification, and failure policy.
