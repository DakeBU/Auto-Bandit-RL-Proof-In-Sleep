# Short Extended Pro Retry: After Suffix Count

ABRL Lean 4 project status:

- `ETC-ACTION-WITH-COMMIT-SUFFIX-COUNT` now compiles locally.
- The theorem is:

```lean
theorem ETC.pullCount_actionWithCommit_explorationPulls_mul_K_add_eq
    {K : Nat} (spec : ETC.Spec K) (commitArm a : Fin K) (r : Nat) :
    pullCount (ETC.actionWithCommit spec commitArm) a
        (spec.explorationPulls * K + r) =
      spec.explorationPulls + (if commitArm = a then r else 0)
```

- `python3 tools\bandit.py check` passed.
- `python3 tools\bandit.py unfinished` now says to ask reviewer before
  commit-arm-only/non-commit-arm-only corollaries, phase splitting, regret past
  exploration horizon, probability/concentration, or final theorem work.

Please answer briefly with the next exact single leaf only:

1. Which leaf should be attempted next?
2. Exact Lean-facing statement.
3. Imports/local APIs.
4. Proof route.
5. Contracts/evidence/classification/failure policy.

Do not recommend probability/concentration unless deterministic ETC count work
should stop here.
