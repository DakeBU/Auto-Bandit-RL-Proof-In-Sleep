# Extended Pro Review Prompt: After Commit-Arm Suffix Count

ABRL Lean 4 status:

- `ETC-ACTION-WITH-COMMIT-SUFFIX-COUNT` compiles locally.
- `ETC-ACTION-WITH-COMMIT-NONCOMMIT-SUFFIX-COUNT` compiles locally.
- `ETC-ACTION-WITH-COMMIT-COMMITARM-SUFFIX-COUNT` now also compiles locally.

Newest theorem:

```lean
theorem ETC.pullCount_actionWithCommit_explorationPulls_mul_K_add_eq_commitArm
    {K : Nat} (spec : ETC.Spec K) (commitArm : Fin K) (r : Nat) :
    pullCount (ETC.actionWithCommit spec commitArm) commitArm
        (spec.explorationPulls * K + r) =
      spec.explorationPulls + r
```

Verification:

```text
lake build Tests
Build completed successfully (1783 jobs).
```

The local `unfinished` boundary should now be:

- stop and ask reviewer/Extended Pro before adding phase-splitting helpers,
  extending `actionWithCommit` regret past the exploration horizon, or moving
  to probability/concentration/final theorem routes.

Please recommend the next exact single leaf:

1. Phase-splitting helper, deterministic post-horizon regret extension, or stop
   deterministic ETC work?
2. Exact Lean-facing statement.
3. Imports/local APIs.
4. Intended proof route.
5. Regularity contracts, retrieval evidence, classification, and failure policy.
