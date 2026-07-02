# Extended Pro Review Prompt: After Post-Commit Succ Count Leaf

We are working in `D:\code\Auto-Bandit-RL-Proof-In-Sleep-main\Auto-Bandit-RL-Proof-In-Sleep-main`, a Lean 4/Mathlib project for formalizing bandit and RL proof leaves.

Current discipline:

- Pick exactly one unfinished leaf at a time.
- Theorem cards and proof weapons are route inspiration only, not local Lean proofs.
- A leaf is complete only after Lean compilation and `python3 tools\bandit.py check`.
- Ask reviewer/Extended Pro before widening to suffix-count helpers, regret past the exploration horizon, probability, filtration, concentration, or final algorithm theorems.

Recent prior recommendation from Extended Pro:

- Implement `ETC-ACTION-WITH-COMMIT-POST-COMMIT-SUCC-COUNT`.
- Use a one-step post-commit pull-count recurrence.
- Do not prove closed-form suffix counts in the same batch.

Completed in this batch:

```lean
theorem ETC.pullCount_actionWithCommit_succ_eq_add_if_commitArm_of_ge
    {K : Nat} (spec : ETC.Spec K) (commitArm a : Fin K) {t : Nat}
    (ht : spec.explorationPulls * K <= t) :
    pullCount (ETC.actionWithCommit spec commitArm) a (Nat.succ t) =
      pullCount (ETC.actionWithCommit spec commitArm) a t +
        if commitArm = a then 1 else 0 := by
  rw [pullCount_succ]
  have hact :
      ETC.actionWithCommit spec commitArm t = commitArm :=
    ETC.actionWithCommit_eq_commitArm_of_ge spec commitArm ht
  simp [hact]
```

Local file:

- `BanditRLProof/Algorithms/ETCTraceCountLemmas.lean`

Consumer test added:

- `Tests/Basic.lean` example instantiating the theorem for `Fin 2`.

Index/tooling updates:

- `tools/bandit.py` now records `ETC-ACTION-WITH-COMMIT-POST-COMMIT-SUCC-COUNT` under `LOCAL-LEAF-ETC-TRACE-COUNT`.
- `python3 tools\bandit.py unfinished` now reports it as compiled locally and says to stop before closed-form post-exploration suffix counts.
- `research-wiki/retrieval-index/local_lean_declarations.json` now has 129 declarations.
- Documentation updated in:
  - `README.md`
  - `docs/project_overview_next_plan.md`
  - `docs/completion_gap_audit.md`
  - `docs/collaborator_unfinished_work_guide.md`
  - `research-wiki/theory-tree/mathlib-foundation-leaf-map.md`
  - `research-wiki/theory-tree/bandit-theory-tree.md`

Verification:

```text
python3 tools\bandit.py check
Build completed successfully (1781 jobs).
Build completed successfully (1783 jobs).
$ lake build
$ lake build Tests
check passed
```

`python3 tools\bandit.py list-lean-decls succ_eq_add_if_commitArm --statement` reports:

```text
ETC.pullCount_actionWithCommit_succ_eq_add_if_commitArm_of_ge [theorem] BanditRLProof/Algorithms/ETCTraceCountLemmas.lean:76
  theorem ETC.pullCount_actionWithCommit_succ_eq_add_if_commitArm_of_ge {K : Nat} (spec : ETC.Spec K) (commitArm a : Fin K) {t : Nat} (ht : spec.explorationPulls * K <= t) : pullCount (ETC.actionWithCommit spec commitArm) a (Nat.succ t) = pullCount (ETC.actionWithCommit spec commitArm) a t + if commitArm = a then 1 else 0
```

Current boundary:

- Completed deterministic finite ETC trace/count leaves through one-step post-commit recurrence.
- Still missing: closed-form post-exploration suffix count, phase splitting, full actionWithCommit regret after the exploration horizon, empirical best-arm/commit correctness, concentration, filtration, and final theorem routes.

Please review:

1. Is the completed leaf scoped correctly and mathematically useful?
2. Is its statement the right local API, or should the recurrence be restated in a more convenient orientation before downstream use?
3. What is the next exact single leaf to attempt?
4. If the next leaf is a suffix-count theorem, give the exact Lean-facing statement, imports, proof route, contracts, retrieval evidence, classification, and failure policy.
5. If instead the next leaf should be a generic helper or a phase-splitting theorem, give that exact leaf with the same details.
