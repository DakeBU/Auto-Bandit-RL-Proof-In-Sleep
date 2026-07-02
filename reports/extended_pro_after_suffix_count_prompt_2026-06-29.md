# Extended Pro Review Prompt: After Suffix Count Leaf

We are working in `D:\code\Auto-Bandit-RL-Proof-In-Sleep-main\Auto-Bandit-RL-Proof-In-Sleep-main`, a Lean 4/Mathlib project for formalizing bandit and RL proof leaves.

Current discipline:

- Pick exactly one unfinished leaf at a time.
- A leaf is complete only after Lean compilation and `python3 tools\bandit.py check`.
- Ask reviewer/Extended Pro before widening to corollaries, phase splitting, regret past the exploration horizon, probability, filtration, concentration, or final algorithm theorems.

Previous Extended Pro recommendation:

- Implement `ETC-ACTION-WITH-COMMIT-SUFFIX-COUNT`.
- Keep the public horizon orientation `spec.explorationPulls * K + r`.
- Do not prove separate commit-arm-only or non-commit-arm-only corollaries in the same batch.

Completed in this batch:

```lean
theorem ETC.pullCount_actionWithCommit_explorationPulls_mul_K_add_eq
    {K : Nat} (spec : ETC.Spec K) (commitArm a : Fin K) (r : Nat) :
    pullCount (ETC.actionWithCommit spec commitArm) a
        (spec.explorationPulls * K + r) =
      spec.explorationPulls + (if commitArm = a then r else 0) := by
  induction r with
  | zero =>
      simp [ETC.pullCount_actionWithCommit_explorationPulls_mul_K_eq]
  | succ r ih =>
      have hge :
          spec.explorationPulls * K <= spec.explorationPulls * K + r :=
        Nat.le_add_right (spec.explorationPulls * K) r
      have hstep :
          pullCount (ETC.actionWithCommit spec commitArm) a
              (Nat.succ (spec.explorationPulls * K + r)) =
            pullCount (ETC.actionWithCommit spec commitArm) a
                (spec.explorationPulls * K + r) +
              if commitArm = a then 1 else 0 :=
        ETC.pullCount_actionWithCommit_succ_eq_add_if_commitArm_of_ge
          (spec := spec)
          (commitArm := commitArm)
          (a := a)
          (t := spec.explorationPulls * K + r)
          hge
      rw [Nat.add_succ]
      rw [hstep]
      rw [ih]
      by_cases h : commitArm = a
      · simp [h, Nat.add_assoc]
      · simp [h]
```

Local file:

- `BanditRLProof/Algorithms/ETCTraceCountLemmas.lean`

Consumer test added:

- `Tests/Basic.lean` example for `Fin 2`.

Index/tooling updates:

- `tools/bandit.py` now records `ETC-ACTION-WITH-COMMIT-SUFFIX-COUNT` under `LOCAL-LEAF-ETC-TRACE-COUNT`.
- `python3 tools\bandit.py unfinished` now reports it as compiled locally and says to stop before commit-arm-only or non-commit-arm-only corollaries, phase-splitting helpers, regret past the exploration horizon, or probability/concentration/final-theorem work.
- `research-wiki/retrieval-index/local_lean_declarations.json` now has 130 declarations.
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

`python3 tools\bandit.py list-lean-decls explorationPulls_mul_K_add --statement` reports:

```text
ETC.pullCount_actionWithCommit_explorationPulls_mul_K_add_eq [theorem] BanditRLProof/Algorithms/ETCTraceCountLemmas.lean:96
  theorem ETC.pullCount_actionWithCommit_explorationPulls_mul_K_add_eq {K : Nat} (spec : ETC.Spec K) (commitArm a : Fin K) (r : Nat) : pullCount (ETC.actionWithCommit spec commitArm) a (spec.explorationPulls * K + r) = spec.explorationPulls + (if commitArm = a then r else 0)
```

Current boundary:

- Completed deterministic finite ETC trace/count leaves through closed-form post-exploration suffix counts.
- Still missing: commit-arm-only and non-commit-arm-only corollaries, phase splitting, full actionWithCommit regret after the exploration horizon, empirical best-arm/commit correctness, concentration, filtration, and final theorem routes.

Please review:

1. Is the completed suffix-count theorem scoped correctly and mathematically useful?
2. Is its statement the right local API for downstream ETC regret work?
3. What is the next exact single leaf to attempt?
4. If the next leaf should be a commit-arm-only corollary, non-commit-arm stability corollary, or phase-splitting helper, give the exact Lean-facing statement, imports, proof route, contracts, retrieval evidence, classification, and failure policy.
5. Should we stop deterministic ETC trace/count work here and move to probability/concentration, or close one more deterministic corollary first?
