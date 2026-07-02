# Extended Pro Review Prompt: After ETC-ACTION-WITH-COMMIT-EXPLORE-PREFIX-PULLCOUNT

We are working in the ABRL Lean 4 repository for formalizing bandit/RL theory.

Following your previous recommendation, I completed exactly one deterministic
ETC trace/count transfer leaf:

```text
ETC-ACTION-WITH-COMMIT-EXPLORE-PREFIX-PULLCOUNT
```

New compiled file:

```text
BanditRLProof/Algorithms/ETCTraceCountLemmas.lean
```

Compiled theorem:

```lean
theorem ETC.pullCount_actionWithCommit_eq_pullCount_exploreArm_of_le
    {K : Nat} (spec : ETC.Spec K) (commitArm a : Fin K)
    (n : Nat) (hn : n <= spec.explorationPulls * K) :
    pullCount (ETC.actionWithCommit spec commitArm) a n =
      pullCount (ETC.exploreArm spec) a n
```

Implementation route:

- imports only `BanditRLProof.LeafLemmas` and
  `BanditRLProof.Algorithms.ETCTrace`;
- proves by induction on `n` after reverting `hn`;
- successor step uses `ETC.actionWithCommit_eq_exploreArm_of_lt`;
- does not import `ETCCountLemmas`, `ETCRegretLemmas`, or
  `RegretCountBounds`;
- does not prove the exploration-horizon count theorem;
- does not introduce regret facts, empirical means, commit argmax, probability,
  concentration, filtration, conditional expectation, or final ETC theorem
  facts.

Current local ETC trace/count surface:

```lean
def ETC.actionWithCommit

@[simp] theorem ETC.actionWithCommit_eq_exploreArm_of_lt
    {K : Nat} (spec : ETC.Spec K) (commitArm : Fin K) {t : Nat}
    (h : t < spec.explorationPulls * K) :
    ETC.actionWithCommit spec commitArm t = ETC.exploreArm spec t

@[simp] theorem ETC.actionWithCommit_eq_commitArm_of_ge
    {K : Nat} (spec : ETC.Spec K) (commitArm : Fin K) {t : Nat}
    (h : spec.explorationPulls * K <= t) :
    ETC.actionWithCommit spec commitArm t = commitArm

theorem ETC.pullCount_actionWithCommit_eq_pullCount_exploreArm_of_le
    {K : Nat} (spec : ETC.Spec K) (commitArm a : Fin K)
    (n : Nat) (hn : n <= spec.explorationPulls * K) :
    pullCount (ETC.actionWithCommit spec commitArm) a n =
      pullCount (ETC.exploreArm spec) a n
```

Existing pure exploration horizon count theorem:

```lean
theorem ETC.pullCount_exploreArm_explorationPulls_mul_K_eq
    {K : Nat}
    (spec : ETC.Spec K) (a : Fin K) :
    pullCount (ETC.exploreArm spec) a (spec.explorationPulls * K) =
      spec.explorationPulls
```

Verification from the current worktree:

```text
python3 tools/bandit.py list-lean-decls pullCount_actionWithCommit --statement
ETC.pullCount_actionWithCommit_eq_pullCount_exploreArm_of_le [theorem] BanditRLProof/Algorithms/ETCTraceCountLemmas.lean:22
  theorem ETC.pullCount_actionWithCommit_eq_pullCount_exploreArm_of_le {K : Nat} (spec : ETC.Spec K) (commitArm a : Fin K) (n : Nat) (hn : n <= spec.explorationPulls * K) : pullCount (ETC.actionWithCommit spec commitArm) a n = pullCount (ETC.exploreArm spec) a n

python3 tools/bandit.py check
Build completed successfully (1781 jobs).
Build completed successfully (1783 jobs).
$ lake build
$ lake build Tests
check passed
```

Updated:

- root import in `BanditRLProof.lean`;
- one consumer test in `Tests/Basic.lean`;
- `tools/bandit.py` local leaf card and `unfinished` recommendation output;
- `README.md`, completion gap audit, project overview, collaborator guide,
  Mathlib foundation leaf map, bandit theory tree;
- retrieval indexes and UCB/ETC memory refresh JSON.

Questions:

1. Is the next single executable leaf the exploration-horizon count for
   `ETC.actionWithCommit`?
2. What exact Lean-facing statement should be attempted next?
3. Should it live in `BanditRLProof/Algorithms/ETCTraceCountLemmas.lean`?
4. Should it import/use `BanditRLProof.Algorithms.ETCCountLemmas`, or should it
   avoid that import and stay below pure ETC count lemmas?
5. What regularity contracts should it require?
6. How should it be classified: imported, port candidate, Mathlib candidate,
   project-local, or theorem-card-only?
7. What should the failure policy be?

Please keep the recommendation to one small compiled Lean leaf. Do not
recommend regret facts, empirical means, commit argmax, probability,
concentration, filtration, conditional expectation, or a final ETC regret
theorem in this batch.
