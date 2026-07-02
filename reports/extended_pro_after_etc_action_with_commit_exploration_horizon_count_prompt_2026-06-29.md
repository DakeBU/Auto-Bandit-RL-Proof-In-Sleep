# Extended Pro Review Prompt: After ETC-ACTION-WITH-COMMIT-EXPLORATION-HORIZON-COUNT

We are working in the ABRL Lean 4 repository for formalizing bandit/RL theory.

Following your previous recommendation, I completed exactly one deterministic
ETC trace/count adapter leaf:

```text
ETC-ACTION-WITH-COMMIT-EXPLORATION-HORIZON-COUNT
```

Updated compiled theorem in:

```text
BanditRLProof/Algorithms/ETCTraceCountLemmas.lean
```

Compiled theorem:

```lean
theorem ETC.pullCount_actionWithCommit_explorationPulls_mul_K_eq
    {K : Nat} (spec : ETC.Spec K) (commitArm a : Fin K) :
    pullCount (ETC.actionWithCommit spec commitArm) a
        (spec.explorationPulls * K) =
      spec.explorationPulls
```

Implementation route:

- `ETCTraceCountLemmas.lean` now imports
  `BanditRLProof.Algorithms.ETCCountLemmas`;
- the theorem uses the compiled prefix transfer
  `ETC.pullCount_actionWithCommit_eq_pullCount_exploreArm_of_le` at
  `n := spec.explorationPulls * K`;
- then closes with the pure exploration theorem
  `ETC.pullCount_exploreArm_explorationPulls_mul_K_eq`;
- no regret facts;
- no empirical means, commit argmax, probability, concentration, filtration,
  conditional expectation, or final ETC theorem facts.

Verification from the current worktree:

```text
python3 tools/bandit.py list-lean-decls pullCount_actionWithCommit --statement
ETC.pullCount_actionWithCommit_eq_pullCount_exploreArm_of_le [theorem] BanditRLProof/Algorithms/ETCTraceCountLemmas.lean:23
  theorem ETC.pullCount_actionWithCommit_eq_pullCount_exploreArm_of_le {K : Nat} (spec : ETC.Spec K) (commitArm a : Fin K) (n : Nat) (hn : n <= spec.explorationPulls * K) : pullCount (ETC.actionWithCommit spec commitArm) a n = pullCount (ETC.exploreArm spec) a n
ETC.pullCount_actionWithCommit_explorationPulls_mul_K_eq [theorem] BanditRLProof/Algorithms/ETCTraceCountLemmas.lean:53
  theorem ETC.pullCount_actionWithCommit_explorationPulls_mul_K_eq {K : Nat} (spec : ETC.Spec K) (commitArm a : Fin K) : pullCount (ETC.actionWithCommit spec commitArm) a (spec.explorationPulls * K) = spec.explorationPulls

python3 tools/bandit.py check
Build completed successfully (1781 jobs).
Build completed successfully (1783 jobs).
$ lake build
$ lake build Tests
check passed
```

Current boundary from `python3 tools/bandit.py unfinished`:

```text
Stop and ask reviewer/Extended Pro before proving post-exploration commit-arm
count increments, regret facts about actionWithCommit, adding phase-splitting
helpers, or moving to Rat-valued/Bochner expected regret, filtration,
concentration, or any algorithm-specific final theorem.
```

Questions:

1. What is the next single executable leaf?
2. Should the next leaf be a first post-exploration commit-arm count increment
   lemma, or a deterministic regret scaffold over the exploration horizon?
3. What exact Lean-facing statement should be attempted next?
4. What imports/local APIs should it use?
5. What regularity contracts should it require?
6. How should it be classified: imported, port candidate, Mathlib candidate,
   project-local, or theorem-card-only?
7. What should the failure policy be?

Please keep the recommendation to one small compiled Lean leaf. Do not
recommend empirical means, commit argmax, probability, concentration,
filtration, conditional expectation, or a final ETC regret theorem in this
batch.
