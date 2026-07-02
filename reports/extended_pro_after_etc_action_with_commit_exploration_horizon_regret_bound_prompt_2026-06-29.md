# Extended Pro Review Prompt: After ETC-ACTION-WITH-COMMIT-EXPLORATION-HORIZON-REGRET-BOUND

We are working in the ABRL Lean 4 repository for formalizing bandit/RL theory.

Following your previous recommendation, I completed exactly one deterministic
ETC regret scaffold:

```text
ETC-ACTION-WITH-COMMIT-EXPLORATION-HORIZON-REGRET-BOUND
```

Updated compiled theorem in:

```text
BanditRLProof/Algorithms/ETCRegretLemmas.lean
```

Compiled theorem:

```lean
theorem ETC.pseudoRegret_actionWithCommit_explorationPulls_mul_K_le_sum_gap_mul_explorationPulls
    {K : Nat}
    (spec : ETC.Spec K) (model : FiniteBanditModel K) (commitArm : Fin K) :
    pseudoRegret model (ETC.actionWithCommit spec commitArm)
        (spec.explorationPulls * K) <=
      ((Finset.univ : Finset (Fin K)).sum
        (fun a : Fin K => model.gap a)) *
        (((spec.explorationPulls : Nat) : Rat))
```

Implementation route:

- `ETCRegretLemmas.lean` imports `BanditRLProof.RegretCountBounds` and
  `BanditRLProof.Algorithms.ETCTraceCountLemmas`;
- theorem uses `pseudoRegret_le_sum_gap_mul_uniform_nat_count_bound`;
- count side is discharged with
  `ETC.pullCount_actionWithCommit_explorationPulls_mul_K_eq`;
- no post-exploration commit-arm count increment;
- no suffix-count helper;
- no empirical means, commit argmax, probability, concentration, filtration,
  conditional expectation, or final ETC theorem facts.

Verification from the current worktree:

```text
python3 tools/bandit.py list-lean-decls pseudoRegret_actionWithCommit --statement
ETC.pseudoRegret_actionWithCommit_explorationPulls_mul_K_le_sum_gap_mul_explorationPulls [theorem] BanditRLProof/Algorithms/ETCRegretLemmas.lean:48
  theorem ETC.pseudoRegret_actionWithCommit_explorationPulls_mul_K_le_sum_gap_mul_explorationPulls {K : Nat} (spec : ETC.Spec K) (model : FiniteBanditModel K) (commitArm : Fin K) : pseudoRegret model (ETC.actionWithCommit spec commitArm) (spec.explorationPulls * K) <= ((Finset.univ : Finset (Fin K)).sum (fun a : Fin K => model.gap a)) * (((spec.explorationPulls : Nat) : Rat))

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
count increments, adding phase-splitting helpers, extending actionWithCommit
regret past the exploration horizon, or moving to Rat-valued/Bochner expected
regret, filtration, concentration, or any algorithm-specific final theorem.
```

Questions:

1. What is the next single executable leaf?
2. Should it be a first post-exploration commit-arm count increment lemma or a
   generic suffix-count helper?
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
