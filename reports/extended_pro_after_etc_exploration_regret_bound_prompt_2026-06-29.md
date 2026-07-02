# Extended Pro Review Prompt: After ETC-EXPLORATION-REGRET-BOUND

We are working in the ABRL Lean 4 repository for formalizing bandit/RL theory.

Following your previous recommendation, I completed exactly one deterministic
ETC exploration-only regret scaffold:

```text
ETC-EXPLORATION-REGRET-BOUND
```

New compiled theorem, in `BanditRLProof/Algorithms/ETCRegretLemmas.lean`:

```lean
theorem ETC.pseudoRegret_exploreArm_explorationPulls_mul_K_le_sum_gap_mul_explorationPulls
    {K : Nat}
    (spec : ETC.Spec K) (model : FiniteBanditModel K) :
    pseudoRegret model (ETC.exploreArm spec) (spec.explorationPulls * K) <=
      ((Finset.univ : Finset (Fin K)).sum
        (fun a : Fin K => model.gap a)) *
        (((spec.explorationPulls : Nat) : Rat))
```

Implementation route:

- import `BanditRLProof.RegretCountBounds`;
- import `BanditRLProof.Algorithms.ETCCountLemmas`;
- instantiate `pseudoRegret_le_sum_gap_mul_uniform_nat_count_bound` with
  `action := ETC.exploreArm spec`,
  `n := spec.explorationPulls * K`,
  and `B := spec.explorationPulls`;
- discharge the uniform count bound with
  `ETC.pullCount_exploreArm_explorationPulls_mul_K_eq`.

Current local ETC deterministic surface:

```lean
theorem ETC.pullCount_exploreArm_explorationPulls_mul_K_eq
    {K : Nat}
    (spec : ETC.Spec K) (a : Fin K) :
    pullCount (ETC.exploreArm spec) a (spec.explorationPulls * K) =
      spec.explorationPulls

theorem ETC.pseudoRegret_exploreArm_explorationPulls_mul_K_le_sum_gap_mul_explorationPulls
    {K : Nat}
    (spec : ETC.Spec K) (model : FiniteBanditModel K) :
    pseudoRegret model (ETC.exploreArm spec) (spec.explorationPulls * K) <=
      ((Finset.univ : Finset (Fin K)).sum
        (fun a : Fin K => model.gap a)) *
        (((spec.explorationPulls : Nat) : Rat))
```

Verification from the current worktree:

```text
python3 tools/bandit.py check
Build completed successfully (1779 jobs).
Build completed successfully (1781 jobs).
$ lake build
$ lake build Tests
check passed
```

Updated:

- new file `BanditRLProof/Algorithms/ETCRegretLemmas.lean`;
- root import in `BanditRLProof.lean`;
- one consumer test in `Tests/Basic.lean`;
- `tools/bandit.py` local leaf card and `unfinished` recommendation output;
- completion gap audit, project overview, collaborator guide,
  Mathlib foundation leaf map, theory tree;
- retrieval indexes and UCB/ETC memory refresh JSON.

Current boundary:

- No phase-switching ETC action trace with commit behavior.
- No empirical mean or commit argmax theorem.
- No probability, expectation, filtration, concentration, or final ETC regret
  theorem.
- Existing deterministic regret adapters are compiled:
  `REGRET-COUNT-BOUND`, `REGRET-NAT-COUNT-BOUND`,
  `REGRET-UNIFORM-NAT-COUNT-BOUND`.

Questions:

1. What is the next single executable leaf?
2. Should we now define a phase-switching ETC action trace boundary, or keep
   extending deterministic ETC-only scaffolds?
3. What exact Lean-facing statement should be attempted next?
4. What imports/local APIs should it use?
5. What regularity contracts should it require?
6. How should it be classified: imported, port candidate, Mathlib candidate,
   project-local, or theorem-card-only?
7. What should the failure policy be?

Please keep the recommendation to one small compiled Lean leaf. Do not
recommend probability, concentration, empirical means, commit argmax, or a final
ETC regret theorem in this batch.
