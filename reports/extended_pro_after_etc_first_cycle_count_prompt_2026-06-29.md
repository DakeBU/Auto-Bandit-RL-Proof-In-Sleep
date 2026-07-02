# Extended Pro Review Prompt: After ETC-ROUND-ROBIN-FIRST-CYCLE-COUNT

We are working in the ABRL Lean 4 repository for formalizing bandit/RL theory.

Following your previous recommendation, I completed exactly one ETC-specific
deterministic count scaffold:

```text
ETC-ROUND-ROBIN-FIRST-CYCLE-COUNT
```

New compiled theorem, in `BanditRLProof/Algorithms/ETCCountLemmas.lean`:

```lean
theorem ETC.pullCount_exploreArm_K_eq_one
    {K : Nat}
    (spec : ETC.Spec K) (a : Fin K) :
    pullCount (ETC.exploreArm spec) a K = 1
```

Implementation route:

- import `Mathlib.Data.Finset.Card`, `BanditRLProof.MathlibWrappers`,
  and `BanditRLProof.Algorithms.ETC`;
- rewrite `pullCount` with `pullCount_eq_finset_filter_card`;
- prove the filtered first-cycle time set
  `{s in Finset.range K | ETC.exploreArm spec s = a}` is exactly
  `({a.val} : Finset Nat)`;
- simplify the singleton cardinality.

Verification:

```text
lake build BanditRLProof.Algorithms.ETCCountLemmas
Build completed successfully (729 jobs).

lake build Tests
Build completed successfully (1780 jobs).

python3 tools/bandit.py check
Build completed successfully (1778 jobs).
Build completed successfully (1780 jobs).
$ lake build
$ lake build Tests
check passed
```

Updated:

- root import in `BanditRLProof.lean`;
- one consumer test in `Tests/Basic.lean`;
- `tools/bandit.py` local leaf card and `unfinished` recommendation output;
- README, completion gap audit, project overview, collaborator guide,
  Mathlib foundation leaf map, theory tree;
- retrieval indexes and UCB/ETC memory refresh JSON.

Current boundary:

- We still do not have a full ETC action trace with commit behavior.
- The only compiled ETC count theorem is the first-cycle statement above.
- Existing deterministic regret adapters are compiled:
  `REGRET-COUNT-BOUND`, `REGRET-NAT-COUNT-BOUND`,
  `REGRET-UNIFORM-NAT-COUNT-BOUND`.
- Still no Rat-valued Bochner expected regret theorem, filtration,
  conditional expectation, sub-Gaussian/Hoeffding/martingale tail theorem,
  or final UCB/ETC theorem.
- `theorem-card` rows are still route cards only, not local Lean proofs.

Questions:

1. What is the next single executable leaf?
2. Should it generalize the ETC count theorem to multiple full cycles
   (`m * K` horizon), define an exploration-phase action trace boundary, or do
   another smaller modular/count helper first?
3. What exact Lean-facing statement should be attempted next?
4. What imports/local APIs should it use?
5. What regularity contracts should it require?
6. How should it be classified: imported, port candidate, Mathlib candidate,
   project-local, or theorem-card-only?
7. What should the failure policy be?

Please keep the recommendation to one small compiled Lean leaf. Do not
recommend jumping directly to probability, concentration, empirical means,
commit argmax, or a final ETC regret theorem in the same batch.
