# Extended Pro Review Prompt: After ETC-ROUND-ROBIN-ADD-K-COUNT

We are working in the ABRL Lean 4 repository for formalizing bandit/RL theory.

Following your previous recommendation, I completed exactly one ETC shifted
cycle count lemma:

```text
ETC-ROUND-ROBIN-ADD-K-COUNT
```

New compiled theorem, in `BanditRLProof/Algorithms/ETCCountLemmas.lean`:

```lean
theorem ETC.pullCount_exploreArm_add_K_eq_add_one
    {K : Nat}
    (spec : ETC.Spec K) (a : Fin K) (t : Nat) :
    pullCount (ETC.exploreArm spec) a (t + K) =
      pullCount (ETC.exploreArm spec) a t + 1
```

Current local ETC count surface:

```lean
theorem ETC.exploreArm_eq_iff_mod_eq_val
    {K : Nat} (spec : ETC.Spec K) (t : Nat) (a : Fin K) :
    ETC.exploreArm spec t = a ↔ t % K = a.val

theorem ETC.pullCount_exploreArm_K_eq_one
    {K : Nat}
    (spec : ETC.Spec K) (a : Fin K) :
    pullCount (ETC.exploreArm spec) a K = 1

theorem ETC.pullCount_exploreArm_add_K_eq_add_one
    {K : Nat}
    (spec : ETC.Spec K) (a : Fin K) (t : Nat) :
    pullCount (ETC.exploreArm spec) a (t + K) =
      pullCount (ETC.exploreArm spec) a t + 1
```

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

- one consumer test in `Tests/Basic.lean`;
- `tools/bandit.py` local leaf card and `unfinished` recommendation output;
- README, completion gap audit, project overview, collaborator guide,
  Mathlib foundation leaf map, theory tree;
- retrieval indexes and UCB/ETC memory refresh JSON.

Current boundary:

- No full ETC action trace with commit behavior.
- No empirical mean or commit argmax theorem.
- No probability, expectation, filtration, concentration, or final ETC regret
  theorem.
- Existing deterministic regret adapters are compiled:
  `REGRET-COUNT-BOUND`, `REGRET-NAT-COUNT-BOUND`,
  `REGRET-UNIFORM-NAT-COUNT-BOUND`.

Questions:

1. Is the next single executable leaf now the multiple-full-cycle count theorem?
2. What exact Lean-facing statement should be attempted?
   In particular, should the horizon be written as `m * K`, `K * m`,
   `(m + 1) * K`, or another orientation that works best with the add-`K`
   recurrence?
3. What proof route should use `ETC.pullCount_exploreArm_add_K_eq_add_one`?
4. What imports/local APIs should it use?
5. What regularity contracts should it require?
6. How should it be classified: imported, port candidate, Mathlib candidate,
   project-local, or theorem-card-only?
7. What should the failure policy be?

Please keep the recommendation to one small compiled Lean leaf. Do not
recommend defining the full ETC trace, probability, concentration, empirical
means, commit argmax, or a final ETC regret theorem in this batch.
