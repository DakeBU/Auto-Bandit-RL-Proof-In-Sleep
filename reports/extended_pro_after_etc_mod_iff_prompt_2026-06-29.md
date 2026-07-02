# Extended Pro Review Prompt: After ETC-EXPLOREARM-EQ-IFF-MOD

We are working in the ABRL Lean 4 repository for formalizing bandit/RL theory.

Following your previous recommendation, I completed exactly one modular ETC
selector helper:

```text
ETC-EXPLOREARM-EQ-IFF-MOD
```

New compiled theorem, in `BanditRLProof/Algorithms/ETC.lean`:

```lean
theorem ETC.exploreArm_eq_iff_mod_eq_val
    {K : Nat} (spec : ETC.Spec K) (t : Nat) (a : Fin K) :
    ETC.exploreArm spec t = a ↔ t % K = a.val
```

Implementation route:

- one direction uses `congrArg Fin.val`;
- the reverse direction uses `Fin.ext`;
- both sides simplify through `ETC.exploreArm_val`;
- no new imports were needed.

Verification:

```text
lake build BanditRLProof.Algorithms.ETC
Build completed successfully (4 jobs).

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
- completion gap audit, project overview, collaborator guide,
  Mathlib foundation leaf map, theory tree;
- retrieval indexes and UCB/ETC memory refresh JSON.

Current ETC count surface:

```lean
theorem ETC.exploreArm_eq_iff_mod_eq_val
    {K : Nat} (spec : ETC.Spec K) (t : Nat) (a : Fin K) :
    ETC.exploreArm spec t = a ↔ t % K = a.val

theorem ETC.pullCount_exploreArm_K_eq_one
    {K : Nat}
    (spec : ETC.Spec K) (a : Fin K) :
    pullCount (ETC.exploreArm spec) a K = 1
```

Questions:

1. What is the next single executable leaf?
2. Should we now prove the multiple-full-cycle ETC count theorem
   `pullCount (ETC.exploreArm spec) a (m * K) = m`, or first prove a generic
   pull-count segment decomposition / shifted-block lemma?
3. What exact Lean-facing statement should be attempted next?
4. What imports/local APIs should it use?
5. What regularity contracts should it require?
6. How should it be classified: imported, port candidate, Mathlib candidate,
   project-local, or theorem-card-only?
7. What should the failure policy be?

Please keep the recommendation to one small compiled Lean leaf. Do not
recommend probability, concentration, empirical means, commit argmax, or a final
ETC regret theorem in this batch.
