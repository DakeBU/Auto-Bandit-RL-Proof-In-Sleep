# Extended Pro Review Prompt: After ETC-ROUND-ROBIN-EXPLORATION-PULLS-COUNT

We are working in the ABRL Lean 4 repository for formalizing bandit/RL theory.

Following your previous recommendation, I completed exactly one configured ETC
exploration-horizon count adapter:

```text
ETC-ROUND-ROBIN-EXPLORATION-PULLS-COUNT
```

New compiled theorem, in `BanditRLProof/Algorithms/ETCCountLemmas.lean`:

```lean
theorem ETC.pullCount_exploreArm_explorationPulls_mul_K_eq
    {K : Nat}
    (spec : ETC.Spec K) (a : Fin K) :
    pullCount (ETC.exploreArm spec) a (spec.explorationPulls * K) =
      spec.explorationPulls
```

It specializes the compiled multiple-cycle theorem:

```lean
theorem ETC.pullCount_exploreArm_mul_K_eq
    {K : Nat}
    (spec : ETC.Spec K) (a : Fin K) (m : Nat) :
    pullCount (ETC.exploreArm spec) a (m * K) = m
```

Current ETC deterministic count surface:

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

theorem ETC.pullCount_exploreArm_mul_K_eq
    {K : Nat}
    (spec : ETC.Spec K) (a : Fin K) (m : Nat) :
    pullCount (ETC.exploreArm spec) a (m * K) = m

theorem ETC.pullCount_exploreArm_explorationPulls_mul_K_eq
    {K : Nat}
    (spec : ETC.Spec K) (a : Fin K) :
    pullCount (ETC.exploreArm spec) a (spec.explorationPulls * K) =
      spec.explorationPulls
```

Verification from the current worktree:

```text
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

Current boundary:

- No full ETC action trace with commit behavior.
- No exploration-phase action trace boundary yet.
- No empirical mean or commit argmax theorem.
- No probability, expectation, filtration, concentration, or final ETC regret
  theorem.
- Existing deterministic regret adapters are compiled:
  `REGRET-COUNT-BOUND`, `REGRET-NAT-COUNT-BOUND`,
  `REGRET-UNIFORM-NAT-COUNT-BOUND`.

Questions:

1. What is the next single executable leaf?
2. Should we define the first exploration-phase action-trace boundary, or prove
   an exploration-only deterministic regret scaffold using the existing count
   lemmas and `REGRET-UNIFORM-NAT-COUNT-BOUND`?
3. What exact Lean-facing statement should be attempted next?
4. What imports/local APIs should it use?
5. What regularity contracts should it require?
6. How should it be classified: imported, port candidate, Mathlib candidate,
   project-local, or theorem-card-only?
7. What should the failure policy be?

Please keep the recommendation to one small compiled Lean leaf. Do not
recommend probability, concentration, empirical means, commit argmax, or a final
ETC regret theorem in this batch.
