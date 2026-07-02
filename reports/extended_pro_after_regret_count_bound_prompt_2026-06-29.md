# Extended Pro Review Prompt: After REGRET-COUNT-BOUND

We are working in the ABRL Lean 4 repository for formalizing bandit/RL theory.

Following your previous recommendation, I completed exactly one deterministic
scaffold leaf:

```text
REGRET-COUNT-BOUND
```

New compiled theorem, in `BanditRLProof/RegretCountBounds.lean`:

```lean
theorem pseudoRegret_le_finset_sum_gap_mul_count_bound
    {K : Nat}
    (model : FiniteBanditModel K)
    (action : ActionTrace (Fin K))
    (n : Nat)
    (B : Fin K -> Rat)
    (hB : forall a : Fin K,
      ((pullCount action a n : Nat) : Rat) <= B a) :
    pseudoRegret model action n <=
      (Finset.univ : Finset (Fin K)).sum
        (fun a : Fin K => model.gap a * B a)
```

Implementation route:

- rewrite with `pseudoRegret_eq_finset_sum_gap_mul_pullCount`;
- use `Finset.sum_le_sum`;
- each summand uses `mul_le_mul_of_nonneg_left (hB a)
  (FiniteBanditModel.gap_nonneg model a)`.

Verification:

```text
python3 tools/bandit.py check
Build completed successfully (1777 jobs).
Build completed successfully (1779 jobs).
$ lake build
$ lake build Tests
check passed
```

Updated:

- root import in `BanditRLProof.lean`;
- one consumer test in `Tests/Basic.lean`;
- `tools/bandit.py` local leaf cards and `unfinished` recommendation;
- README, completion gap audit, project overview, collaborator guide, theory
  tree, Mathlib foundation leaf map;
- retrieval indexes and UCB/ETC memory refresh JSON.

Current boundary:

- We have not proved Rat-valued expected regret, Bochner expectation,
  integrability, filtrations, conditional expectation, concentration, or final
  UCB/ETC/TS/EXP3/Tsallis/OFUL/RL theorem routes.
- `tools/bandit.py unfinished` now says to ask before choosing a Nat-bound
  convenience corollary or an ETC-specific count scaffold.

Questions:

1. What is the right next single executable leaf?
2. Should it be a Nat-bound convenience corollary for `REGRET-COUNT-BOUND`, or
   the first ETC-specific count scaffold?
3. What exact Lean-facing statement should be attempted next?
4. What imports/local APIs should it use?
5. What should the failure policy be?
