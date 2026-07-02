# Extended Pro Review Prompt: After REGRET-NAT-COUNT-BOUND

We are working in the ABRL Lean 4 repository for formalizing bandit/RL theory.

Following your previous recommendation, I completed exactly one deterministic
adapter leaf:

```text
REGRET-NAT-COUNT-BOUND
```

New compiled theorem, in `BanditRLProof/RegretCountBounds.lean`:

```lean
theorem pseudoRegret_le_finset_sum_gap_mul_nat_count_bound
    {K : Nat}
    (model : FiniteBanditModel K)
    (action : ActionTrace (Fin K))
    (n : Nat)
    (B : Fin K -> Nat)
    (hB : forall a : Fin K,
      pullCount action a n <= B a) :
    pseudoRegret model action n <=
      (Finset.univ : Finset (Fin K)).sum
        (fun a : Fin K => model.gap a * (((B a : Nat) : Rat)))
```

Implementation route:

- reuse `pseudoRegret_le_finset_sum_gap_mul_count_bound`;
- instantiate `B := fun a => ((B a : Nat) : Rat)`;
- convert Nat count bounds using `(@Nat.cast_le Rat _ _ _ _ _).mpr`.

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

- one consumer test in `Tests/Basic.lean`;
- `tools/bandit.py` local leaf card and `unfinished` recommendation output;
- README, completion gap audit, project overview, collaborator guide,
  Mathlib foundation leaf map, theory tree;
- retrieval indexes and UCB/ETC memory refresh JSON.

Current boundary:

- Still no Rat-valued expected regret, Bochner expectation, integrability,
  filtration, conditional expectation, concentration, or final UCB/ETC theorem.
- `tools/bandit.py unfinished` now says to ask before choosing a uniform
  Nat-bound corollary or an ETC-specific count scaffold.

Questions:

1. What is the next single executable leaf?
2. Should it be a uniform Nat-bound corollary or the first ETC-specific count
   scaffold?
3. What exact Lean-facing statement should be attempted next?
4. What imports/local APIs should it use?
5. What should the failure policy be?
