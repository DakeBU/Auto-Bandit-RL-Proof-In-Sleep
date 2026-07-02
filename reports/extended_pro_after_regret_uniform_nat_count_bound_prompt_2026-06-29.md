# Extended Pro Review Prompt: After REGRET-UNIFORM-NAT-COUNT-BOUND

We are working in the ABRL Lean 4 repository for formalizing bandit/RL theory.

Following your previous recommendation, I completed exactly one deterministic
adapter leaf:

```text
REGRET-UNIFORM-NAT-COUNT-BOUND
```

New compiled theorem, in `BanditRLProof/RegretCountBounds.lean`:

```lean
theorem pseudoRegret_le_sum_gap_mul_uniform_nat_count_bound
    {K : Nat}
    (model : FiniteBanditModel K)
    (action : ActionTrace (Fin K))
    (n B : Nat)
    (hB : forall a : Fin K,
      pullCount action a n <= B) :
    pseudoRegret model action n <=
      ((Finset.univ : Finset (Fin K)).sum
        (fun a : Fin K => model.gap a)) * (((B : Nat) : Rat))
```

Implementation route:

- reuse `pseudoRegret_le_finset_sum_gap_mul_nat_count_bound`;
- instantiate the arm-dependent Nat budget with `B := fun _a : Fin K => B`;
- use `Finset.sum_mul` to factor the uniform Rat budget out of the finite sum.

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

Current local ETC API, in `BanditRLProof/Algorithms/ETC.lean`:

```lean
structure Spec (K : Nat) where
  hK : 0 < K
  explorationPulls : Nat

def exploreArm (spec : Spec K) (t : Nat) : Fin K :=
  { val := t % K, isLt := Nat.mod_lt t spec.hK }

@[simp] theorem exploreArm_val (spec : Spec K) (t : Nat) :
    (exploreArm spec t).val = t % K := rfl

theorem exploreArm_eq_of_mod_eq (spec : Spec K) {s t : Nat}
    (h : s % K = t % K) :
    exploreArm spec s = exploreArm spec t := by
  apply Fin.ext
  exact h

theorem exploreArm_add_K (spec : Spec K) (t : Nat) :
    exploreArm spec (t + K) = exploreArm spec t := by
  apply exploreArm_eq_of_mod_eq
  simp
```

There is no full ETC action trace yet. Current ETC obligations are only named:

```lean
def obligationNames : List String :=
  [ "round_robin_exploration_counts"
  , "empirical_mean_argmax_commit"
  , "subgaussian_wrong_commit_probability"
  , "pull_count_bound_after_commit"
  , "regret_from_pull_count_bounds"
  ]
```

Current boundary:

- Deterministic finite-sum/count/regret scaffolds are compiled.
- Mathlib-backed `Finset.range` wrappers are compiled.
- Measurability canaries and ENNReal lower-integral pull-count/regret bridges
  are compiled.
- Still no Rat-valued Bochner expected regret theorem, filtration,
  conditional expectation, sub-Gaussian/Hoeffding/martingale tail theorem,
  or final UCB/ETC theorem.
- `theorem-card` rows are still route cards only, not local Lean proofs.

Questions:

1. What is the next single executable ETC-specific count scaffold?
2. Should the next leaf define an exploration action trace/predicate first, or
   prove one more property of `ETC.exploreArm`?
3. What exact Lean-facing statement should be attempted next?
4. What imports/local APIs should it use?
5. What regularity contracts should it require?
6. How should it be classified: imported, port candidate, Mathlib candidate,
   project-local, or theorem-card-only?
7. What should the failure policy be?

Please keep the recommendation to one small compiled Lean leaf. Do not
recommend jumping directly to probability, concentration, or a final ETC regret
theorem in the same batch.
