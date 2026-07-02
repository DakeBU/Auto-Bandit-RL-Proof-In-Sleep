# Extended Pro Review Prompt: After ETC BestArm Suffix Regret Bound

ABRL Lean 4 status:

- `ETC-ACTION-WITH-COMMIT-BESTARM-SUFFIX-NO-REGRET` compiles locally.
- Extended Pro then chose the direct consumer
  `ETC-ACTION-WITH-COMMIT-BESTARM-SUFFIX-REGRET-BOUND`.
- That bound now compiles locally in `BanditRLProof.Algorithms.ETCRegretLemmas`.
- `python3 tools/bandit.py check` passed after the theorem, tests, docs, and
  retrieval index were updated.

Newest compiled theorem:

```lean
theorem ETC.pseudoRegret_actionWithCommit_explorationPulls_mul_K_add_le_sum_gap_mul_explorationPulls_of_commitArm_eq_bestArm
    {K : Nat}
    (spec : ETC.Spec K) (model : FiniteBanditModel K)
    (commitArm : Fin K) (r : Nat)
    (hcommit : commitArm = model.bestArm) :
    pseudoRegret model (ETC.actionWithCommit spec commitArm)
        (spec.explorationPulls * K + r) <=
      ((Finset.univ : Finset (Fin K)).sum
        (fun a : Fin K => model.gap a)) *
        (((spec.explorationPulls : Nat) : Rat))
```

Please choose the next exact single leaf. Do not choose empirical means,
commit argmax, probability, concentration, filtration, conditional expectation,
or final ETC theorem work yet unless you explicitly argue the deterministic
fixed-commit layer is now saturated.

## Candidate A: Best-Arm Commit Phase Trace Lemma

```lean
theorem ETC.actionWithCommit_eq_bestArm_of_commitArm_eq_bestArm_of_explorationPulls_mul_K_le
    {K : Nat}
    (spec : ETC.Spec K) (model : FiniteBanditModel K)
    (commitArm : Fin K) (t : Nat)
    (hcommit : commitArm = model.bestArm)
    (ht : spec.explorationPulls * K <= t) :
    ETC.actionWithCommit spec commitArm t = model.bestArm
```

## Candidate B: General Suffix RHS Simplification

```lean
theorem ETC.sum_gap_mul_suffix_count_budget_eq_sum_gap_mul_explorationPulls_add_commit_gap_mul_suffix
    {K : Nat}
    (spec : ETC.Spec K) (model : FiniteBanditModel K)
    (commitArm : Fin K) (r : Nat) :
      (Finset.univ : Finset (Fin K)).sum
        (fun a : Fin K =>
          model.gap a *
            (((spec.explorationPulls +
                (if commitArm = a then r else 0) : Nat) : Rat))) =
      ((Finset.univ : Finset (Fin K)).sum
        (fun a : Fin K => model.gap a)) *
        (((spec.explorationPulls : Nat) : Rat)) +
      model.gap commitArm * (((r : Nat) : Rat))
```

## Candidate C: Stop Deterministic ETC For Now

If the fixed-commit deterministic layer is saturated enough, say so and name
the next non-deterministic prerequisite as theorem-card-only or missing-leaf.
Do not ask to prove it in this batch.

Requested response:

1. Pick exactly one next leaf.
2. Give the exact Lean-facing statement.
3. List local APIs/imports.
4. Give the intended proof route.
5. State regularity contracts.
6. Give retrieval evidence from Mathlib/LML/local declarations.
7. Classify it as imported, port candidate, Mathlib candidate, project-local,
   or theorem-card-only.
8. Give a failure policy.
