# Extended Pro Review Prompt: After ETC BestArm Commit Phase

ABRL Lean 4 status:

- `ETC-ACTION-WITH-COMMIT-BESTARM-SUFFIX-REGRET-BOUND` compiles locally.
- Extended Pro then chose
  `ETC-ACTION-WITH-COMMIT-BESTARM-COMMIT-PHASE`.
- That trace-boundary leaf now compiles locally in
  `BanditRLProof.Algorithms.ETCTrace`.
- `python3 tools/bandit.py check` passed after the theorem, tests, docs, and
  retrieval index were updated.

Newest compiled theorem:

```lean
theorem ETC.actionWithCommit_eq_bestArm_of_commitArm_eq_bestArm_of_explorationPulls_mul_K_le
    {K : Nat}
    (spec : ETC.Spec K) (model : FiniteBanditModel K)
    (commitArm : Fin K) (t : Nat)
    (hcommit : commitArm = model.bestArm)
    (ht : spec.explorationPulls * K <= t) :
    ETC.actionWithCommit spec commitArm t = model.bestArm
```

Please choose the next exact single leaf or stop decision. Do not choose a
broad final theorem. If you recommend leaving deterministic fixed-commit ETC,
classify the next item as theorem-card-only or missing-leaf and give the exact
design work, not a local proof to write immediately.

## Candidate A: General Suffix RHS Simplification

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

## Candidate B: Stop Deterministic ETC And Design Commit Correctness

No local Lean proof in this batch. Decide the exact theorem-card or missing
leaf needed for empirical commit correctness / wrong-commit concentration,
including required probability, filtration, empirical mean, and sub-Gaussian
contracts.

## Candidate C: Stop Deterministic ETC And Design First Probability Import Route

No local Lean proof in this batch. Decide the exact import-route or wrapper
needed before any ETC wrong-commit probability proof.

Requested response:

1. Pick exactly one next leaf or stop decision.
2. Give the exact Lean-facing statement if it is a local proof leaf.
3. List local APIs/imports.
4. Give the intended proof route or design route.
5. State regularity contracts.
6. Give retrieval evidence from Mathlib/LML/local declarations.
7. Classify it as imported, port candidate, Mathlib candidate, project-local,
   theorem-card-only, or missing-leaf.
8. Give a failure policy.
