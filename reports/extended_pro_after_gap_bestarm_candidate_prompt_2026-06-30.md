# Extended Pro Review Prompt: After Finite-Bandit Gap BestArm Ledger

ABRL Lean 4 status:

- You previously rejected A/B/C for one batch after
  `ETC-ACTION-WITH-COMMIT-PHASE-SPLIT-REGRET-BOUND` and requested the smaller
  prerequisite `FINITE-BANDIT-GAP-BESTARM`.
- Local verification found that prerequisite was already compiled as
  `FiniteBanditModel.gap_bestArm` in `BanditRLProof.Core`.
- We recorded it in local leaf cards, the theory tree, collaborator docs, and
  the retrieval index.
- `python3 tools/bandit.py check` passed after the ledger update.

Compiled prerequisite:

```lean
@[simp] theorem FiniteBanditModel.gap_bestArm
    {K : Nat}
    (model : FiniteBanditModel K) :
    model.gap model.bestArm = 0
```

Newest ETC regret facts already compiled:

```lean
theorem ETC.pseudoRegret_actionWithCommit_explorationPulls_mul_K_add_eq_add_suffix_gap
    {K : Nat}
    (spec : ETC.Spec K) (model : FiniteBanditModel K)
    (commitArm : Fin K) (r : Nat) :
    pseudoRegret model (ETC.actionWithCommit spec commitArm)
        (spec.explorationPulls * K + r) =
      pseudoRegret model (ETC.actionWithCommit spec commitArm)
        (spec.explorationPulls * K) +
      (((r : Nat) : Rat) * model.gap commitArm)

theorem ETC.pseudoRegret_actionWithCommit_explorationPulls_mul_K_add_le_sum_gap_mul_explorationPulls_add_suffix_gap
    {K : Nat}
    (spec : ETC.Spec K) (model : FiniteBanditModel K)
    (commitArm : Fin K) (r : Nat) :
    pseudoRegret model (ETC.actionWithCommit spec commitArm)
        (spec.explorationPulls * K + r) <=
      ((Finset.univ : Finset (Fin K)).sum
        (fun a : Fin K => model.gap a)) *
        (((spec.explorationPulls : Nat) : Rat)) +
      (((r : Nat) : Rat) * model.gap commitArm)
```

Please choose the next exact single leaf. Do not choose empirical means,
commit argmax, probability, concentration, filtration, conditional expectation,
or final ETC theorem work yet.

## Candidate A: Optimal Commit Has No Extra Suffix Regret

```lean
theorem ETC.pseudoRegret_actionWithCommit_explorationPulls_mul_K_add_eq_of_commitArm_eq_bestArm
    {K : Nat}
    (spec : ETC.Spec K) (model : FiniteBanditModel K)
    (commitArm : Fin K) (r : Nat)
    (hcommit : commitArm = model.bestArm) :
    pseudoRegret model (ETC.actionWithCommit spec commitArm)
        (spec.explorationPulls * K + r) =
      pseudoRegret model (ETC.actionWithCommit spec commitArm)
        (spec.explorationPulls * K)
```

Potential proof route:

- Rewrite with the phase-split equality.
- Use `hcommit` and `FiniteBanditModel.gap_bestArm`.
- Close `r * 0 = 0` and `x + 0 = x`.

## Candidate B: Best-Arm Commit Phase Trace Lemma

```lean
theorem ETC.actionWithCommit_eq_bestArm_of_commitArm_eq_bestArm_of_explorationPulls_mul_K_le
    {K : Nat}
    (spec : ETC.Spec K) (model : FiniteBanditModel K)
    (commitArm : Fin K) (t : Nat)
    (hcommit : commitArm = model.bestArm)
    (ht : spec.explorationPulls * K <= t) :
    ETC.actionWithCommit spec commitArm t = model.bestArm
```

Potential proof route:

- Use `ETC.actionWithCommit_eq_commitArm_of_ge`.
- Rewrite with `hcommit`.

## Candidate C: Do Not Add A New Leaf

If Candidate A should now be proved directly and Candidate B is unnecessary,
say so explicitly. If another smaller prerequisite is needed, give its exact
Lean-facing statement and explain why it must precede Candidate A.

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
