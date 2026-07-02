# Extended Pro Review Prompt: After ETC Suffix Count-Budget Regret

ABRL Lean 4 status:

- `ETC-ACTION-WITH-COMMIT-COMMITARM-SUFFIX-COUNT` compiles locally.
- Extended Pro chose Candidate B after that boundary.
- `ETC-ACTION-WITH-COMMIT-SUFFIX-COUNT-BUDGET-REGRET` now compiles locally.
- `lake build` and `lake build Tests` passed after the new theorem was added.

Newest compiled theorem:

```lean
theorem ETC.pseudoRegret_actionWithCommit_explorationPulls_mul_K_add_le_sum_gap_mul_suffix_count_budget
    {K : Nat}
    (spec : ETC.Spec K) (model : FiniteBanditModel K)
    (commitArm : Fin K) (r : Nat) :
    pseudoRegret model (ETC.actionWithCommit spec commitArm)
        (spec.explorationPulls * K + r) <=
      (Finset.univ : Finset (Fin K)).sum
        (fun a : Fin K =>
          model.gap a *
            (((spec.explorationPulls +
                (if commitArm = a then r else 0) : Nat) : Rat)))
```

Current local APIs:

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

theorem ETC.pullCount_actionWithCommit_explorationPulls_mul_K_add_eq
    {K : Nat} (spec : ETC.Spec K) (commitArm a : Fin K) (r : Nat) :
    pullCount (ETC.actionWithCommit spec commitArm) a
        (spec.explorationPulls * K + r) =
      spec.explorationPulls + (if commitArm = a then r else 0)

theorem ETC.actionWithCommit_eq_commitArm_of_ge
    {K : Nat} (spec : ETC.Spec K) (commitArm : Fin K) {t : Nat}
    (h : spec.explorationPulls * K <= t) :
    ETC.actionWithCommit spec commitArm t = commitArm
```

Please choose the next exact single leaf. Do not choose probability,
filtration, conditional expectation, empirical means, commit argmax,
concentration, or final ETC theorem work yet.

## Candidate A: Generic Constant-Arm Pseudo-Regret Suffix Equality

Possible statement:

```lean
theorem pseudoRegret_add_eq_add_nat_mul_gap_of_forall_action_eq_between
    {K : Nat}
    (model : FiniteBanditModel K) (action : ActionTrace (Fin K))
    (t n : Nat) (arm : Fin K)
    (h : forall s : Nat, t <= s -> s < t + n -> action s = arm) :
    pseudoRegret model action (t + n) =
      pseudoRegret model action t + (((n : Nat) : Rat) * model.gap arm)
```

Potential value:

- Reusable beyond ETC.
- The ETC phase split can later instantiate it with
  `ETC.actionWithCommit_eq_commitArm_of_ge`.

Concern:

- It introduces Rat/Nat multiplication arithmetic and may need extra Mathlib
  imports or a smaller arithmetic helper.

## Candidate B: ETC Phase-Splitting Regret Equality

Possible statement:

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
```

Potential value:

- Direct phase split for fixed-commit ETC.
- Avoids Finset RHS simplification.

Concern:

- Less reusable than Candidate A, and still has Rat/Nat multiplication
  arithmetic.

## Candidate C: Coarse Uniform Post-Horizon Count-Budget Regret Bound

Possible statement:

```lean
theorem ETC.pseudoRegret_actionWithCommit_explorationPulls_mul_K_add_le_sum_gap_mul_explorationPulls_add_suffix
    {K : Nat}
    (spec : ETC.Spec K) (model : FiniteBanditModel K)
    (commitArm : Fin K) (r : Nat) :
    pseudoRegret model (ETC.actionWithCommit spec commitArm)
        (spec.explorationPulls * K + r) <=
      ((Finset.univ : Finset (Fin K)).sum
        (fun a : Fin K => model.gap a)) *
        ((((spec.explorationPulls + r) : Nat) : Rat))
```

Potential proof route:

- Apply `pseudoRegret_le_sum_gap_mul_uniform_nat_count_bound`.
- Prove each arm count is at most `spec.explorationPulls + r` from
  `ETC.pullCount_actionWithCommit_explorationPulls_mul_K_add_eq`.

Concern:

- It is weaker than the already compiled unsimplified count-budget bound, but
  likely easier than phase splitting or Finset RHS simplification.

Requested response:

1. Pick exactly one candidate, or reject all with a smaller replacement.
2. Give the exact Lean-facing statement.
3. Give imports/local APIs.
4. Give intended proof route.
5. Give regularity contracts.
6. Give retrieval evidence/classification.
7. Give failure policy.
