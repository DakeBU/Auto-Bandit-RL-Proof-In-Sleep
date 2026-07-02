# Extended Pro Review Prompt: After ETC Phase-Split Regret Bound

ABRL Lean 4 status:

- `ETC-ACTION-WITH-COMMIT-PHASE-SPLIT-REGRET` compiles locally.
- Extended Pro then chose the phase-split bound consumer.
- `ETC-ACTION-WITH-COMMIT-PHASE-SPLIT-REGRET-BOUND` now compiles locally.
- `lake build` and `lake build Tests` passed after the theorem was added.

Newest compiled theorem:

```lean
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

## Candidate B: Simplify Unsimplified Suffix Budget RHS

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

## Candidate C: Generic Constant-Arm Pseudo-Regret Suffix Equality

```lean
theorem pseudoRegret_add_eq_add_nat_mul_gap_of_forall_action_eq_between
    {K : Nat}
    (model : FiniteBanditModel K) (action : ActionTrace (Fin K))
    (t n : Nat) (arm : Fin K)
    (h : forall s : Nat, t <= s -> s < t + n -> action s = arm) :
    pseudoRegret model action (t + n) =
      pseudoRegret model action t + (((n : Nat) : Rat) * model.gap arm)
```

Requested response:

1. Pick exactly one candidate, or reject all with a smaller replacement.
2. Give the exact Lean-facing statement.
3. Give imports/local APIs.
4. Give intended proof route.
5. Give regularity contracts.
6. Give retrieval evidence/classification.
7. Give failure policy.
