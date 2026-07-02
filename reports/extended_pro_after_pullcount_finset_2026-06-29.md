# Extended Pro Review: After PULLCOUNT-FINSET Closure

Prompt: `reports/extended_pro_after_pullcount_finset_prompt_2026-06-29.md`

Status: review received in ChatGPT Pro Extended.

## Key Conclusions

Extended Pro agreed that closing `PULLCOUNT-FINSET` by direct induction was
reasonable.  The list bridge was a plausible route, but the direct recurrence
proof better matched the local recursive definition and avoided brittle
alignment between `List.range.filter.length` and `Finset.range.filter.card`.

It confirmed `Mathlib.Data.Finset.Card` as the correct import boundary for
the cardinality wrapper.

For finite sums, it recommended a deterministic big-operator boundary:

```lean
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
```

It recommended `PSEUDOREGRET-FINSET` before `SUMREWARDS-FINSET` because the
pseudo-regret target is a cleaner `Finset.sum` over `Rat` gaps, while reward
sums add a generic `Reward` type and stronger additive contracts.

## Recommended Execution Order

1. Keep `PULLCOUNT-FINSET` closed.
2. Add `PSEUDOREGRET-FINSET`.
3. Add one small test consumer.
4. Refresh the unfinished-leaf index and docs.
5. If it compiles, do at most one more leaf: `SUMREWARDS-FINSET`.
6. Stop and review again before moving into probability, measure,
   filtration, or concentration.

## Local Follow-Through

This run followed the recommendation and completed both finite-sum wrappers:

```lean
theorem pseudoRegret_eq_finset_sum :
    pseudoRegret model action t =
      (Finset.range t).sum (fun s : Nat => model.gap (action s))

theorem sumRewards_eq_finset_filter_sum :
    sumRewards action reward a t =
      ((Finset.range t).filter (fun s : Nat => action s = a)).sum
        (fun s : Nat => reward s)
```

The `SUMREWARDS-FINSET` wrapper records the stronger local contract
`[AddCommMonoid Reward]`, which is required by `Finset.sum` and by the
inserted-summand branch where addition order is swapped.

## Failure Policy To Preserve

- Do not introduce `sorry`, `axiom`, fake instances, or broad `import Mathlib`.
- Do not import probability/measure/order modules to solve deterministic
  finite-sum wrapper friction.
- If typeclass synthesis fails, document the exact scalar/additive structure
  problem and keep the gate green.
- Ask again before entering probability/concentration work.
