# Extended Pro Review: After Three Finset Wrappers

Prompt: `reports/extended_pro_after_three_finset_wrappers_prompt_2026-06-29.md`

Status: review received in ChatGPT Pro Extended.

## Key Conclusion

Extended Pro recommended not entering the probability/measure layer yet.
Instead, the next single leaf should be a deterministic consumer of the three
compiled Finset wrappers:

```text
REGRET-PULLCOUNT
```

The goal is to convert the time-indexed pseudo-regret sum into an arm-indexed
finite sum of gaps times pull counts.  This creates the deterministic identity
that UCB, ETC, and later concentration arguments should consume.

## Recommended Statement Shape

Suggested theorem name:

```lean
pseudoRegret_eq_finset_sum_gap_mul_pullCount
```

Suggested statement:

```lean
theorem pseudoRegret_eq_finset_sum_gap_mul_pullCount
    (model : FiniteBanditModel K) (action : Nat -> Fin K) (t : Nat) :
    pseudoRegret model action t =
      (Finset.univ : Finset (Fin K)).sum
        (fun a : Fin K => model.gap a * (pullCount action a t : Rat))
```

## Suggested Imports

```lean
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Nat.Cast.Basic
import BanditRLProof.MathlibWrappers
```

The local wrapper import provides:

- `pseudoRegret_eq_finset_sum`;
- `pullCount_eq_finset_filter_card`;
- the existing finite-sum and Rat imports.

## Suggested Proof Route

1. Rewrite pseudo-regret with `pseudoRegret_eq_finset_sum`.
2. Reindex the time sum by action fibers using `Finset.sum_fiberwise'`.
3. Use `Finset.sum_congr` arm-by-arm.
4. Use `Finset.sum_const` on each action fiber.
5. Replace the fiber cardinality using `pullCount_eq_finset_filter_card`.
6. Normalize `Nat` scalar multiplication with `nsmul_eq_mul'`.

## Failure Policy

- Do not start probability imports if this deterministic identity fails.
- Do not use `import Mathlib`, `sorry`, `axiom`, fake instances, or theorem-card
  weakening.
- If `Finset.univ` or `Fintype (Fin K)` fails, keep/add
  `Mathlib.Data.Fintype.Basic`.
- If the cast/scalar rewrite fails, use a local helper for
  `n • x = x * (n : Rat)`.
- If `Finset.sum_fiberwise'` is the friction point, document the exact error
  and keep the gate green.

## Batch Rule

Complete only `REGRET-PULLCOUNT`, one test consumer, docs/index refresh, and
`python3 tools/bandit.py check`, then ask Extended Pro again before moving to
probability, UCB/ETC, or another reindexing row.
