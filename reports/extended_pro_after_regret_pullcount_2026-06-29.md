# Extended Pro Review: After REGRET-PULLCOUNT

Prompt: `reports/extended_pro_after_regret_pullcount_prompt_2026-06-29.md`

Status: review received in ChatGPT Pro Extended.

## Key Conclusion

Extended Pro accepted `REGRET-PULLCOUNT` as the right first deterministic
consumer leaf after the three compiled Finset wrappers.

The completed theorem:

```lean
theorem pseudoRegret_eq_finset_sum_gap_mul_pullCount
    (model : FiniteBanditModel K) (action : Nat -> Fin K) (t : Nat) :
    pseudoRegret model action t =
      (Finset.univ : Finset (Fin K)).sum
        (fun a : Fin K => model.gap a * (pullCount action a t : Rat))
```

The review said this is the deterministic interface that UCB, ETC, and
expected-regret arguments should consume.  It also validated the Mathlib
reindexing surface used by the proof: `Finset.sum_fiberwise'`,
`Finset.sum_const`, and Nat-to-`Rat` scalar normalization.

## Recommended Next Single Leaf

Do one more deterministic count-prep leaf before entering probability or
measure theory:

```text
PULLCOUNT-SUM-TIME
```

The intended mathematical statement is:

```text
sum_a N_a(t) = t
```

This is the natural companion to `REGRET-PULLCOUNT`: the previous theorem says
regret decomposes over arm pull counts, while this one says those pull counts
partition the time horizon.

## Suggested Lean Statement

Suggested theorem name:

```lean
finset_sum_pullCount_eq_time
```

Suggested statement:

```lean
import Mathlib.Data.Fintype.Basic
import BanditRLProof.MathlibWrappers

namespace BanditRLProof

theorem finset_sum_pullCount_eq_time
    (action : Nat -> Fin K) (t : Nat) :
    (Finset.univ : Finset (Fin K)).sum
      (fun a : Fin K => pullCount action a t) = t := by
  ...

end BanditRLProof
```

## Suggested Imports

```lean
import Mathlib.Data.Fintype.Basic
import BanditRLProof.MathlibWrappers
```

`Mathlib.Data.Fintype.Basic` is the explicit boundary for
`Finset.univ : Finset (Fin K)`.  `BanditRLProof.MathlibWrappers` should expose
`pullCount_eq_finset_filter_card` and the finite-sum Mathlib imports already
needed by the wrapper layer.

## APIs to Reuse

Local declaration:

```lean
pullCount_eq_finset_filter_card
```

Mathlib declaration:

```lean
Finset.sum_card_fiberwise_eq_card_filter
```

Fallback if that theorem is awkward:

```lean
Finset.card_eq_sum_card_fiberwise
```

Do not use `pseudoRegret_eq_finset_sum_gap_mul_pullCount` in this proof.  This
leaf is a count invariant, not a regret theorem.

## Regularity and Typeclass Contract

Expected inferred contracts only:

```lean
Fintype (Fin K)
DecidableEq (Fin K)
AddCommMonoid Nat
```

Do not add probability, measure, filtration, order, field, `Rat`, or explicit
`0 < K` assumptions.

## Proof Route

1. Rewrite each `pullCount` using `pullCount_eq_finset_filter_card`.
2. Apply `Finset.sum_card_fiberwise_eq_card_filter` with:

```lean
s := Finset.range t
t := (Finset.univ : Finset (Fin K))
g := action
```

3. Simplify `action s in Finset.univ` to `True`.
4. Simplify `(Finset.range t).card` to `t`.

This should use the Mathlib fiber theorem rather than induction on `t`, unless
the fiber theorem route unexpectedly fails.

## Failure Policy

- Prefer explicit `.sum` notation if big-operator notation creates friction.
- If `Finset.sum_card_fiberwise_eq_card_filter` does not simplify cleanly, try
  `Finset.card_eq_sum_card_fiberwise`.
- If `Finset.univ` or `Fin.fintype` resolution fails, keep the explicit
  `Mathlib.Data.Fintype.Basic` import.
- Do not add probability imports, `sorry`, `axiom`, fake instances, or a
  weakened theorem.
- Do not mark the row complete until `python3 tools/bandit.py check` passes.

## Batch Rule

Complete exactly `PULLCOUNT-SUM-TIME`, add one test consumer, refresh the
unfinished-leaf/docs index, run `python3 tools/bandit.py check`, then ask
Extended Pro again.  The next review should decide whether to start the
probability/measure foundation or add one more deterministic count corollary
such as `pullCount_le_time`.
