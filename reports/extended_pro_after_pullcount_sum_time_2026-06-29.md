# Extended Pro Review: After PULLCOUNT-SUM-TIME

Prompt: `reports/extended_pro_after_pullcount_sum_time_prompt_2026-06-29.md`

Status: review received in ChatGPT Pro Extended.

## Key Conclusion

Extended Pro accepted the generalized `PULLCOUNT-SUM-TIME` theorem as the right
deterministic count-partition leaf:

```lean
theorem finset_sum_pullCount_eq_time
    {Action : Type u} [Fintype Action] [DecidableEq Action]
    (action : ActionTrace Action) (t : Nat) :
    (Finset.univ : Finset Action).sum
      (fun a : Action => pullCount action a t) = t
```

The review said generalizing from `Fin K` to arbitrary finite actions was the
right contract because the theorem is independent of `FiniteBanditModel`,
`Rat`, gaps, rewards, and probability.

## Recommended Next Single Leaf

Start the probability/measure foundation now, but only with the smallest
probability-facing canary:

```text
MEAS-FIN-ACTION
```

The next leaf should prove that if each time-indexed action random variable is
measurable, then the event that the selected action at time `t` equals arm `a`
is measurable.

Do not start expectation, integrability, conditional expectation, filtrations,
martingales, or concentration yet.

## Suggested File

```text
BanditRLProof/MeasureFoundation.lean
```

Import it from:

```text
BanditRLProof.lean
```

## Suggested Imports

```lean
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import BanditRLProof.LeafLemmas
```

If `Defs` is insufficient, escalate only to:

```lean
import Mathlib.MeasureTheory.MeasurableSpace.Basic
```

Do not import measure, probability measure, integration, filtration, or all of
Mathlib for this leaf.

## Suggested Theorem

Suggested theorem name:

```lean
measurableSet_actionTrace_eval_eq
```

Suggested statement:

```lean
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import BanditRLProof.LeafLemmas

universe u v

namespace BanditRLProof

theorem measurableSet_actionTrace_eval_eq
    {Omega : Type u} {Action : Type v}
    [MeasurableSpace Omega] [MeasurableSpace Action]
    [MeasurableSingletonClass Action]
    (action : Omega -> ActionTrace Action)
    (hmeas : forall t : Nat, Measurable (fun omega : Omega => action omega t))
    (a : Action) (t : Nat) :
    MeasurableSet {omega : Omega | action omega t = a} := by
  simpa [Set.preimage] using
    ((hmeas t) (MeasurableSet.singleton a))

end BanditRLProof
```

An explicit fallback proof:

```lean
have hsingle : MeasurableSet ({a} : Set Action) :=
  MeasurableSet.singleton a
have hpre :
    MeasurableSet
      ((fun omega : Omega => action omega t) ⁻¹' ({a} : Set Action)) :=
  (hmeas t) hsingle
simpa [Set.preimage] using hpre
```

## Local APIs to Reuse

Reuse only:

```lean
ActionTrace
```

Do not use deterministic finite-sum or regret modules in this proof.

## Regularity Contract

Use:

```lean
[MeasurableSpace Omega]
[MeasurableSpace Action]
[MeasurableSingletonClass Action]
hmeas : forall t : Nat, Measurable (fun omega : Omega => action omega t)
```

Do not require:

```lean
[Fintype Action]
[DecidableEq Action]
Measure Omega
ProbabilityMeasure Omega
IsProbabilityMeasure mu
Integrable
Filtration
```

The theorem should remain more general than finite actions: equality-event
measurability only needs singleton measurability.

## Proof Route

1. Take the singleton `{a}` in the action space.
2. Use `[MeasurableSingletonClass Action]` to prove
   `MeasurableSet ({a} : Set Action)`.
3. Apply `hmeas t`.
4. Simplify the preimage `(fun omega => action omega t) ⁻¹' {a}` into
   `{omega | action omega t = a}`.

## Failure Policy

- If the compact proof fails, use the explicit singleton/preimage fallback.
- If `Mathlib.MeasureTheory.MeasurableSpace.Defs` is insufficient, escalate
  only to `Mathlib.MeasureTheory.MeasurableSpace.Basic`.
- Do not add broad imports, probability imports, `sorry`, `axiom`, fake
  instances, or a weakened theorem.
- Do not mark `MEAS-FIN-ACTION` closed until `python3 tools/bandit.py check`
  passes.

## Batch Rule

Complete only this batch:

```text
MEAS-FIN-ACTION
```

with:

- `BanditRLProof/MeasureFoundation.lean`;
- one test consumer in `Tests/Basic.lean`;
- root import in `BanditRLProof.lean`;
- unfinished-leaf/docs/index refresh;
- `python3 tools/bandit.py check`.

Then ask Extended Pro again.  The next decision should be between
`MEAS-PULLCOUNT` / `EXP-INDICATOR-PULL` and the first filtration contract, not
expectation or concentration directly.
