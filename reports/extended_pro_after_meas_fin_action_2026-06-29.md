# Extended Pro Review: After MEAS-FIN-ACTION

Prompt: `reports/extended_pro_after_meas_fin_action_prompt_2026-06-29.md`

Status: review received in ChatGPT Pro Extended.

## Key Conclusion

Extended Pro accepted `MEAS-FIN-ACTION` as the right first probability/measure
canary:

```lean
theorem measurableSet_actionTrace_eval_eq
    {Omega : Type u} {Action : Type v}
    [MeasurableSpace Omega] [MeasurableSpace Action]
    [MeasurableSingletonClass Action]
    (action : Omega -> ActionTrace Action)
    (hmeas : forall t : Nat, Measurable (fun omega : Omega => action omega t))
    (a : Action) (t : Nat) :
    MeasurableSet {omega : Omega | action omega t = a}
```

The review said this establishes the minimal event-level stochastic interface
without requiring a measure, probability measure, integrability, filtration,
finite action space, or reward model.

## Recommended Next Single Leaf

Do one pull-event indicator measurability leaf next:

```text
MEAS-PULL-INDICATOR
```

Do not jump directly to `MEAS-REGRET`, `MEAS-REWARD`,
`EXP-INDICATOR-PULL`, or `EXP-REGRET-PULLCOUNT`.

The goal is to turn the measurable action-equality event into a measurable
indicator-valued function.  This is the bridge needed before expectation
identities over pull indicators.

## Suggested File

Keep it in:

```text
BanditRLProof/MeasureFoundation.lean
```

## Suggested Imports

Change:

```lean
import Mathlib.MeasureTheory.MeasurableSpace.Defs
```

to:

```lean
import Mathlib.MeasureTheory.MeasurableSpace.Basic
```

Keep:

```lean
import BanditRLProof.Core
```

`Basic` is the right boundary because it provides `Measurable.indicator`.

## Suggested Theorem

Suggested theorem name:

```lean
measurable_actionTrace_eval_eq_indicator_const
```

Suggested statement:

```lean
theorem measurable_actionTrace_eval_eq_indicator_const
    {Omega : Type u} {Action : Type v} {Beta : Type w}
    [MeasurableSpace Omega] [MeasurableSpace Action]
    [MeasurableSingletonClass Action]
    [MeasurableSpace Beta] [Zero Beta]
    (action : Omega -> ActionTrace Action)
    (hmeas : forall t : Nat, Measurable (fun omega : Omega => action omega t))
    (a : Action) (t : Nat) (c : Beta) :
    Measurable
      (({omega : Omega | action omega t = a} : Set Omega).indicator
        (fun _ : Omega => c)) := by
  exact Measurable.indicator measurable_const
    (measurableSet_actionTrace_eval_eq action hmeas a t)
```

The statement should stay scalar-agnostic instead of specializing to `Rat` or
`Real`.

## Local APIs to Reuse

Reuse:

```lean
measurableSet_actionTrace_eval_eq
```

Use Mathlib:

```lean
Measurable.indicator
measurable_const
```

## Regularity Contract

Use:

```lean
[MeasurableSpace Omega]
[MeasurableSpace Action]
[MeasurableSingletonClass Action]
[MeasurableSpace Beta]
[Zero Beta]
```

Do not require:

```lean
[DecidableEq Action]
[Fintype Action]
Measure Omega
ProbabilityMeasure Omega
IsProbabilityMeasure mu
Integrable
NormedAddCommGroup Beta
Rat
Real
Filtration
```

The absence of `[DecidableEq Action]` is intentional because this theorem uses
`Set.indicator`, not a computable `if action omega t = a then ... else ...`.

## Proof Route

The proof should be one step:

```lean
exact Measurable.indicator measurable_const
  (measurableSet_actionTrace_eval_eq action hmeas a t)
```

No induction, finite sums, pull-count recursion, reward trace, or regret theorem
should appear.

## Failure Policy

- If this leaf fails, first confirm `Mathlib.MeasureTheory.MeasurableSpace.Basic`
  is imported instead of only `Defs`.
- If method syntax is brittle, use explicit theorem arguments for
  `Measurable.indicator`.
- Keep `[MeasurableSpace Beta]` explicit if codomain inference is brittle.
- Do not import integration, probability, filtration, or all of Mathlib.
- Do not specialize prematurely to `Rat` or `Real`.
- Do not add `sorry`, `axiom`, or a weakened event-only restatement.
- Mark the row complete only after `python3 tools/bandit.py check` passes.

## Batch Rule

Complete only:

```text
MEAS-PULL-INDICATOR
```

plus:

- one test consumer;
- root import check;
- unfinished-leaf/docs/index refresh;
- `python3 tools/bandit.py check`.

Then ask again.  The next review should decide whether to move to
`EXP-INDICATOR-PULL` or add a measurable finite-sum/count random-variable leaf
first.
