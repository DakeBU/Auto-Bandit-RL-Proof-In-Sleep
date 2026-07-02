# Extended Pro review after MEAS-PULLCOUNT

Extended Pro accepted `MEAS-PULLCOUNT / measurable_pullCount` and recommended one more local measurable-function leaf before entering expectation or probability measures.

## Review of MEAS-PULLCOUNT

`MEAS-PULLCOUNT / measurable_pullCount` is reasonable as implemented. Do not adjust it before building on it.

The proof made the right local choice:

- induction over `pullCount`;
- use the compiled event-measurability theorem;
- use the local recurrence `pullCount_succ`;
- keep `[MeasurableSpace Nat] [MeasurableAdd₂ Nat]` explicit for the Nat-valued theorem.

These assumptions are acceptable for the Nat-valued measurable-function layer, but should not be treated as the final scalar contract for expected-regret algebra.

## Next Leaf

Do scalar-casted pull-count measurability next.

Recommended row:

```text
MEAS-PULLCOUNT-CAST
```

Recommended theorem:

```lean
measurable_natCast_pullCount
```

Do not start `EXP-INDICATOR-PULL` yet. Expectation will force a measure/integration route. The next lower-risk bridge is to show that the count appearing in the compiled regret decomposition,

```lean
(pullCount action a t : Rat)
```

or more generally:

```lean
(pullCount action a t : Beta)
```

is measurable.

## Recommended File

```text
BanditRLProof/MeasurablePullCountCast.lean
```

Root import:

```lean
import BanditRLProof.MeasurablePullCountCast
```

## Recommended Imports

```lean
import Mathlib.Data.Nat.Cast.Basic
import Mathlib.MeasureTheory.Group.Arithmetic
import BanditRLProof.MeasurablePullCount
```

## Recommended Statement

```lean
theorem measurable_natCast_pullCount
    {Omega : Type u} {Action : Type v} {Beta : Type w}
    [MeasurableSpace Omega] [MeasurableSpace Action]
    [MeasurableSingletonClass Action]
    [MeasurableSpace Beta] [AddCommMonoidWithOne Beta] [MeasurableAdd₂ Beta]
    [DecidableEq Action]
    (action : Omega -> ActionTrace Action)
    (haction : forall t : Nat,
      Measurable (fun omega : Omega => action omega t))
    (a : Action) (n : Nat) :
    Measurable
      (fun omega : Omega =>
        ((pullCount (action omega) a n : Nat) : Beta))
```

## Proof Route

Use direct scalar induction rather than proving Nat-valued pull-count measurability and composing a cast.

The successor case should use:

- `measurableSet_actionTrace_eval_eq`;
- `Measurable.ite`;
- `Measurable.add`;
- `pullCount_succ`;
- `Nat.cast_add`.

This avoids requiring `[MeasurableSpace Nat] [MeasurableAdd₂ Nat]` and proves the scalar-valued statement needed by regret algebra.

## Contracts

Use:

```lean
[MeasurableSpace Omega]
[MeasurableSpace Action]
[MeasurableSingletonClass Action]
[MeasurableSpace Beta]
[AddCommMonoidWithOne Beta]
[MeasurableAdd₂ Beta]
[DecidableEq Action]
```

Do not add:

```lean
[MeasurableSpace Nat]
[MeasurableAdd₂ Nat]
[Fintype Action]
Measure Omega
ProbabilityMeasure Omega
IsProbabilityMeasure μ
Integrable
Filtration
Real
Rat
```

The theorem should stay scalar-generic; later consumers can instantiate `Beta := Rat`.

## Minimal Batch

Complete only:

```text
MEAS-PULLCOUNT-CAST
```

with:

```text
BanditRLProof/MeasurablePullCountCast.lean
root import in BanditRLProof.lean
one consumer test in Tests/Basic.lean
unfinished/docs/index refresh
python3 tools\bandit.py check
```

Then ask again. The next review should decide whether to introduce the first expectation canary or add a Rat-specific expected-regret interface.
