# Extended Pro review after MEAS-REGRET

Extended Pro reviewed `MEAS-REGRET / measurable_pseudoRegret` after a retry. It accepted the implementation and recommended staying in the measurable-function layer for one more step before introducing probability measures, expectations, or integration.

## Review of MEAS-REGRET

`MEAS-REGRET / measurable_pseudoRegret` is reasonable as implemented. The theorem has the right scope:

```lean
Measurable
  (fun omega : Omega => pseudoRegret model (action omega) n)
```

The proof correctly:

- consumes `pseudoRegret_eq_finset_sum`;
- avoids unfolding `pseudoRegret`;
- avoids probability measures, expectation, filtrations, and concentration;
- keeps `[MeasurableSpace Rat] [MeasurableAdd₂ Rat]` explicit rather than silently choosing an integration/Borel route;
- uses `measurable_of_finite` for the finite-domain gap map.

## Candidate discussion

The response first discussed a scalar-generic cast bridge:

```text
MEAS-PULLCOUNT-CAST
measurable_natCast_pullCount
```

This would prove casted pull counts measurable in an arbitrary scalar `Beta`. The response then produced a final explicit “2/2” recommendation to first do the more basic Nat-valued pull-count measurability leaf, and leave the scalar-cast bridge for the next review.

## Final next leaf

Do:

```text
MEAS-PULLCOUNT
```

Recommended theorem:

```lean
measurable_pullCount
```

Do not start `EXP-INDICATOR-PULL` yet. Expected pull-count identities require probability/integration choices, while `MEAS-PULLCOUNT` remains a pure measurable-function leaf.

## Recommended file

```text
BanditRLProof/MeasurablePullCount.lean
```

Root import:

```lean
import BanditRLProof.MeasurablePullCount
```

## Recommended imports

```lean
import Mathlib.MeasureTheory.Group.Arithmetic
import BanditRLProof.MeasureFoundation
import BanditRLProof.LeafLemmas
```

## Recommended statement

```lean
theorem measurable_pullCount
    {Omega : Type u} {Action : Type v}
    [MeasurableSpace Omega] [MeasurableSpace Action]
    [MeasurableSingletonClass Action]
    [MeasurableSpace Nat] [MeasurableAdd₂ Nat]
    [DecidableEq Action]
    (action : Omega -> ActionTrace Action)
    (haction : forall t : Nat,
      Measurable (fun omega : Omega => action omega t))
    (a : Action) (n : Nat) :
    Measurable
      (fun omega : Omega => pullCount (action omega) a n)
```

## Proof route

Use induction on `n`.

For the successor case, use:

- `measurableSet_actionTrace_eval_eq`;
- `pullCount_succ`;
- `Measurable.ite`;
- `Measurable.add`;
- `measurable_const`.

The fallback form should match the actual recurrence:

```lean
pullCount action a (n + 1)
  = pullCount action a n + if action n = a then 1 else 0
```

so the successor proof can build a measurable increment:

```lean
if action omega n = a then (1 : Nat) else 0
```

and add it to the induction hypothesis.

## Regularity contracts

Use:

```lean
[MeasurableSpace Omega]
[MeasurableSpace Action]
[MeasurableSingletonClass Action]
[MeasurableSpace Nat]
[MeasurableAdd₂ Nat]
[DecidableEq Action]
```

plus:

```lean
haction : forall t : Nat,
  Measurable (fun omega : Omega => action omega t)
```

Do not add:

```lean
[Fintype Action]
Measure Omega
ProbabilityMeasure Omega
IsProbabilityMeasure μ
Integrable
Rat
Real
Filtration
```

## Classification

Classify as:

```text
MEAS-PULLCOUNT: executable local measurable-quantity leaf
```

It should not close:

```text
EXP-INDICATOR-PULL
EXP-REGRET-PULLCOUNT
COND-EXPECT-REWARD
MART-DIFF-REWARD
```

## Minimal batch

Complete only:

```text
MEAS-PULLCOUNT
```

with:

```text
BanditRLProof/MeasurablePullCount.lean
root import in BanditRLProof.lean
one consumer test in Tests/Basic.lean
unfinished/docs/index refresh
python3 tools\bandit.py check
```

Then ask again. The next review should decide whether to introduce the first expectation canary or add a casted pull-count measurability bridge such as `Measurable (fun omega => (pullCount ... : Rat))`.
